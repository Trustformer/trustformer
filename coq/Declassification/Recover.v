(*! The attacker's recipe: node values worked out from published bits alone, by
    running the circuit's operations forward and the declassification packets
    backward.  Definitions only; the proofs that it is right are in Extract.v. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.

Require Import Trustformer.Syntax.
Require Import Trustformer.Semantics.
Require Import Trustformer.DFG.

Require Import Coq.Lists.List.
Import ListNotations.

(* The first [Some] a list yields. *)
Fixpoint find_map {A B} (f: A -> option B) (l: list A) : option B :=
  match l with
  | [] => None
  | a :: rest => match f a with Some b => Some b | None => find_map f rest end
  end.

Section Recover.
  Context {s_var i_var o_var p_var: Type} {p_eq: EqDec p_var}.
  Context (ips: p_var -> ip_decl).
  Context (decls: list (decl_packet s_var i_var o_var p_var)).
  Context (g: @dfg_state_t s_var i_var o_var p_var).

  (* What is known so far: some nodes' bits, each at the node's own width. *)
  Definition known := forall n: nid_t, option (bits_t (node_sz g n)).

  Definition fill (k: known) : valuation g :=
    fun m => match k m with Some v => v | None => Bits.zero end.

  (* A path condition's truth, once every literal in it is known. *)
  Fixpoint guard_val (k: known) (en: list (nid_t * bool)) : option bool :=
    match en with
    | [] => Some true
    | (c, b) :: rest =>
        match k c, guard_val k rest with
        | Some v, Some r => Some (Bool.eqb (nonzero v) b && r)
        | _, _ => None
        end
    end.

  (* The drive a sample answers, through its stall and ordering join. *)
  Definition drive_head (p: p_var) (h: nid_t) : option nid_t :=
    match op (node_at g h) with
    | DFG_Drive p' _ _ => if eq_dec p' p then Some h else None
    | DFG_Join d _ =>
        match op (node_at g d) with
        | DFG_Drive p' _ _ => if eq_dec p' p then Some d else None
        | _ => None
        end
    | _ => None
    end.

  Definition drive_of (n: nid_t) : option nid_t :=
    match op (node_at g n) with
    | DFG_Sample p tok _ =>
        match op (node_at g tok) with
        | DFG_Stall _ h => drive_head p h
        | _ => drive_head p tok
        end
    | _ => None
    end.

  Definition payload_of (n: nid_t) : option nid_t :=
    match drive_of n with
    | Some d => match op (node_at g d) with DFG_Drive _ a _ => Some a | _ => None end
    | None => None
    end.

  (* FORWARD: a node from its arguments, as the hardware reads it.  An IP
     answer is [ip_fn] of its request, and zero when the call's path condition
     is false; a request reads its argument, and a stall or join reads zero. *)
  Definition step (k: known) (n: nid_t) : option (bits_t (node_sz g n)) :=
    match op (node_at g n) with
    | DFG_Const c => Some (Bits.of_nat _ c)
    | DFG_Stall _ _ | DFG_Join _ _ => Some Bits.zero
    | DFG_Drive _ a _ => option_map convert (k a)
    | DFG_Unary uop a => option_map (op1_bits uop _ _) (k a)
    | DFG_Resize a => option_map convert (k a)
    | DFG_Binary bop a b =>
        match k a, k b with
        | Some x, Some y => Some (op2_bits bop _ _ _ x y)
        | _, _ => None
        end
    | DFG_Phi c t e =>
        match k c with
        | Some x => if nonzero x then option_map convert (k t) else option_map convert (k e)
        | None => None
        end
    | DFG_Sample p _ en =>
        match guard_val k en with
        | Some true =>
            match payload_of n with
            | Some a => option_map (fun x => convert (ip_fn (ips p) (convert x))) (k a)
            | None => None
            end
        | Some false => Some Bits.zero
        | None => None
        end
    | _ => None
    end.

  Definition instances : list (decl_packet s_var i_var o_var p_var * decl_instance) :=
    flat_map (fun r => map (pair r) (dp_rule r g)) decls.

  (* BACKWARD: a packet's recovery, once its guard holds and its sources are known. *)
  Definition back (k: known) (n: nid_t) : option (bits_t (node_sz g n)) :=
    find_map
      (fun ri =>
         match Nat.eq_dec (di_target (snd ri)) n with
         | left e =>
             match guard_val k (di_guard (snd ri)) with
             | Some true =>
                 if forallb (fun s => match k s with Some _ => true | None => false end)
                            (di_sources (snd ri))
                 then Some (eq_rect _ (fun m => bits_t (node_sz g m))
                              (dp_extract (fst ri) g (snd ri) (fill k)) n e)
                 else None
             | _ => None
             end
         | right _ => None
         end)
      instances.

  Fixpoint recover (seed: known) (fuel: nat) (n: nid_t) : option (bits_t (node_sz g n)) :=
    match fuel with
    | 0 => None
    | S f =>
        match seed n with
        | Some v => Some v
        | None =>
            match step (recover seed f) n with
            | Some v => Some v
            | None => back (recover seed f) n
            end
        end
    end.

  (* Enough rounds for every chain the graph and the instances can form. *)
  Definition rounds : nat :=
    let m := S (length (graph g) + length instances) in m * m.
End Recover.

Section Seed.
  Context {s_var i_var o_var p_var: Type}.
  Context (i_sz: i_var -> nat) (o_sz: o_var -> nat).
  Context (g: @dfg_state_t s_var i_var o_var p_var).

  (* The published bits: public inputs, and public outputs before and after.
     An output's value after the action is its root's. *)
  Definition seed (sin: forall v, option (bits_t (i_sz v)))
      (spre spost: forall o, option (bits_t (o_sz o))) : known g :=
    fun n =>
      match
        match op (node_at g n) with
        | DFG_Input v => option_map convert (sin v)
        | DFG_Var (DFG_OVar o) => option_map convert (spre o)
        | _ => None
        end
      with
      | Some v => Some v
      | None =>
          find_map
            (fun e => match e with
                      | (DFG_OVar o, r) => if Nat.eqb r n then option_map convert (spost o) else None
                      | _ => None
                      end)
            (var_map g)
      end.
End Seed.
