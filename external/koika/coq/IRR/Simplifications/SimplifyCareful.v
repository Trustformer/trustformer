(* We used to have an explosion problem when simplifying non-ground
   terms of the siple form. This was due to the fact that functions
   implementing SBinops and SUnops were unfolded even when they should not have
   been. SimplifyCareful remedies to this issue by probing whether simplifications
   lead to this issue or not before applying them.

   It is closely related to SimplifyTargeted (which defines a simplification
   function which avoids simplifying at some locations which are passed as
   input). In fact, this file does not define simplification functions: it only
   contains Ltac definitions.  In particular, probe_simplifications does not
   modify the proof context. *)
Require Import Koika.BitsToLists.
Require Import Koika.IRR.IRR.
Require Import Koika.IRR.Direction.
Require Import Koika.IRR.Operations.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.IRR.Simplifications.SimplifyTargeted.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(* returns val, [positions of explosions] *)
Ltac probe_simplifications r sigma H pos :=
  lazymatch H with
  | @SIf ?rt ?eft ?c ?t ?f =>
    let c_ret := probe_simplifications r sigma c (branch1::pos) in
    let new_c := (eval vm_compute in (fst c_ret)) in
    let ec := (eval vm_compute in (snd c_ret)) in
    let t_ret := probe_simplifications r sigma t (branch2::pos) in
    let new_t := (eval vm_compute in (fst t_ret)) in
    let et := (eval vm_compute in (snd t_ret)) in
    let f_ret := probe_simplifications r sigma f (branch3::pos) in
    let new_f := (eval vm_compute in (fst f_ret)) in
    let ef := (eval vm_compute in (snd f_ret)) in
    match eval vm_compute in (eval_sact_no_vars r sigma new_c) with
    | Some (Bits [true]) => eval vm_compute in (new_t, ec ++ et)
    | Some (Bits [false]) => eval vm_compute in (new_f, ec ++ ef)
    | None =>
      eval vm_compute in (
        SIf (reg_t := rt) (ext_fn_t := eft) new_c new_t new_f, ec ++ et ++ ef
      )
    | _ =>
      eval vm_compute in (
        SIf (reg_t := rt) (ext_fn_t := eft) new_c new_t new_f,
        pos :: ec ++ et ++ ef
      )
    end
  | @SUnop ?rt ?eft ?fn ?arg =>
    let a_ret := probe_simplifications r sigma arg (branch1::pos) in
    let new_a := (eval vm_compute in (fst a_ret)) in
    let ea := (eval vm_compute in (snd a_ret)) in
    let res := (
      eval vm_compute in (eval_sact_no_vars r sigma (SUnop fn new_a))
    ) in
    match res with
    | Some (Bits (cons (match _ with _ => _ end) _)) =>
      eval vm_compute in
        (SUnop (reg_t := rt) (ext_fn_t := eft) fn new_a, pos :: ea)
    | Some ?x =>
      (eval vm_compute in (SConst (reg_t := rt) (ext_fn_t := eft) x, ea))
    | None =>
      eval vm_compute in (SUnop (reg_t := rt) (ext_fn_t := eft) fn new_a, ea)
    | _ =>
      eval vm_compute in
        (SUnop (reg_t := rt) (ext_fn_t := eft) fn new_a, pos :: ea)
    end
  | @SBinop ?rt ?eft ?fn ?arg1 ?arg2 =>
    let a1_ret := probe_simplifications r sigma arg1 (branch1::pos) in
    let new_a1 := (eval vm_compute in (fst a1_ret)) in
    let ea1 := (eval vm_compute in (snd a1_ret)) in
    let a2_ret := probe_simplifications r sigma arg2 (branch2::pos) in
    let new_a2 := (eval vm_compute in (fst a2_ret)) in
    let ea2 := (eval vm_compute in (snd a2_ret)) in
    let res := (
      eval vm_compute in
        (eval_sact_no_vars
          r sigma (SBinop (reg_t := rt) (ext_fn_t := eft) fn new_a1 new_a2))
    ) in
    lazymatch res with
    | Some (Bits (cons (match _ with _ => _ end) _)) =>
      eval vm_compute in
        (SBinop (reg_t := rt) (ext_fn_t := eft) fn new_a1 new_a2,
         pos :: ea1 ++ ea2)
    | Some ?x =>
      eval vm_compute in (SConst (reg_t := rt) (ext_fn_t := eft) x, ea1 ++ ea2)
    | None =>
      eval vm_compute in
        (SBinop (reg_t := rt) (ext_fn_t := eft) fn new_a1 new_a2, ea1 ++ ea2)
    | _ =>
      eval vm_compute in
        (SBinop (reg_t := rt) (ext_fn_t := eft) fn new_a1 new_a2,
         pos :: ea1 ++ ea2)
    end
  | @SExternalCall ?rt ?eft ?fn ?arg =>
    let a_ret := probe_simplifications r sigma arg (branch1::pos) in
    let new_a := (eval vm_compute in (fst a_ret)) in
    let ea := (eval vm_compute in (snd a_ret)) in
    let res := (
      eval vm_compute in (eval_sact_no_vars r sigma (SExternalCall fn new_a))
    ) in
    match res with
    | Some ?x =>
      eval vm_compute in (SConst (reg_t := rt) (ext_fn_t := eft) x, ea)
    | None => eval vm_compute in (SExternalCall fn new_a, ea)
    | _ => eval vm_compute in (SExternalCall fn new_a, pos :: ea)
    end
  | @SReg ?rt ?eft ?idx =>
    eval vm_compute in (H, (@nil Direction.position))
  | @SVar ?rt ?eft ?v =>
    eval vm_compute in (H, (@nil Direction.position))
  | @SConst ?rt ?eft ?c =>
    eval vm_compute in (H, (@nil Direction.position))
  | _ => idtac "ERROR: unexpected argument passed to probe_simplifications" H
  end.

Ltac probe_in_var r sigma i :=
  lazymatch i with
  | (_, (_, ?x)) =>
    let stac := probe_simplifications r sigma x (@nil Direction.direction) in
    eval vm_compute in (snd stac)
  | _ => idtac "ERROR: unexpected argument passed to apply_option" i
  end.

Ltac probe_in_vars r sigma vars :=
  lazymatch vars with
  | [] => eval vm_compute in (@Maps.PTree.empty (list Direction.position))
  | ?h :: ?t =>
    let exempted_h := probe_in_var r sigma h in
    let exempted_t := probe_in_vars r sigma t in
    eval vm_compute in (Maps.PTree.set (fst h) exempted_h exempted_t)
  end.

Ltac simplify_targeted protected :=
  erewrite simplify_sf_targeted_interp_cycle_ok with (e := protected); eauto.

Ltac simplify_careful_t :=
  lazymatch goal with
  | |- getenv ?REnv (interp_cycle ?ctx ?ext_sigma ?sf) _ = _ =>
    let vars := (eval vm_compute in (Maps.PTree.elements (vars sf))) in
    let protected := probe_in_vars ctx ext_sigma vars in
    simplify_targeted protected
  end.
