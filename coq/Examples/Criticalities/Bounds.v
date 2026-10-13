(*! Static comparison of the three phi criticalities for every design in
    [Designs]: per action, the best and worst cycle count ([Audit]'s bounds
    under each mode's taint) and the branch conditions the mode pads.
    [report] is CSV; extract and run it, the walk is too slow for [vm_compute]. !*)

Require Import Koika.Frontend.
Require Import Koika.Utils.Common.
Require Import Trustformer.Contract.
Require Import Trustformer.Scheduler.Schedule.
Require Import Trustformer.Scheduler.Audit.
Require Import Trustformer.Backend.Lowering.
Require Trustformer.Examples.Criticalities.Designs.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Local Infix "+++" := String.append (at level 60, right associativity).

(* [Ours] is the taint analysis; the other two are [EvalModes]'s baselines. *)
Inductive mode := NoCrit | Ours | AllCrit.

Section Modes.

  Context (ctx: TFSchedContext).
  Context (cost: nat).

  Local Notation dfg_state :=
    (@dfg_state_t (tfs_spec_states ctx) (tfs_spec_inputs ctx) (tfs_spec_outputs ctx) (tfs_spec_ips ctx)).

  Definition mode_taint (m: mode) (dfg: dfg_state) : list nid_t :=
    match m with
    | NoCrit => []
    | Ours => Taint.get_tainted ctx dfg
    | AllCrit => map nid (graph dfg)
    end.

  Definition mode_facts (m: mode) (dfg: dfg_state) : list gfact :=
    match m with
    | Ours => Taint.decl_facts ctx dfg
    | _ => []
    end.

  (* [action_bounds_w] with the mode's taint and facts in place of the real ones. *)
  Definition mode_bounds_w (m: mode) (dfg: dfg_state) : wcycle * wcycle :=
    let tainted := mode_taint m dfg in
    let dfacts := mode_facts m dfg in
    let bufs := Buffers.require_buffer ctx dfg (Cost.calc_target_cycle cost (Cost.calc_backward_cost ctx cost dfg)) in
    let '(l, u) :=
      fold_left (fun '(l, u) v =>
                   let '(lv, uv) :=
                     node_bounds_w ctx dfg tainted dfacts bufs [] (List.length (graph dfg)) (snd v) in
                   (wmax_lo l lv, wmax u uv))
                (var_map dfg) ((0, []), (0, [])) in
    ((S (fst l), snd l), (S (fst u), snd u)).

  Lemma mode_bounds_ours (dfg: dfg_state) : mode_bounds_w Ours dfg = action_bounds_w ctx cost dfg.
  Proof. reflexivity. Qed.

  (* The walk above revisits shared nodes once per path, exponential on the hash
     designs.  Its numbers depend on the path only through [declassified_at],
     which reads only guard literals, so memoising on (node, path cut to guard
     literals) gives the same bounds and the same critical conditions. *)
  Section Fast.

    Context (dfg: dfg_state) (tainted: list nid_t) (dfacts: list gfact).
    Context (bufs: list nid_t).

    Definition guard_lits : list lit := flat_map snd dfacts.
    Definition cut (pi: list lit) : list lit := filter (fun a => lit_in a guard_lits) pi.

    Definition key := (nid_t * list lit)%type.
    Definition key_eqb (a b: key) : bool :=
      Nat.eqb (fst a) (fst b)
      && (Nat.eqb (List.length (snd a)) (List.length (snd b))
          && forallb (fun '(x, y) => Taint.lit_eqb x y) (combine (snd a) (snd b))).

    Definition lookup {A} (k: key) (memo: list (key * A)) : option A :=
      option_map snd (find (fun e => key_eqb (fst e) k) memo).

    Fixpoint fast_bounds (fuel: nat) (pi: list lit) (n: nid_t) (memo: list (key * (nat * nat)))
      : (nat * nat) * list (key * (nat * nat)) :=
      match fuel with
      | 0 => ((0, 0), memo)
      | S fuel' =>
          match lookup (n, pi) memo with
          | Some b => (b, memo)
          | None =>
              let node := nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |} in
              let delay := if existsb (Nat.eqb n) bufs
                           then match op node with DFG_Stall l _ => l | _ => 1 end else 0 in
              let one a m := fast_bounds fuel' pi a m in
              let both (x: (nat * nat) * list (key * (nat * nat))) m :=
                let '((l1, u1), m1) := x in
                let '((l2, u2), m2) := fast_bounds fuel' pi m m1 in
                ((Nat.max l1 l2, Nat.max u1 u2), m2) in
              let '((l, u), memo') :=
                match op node with
                | DFG_Unary _ a | DFG_Resize a | DFG_Stall _ a => one a memo
                | DFG_Sample _ t _ => one t memo
                | DFG_Binary _ a1 a2 | DFG_Join a1 a2 => both (one a1 memo) a2
                | DFG_Drive _ a en => fold_left (fun x g => both x (fst g)) en (one a memo)
                | DFG_Phi c t e =>
                    let crit := Codegen.phi_crit tainted dfacts c pi in
                    let '((lc, uc), m1) := fast_bounds fuel' pi c memo in
                    let '((lt, ut), m2) := fast_bounds fuel' (cut (Codegen.phi_path crit c true pi)) t m1 in
                    let '((le, ue), m3) := fast_bounds fuel' (cut (Codegen.phi_path crit c false pi)) e m2 in
                    ((Nat.max lc (if crit then Nat.max lt le else Nat.min lt le),
                      Nat.max uc (Nat.max ut ue)), m3)
                | _ => ((0, 0), memo)
                end in
              let b := (l + delay, u + delay) in
              (b, ((n, pi), b) :: memo')
          end
      end.

    (* Every (node, cut path) the critical-phi report visits, once each. *)
    Fixpoint fast_conds (fuel: nat) (pi: list lit) (n: nid_t) (seen: list key) (acc: list nid_t)
      : list key * list nid_t :=
      match fuel with
      | 0 => (seen, acc)
      | S fuel' =>
          if existsb (key_eqb (n, pi)) seen then (seen, acc)
          else
            let seen := (n, pi) :: seen in
            let node := nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |} in
            match op node with
            | DFG_Unary _ a | DFG_Resize a | DFG_Stall _ a | DFG_Drive _ a _ =>
                fast_conds fuel' pi a seen acc
            | DFG_Sample _ t _ => fast_conds fuel' pi t seen acc
            | DFG_Binary _ a1 a2 | DFG_Join a1 a2 =>
                let '(s1, c1) := fast_conds fuel' pi a1 seen acc in fast_conds fuel' pi a2 s1 c1
            | DFG_Phi c t e =>
                let crit := Codegen.phi_crit tainted dfacts c pi in
                let acc := if crit then c :: acc else acc in
                let '(s1, c1) := fast_conds fuel' pi c seen acc in
                let '(s2, c2) := fast_conds fuel' (cut (Codegen.phi_path crit c true pi)) t s1 c1 in
                fast_conds fuel' (cut (Codegen.phi_path crit c false pi)) e s2 c2
            | _ => (seen, acc)
            end
      end.

  End Fast.

  Definition mode_bounds (m: mode) (dfg: dfg_state) : nat * nat :=
    let tainted := mode_taint m dfg in
    let dfacts := mode_facts m dfg in
    let bufs := Buffers.require_buffer ctx dfg (Cost.calc_target_cycle cost (Cost.calc_backward_cost ctx cost dfg)) in
    let fuel := List.length (graph dfg) in
    let '((l, u), _) :=
      fold_left (fun '((l, u), memo) v =>
                   let '((lv, uv), memo') := fast_bounds dfg tainted dfacts bufs fuel [] (snd v) memo in
                   ((Nat.max l lv, Nat.max u uv), memo'))
                (var_map dfg) ((0, 0), []) in
    (S l, S u).

  Definition mode_conds (m: mode) (dfg: dfg_state) : list nid_t :=
    let tainted := mode_taint m dfg in
    let dfacts := mode_facts m dfg in
    let fuel := List.length (graph dfg) in
    nodup Nat.eq_dec
      (snd (fold_left (fun '(seen, acc) v => fast_conds dfg tainted dfacts fuel [] (snd v) seen acc)
                      (var_map dfg) ([], []))).

  (* The latency under one outcome per branch condition: a phi on a [crit] condition
     waits for both arms, any other takes the arm [asg] selects. *)
  Section Exact.

    Context (dfg: dfg_state) (bufs: list nid_t) (crit: list nid_t) (asg: nid_t -> bool).

    Fixpoint exact_lat (fuel: nat) (n: nid_t) (memo: list (nid_t * nat)) : nat * list (nid_t * nat) :=
      match fuel with
      | 0 => (0, memo)
      | S fuel' =>
          match find (fun e => Nat.eqb (fst e) n) memo with
          | Some (_, t) => (t, memo)
          | None =>
              let node := nth n (graph dfg) {| nid := 0; op := DFG_Empty; sz := 0 |} in
              let delay := if existsb (Nat.eqb n) bufs
                           then match op node with DFG_Stall l _ => l | _ => 1 end else 0 in
              let one a m := exact_lat fuel' a m in
              let both (x: nat * list (nid_t * nat)) b :=
                let '(t1, m1) := x in let '(t2, m2) := exact_lat fuel' b m1 in (Nat.max t1 t2, m2) in
              let '(t, memo') :=
                match op node with
                | DFG_Unary _ a | DFG_Resize a | DFG_Stall _ a => one a memo
                | DFG_Sample _ t _ => one t memo
                | DFG_Binary _ a1 a2 | DFG_Join a1 a2 => both (one a1 memo) a2
                | DFG_Drive _ a en => fold_left (fun x g => both x (fst g)) en (one a memo)
                | DFG_Phi c t e =>
                    if existsb (Nat.eqb c) crit then both (both (one c memo) t) e
                    else both (one c memo) (if asg c then t else e)
                | _ => (0, memo)
                end in
              (t + delay, (n, t + delay) :: memo')
          end
      end.

  End Exact.

  Definition action_lat (m: mode) (dfg: dfg_state) (asg: nid_t -> bool) : nat :=
    let bufs := Buffers.require_buffer ctx dfg (Cost.calc_target_cycle cost (Cost.calc_backward_cost ctx cost dfg)) in
    let crit := mode_conds m dfg in
    S (fst (fold_left (fun '(t, memo) v =>
                         let '(tv, memo') := exact_lat dfg bufs crit asg (List.length (graph dfg)) (snd v) memo in
                         (Nat.max t tv, memo'))
                      (var_map dfg) (0, []))).

  Fixpoint all_bools (k: nat) : list (list bool) :=
    match k with
    | 0 => [[]]
    | S k' => flat_map (fun l => [false :: l; true :: l]) (all_bools k')
    end.

  Definition assign (conds: list nid_t) (vals: list bool) (rest: nid_t -> bool) : nid_t -> bool :=
    fun n => match find (fun e => Nat.eqb (fst e) n) (combine conds vals) with
             | Some (_, b) => b
             | None => rest n
             end.

  (* Every outcome of up to 12 secret conditions; beyond that all-false, all-true
     and each single flip. *)
  Definition secret_outcomes (k: nat) : list (list bool) :=
    if Nat.leb k 12 then all_bools k
    else repeat true k :: map (fun i => map (Nat.eqb i) (seq 0 k)) (seq 0 k)
                       ++ map (fun i => map (fun j => negb (Nat.eqb i j)) (seq 0 k)) (seq 0 k).

  Definition secret_conds (dfg: dfg_state) : list nid_t := mode_conds Ours dfg.
  Definition public_conds (dfg: dfg_state) : list nid_t :=
    filter (fun c => negb (existsb (Nat.eqb c) (secret_conds dfg))) (mode_conds AllCrit dfg).

  Fixpoint find_some {A B} (f: A -> option B) (l: list A) : option B :=
    match l with
    | [] => None
    | x :: l' => match f x with Some y => Some y | None => find_some f l' end
    end.

  Definition flip (vals: list bool) (i: nat) : list bool :=
    map (fun '(j, b) => if Nat.eqb i j then negb b else b) (combine (seq 0 (List.length vals)) vals).

  (* A leak witness: a public outcome [p], a secret outcome [s], and a secret condition
     [i] whose flip alone changes the latency, from [t] to [t']; the largest change wins. *)
  Record witness_t := { w_pub : list bool; w_sec : list bool; w_flip : nat; w_lat : nat; w_lat' : nat }.

  Definition witness (m: mode) (dfg: dfg_state) : option witness_t :=
    let secs := secret_conds dfg in
    let pubs := public_conds dfg in
    let k := List.length secs in
    let lat p s := action_lat m dfg (assign secs s (assign pubs p (fun _ => false))) in
    let gap a b := if Nat.ltb a b then b - a else a - b in
    let better (best: option witness_t) (w: witness_t) :=
      match best with
      | Some v => if Nat.ltb (gap (w_lat v) (w_lat' v)) (gap (w_lat w) (w_lat' w)) then Some w else best
      | None => if Nat.eqb (w_lat w) (w_lat' w) then None else Some w
      end in
    find_some (fun s =>
      fold_left (fun best p =>
        let t := lat p s in
        fold_left (fun best i =>
          better best {| w_pub := p; w_sec := s; w_flip := i; w_lat := t; w_lat' := lat p (flip s i) |})
          (seq 0 k) best)
        (all_bools (List.length pubs)) None)
      (repeat false k :: secret_outcomes k).

  (* The mode leaks when, for some outcome of the public conditions, two outcomes of
     the secret ones (those [Ours] protects) give different latencies; [witness] then
     finds one secret flip that shows it. *)
  Definition leaks (m: mode) (dfg: dfg_state) : bool :=
    let secs := secret_conds dfg in
    let pubs := public_conds dfg in
    existsb (fun p =>
               let lat s := action_lat m dfg (assign secs s (assign pubs p (fun _ => false))) in
               let t0 := lat (repeat false (List.length secs)) in
               existsb (fun s => negb (Nat.eqb (lat s) t0)) (secret_outcomes (List.length secs)))
            (all_bools (List.length pubs)).

  Definition row (design: string) (name: string) (act: tfs_spec_action ctx) : string :=
    let dfg := Build.build_dfg ctx act in
    let b m := let '(lo, hi) := mode_bounds m dfg in show lo +++ "," +++ show hi in
    let l m := if leaks m dfg then "1" else "0" in
    design +++ "," +++ name +++ "," +++ b NoCrit +++ "," +++ b Ours +++ "," +++ b AllCrit +++ ","
      +++ show (List.length (mode_conds AllCrit dfg)) +++ ","
      +++ show (List.length (mode_conds Ours dfg)) +++ ","
      +++ l NoCrit +++ "," +++ l Ours +++ "," +++ l AllCrit +++ String (Ascii.ascii_of_nat 10) "".

  Definition design_rows (design: string) (nm: tfs_spec_action ctx -> string) : string :=
    fold_left (fun acc a => acc +++ row design (nm a) a) (@finite_elements _ (tfs_spec_action_fin ctx)) "".

  Definition mode_name (m: mode) : string :=
    match m with NoCrit => "none" | Ours => "taint" | AllCrit => "all" end.

  (* Per leaking action and mode: the latency with the flipped secret condition true and
     false, the public outcomes, and the other secret conditions held true. *)
  Definition witness_text (design name: string) (act: tfs_spec_action ctx) : string :=
    let dfg := Build.build_dfg ctx act in
    let nl := String (Ascii.ascii_of_nat 10) "" in
    let secs := secret_conds dfg in
    fold_left (fun acc m =>
      if negb (leaks m dfg) then acc
      else acc +++ design +++ " " +++ name +++ " (" +++ mode_name m +++ "): " +++
        match witness m dfg with
        | None => "leaks, no single-flip witness among the outcomes searched" +++ nl
        | Some w =>
            let c := nth (w_flip w) secs 0 in
            let on := nth (w_flip w) (w_sec w) false in
            let t_true := if on then w_lat w else w_lat' w in
            let t_false := if on then w_lat' w else w_lat w in
            let others := filter (fun l => snd l && negb (Nat.eqb (fst l) c)) (combine secs (w_sec w)) in
            let cyc t := show t +++ (if Nat.eqb t 1 then " cycle" else " cycles") in
            cyc t_true +++ " when " +++ show_path ctx dfg [(c, true)] +++ ", "
              +++ cyc t_false +++ " when not" +++ nl
            +++ "  public: " +++ show_path ctx dfg (combine (public_conds dfg) (w_pub w)) +++ nl
            +++ "  other secret conditions true: "
            +++ (match others with [] => "none" | _ => show_path ctx dfg others end) +++ nl
        end) [NoCrit; Ours; AllCrit] "".

  Definition design_witnesses (design: string) (nm: tfs_spec_action ctx -> string) : string :=
    fold_left (fun acc a => acc +++ witness_text design (nm a) a) (@finite_elements _ (tfs_spec_action_fin ctx)) "".

  (* [crit_report_all]'s walk under the mode's taint, for [fast_agrees]. *)
  Definition walk_conds (m: mode) (dfg: dfg_state) : list nid_t :=
    nodup Nat.eq_dec
      (map cr_cond
        (flat_map (fun v => crit_report_aux ctx dfg (mode_taint m dfg) (mode_facts m dfg) []
                              (List.length (graph dfg)) (snd v) [])
                  (var_map dfg))).

  (* The memoised bounds and conditions against the walks, every action and mode:
     the check that pins them together on designs small enough for the walk. *)
  Definition fast_agrees : bool :=
    forallb (fun act =>
               let dfg := Build.build_dfg ctx act in
               forallb (fun m => let '((lo, _), (hi, _)) := mode_bounds_w m dfg in
                                 let '(lo', hi') := mode_bounds m dfg in
                                 Nat.eqb lo lo' && Nat.eqb hi hi'
                                 && Nat.eqb (List.length (walk_conds m dfg))
                                            (List.length (mode_conds m dfg)))
                       [NoCrit; Ours; AllCrit])
            (@finite_elements _ (tfs_spec_action_fin ctx)).

End Modes.

(* Reads ctx and cost off the schedule, as [EvalModes.baseline] does. *)
Ltac on_sched sched k :=
  let s := eval red in sched in
  lazymatch s with
  | tfs_schedule ?ctx ?cost => k ctx cost
  end.

(* Every design at the running example's cost limit (Examples/LockboxTries). *)
Definition report_cost := 4.

(* [f] (design_rows or design_witnesses) for one design, read off its schedule. *)
Ltac each f design sched tf :=
  on_sched sched ltac:(fun ctx _ => exact (f ctx report_cost design (@show _ (tf_action_names tf)))).

Ltac each_nm f design sched nm :=
  on_sched sched ltac:(fun ctx _ => exact (f ctx report_cost design nm)).

Definition lockbox_names (a: LockboxTries.Spec.fs_action) : string :=
  match a with
  | LockboxTries.Spec.fs_act_set => "act_set"
  | LockboxTries.Spec.fs_act_test => "act_test"
  end.

Ltac agrees sched :=
  on_sched sched ltac:(fun ctx cost => exact (fast_agrees ctx cost)).

(* The protected modes never leak; the unprotected one does on Fig2Backup's pin check. *)
Ltac leak_free sched :=
  on_sched sched ltac:(fun ctx cost =>
    exact (forallb (fun act => let dfg := Build.build_dfg ctx act in
                               negb (leaks ctx cost Ours dfg) && negb (leaks ctx cost AllCrit dfg))
                   (@finite_elements _ (tfs_spec_action_fin ctx)))).

Example protected_modes_never_leak_small :
  forallb (fun b => b)
    [ltac:(leak_free Designs.lockboxtries_sched); ltac:(leak_free Designs.lockboxtries_public_sched);
     ltac:(leak_free Designs.adder_sched); ltac:(leak_free Designs.counter_sched);
     ltac:(leak_free Designs.fifo_sched); ltac:(leak_free Designs.fifo1_sched);
     ltac:(leak_free Designs.fig2backup_sched); ltac:(leak_free Designs.lockbox_sched);
     ltac:(leak_free Designs.multilockbox_sched)] = true.
Proof. vm_compute. reflexivity. Qed.

Example unprotected_pin_check_leaks :
  ltac:(on_sched Designs.fig2backup_sched ltac:(fun ctx _ =>
    exact (leaks ctx 4 NoCrit (Build.build_dfg ctx Knox.Fig2Backup.Spec.act_retrieve)))) = true.
Proof. vm_compute. reflexivity. Qed.

Example fast_agrees_small :
  forallb (fun b => b)
    [ltac:(agrees Designs.lockboxtries_sched); ltac:(agrees Designs.lockboxtries_public_sched);
     ltac:(agrees Designs.adder_sched); ltac:(agrees Designs.counter_sched);
     ltac:(agrees Designs.fifo_sched); ltac:(agrees Designs.fifo1_sched);
     ltac:(agrees Designs.fig2backup_sched); ltac:(agrees Designs.lockbox_sched);
     ltac:(agrees Designs.multilockbox_sched)] = true.
Proof. vm_compute. reflexivity. Qed.

(* The suite in table order: the running example, the Knox designs, MARS. *)
Ltac suite f :=
  exact (""
  +++ ltac:(each f "Example_LockboxTries" Designs.lockboxtries_sched LockboxTries.Spec.tf_ctx)
  +++ ltac:(each_nm f "Example_LockboxTries_public" Designs.lockboxtries_public_sched lockbox_names)
  +++ ltac:(each f "Knox_Adder" Designs.adder_sched Knox.Adder.Spec.tf_ctx)
  +++ ltac:(each f "Knox_Counter" Designs.counter_sched Knox.Counter.Spec.tf_ctx)
  +++ ltac:(each f "Knox_Fifo" Designs.fifo_sched Knox.Fifo.Spec.tf_ctx)
  +++ ltac:(each f "Knox_Fifo1" Designs.fifo1_sched Knox.Fifo1.Spec.tf_ctx)
  +++ ltac:(each f "Knox_Fig2Backup" Designs.fig2backup_sched Knox.Fig2Backup.Spec.tf_ctx)
  +++ ltac:(each f "Knox_Lockbox" Designs.lockbox_sched Knox.Lockbox.Spec.tf_ctx)
  +++ ltac:(each f "Knox_MultiLockbox" Designs.multilockbox_sched Knox.MultiLockbox.Spec.tf_ctx)
  +++ ltac:(each f "Knox_Otp" Designs.otp_sched Knox.Otp.Spec.tf_ctx)
  +++ ltac:(each f "Knox_PwHasher" Designs.pwhasher_sched Knox.PasswordHasher.Spec.tf_ctx)
  +++ ltac:(each f "Knox_PinBackup" Designs.pinbackup_sched Knox.PinBackup.Spec.tf_ctx)
  +++ ltac:(each f "Example_MarsV2" Designs.marsv2_sched Designs.marsv2_tf)).

Definition report : string :=
  "design,action,lo_nocrit,hi_nocrit,lo_ours,hi_ours,lo_allcrit,hi_allcrit,branch_conds,secret_conds,leak_nocrit,leak_ours,leak_allcrit"
  +++ String (Ascii.ascii_of_nat 10) "" +++ ltac:(suite design_rows).

Definition witnesses : string := ltac:(suite design_witnesses).
