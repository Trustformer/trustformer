(*! Loop !*)

Require Import Koika.Frontend.

Module Loop.
  Inductive reg_t := r0.
  Inductive rule_name_t := tick.

  Definition field_width := 32.

  Definition R r :=
    match r with
    | r0 => bits_t field_width
    end.

  Definition r idx : R idx :=
    match idx with
    | r0 => Bits.zero
    end.

  Definition _tick : uaction reg_t empty_ext_fn_t := {{
    let v := read0(r0) in write0(r0, v + |field_width`d1|)
  }}.

  Definition loop : scheduler :=
    tick |> done.

  Definition cr := ContextEnv.(create) r.

  (* Typechecking  *)
  Definition rules :=
    tc_rules R empty_Sigma (fun r => match r with tick => _tick end).

  Definition cycle_log :=
    tc_compute (interp_scheduler cr empty_sigma rules loop).

  Definition tick_result :=
    tc_compute (
      interp_action cr empty_sigma CtxEmpty log_empty log_empty (rules tick)
    ).

  Definition result := tc_compute (commit_update cr cycle_log).

  Definition external (r: rule_name_t) := false.

  Definition circuits := compile_scheduler rules external loop.
  Definition circuits_result :=
    tc_compute (
      interp_circuits empty_sigma circuits (lower_r (ContextEnv.(create) r))
    ).

  Example test:
    circuits_result = Environments.map _ (fun _ => bits_of_value) result
  := eq_refl.

  Definition package := {|
    ip_koika := {|
      koika_reg_types := R;
      koika_reg_init := r;
      koika_ext_fn_types := empty_Sigma;
      koika_rules := rules;
      koika_rule_external := external;
      koika_scheduler := loop;
      koika_module_name := "loop"
    |};
    ip_sim := {|
      sp_ext_fn_specs := empty_ext_fn_props;
      sp_prelude := None
    |};
    ip_verilog := {|
      vp_ext_fn_specs := empty_ext_fn_props
    |}
  |}.
End Loop.

Definition prog := Interop.Backends.register Loop.package.
