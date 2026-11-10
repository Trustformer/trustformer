(*! Computing terms of the Euclid sequence (Coq version) !*)
Require Import Koika.Frontend.

Module Euclid.
  Inductive reg_t := a | b.
  Inductive rule_name_t := pgcd.

  Definition logsz := 4.
  Notation sz := (pow2 logsz).

  Definition R (r: reg_t) := bits_t sz.

  Definition r idx : R idx :=
    match idx with
    | a => Bits.of_nat sz 15
    | b => Bits.of_nat sz 2
    end.

  Definition _pgcd : uaction reg_t empty_ext_fn_t := {{
    let v_a := read0(a) in
    let v_b := read0(b) in
    if v_a != Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0 then
      if v_a > v_b then
        write0(a, v_b);
        write0(b, v_a)
      else
        write0(a, v_a - v_b)
    else fail
  }}.

  (*! The design's schedule defines the order in which rules should (appear to) run !*)
  Definition euclid : scheduler :=
    pgcd |> done.

  (*! Rules are written in an untyped language, so we need to typecheck them: !*)
  Definition urules rule :=
    match rule with
    | pgcd => _pgcd
    end.

  Definition rules :=
    tc_rules
      R empty_Sigma
      (fun r =>
        match r with
        | pgcd => _pgcd
        end).

  (*! And now we can compute results: uncomment the ``Print`` commands below to show results. !*)

  Definition cr := ContextEnv.(create) r.

  Definition external (r: rule_name_t) := false.

  Definition circuits :=
    compile_scheduler rules external euclid.

  Definition circuits_result :=
    tc_compute (interp_circuits empty_sigma circuits (lower_r (ContextEnv.(create) r))).

  (*! This package configures compilation to C++ with Cuttlesim and Verilog with Kôika's verified compiler: !*)
  Definition package :=
    {| ip_koika := {| koika_reg_types := R;
                     koika_reg_init := r;
                     koika_ext_fn_types := empty_Sigma;
                     koika_rules := rules;
                     koika_rule_external := external;
                     koika_scheduler := euclid;
                     koika_module_name := "euclid" |};

       ip_sim := {| sp_ext_fn_specs := empty_ext_fn_props;
                   sp_prelude := None |};

       ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_props |} |}.
End Euclid.

(*! This is the entry point used by the compiler: !*)
Definition prog := Interop.Backends.register Euclid.package.
