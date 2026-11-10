(*! UART transmitter !*)
Require Import Koika.Frontend.
Require Import Koika.Std.

Module UART.
  Definition CLOCK_SPEED := 25_000_000%N.
  Definition BAUD_RATE := 115200%N.
  Definition _CLOCK_SCALE := (CLOCK_SPEED / BAUD_RATE)%N.
  Definition CLOCK_DELAY_BITS := N.to_nat (N.log2_up _CLOCK_SCALE).
  Definition CLOCK_DELAY := Bits.of_N CLOCK_DELAY_BITS (_CLOCK_SCALE - 1).

  Inductive reg_t :=
  | state
  | in_byte
  | in_byte_offset
  | out_bit
  | delay
  | last_write_ack
  | last_write_byte_ack
  | rstate
  | rclock_count
  | rbit_index
  | rrx_byte
  | dummy.

  Inductive ext_fn_t := ext_read_byte | ext_write_bit | ext_read_bit | ext_write_byte | ext_consume | ext_show_state.
  Inductive rule_name_t := read_input | transmit | rx.

  Definition tx_state :=
    {| enum_name := "tx_state";
       enum_members := ["idle"; "start"; "tx"; "finish"];
       enum_bitpatterns := [Ob~0~0; Ob~0~1; Ob~1~0; Ob~1~1] |}%vect.

  Definition rx_state :=
    {| enum_name := "rx_state";
       enum_members := ["idle"; "start"; "rx"; "finish";"cleanup"];
       enum_bitpatterns := [Ob~0~0~0; Ob~0~0~1; Ob~0~1~0; Ob~0~1~1; Ob~1~0~0] |}%vect.


  Definition R r :=
    match r with
    | state => enum_t tx_state
    | in_byte => bits_t 8
    | in_byte_offset => bits_t 3
    | out_bit => bits_t 1
    | delay => bits_t CLOCK_DELAY_BITS
    | last_write_ack => bits_t 1
    | last_write_byte_ack => bits_t 1
    | rstate => enum_t rx_state
    | rclock_count => bits_t 8
    | rbit_index => bits_t 3
    | rrx_byte => bits_t 8
    | dummy => bits_t 1
    end.

  Definition r idx : R idx :=
    match idx with
    | state => Ob~0~0
    | in_byte => Bits.zero
    | in_byte_offset => Bits.zero
    | out_bit => Ob~1
    | delay => Bits.zero
    | last_write_ack => Bits.zero
    | last_write_byte_ack => Bits.zero
    | rstate => Ob~0~0~0
    | rclock_count => Bits.zero
    | rbit_index => Bits.zero
    | rrx_byte => Bits.zero
    | dummy => Bits.zero
    end.

  Definition Sigma (fn: ext_fn_t) :=
    match fn with
    | ext_read_byte => {$ bits_t 1 ~> maybe (bits_t 8) $}
    | ext_write_bit => {$ bits_t 1 ~> bits_t 1 $}
    | ext_write_byte => {$ maybe (bits_t 8) ~> bits_t 1 $}
    | ext_read_bit => {$ bits_t 1 ~> bits_t 1 $}
    | ext_consume => {$ bits_t 1 ~> bits_t 1 $}
    | ext_show_state => {$ enum_t rx_state ~> bits_t 1 $}
    end.

  Definition _read_input : uaction reg_t ext_fn_t :=
    {{
        let ready := read1(state) == enum tx_state { idle } in
        let opt_byte := extcall ext_read_byte(ready) in
        (when ready && get(opt_byte, valid) do
           write1(in_byte, get(opt_byte, data));
           write1(state, enum tx_state { start }))
    }}.


  Definition _rx : uaction reg_t ext_fn_t :=
    {{
        let state := read0(rstate) in
        write0(dummy, extcall ext_show_state(state));
        let new_opt_data :=
          struct (Maybe (bits_t 8)) {
              valid := if state == enum rx_state {cleanup} then Ob~1 else Ob~0;
              data := read0(rrx_byte)
            } in
        let data := extcall ext_read_bit(Ob~1) in
        let new_rx_byte := read0(rrx_byte) in
        match state with
        | enum rx_state { idle } =>
            (write1(rclock_count, |8`d0|);
             write1(rbit_index, |3`d0|);
             set new_rx_byte := |8`d65|;
             if data == Ob~0 then write1(rstate, enum rx_state {start}) else pass
            )
        | enum rx_state { start } =>
            if data == Ob~0
            then
              (if read0(rclock_count) == |8`d((_CLOCK_SCALE - 1) / 2)|
               then (
                   write1(rclock_count, |8`d0|);
                   write1(rstate, enum rx_state { rx });

                   set new_rx_byte := |8`d0|
                 )
               else (
                   write1(rclock_count, read0(rclock_count) + |8`d1|)
                 )
              )
            else write1(rstate, enum rx_state { idle })
    | enum rx_state { rx } =>
        if read0(rclock_count) < #CLOCK_DELAY
        then
          ( write1(rclock_count, read0(rclock_count) + |8`d1|))
        else
          (write1(rclock_count, |8`d0|);
           let idx := read0(rbit_index) in
           let byte := read0(rrx_byte) in
           (* let byte := byte << Ob~1 + zeroExtend(data, 8) in *)
           let byte := byte + (zeroExtend(data,8) << idx) in
           set new_rx_byte := byte;
           if idx < |3`d7|
           then write1(rbit_index, idx + Ob~0~0~1)
           else (write1(rbit_index, |3`d0|);
                 write1(rstate, enum rx_state { finish })
                )
          )
    | enum rx_state { finish } =>
        if read0(rclock_count) < #CLOCK_DELAY
        then
          ( write1(rclock_count, read0(rclock_count) + |8`d1|))
        else
          (write1(rclock_count, |8`d0|);
           write1(rstate, enum rx_state { cleanup })
          )
    | enum rx_state { cleanup } =>
        (if extcall ext_consume( Ob~0 ) == Ob~1 then
           (write1(rstate, enum rx_state { idle }))
         else pass
        )
          return default: pass
        end;
        write1(rrx_byte, new_rx_byte);
        write1(last_write_byte_ack, extcall ext_write_byte( new_opt_data ))
     }}.


  Definition _transmit : uaction reg_t ext_fn_t :=
    {{
        let bit := read0(out_bit) in
        let state := read0(state) in
        (if read0(delay) == |CLOCK_DELAY_BITS`d0| then
          match state with
          | enum tx_state { start } =>
            (set bit := Ob~0;
             set state := enum tx_state { tx })
          | enum tx_state { tx } =>
            let bits := read0(in_byte) in
            let offset := read0(in_byte_offset) in
            let last_char := offset == Ob~1~1~1 in
            set bit := bits[Ob~0~0~0];
            write0(in_byte, bits >> Ob~1);
            write0(in_byte_offset, offset + Ob~0~0~1);
            (when last_char do
               set state := enum tx_state { finish })
          | enum tx_state { finish } =>
            (set bit := Ob~1;
             set state := enum tx_state { idle })
          return default: pass
          end;
          write0(delay, #CLOCK_DELAY)
        else
          write0(delay, read0(delay) - |CLOCK_DELAY_BITS`d1|));
        write0(out_bit, bit);
        write0(state, state);
        (* last_write_ack prevents the write from being optimized out *)
        write0(last_write_ack, extcall ext_write_bit(bit))
    }}.

  Definition uart : scheduler :=
    transmit |> read_input |> rx |> done.

  Definition cr := ContextEnv.(create) r.

  (* Typechecking  *)
  Definition rules :=
    tc_rules R Sigma
             (fun r => match r with
                    | read_input => _read_input
                    | transmit => _transmit
                    | rx => _rx
                    end).

  Definition ext_fn_specs (fn : ext_fn_t) :=
    match fn with
    | ext_read_byte => {| efr_name := "read_byte"; efr_internal := false |}
    | ext_write_bit => {| efr_name := "write_bit"; efr_internal := false |}
    | ext_write_byte => {| efr_name := "write_byte"; efr_internal := false |}
    | ext_read_bit => {| efr_name := "read_bit"; efr_internal := false |}
    | ext_consume => {| efr_name := "consume"; efr_internal := false |}
    | ext_show_state => {| efr_name := "show_state"; efr_internal := false |}
    end.

  Definition package :=
    {| ip_koika := {| koika_reg_types := R;
                     koika_reg_init := r;
                     koika_ext_fn_types := Sigma;
                     koika_rules := rules;
                     koika_rule_external := (fun _ => false);
                     koika_scheduler := uart;
                     koika_module_name := "uart" |};

       ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                   sp_prelude := None |};

       ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.
End UART.

Definition prog := Interop.Backends.register UART.package.
Set Extraction Output Directory "examples_extr".
Extraction "uart.ml" prog.
