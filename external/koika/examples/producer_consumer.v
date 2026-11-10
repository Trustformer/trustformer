Require Import Koika.Frontend.

Module ProducerConsumer.
  (* 1. Parameterization *)
  Definition r_sz := pow2 2. (** Size of a standard register *)
  Definition q_id_sz := 4. (** Bits required to hold a queue index *)
  Definition q_cap := pow2 q_id_sz. (** Capacity of the queue *)

  (* Further down the line, the number of elements present in the queue will
   * have to be tracked. Note that a queue with capacity q with
   * q := pow2 q_id_sz could hold anywhere from [0, q] elements. This set
   * contains q + 1 elements, which means, given the way q and q_id_sz are
   * related, that the number of bits required to represent this information is
   * q_id_sz + 1. This would be a bit unwieldy, so the last element of the
   * queue is left unused. This way, the fill level of the queue can be
   * represented with the same type as the index type.
   * It should be possible to define a non pow2 q_cap directly but doing so led
   * me to other issues TODO.
   *)

  (* 2. Registers description *)
  (* 2.1. Names *)
  Inductive reg_t :=
  | producer_counter (** State of the producer, used to get varied outputs *)
  | queue_size (** Number of elements in the queue *)
  | queue_head (** Index of the head of the queue *)
  | queue_data (n : Vect.index q_cap) (** Contents of the queue (vector) *)
  | data_sink. (** Where consumer writes outputs *)

  (* 2.2. Memory requirements *)
  Definition R r :=
    match r with
    | producer_counter => bits_t r_sz
    | queue_head => bits_t q_id_sz
    | queue_size => bits_t q_id_sz
    | queue_data _ => bits_t r_sz
    | data_sink => bits_t r_sz
    end.

  (* 2.3. Initial values *)
  Definition r (reg: reg_t): R reg :=
    match reg with
    | producer_counter => Bits.zero
    | queue_size => Bits.zero
    | queue_head => Bits.zero
    | queue_data _ => Bits.zero
    | data_sink => Bits.zero
    end.

  (* Rules *)
  (* 3. Rules description *)
  (* 3.1. Names *)
  Inductive rule_name_t := produce | consume.

  (* 3.2. Definitions *)
  Definition write0_queue : UInternalFunction reg_t empty_ext_fn_t := {{
    fun write0_queue (idx : bits_t q_id_sz) (val: bits_t r_sz) : unit_t =>
      `UCompleteSwitch (SequentialSwitchTt) q_id_sz "idx"
        (fun idx => {{ write0(queue_data idx, val) }})`
    }}.

  Definition read1_queue idx : uaction reg_t empty_ext_fn_t := {{
    `UCompleteSwitch (SequentialSwitch (bits_t r_sz) "tmp") q_id_sz idx
      (fun idx => {{ read1(queue_data idx) }})`
  }}.

  Definition _produce : uaction reg_t empty_ext_fn_t := {{
    let qs := read0(queue_size) in
    let qh := read0(queue_head) in
    if (qs + #(Bits.of_nat q_id_sz 1)) != #(Bits.of_nat q_id_sz q_cap) then
      let v := read0(producer_counter) in
      write0_queue(qh, qs);
      write0(producer_counter, v + |r_sz`d1|);
      write0(queue_size, qs + |q_id_sz`d1|)
    else fail
  }}.

  Definition _consume : uaction reg_t empty_ext_fn_t := {{
    let qs := read1(queue_size) in
    let qh := read1(queue_head) in
    if qs != |q_id_sz`d0| then
      let v := `read1_queue("qh")` in
      write1(queue_size, qs - |q_id_sz`d1|);
      let next_qh :=
        if ((qh + |q_id_sz`d1|) == #(Bits.of_nat q_id_sz q_cap)) then
          |q_id_sz`d0|
        else qs + |q_id_sz`d1|
      in
      write1(queue_head, next_qh);
      write1(data_sink, v)
    else fail
  }}.

  (* 3.3. Rule name to definition mapping *)
  Definition rules :=
    tc_rules R empty_Sigma (fun r =>
      match r with
      | produce => _produce
      | consume => _consume
      end
    ).

  (* 4. Scheduler definition *)
  Definition pc_scheduler : scheduler := produce |> consume |> done.

  (* 5. Misc. *)
  Definition cr := ContextEnv.(create) r.

  (** Way of injecting Verilog code, disabled here *)
  Definition cycle_log :=
    tc_compute (interp_scheduler cr empty_sigma rules pc_scheduler).

  Definition produce_result :=
    tc_compute (
      interp_action cr empty_sigma CtxEmpty log_empty log_empty (rules produce)
    ).

  Definition consume_result :=
    tc_compute (
      interp_action cr empty_sigma CtxEmpty log_empty log_empty (rules consume)
    ).

  Definition result := tc_compute(commit_update cr cycle_log).

  Definition external (r : rule_name_t) := false.

  Definition circuits := compile_scheduler rules external pc_scheduler.

  Definition package := {|
    ip_koika := {|
      koika_reg_types := R;
      koika_reg_init reg := r reg;
      koika_ext_fn_types := empty_Sigma;
      koika_rules := rules;
      koika_rule_external := external;
      koika_scheduler := pc_scheduler;
      koika_module_name := "vector"
    |};
    ip_sim := {|
      sp_ext_fn_specs := empty_ext_fn_props;
      sp_prelude := None
    |};
    ip_verilog := {|
      vp_ext_fn_specs := empty_ext_fn_props
    |}
  |}.
End ProducerConsumer.

Definition prog := Interop.Backends.register ProducerConsumer.package.
Set Extraction Output Directory "extr".
Extraction "producer_consumer.ml" prog.
