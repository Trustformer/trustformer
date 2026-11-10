(*! Language | Logs of reads and writes !*)
Require Export Koika.Utils.Common.
Require Export Koika.Utils.Environments.
Require Export Koika.KoikaForm.Syntax.
Require Export Koika.KoikaForm.Typed.TypedSyntax.

Section Logs.
  Context {reg_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.
  Context {R: reg_t -> Type}.
  Context {REnv: Env reg_t}.

  Inductive LogEntryKind := LogRead | LogWrite.

  Record LogEntry := LE {
    reg: reg_t;
    kind: LogEntryKind;
    port: Port;
    val:
      match kind with
      | LogRead => unit: Type
      | LogWrite => R reg
      end
  }.

  Definition RLog := list (@LogEntry).
  Definition _Log := list LogEntry.
  Notation Log := _Log.

  Definition log_empty : Log := [].
  Definition log_app (l1 l2: Log) := l1 ++ l2.

  Definition log_find {T} (log: Log) r (f: LogEntry -> option T) : option T :=
    list_find_opt (fun le => if eq_dec (reg le) r then f le else None) log.

  Definition log_cons le (l: Log) := (le :: l).

  Definition log_forallb (log: Log) reg (f: LogEntryKind -> Port -> bool) :=
    List.forallb (
      fun '(LE r kind prt _) => if eq_dec r reg then f kind prt else true
    ) log.

  Definition log_existsb (log: Log) reg (f: LogEntryKind -> Port -> bool) :=
    List.existsb (
      fun '(LE r kind prt _) => if eq_dec r reg then f kind prt else false
    ) log.

  Definition is_read0 kind prt :=
    match kind, prt with
    | LogRead, P0 => true
    | _, _ => false
    end.

  Definition is_read1 kind prt :=
    match kind, prt with
    | LogRead, P1 => true
    | _, _ => false
    end.

  Definition is_write0 kind prt :=
    match kind, prt with
    | LogWrite, P0 => true
    | _, _ => false
    end.

  Definition is_write1 kind prt :=
    match kind, prt with
    | LogWrite, P1 => true
    | _, _ => false
    end.

  Open Scope bool_scope.

  Definition may_read (sched_log: Log) prt idx :=
    match prt with
    | P0 => negb (log_existsb sched_log idx is_write0)
              && negb (log_existsb sched_log idx is_write1)
    | P1 => negb (log_existsb sched_log idx is_write1)
    end.

  Definition log_latest_write0_fn idx (le: LogEntry) : option (R idx).
    destruct le. destruct kind0. exact None.
    destruct port0 eqn:?.
    destruct (eq_dec reg0 idx). subst.
    exact (Some val0).
    exact None.
    exact None.
  Defined.

  Definition latest_write0 (log: Log) idx : option (R idx) :=
    log_find log idx (log_latest_write0_fn idx).

  Definition log_latest_write1_fn idx (le: LogEntry) : option (R idx).
    destruct le. destruct kind0 eqn:?. exact None.
    destruct port0 eqn:?. exact None.
    destruct (eq_dec reg0 idx). subst.
    exact (Some val0).
    exact None.
  Defined.

  Definition latest_write1 (log: Log) idx : option (R idx) :=
    log_find log idx (log_latest_write1_fn idx).

  Definition may_write (sched_log rule_log: Log) prt idx :=
    match prt with
    | P0 => negb (log_existsb (log_app rule_log sched_log) idx is_read1) &&
           negb (log_existsb (log_app rule_log sched_log) idx is_write0) &&
           negb (log_existsb (log_app rule_log sched_log) idx is_write1)
    | P1 => negb (log_existsb (log_app rule_log sched_log) idx is_write1)
    end.

  Definition log_latest_write_fn idx (le: LogEntry) : option (R idx).
    destruct le. destruct kind0 eqn:?. exact None.
    destruct (eq_dec reg0 idx). subst.
    exact (Some val0).
    exact None.
  Defined.

  Definition latest_write (log: Log) idx : option (R idx) :=
    log_find log idx (log_latest_write_fn idx).

  Definition commit_update (r0: REnv.(env_t) R) (log: Log) : REnv.(env_t) R :=
    REnv.(create) (fun k => match latest_write log k with
                         | Some v => v
                         | None => REnv.(getenv) r0 k
                         end).

  Fixpoint no_latest_writes (log: Log) l :=
    match l with
    | [] => True
    | [a] => latest_write log a = None
    | a::b => latest_write log a = None /\ no_latest_writes log b
    end.
End Logs.

Arguments LE {reg_t R} reg kind port val : assert.
Arguments LogEntry: clear implicits.
Arguments RLog: clear implicits.

Definition Log {reg_t} R := @_Log reg_t (fun idx => type_denote (R idx)) .
Definition CLog {reg_t} R := @_Log reg_t (fun idx => Bits.bits (R idx)) .

Arguments may_read : simpl never.
Arguments may_write : simpl never.
