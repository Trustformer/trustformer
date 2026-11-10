(*! Language | Untyped logs of reads and writes !*)
Require Export Koika.Utils.Common.
Require Export Koika.Utils.Environments.
Require Export Koika.KoikaForm.Syntax.
Require Koika.KoikaForm.Logs.

Section Logs.
  Context {V: Type}.

  Record LogEntry := LE {
    kind: Logs.LogEntryKind;
    port: Port;
    val: V
  }.

  Definition RLog := list LogEntry.

  Context {reg_t: Type}.
  Context {REnv: Env reg_t}.
  Definition R : reg_t -> Type := fun _ => V.

  Definition _ULog := REnv.(env_t) (fun idx => RLog).
  Notation ULog := _ULog.

  Definition log_empty : ULog := REnv.(create) (fun _ => []).

  Definition log_app (l1 l2: ULog) :=
    map2 REnv (fun _ ll1 ll2 => ll1 ++ ll2) l1 l2.

  Definition log_find {T} (log: ULog) reg (f: LogEntry -> option T) :=
    list_find_opt f (REnv.(getenv) log reg).

  Definition log_cons (reg: reg_t) le (l: ULog) :=
    REnv.(putenv) l reg (le :: REnv.(getenv) l reg).

  Definition log_forallb (log: ULog) reg (f: Logs.LogEntryKind -> Port -> bool)
  :=
    List.forallb (fun '(LE kind prt _) => f kind prt) (REnv.(getenv) log reg).

  Definition log_existsb (log: ULog) reg (f: Logs.LogEntryKind -> Port -> bool)
  :=
    List.existsb (fun '(LE kind prt _) => f kind prt) (REnv.(getenv) log reg).

  Definition is_read0 kind prt :=
    match kind, prt with
    | Logs.LogRead, P0 => true
    | _, _ => false
    end.

  Definition is_read1 kind prt :=
    match kind, prt with
    | Logs.LogRead, P1 => true
    | _, _ => false
    end.

  Definition is_write0 kind prt :=
    match kind, prt with
    | Logs.LogWrite, P0 => true
    | _, _ => false
    end.

  Definition is_write1 kind prt :=
    match kind, prt with
    | Logs.LogWrite, P1 => true
    | _, _ => false
    end.

  Open Scope bool_scope.

  Definition may_read (sched_log: ULog) prt idx :=
    match prt with
    | P0 =>
      negb (log_existsb sched_log idx is_write0)
      && negb (log_existsb sched_log idx is_write1)
    | P1 => negb (log_existsb sched_log idx is_write1)
    end.

  Definition log_latest_write0_fn (le: LogEntry) :=
    match le with
    | LE Logs.LogWrite P0 v => Some v
    | _ => None
    end.

  Definition latest_write0 (log: ULog) idx :=
    log_find log idx log_latest_write0_fn.

  Definition log_latest_write1_fn (le: LogEntry) :=
    match le with
    | LE Logs.LogWrite P1 v => Some v
    | _ => None
    end.

  Definition latest_write1 (log: ULog) idx :=
    log_find log idx log_latest_write1_fn.

  Definition may_write (sched_log rule_log: ULog) prt idx :=
    match prt with
    | P0 =>
      negb (log_existsb (log_app rule_log sched_log) idx is_read1)
      && negb (log_existsb (log_app rule_log sched_log) idx is_write0)
      && negb (log_existsb (log_app rule_log sched_log) idx is_write1)
    | P1 => negb (log_existsb (log_app rule_log sched_log) idx is_write1)
    end.

  Definition log_latest_write_fn (le: LogEntry) :=
    match le with
    | LE Logs.LogWrite _ v => Some v
    | _ => None
    end.

  Definition latest_write (log: ULog) idx :=
    log_find log idx log_latest_write_fn.

  Definition commit_update (r0: REnv.(env_t) R) (log: ULog) : REnv.(env_t) R :=
    REnv.(create) (fun k =>
      match latest_write log k with
      | Some v => v
      | None   => REnv.(getenv) r0 k
      end
    ).

  Fixpoint no_latest_writes (log: ULog) l :=
    match l with
    | []   => True
    | [a]  => latest_write log a = None
    | a::b => latest_write log a = None /\ no_latest_writes log b
    end.
End Logs.

Arguments LE _ kind port val : assert.
Arguments LogEntry: clear implicits.
Arguments RLog: clear implicits.

Section Maps.
  Context {reg_t: Type}.

  Context {REnv: Env reg_t}.
  Context {R1: reg_t -> Type}.
  Context {R2: reg_t -> Type}.

  Context {V: Type}.
  Notation Log1 := (@_ULog V reg_t REnv).
  Notation Log2 := (@_ULog V reg_t REnv).

  Definition LogEntry_map (f: V -> V) := fun '(LE kind prt v) =>
    match kind with
    | Logs.LogRead => fun v => LE Logs.LogRead prt v
    | Logs.LogWrite => fun v => LE Logs.LogWrite prt (f v)
    end v.

  Definition RLog_map (f: V -> V) l := List.map (LogEntry_map f) l.

  Definition log_map (f: RLog V -> RLog V) (log: Log1) : Log2 :=
    Environments.map REnv (fun k l1 => f l1) log.

  Definition log_map_values (f: V -> V) (log: Log1) : Log2 :=
    log_map (RLog_map f) log.
End Maps.
