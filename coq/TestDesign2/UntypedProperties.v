(*! Properties that are useful to reason about untyped semantics !*)
(* TODO: move this to the kôika repo *)
Require Export Koika.Utils.Common.
Require Import Koika.KoikaForm.Untyped.UntypedSemantics.
Require Import Koika.KoikaForm.SimpleVal.
Require Import Koika.KoikaForm.Untyped.UntypedLogs.

Section Logs.
    Context {V: Type}.

    Context {reg_t: Type}.
    Context {REnv: Env reg_t}.
    Definition R : reg_t -> Type := fun _ => V.

    Notation Log := (@_ULog V reg_t REnv).

    Lemma log_find_empty {T} idx (f: @LogEntry (R idx) -> option T):
        log_find (log_empty: Log) idx f = None.
    Proof.
        unfold log_find, log_empty; intros; rewrite getenv_create; reflexivity.
    Qed.
End Logs.