---
name: coq-fragile-proofs
description: >-
  Work safely on the timeout-prone Coq/Kôika proofs under coq/Properties/
  (Synthesis.v, IPR.v, Common.v). USE WHEN: editing or proving lemmas in
  coq/Properties/**; touching Kôika log / bits_t / interp_action lemmas;
  diagnosing slow or non-terminating Qed / kernel checks; handling
  Admitted (* SPEEDUP/PERF *) markers; adding Time / Timeout annotations to Coq
  proofs. These files can make the Coq kernel hang on Qed even when the proof is
  complete, so every checking step must be time-bounded.
---

# Working with fragile Coq/Kôika proofs (coq/Properties/)

These files (`coq/Properties/Synthesis.v` ~2500 lines, `IPR.v`, `Common.v`) build
huge dependently-typed Kôika terms (`interp_action`, `Log`, `bits_t`, `eq_rect`
casts from `convert`). The **Coq kernel can fail to terminate on `Qed`** even when
the tactic script has closed all goals. Treat every proof-checking action as
potentially non-terminating and always bound it in time.

## ⚠️ Implicit-type mismatches (very common; read this)

Kôika carries many **implicit** type arguments — register maps (`R`, `REnv`), bit
sizes in `bits_t n`, `reg_t`, port and `Log` parameters. A tiny mismatch in one of
these _implicit_ arguments produces errors and goals where both sides **print
identically**, e.g. `x is not equal to x` or a `rewrite`/`apply` that "should"
work but fails.

- The terms are **not** actually equal — an invisible implicit differs.
- First move: `Set Printing Implicit.` (and if needed `Set Printing All.`) to see
  the real discrepancy.
- Fix by aligning the implicit explicitly: `(R:=...)`, `(REnv:=...)`, size
  annotations, or a `change`/`unify` to force the intended type.
- Never assume equality just because the pretty-printed forms match.

## ⚠️ Never blindly `simpl`/`cbn` Kôika `interp_*`

The single most common trap: goals contain Kôika `interp_action` /
`interp_rule` / `interp_scheduler` (`interp_*`) terms, and the instinct is to
`simpl`, `cbn`, or `unfold` them to "make progress". **Don't.** Reducing `interp_*`
unfolds the whole action interpreter and explodes the proof term — leading straight
to `Qed`/kernel timeouts and unreadable goals. It _may_ occasionally work on a tiny
term, but assume it won't.

Prefer targeted rewriting instead:

- Use dedicated stepper lemmas that peel one construct at a time (e.g.
  `interp_action_seq`, `interp_action_if`, `interp_action_read0`), then `rewrite`
  with them.
- Keep `interp_*` **opaque**; rewrite by equations rather than reducing.
- If you must reduce, scope it hard: `cbn [fst snd]`, `cbn [interp_scheduler']`,
  or `change`/`set` a subterm — never a bare `simpl`/`cbn`/`unfold interp_action`.
- Bound any reduction you do try with `Timeout N` so it fails fast.

## Core mental model: two different failures

Always diagnose which one you are facing — the fix differs:

1. **Slow / non-terminating tactic search** (proof not yet closed).
   - Symptom: a single tactic (`sauto`, `hammer`, `cbn`, `simpl`, big `rewrite`)
     spins.
   - Fix: guard it with `Timeout N tac` and shrink the search.

2. **Slow / non-terminating `Qed`** (goals closed, kernel re-checks the term).
   - Symptom: script reaches "No more goals" but `Qed` hangs.
   - This is a **term-size** problem, not a logic problem. `Timeout` around a
     tactic will NOT catch it — only wall-clock `timeout` around the build does.

## Hard timing rules (never violate)

- **No single step should take longer than ~30 s.** Bound every build/check with
  an OS `timeout`.
- Any step expected to take non-trivial time **must** be wrapped in `Time` in the
  code so the duration is visible.
- Every timed step gets a brief comment with the expected duration **measured on
  this machine**, e.g. `(* ca. 12 s *)`. **Never guess a number** — only write a
  time you actually observed here. If you have not measured it, omit the number
  or write `(* ca. ? s *)`.
- The budget **adapts on demand**: escalate a timeout only deliberately, and when
  you do, update the `(* ca. X s *)` comment with the newly observed time.

## Mandated workflow loop

`timeout` (GNU coreutils) is available inside the `nix develop` shell.

1. Check a single file target, time-bounded:
   ```bash
   timeout 30 dune build coq/Properties/Synthesis.vo
   ```
   Never run an un-timed full `dune build` on these files.
2. If a **tactic** is the suspect: guard it first, then shrink it.
   ```coq
   Timeout 30 sauto.   (* fails fast instead of hanging *)
   ```
   Replace broad automation with explicit steps (`reflexivity`, `congruence`,
   targeted `rewrite`, `apply`).
3. If **`Qed`** is the suspect: apply the term-shrinking ladder (below) BEFORE
   admitting.
4. Re-measure with `Time`, then update the `(* ca. X s *)` comment to the value
   you just observed.

## Qed policy: always try to optimize before admitting

When a finished proof's `Qed` exceeds the budget, work down this ladder:

1. Push subgoals into `abstract (...)` or split them into standalone `Lemma`s so
   the kernel checks small terms instead of one huge one.
2. Make register/size data `Opaque`; avoid `cbn`/`simpl` that force reduction of
   large dependent terms — rewrite by equational lemmas instead.
3. Replace `sauto`/`hammer`-closed leaves with minimal explicit proofs (they emit
   large, redundant terms that are expensive to _check_).
4. Consider reflection / `vm_compute`-backed equality lemmas for `bits`/log
   computations so `Qed` checks a computation, not a symbolic term.
5. **Only if all fail**, admit with a clear, categorized marker (below) and note
   it is soundness-relevant.

## Admit categories — keep them distinct

Never silently convert one into the other.

- `Admitted. (* PERF: Qed >N s *)` — proof is **complete**, kernel too slow. Still
  a trust risk, but the logic exists. (Historically tagged `(* SPEEDUP *)`.)
- `Admitted. (* TODO *)` — a **genuine gap**; real remaining proof work.

## Guardrails / anti-patterns

- Never run an un-timed `dune build` / `coqc` on these files.
- Never `Set Hammer ATPLimit` higher or add broad automation to brute-force a slow
  goal — it makes `Qed` worse.
- Never delete or weaken existing `Time` / `Timeout` annotations.
- Never fabricate an expected-time comment; only record measured times.
- Prefer editing the smallest relevant lemma; don't speculatively re-elaborate the
  whole section.

## Reference snippets

```bash
# time-bounded single-file check
timeout 30 dune build coq/Properties/Synthesis.vo
```

```coq
Timeout 30 tac.              (* bound a suspect tactic *)
Time tac.                    (* measure a step; then add (* ca. X s *) *)
Admitted. (* PERF: Qed >30 s, complete proof *)
Admitted. (* TODO: depends on interp_rule_correct *)
```
