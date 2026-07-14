---
name: rocq-iterative-proving
description: >-
  General working style for all Rocq/Coq files (.v) in this repo. USE WHEN:
  writing, editing, or debugging any Coq/Rocq proof or definition; developing
  lemmas incrementally; deciding whether an approach works. Prefer an iterative,
  test-driven loop — actively check each change against Rocq instead of
  speculating deeply about whether a tactic or definition will work. Also points
  to the vendored read-only Kôika source for reference.
---

# Iterative Rocq/Coq proving

Applies to every `.v` file in this repo. The guiding principle: **verify with the
proof assistant early and often; do not reason many steps ahead in your head about
whether something type-checks or a tactic closes a goal.** Rocq is the source of
truth — ask it.

## Core loop

1. Make the **smallest** meaningful change (one lemma, one tactic, one definition).
2. **Check it immediately** by compiling the file (or the single lemma).
3. Read the actual error / remaining goal.
4. Adjust based on what Rocq reported — not on what you assumed it would report.
5. Repeat.

Prefer many small verified steps over one large speculative edit. If you have
written more than a few tactics without checking, stop and check.

## Rules

- **Test over speculation.** When unsure whether a tactic, `rewrite`, or lemma
  application works, try it and read the result rather than composing a long chain
  and hoping. One confirmed step unblocks the next.
- **Compile frequently.** After each meaningful edit, build the file:
  ```bash
  dune build coq/<Path>/<File>.vo
  ```
  Fix the first error before moving on; later errors are often cascades.
- **Beware Kôika implicit types.** Kôika has many implicit arguments (`R`, `REnv`,
  `bits_t` sizes, `reg_t`, ports). A mismatch shows up as errors where both sides
  print the same (e.g. `x is not equal to x`). Enable `Set Printing Implicit.`
  (or `Set Printing All.`) to see the real difference, then align the implicit
  explicitly (`(R:=...)`, `(REnv:=...)`, size annotations, or `change`).
- **Inspect goals, don't guess them.** Use `Check`, `Print`, `About`,
  `Search`/`Search (pattern)`, and leave the proof state visible (`admit` a tail
  temporarily) to see what you're actually proving.
- **Keep the file compiling.** Don't accumulate many broken lemmas at once;
  a green file after each step keeps errors localized.
- **Reuse existing lemmas.** Before proving something, `Search` for it — in this
  repo and in the vendored Kôika source (below).
- **Small definitions first.** When a proof is hard, consider whether the
  definition can be reshaped to make it provable, and verify that reshape compiles
  before building on it.

## Reference: vendored Kôika source (read-only)

The Kôika library this repo builds on is checked out (untracked, git-ignored) at:

```
vendor/koika/
```

Use it **read-only** to understand Kôika's semantics, lemmas, and notations — e.g.:

- `vendor/koika/coq/KoikaForm/` — syntax / semantics of actions and logs
- `vendor/koika/coq/Properties/` — reusable semantic lemmas (`SemanticProperties`, …)
- `vendor/koika/coq/Primitives.v`, `Std.v`, `Frontend.v` — core definitions used here
- `vendor/koika/coq/Utils/` — `Common`, `Environments`, tactics

When a Kôika lemma or definition is needed, look it up there rather than guessing
its name or signature. Do **not** edit anything under `vendor/`.

## Relationship to other skills

For files under `coq/Properties/**` (Synthesis.v, IPR.v, Common.v), the fragile /
timeout-prone behavior takes precedence — follow the `coq-fragile-proofs` skill's
timing rules (bounded `timeout`, `Time`/`Timeout` annotations) in addition to this
iterative loop.
