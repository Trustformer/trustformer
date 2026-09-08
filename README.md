# Trustformer

Trustformer compiles a small imperative specification language into
constant-time hardware, and proves in Coq that the result does not leak secrets
through its timing.

A design is written as a set of *actions* over state, input and output
variables. Trustformer builds a data-flow graph, schedules it into pipeline
stages under a cost budget, and emits [Kôika](https://github.com/mit-plv/koika)
rules that are lowered to Verilog. Along the way a taint analysis decides which
branches are secret-dependent; those are compiled to wait for *both* sides, so
the number of cycles an action takes reveals nothing an attacker could not
already compute. That last sentence is the theorem
(`latency_noninterference_start`), not an aspiration.

Branches whose outcome the attacker can already deduce need not be paid for.
The user may supply *declassification rules* — small, separately proved lemmas
saying "this node is recoverable from those nodes under this guard" — and the
scheduler then leaves the corresponding branches variable-latency. Five such
rules ship in `coq/Rules/`.

> **Status.** Research artifact, under active development. The proofs are
> complete and admit-free, but the interface is not stable and there is no
> release. Please get in touch before building on it.

## Build

Everything runs inside the Nix development shell; `coqc` and `dune` are not
expected on the ambient `PATH`.

```sh
nix develop --command dune build coq/     # the library and all proofs (~90 s)
nix develop --command make all            # the above, then Verilog into build/
```

`make all` extracts each extraction target under `coq/Examples/` to OCaml and
runs `cuttlec -T verilog` on it. The resulting `build/*.v` files are **Verilog**,
not Coq.

## What is in here

| Path | Contents |
| --- | --- |
| `coq/Syntax.v`, `coq/Semantics.v` | the specification language and its denotational semantics |
| `coq/Scheduler/Contract.v` | `TFSchedContext` (what a user writes) and `TFSchedule` (what the scheduler must produce) |
| `coq/Scheduler/DFG.v` | data-flow graph datatypes and declassification instances |
| `coq/Scheduler/VariableScheduler.v` | DFG construction, cost model, taint and declassification analyses, buffering, code generation |
| `coq/Scheduler/Show.v`, `coq/Scheduler/Audit.v` | diagnostics: readable criticality reports, cycle bounds with witnesses, Graphviz output |
| `coq/TypedSynthesis.v` | the Kôika register file, rules and scheduler for a `TFSchedule` |
| `coq/Properties/` | the proofs: `Synthesis.v`, `SchedulerSimulation.v`, `IPR.v` |
| `coq/Rules/` | the declassification rule library, each with its soundness proof |
| `coq/Examples/` | worked designs, regressions, and extraction targets |
| `paper/` | the accompanying paper |

## Trying it

Every analysis result is a Coq term, so asking a question is a `Compute`. The
audit answers all of them at once, for one action at one cost limit:

```coq
Require Import Trustformer.Scheduler.Audit.
Require Import Trustformer.Examples.LockboxTriesTaint.

Compute (audit_report ctxA_blackbox 4 fs_act_test).
```

```
nodes:         23
buffers:       1
tainted nodes: 11
cycles:        2
constant time: yes
critical phis:
  - branch on ($fs_st_tries !=[2] #0) (node 3) is tainted and no declassification rule targets it [3 occurrences]
  - branch on ($fs_st_pin ==[32] ?fs_in_pin) (node 6) is tainted and no declassification rule targets it [3 occurrences]
```

Criticality is per branch *occurrence*, and the report says why each one could
not be discharged: no rule at all, a rule whose sources are unknown, or a rule
whose guard this path does not satisfy.

When an action is *not* constant time, the audit names the two paths that
differ — which is the leak:

```
cycles:        1 .. 3
constant time: NO
  fastest (1) when: not (?sk_in ==[32] #0)
  slowest (3) when: (?sk_in ==[32] #0)
```

`audit_dot ctx cost act` emits the same graph as Graphviz input, with tainted
nodes filled yellow, critical phis red, buffered nodes boxed and assigned
variables double-outlined. `coq/Examples/DiagnosticsRegression.v` shows all of
this pinned as tests.

## Writing a module

1. Declare three variable types (states, inputs, outputs) with their bit widths,
   and an action type. State variables are secret; output variables are what
   the attacker sees.
2. Give the action semantics as `tf_ops` — see the notation in
   `coq/Examples/LockboxTries.v` (`let $x := ...`, `if ... then ... else ...`).
3. Pack it into a `TFSchedContext`. Leave `tfs_spec_decls := []` for the
   blackbox behaviour, or list declassification rules from `coq/Rules/`.
4. `tfs_schedule ctx cost_limit` produces the `TFSchedule`; feeding it to
   `TypedSynthesis` yields the Kôika `package`, and
   `Interop.Backends.register package` plus `Extraction` produce the Verilog
   generator.

`coq/Examples/SimpleLockbox.v` is the shortest complete instance;
`coq/Examples/LockboxTries.v` is the paper's running example.

If you supply declassification rules, you also owe their soundness obligations
(`uncond_sound` and `decl_sound`). `lockboxB_uncond_sound` in
`coq/Examples/LockboxTriesTaint.v` shows how to discharge them from the shipped
rule library in a dozen lines.

## Where the claims are proved

| Claim | Coq |
| --- | --- |
| The scheduled machine refines one source-level action step | `variable_scheduler_correct` (Properties/SchedulerSimulation.v) |
| The Kôika circuit implements the schedule | `synthesis_correct`, `initial_state_matches` (Properties/Synthesis.v) |
| Taint propagates along data flow, and only secret-state reads are sources | `taint_propagates` (Properties/IPR.v), regressions in Examples/TaintRegression.v |
| Anything the analysis leaves untainted really is attacker-derivable | `untainted_derivable`, `untainted_roots_derivable` (Properties/IPR.v) |
| A secret state read is *not* derivable, so untainting cannot be vacuous | `svar_not_derivable` (Properties/IPR.v) |
| User declassification rules compose into the analysis soundly | `uncond_sound_of_instances`, `decl_sound_of_instances` (Properties/IPR.v) |
| Each shipped rule is sound | `neg_rule_sound`, `xor_rule_sound`, `widen_rule_sound`, `phiconst_rule_sound`, `phibranch_rule_sound` (Rules/) |
| Two runs with the same public view finish in the same number of cycles | `latency_noninterference`, `latency_noninterference_start` (Properties/IPR.v) |
| Latency is a function of the observable outputs alone | `latency_from_outputs`, `L_public` (Properties/IPR.v) |
| The emulator reproduces the circuit's observable trace, at the public latency | `emulator_correct`, `emulator_correct_L` (Properties/IPR.v) |
| With `tries` secret, every branch of the lockbox is critical (paper fig. A5) | `every_phi_is_critical`, `all_critical_for_lack_of_a_rule` (Examples/LockboxTriesTaint.v) |
| With `tries` public, only the pin check is (paper fig. B5) | `only_the_pin_check_is_critical` (Examples/LockboxTriesTaint.v) |
| ...and the whitebox rules remove even that | `whitebox_removes_all_criticality` (Examples/LockboxTriesTaint.v) |
| ...while the same rules buy nothing back when `tries` is secret | `secret_tries_defeats_the_same_rules` (Examples/LockboxTriesTaint.v) |
| The generated valid-signal expressions are the ones the paper derives | `valid_signals_all_phis_critical`, `valid_signals_no_phi_critical` (Examples/LockboxTriesTaint.v) |
| The lockbox takes two cycles at a cost limit of 4, one at 10 | `lockbox_takes_two_cycles`, `lockbox_is_combinational_at_10` (Examples/LockboxTriesTaint.v) |

There are no `Axiom`s and no `Admitted` proofs. Each of the theorems above is
followed by a `Print Assumptions`, so a build prints the evidence: every one
reports either *Closed under the global context* or, for the theorems stated
inside a section, that section's context record — never an axiom and never an
admitted lemma.

## Licence

See `LICENSE.md`.

