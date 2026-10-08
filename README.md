# Trustformer

Trustformer compiles a small imperative specification language into
variable-time hardware, and proves in Coq that the result does not leak secrets
through its timing.

A design is written as a set of _actions_ over state, input and output
variables. Trustformer builds a data-flow graph, schedules it into pipeline
stages under a cost budget, and emits [Kôika](https://github.com/mit-plv/koika)
rules that are lowered to Verilog. Along the way a taint analysis decides which
branches are secret-dependent; those are compiled to wait for _both_ sides, so
the number of cycles an action takes provably reveals nothing an attacker could not
already compute.

> **Status:** Research artifact, under active development.

## Build

Everything runs inside the Nix development shell; `coqc` and `dune` are not
expected on the ambient `PATH`.

```sh
nix develop --command dune build coq/     # the library and all proofs (~90 s)
nix develop --command make all            # the above, then Verilog into build/
nix develop --command make test           # the above, then every check we have
```

`make all` extracts each extraction target under `coq/Examples/` and
`coq/Regressions/` to OCaml and runs `cuttlec -T verilog` on it. The
resulting `build/*.v` files are **Verilog**.

`make test` adds three checks: that every headline theorem is proved and
axiom-free (`scripts/check-theorems.py`), that no generated net has two
different drivers (`scripts/check-drivers.py`), and the twelve verilator
testbenches (`scripts/run-sim.py`, see `sim/README.md`).

`scripts/check-theorems.py --list` prints the theorems the project stands on.
They are listed in that script: Rocq checks the proofs, so what needs a human
is whether the list is the right one.

## What is in here

| Path                                                  | Contents                                                                                      |
| ----------------------------------------------------- | --------------------------------------------------------------------------------------------- |
| `coq/Syntax.v`, `coq/Semantics.v`                     | the specification language and its denotational semantics                                     |
| `coq/Contract.v`                                      | `TFSchedContext` (what a user writes) and `TFSchedule` (what the scheduler must produce)      |
| `coq/DFG.v`                                           | data-flow graph datatypes and declassification instances                                      |
| `coq/Scheduler/Build.v`                               | step 1: the DFG builder, a state monad over the action's `tf_ops`                             |
| `coq/Scheduler/Cost.v`, `coq/Scheduler/Buffers.v`     | steps 2-4: the cost model, target cycles, and which nodes need a buffer register               |
| `coq/Scheduler/States.v`                              | the scheduled register file, indexed by the buffer table                                      |
| `coq/Scheduler/Taint.v`                               | step 5: taint and declassification analyses                                                   |
| `coq/Scheduler/Codegen.v`                             | step 6: the DFG as `tf_ops` over that register file, and `schedule`                           |
| `coq/Scheduler/Schedule.v`                            | the `TFSchedule` record and the obligations it carries                                        |
| `coq/Scheduler/Show.v`, `coq/Scheduler/Audit.v`       | diagnostics: criticality reports, cycle bounds with witnesses, Graphviz output                 |
| `coq/Backend/`                                        | `Lowering.v`, the Kôika register file, rules and scheduler for a `TFSchedule`                 |
| `coq/Theorems/`                                       | the guarantees: `Synthesis.v`, `SchedulerSimulation.v`, `IPR.v`, `Confidentiality.v`          |
| `coq/Theorems/Internal/`                              | proof bulk those rest on — machine-checked, not written to be read                            |
| `coq/Declassification/`                               | the declassification rule library                                                             |
| `coq/Examples/`                                       | the worked designs, one folder each: a `Spec.v` and any proofs about it                       |
| `coq/Regressions/`                                    | toolchain tests: the analyses, the lowering, and the designs the testbenches drive            |

## Writing a module

1. Declare three variable types (states, inputs, outputs) with their bit widths,
   and an action type. State variables are secret; output variables are what
   the attacker may see.
2. Give the action semantics as `tf_ops` — see the notation in
   `coq/Examples/LockboxTries/Spec.v` (`let $x := ...`, `if ... then ... else ...`).
3. Pack it into a `TFSchedContext`. Leave `tfs_spec_decls := []` for a
   blackbox attacker, or list declassification rules from `coq/Declassification/` for a whitebox attacker.
4. `tfs_schedule ctx cost_limit` produces the `TFSchedule`; feeding it to
   `coq/Backend/Lowering.v` yields the Kôika `package`, and
   `Interop.Backends.register package` plus `Extraction` produce the Verilog
   generator.

`coq/Examples/SimpleLockbox/Spec.v` is the shortest complete instance;
`coq/Examples/LockboxTries/Spec.v` is the paper's running example.
