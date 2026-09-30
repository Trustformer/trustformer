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
resulting `build/*.v` files are **Verilog**. `make test` adds the duplicate-driver
scan (`scripts/check-drivers.py`) and the eleven verilator testbenches
(`scripts/run-sim.py`, see `sim/README.md`).

## What is in here

| Path                                            | Contents                                                                                      |
| ----------------------------------------------- | --------------------------------------------------------------------------------------------- |
| `coq/Syntax.v`, `coq/Semantics.v`               | the specification language and its denotational semantics                                     |
| `coq/Scheduler/Contract.v`                      | `TFSchedContext` (what a user writes) and `TFSchedule` (what the scheduler must produce)      |
| `coq/Scheduler/DFG.v`                           | data-flow graph datatypes and declassification instances                                      |
| `coq/Scheduler/VariableScheduler.v`             | DFG construction, cost model, taint and declassification analyses, buffering, code generation |
| `coq/Scheduler/Show.v`, `coq/Scheduler/Audit.v` | diagnostics: readable criticality reports, cycle bounds with witnesses, Graphviz output       |
| `coq/TypedSynthesis.v`                          | the Kôika register file, rules and scheduler for a `TFSchedule`                               |
| `coq/Properties/`                               | the proofs: `Synthesis.v`, `SchedulerSimulation.v`, `IPR.v`                                   |
| `coq/Rules/`                                    | the declassification rule library                                                             |
| `coq/Examples/`                                 | the worked designs, one folder each: a `Spec.v` and any proofs about it                       |
| `coq/Regressions/`                              | toolchain tests: the analyses, the lowering, and the designs the testbenches drive             |

## Writing a module

1. Declare three variable types (states, inputs, outputs) with their bit widths,
   and an action type. State variables are secret; output variables are what
   the attacker may see.
2. Give the action semantics as `tf_ops` — see the notation in
   `coq/Examples/LockboxTries/Spec.v` (`let $x := ...`, `if ... then ... else ...`).
3. Pack it into a `TFSchedContext`. Leave `tfs_spec_decls := []` for a
   blackbox attacker, or list declassification rules from `coq/Rules/` for a whitebox attacker.
4. `tfs_schedule ctx cost_limit` produces the `TFSchedule`; feeding it to
   `TypedSynthesis` yields the Kôika `package`, and
   `Interop.Backends.register package` plus `Extraction` produce the Verilog
   generator.

`coq/Examples/SimpleLockbox/Spec.v` is the shortest complete instance;
`coq/Examples/LockboxTries/Spec.v` is the paper's running example.
