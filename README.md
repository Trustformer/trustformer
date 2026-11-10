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

> **Note:** The Chipyard SoC integration and the testbed for the evaluation live
> in a separate repository, due to their large codebase including many submodules.
> It will be provided for the artifact evaluation.

## Build

All commands run inside the Nix development shell.

```sh
nix develop --command dune build coq/     # the library and all proofs (~90 s)
nix develop --command make all            # the above, then Verilog into build/
nix develop --command make test           # the above, then all checks
```

`make all` extracts each extraction target under `coq/Examples/` and
`coq/Regressions/` to OCaml and runs `cuttlec -T verilog` on it. The
resulting `build/*.v` files are Verilog.

`make test` adds three checks: every headline theorem is proved and
axiom-free (`scripts/check-theorems.py`), no generated net has two
different drivers (`scripts/check-drivers.py`), and the twenty-four Verilator
testbenches pass (`scripts/run-sim.py`, see `sim/README.md`).

`scripts/check-theorems.py --list` prints the headline theorems, which are
listed in that script.

## Contents

| Path                                              | Contents                                                                                 |
| ------------------------------------------------- | ---------------------------------------------------------------------------------------- |
| `coq/Syntax.v`, `coq/Semantics.v`                 | the specification language and its denotational semantics                                |
| `coq/Contract.v`                                  | `TFSchedContext` (what a user writes) and `TFSchedule` (what the scheduler must produce) |
| `coq/DFG.v`                                       | data-flow graph datatypes and declassification instances                                 |
| `coq/Scheduler/Build.v`                           | step 1: the DFG builder, a state monad over the action's `tf_ops`                        |
| `coq/Scheduler/Cost.v`, `coq/Scheduler/Buffers.v` | steps 2-4: the cost model, target cycles, and which nodes need a buffer register         |
| `coq/Scheduler/States.v`                          | the scheduled register file, indexed by the buffer table                                 |
| `coq/Scheduler/Taint.v`                           | step 5: taint and declassification analyses                                              |
| `coq/Scheduler/Codegen.v`                         | step 6: the DFG as `tf_ops` over that register file, and `schedule`                      |
| `coq/Scheduler/Schedule.v`                        | the `TFSchedule` record and the obligations it carries                                   |
| `coq/Scheduler/Show.v`, `coq/Scheduler/Audit.v`   | diagnostics: criticality reports, cycle bounds with witnesses, Graphviz output           |
| `coq/Backend/`                                    | `Lowering.v`, the Kôika register file, rules and scheduler for a `TFSchedule`            |
| `coq/Theorems/`                                   | the guarantees: `IPR.v` on the emitted circuit                                           |
| `coq/Theorems/Internal/`                          | supporting lemmas for the theorems above                                                 |
| `coq/Declassification/`                           | the declassification rule library                                                        |
| `coq/Examples/`                                   | examples, each with a `Spec.v` and any proofs about it                                   |
| `coq/Regressions/`                                | toolchain tests: the analyses, the lowering, and the designs the testbenches drive       |
| `external/ipr/`                                   | the vendored IPR definitions of Athalye et al., against which `IPR.v` is stated          |

## Guarantee

`coq/Theorems/IPR.v` states what the generated circuit guarantees against the
formalization of information-preserving refinement (IPR) by Athalye et al.,
[anishathalye/ipr](https://github.com/anishathalye/ipr). Its definition files are
vendored in `external/ipr/` unchanged except `From Stdlib` -> `From Coq`, for Coq 8.19.

| IPR, upstream                            | Trustformer, `coq/Theorems/IPRDefinitions.v`                                                      |
| ---------------------------------------- | ------------------------------------------------------------------------------------------------- |
| `M1 : machine I1 O1`, the implementation | `closed_circuit ip src`: a step is one Kôika cycle; I1 the wires, O1 ready and the public outputs |
| `M2 : machine I2 O2`, the specification  | `closed_spec src`: queries `Run act pin` and `Peek`, answered with the public outputs             |
| `d : driver I1 O1 I2 O2`                 | `driver`: offer the command, idle until ready is seen, read the outputs                           |
| `IPR M1 M2 d` (`Definition.v`)           | `IPR.ipr`: upstream's `IPR`, for every `ip` meeting its `datasheet`                               |

The statement builds on upstream's setting in two ways:

1. **Trusted IP and secure ports.** Upstream treats every wire as the attacker's.
   A Trustformer design may attach trusted IP and mark ports `Secret`, and those
   wires belong to a trusted environment that both machines are closed over
   (`close`). Any `src` drives the secure input ports and may react to the
   outputs shown at each command. Any `ip` that meets its `datasheet` answers the
   IP requests. With no IP and no secure port, `close` passes every wire through,
   and the statement is upstream's for the bare circuit.
2. **Reset.** A reset returns both machines, environment included, to their
   initial states.

The emulator IPR asks for is in `Internal/IPRBridge.v`. It reads only the
attacker's wires and the spec's answers to its queries.

IPR only speaks of what the attacker sees. `IPR.synthesis_correct` covers the rest:
from any start where the circuit is `at_rest` holding the spec's state, the driver
finishes every query, answers as the spec does, and leaves the circuit `at_rest`
holding the spec's next state, Secret state and outputs included.

## Writing a module

1. Declare three variable types (states, inputs, outputs) with their bit widths,
   and an action type. State variables are secret; output variables are what
   the attacker may see.
2. Give the action semantics as `tf_ops`, using the notation in
   `coq/Examples/LockboxTries/Spec.v` (`let $x := ...`, `if ... then ... else ...`).
3. Pack it into a `TFSchedContext`. Leave `tfs_spec_decls := []` for a
   blackbox attacker, or list declassification rules from `coq/Declassification/` for a whitebox attacker.
4. `tfs_schedule ctx cost_limit` produces the `TFSchedule`; feeding it to
   `coq/Backend/Lowering.v` yields the Kôika `package`, and
   `Interop.Backends.register package` plus `Extraction` produce the Verilog
   generator.

`coq/Examples/SimpleLockbox/Spec.v` is the shortest complete instance;
`coq/Examples/LockboxTries/Spec.v` is the paper's running example.
