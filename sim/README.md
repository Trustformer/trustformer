# Simulating the IP round trip

Reading the generated Verilog is not running it. Every bug in the drive/sample
path so far was invisible at the Coq level -- the cycle assignment was correct
and every lemma held -- and each was read off the Verilog and matched against
the shape that was expected before a testbench found it in about a second:

- a sequenced call's request strobe was a four-cycle LEVEL rather than two
  pulses, so the first of two calls never reached the IP (`tb_two.sv`);
- a guarded drive was compiled for the cycle its guard was WRITTEN rather than
  the cycle it fires, so the one-action MARS sent no request at all
  (`tb_mars.sv`);
- a guard on a call result read the live response wire instead of the sample's
  latch, and took the else arm whatever the answer was (`tb_guard.sv`).

## What the testbenches assume

The spikes model the attached IP as **identity (or `+1`), latency 3, NOT
pipelined**, and do two things that make a pass mean something:

- the answer is presented for **exactly one cycle**, and the response wire
  carries `deadbeef...` at every other cycle, so sampling on the wrong cycle
  latches garbage instead of accidentally working;
- a request arriving while another is in flight is a **failure**, so a held
  strobe is reported rather than absorbed.

`tb_call.sv` also changes the live input after the command is accepted, to check
the design uses the latched value.

| testbench | design | checks |
| --- | --- | --- |
| `tb_call.sv` | `Example_CallSpike` | one call: one strobe, right payload out, right answer in, latched input used |
| `tb_two.sv` | `Example_TwoCallSpike` | two calls, independent arguments: two pulses, program order, both results |
| `tb_chain.sv` | `Example_ChainedCallSpike` | two calls where the second's argument is the first's result |
| `tb_branch.sv` | `Example_BranchCallSpike` | a call under an `if` on an INPUT: both arms drive, mutually exclusive in time |
| `tb_guard.sv` | `Example_GuardCallSpike` | a branch on a CALL RESULT: the right arm is taken, and the guard reads the sample's latch |
| `tb_xport.sv` | `Example_XPortGuardSpike` | the same branch with the arms' calls on a DIFFERENT port from the one the condition reads -- **currently FAILS**, and is meant to |
| `tb_mars.sv` | `Example_Mars` | the one-action MARS, 77 checks -- see below |

## Running them

Not wired into `make test`: verilator is not in `flake.nix`. It is in the local
nix store, so `--offline` works and nothing here needs the network. Verilator
shells out to `make`, `g++` and `python3`, none of which are on the dev-shell
PATH -- omit any one and it fails late with a bare `sh: 1: X: not found`.
`--build-jobs 2` is required: with a single job verilator bundles `main` into
`Vtb__ALL.a` and the linker discards it.

```sh
scripts/run-sim.sh              # all six
scripts/run-sim.sh tb_two.sv    # just one
```

`build/<design>.v` must be current: `nix develop --offline --command bash -c
'cp -au _build/default/build/. build/ && make compile'` first. (`make all` fails
at `copy_build` because `rsync` is absent.)

## The one-action MARS

`tb_mars.sv` drives `Example_Mars` through CapabilityGet, RegRead, PcrExtend,
Quote and _MARS_Init, with both IPs modelled as deterministic functions of the
whole request word. The expected digests are computed by applying those same
functions to request payloads the testbench builds independently from the
framing in `coq/Examples/Mars.v`, so a wrong field order, length or key fails
even though the digest itself is arbitrary. It also checks the guards, the
response codes, that an error arm drives no request at all, that the request
carries the LATCHED input, and that both arms of a branch take the same number
of cycles.

`LSHA`/`LHMAC` at the top of the file must match `fs_ip`'s `ip_lat` in
`coq/Examples/Mars.v` -- currently the real 140 and 275.

## Not the same thing as the oracle

These check the module against a model of the IP. The campaign's acceptance test
checks it against the REAL SHA-256 and the TCG reference emulator:
`agents/mars/oracle/run-stage3-v4.sh` (agents/ is gitignored). Both should be
green before the interface is reviewed.

## tb_xport.sv: a branch whose condition reads another port

`tb_guard.sv` passes because every call in it is on one port: `last_sample`
finds the first call's sample -- its guard is not disjoint from either arm's --
so both arms' drives are sequenced behind it by an ordering join and cannot
fire until the answer is latched.

Move the condition's call to a second port and that join is gone: `last_sample`
searches the *arm's* port, where nothing precedes. A drive's compiled validity
is its ARGUMENT's, not its guard's, so the arm's stall starts counting
immediately and the arm's drive gets its one pulse window while the condition's
answer is still in flight and its latch still reads zero. The design then takes
the arm the zeroed latch selects:

    st_c = 0   (then arm): arm asks for 7, st_r = 7   -- right, by luck
    st_c != 0  (else arm): arm asks for 7, st_r = 7   -- WRONG, should be 9

`st_c` itself is correct (`f5`) by the time the action finishes; the branch was
simply decided before it arrived. This is the same family as the `ip_lat = 0`
collision: a call that is emitted but can never fire.

It is excluded from the default run because it fails. Run it by name:

    scripts/run-sim.sh tb_xport.sv
