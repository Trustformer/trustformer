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
  latch, and took the else arm whatever the answer was (`tb_guard.sv`);
- a drive under a guard fired before its guard's sources had settled, so a
  branch on a call on ANOTHER port sent the wrong arm's request (`tb_xport.sv`);
- a sample's latch enable ignored its guard, so a call in an arm that was not
  taken latched whatever the shared response channel held (`tb_untaken.sv`).

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
| `tb_arms.sv` | `Example_ArmsSeqSpike` | a call AFTER an `if` whose arms both call one IP: it waits for whichever arm ran, not just the last one written |
| `tb_untaken.sv` | `Example_ArmsSeqSpike` | the same design, read the other way: the SKIPPED arm still validates and still counts its cycles, and its buffer holds zero rather than the other arm's answer |
| `tb_xport.sv` | `Example_XPortGuardSpike` | the same branch with the arms' calls on a DIFFERENT port from the one the condition reads: the drives wait for the condition to arrive before either fires |
| `tb_mars.sv` | `Example_Mars` | the one-action MARS, 77 checks -- see below |

## Running them

Not wired into `make test`: verilator is not in `flake.nix`. It is in the local
nix store, so `--offline` works and nothing here needs the network. Verilator
shells out to `make`, `g++` and `python3`, none of which are on the dev-shell
PATH -- omit any one and it fails late with a bare `sh: 1: X: not found`.
`--build-jobs 2` is required: with a single job verilator bundles `main` into
`Vtb__ALL.a` and the linker discards it.

```sh
scripts/run-sim.sh              # all nine
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

`tb_guard.sv` would pass on the argument alone: every call in it is on one port,
so `last_sample` finds the first call's sample -- its guard is not disjoint from
either arm's -- and both arms' drives are sequenced behind it by an ordering
join, which by itself holds them until the answer is latched.

Move the condition's call to a second port and that join is gone: `last_sample`
searches the *arm's* port, where nothing precedes. The ordering is no longer
what holds the drives back, so this is the testbench that pins the mechanism
that does: a drive's compiled validity ANDs in its guard's sources, so the arm's
stall starts counting only once the condition's latch is up.

    st_c = 0   (then arm): arm asks for 7, st_r = 7
    st_c != 0  (else arm): arm asks for 9, st_r = 9

Read the two rows together -- one arm alone would pass on a design that decides
the branch off a zeroed latch, because `7` is what that design asks for either
way.

## tb_untaken.sv: the arm that was not taken

`Example_ArmsSeqSpike` again, checking the sample side rather than the drive
side. Both arms of the `if` call the same IP on the same port, and the counters
of BOTH arms run whichever way the branch goes -- that padding is what makes the
action's length independent of the condition, so the testbench asserts it.

What the skipped arm must NOT do is capture. Its counter reaches the latch
cycle while the channel is carrying another call's cycle, where the datasheet
promises nothing -- `deadbeef` here. A latch enable of `valid AND NOT v` alone
would copy that in. The enable ANDs in the arm's guard, so the buffer keeps its
reset value:

    run 0, then arm skipped:  valid at cyc 11, captured 0x00000000
    run 0, else arm taken:    valid at cyc  9, captured 0x00000007

The captured value is dead -- the phi discards it -- but the ordering join that
sequences a later call on that port is not gated by the phi, so a capture there
would be visible in the CYCLE COUNT. That is the leak this testbench holds
closed.
