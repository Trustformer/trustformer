# Simulating the IP round trip

Reading the generated Verilog is not running it. On 2026-09-15 a sequenced
call's request strobe was a four-cycle LEVEL rather than two pulses, so the
first of two calls never reached the IP and its destination received the second
call's answer. Every lemma held, `check-drivers` was clean, and the expression
had been read and recorded as correct on two branches. `tb_two.sv` finds it in
about a second.

## What the testbenches assume

Each models the attached IP as **identity (or `+1`), latency 3, NOT pipelined**,
and does two things that make a pass mean something:

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

## Running them

Not wired into `make test`: verilator is not in `flake.nix`, and the nix shell
below fetches it. Verilator shells out to `make`, `g++` and `python3`, none of
which are on the dev-shell PATH — omit any one and it fails late with a bare
`sh: 1: X: not found`. `--build-jobs 2` is required: with a single job verilator
bundles `main` into `Vtb__ALL.a` and the linker discards it.

```sh
scripts/run-sim.sh              # all of them
scripts/run-sim.sh tb_two.sv    # just one
```

## The one-action MARS

`tb_mars.sv` drives `Example_Mars` through CapabilityGet, RegRead, PcrExtend,
Quote and _MARS_Init, with both IPs modelled as deterministic functions of the
whole request word.  The expected digests are computed by applying those same
functions to request payloads the testbench builds independently from the
framing in `coq/Examples/Mars.v`, so a wrong field order, length or key fails
even though the digest itself is arbitrary.  It also checks the guards, the
response codes, that an error arm drives no request at all, that the request
carries the LATCHED input, and that both arms of a branch take the same number
of cycles.
