# `external/` — IP blocks and glue for a generated Trustformer module

A Trustformer module is only half a device: its `Trusted` ports face crypto IP
that lives outside the verified boundary. This directory holds those blocks and
the thin adapters that speak the module's handshake. The testbenches that drive
the pair live in `sim/` with every other testbench.

Nothing here is generated. `build/*.v` is generated; this is what it is wired to.

```
external/
  ipr/      vendored Coq definitions of IPR — anishathalye/ipr (MIT)
  sha256/   vendored upstream IP, unmodified — secworks/sha256 (BSD-2)
  glue/     thin adapters between an IP's native interface and a module's
            Trusted port group.  This is TCB: secrets cross it.
```

## `ipr/`

`anishathalye/ipr`, from https://github.com/anishathalye/ipr at commit
`8697bdcd9b72df2ab1f12582e8c8e10b5f11bdb9`, MIT, © Anish Athalye. Only the definition
files are copied: `Common.v`, `Tactics.v`, `Machine.v`, `Driver.v`, `Emulator.v`,
`Definition.v`. The one change is `From Stdlib Require` -> `From Coq Require`, for
Coq 8.19; `diff` against upstream shows nothing else. `coq/Theorems/IPR.v` states
Trustformer's guarantee against these definitions.

## `sha256/`

`secworks/sha256`, from https://github.com/secworks/sha256, BSD-2-Clause,
© 2013 Secworks Sweden AB. Copied verbatim — do not edit; if it needs changing,
change the glue.

Two properties of `sha256_core.v` that its users must know, both read out of the
source rather than assumed:

- **It does not pad.** `block` is 512 bits, `init` starts a first block and
  `next` a subsequent one. Padding is the caller's job.
- **`digest_valid` stays high between requests.** It is set in `CTRL_DONE` and
  cleared only when the next `init`/`next` fires (L505/L516/L541). Any adapter
  that forwards it as a "result ready" level must deassert it itself once the
  consumer has taken the result.

## `glue/`

`mars_sha256_glue.v` adapts `sha256_core` to the MARS module's Trusted port
group (`crypt_op`/`key`/`msg`/`len`/`req` out, `crypt_res`/`valid`/`tag` in).

**It is TCB.** DP and AK cross it from Stage 4 onward, and the module's
correctness is conditional on it (`agents/mars/MVP.md` §9, A1/A6/A7/A8). Keep it
small, keep it auditable, and keep everything that is not strictly adaptation out
of it.

Build it with `+define+GLUE_OMIT_DEASSERT` to get a deliberately misbehaving
adapter — one that never drops `crypt_valid`. The module must remain safe under
it. `agents/mars/oracle/run-stage3.sh` asserts exactly that.

`pwhash_sha256_adapter.v` gives `sha256_core` the one-block port of the Knox
password hasher (`coq/Examples/Knox/PasswordHasher`): a strobe and a 512-bit
block in, the digest held on the response until the next request.

## What each adapter is responsible for

`mars_sha256_glue.v` and `mars_hmac_glue.v` both pad, because `sha256_core`
does not (§9 A8). MARS hashes exactly four message lengths — 36, 64, 68 and
100 bytes — and HMACs exactly three — 13, 32 and 42 — so padding is a small
case per adapter rather than a byte-indexed shifter. A length outside those
sets produces no request at all: a stall the test bench notices beats a
silently mis-padded hash.

`mars_hmac_glue.v` implements HMAC-SHA256 over the same core rather than
vendoring one, because `secworks/hmac_core` computes a full 256-bit digest
internally but exposes only the top 128 bits (`hmac_core.v` L52), and MARS
needs 32 bytes. That puts the two-pass structure in the TCB; it is bounded and
checked byte-for-byte against the reference emulator by
`agents/mars/oracle/run-stage3.sh`.

## The one-action interface

`mars_ip_sha_adapter.v` and `mars_ip_hmac_adapter.v` attach the same two glue
blocks to the **one-action** module, whose IP link is one request word and one
response word:

```
ip_req  = {strobe, len, msg}    a one-cycle pulse
ip_resp = digest                sampled ip_lat cycles after the strobe
```

There is no valid line and no tag, because the schedule already knows when the
answer is due — `ip_lat` is declared in the Coq context and the wait is compiled
into the action. That moves two obligations onto whoever attaches an IP, and the
adapters are where they are discharged: the answer must be **ready** by `ip_lat`
cycles after the strobe, and it must still be **on the wire** at that cycle, so
the adapter holds the last answer rather than presenting it for a window. Each
adapter checks the first obligation in simulation and prints `FAIL` if the IP
overruns its declared latency.

Measured on `secworks/sha256_core` through the glue, one request start to
`valid`:

| request | blocks | cycles |
| --- | --- | --- |
| SHA, 36 bytes | 1 | 68 |
| SHA, 64 / 68 / 100 bytes | 2 | 135 |
| HMAC, 13 / 32 / 42 bytes | 4 | 269 |

So `ip_lat` must be at least 135 for SHA and 269 for HMAC. `coq/Examples/Mars/Spec.v`
declares 140 and 275.

`agents/mars/oracle/run-stage3-v4.sh` runs the pair against the TCG C reference
emulator. `run-stage3.sh` is the sequential design's version of the same test and
now belongs to `Example_MarsSeq`.
