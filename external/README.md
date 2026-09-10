# `external/` — IP blocks and glue for a generated Trustformer module

A Trustformer module is only half a device: its `Trusted` ports face crypto IP
that lives outside the verified boundary. This directory holds those blocks, the
thin adapters that speak the module's handshake, and the simulation harness that
checks the pair against a reference.

Nothing here is generated. `build/*.v` is generated; this is what it is wired to.

```
external/
  sha256/   vendored upstream IP, unmodified — secworks/sha256 (BSD-2)
  glue/     thin adapters between an IP's native interface and a module's
            Trusted port group.  This is TCB: secrets cross it.
  tb/       simulation harnesses
```

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

## `tb/`

`tb_mars_pcrextend.v` drives the generated module through the MMIO handshake,
with the glue and the core attached. Run it via
`agents/mars/oracle/run-stage3.sh`, which also diffs the result against the TCG
reference emulator.
