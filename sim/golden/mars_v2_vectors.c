/* MarsV2 golden driver: the crypto-dependent commands of sim/tb_mars_v2.sv, in
   the bench's order, through the TCG reference emulator.  One line per
   observation, tagged with the bench's localparam name; the bench's error and
   FAILURE answers leave the state as it is, so only its successes appear here.
   scripts/regen-golden.py --design mars_v2 builds and runs it. */
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include "mars.h"

void _MARS_Init(void);
void CryptSnapshot(void *out, uint32_t regSelect, const void *ctx, uint16_t ctxlen);

static uint8_t nonce[32], ctx[32], dig[32], ctx2[32];

static void val(const char *tag, MARS_RC rc, const char *field, const uint8_t *v)
{
    printf("%-12s rc=%d %s=", tag, rc, field);
    for (int k = 0; k < 32; k++) printf("%02x", v[k]);
    printf("\n");
}

static void verdict(const char *tag, MARS_RC rc, bool r)
{
    printf("%-12s rc=%d result=%d\n", tag, rc, r);
}

/* A command whose effect the next observation shows: stop on any error. */
static void must(MARS_RC rc, const char *what)
{
    if (rc) { fprintf(stderr, "%s answered rc=%d\n", what, rc); exit(1); }
}

static void extend_read(const char *tag, uint16_t i, uint8_t last)
{
    uint8_t d[32] = {0};
    d[31] = last;                               /* big-endian 256-bit value */
    must(MARS_PcrExtend(i, d), "PcrExtend");
    MARS_RC rc = MARS_RegRead(i, d);
    val(tag, rc, "dig", d);
}

static void quote(const char *sig_tag, const char *snap_tag, uint32_t rsel,
                  uint8_t *sig, uint8_t *snap)
{
    MARS_RC rc = MARS_Quote(rsel, nonce, 32, ctx, 32, sig);
    val(sig_tag, rc, "sig", sig);
    CryptSnapshot(snap, rsel, nonce, 32);
    val(snap_tag, rc, "snap", snap);
}

int main(void)
{
    uint8_t out[32], sig[32], snap[32], sig_u[32], sig_q3[32], snap3[32], bad[32];
    char st[16], sn[16];
    bool r;
    MARS_RC rc;
    int k;

    for (k = 0; k < 32; k++) {
        nonce[k] = (uint8_t)(k + 0x01);
        ctx[k]   = (uint8_t)(k + 0x21);
        dig[k]   = (uint8_t)(k + 0x41);
        ctx2[k]  = (uint8_t)(k + 0x61);
    }

    _MARS_Init();                               /* Init, init_req = 1 */

    extend_read("E_EXT1", 0, 0x01);
    extend_read("E_PCR1", 1, 0xAA);

    for (k = 0; k < 4; k++) {
        snprintf(st, sizeof st, "E_QUOTE%d", k);
        snprintf(sn, sizeof sn, "E_SNAP%d", k);
        quote(st, sn, (uint32_t)k, sig, snap);
    }
    memcpy(sig_q3, sig, 32);
    memcpy(snap3, snap, 32);

    rc = MARS_Derive(3, ctx, 32, out);
    val("E_DERIVE", rc, "out", out);

    rc = MARS_Sign(ctx, 32, dig, sig_u);
    val("E_SIGN", rc, "sig", sig_u);

    memcpy(bad, sig_u, 32);
    bad[31] ^= 1;                               /* the bench's E_SIGN ^ 1 */
    rc = MARS_SignatureVerify(false, ctx, 32, dig, sig_u, &r);
    verdict("E_VFY_U_OK", rc, r);
    rc = MARS_SignatureVerify(false, ctx, 32, dig, bad, &r);
    verdict("E_VFY_U_BAD", rc, r);
    rc = MARS_SignatureVerify(true, ctx, 32, snap3, sig_q3, &r);
    verdict("E_VFY_R_OK", rc, r);
    rc = MARS_SignatureVerify(true, ctx, 32, dig, sig_u, &r);
    verdict("E_VFY_R_BAD", rc, r);

    /* DpDerive extends DP, so the same Quote signs differently ... */
    must(MARS_DpDerive(3, ctx2, 32), "DpDerive");
    quote("E_QUOTE_DP", "E_SNAP3", 3, sig, snap);

    /* ... and a NULL ctx resets DP to Init's, so it signs as before. */
    must(MARS_DpDerive(3, NULL, 0), "DpDerive reset");
    quote("E_QUOTE3", "E_SNAP3", 3, sig, snap);

    /* in_fault, then the Init that clears failure mode: DP is Init's again. */
    _MARS_Init();
    rc = MARS_Sign(ctx, 32, dig, sig);
    val("E_SIGN", rc, "sig", sig);
    return 0;
}
