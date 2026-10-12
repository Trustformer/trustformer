/* Differential fuzz stream for Example_MarsV2.  Draws a seeded command stream,
   runs it through the TCG reference emulator (built by scripts/fuzz-mars.py with
   this project's Profile), and writes the full public state expected after each
   command: rc cap result dout snap pcr0 pcr1 failure st.  Each line of the meta
   file names the rule that produced its expectation:
     EMU      the emulator's answer         EMU-F  the emulator in failure mode
     EMU-N10  DpDerive ctxlen 0 = CryptDpInit (Profile)
     N1  _MARS_Init is gated by init_req; guarded commands answer VALUE before it
     N2  Sequence* answer COMMAND (Profile)   N4  ctxlen/nlen != 32 answer BUFFER
     N5  unknown codes fire no action; state unchanged
     D1  in failure mode codes 2-4 and 9 answer FAILURE (dispatcher order, 8)
     E1  CapabilityGet answers in failure mode (5.3.1); the emulator's check is bypassed
     F1  the platform fault input at accept enters failure mode (5.6)
     F2  SelfTest with a corrupted known answer enters failure mode (5.6)
   usage: gen_mars_v2 SEED N PRE cmds.txt expected.txt meta.txt */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <stdbool.h>
#include "mars.h"
void CryptSnapshot(void * out, uint32_t regSelect, const void * ctx, uint16_t ctxlen);
extern bool failure;
void _MARS_Init();

static uint64_t s;
static uint64_t rnd(void) { uint64_t z = (s += 0x9E3779B97F4A7C15ULL);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; return z ^ (z >> 31); }
static unsigned pct(void) { return rnd() % 100; }
static void rbytes(uint8_t *b, int n) { for (int i = 0; i < n; i++) b[i] = (uint8_t)rnd(); }
static void hex(FILE *f, const uint8_t *b, int n) { for (int i = 0; i < n; i++) fprintf(f, "%02x", b[i]); }

static uint16_t draw_len(unsigned p32, unsigned p0) {
  unsigned r = pct();
  if (r < p32) return 32;
  if (r < p32 + p0) return 0;
  static const uint16_t sp[] = {0, 1, 31, 33, 64, 0xFFFF};
  unsigned q = rnd() % 10;
  if (q < 6) return sp[q];
  if (q < 8) return (uint16_t)(32 + (1u << (6 + rnd() % 10)));   /* low 6 bits = 32 */
  return (uint16_t)rnd();
}
static uint16_t draw_idx(void) {
  if (pct() < 80) return rnd() % 2;
  unsigned q = rnd() % 6, k = 1 + rnd() % 15;
  switch (q) { case 0: return 2; case 1: return 3; case 2: return 0xFFFF;
    case 3: return (uint16_t)(1u << k); case 4: return (uint16_t)(1 + (1u << k)); default: return (uint16_t)rnd(); }
}
static uint16_t draw_pt(void) {
  unsigned r = pct();
  if (r < 85) return rnd() % 14;
  if (r < 90) return 0xFFFF;
  if (r < 95) return (uint16_t)((rnd() % 12) | (1u << (4 + rnd() % 12)));  /* valid low bits, high junk */
  return (uint16_t)rnd();
}
static uint32_t draw_regsel(void) {
  if (pct() < 80) return rnd() % 4;
  unsigned q = rnd() % 6;
  switch (q) { case 0: return 4; case 1: return 5; case 2: return 0x80000000u; case 3: return 0xFFFFFFFFu;
    case 4: return (uint32_t)((rnd() % 4) | (1ull << (2 + rnd() % 30))); default: return (uint32_t)rnd(); }
}
static uint16_t draw_code(void) {
  unsigned r = rnd() % 1000;
  if (r < 60)  return 0;      /* SelfTest */
  if (r < 140) return 1;      /* CapabilityGet */
  if (r < 160) return 2;
  if (r < 180) return 3;
  if (r < 200) return 4;
  if (r < 350) return 5;      /* PcrExtend */
  if (r < 430) return 6;      /* RegRead */
  if (r < 520) return 7;      /* Derive */
  if (r < 600) return 8;      /* DpDerive */
  if (r < 620) return 9;      /* PublicRead */
  if (r < 740) return 10;     /* Quote */
  if (r < 840) return 11;     /* Sign */
  if (r < 945) return 12;     /* SignatureVerify */
  if (r < 995) return 0xFFFF; /* _MARS_Init */
  { unsigned q = rnd() % 4;  /* N5: unknown codes */
    return q == 0 ? 13 : q == 1 ? 14 : q == 2 ? 0xFFFE : (uint16_t)(13 + rnd() % (0xFFFE - 13)); }
}

static const char *nm[] = {"selftest","capget","seqhash","sequpd","seqcomp","pcrext","regread","derive","dpderive","pubread","quote","sign","verify"};
/* The latency class a command falls in, from public data only: the code, the
   arguments, and the public failure/st bits before it. */
static void tclass(char *o, size_t n, uint16_t code, uint16_t pt, uint16_t idx, uint32_t regsel, uint16_t nlen, uint16_t ctxlen, bool inited, bool infail) {
  if (code > 12 && code != 0xFFFF) { snprintf(o, n, "unknown"); return; }
  if (code == 0xFFFF) { snprintf(o, n, "init"); return; }
  const char *nme = nm[code];
  if (code == 1) { snprintf(o, n, pt >= 1 && pt <= 8 ? "capget:t1-8" : "capget:other"); return; }
  if (infail) { snprintf(o, n, "%s:infail", nme); return; }
  if ((code >= 2 && code <= 4) || code == 9) { snprintf(o, n, "%s:COMMAND", nme); return; }
  if (!inited) { snprintf(o, n, "%s:preinit", nme); return; }
  const char *b = "ok";
  switch (code) {
  case 5: case 6: b = idx < 2 ? "ok" : "REG"; break;
  case 7: b = regsel > 3 ? "REG" : ctxlen != 32 ? "BUFFER" : "ok"; break;
  case 8: b = regsel > 3 ? "REG" : ctxlen == 0 ? "reset" : ctxlen != 32 ? "BUFFER" : "ok"; break;
  case 10: b = regsel > 3 ? "REG" : (nlen != 32 || ctxlen != 32) ? "BUFFER" : "ok"; break;
  case 11: case 12: b = ctxlen != 32 ? "BUFFER" : "ok"; break;
  }
  snprintf(o, n, "%s:%s", nme, b);
}

typedef struct { uint16_t rc, cap; int result; uint8_t dout[32], snap[32], p0[32], p1[32]; int fail, st; } pub_t;
static void state_str(char *o, const pub_t *p) {
  char *q = o; q += sprintf(q, "%d %04x %d ", p->rc, p->cap, p->result);
  for (int i = 0; i < 32; i++) q += sprintf(q, "%02x", p->dout[i]); *q++ = ' ';
  for (int i = 0; i < 32; i++) q += sprintf(q, "%02x", p->snap[i]); *q++ = ' ';
  for (int i = 0; i < 32; i++) q += sprintf(q, "%02x", p->p0[i]); *q++ = ' ';
  for (int i = 0; i < 32; i++) q += sprintf(q, "%02x", p->p1[i]);
  sprintf(q, " %d %d", p->fail, p->st);
}
static void read_pcrs(pub_t *p, bool inited) {
  if (!inited) { memset(p->p0, 0, 32); memset(p->p1, 0, 32); return; }
  bool f = failure; failure = false;          /* state read, not a command */
  if (MARS_RegRead(0, p->p0) || MARS_RegRead(1, p->p1)) { fprintf(stderr, "RegRead failed\n"); exit(3); }
  failure = f;
}

static FILE *fc, *fe, *fm;
static long line = 0;
static void emit(uint16_t code, uint16_t pt, uint16_t idx, uint32_t regsel, uint16_t nlen, uint16_t ctxlen,
                 int restricted, int fault, int init_req, int inj, const uint8_t *dig, const uint8_t *nonce,
                 const uint8_t *ctx, const uint8_t *sig, const char *st, const char *rule, const char *tag, const char *tcls) {
  fprintf(fc, "%04x %04x %04x %08x %04x %04x %x %x %x %x ", code, pt, idx, regsel, nlen, ctxlen, restricted, fault, init_req, inj);
  hex(fc, dig, 32); fputc(' ', fc); hex(fc, nonce, 32); fputc(' ', fc); hex(fc, ctx, 32); fputc(' ', fc); hex(fc, sig, 32); fputc('\n', fc);
  fprintf(fe, "%ld %04x %s\n", line, code, st);
  fprintf(fm, "%ld %04x %s %s %d %s\n", line, code, rule, tag, fault, tcls);
  line++;
}

int main(int argc, char **argv)
{
  if (argc != 7) return 2;
  s = strtoull(argv[1], 0, 0); long n = atol(argv[2]); long pre = atol(argv[3]);
  fc = fopen(argv[4], "w"); fe = fopen(argv[5], "w"); fm = fopen(argv[6], "w");
  if (!freopen("/dev/null", "w", stdout)) return 2;   /* the emulator prints PS/DP/Skdf */
  bool inited = false;
  pub_t cur; memset(&cur, 0, sizeof cur);
  char prev[400], now[400]; state_str(prev, &cur);
  static uint8_t ctxbuf[65536], noncebuf[65536];
  long inserted = 0;
  for (long i = 0; i < n; i++) {
    uint16_t code = (i == pre) ? 0xFFFF : draw_code();
    uint16_t pt = draw_pt(), idx = draw_idx();
    uint32_t regsel = draw_regsel();
    uint16_t nlen = draw_len(85, 0), ctxlen = (code == 8) ? draw_len(65, 20) : draw_len(85, 0);
    int restricted = rnd() & 1;
    int fault = (pct() < 3 && (rnd() % 4) == 0) ? 1 : 0;        /* ~0.75% */
    int init_req = (code == 0xFFFF) ? (i < pre ? 0 : (i == pre ? 1 : (pct() < 75))) : (int)(rnd() & 1);
    int inj = 0;
    char tcls[48]; tclass(tcls, sizeof tcls, code, pt, idx, regsel, nlen, ctxlen, inited, failure);
    uint8_t dig[32], nonce[32], ctx[32], sig[32];
    rbytes(dig, 32); rbytes(nonce, 32); rbytes(ctx, 32); rbytes(sig, 32);
    const char *vmode = "rand";
    if (code == 12 && !failure) {                      /* craft signatures that verify */
      unsigned m = pct();
      bool flip = false, swap = false;
      if (m < 55) { flip = (m >= 40 && m < 48); swap = (m >= 48); }
      if (m < 55) {
        bool want_r = (rnd() & 1);
        if (!want_r) { if (MARS_Sign(ctx, 32, dig, sig)) { fprintf(stderr, "Sign failed\n"); return 3; } }
        else { uint32_t rs = rnd() % 4; uint8_t nn[32]; rbytes(nn, 32);
               if (MARS_Quote(rs, nn, 32, ctx, 32, sig)) { fprintf(stderr, "Quote failed\n"); return 3; }
               CryptSnapshot(dig, rs, nn, 32); }
        restricted = want_r ? 1 : 0; vmode = want_r ? "validR" : "validU";
        if (swap) { restricted ^= 1; vmode = "swapped"; }
        if (flip) { unsigned b = rnd() % 256; if (rnd() & 1) sig[b / 8] ^= (uint8_t)(1u << (b % 8)), vmode = "flipsig";
                    else dig[b / 8] ^= (uint8_t)(1u << (b % 8)), vmode = "flipdig"; }
      }
    }
    memset(ctxbuf, 0, sizeof ctxbuf); memcpy(ctxbuf, ctx, 32);
    memset(noncebuf, 0, sizeof noncebuf); memcpy(noncebuf, nonce, 32);

    pub_t nx = cur; nx.rc = 0; nx.cap = 0; nx.result = 0; memset(nx.dout, 0, 32);
    const char *rule = "EMU"; char tag[64] = "";
    int rc = -1;
    bool known = code <= 12 || code == 0xFFFF;
    const char *name = code == 0xFFFF ? "init" : (code <= 12 ? nm[code] : "unknown");
    if (!known) {                                       /* N5: no rule fires, nothing changes */
      nx = cur; rule = "N5"; snprintf(tag, sizeof tag, "unknown:nochange");
    } else if (code == 0xFFFF) {
      if (init_req) { _MARS_Init(); rc = 0; rule = "N1"; snprintf(tag, sizeof tag, "init:%s%s", inited ? "reinit" : "first", fault ? ":fault" : "");
                      inited = true; }
      else { rc = 6; rule = "N1"; snprintf(tag, sizeof tag, "init:refused%s%s", failure ? ":infail" : "", fault ? ":fault" : ""); }
    } else if (code == 1) {
      uint16_t c2 = 0;
      if (failure) { failure = false; rc = MARS_CapabilityGet(pt, &c2, sizeof c2); failure = true; rule = "E1"; }
      else rc = MARS_CapabilityGet(pt, &c2, sizeof c2);
      if (!rc) nx.cap = c2;
      snprintf(tag, sizeof tag, "capget:%s%s", rc ? "VALUE" : "ok", fault ? ":fault" : "");
    } else if (failure) {                               /* 5.3.1 / section 8 dispatcher */
      switch (code) {
      case 2: case 3: case 4: case 9: rc = MARS_RC_FAILURE; rule = "D1"; break;
      case 0: rc = MARS_SelfTest(true); break;
      case 5: rc = MARS_PcrExtend(idx, dig); break;
      case 6: { uint8_t o[32]; rc = MARS_RegRead(idx, o); } break;
      case 7: { uint8_t o[32]; rc = MARS_Derive(regsel, ctxbuf, ctxlen, o); } break;
      case 8: rc = MARS_DpDerive(regsel, ctxlen ? ctxbuf : NULL, ctxlen); break;
      case 10: { uint8_t o[32]; rc = MARS_Quote(regsel, noncebuf, nlen, ctxbuf, ctxlen, o); } break;
      case 11: { uint8_t o[32]; rc = MARS_Sign(ctxbuf, ctxlen, dig, o); } break;
      case 12: { bool r; rc = MARS_SignatureVerify(restricted, ctxbuf, ctxlen, dig, sig, &r); } break;
      }
      if (rc != MARS_RC_FAILURE) { fprintf(stderr, "emulator answered %d in failure mode, code %d\n", rc, code); return 3; }
      if (strcmp(rule, "D1")) rule = "EMU-F";
      snprintf(tag, sizeof tag, "%s:infail", name);
    } else if (fault) {                                 /* F1: the platform's fault at accept */
      failure = true; rc = MARS_RC_FAILURE; rule = "F1"; snprintf(tag, sizeof tag, "%s:fault%s", name, inited ? "" : ":preinit");
    } else if (code >= 2 && code <= 4) {
      rc = MARS_RC_COMMAND; rule = "N2"; snprintf(tag, sizeof tag, "%s:COMMAND", name);
    } else if (code == 9) {
      bool r = restricted; uint8_t pub[64];
      rc = MARS_PublicRead(r, ctxbuf, ctxlen, pub); snprintf(tag, sizeof tag, "pubread:COMMAND");
    } else if (!inited) {
      rc = MARS_RC_VALUE; rule = "N1"; snprintf(tag, sizeof tag, "%s:preinit", name);
    } else switch (code) {
      case 0:
        if (pct() < 10) {                               /* F2: the bench corrupts a known answer */
          inj = 1 + rnd() % 3; failure = true; rc = MARS_RC_FAILURE; rule = "F2";
          snprintf(tag, sizeof tag, "selftest:katfail:%s", (const char *[]){"", "sha", "hmac", "both"}[inj]); }
        else { rc = MARS_SelfTest(true); snprintf(tag, sizeof tag, "selftest:%s", rc ? "FAIL" : "ok"); }
        break;
      case 5: rc = MARS_PcrExtend(idx, dig); snprintf(tag, sizeof tag, "pcrext:%s", rc ? "REG" : (idx ? "ok1" : "ok0")); break;
      case 6: { uint8_t o[32]; rc = MARS_RegRead(idx, o); if (!rc) memcpy(nx.dout, o, 32);
                snprintf(tag, sizeof tag, "regread:%s", rc ? "REG" : (idx ? "ok1" : "ok0")); } break;
      case 7:
        if (regsel > 3 || ctxlen == 32) { uint8_t o[32]; rc = MARS_Derive(regsel, ctxbuf, ctxlen, o); if (!rc) memcpy(nx.dout, o, 32);
          snprintf(tag, sizeof tag, "derive:%s", rc ? "REG" : (const char *[]){"ok:rs0","ok:rs1","ok:rs2","ok:rs3"}[regsel]); }
        else { rc = MARS_RC_BUFFER; rule = "N4"; snprintf(tag, sizeof tag, "derive:BUFFER"); }
        break;
      case 8:
        if (regsel > 3 || ctxlen == 0 || ctxlen == 32) {
          rc = MARS_DpDerive(regsel, ctxlen ? ctxbuf : NULL, ctxlen);
          if (ctxlen == 0) rule = "EMU-N10";
          snprintf(tag, sizeof tag, "dpderive:%s", rc ? "REG" : ctxlen == 0 ? "ok:reset" : (const char *[]){"ok:rs0","ok:rs1","ok:rs2","ok:rs3"}[regsel]); }
        else { rc = MARS_RC_BUFFER; rule = "N4"; snprintf(tag, sizeof tag, "dpderive:BUFFER"); }
        break;
      case 10:
        if (regsel > 3 || (nlen == 32 && ctxlen == 32)) { uint8_t o[32]; rc = MARS_Quote(regsel, noncebuf, nlen, ctxbuf, ctxlen, o);
          if (!rc) { memcpy(nx.dout, o, 32); CryptSnapshot(nx.snap, regsel, nonce, 32); }
          snprintf(tag, sizeof tag, "quote:%s", rc ? "REG" : (const char *[]){"ok:rs0","ok:rs1","ok:rs2","ok:rs3"}[regsel]); }
        else { rc = MARS_RC_BUFFER; rule = "N4"; snprintf(tag, sizeof tag, "quote:BUFFER:%s", nlen != 32 && ctxlen != 32 ? "both" : nlen != 32 ? "nlen" : "ctxlen"); }
        break;
      case 11:
        if (ctxlen == 32) { uint8_t o[32]; rc = MARS_Sign(ctxbuf, 32, dig, o); if (!rc) memcpy(nx.dout, o, 32); snprintf(tag, sizeof tag, "sign:ok"); }
        else { rc = MARS_RC_BUFFER; rule = "N4"; snprintf(tag, sizeof tag, "sign:BUFFER"); }
        break;
      case 12:
        if (ctxlen == 32) { bool r = false; rc = MARS_SignatureVerify(restricted, ctxbuf, 32, dig, sig, &r); if (!rc) nx.result = r;
          snprintf(tag, sizeof tag, "verify:ok:%s:%d:%s", restricted ? "R" : "U", (int)r, vmode); }
        else { rc = MARS_RC_BUFFER; rule = "N4"; snprintf(tag, sizeof tag, "verify:BUFFER"); }
        break;
    }
    if (known) { nx.rc = rc; nx.fail = failure; nx.st = inited; read_pcrs(&nx, inited); }
    state_str(now, &nx);
    if (known && !strcmp(now, prev)) {                  /* distinguishing CapabilityGet */
      static const uint16_t pts[] = {1, 3, 8, 10};
      for (int k = 0; k < 4; k++) {
        pub_t cg = nx; cg.rc = 0; cg.result = 0; memset(cg.dout, 0, 32);
        uint16_t c2 = 0; bool f = failure; failure = false;
        if (MARS_CapabilityGet(pts[k], &c2, sizeof c2)) return 3;
        failure = f; cg.cap = c2;
        char cs[400]; state_str(cs, &cg);
        if (strcmp(cs, now)) {
          uint8_t z[32]; rbytes(z, 32);
          emit(1, pts[k], draw_idx(), draw_regsel(), draw_len(85,0), draw_len(85,0), rnd() & 1, 0, rnd() & 1, 0, z, z, z, z,
               cs, f ? "E1" : "EMU", "capget:distinguisher", pts[k] <= 8 ? "capget:t1-8" : "capget:other");
          inserted++; break;
        }
      }
    }
    emit(code, pt, idx, regsel, nlen, ctxlen, restricted, fault, init_req, inj, dig, nonce, ctx, sig, now, rule, tag, tcls);
    if (known) { cur = nx; strcpy(prev, now); }
  }
  fclose(fc); fclose(fe); fclose(fm);
  fprintf(stderr, "lines=%ld drawn=%ld distinguishers=%ld\n", line, n, inserted);
  return 0;
}
