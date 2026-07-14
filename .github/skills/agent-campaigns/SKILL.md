---
name: agent-campaigns
description: >-
  Long-term memory and handoff protocol for larger multi-step work in this repo,
  stored under the untracked agents/ folder. USE WHEN: starting, resuming, or
  handing off a "campaign" (multi-session / multi-step / multi-file effort);
  planning larger work; recording plan/status/context for the next agent;
  capturing reusable insights ("tactic X works", "Y is a typical hurdle"). Each
  campaign keeps a PLAN.md (plan + status + resume context, updated after every
  completed task) and an INSIGHTS.md (strict-format insights). A shared
  agents/GENERAL_INSIGHTS.md is read by all campaigns and is never written to
  automatically.
---

# Agent campaigns (long-term memory & handoff)

Larger work in this repo is organized into **campaigns** whose state lives in the
untracked `agents/` folder so any future agent can resume it.

```
agents/
  GENERAL_INSIGHTS.md          # cross-campaign; ALWAYS read, NEVER auto-write
  <campaign-slug>/
    PLAN.md                    # plan + status + resume context
    INSIGHTS.md                # campaign insights (strict format)
```

`agents/` is git-ignored. Never commit it.

## When is something a campaign?

Create a campaign only if **either**:

- the user explicitly labels it a campaign, **or**
- you judge the work is campaign-sized (multi-session, multi-step, or spanning
  multiple files) — in which case **ask the user to confirm before creating it**.

Do not create campaign files for quick, one-off edits.

## Starting a campaign

1. Pick a kebab-case slug from the topic (e.g. `synthesis-qed-speedup`).
2. Create `agents/<slug>/PLAN.md` using the template below — the onboarding block
   MUST be first.
3. Create `agents/<slug>/INSIGHTS.md` with the header from the strict format below.

## Resuming a campaign (do this first, every time)

1. Read `agents/<slug>/PLAN.md` — start with its onboarding block.
2. Read every skill it lists.
3. Read `agents/<slug>/INSIGHTS.md` (campaign insights).
4. Read `agents/GENERAL_INSIGHTS.md` (cross-campaign insights).
5. Only then continue the work.

## The iron rule: keep PLAN.md current

**After every completed task, before starting the next**, update `PLAN.md`:

- move the finished item to done / tick it,
- refresh **Status**,
- refresh **Context for the next agent** (dead-ends, open questions, key files).

A stale `PLAN.md` is a bug. Update it even if the session is ending abruptly.

## Capturing insights

- Campaign-specific insight → append to `agents/<slug>/INSIGHTS.md` using the
  strict format below.
- Cross-campaign insight → do **not** edit `GENERAL_INSIGHTS.md` yourself; note the
  candidate in the campaign INSIGHTS.md and let the user decide to promote it.
  Only write to `GENERAL_INSIGHTS.md` when the user explicitly instructs you to.

## Strict insight format (mandatory — enables clean merging)

Every insight is a single top-level bullet, one entry, in exactly this shape:

```
- **[<tag>] <short claim>.** <supporting detail, 1-3 sentences.> — evidence: <file/lemma/command>
```

Rules:

- One bullet per insight; no nested prose paragraphs.
- `<tag>` is a lowercase category, e.g. `koika`, `tactic`, `qed`, `build`, `dune`.
- Start the claim in **bold**; it must be self-contained (readable out of context).
- Always end with `— evidence:` pointing to a file, lemma, or command.
- Keep it factual and reusable; no session narration.

Because `GENERAL_INSIGHTS.md` uses the same format, promoting an insight is a
verbatim copy of the bullet.

`INSIGHTS.md` header (create the file with this):

```
# Insights: <campaign name>

> Strict format: one bullet per insight —
> `- **[tag] claim.** detail — evidence: <ref>`

---
```

## PLAN.md template

```
# Campaign: <name>

## ⚠️ Agent onboarding (read before doing anything)
- Read these skills: <e.g. rocq-iterative-proving, coq-fragile-proofs>
- Read agents/<slug>/INSIGHTS.md (this campaign's insights)
- Read agents/GENERAL_INSIGHTS.md (cross-campaign insights)

## Goal
<what success looks like>

## Status
<current state; last completed task; what is in progress>

## Plan
- [ ] task 1
- [ ] task 2

## Context for the next agent
<resume notes, dead-ends, open questions, key file references>
```
