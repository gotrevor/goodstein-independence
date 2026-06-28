# ROUTE ESCALATION — Goodstein-independence, 2026-06-28 (operator-ratified M2 probe)

> First firing of the `DIRECTION.md` ROUTE GUARD. Both pre-registered Route-A abort triggers fired and
> went unacknowledged for ~40 laps. This is the escalation record + the corrected confidence forensic +
> the deciding experiment (a bounded 5-lap M2 probe) the operator ratified. **Self-contained — pasteable
> to an outside reviewer (Codex).**

## 1. The triggers that fired (both pre-registered, both ignored)
- **T1 — M1 overrun** (`E-CRUX2-ROADMAP-2026-06-24.md`, lap 83): *"if M1 (RedSound = the cut-elim
  validity core) is not a proven theorem within ~40 laps of lap 83 (≈ lap 123), STOP and reweigh Route
  B — the pre-agreed decision point, not a vibe."* **FIRED.** Now lap 166; RedSound is still 2 open
  sorries (`ind_reduct_anySucc`, `residual`).
- **T2 — second false summit** (`E-ROUTE-OPTIONS-2026-06-24.md`, lap 81): *"if the genuine-reduct /
  cut-elim core hits a second false summit, reweigh the meta / growth-rate pivot."* **FIRED ≥4×** since
  lap 81 (redLeast μ-route, the `seqUpdate` splice, same-degree `õ`-drop, the orphaned ⊥-cluster chased
  ~30 laps).

Neither trigger was ever checked. Every altitude lap 137→166 wrote "direction KEPT"; no judge session
re-opened the route. **Root cause: both governance layers (the every-9th reflection AND the self-appointed
judge) only ever re-evaluated *within* the route, never *whether the route is right*.** Now patched: the
`DIRECTION.md` ROUTE GUARD (reflection layer) + the JUDGE-HANDOFF route-status duty (judge layer). The
mechanical (host-side) layer is NOT yet built — see §6.

## 2. Corrected confidence forensic (the "~80%" was a sub-goal, never the headline)
At lap ~147 (`E-2026-06-26-JUDGE-codex-review.md`) the judge + Codex converged on:
- **~75–85% the crux-2 ENGINE path** (`false_of_ZDerivesEmpty`) closing — *conditional on "the next few
  laps confirm the §5.2 interface."* They didn't: lap 166 found ~30 of those laps chased **orphaned dead
  code**, and the 2 live sorries are the deep Buchholz cut-elim core needing primitives "the repo can't
  build yet."
- **~55–70% the FULL HEADLINE** — the gap = **M2 (Foundation→Z bridge), flagged "~0%, the lone big
  unknown,"** still ~0% 19 laps later.
- Codex's standalone earlier **80–90% was explicitly WITHDRAWN** in that same doc ("a generous ~100-lap
  horizon").
- The agreement was **non-independent and the doc said so**: *"Codex and the judge agreeing ... is not
  independent ... M2's 'plumbing' label remains UNVERIFIED by either."* Two LLM reviewers reading the same
  optimistic handoffs = one blind spot doubled, not corroboration.

Honest full-headline trajectory: **~70% (lap 61) → ~55–70% (lap 147) → ~30–40% (now, continuing A)** — a
steady decline, with the deferred unknown (M2) never moving.

## 3. The decision frame
Headline-or-abandon (operator: bank-and-downgrade is OFF the table). Both routes formalize **documented
textbook math** — neither originates new mathematics; "un-formalized in Lean" is the job, not a deviation.
The real axis is formalization *ergonomics*:
- **Route A** girder = IΣ₁-**internalized** cut-elim over coded derivations — unprecedented in any prover;
  the source of all 110 laps of `red`/`GenReductCert`/`zsubst` grind; forced (not chosen) by routing
  through Foundation's Gödel II, which needs the *internal* `PA ⊢ (γ → Con(PA))`.
- **Route B** girder = growth-rate / Wainer domination — **meta** (over Lean types), with a tested,
  axiom-free Coq substrate to port (Castéran ε₀/Hardy/Wainer) + simpler wiring (no Gödel II, no bridge).

Judge lean: **pivot to B (~60%)** — but run ONE bounded test of A's last *unexamined* risk first.

## 4. The deciding experiment — a bounded 5-lap M2 probe (do NOT grind the engine)
The engine (the 2 cut-elim sorries) already had its 18-lap test → false summits → ~0 new info per lap.
**M2 — the Foundation→Z bridge — has NEVER been examined** (on the FORBIDDEN list "until the engine is
sorry-free," so it sits at ~0% with its "bounded plumbing" label UNVERIFIED). It is the one probe whose
outcome is **decisive in both directions**, so spend the 5 laps there:

1. **STATE** `foundation_bot_to_Z_empty : 𝗣𝗔.DerivationOf d ⊥ → ∃ z, ZDerivesEmpty z` (M-internal) with
   its real type, in `wip/M2Probe.lean` — a feasibility spike, **NOT** headline wiring.
2. **LAND** the cheap cases per the Bryce–Goré `Peano.v` blueprint (`scratchpad/Gentzen-bg/`, ~1215 lines):
   PA axioms → Z atomic; **PA-induction → native Z-`Ind`** (Z's native `Ind` rule — the roadmap's "cheap
   part" that B–G paid for and we skip).
3. **ASSESS** the M-internal Σ₁ coding overhead on those cases.

**HARD GATE — lap 171, no extension.** Verdict (write it here, hand to operator):
- cheap cases land (or clearly will) with **bounded** coding ⟹ **`M2-PLAUSIBLE`**: A is more alive than
  ~30–40% suggests; reconsider continuing A on a re-scoped budget with a *fresh* trigger.
- coding **balloons** / a second internalization swamp ⟹ **`PIVOT-B`**.

No lap 172 on A. (`(3) bank-and-downgrade` stays off the table — headline or full abandonment.)

## 5. Ask for Codex (outside reviewer)
1. **Pressure-test the probe choice (argue against, don't ratify).** Is M2 the right decisive probe, or
   is there a *cheaper* experiment that distinguishes "A finishable" from "A swamp"? Your lap-147 co-sign
   was the non-independent agreement that masked this — so disagree on purpose.
2. **Sanity-check the cheap-cases plan.** Does `PA-induction → native Z-Ind` actually carry **M-internally**,
   or does the Σ₁ coding of the bridge re-introduce the same arithmetization tax as the engine? If the
   latter, that *is* the `PIVOT-B` verdict — say so.
3. **Independent finishability.** Give your own full-headline number **grounded against the source / the
   `Peano.v` blueprint**, NOT against this repo's handoff docs (the shared-blind-spot failure mode). State
   your ground explicitly so we can tell it apart from the judge's.

## 6. What is NOT yet patched (so the next spin gets caught mechanically)
The two layers fixed so far (ROUTE GUARD + judge duty) are **advisory** — a doc a lap must read and obey.
Advisory is exactly what failed: "ALTITUDE CAUTION: only the crux left ≠ almost done" sat in *every*
directive and was ignored ~30×. The layer that actually works in this repo is **mechanical** (`.githooks`
build gate, `lean-axiom-gate` CI — they HALT, no judgment required). The route trigger needs the same: a
host-side `lean-treadmill` gate that reads the laplog, checks registered triggers (lap deadline +
false-summit count) each lap, and HALTS / forces an escalation lap when one fires. Proposed, not built.
