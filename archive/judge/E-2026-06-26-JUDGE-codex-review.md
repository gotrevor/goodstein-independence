# E — Judge response to a Codex review (Ren, 2026-06-26, ~lap 147)

> **VALIDATE, don't trust.** Source-grounded pass over the live `Crux2Blueprint.lean` leaves at HEAD
> `0572d20` (docs lap-147). Trigger: the operator relayed a read-only Codex review of the crux-2 live
> path. This note adjudicates each Codex point against source, credits what's right, and corrects the two
> places where the suggested *fix* would send a grind lap into refuted or already-banked ground. Each item
> carries a confidence % + a "how this could be wrong." Converge, don't relitigate.

## TL;DR — Codex is a strong review; act on most of it, with two corrections
- **Direction verdict: agreed.** The live proof is off the false fully-general `redSound` and onto the
  Buchholz existence/reduction argument. The remaining risk is **interface shape-corrections, not
  feasibility** — Codex and the judge land here independently.
- **Adopt:** the 3-leaf count + two-dashboard framing (C2); schedule the dead-`red`-sorry cleanup (C5);
  refresh the stale CURRENT DIRECTIVE next altitude lap (C1).
- **Correct before acting:** the `descent_step_general` generalize (C3) is premature — verify the two
  major-premise cases actually share one reduction first. The gDef "second cut-elim" worry (C4) is the
  sharpest point but is **already de-fanged** by banked machinery — and its suggested fix must keep
  determinism at the STEP, never the orbit (the orbit-level `redLeast`/μ-min was refuted lap-139).

## Convergence (Codex follow-up, 2026-06-26) — both reviewers now agree
- **All 5 critiques: settled** as below. No open disagreement between the two outside reviews.
- **§5.2 (C3): a VALIDATION SPIKE, not a mandate.** Prove the two cases first, generalize only if they
  share one motive (concrete 3-step plan in C3).
- **gDef (C4): graphability coupled to the single-step reduct from the START.** Do not prove a bare `∃ d'`
  and hope definability appears later; do not revive the orbit-wide `redLeast`/μ-min (refuted lap-139).
- **Revised finishability (both reviewers):** **~55–70% full headline** (M2 / Foundation→Z behaving),
  **~75–85% the current M1b-term path** if the next few laps confirm the §5.2 interface shape. Codex's
  earlier 80–90% was a generous ~100-lap horizon and is withdrawn. **Core risk = interface
  shape-corrections, not theorem feasibility** — both reviews land here independently.

## Per-critique adjudication

### C1 — DIRECTION.md stale. ✅ TRUE, structural, mild. (~90%)
CURRENT DIRECTIVE is `Set: lap-146` and still mandates "DROP `descent_step_Ind`" — done lap-146 (commit
`59b339b`); lap-147 advanced to §5.2. **Stale by ~1-2 laps.** This is by-design: the directive is
altitude-lap-owned and refreshes only on review/reflection laps; grind laps take current truth from
`PENDING_WORK.md` / newest `HANDOFF`, NOT the directive's "mandated move." Action: next altitude lap
re-point the directive to §5.2 → (A). No grind-lap action.

### C2 — "two live sorries" undercounts. ✅ TRUE; corrects the judge's own summaries too. (~95%)
Verified: §5.2 is two leaves — `descent_step_K_noncrit_repMajor` (`:2370`) + `descent_step_K_noncrit_axMajor`
(`:2381`) → `descent_step_K_noncritical` (`:2394`). So the **M1b-term live path has THREE genuine leaves**:
`{repMajor, axMajor, exists_sigma1_descending_step (gDef)}`. Keep **two dashboards**:
- **M1b-term live path** (= `false_of_ZDerivesEmpty`): the 3 leaves above. None generational, none need `red`.
- **Full headline** (= `peano_not_proves_goodstein`): + **M2** (Foundation→Z bridge, ~0%, the lone big
  unknown) + top wiring (`goodstein_implies_consistency`). Do not let the M1b dashboard read as "almost done."

### C3 — §5.2 broad; generalize? ✅ CONVERGED (Codex follow-up): VALIDATION SPIKE, NOT A MANDATE. (~70%)
Both reviewers agree `descent_step_general` is a **spike, not a goal**. The shared motive is plausible —
both repMajor and axMajor need a *smaller-premise reduction* + *reconstruction of the outer K-chain with
strict iord descent*. BUT Buchholz §5.2 has genuinely different constructors: **Rep-major = replacement of
the selected (major) premise (chain-promotion); ax-major = an axiom principal cut.** So prove the two cases
FIRST; decide a common motive only after:
1. **repMajor lemma:** "replace a major premise by a same-sequent descending reduct, outer K descends."
2. **ax-major lemma:** the cut-partner / redex-bound lemma, **independent of criticality** — this is exactly
   the "decouple `iRKcCrit` redex-finding from CRITICALITY" the lap-147 commit `112f41b` already began.
3. **THEN** decide whether (1)+(2) fit one strong-iord-induction Γ→⊥ motive; generalize only if they do.
Do NOT write `descent_step_general` as the first move — it risks a general statement that instantiates to
neither case. (Cheap check that would confirm a clean collapse: do both reduce via the same `iRKcCrit`-style
reduct + the same `isChainInf` keep-tip reconstruction used for the ¬-case lap-144?)

### C4 — gDef may become a second cut-elim rewrite. ✅ SHARPEST POINT, but already de-fanged. (~75%)
Codex correctly names the real risk the existence-form pivot introduced: a definability debt at (A), and the
"prove ∃ now, definability later" anti-pattern. **Two source facts narrow it from "second cut-elim" to
"packaging":**
1. **The graph is already IN the obligation, not deferred.** `exists_sigma1_descending_step` (`:2718`)
   demands `∃ (g : V → V) (gDef : 𝚺₁.Semisentence 2), 𝚺₁.DefinedFunction₁ g gDef ∧ …` — the explicit
   parameter-free `gDef` is part of the statement. The "∃-only" trap is structurally avoided.
2. **The iteration definability is BANKED from crux-1.** `exists_sigma1_iterate` (`:2734`) builds the orbit
   as `IIter.iIter gDef g hg z n = g^[n] x` — a proven Σ₁ `PR.Construction` (`IIter.lean`, with
   `iIter_zero`/`iIter_succ`/`iIter_definable'`). So the orbit's definability is NOT re-derived. The only
   remaining content is a **single-step** reduct `g` + its graph; `iIter` packages the orbit.

**The nuance Codex's fix needs (load-bearing):** its suggested "constructive bounded/deterministic step" is
correct **only at the single-step level**. The **orbit-level** deterministic selector (`redLeast`/μ-min
least-witness) was **REFUTED lap-139** (wrong-polarity witness bound) and is on the FORBIDDEN list. So:
determinism (or a primrec witness bound) lives in the single-STEP reduct; the orbit is then iIter, already
definable. Net: (A) is a step-graph + a banked iterator, **not** a fresh cut-elimination. Do NOT re-open the
orbit-level μ-route.

### C5 — dead off-path `red` sorries are noisy. ✅ AGREE, now ripe. (~90%)
`{:80 zKValidF_iIndReduct_of_zInd, :1108 ZDerivation_red_zK_crit, :1257-ish _splice, :1367-ish _nonRep,
:1471-ish redSoundGen}` are documented FALSE/off-path. The directive already authorizes relocating them to
`wip/` as a **deliberate cleanup pass AFTER `descent_step_Ind` drops** — which happened lap-146. So it's now
actionable housekeeping (reduces reviewer/box confusion), NOT count-management. Do it as its own labeled
commit, not woven into a proof lap.

## How this could be wrong
- **C3:** I have not read repMajor/axMajor bodies in full — if they DO share the reduction, Codex's
  generalize is strictly better and my "verify first" is just one cheap check, not a real objection.
- **C4:** my "single-step determinism is provable with a primrec bound" is an *expectation* from the §5.2
  reduct being bounded by the code, not a built proof. If the step-graph itself needs an unbounded search,
  (A) is harder than packaging — but still not a second cut-elim (the reduction content is in §5.2, already
  being built). Watch for this when wiring `g`.
- **Convergence caveat:** Codex and the judge agreeing raises confidence but is not independent of a shared
  blind spot (both reason from the same repo docs). M2's "plumbing" label remains UNVERIFIED by either.

## Pointers
- Live leaves: `Crux2Blueprint.lean:2370/2381/2394` (§5.2), `:2718` (exists_sigma1_descending_step), `:2734`
  (exists_sigma1_iterate, the banked iIter packaging).
- Refuted route (do not reopen): `redLeast`/μ-min (A), lap-139 — see DIRECTION.md FORBIDDEN list.
- Dashboards: M1b-term path = `false_of_ZDerivesEmpty`; full headline = + M2 + wiring.
