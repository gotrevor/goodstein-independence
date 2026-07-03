# DEEP REFLECTION — lap 101 · 2026-06-25 · the skipped due-diligence (de-risk Path C)

> Primary deliverable of the every-9th reflection lap. Kernel re-verified in-kernel this lap
> (`lake env lean`, green 1325): headline `peano_not_proves_goodstein = [propext, sorryAx,
> Classical.choice, Quot.sound]` (**0 math axioms**, anti-fraud intact), `peano_not_proves_consistency`
> = `[propext, choice, Quot.sound]` (clean), faithfulness anchor `goodsteinSentence_faithful` clean.
> Statement re-audited against the paper (point 4) — no drift.

## The one-paragraph call

**Destination: KEEP. Crux-2 target: KEEP. Sub-route: the Path-X (finitary) commitment was made on
SKIPPED due diligence, and the evidence since now favors reopening it.** The lap-92 reflection (also a
stronger-model lap) diagnosed the finitary eigenvariable presentation as the *cause* of the laps-78–91
wall and recommended pivoting to the ω-rule system (Path C) — **after running a de-risk spike**. Lap-95
overruled to Path X **without running that spike**, and laps 95–100, though mechanically productive, did
**not dissolve** the wall: they *relocated* it from O2 (eigensubst) to the `redZKReady` "hereditary
all-Rep selected spine" motive — which is exactly the conclusion-tracking the ω-rule makes automatic. The
single highest-value action this lap's analysis identifies is to **finally run the skipped spike**: define
the internal ω-rule ∀-node + its critical-cut reduct and confirm in-kernel the reduct is substitution-free.
That one artifact resolves a route decision that has been re-litigated every reflection lap, with EVIDENCE
instead of conviction.

## 1. Is the destination still right? — YES, unchanged

`𝗣𝗔 ⊬ goodsteinSentence` (Kirby–Paris) via Rathjen 2014 Cor 3.7: `γ → PRWO(ε₀) → Con(𝗣𝗔)`, then Gödel II.
- **Faithfulness re-audited THIS lap (reflection point 4).** `goodsteinSentence_faithful` (axiom-clean):
  `(ℕ ⊧ₘ goodsteinSentence) ↔ ∀ m, ∃ N, goodsteinSeq m N = 0`. Traced the RHS to source: `goodsteinSeq m
  (k+1) = bump (base k) (goodsteinSeq m k) - 1`, `base k = k+2`, and `bump b n` recurses on the
  base-`b` exponents (`bump b (Nat.log b n)`) = the genuine HEREDITARY base bump. The headline says exactly
  what Kirby–Paris says. No transcription drift.
- **Single front confirmed.** `peano_not_proves_consistency` axiom-clean (Foundation discharged
  `PA_delta1Definable` upstream, lap-89). The only open obligation is `goodstein_implies_consistency`
  (`Reduction.lean:68`) = crux-1 (γ→PRWO) ∘ crux-2 (PRWO→Con).
- **Honest endpoint (recalibrated, NOT surrendered).** Arithmetizing Gentzen's `Con(PA)` inside IΣ₁ is a
  multi-month/multi-year formalization — strictly harder than Bryce–Goré's *meta-level* Coq `Con(PA)`
  (Feb 2026), which proves Con(PA) *about* PA in a strong metatheory; the repo needs the *internal*
  `IΣ₁ ⊢ (PRWO → Con)`. This is genuine **🟡 project-scale frontier debt** that must be fully discharged
  (operator: axiom-free or abandoned). Feasibility is settled (Bryce–Goré + the repo's own meta `Zinfty`
  both machine-check the cut-elimination math); the remaining work is engineering a known proof. The
  headline will NOT close this lap or soon — and that is the correct, honest state, not a failure.

## 2. Are we attacking the highest-value thing? — the TARGET yes, the ROUTE is the live question

crux-2 (= `redSound`, internalized cut-elimination) is the sole remaining math content on the headline.
No drift, no easy-leaf bagging — laps 95–100 stayed on the crux. The question is one level down: **which
cut-elimination presentation to arithmetize.** And here the trajectory shows the circling signal a
reflection lap exists to catch.

**The laps-95→100 trajectory, read honestly.** The K-case validity went from "open" to "one consolidated
`redZKReady` predicate, with the I∀/I¬/axAll non-Rep replace cases assembled." Real localization — BUT the
*deep* content did not close; it moved. The eigensubst wall (O2, laps 78–91) became the conclusion-tracking
motive (`redZKReady`'s hereditary all-Rep selected spine). And the motive's hard core does not look like a
clean induction away:

> A ∅→⊥ chain `zK s r ds`'s premises have **growing** antecedents `Γᵢ ⊆ Γ ∪ {A₀..A_{i-1}}`, so a selected
> premise `dᵢ` concludes `{A₀..A_{i-1}} → Dᵢ`, **not** `∅→⊥`. Hence Cor 2.1 (selected-premise-is-Rep, the
> first hereditary level) does NOT directly reapply to `dᵢ`. The "hereditary all-Rep" invariant is a
> repo-specific artifact of the design choice to keep `Π` (`fstIdx_iRK = fstIdx d`) and patch with
> `tpReduce` — it is not part of Buchholz's standard treatment, and whether it even holds as stated is
> open.

This is the lap-92 pattern repeating: the finitary route keeps spawning subtle conclusion-tracking
invariants. Each is a potential wall, and the remaining finitary obligation list is LONG:
`redZKReady` motive · axNeg ¬-cut · `zKValidF_iIndReduct_of_zInd` (Ind) · `ZDerivation_red_zK_crit` (5.1) ·
`ZDerivation_red_zK_splice` (5.2.1) · `iord_descent_red` (ordinal K-case) — then M2 + M3 + wiring.

## 3. What a sharp outside expert sees we're missing — the SKIPPED spike

**The lap-95 route decision was made without the evidence lap-92 said to gather first.** lap-92's
recommendation was explicit: "a `wip/InternalZomega.lean` SPIKE that defines the internal ω-rule ∀-node
+ its critical-cut reduct and *confirms by elaboration* the reduct is substitution-free, BEFORE committing."
That spike was **never written** (`find` confirms no such file ever existed). Lap-95 committed to Path X on
a kernel read ("O1/O2 are done, the wall is one false hypothesis") that the subsequent 5 laps did not bear
out. A route decision governing ~6 laps (and counting) was taken on un-de-risked grounds. **That is a
process gap a reflection lap must close — and the fix is not a reckless counter-pivot, it is to run the
spike.**

**Why the ω-rule is the strong prior.** Two *independent* machine-checked proofs that the cut-elimination
math works in the ω-rule presentation:
1. **Bryce–Goré** (the only complete `Con(PA)`, Coq, Feb 2026) work in infinitary `PA_ω`: `w_rule1`
   premises indexed by all closed terms, **no eigenvariables**; cut-elimination *selects* the witness
   premise (substitution-free).
2. **This repo's OWN meta engine** `Zinfty.lean` (1560 lines, in `src/`, axiom-clean) already replaces
   Foundation's finitary `all` with the ω-rule `allω` and machine-checks the full Towsner §19
   cut-elimination. The hard math is already cracked — in the ω-rule presentation.

In an ω-rule node, `∀xF` comes from a premise family `{dₙ ⊢ Γ→F(n)}`; a critical cut **selects `dₙ`**
(already deriving `Γ→F(n)`). Therefore O2 (eigensubst) GONE, O1 (freshness) GONE, route-B `tpReduce`
conclusion-tracking AUTOMATIC, and the `redZKReady` motive — the current wall — never arises. One
architectural change retires the entire remaining finitary obligation list.

**The honest, unprobed risk (this is why it is a spike, not a fait accompli).** Arithmetizing the ω-rule
premise family as a Σ₁ recursive notation (Buchholz §6 `Z*`: `h[n] = h₀(x/n)`) inside IΣ₁, with
cut-elimination by recursion on `iord < ε₀`, is NEW and could carry its own wall. **Mitigants, gathered
this lap:** (a) the repo already arithmetizes premise *sequences* (`zKseq`/`iIndReductSeq`/`iRepeatSeq`);
(b) the premise-`n` computation `h₀(x/n)` reuses the existing axiom-clean `zsubst` (substitution of a
NUMERAL `n` — benign, and crucially it lives in the *premise-family data* where validity is *assumed*, NOT
in the cut-reduction where validity must be *proved*; that is precisely why O2 dissolves); (c) recursion
on `iord<ε₀` is *licensed by the PRWO(ε₀) hypothesis itself*; (d) the whole `iord`/`icmp`/`idg`/`iõ`/ω-tower
ordinal engine (laps 58–61, axiom-clean) is reused unchanged; (e) `Zinfty.lean` is a worked template for
every cut-reduction case.

## 4. Faithfulness at altitude — CLEAN

Headline statement = genuine Kirby–Paris (point 1 audit). Headline `#print axioms` = trust-base + the lone
`sorryAx` (the disclosed headline `sorry`); **0 math axioms**, no `🔴`. `goodsteinSentence_faithful` and
`peano_not_proves_consistency` both clean. Anti-fraud intact — the headline is NOT wired to any axiomatized
girder; `goodstein_implies_consistency` carries its open obligation openly as a `sorry`.

## The deliverable: direction call

- **KEEP doing:** crux-2 = `redSound` is the right target; the ordinal engine + `Zinfty` meta template +
  `zsubst`/premise-sequence machinery are reusable assets; faithfulness discipline (`#print axioms` gating,
  bare-`sorry` headline) is working.
- **STOP doing:** re-litigating the finitary-vs-ω-rule fork by conviction each reflection lap. Specifically:
  **do not sink further laps into the `redZKReady` hereditary-Rep motive / axNeg ¬-cut until the spike has
  run.** Those are precisely the obligations the ω-rule would retire; grinding them before the route is
  settled risks more of the laps-78–100 pattern.
- **SINGLE highest-value next target:** **the de-risk spike `wip/InternalZomega.lean`** — define the
  internal ω-rule ∀-node `zAllω` (premise family via `zsubst h x (numeral n)`), define the critical-cut
  reduct that SELECTS premise `t`, and confirm in-kernel that the reduct is substitution-free (the reduct =
  the already-given premise-`t`, no `fvSubst` in the reduction step) and that the conclusion-tracking
  `tpReduce`-analogue is automatic. **Decision rule (the point of the spike):** if it elaborates clean →
  pivot to Path C, retiring the finitary obligation list. If it walls on the Σ₁ arithmetization → commit to
  Path X with the evidence that finitary is genuinely the only feasible internal route. Either outcome ends
  the re-litigation.
- **Do NOT tear down Path X.** The finitary infrastructure (`InternalZ`, `Zsubst`, `Crux2Blueprint`) stays
  in `src/`, green, axiom-clean — it is the fallback and most of it (the ordinal side, `zsubst`, the Z
  object theory) transfers to Path C anyway. This is a fork-resolution lap, not a demolition.

**Trajectory verdict:** laps 95–100 are genuine engineering progress but on a sub-route whose feasibility
was never established against the proven alternative. The destination is sound; the next lap's job is to
buy the missing evidence, cheaply, before spending more laps on either branch.
