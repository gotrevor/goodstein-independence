# DEEP REFLECTION — 2026-06-26 · lap 132

> Every-9th-lap altitude pass. Build re-verified 🟢 green (`lake build GoodsteinPA`, 1326 jobs).
> Headline footprint re-verified in-kernel: `peano_not_proves_goodstein =
> [propext, sorryAx, Classical.choice, Quot.sound]` — **0 math axioms**, lone `sorryAx` = crux-2.
> Statement re-audited vs source — **no drift** (details in §4). HEAD at entry `5748b4b` (lap 131).

---

## TL;DR — the direction call

**Destination KEPT. Faithfulness clean. But the recent ~12 laps (120→131) have been paying down a
debt that may be an ARTIFACT of one design choice, and I am recommending a real course-test.**

The genuine open crux (crux-2 = internalized Gentzen consistency) has, since lap 120, been attacked
as: "make the *fixed, deterministic, permIdx-based* engine `red` not STALL, so that `red`-fixpoint ⟹
cut-free holds and the fixpoint branch of `false_of_ZDerivesEmpty` closes." That sub-goal forces an
open-ended campaign — `firstBotPrem_reducible`, the `majorIdx` re-key, the tag-5/6 critical dispatch,
and a *succession* of invariant folds (`zReg` lap 119, `zFresh` 126-128, `seqAntSeq` 131) + ZPhi
exact-shape strengthenings (`zAx1` 115, `zAxNeg` 118, `zAxAll` 131, `zIneg` pending).

**The stall exists ONLY because we demand `red` be a total Σ₁ FUNCTION that descends on every orbit
step.** Reformulate the endgame to the *existence / least-descending-reduct* form and "fixpoint ⟹
cut-free" becomes **definitional**, the permIdx-selection-correctness campaign (laps 120-131's
`majorIdx`/`firstBotPrem`/tag-dichotomy) is **obviated**, and the genuinely-hard banked work
(per-reduct soundness laps 112-119 + the invariant folds + the per-reduct descent lemmas) is **fully
reused**. This reframing has NOT been considered in any analysis doc (verified by grep). Highest-value
next move = a cheap `wip/` spike to test it, exactly as lap-101's spike settled the Path X/C fork.

---

## 1. Is the DESTINATION still right?  — YES, and it is the only honest one.

**Where it's going.** Kirby–Paris: `𝗣𝗔 ⊬ Goodstein`. Route (resolved lap 45→46, unchanged since):
`𝗣𝗔 ⊢ γ →(crux-1, §3 all-primrec) 𝗣𝗔 ⊢ PRWO(ε₀) →(crux-2, Gentzen ordinal analysis) 𝗣𝗔 ⊢ Con(𝗣𝗔)`,
then Gödel II. Why it's worth it: a *fully machine-checked, axiom-free* Kirby–Paris independence —
the canonical "true but PA-unprovable" theorem — with the Gentzen consistency proof arithmetized
inside IΣ₁. Nothing of this depth exists in mathlib.

**Has new information changed the realistic endpoint?** No — and the obvious shortcuts are already
*actively refuted*, not merely untried:
- The **semantic / fast-growing-function route** (Goodstein dominates `H_{ε₀}` ⟹ not PA-provably-total)
  was empirically refuted lap 98: Rathjen §3's slow-down is *primrec-only*; a free-`X` oracle descent
  is not primrec-dominated, so `DescentSemantic:582` asks the impossible. `peano_not_proves_TI`
  (Buchholz free-X, axiom-clean) is a banked asset but OFF-path (free-X-TI ⊢ PRWO is the wrong
  direction). The characterization of PA's provably-recursive functions IS ordinal analysis — no escape.
- The repo's own faithfulness invariant (`Statement.lean`, `DIRECTION.md`) correctly **forbids
  axiomatizing crux-2**: a bare `axiom` for `TI(ε₀) ⊢ Con(PA)` smuggles the whole theorem. So the
  honest endpoint is the *built* crux-2, not a cited axiom. There is no narrower honest axiom: crux-1
  already *proves* `PRWO(ε₀)` axiom-clean, and the remaining content (cut-elimination soundness +
  ordinal descent on codes) is irreducibly the hard part.

**Honest scope.** crux-2 (arithmetized cut-elimination inside IΣ₁, total on non-standard codes) is
multi-year-class — but that is licensed, and "needs deep machinery" is a hypothesis to test, not a
verdict. The realistic state today is **"one open girder (crux-2) + a faithful, axiom-clean
remainder"**, with the girder being a *proven theorem under formalization* (a disclosed `sorryAx`),
NOT an open conjecture. That is the correct honest checkpoint.

## 2. Are we attacking the highest-value thing?  — Yes (hardest-first honored), with a structural inefficiency.

The entire residual is crux-2's engine `red`/`iord`. Crux-1 is done axiom-clean; the statement is
faithful; the two independent downstream pieces (`false_of_ZDerivesEmpty` descent-branch wiring, M2
`foundation_bot_to_Z_empty` embedding) are untouched but genuinely lower-value plumbing. So the focus
on the engine is correct per hardest-first.

**But read the trajectory lap-over-lap (git log is the proxy; no treadmill jsonl exists):** the
engine SWAP has been "the next step" since **lap 119** (13 laps). Within it the diagnoses have
*converged* (good) — laps 92/101/111/120/129 all re-pin the crux to the `red`-engine on the ⊥-orbit —
but the *work* is a sequence of mini-campaigns each "mirror the existing fold machinery":
`zReg` (119), `zFresh` (126-128), `seqAntSeq` (131 → pending fold), plus ZPhi disjunct strengthenings
each a ~64-site ripple. Lap 131's own handoff: the lap-130 "turnkey" plan "found its hidden depth";
the "self-healing" claim was FALSE. **This is the smell of fixation on one *formulation*, not of a
dead end** — the pieces do land, but the formulation keeps spawning obligations.

## 3. What a sharp outside expert would say we're MISSING — the deterministic engine is the artifact.

Read `false_of_ZDerivesEmpty`'s intended closure (`Crux2Blueprint:1281-1314`):

```
iord_red_iterate_descends :  red^[n+1] z = red^[n] z  ∨  iord(red^[n+1] z) ≺ iord(red^[n] z)
```

The endgame closes the **descent** disjunct by PRWO (infinite ε₀-descent forbidden) and the
**fixpoint** disjunct by "a `red`-fixpoint on a ⊥-orbit is cut-free, hence absurd." Lap 129 *refuted*
the easy version of that second implication: a permIdx-leaf-stall fixpoint is a genuine valid ⊥-orbit
derivation, NOT cut-free. So the whole laps-120-131 campaign exists to *force* "fixpoint ⟹ cut-free"
to hold for the **fixed permIdx engine** — by re-keying selection to `majorIdx` so the engine can't
stall on a leaf.

**The reframing: define the iteration as the least *descending* reduct, not a fixed selector.**

```
redLeast(d) := least d'  such that  [ ZDerivesEmptyR d' ∧ icmp (iord d') (iord d) = 0
                                       ∧ d' is a one-step cut-reduct of d ]      -- Σ₁ (least-witness)
            := d   if no such d' exists                                          -- the "fixpoint"
```

Then **"`redLeast(d) = d`"  ⟺  "no descending reduct exists"  ⟹  "`d` is cut-free"** — by the
*contrapositive of a single existence lemma*, NOT by proving any selector is faithful:

> **(E) existence lemma.**  `ZDerivesEmptyR d` ∧ `d` not cut-free  ⟹  `∃ d', ZDerivesEmptyR d' ∧
> iord d' ≺ iord d ∧ d' a cut-reduct of d.`

Everything the existence form needs is **already banked or trivially within reach**:
- Every ⊥-derivation's root is Ind or K — `zTag_Ind_or_K_of_ZDerivesEmpty` (`InternalZ:8636`). A leaf
  axiom cannot conclude `∅→⊥` (Cor 2.1, `tp_selected_isymRep_of_emptyAnt_botSucc` `:7684`).
- The K-node *critical* reduct is sound — laps 112-119 (`ZDerivation_iRKcCrit_all` + ¬-twin), and
  descends — `iord_descent_iRKcCrit_corr`/`_neg` (`RedZKDescent:580/597`). The Ind reduct: sound +
  `iord_descent_red_zInd` (`Crux2Blueprint:1116`).
- The dichotomy `iRcrit_descends_or_zInd_zK_premise` (`RedZKDescent:734`) already *is* essentially (E)
  at the root: it descends, OR the redex is a zInd/zK premise (recurse / it's a real cut pair).
- The invariant folds `ZRegular_red`/`ZFresh_red` and the pending `seqAntSeq` fold give that `redLeast d`
  stays in `ZDerivesEmptyR` — **needed in BOTH formulations**, so the recent fold work is NOT wasted.

**What the existence form ELIMINATES:** the obligation to prove a *fixed deterministic* selector
(`permIdx`/`majorIdx`) never mis-selects across an *unbounded orbit*. The redex-pair combinatorics
("which premises form the principal cut") survives — but as a **one-shot `∃`** discharged immediately
by reduce-and-descend, not as a total Σ₁ function whose correctness must be threaded through every
orbit step + every invariant fold. The fixpoint-branch reasoning becomes definitional; the
`majorIdx` re-key, `firstBotPrem_reducible`, the tag-5/6 dispatch, and the remaining ZPhi exact-shape
strengthenings (whose only consumer is the fixed engine's soundness *derivation*) are obviated.

**Honest caveat (not over-selling).** The hard combinatorial content — "this ⊥-chain has a reducible
cut pair, and its reduct is sound + descends" — is SHARED; the spike must confirm (E) is genuinely
provable at the root without re-importing the stall through the back door (the "is there a real cut
vs. a structurally-cut-free chain" determination is exactly Cor 2.1's job and must be clean). This is
a course-TEST, decisive either way, not a declared win.

## 4. Faithfulness at altitude — re-audited, no drift.

- Headline `peano_not_proves_goodstein` (`Statement.lean:22`): `𝗣𝗔 ⊬ ↑goodsteinSentence`. In-kernel
  `[propext, sorryAx, choice, Quot.sound]` — 0 math axioms.
- `goodsteinSentence_faithful` (`Bridge.lean:34`): `(ℕ ⊧ₘ goodsteinSentence) ↔ ∀ m, ∃ N, goodsteinSeq
  m N = 0` — axiom-clean `[propext, choice, Quot.sound]`. The semantic anchor holds.
- `goodsteinSeq`/`bump` (`Defs.lean:30/46`): `bump b n = (n/b^e)·(b+1)^(bump b e) + bump b (n%b^e)`
  (recurses on exponent `e=log_b n` AND remainder) with `base k = k+2`, `G(k+1)=bump(base k)(G k)-1`.
  This IS the genuine hereditary-base Goodstein sequence — anti-vacuity satisfied.
- `peano_not_proves_consistency` (`Reduction.lean:36`, Gödel II): axiom-clean. `𝗣𝗔.Δ₁` discharged
  upstream (lap 89) — Foundation *proves* it, not an axiom.
- The lone `sorryAx` traces exactly to `goodstein_implies_consistency` (`Reduction.lean:68`, bare
  `sorry`), which Crux2Blueprint will discharge once crux-2 is built (the file is standalone WIP, not
  yet wired — by design, "only when `#print axioms` is clean").

## Direction record

- **KEEP doing:** the destination + route; per-reduct soundness (laps 112-119); the invariant folds
  (`zReg`/`zFresh`, and finish the `seqAntSeq` fold — needed in *both* formulations); the per-reduct
  descent lemmas. Commit every green build; honest disclosed sorries.
- **STOP doing (pending the spike verdict):** sinking laps into the *fixed-engine* permIdx→`majorIdx`
  swap and selection-correctness (`firstBotPrem_reducible`, the tag-5/6 dispatch, the stall campaign)
  and the ZPhi exact-shape strengthenings whose only consumer is that engine's soundness derivation.
  These are the pieces the existence form obviates.
- **Single highest-value next target:** a self-contained `wip/` spike `ExistenceEndgame.lean` — define
  `redLeast` (Σ₁ least-descending-reduct), state (E) the existence lemma, and assemble the existence-form
  `false_of_ZDerivesEmpty` = `redLeast`-orbit descends-while-cut + PRWO + Cor 2.1, signatures pinned
  against the real `InternalZ`/`RedZKDescent`/`Crux2Blueprint` API, bodies sorried where the banked
  lemmas plug in. **Decision rule (mirror lap-101):** (E) discharges cleanly at the root from the
  banked descent/soundness ⟹ PIVOT the endgame, drop the stall campaign. (E) walls (re-imports the
  stall) ⟹ fall back to the engine swap *with that evidence*, and the spike's `redLeast` still
  documents why. Either way the lap advances the crux.
