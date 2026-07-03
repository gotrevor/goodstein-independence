# ANALYSIS (lap 69) — the `RedSound` wall: `iR2` is ordinal-faithful, NOT derivation-valid

## Where we are
Lap 69 assembled crux-2's entire Gentzen back-half as proven Lean lemmas (`InternalZ.lean` footer),
modulo three named obligations. Driving the headline now hinges on the first one, **`RedSound`**:

    RedSound : ∀ d, ZDerivesEmpty d → ZDerivation (iR2 d)

Both reduct cases are decomposed to chain-validity of the produced reduct:
- tag 3 (Ind): `ZDerivation_iR2_zInd_of_zKValid` reduces it to `zKValid s (irk p) (iIndReductSeq d0 d1 1)`.
- tag 4 (K): `ZDerivation_iCritReduct_of` reduces it to the two `iCritAux` auxiliaries being
  `ZDerivation`s + `zKValid (fstIdx d) (zKrank d - 1) (iCritReductSeq …)`.

## THE WALL (the load-bearing finding)
`iR2` is the **ordinal-model** reduct, NOT the genuine derivation-valid Buchholz reduct. Documented at
`InternalZ.lean:2442–2447`: `iIndReductSeq d0 d1 k = ⟨d1,…,d1 (k copies), d0⟩` is *"ordinal-faithful"*;
the **genuine count `k = ⟦t⟧`** (with the `k=0` special case `d[0]=K^r(d0)`) and the **eigenvariable
substitution `d1(ν/a)`** are explicitly *"deferred derivation-validity concerns."*

Consequence: **`RedSound` is NOT provable for the current `iR2`** (the Ind reduct uses count-1 and the
SAME `d1`, not the substituted copies, so `zKValid (iIndReductSeq d0 d1 1)` is false in general). Do NOT
grind `zKValid`-of-reduct against the current `iR2`. The decomposition lemmas are still correct and
reusable — they take `zKValid` as a hypothesis — but that hypothesis cannot be discharged here.

Also under-constrained (orthogonal, smaller): the I-rule disjuncts carry succedent permissibility but
NOT matrix `IsUFormula`; the Ind disjunct carries no sequent threading. `zKValid`'s formula-hood and
`isChainInf` conjuncts need these regardless.

## TWO ARCHITECTURAL OPTIONS for the next lap (decide first, then execute)

### Option A — upgrade `iR2` to the genuine derivation-valid reduct
Make the Ind reduct use count `⟦t⟧` and eigenvariable-substituted copies `d1(ν/a)`; make the leaf/Ind
disjuncts carry full Buchholz side conditions; then `RedSound` becomes true and provable (Buchholz's
reduction lemma). COST: the ordinal-descent proofs (`iord_descent_iIndReduct`, the count-1 model) are
built on the ordinal-faithful version and would need re-fitting to the real count/substitution. The
ordinal facts (substitution-invariance `õ(d1(ν))=õ(d1)`, `iseqNaddIdg` folds) are already proven, so the
ordinal side should survive; the work is the validity side + re-wiring. Heavy.

### Option B — `ZPreDerivation` (the lean route — RECOMMENDED to evaluate first)
Key insight: the no-infinite-descent contradiction needs the iterate class to be (i) closed under `iR2`,
(ii) have `iord` strictly descending each step, (iii) be populated by the C0.5 bridge from `¬Con`. It does
**NOT** need genuine derivation-validity — only the ordinal-relevant structure the descent capstone
consumes (`zKValid` for K-nodes via `zKValid_of_…`, `isNF` via `isNF_iotil_of_…`). Define a weaker
`ZPreDerivation` capturing exactly that, which the ordinal-model `iR2` DOES preserve (no eigenvariable
obligation), re-prove the descent capstone for it (mostly the same proofs — they already factor through
`zKValid`/`isNF`), and have the C0.5 bridge produce a `ZPreDerivation` (every genuine derivation is one).
RISK: must check the bridge still populates it from `¬Con` and that the descent capstone's inputs are all
`ZPreDerivation`-derivable. If it works, it SIDESTEPS the eigenvariable/count nut entirely — the
consistency proof never needs the substituted reduct, only the descending ordinal sequence.

DECISION HEURISTIC: scope Option B first (one focused pass: define `ZPreDerivation`, check the descent
capstone's exact hypotheses factor through it). If the capstone needs full `ZDerivation` anywhere that
`ZPreDerivation` can't supply, fall back to Option A.

## The other two obligations (unchanged, parallelizable)
2. C0.5 bridge `¬Con(M) → ∃ z:M, ZDerivesEmpty z` (Foundation ⊥-proof → Z ⊥-derivation;
   `InternalZ.lean:3913` docstring; `E-CRUX2-DECOMPOSITION §5`). Produces the starting object.
3. Internalize `n ↦ iord(iR2^[n] z)` as the `𝚺₁` graph `gentzenDescentφ` and prove the per-model
   `gentzen_descent_of_inconsistent` (the disclosed axiom in `wip/GentzenCon.lean`).
