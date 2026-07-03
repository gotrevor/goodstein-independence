# Lap 114 — the cut-elimination inversion is feasible, not a multi-year wall

**TL;DR.** The crux-2 "prize" `ZDerivation_red_zK_crit` (the critical-cut SOUNDNESS inversion,
`Crux2Blueprint:100`) is **FALSE as currently stated**, for a precise and fixable reason: `red`'s
critical reduct substitutes the eigenvariable by `0`, but Buchholz §3.2 case 5.1 cut-elimination
requires substituting the **L-redex instance `k`**. The fix is a *contained* re-principalization of
`red`'s tag-4 critical branch — NOT the multi-year `Zinfty.allInv` machinery the prior laps assumed.
The building blocks (`ZDerivation_zsubst_zIall_premise` + the new `seqSucc_zsubst_zIall_premise`) are
already banked in `src/`. This reframes the project's deepest open piece.

## The chain of reasoning (kernel-grounded)

1. **The inversion reduces to two stripped halves.** `ZDerivation_red_zK_crit` delegates to
   `ZDerivation_iRcritG_of` (`InternalZ:8336`), which — because the outer recombination chain's
   validity is automatic (`zKValidF_iCritReductGen`, "the inner premise sequences ds0/ds1 are
   immaterial to the outer chain's validity", `InternalZ:3126`) — reduces the whole thing to the two
   half-derivations being `ZDerivation`s:
   - `haux0 : ZDerivation (zK (seqSetSucc (fstIdx d) (cutFormula d)) (zKrank d)
       (seqUpdate (zKseq d) (redexI d) (ρ (redexI d))))` — concludes `Γ → cutFormula d`.
   - `haux1` — concludes `cutFormula d, Γ → Δ`.

2. **`cutFormula d` is the stripped INSTANCE `F(k)`.** For an `∀`-redex (R-principal `A_i = ∀xF`),
   `cutFormula d = substs1 (numeral k) F` with `k = π₁(π₂(tp (redexJ premise)))` — the instance read
   off the L-redex **axAll** premise (`cutFormula` / `cutFormula_all`, `InternalZ:6484/6517`).

3. **`haux0`'s threading forces the redexI premise to derive `F(k)`.** `isChainInf` needs
   `∃ j₀, chainAsucc ds0 j₀ = seqSucc (seqSetSucc s C) = cutFormula d`. The only premise that can carry
   `F(k)` is the redexI slot, so `seqSucc (fstIdx (ρ (redexI d))) = cutFormula d = F(k)` is REQUIRED.

4. **But `ρ = zAxReduct ∘ red` supplies `F(0)`, not `F(k)`.** `red (zIall s a p d0) = zsubst d0 a
   (numeral 0)` (`red_zIall`, `InternalZ:7198`), so its succedent is `substs1 (numeral 0) p = F(0)`
   (`red_zIall_tpReduce`). `zAxReduct` is the identity off tags 5/6, so `ρ (redexI) = zsubst d0 a 0`.
   `F(0) ≠ F(k)` for `k ≠ 0` ⟹ **`haux0` is unprovable for this `ρ`**. `red`'s critical reduct is
   UNSOUND (it loses the cut instance).

   *Why it went unnoticed:* instance-0 is **correct for the ordinal DESCENT** — `iord (zsubst d0 a n)`
   is instance-invariant, which is exactly why `iord_descent_red` (laps 108–113) is sound and survives.
   The defect is only on the SOUNDNESS (`ZDerivation`) side, which the descent laps never exercised on
   the critical node. This is lap-104's `red_redAllEx_eq` "re-principalize" finding, now pinned to the
   live engine `red` (post the lap-107 pivot off the external `ZInf` prototype).

## The fix (contained)

The critical reduct's R-redex premise must be `zsubst d0 a (numeral k)`, NOT `zsubst d0 a (numeral 0)`,
with `k = π₁(π₂(tp (redexJ d)))` (the L-redex instance, same `k` that `cutFormula` already reads). Then:

- **succedent:** `seqSucc (fstIdx (zsubst d0 a (numeral k))) = substs1 (numeral k) p = cutFormula d`
  — the new `seqSucc_zsubst_zIall_premise` (`Zsubst.lean`, banked this lap, axiom-clean), modulo the
  eigenvariable freshness `hpfresh : fvSubst a (numeral k) p = p` (Buchholz O3, supplied on the ⊥-orbit
  by the embedding's fresh-eigenvariable choice).
- **derivability:** `ZDerivation (zsubst d0 a (numeral k))` — `ZDerivation_zsubst_zIall_premise`
  (`Zsubst.lean:1879`, banked), modulo `maxEigen d0 < a` (O1 freshness).
- **I¬ redex needs NO change:** `red (zIneg s p d0) = d0` carries no instance — already the correct
  inversion reduct.

So the inversion is a `red`-redefinition (re-key the tag-4 critical branch of `iRNextG`/`iRNext` so the
R-redex premise substitutes the L-redex `k`), then `ZDerivation_red_zK_crit` follows from
`ZDerivation_iRcritG_of` with `haux0`/`haux1` discharged by the banked `zsubst` building blocks +
threading reconstruction. The 0→k change preserves the descent.

## Risk / what is NOT yet proven

- The `red`-redefinition ripples through `red`'s `𝚺₁`-definability (`iRNextDef`) and the `red_zK_crit`
  equation + the descent lemmas built on the current `ρ`. The descent is instance-invariant so it
  should transfer, but each `red_zK_*` rewrite must be re-checked.
- `haux0`/`haux1`'s **threading reconstruction** (`isChainInf` for `seqUpdate ds redexI (corrected
  reduct)` at the new conclusion succedent) is the genuine remaining inversion content — analogous to
  the `ZDerivation_iCritReplaceReduce_of` replace machinery, but at the redex position. Substantial but
  not deep (inherited from the original chain's `isChainInf` restricted to `≤ redexI`).
- The orbit freshness data (`hpfresh`/`hΓfresh`/`maxEigen < a`) must be threaded by the `redSound`
  motive — the same O1/O3 obligations the replace branch already isolates (lap-99/100).

## Next-lap target

Implement the corrected critical reduct (re-principalize at `k`) and prove `haux0`/`haux1`. The succedent
identity is banked; the threading + freshness are the work. THEN `ZDerivation_red_zK_crit` is real, which
unblocks `redSound` → the headline.
