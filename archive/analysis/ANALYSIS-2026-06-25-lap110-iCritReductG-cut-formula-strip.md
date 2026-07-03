# ANALYSIS lap-110 — `iCritReductG` cuts on the PRINCIPAL, not the STRIPPED, formula

## The finding (kernel-grounded, redirects the crux-2 critical-case endgame)

The genuine critical reduct `iRcritG d ρ = iCritReductG (fstIdx d) C (zKrank d - 1) (zKrank d) (zKrank d) …`
uses cut formula **`C = chainAsucc (zKseq d) (redexI d)`** — the succedent of the redex's R-premise, i.e. the
**PRINCIPAL** formula `A_i` of the `R_{A_i}`/`L^k_{A_i}` critical pair (confirmed: `redexPair_tp` gives
`tp(redexI) = isymR (chainAsucc ds (redexI))`, and `isymR`'s argument is the R-rule principal).

**Buchholz Thm 3.4(a)** (`scratchpad/buchholz-gentzen.txt:690,705,808`) cuts the reduct on the **STRIPPED**
subformula `A(d)`:
- line 690: "If `d = Kʳ_Π d₀…dₗ` is critical, then `d{0} ⊢ Π.A(d)`, `d{1} ⊢ A(d),Π`, and **`rk(A(d)) < r`**."
- line 705: "`rk(A(d)) = rk(F(k)) < rk(Aᵢ) ≤ r`" — so for `Aᵢ = ∀xF`, `A(d) = F(k)` (the L-instance),
  STRICTLY lower rank.
- line 808 (case 5.2.1 splice): reduct rank `r0 = max{rk(A(dᵢ)), r}` with `rk(A(dᵢ)) < dg(dᵢ)` (IH(b)).

So the repo's reduct uses `rk(C) = rk(Aᵢ) ≤ r` (principal, NOT strict), where Buchholz uses
`rk(A(d)) < r` (stripped, strict). `rk(Aᵢ) = rk(A(d)) + 1` for `Aᵢ ∈ {∀xF, ¬A}`.

## This is the SHARED root cause of TWO open `sorry`s

1. **`ZDerivation_red_zK_crit`** (`Crux2Blueprint.lean:100`, the critical-case SOUNDNESS). Discharged by
   `ZDerivation_iRcritG_of` (`InternalZ:8126`), whose `hCrk : irk C ≤ zKrank d - 1 = r - 1` demands
   `irk C < r`. With `C` the principal this is `rk(Aᵢ) < r` — FALSE in general (`rk(Aᵢ) ≤ r` only). With the
   STRIPPED `A(d)`, `rk(A(d)) < r` holds (`irk_cut_lt_rank_forall`/`_neg`, `InternalZ:409/415`).
2. **`iord_descent_red`'s splice `hr'`** (`Crux2Blueprint.lean:608`, lap-110). `hr' : max(irk C, r) ≤
   idg(parent)`; the hard half `irk C ≤ idg(parent)` needs `irk C < r'ᵢ` (then `≤ idg(dᵢ) - 1 ≤
   iseqMaxIdg ds - 1 ≤ idg(parent)`). Strict holds for the STRIPPED `A(d)` (Thm 3.4(a)), fails for the
   principal `C` in the edge case `rk(C) = r'ᵢ = idg(dᵢ) = iseqMaxIdg ds`.

**Why the DESCENT lemmas are immune** (`iord_descent_red_zK_crit`, `iCrit_halves_descend` stay green): `iotil`
and `idg` of a `zK` read only the PREMISE sequence (`iseqNaddIdg`/`iseqMaxIdg`), never the conclusion
succedent `C`. So changing `C` from principal to stripped does NOT touch any banked ordinal-descent fact —
only `ZDerivation`/`ZRegular` (which read end-sequents) and the splice rank `irk(seqSucc(fstIdx half0)) =
irk C`.

## The fix (next lap, the genuine cut-elimination content)

Redefine `iCritReductG`'s cut formula to the **stripped** `A(d)`:
- The strip is determined by the redex `L^k_{Aᵢ}` symbol: `Aᵢ = ∀xF ⟹ A(d) = F(k) = substs1 ℒₒᵣ k F`;
  `Aᵢ = ¬A ⟹ A(d) = A`. Define `cutFormula d` from `redexI`/`redexJ` (or reuse `tpReduce`/the §5 reduct
  data). Prove `irk (cutFormula d) < irk (chainAsucc ds (redexI d)) ≤ zKrank d` via `irk_cut_lt_rank_*`.
- The DEEP part: the two halves must DERIVE the stripped endsequents — `d{0} ⊢ Θ→A(d)`, `d{1} ⊢ A(d),Θ→D`.
  This is Buchholz Thm 3.4(a)'s **inversion** (∀-inversion `substs1`, ¬-inversion), the genuine
  cut-elimination — currently abstracted as `ZDerivation_iRcritG_of`'s `haux0`/`haux1` hypotheses. The
  META port `Zinfty.allInv`/`andInv`/`orInv` (`wip/PathCInf.lean`, lap-106) is the blueprint.

NB: `iCritReductG` is shared between the critical-case soundness AND the splice; fixing the cut formula
once unblocks both `hr'` and `ZDerivation_red_zK_crit`'s rank conjunct (the inversions remain for full
soundness). The splice `hr'` needs ONLY the stripped rank bound (no inversion), so it closes first.
