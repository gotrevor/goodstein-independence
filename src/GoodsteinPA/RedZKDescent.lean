/-
# `RedZKDescent.lean` — the K-case ordinal descent for the GENUINE reduct `red` (critical branch)

`iord_descent_red`'s K/cut case (`Crux2Blueprint.lean`) needs `icmp (iord (red (zK s r ds))) (iord (zK s r
ds)) = 0`. `red` dispatches three Buchholz Def-3.2 case-5 branches via `iRK`; this file ports the CRITICAL
branch (5.1) from the banked `iord_descent_iR2_zK_of_valid` (which is stated for the `iR2`-ρ).

The ρ for `red`'s critical reduct is `fun n => zAxReduct (red (znth ds n))` (vs `iR2`'s `… (iR2 …)`). The two
agree on the redex premises' `iotil`/`idg`: on the j-side axiom leaves `red = iR2 = id`; on the i-side I¬
`red = iR2 = d0`; on the i-side I∀ `red = zsubst d0 a 0` (≠ `iR2 = d0`) but `iotil_zsubst`/`idg_zsubst` give
equal `iotil`/`idg` (the eigensubst preserves the ordinal — `iord_zsubst`). So the `iRedDescent` bundles
transfer; the genuine reduct `iRcritG` shares `iord` with `iRcrit` (`iord_iRcritG_eq_iRcrit`). Net: the
banked descent transfers verbatim, the I∀ case costing only the regularity `maxEigen d0 < a`.

Sorry-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). Not yet WIRED into `iord_descent_red`'s
K-case: that needs (a) the non-critical splice/replace branch descents, and (b) `zKValid` available from the
∅→⊥ orbit (the bare `ZDerivation` `zK` disjunct does not yet carry it — see `InternalZ.lean:7517`). Banked
green-gated until then. See `PENDING_WORK.md` lap-108.
-/
import GoodsteinPA.Zsubst

namespace GoodsteinPA.InternalZ

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalONote

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **j-side `red`-ρ bundle** (L-axiom redex premise): for a §5 atomic-axiom premise `d` (`tp d = L^k_A`),
the wrapped genuine reduct `zAxReduct (red d)` satisfies the `iRedDescent` bundle. `red` is the identity on
the axiom leaves (tags 5/6, `red_zAxAll`/`red_zAxNeg`), so this is literally the banked `iR2` bundle. -/
lemma iRedDescent_zAxReduct_red_of_tp_isymLk {d k A : V} (htp : tp d = isymLk k A)
    (hZ : ZDerivation d) : iRedDescent (zAxReduct (red d)) d := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k', rfl, hp, _⟩ | ⟨s, p, rfl, hp, _⟩
  · rw [tp_zAtom] at htp; exact absurd htp (by simp)
  · rw [tp_zIall] at htp; exact absurd htp (by simp)
  · rw [tp_zIneg] at htp; exact absurd htp (by simp)
  · rw [tp_zInd] at htp; exact absurd htp (by simp)
  · rw [tp_zK] at htp; exact absurd htp (by simp)
  · rw [red_zAxAll]; exact iRedDescent_zAxReduct_zAxAll hp
  · rw [red_zAxNeg]; exact iRedDescent_zAxReduct_zAxNeg hp

/-- **i-side `red`-ρ bundle** (R-redex premise): for an I-rule premise `d` (`tp d = R_A`), the wrapped
genuine reduct `zAxReduct (red d)` satisfies the `iRedDescent` bundle. For I¬, `red = d0 = iR2`. For I∀,
`red = zsubst d0 a 0`; the eigensubst preserves `iotil`/`idg` (`iotil_zsubst`/`idg_zsubst`), so the base
bundle transfers from `iRedDescent_zIall`, and `ZDerivation (zsubst d0 a 0)` (needed for the `zAxReduct`
wrap) holds by `ZDerivation_zsubst` given the I∀ regularity `maxEigen d0 < a` (from `ZRegular d`). -/
lemma iRedDescent_zAxReduct_red_of_tp_isymR {d A : V} (htp : tp d = isymR A)
    (hZ : ZDerivation d) (hreg : ZRegular d) : iRedDescent (zAxReduct (red d)) d := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, hd0, _⟩ | ⟨s, p, d0, rfl, hd0, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩
  · rw [tp_zAtom] at htp; exact absurd htp (by simp)
  · -- I∀: red = zsubst d0 a 0
    have ht0 : IsSemiterm ℒₒᵣ 0 (Bootstrapping.Arithmetic.numeral 0 : V) := by simp
    have hut0 : IsUTerm ℒₒᵣ (Bootstrapping.Arithmetic.numeral 0 : V) := ht0.isUTerm
    have hregd : maxEigen d0 < a := maxEigen_lt_of_regular_zIall hreg
    have hZred : ZDerivation (zsubst d0 a (Bootstrapping.Arithmetic.numeral 0)) :=
      ZDerivation_zsubst ht0 d0 hd0 hregd
    have hbase : iRedDescent (zsubst d0 a (Bootstrapping.Arithmetic.numeral 0)) (zIall s a p d0) := by
      have hb0 := iRedDescent_zIall (s := s) (a := a) (p := p) (isNF_iotil_of_ZDerivation d0 hd0)
      refine ⟨?_, ?_, ?_⟩
      · rw [idg_zsubst hut0 a d0 hd0]; exact hb0.dg_le
      · rw [iotil_zsubst hut0 a d0 hd0]; exact hb0.otil_lt
      · rw [iotil_zsubst hut0 a d0 hd0]; exact hb0.nf
    rw [red_zIall]; exact iRedDescent_zAxReduct_of_iRedDescent hZred hbase
  · -- I¬: red = d0 = iR2
    rw [red_zIneg]
    exact iRedDescent_zAxReduct_of_iRedDescent hd0 (iRedDescent_zIneg (isNF_iotil_of_ZDerivation d0 hd0))
  · rw [tp_zInd] at htp; exact absurd htp (by simp)
  · rw [tp_zK] at htp; exact absurd htp (by simp)
  · rw [tp_zAxAll] at htp; exact absurd htp (by simp)
  · rw [tp_zAxNeg] at htp; exact absurd htp (by simp)

/-- **THE critical-branch K-case descent for the GENUINE reduct `red`.** For a valid `K^r` chain whose
selected premise is critical (`¬ permIdx < lh ds`), `red (zK s r ds) = iRcritG …` and the ordinal strictly
descends: `icmp (iord (red (zK s r ds))) (iord (zK s r ds)) = 0`. Port of `iord_descent_iR2_zK_of_valid`
(`iR2`-ρ) to the `red`-ρ, via the i/j-side `red` bundles + `iord_iRcritG_eq_iRcrit` (the genuine reduct
shares `iord` with the ordinal-shadow `iRcrit`). The I∀ redex premise costs the regularity `hreg`. -/
lemma iord_descent_red_zK_crit {s r ds : V} (hcrit : ¬ permIdx (zK s r ds) < lh ds)
    (hds : Seq ds) (hmem : ∀ i < lh ds, ZDerivation (znth ds i))
    (hreg : ∀ i < lh ds, ZRegular (znth ds i)) (hvalid : zKValid s r ds) :
    icmp (iord (red (zK s r ds))) (iord (zK s r ds)) = 0 := by
  obtain ⟨hci, hperm0, hnperm0, hf1, hf2, hf5, hf6, _hsucc, _hssf, _hsaf⟩ := hvalid
  obtain ⟨j0, hj0, hAj0, hchain, hrank⟩ := hci
  have hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ False :=
    fun i hi A h => Or.inl (tp_isymR_pos h (hf1 i (lt_of_le_of_lt hi hj0))
      (hf2 i (lt_of_le_of_lt hi hj0)))
  have hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ (A = (^⊥ : V)) :=
    fun i hi k A h => Or.inl (tp_isymLk_pos h (hf5 i (lt_of_le_of_lt hi hj0))
      (hf6 i (lt_of_le_of_lt hi hj0)))
  have hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)) :=
    fun i hi => hperm0 i (lt_of_le_of_lt hi hj0)
  have hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s :=
    fun i hi => hnperm0 i (lt_of_le_of_lt hi hj0)
  have hnf : isNF (iotil (zK s r ds)) :=
    isNF_iotil_zK hds (fun i hi => isNF_iotil_of_ZDerivation _ (hmem i hi))
  have hNF : ∀ n, isNF (iotil (znth ds n)) := by
    intro n
    rcases lt_or_ge n (lh ds) with hn | hn
    · exact isNF_iotil_of_ZDerivation _ (hmem n hn)
    · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero
  obtain ⟨i0, j1, k0, hij, hjle, hRi, hLj, hrkpos, hrkr⟩ :=
    inference_critical_pair_of_chain (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
      hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm (fun _ h => h.1)
      (fun A h => by rw [h]; exact irk_falsum) rfl
  have hjlt : j1 < lh ds := lt_of_le_of_lt hjle hj0
  have hilt : i0 < lh ds := lt_trans hij hjlt
  have hredex : isRedexPair ds (⟪i0, j1⟫ : V) := by
    simp only [isRedexPair, pi₁_pair, pi₂_pair]
    refine ⟨hij, hjlt, ?_, ?_, ?_⟩
    · rw [hRi]; simp [isymR]
    · rw [hLj]; simp [isymLk]
    · rw [hRi, hLj]; simp [isymR, isymLk]
  have hex : ∃ c < (⟪lh (zKseq (zK s r ds)), lh (zKseq (zK s r ds))⟫ : V),
      isRedexPair (zKseq (zK s r ds)) c := by
    simp only [zKseq_zK]; exact ⟨⟪i0, j1⟫, pair_lt_pair hilt hjlt, hredex⟩
  have hrc : isRedexPair (zKseq (zK s r ds)) (redexCode (zK s r ds)) := redexCode_isRedexPair hex
  simp only [zKseq_zK] at hrc
  have hIlt : redexI (zK s r ds) < lh ds := lt_trans hrc.1 hrc.2.1
  have hJlt : redexJ (zK s r ds) < lh ds := hrc.2.1
  obtain ⟨hRedI, hRedJ⟩ := redexPair_tp hrc
  have hbI := iRedDescent_zAxReduct_red_of_tp_isymR hRedI (hmem _ hIlt) (hreg _ hIlt)
  have hbJ := iRedDescent_zAxReduct_red_of_tp_isymLk hRedJ (hmem _ hJlt)
  rw [red_zK_crit hcrit, iord_iRcritG_eq_iRcrit]
  exact iord_descent_iRcrit_of_chain' (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
    hds hnf hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm (fun _ h => h.1)
    (fun A h => by rw [h]; exact irk_falsum) rfl hNF
    hbI.otil_lt hbJ.otil_lt hbI.dg_le hbJ.dg_le hbI.nf hbJ.nf

/-- **Critical-reduct halves descend below the chain — the splice sub-fact (lap 110).** For a valid
critical `K^r` chain `dᵢ = zK s r ds` (`¬ permIdx < lh ds`), `red dᵢ = iRcritG dᵢ ρ` whose two
premise-halves `a,b = znth (zKseq (red dᵢ)) {0,1}` are `K`-chains over `seqUpdate ds (redexI/J) (red·)` —
i.e. `dᵢ`'s OWN premise sequence with the redex-`R`/`L` premise replaced by its strictly-descending genuine
reduct. So each half's `õ`/`idg`-fold lies (strictly/weakly) below `dᵢ`'s and is NF — **the `õ`-jump of the
critical 5.1 reduct is in the OUTER `K^{r-1}` rank-drop, NOT in the individual halves' premise folds.**
This extracts exactly the per-half `ha`/`hb`/`hag`/`hbg`/`hNFa`/`hNFb` that `iord_descent_red_zK_chain_splice`
consumes for the parent chain-splice (Buchholz Def-3.2 case 5.2.1); the rank bound `hr'` remains the
documented residual (the cut-rank `rk(A(dᵢ))` degree-drop bookkeeping). Mirrors the redex extraction of
`iord_descent_red_zK_crit`, then applies the `iCritAux` fold-monotonicity lemmas (`iotil_iCritAux_lt`,
`idg_iCritAux_le`) since `iotil`/`idg` ignore the half's reset conclusion/rank. -/
lemma iCrit_halves_descend {s r ds : V} (hcrit : ¬ permIdx (zK s r ds) < lh ds)
    (hds : Seq ds) (hmem : ∀ i < lh ds, ZDerivation (znth ds i))
    (hreg : ∀ i < lh ds, ZRegular (znth ds i)) (hvalid : zKValid s r ds)
    (hrankI : irk (chainAsucc ds (redexI (zK s r ds))) ≤ r) :
    icmp (iotil (znth (zKseq (red (zK s r ds))) 0)) (iotil (zK s r ds)) = 0 ∧
    icmp (iotil (znth (zKseq (red (zK s r ds))) 1)) (iotil (zK s r ds)) = 0 ∧
    idg (znth (zKseq (red (zK s r ds))) 0) ≤ idg (zK s r ds) ∧
    idg (znth (zKseq (red (zK s r ds))) 1) ≤ idg (zK s r ds) ∧
    isNF (iotil (znth (zKseq (red (zK s r ds))) 0)) ∧
    isNF (iotil (znth (zKseq (red (zK s r ds))) 1)) ∧
    irk (seqSucc (fstIdx (znth (zKseq (red (zK s r ds))) 0))) < r := by
  obtain ⟨hci, hperm0, hnperm0, hf1, hf2, hf5, hf6, _hsucc, _hssf, _hsaf⟩ := hvalid
  obtain ⟨j0, hj0, hAj0, hchain, hrank⟩ := hci
  have hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ False :=
    fun i hi A h => Or.inl (tp_isymR_pos h (hf1 i (lt_of_le_of_lt hi hj0))
      (hf2 i (lt_of_le_of_lt hi hj0)))
  have hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ (A = (^⊥ : V)) :=
    fun i hi k A h => Or.inl (tp_isymLk_pos h (hf5 i (lt_of_le_of_lt hi hj0))
      (hf6 i (lt_of_le_of_lt hi hj0)))
  have hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)) :=
    fun i hi => hperm0 i (lt_of_le_of_lt hi hj0)
  have hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s :=
    fun i hi => hnperm0 i (lt_of_le_of_lt hi hj0)
  have hNF : ∀ n, isNF (iotil (znth ds n)) := by
    intro n
    rcases lt_or_ge n (lh ds) with hn | hn
    · exact isNF_iotil_of_ZDerivation _ (hmem n hn)
    · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero
  obtain ⟨i0, j1, k0, hij, hjle, hRi, hLj, hrkpos, hrkr⟩ :=
    inference_critical_pair_of_chain (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
      hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm (fun _ h => h.1)
      (fun A h => by rw [h]; exact irk_falsum) rfl
  have hjlt : j1 < lh ds := lt_of_le_of_lt hjle hj0
  have hilt : i0 < lh ds := lt_trans hij hjlt
  have hredex : isRedexPair ds (⟪i0, j1⟫ : V) := by
    simp only [isRedexPair, pi₁_pair, pi₂_pair]
    refine ⟨hij, hjlt, ?_, ?_, ?_⟩
    · rw [hRi]; simp [isymR]
    · rw [hLj]; simp [isymLk]
    · rw [hRi, hLj]; simp [isymR, isymLk]
  have hex : ∃ c < (⟪lh (zKseq (zK s r ds)), lh (zKseq (zK s r ds))⟫ : V),
      isRedexPair (zKseq (zK s r ds)) c := by
    simp only [zKseq_zK]; exact ⟨⟪i0, j1⟫, pair_lt_pair hilt hjlt, hredex⟩
  have hrc : isRedexPair (zKseq (zK s r ds)) (redexCode (zK s r ds)) := redexCode_isRedexPair hex
  simp only [zKseq_zK] at hrc
  have hIlt : redexI (zK s r ds) < lh ds := lt_trans hrc.1 hrc.2.1
  have hJlt : redexJ (zK s r ds) < lh ds := hrc.2.1
  obtain ⟨hRedI, hRedJ⟩ := redexPair_tp hrc
  have hbI := iRedDescent_zAxReduct_red_of_tp_isymR hRedI (hmem _ hIlt) (hreg _ hIlt)
  have hbJ := iRedDescent_zAxReduct_red_of_tp_isymLk hRedJ (hmem _ hJlt)
  -- The two halves, computed from `red_zK_crit` + `iRcritG`/`iCritReductSeq` read-outs. `iotil`/`idg`
  -- ignore the reset conclusion/rank, so each half's fold equals the corresponding `iCritAux` fold.
  set vI : V := zAxReduct (red (znth ds (redexI (zK s r ds)))) with hvI
  set vJ : V := zAxReduct (red (znth ds (redexJ (zK s r ds)))) with hvJ
  have e0 : znth (zKseq (red (zK s r ds))) 0
      = zK (seqSetSucc s (cutFormula (zK s r ds))) r
          (seqUpdate ds (redexI (zK s r ds)) vI) := by
    rw [red_zK_crit hcrit, iRcritG]
    simp only [fstIdx_zK, zKseq_zK, zKrank_zK, zKseq_iCritReductG, znth_iCritReductSeq_zero, hvI]
  have e1 : znth (zKseq (red (zK s r ds))) 1
      = zK (seqAddAnt (cutFormula (zK s r ds)) s) r
          (seqUpdate ds (redexJ (zK s r ds)) vJ) := by
    rw [red_zK_crit hcrit, iRcritG]
    simp only [fstIdx_zK, zKseq_zK, zKrank_zK, zKseq_iCritReductG, znth_iCritReductSeq_one, hvJ]
  have hiotil0 : iotil (znth (zKseq (red (zK s r ds))) 0)
      = iotil (iCritAux (zK s r ds) (redexI (zK s r ds)) vI) := by
    rw [e0, iCritAux_zK, iotil_zK _ _ _ (seqUpdate_seq ds _ vI), iotil_zK _ _ _ (seqUpdate_seq ds _ vI)]
  have hiotil1 : iotil (znth (zKseq (red (zK s r ds))) 1)
      = iotil (iCritAux (zK s r ds) (redexJ (zK s r ds)) vJ) := by
    rw [e1, iCritAux_zK, iotil_zK _ _ _ (seqUpdate_seq ds _ vJ), iotil_zK _ _ _ (seqUpdate_seq ds _ vJ)]
  have hidg0 : idg (znth (zKseq (red (zK s r ds))) 0)
      = idg (iCritAux (zK s r ds) (redexI (zK s r ds)) vI) := by
    rw [e0, iCritAux_zK, idg_zK _ _ _ (seqUpdate_seq ds _ vI), idg_zK _ _ _ (seqUpdate_seq ds _ vI)]
  have hidg1 : idg (znth (zKseq (red (zK s r ds))) 1)
      = idg (iCritAux (zK s r ds) (redexJ (zK s r ds)) vJ) := by
    rw [e1, iCritAux_zK, idg_zK _ _ _ (seqUpdate_seq ds _ vJ), idg_zK _ _ _ (seqUpdate_seq ds _ vJ)]
  -- The redex R-principal `A_i = chainAsucc ds (redexI)` equals `π₂ (tp dᵢ)` by R-permissibility
  -- (global `hperm0` at `redexI < lh ds`), so the redexCode's `tp = R_{A_i}` is in `chainAsucc` form
  -- — exactly what `irk_cutFormula_lt` consumes. This is the rank-side conjunct (T3.4(a) strict drop).
  have hRedI' : tp (znth ds (redexI (zK s r ds)))
      = isymR (π₂ (tp (znth ds (redexI (zK s r ds))))) := hRedI
  have hChA : chainAsucc ds (redexI (zK s r ds)) = π₂ (tp (znth ds (redexI (zK s r ds)))) := by
    have hp := hperm0 _ hIlt
    rw [hRedI', iperm_isymR_iff] at hp
    exact hp.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hiotil0]; exact iotil_iCritAux_lt hds hIlt hbI.otil_lt hNF hbI.nf
  · rw [hiotil1]; exact iotil_iCritAux_lt hds hJlt hbJ.otil_lt hNF hbJ.nf
  · rw [hidg0]; exact idg_iCritAux_le hds hIlt hbI.dg_le
  · rw [hidg1]; exact idg_iCritAux_le hds hJlt hbJ.dg_le
  · rw [hiotil0, iCritAux_zK]
    exact isNF_iotil_zK (seqUpdate_seq ds _ vI) (fun n _ => by
      rcases eq_or_ne n (redexI (zK s r ds)) with rfl | hne
      · rw [znth_seqUpdate_self hIlt]; exact hbI.nf
      · rw [znth_seqUpdate_of_ne hne]; exact hNF n)
  · rw [hiotil1, iCritAux_zK]
    exact isNF_iotil_zK (seqUpdate_seq ds _ vJ) (fun n _ => by
      rcases eq_or_ne n (redexJ (zK s r ds)) with rfl | hne
      · rw [znth_seqUpdate_self hJlt]; exact hbJ.nf
      · rw [znth_seqUpdate_of_ne hne]; exact hNF n)
  · -- T3.4(a): `rk(A(d)) < r`. Read out the half-0 succedent as `cutFormula`, then strict drop.
    rw [e0, fstIdx_zK, seqSucc_seqSetSucc]
    refine irk_cutFormula_lt (d := zK s r ds) ?_ ?_ ?_
    · rw [zKseq_zK]; exact hmem _ hIlt
    · rw [zKseq_zK, hChA]; exact hRedI
    · rw [zKseq_zK]; exact hrankI

/-- **The non-critical REPLACE-branch K-case descent (Buchholz Def-3.2 case 5.2.2), conditional on the
selected premise's reduct descending.** Both replace dispatches (`red_zK_rep` chain-`dᵢ`-non-critical and
`red_zK_rep_nonchain` non-chain `dᵢ`) produce the SAME reduct shape `red (zK s r ds) = K^r(i/red dᵢ)` —
a `seqUpdate` of `ds` at `i = permIdx` swapping premise `dᵢ` for its reduct `red dᵢ`, same rank `r`. Given
the premise IH `iRedDescent (red dᵢ) dᵢ` (the recursive descent: `red dᵢ` doesn't raise the degree and
strictly lowers `õ`, judge §8.3 LH3/N2), the whole `K^r` ordinal strictly descends — `iotil` drops one
summand (`iotil_zK_lt_replace`, the F1 strict `#`-mono), `idg` doesn't rise (`idg_zK_le_replace`), then
`iord_descent_le` combines through the tower. Stated against the explicit reduct equation `hred` so a
single lemma covers both replace dispatches. -/
lemma iRedDescent_red_zK_replace_eq {s s' r ds i : V}
    (hds : Seq ds) (hmem : ∀ n < lh ds, ZDerivation (znth ds n)) (hi : i < lh ds)
    (hred : red (zK s r ds) = zK s' r (seqUpdate ds i (red (znth ds i))))
    (hIH : iRedDescent (red (znth ds i)) (znth ds i)) :
    iRedDescent (red (zK s r ds)) (zK s r ds) := by
  have hNF : ∀ n, isNF (iotil (znth ds n)) := fun n => by
    rcases lt_or_ge n (lh ds) with hn | hn
    · exact isNF_iotil_of_ZDerivation _ (hmem n hn)
    · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero
  have hNF' : ∀ n, isNF (iotil (znth (seqUpdate ds i (red (znth ds i))) n)) := fun n => by
    rcases eq_or_ne n i with rfl | hne
    · rw [znth_seqUpdate_self hi]; exact hIH.nf
    · rw [znth_seqUpdate_of_ne hne]; exact hNF n
  have hle : ∀ n, idg (znth (seqUpdate ds i (red (znth ds i))) n) ≤ idg (znth ds n) := fun n => by
    rcases eq_or_ne n i with rfl | hne
    · rw [znth_seqUpdate_self hi]; exact hIH.dg_le
    · rw [znth_seqUpdate_of_ne hne]
  have heq : ∀ n, n ≠ i →
      iotil (znth (seqUpdate ds i (red (znth ds i))) n) = iotil (znth ds n) :=
    fun n hne => by rw [znth_seqUpdate_of_ne hne]
  have hlt : icmp (iotil (znth (seqUpdate ds i (red (znth ds i))) i)) (iotil (znth ds i)) = 0 := by
    rw [znth_seqUpdate_self hi]; exact hIH.otil_lt
  rw [hred]
  exact ⟨idg_zK_le_replace hds (seqUpdate_seq ds i _) (seqUpdate_lh ds i _) hle,
    iotil_zK_lt_replace hds (seqUpdate_seq ds i _) (seqUpdate_lh ds i _) hi hlt heq hNF hNF',
    isNF_iotil_zK (seqUpdate_seq ds i _) (fun n _ => hNF' n)⟩

/-- **`iord`-descent corollary of the REPLACE bundle** (the form the current `iord_descent_red`
non-recursive dispatch consumes). -/
lemma iord_descent_red_zK_replace_eq {s s' r ds i : V}
    (hds : Seq ds) (hmem : ∀ n < lh ds, ZDerivation (znth ds n)) (hi : i < lh ds)
    (hred : red (zK s r ds) = zK s' r (seqUpdate ds i (red (znth ds i))))
    (hIH : iRedDescent (red (znth ds i)) (znth ds i)) :
    icmp (iord (red (zK s r ds))) (iord (zK s r ds)) = 0 :=
  iord_descent_of_iRedDescent (iRedDescent_red_zK_replace_eq hds hmem hi hred hIH)
    (isNF_iotil_zK hds (fun n hn => isNF_iotil_of_ZDerivation _ (hmem n hn)))

/-- **The non-critical SPLICE-branch K-case descent (Buchholz Def-3.2 case 5.2.1), conditional on the two
spliced halves descending below the selected premise.** When the selected premise `dᵢ = znth ds i`
(`i = permIdx`) is itself a CRITICAL chain (`zTag dᵢ = 4` ∧ `dᵢ` critical), `red (zK s r ds) =
K^{r'}(seqInsert ds i a b)` splices `dᵢ`'s two critical-reduct halves `a,b = znth (zKseq (red dᵢ)) {0,1}`
in place at `i`, with the genuine reduct rank `r' = max{rk(A(dᵢ)), r}` (judge §8.3 LH5). Given each half's
`õ`/`idg` bound below `dᵢ` (`ha`/`hb`/`hag`/`hbg`, from the critical reduction of `dᵢ`) and the faithful
rank bound `r' ≤ dg(parent)` (`hr'`), the `K^r` ordinal strictly descends via the F2 rotation kernel
(`iotil_seqInsert_lt`) + the rank-general `idg` bound (`idg_seqInsert_le'`) through `iord_descent_le`,
i.e. the banked `iord_descent_seqInsert'`. Stated against the explicit reduct equation `hred`. -/
lemma iord_descent_red_zK_splice_eq {s r ds i a b s' r' : V}
    (hds : Seq ds) (hmem : ∀ n < lh ds, ZDerivation (znth ds n)) (hi : i < lh ds)
    (hred : red (zK s r ds) = zK s' r' (seqInsert ds i a b))
    (hr' : r' ≤ idg (zK s r ds))
    (ha : icmp (iotil a) (iotil (znth ds i)) = 0) (hb : icmp (iotil b) (iotil (znth ds i)) = 0)
    (hag : idg a ≤ idg (znth ds i)) (hbg : idg b ≤ idg (znth ds i))
    (hNFa : isNF (iotil a)) (hNFb : isNF (iotil b)) :
    icmp (iord (red (zK s r ds))) (iord (zK s r ds)) = 0 := by
  have hNF : ∀ n, isNF (iotil (znth ds n)) := fun n => by
    rcases lt_or_ge n (lh ds) with hn | hn
    · exact isNF_iotil_of_ZDerivation _ (hmem n hn)
    · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero
  have hnf : isNF (iotil (zK s r ds)) := isNF_iotil_zK hds (fun n _ => hNF n)
  rw [hred]
  exact iord_descent_seqInsert' hds hi hnf hr' ha hb hag hbg hNF hNFa hNFb

/-- **I∀ genuine-reduct descent bundle.** `red (zIall s a p d0) = zsubst d0 a 0` satisfies `iRedDescent`
against `zIall s a p d0` — NO regularity needed for the ORDINAL bundle (only the eigensubst-invariance of
the assignment): `iotil_zsubst`/`idg_zsubst` carry the banked `iRedDescent_zIall` (stated for the `iR2`-ρ
`d0`) onto the genuine eigensubst reduct. The selected-I∀-premise case of the non-critical K-branch
(`iord_descent_red`) feeds this to `iord_descent_red_zK_replace_eq`. -/
lemma iRedDescent_red_zIall {s a p d0 : V} (hZ : ZDerivation (zIall s a p d0)) :
    iRedDescent (red (zIall s a p d0)) (zIall s a p d0) := by
  obtain ⟨hd0, _, _⟩ := zDerivation_zIall_inv hZ
  have hut0 : IsUTerm ℒₒᵣ (Bootstrapping.Arithmetic.numeral 0 : V) :=
    (by simp : IsSemiterm ℒₒᵣ 0 (Bootstrapping.Arithmetic.numeral 0 : V)).isUTerm
  have hb0 := iRedDescent_zIall (s := s) (a := a) (p := p) (isNF_iotil_of_ZDerivation d0 hd0)
  rw [red_zIall]
  exact ⟨by rw [idg_zsubst hut0 a d0 hd0]; exact hb0.dg_le,
    by rw [iotil_zsubst hut0 a d0 hd0]; exact hb0.otil_lt,
    by rw [iotil_zsubst hut0 a d0 hd0]; exact hb0.nf⟩

/-- **Chain sub-case, REPLACE dispatch (`dᵢ` a non-critical chain), reduced to the premise IH.** When the
selected premise `dᵢ = znth ds (permIdx)` is a chain (`zTag = 4`) that is itself non-critical
(`permIdx dᵢ < lh (zKseq dᵢ)`), `red (zK s r ds) = K^r(i/red dᵢ)` (`red_zK_rep`), so the descent is exactly
`iord_descent_red_zK_replace_eq` fed the recursive IH `iRedDescent (red dᵢ) dᵢ`. This is the precise interface
the strong-induction recursion supplies for the chain-replace branch. -/
lemma iord_descent_red_zK_chain_replace {s r ds : V}
    (hds : Seq ds) (hmem : ∀ n < lh ds, ZDerivation (znth ds n))
    (h1 : permIdx (zK s r ds) < lh ds)
    (h2 : permIdx (znth ds (permIdx (zK s r ds)))
        < lh (zKseq (znth ds (permIdx (zK s r ds)))))
    (hIH : iRedDescent (red (znth ds (permIdx (zK s r ds)))) (znth ds (permIdx (zK s r ds)))) :
    icmp (iord (red (zK s r ds))) (iord (zK s r ds)) = 0 :=
  iord_descent_red_zK_replace_eq hds hmem h1 (red_zK_rep h1 h2) hIH

/-- **Chain sub-case, SPLICE dispatch (`dᵢ` a critical chain), reduced to the two halves' descent.** When
the selected premise `dᵢ` is a critical chain (`zTag = 4`, `¬ permIdx dᵢ < lh (zKseq dᵢ)`),
`red (zK s r ds)` splices `dᵢ`'s critical-reduct halves (`red_zK_splice`); the descent is
`iord_descent_red_zK_splice_eq` fed the per-half `õ`/`idg` bounds + rank bound (from `dᵢ`'s critical
reduction). The genuine reduct rank is `max{rk(A(dᵢ)), r}`; here the halves `a,b` and the rank-bound `hr'`
are the recursion's outputs. -/
lemma iord_descent_red_zK_chain_splice {s r ds : V}
    (hds : Seq ds) (hmem : ∀ n < lh ds, ZDerivation (znth ds n))
    (h1 : permIdx (zK s r ds) < lh ds)
    (h2 : ¬ permIdx (znth ds (permIdx (zK s r ds)))
        < lh (zKseq (znth ds (permIdx (zK s r ds)))))
    (htag : zTag (znth ds (permIdx (zK s r ds))) = 4)
    (hr' : max (irk (seqSucc (fstIdx
        (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0)))) r ≤ idg (zK s r ds))
    (ha : icmp (iotil (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0))
        (iotil (znth ds (permIdx (zK s r ds)))) = 0)
    (hb : icmp (iotil (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 1))
        (iotil (znth ds (permIdx (zK s r ds)))) = 0)
    (hag : idg (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0)
        ≤ idg (znth ds (permIdx (zK s r ds))))
    (hbg : idg (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 1)
        ≤ idg (znth ds (permIdx (zK s r ds))))
    (hNFa : isNF (iotil (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 0)))
    (hNFb : isNF (iotil (znth (zKseq (red (znth ds (permIdx (zK s r ds))))) 1))) :
    icmp (iord (red (zK s r ds))) (iord (zK s r ds)) = 0 :=
  iord_descent_red_zK_splice_eq hds hmem h1 (red_zK_splice h1 h2 htag) hr' ha hb hag hbg hNFa hNFb

/-- **The atom-selection FIXPOINT defect, formalized (lap 109).** If the selected (least-permissible)
premise of a non-critical chain is a bare identity-atom `zAtom sᵢ` (`zTag = 0`, a `red`-normal form), the
genuine reduct is a **FIXPOINT**: `red (zK s r ds) = zK s r ds`. Because the non-chain replace dispatch
(`red_zK_rep_nonchain`) swaps premise `i` for `red dᵢ = dᵢ` (atoms are normal, `red_zAtom`) and reduces the
conclusion by `tpReduce (tp dᵢ) s 0 = tpReduce isymRep s 0 = s` (Rep-reduce is the identity,
`tpReduce_isymRep`), so `seqUpdate ds i dᵢ = ds` (`seqUpdate_znth_self`) leaves the whole node unchanged.

This pins the kernel obstruction to the descent recursion (PENDING_WORK lap-109): when `permIdx` selects an
atom, `iord (red (zK s r ds)) = iord (zK s r ds)` — NO strict descent, the orbit STALLS. The `isymRep` tag
conflates atoms (normal forms) with reducible Ind/chains, and `iperm isymRep` is unconditionally true
(`iperm_isymRep`), so an atom CAN be the first permissible premise. The fix is an `isPermPrem`/`permIdx`
engine refinement that excludes atom premises (so the selected premise is always reducible), OR an embedding
(`foundation_bot_to_Z_empty`) that produces atom-free chains. -/
lemma red_zK_fixpoint_of_atom_selected {s r ds sᵢ : V}
    (hds : Seq ds) (h1 : permIdx (zK s r ds) < lh ds)
    (hatom : znth ds (permIdx (zK s r ds)) = zAtom sᵢ) :
    red (zK s r ds) = zK s r ds := by
  have htag : zTag (znth ds (permIdx (zK s r ds))) ≠ 4 := by rw [hatom]; simp
  rw [red_zK_rep_nonchain h1 htag,
    show red (znth ds (permIdx (zK s r ds))) = znth ds (permIdx (zK s r ds)) from by
      rw [hatom, red_zAtom],
    seqUpdate_znth_self hds h1,
    show tp (znth ds (permIdx (zK s r ds))) = isymRep from by rw [hatom, tp_zAtom],
    tpReduce_isymRep]

end GoodsteinPA.InternalZ
