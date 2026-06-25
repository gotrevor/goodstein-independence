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

end GoodsteinPA.InternalZ
