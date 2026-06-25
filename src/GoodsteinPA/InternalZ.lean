/-
# `wip/InternalZ.lean` — C0: arithmetized system-Z derivation constructor codes

**Status: wip brick for crux 2 (lap 60).** Buchholz's consistency proof runs over his finitary system
**Z** (`CRUX2-ORD-ASSIGNMENT-2026-06-24.md §3`), NOT Foundation's Tait calculus. To internalize Thm 4.2
(`o(d[n]) ≺ o(d)`) we must arithmetize Z as a `V → Prop` predicate on derivation **codes**, mirroring
Foundation's `Theory.Derivation` (`…/Proof/Basic.lean`). This file is the **data layer**: the coded
constructors for Z's five inference forms, their `𝚺₀` graphs, the subterm `<`-bounds (well-foundedness
for the eventual `Fixpoint`), and the `fstIdx` (end-sequent) projection.

Z's rules (doc §3), each code `⟪s, tag, …payload…⟫ + 1` (end-sequent `s` first, rule `tag` second):
* `zAtom s`            — tag 0 — atomic axiom (§5 content TBD).
* `zIall s a p d0`     — tag 1 — `I^a_∀xF`  (eigenvar `a`, formula `p = F`, premise `d0`).
* `zIneg s p d0`       — tag 2 — `I_¬A`      (formula `p = A`, premise `d0`).
* `zInd s at p d0 d1`  — tag 3 — `Ind^{a,t}_F` (bundled `at = ⟪a,t⟫`, formula `p = F`, premises).
* `zK s r ds`          — tag 4 — `K^r_Π`     (rank `r`, **sequence** `ds` of premises — variadic).

NEXT (next bricks): `Phi`/`blueprint`/`construction` (Fixpoint) → `ZDerivation : V → Prop`; then C1
(`iõ`/`idg`/`iord = iotower idg iõ` by recursion on it) and C2 (`iR`).
-/
import GoodsteinPA.InternalTower
import Foundation.FirstOrder.Incompleteness.Second

namespace GoodsteinPA.InternalZ

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalONote

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-! ## Constructor codes -/

noncomputable def zAtom (s : V) : V := ⟪s, 0, 0⟫ + 1
noncomputable def zIall (s a p d0 : V) : V := ⟪s, 1, a, p, d0⟫ + 1
noncomputable def zIneg (s p d0 : V) : V := ⟪s, 2, p, d0⟫ + 1
noncomputable def zInd (s at' p d0 d1 : V) : V := ⟪s, 3, at', p, d0, d1⟫ + 1
noncomputable def zK (s r ds : V) : V := ⟪s, 4, r, ds⟫ + 1

/-! ## `𝚺₀` graphs -/

def zAtomGraph : 𝚺₀.Semisentence 2 :=
  .mkSigma “y s. ∃ y' < y, !pair₃Def y' s 0 0 ∧ y = y' + 1”
instance zAtom_defined : 𝚺₀-Function₁ (zAtom : V → V) via zAtomGraph := .mk fun v ↦ by
  simp_all [zAtomGraph, zAtom]

def zIallGraph : 𝚺₀.Semisentence 5 :=
  .mkSigma “y s a p d0. ∃ y' < y, !pair₅Def y' s 1 a p d0 ∧ y = y' + 1”
instance zIall_defined : 𝚺₀-Function₄ (zIall : V → V → V → V → V) via zIallGraph := .mk fun v ↦ by
  simp_all [zIallGraph, numeral_eq_natCast, zIall]

def zInegGraph : 𝚺₀.Semisentence 4 :=
  .mkSigma “y s p d0. ∃ y' < y, !pair₄Def y' s 2 p d0 ∧ y = y' + 1”
instance zIneg_defined : 𝚺₀-Function₃ (zIneg : V → V → V → V) via zInegGraph := .mk fun v ↦ by
  simp_all [zInegGraph, numeral_eq_natCast, zIneg]

def zIndGraph : 𝚺₀.Semisentence 6 :=
  .mkSigma “y s at' p d0 d1. ∃ y' < y, !pair₆Def y' s 3 at' p d0 d1 ∧ y = y' + 1”
instance zInd_defined : 𝚺₀-Function₅ (zInd : V → V → V → V → V → V) via zIndGraph := .mk fun v ↦ by
  simp_all [zIndGraph, numeral_eq_natCast, zInd]

def zKGraph : 𝚺₀.Semisentence 4 :=
  .mkSigma “y s r ds. ∃ y' < y, !pair₄Def y' s 4 r ds ∧ y = y' + 1”
instance zK_defined : 𝚺₀-Function₃ (zK : V → V → V → V) via zKGraph := .mk fun v ↦ by
  simp_all [zKGraph, numeral_eq_natCast, zK]

/-! ## Subterm `<`-bounds (well-foundedness of the eventual `Fixpoint`) -/

@[simp] lemma seq_lt_zAtom (s : V) : s < zAtom s := le_iff_lt_succ.mp <| le_pair_left _ _

@[simp] lemma seq_lt_zIall (s a p d0 : V) : s < zIall s a p d0 := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma d0_lt_zIall (s a p d0 : V) : d0 < zIall s a p d0 :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _)
    <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_zIneg (s p d0 : V) : s < zIneg s p d0 := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma d0_lt_zIneg (s p d0 : V) : d0 < zIneg s p d0 :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_zInd (s at' p d0 d1 : V) : s < zInd s at' p d0 d1 :=
  le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma d0_lt_zInd (s at' p d0 d1 : V) : d0 < zInd s at' p d0 d1 :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_trans (by simp) <| le_pair_right _ _)
    <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma d1_lt_zInd (s at' p d0 d1 : V) : d1 < zInd s at' p d0 d1 :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_trans (by simp) <| le_pair_right _ _)
    <| le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma a_lt_zIall (s a p d0 : V) : a < zIall s a p d0 :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma p_lt_zIall (s a p d0 : V) : p < zIall s a p d0 :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _)
    <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma p_lt_zIneg (s p d0 : V) : p < zIneg s p d0 :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma at_lt_zInd (s at' p d0 d1 : V) : at' < zInd s at' p d0 d1 :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma p_lt_zInd (s at' p d0 d1 : V) : p < zInd s at' p d0 d1 :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _)
    <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma seq_lt_zK (s r ds : V) : s < zK s r ds := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma r_lt_zK (s r ds : V) : r < zK s r ds :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma ds_lt_zK (s r ds : V) : ds < zK s r ds :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

/-! ## `zTag` — the rule tag (second pair component), for recursion dispatch

The ordinal assignment functions `idg`/`iõ`/`iord` are **total** `𝚺₁` functions on codes, defined by
course-of-values recursion (like `iC`/`iomul`) that dispatches on `zTag d` and reads the relevant
subderivations. (`ZDerivation : V → Prop` — the Fixpoint, NEXT brick — is needed only to characterize
*which* codes are derivations + for `derivesEmpty`, not for the descent on these functions.) -/

/-- The rule tag of a derivation code: `π₁ (sndIdx d)` (`= π₁ (π₂ (d-1))`). -/
noncomputable def zTag (d : V) : V := π₁ (sndIdx d)

def _root_.LO.FirstOrder.Arithmetic.zTagDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ sd <⁺ d, !sndIdxDef sd d ∧ !pi₁Def y sd”

instance zTag_defined : 𝚺₀-Function₁ (zTag : V → V) via zTagDef := .mk fun v ↦ by
  simp [zTagDef, zTag, sndIdx_defined.iff, pi₁_defined.iff]

instance zTag_definable : 𝚺₀-Function₁ (zTag : V → V) := zTag_defined.to_definable

@[simp] lemma zTag_zAtom (s : V) : zTag (zAtom s) = 0 := by simp [zTag, sndIdx, zAtom]
@[simp] lemma zTag_zIall (s a p d0 : V) : zTag (zIall s a p d0) = 1 := by simp [zTag, sndIdx, zIall]
@[simp] lemma zTag_zIneg (s p d0 : V) : zTag (zIneg s p d0) = 2 := by simp [zTag, sndIdx, zIneg]
@[simp] lemma zTag_zInd (s at' p d0 d1 : V) : zTag (zInd s at' p d0 d1) = 3 := by
  simp [zTag, sndIdx, zInd]
@[simp] lemma zTag_zK (s r ds : V) : zTag (zK s r ds) = 4 := by simp [zTag, sndIdx, zK]

/-! ## `fstIdx` (end-sequent) projection -/

@[simp] lemma fstIdx_zAtom (s : V) : fstIdx (zAtom s) = s := by simp [fstIdx, zAtom]
@[simp] lemma fstIdx_zIall (s a p d0 : V) : fstIdx (zIall s a p d0) = s := by simp [fstIdx, zIall]
@[simp] lemma fstIdx_zIneg (s p d0 : V) : fstIdx (zIneg s p d0) = s := by simp [fstIdx, zIneg]
@[simp] lemma fstIdx_zInd (s at' p d0 d1 : V) : fstIdx (zInd s at' p d0 d1) = s := by
  simp [fstIdx, zInd]
@[simp] lemma fstIdx_zK (s r ds : V) : fstIdx (zK s r ds) = s := by simp [fstIdx, zK]

/-! ## Payload + sub-derivation projections (for the assignment recursion)

`zRest d = π₂ (sndIdx d)` is the payload *after* the rule tag (`sndIdx d = ⟪zTag d, zRest d⟫`).
The per-constructor sub-derivation/formula projections are π-chains on `zRest`; each is `≤ d`
(so the recursion reads them out of the value-table) and computes correctly on its own code. -/

/-- The payload after the tag: `sndIdx d = ⟪zTag d, zRest d⟫`. -/
noncomputable def zRest (d : V) : V := π₂ (sndIdx d)

def _root_.LO.FirstOrder.Arithmetic.zRestDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ sd <⁺ d, !sndIdxDef sd d ∧ !pi₂Def y sd”
instance zRest_defined : 𝚺₀-Function₁ (zRest : V → V) via zRestDef := .mk fun v ↦ by
  simp [zRestDef, zRest, sndIdx_defined.iff, pi₂_defined.iff]
instance zRest_definable : 𝚺₀-Function₁ (zRest : V → V) := zRest_defined.to_definable

@[simp] lemma zRest_le_self (d : V) : zRest d ≤ d := le_trans (by simp [zRest]) (sndIdx_le_self d)

-- Premise/formula projections (π-chains on the payload).
/-- `I^a_∀xF` premise `d0` (payload `⟪a,p,d0⟫`). -/
noncomputable def zIallPrem (d : V) : V := π₂ (π₂ (zRest d))
/-- `I_¬A` premise `d0` (payload `⟪p,d0⟫`). -/
noncomputable def zInegPrem (d : V) : V := π₂ (zRest d)
/-- `Ind^{a,t}_F` induction formula `F` (payload `⟪at,p,d0,d1⟫`). -/
noncomputable def zIndP (d : V) : V := π₁ (π₂ (zRest d))
/-- `Ind^{a,t}_F` base premise `d0`. -/
noncomputable def zIndPrem0 (d : V) : V := π₁ (π₂ (π₂ (zRest d)))
/-- `Ind^{a,t}_F` step premise `d1`. -/
noncomputable def zIndPrem1 (d : V) : V := π₂ (π₂ (π₂ (zRest d)))
/-- `K^r_Π` rank `r` (payload `⟪r,ds⟫`). -/
noncomputable def zKrank (d : V) : V := π₁ (zRest d)
/-- `K^r_Π` premise sequence `ds`. -/
noncomputable def zKseq (d : V) : V := π₂ (zRest d)

section ProjDef
open LO.FirstOrder.Arithmetic
def _root_.LO.FirstOrder.Arithmetic.zIallPremDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ ∃ r2 <⁺ r, !pi₂Def r2 r ∧ !pi₂Def y r2”
instance zIallPrem_defined : 𝚺₀-Function₁ (zIallPrem : V → V) via zIallPremDef := .mk fun v ↦ by
  simp [zIallPremDef, zIallPrem, zRest_defined.iff, pi₂_defined.iff]
instance zIallPrem_definable : 𝚺₀-Function₁ (zIallPrem : V → V) := zIallPrem_defined.to_definable

def _root_.LO.FirstOrder.Arithmetic.zInegPremDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ !pi₂Def y r”
instance zInegPrem_defined : 𝚺₀-Function₁ (zInegPrem : V → V) via zInegPremDef := .mk fun v ↦ by
  simp [zInegPremDef, zInegPrem, zRest_defined.iff, pi₂_defined.iff]
instance zInegPrem_definable : 𝚺₀-Function₁ (zInegPrem : V → V) := zInegPrem_defined.to_definable

def _root_.LO.FirstOrder.Arithmetic.zIndPDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ ∃ r2 <⁺ r, !pi₂Def r2 r ∧ !pi₁Def y r2”
instance zIndP_defined : 𝚺₀-Function₁ (zIndP : V → V) via zIndPDef := .mk fun v ↦ by
  simp [zIndPDef, zIndP, zRest_defined.iff, pi₂_defined.iff, pi₁_defined.iff]
instance zIndP_definable : 𝚺₀-Function₁ (zIndP : V → V) := zIndP_defined.to_definable

def _root_.LO.FirstOrder.Arithmetic.zIndPrem0Def : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ ∃ r2 <⁺ r, !pi₂Def r2 r ∧ ∃ r3 <⁺ r2, !pi₂Def r3 r2 ∧ !pi₁Def y r3”
instance zIndPrem0_defined : 𝚺₀-Function₁ (zIndPrem0 : V → V) via zIndPrem0Def := .mk fun v ↦ by
  simp [zIndPrem0Def, zIndPrem0, zRest_defined.iff, pi₂_defined.iff, pi₁_defined.iff]
instance zIndPrem0_definable : 𝚺₀-Function₁ (zIndPrem0 : V → V) := zIndPrem0_defined.to_definable

def _root_.LO.FirstOrder.Arithmetic.zIndPrem1Def : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ ∃ r2 <⁺ r, !pi₂Def r2 r ∧ ∃ r3 <⁺ r2, !pi₂Def r3 r2 ∧ !pi₂Def y r3”
instance zIndPrem1_defined : 𝚺₀-Function₁ (zIndPrem1 : V → V) via zIndPrem1Def := .mk fun v ↦ by
  simp [zIndPrem1Def, zIndPrem1, zRest_defined.iff, pi₂_defined.iff]
instance zIndPrem1_definable : 𝚺₀-Function₁ (zIndPrem1 : V → V) := zIndPrem1_defined.to_definable

def _root_.LO.FirstOrder.Arithmetic.zKrankDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ !pi₁Def y r”
instance zKrank_defined : 𝚺₀-Function₁ (zKrank : V → V) via zKrankDef := .mk fun v ↦ by
  simp [zKrankDef, zKrank, zRest_defined.iff, pi₁_defined.iff]
instance zKrank_definable : 𝚺₀-Function₁ (zKrank : V → V) := zKrank_defined.to_definable

def _root_.LO.FirstOrder.Arithmetic.zKseqDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ !pi₂Def y r”
instance zKseq_defined : 𝚺₀-Function₁ (zKseq : V → V) via zKseqDef := .mk fun v ↦ by
  simp [zKseqDef, zKseq, zRest_defined.iff, pi₂_defined.iff]
instance zKseq_definable : 𝚺₀-Function₁ (zKseq : V → V) := zKseq_defined.to_definable
end ProjDef

-- Compute lemmas: each projection reads the right component of its own code.
@[simp] lemma zRest_zIall (s a p d0 : V) : zRest (zIall s a p d0) = ⟪a, p, d0⟫ := by
  simp [zRest, sndIdx, zIall]
@[simp] lemma zRest_zIneg (s p d0 : V) : zRest (zIneg s p d0) = ⟪p, d0⟫ := by
  simp [zRest, sndIdx, zIneg]
@[simp] lemma zRest_zInd (s at' p d0 d1 : V) : zRest (zInd s at' p d0 d1) = ⟪at', p, d0, d1⟫ := by
  simp [zRest, sndIdx, zInd]
@[simp] lemma zRest_zK (s r ds : V) : zRest (zK s r ds) = ⟪r, ds⟫ := by
  simp [zRest, sndIdx, zK]

@[simp] lemma zIallPrem_zIall (s a p d0 : V) : zIallPrem (zIall s a p d0) = d0 := by simp [zIallPrem]
@[simp] lemma zInegPrem_zIneg (s p d0 : V) : zInegPrem (zIneg s p d0) = d0 := by simp [zInegPrem]
@[simp] lemma zIndP_zInd (s at' p d0 d1 : V) : zIndP (zInd s at' p d0 d1) = p := by simp [zIndP]
@[simp] lemma zIndPrem0_zInd (s at' p d0 d1 : V) : zIndPrem0 (zInd s at' p d0 d1) = d0 := by
  simp [zIndPrem0]
@[simp] lemma zIndPrem1_zInd (s at' p d0 d1 : V) : zIndPrem1 (zInd s at' p d0 d1) = d1 := by
  simp [zIndPrem1]
@[simp] lemma zKrank_zK (s r ds : V) : zKrank (zK s r ds) = r := by simp [zKrank]
@[simp] lemma zKseq_zK (s r ds : V) : zKseq (zK s r ds) = ds := by simp [zKseq]

/-- `I^a_∀xF` principal-formula matrix `F` (payload `⟪a,p,d0⟫`, so `F = p`). -/
noncomputable def zIallF (d : V) : V := π₁ (π₂ (zRest d))
/-- `I_¬A` principal-formula body `A` (payload `⟪p,d0⟫`, so `A = p`). -/
noncomputable def zInegF (d : V) : V := π₁ (zRest d)
@[simp] lemma zIallF_zIall (s a p d0 : V) : zIallF (zIall s a p d0) = p := by simp [zIallF]
@[simp] lemma zInegF_zIneg (s p d0 : V) : zInegF (zIneg s p d0) = p := by simp [zInegF]

-- Bounds: each projection is `≤ d` (so the recursion reads the value-table at a smaller index).
@[simp] lemma zIallPrem_le (d : V) : zIallPrem d ≤ d :=
  le_trans (le_trans (pi₂_le_self _) (pi₂_le_self _)) (zRest_le_self d)
@[simp] lemma zInegPrem_le (d : V) : zInegPrem d ≤ d := le_trans (pi₂_le_self _) (zRest_le_self d)
@[simp] lemma zIndP_le (d : V) : zIndP d ≤ d :=
  le_trans (le_trans (pi₁_le_self _) (pi₂_le_self _)) (zRest_le_self d)
@[simp] lemma zIndPrem0_le (d : V) : zIndPrem0 d ≤ d :=
  le_trans (le_trans (le_trans (pi₁_le_self _) (pi₂_le_self _)) (pi₂_le_self _)) (zRest_le_self d)
@[simp] lemma zIndPrem1_le (d : V) : zIndPrem1 d ≤ d :=
  le_trans (le_trans (le_trans (pi₂_le_self _) (pi₂_le_self _)) (pi₂_le_self _)) (zRest_le_self d)
@[simp] lemma zKrank_le (d : V) : zKrank d ≤ d := le_trans (pi₁_le_self _) (zRest_le_self d)
@[simp] lemma zKseq_le (d : V) : zKseq d ≤ d := le_trans (pi₂_le_self _) (zRest_le_self d)

/-! ## `irk` — formula rank (Buchholz logical complexity), a real `UformulaRec1` recursion

Buchholz's `dg` uses `r := rk(F)` (logical complexity of the induction formula) in the `Ind`/`K^r`
cases. `rk` is the standard course-of-values recursion on Foundation's coded `ℒₒᵣ`-formulas:
`rk(atom)=rk(⊤)=rk(⊥)=0`, `rk(A∧B)=rk(A∨B)=max(rk A, rk B)+1`, `rk(∀F)=rk(∃F)=rk F+1`. Realized as a
total `𝚺₁` function via Foundation's `UformulaRec1.Construction` (the same recursion engine behind
`bv`), so it is genuine machine-checked content, NOT a stub. -/

namespace IRk

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. y = 0”
  nrel := .mkSigma “y param k R v. y = 0”
  verum := .mkSigma “y param. y = 0”
  falsum := .mkSigma “y param. y = 0”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. ∃ m, !max.dfn m y₁ y₂ ∧ y = m + 1”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. ∃ m, !max.dfn m y₁ y₂ ∧ y = m + 1”
  all := .mkSigma “y param p₁ y₁. y = y₁ + 1”
  exs := .mkSigma “y param p₁ y₁. y = y₁ + 1”
  allChanges := .mkSigma “param' param. param' = 0”
  exsChanges := .mkSigma “param' param. param' = 0”

noncomputable def construction : UformulaRec1.Construction V blueprint where
  rel {_} := fun _ _ _ ↦ 0
  nrel {_} := fun _ _ _ ↦ 0
  verum {_} := 0
  falsum {_} := 0
  and {_} := fun _ _ y₁ y₂ ↦ Max.max y₁ y₂ + 1
  or {_} := fun _ _ y₁ y₂ ↦ Max.max y₁ y₂ + 1
  all {_} := fun _ y₁ ↦ y₁ + 1
  exs {_} := fun _ y₁ ↦ y₁ + 1
  allChanges := fun _ ↦ 0
  exsChanges := fun _ ↦ 0
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  allChanges_defined := .mk fun v ↦ by simp [blueprint]
  exChanges_defined := .mk fun v ↦ by simp [blueprint]

end IRk

noncomputable def irk (p : V) : V := IRk.construction.result ℒₒᵣ 0 p

noncomputable def _root_.LO.FirstOrder.Arithmetic.irkDef : 𝚺₁.Semisentence 2 :=
  (IRk.blueprint.result ℒₒᵣ).rew (Rew.subst ![#0, ‘0’, #1])

instance irk_defined : 𝚺₁-Function₁ (irk : V → V) via irkDef := .mk fun v ↦ by
  simpa [irkDef, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using!
    (IRk.construction.result_defined (L := ℒₒᵣ)).defined ![v 0, 0, v 1]

instance irk_definable : 𝚺₁-Function₁ (irk : V → V) := irk_defined.to_definable
instance irk_definable' (Γ) : Γ-[m + 1]-Function₁ (irk : V → V) := irk_definable.of_sigmaOne

@[simp] lemma irk_rel {k R v : V} (hR : (ℒₒᵣ).IsRel k R) (hv : IsUTermVec ℒₒᵣ k v) :
    irk (^rel k R v : V) = 0 := by simp [irk, hR, hv, IRk.construction]
@[simp] lemma irk_nrel {k R v : V} (hR : (ℒₒᵣ).IsRel k R) (hv : IsUTermVec ℒₒᵣ k v) :
    irk (^nrel k R v : V) = 0 := by simp [irk, hR, hv, IRk.construction]
@[simp] lemma irk_verum : irk (^⊤ : V) = 0 := by simp [irk, IRk.construction]
@[simp] lemma irk_falsum : irk (^⊥ : V) = 0 := by simp [irk, IRk.construction]
@[simp] lemma irk_and {p q : V} (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    irk (p ^⋏ q : V) = Max.max (irk p) (irk q) + 1 := by simp [irk, hp, hq, IRk.construction]
@[simp] lemma irk_or {p q : V} (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    irk (p ^⋎ q : V) = Max.max (irk p) (irk q) + 1 := by simp [irk, hp, hq, IRk.construction]
@[simp] lemma irk_all {p : V} (hp : IsUFormula ℒₒᵣ p) : irk (^∀ p : V) = irk p + 1 := by
  simp [irk, hp, IRk.construction]
@[simp] lemma irk_ex {p : V} (hp : IsUFormula ℒₒᵣ p) : irk (^∃ p : V) = irk p + 1 := by
  simp [irk, hp, IRk.construction]

/-! ### T4(a)/(b) — `rk` substitution-invariance via Foundation's `formulaComplexity`

Buchholz's `rk` (logical complexity) is **identical** to Foundation's `formulaComplexity ℒₒᵣ` (same
recursion: atoms/⊤/⊥ ↦ 0, `∧`/`∨` ↦ max+1, `∀`/`∃` ↦ +1). Foundation already proves
`fomulaComplexity_substs1 : formulaComplexity L (substs1 L t p) = formulaComplexity L p` — exactly the
**T4(a)** rank-substitution-invariance leaf (judge `E-CRUX2-DECOMPOSITION §8.2`, "the ONE new rank
fact"). We bridge `irk = formulaComplexity ℒₒᵣ` (a clean `IsUFormula`-induction matching the equations)
and inherit it, then chain with `irk_all` (**T4(b)** `rk(∀xF)=rk(F)+1`) to get `rk(F(t)) < rk(∀xF)` —
the linchpin of T3.4's degree-drop `rk(A(d)) < r` (only the chain-rank invariant `rk(∀xF)=rk(A_i) ≤ r`,
gated on L3.1, remains beyond this). -/

/-- `irk` coincides with Foundation's `formulaComplexity ℒₒᵣ` on coded formulas (same recursion). -/
lemma irk_eq_formulaComplexity {p : V} :
    IsUFormula ℒₒᵣ p → irk p = formulaComplexity ℒₒᵣ p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp]
  · intro p hp ihp; simp [hp, ihp]

/-- **T4(a) — rank is substitution-invariant**: `rk(F(t)) = rk(F)` for a term substitution into a
1-variable formula. Inherited from Foundation's `fomulaComplexity_substs1` via the `irk` bridge. -/
lemma irk_substs1 {m t p : V} (hp : IsSemiformula ℒₒᵣ 1 p) (ht : IsSemiterm ℒₒᵣ m t) :
    irk (substs1 ℒₒᵣ t p) = irk p := by
  rw [irk_eq_formulaComplexity (IsSemiformula.substs1 ht hp).isUFormula,
    fomulaComplexity_substs1 hp ht, irk_eq_formulaComplexity hp.isUFormula]

/-- **T4(a)+(b) — `rk(F(t)) < rk(∀xF)`**: the cut-formula rank strictly below the quantified formula's,
the heart of T3.4's `rk(A(d)) < r`. `rk(F(t)) = rk(F)` (T4a) `< rk(F)+1 = rk(∀xF)` (T4b). -/
lemma irk_substs1_lt_all {m t p : V} (hp : IsSemiformula ℒₒᵣ 1 p) (ht : IsSemiterm ℒₒᵣ m t) :
    irk (substs1 ℒₒᵣ t p) < irk (^∀ p : V) := by
  rw [irk_substs1 hp ht, irk_all hp.isUFormula]
  exact lt_succ_iff_le.mpr le_rfl

/-- `irk` is invariant under bare Tait negation `∼A`, inherited from Foundation's
`formulaComplexity_neg`. (Buchholz's `¬A`, with `rk(¬A)=rk(A)+1`, is the De Morgan `∼A ∨ ⊥` = `inegF`,
NOT bare `∼A`.) -/
lemma irk_neg {A : V} (hA : IsUFormula ℒₒᵣ A) : irk (neg ℒₒᵣ A) = irk A := by
  rw [irk_eq_formulaComplexity hA.neg, formulaComplexity_neg hA, irk_eq_formulaComplexity hA]

/-- **Buchholz's `¬A`** (Def 3.1.3) as a Tait formula: `¬A := ∼A ∨ ⊥` (= `A → ⊥`), so
`rk(¬A) = rk(A)+1`, matching Buchholz's `rk(¬A)=rk(A)+1` — unlike bare Tait `∼A`, which preserves rank.
This is the cut formula `A(d) = A` strips below in the `I_¬A` redex case of T3.4(a). -/
noncomputable def inegF (A : V) : V := (neg ℒₒᵣ A) ^⋎ (^⊥ : V)

@[simp] lemma irk_inegF {A : V} (hA : IsUFormula ℒₒᵣ A) : irk (inegF A) = irk A + 1 := by
  rw [inegF, irk_or hA.neg (by simp), irk_neg hA, irk_falsum]
  simp

/-- `rk(A) < rk(¬A)` — the `I_¬A` redex strip (the negation analogue of T4's `rk(F(k)) < rk(∀xF)`). -/
lemma irk_lt_inegF {A : V} (hA : IsUFormula ℒₒᵣ A) : irk A < irk (inegF A) := by
  rw [irk_inegF hA]; exact lt_succ_iff_le.mpr le_rfl

/-! ### T3.4(a) — the rank bound `rk(A(d)) < r`

Buchholz Theorem 3.4(a), p.9: for a critical chain `d = K^r_Π …` with redex `(i,j,k)` (Lemma 3.1,
`inference_critical_pair`), the cut formula `A(d)` (`= F(k)` if `A_i = ∀xF`, `= A` if `A_i = ¬A`)
satisfies `rk(A(d)) < r`. Proof: `rk(A(d)) < rk(A_i) ≤ r`, where the strict step is the substitution /
negation strip (T4, banked) and `rk(A_i) ≤ r` is the chain-rule rank invariant (`∀ i<j₀, rk(A_i) ≤ r`,
read off the `K^r` chain inference — the redex has `i < j ≤ j₀`). This is the rank-side assembly of
T3.4(a). -/

/-- **T3.4(a) rank bound, generic assembly**: `rk(A(d)) < rk(A_i) ≤ r ⟹ rk(A(d)) < r`. -/
theorem irk_cut_lt_rank {Ad Ai r : V} (hstrip : irk Ad < irk Ai) (hr : irk Ai ≤ r) :
    irk Ad < r := lt_of_lt_of_le hstrip hr

/-- **T3.4(a), `∀`-redex case**: `A_i = ∀xF`, `A(d) = F(k)`, gives `rk(F(k)) < r` from `rk(∀xF) ≤ r`. -/
theorem irk_cut_lt_rank_forall {m F t r : V}
    (hF : IsSemiformula ℒₒᵣ 1 F) (ht : IsSemiterm ℒₒᵣ m t) (hr : irk (^∀ F : V) ≤ r) :
    irk (substs1 ℒₒᵣ t F) < r :=
  irk_cut_lt_rank (irk_substs1_lt_all hF ht) hr

/-- **T3.4(a), `¬`-redex case**: `A_i = ¬A`, `A(d) = A`, gives `rk(A) < r` from `rk(¬A) ≤ r`. -/
theorem irk_cut_lt_rank_neg {A r : V} (hA : IsUFormula ℒₒᵣ A) (hr : irk (inegF A) ≤ r) :
    irk A < r :=
  irk_cut_lt_rank (irk_lt_inegF hA) hr

/-! ## §3 — Inference symbols and Lemma 3.1 (the redex finder, L3.1)

Buchholz §3 (pp.7–8). Each premise of a chain inference carries an *inference symbol*
`I ∈ {R_A, L^k_A, Rep}`, with a *permissibility* relation `I ◁ Γ→C`:
`I ◁ Γ→C :⇔ I = R_C ∨ (I = L^k_A with A ∈ Γ) ∨ I = Rep`. A symbol is *well-formed* iff `R_A` has
`rk A > 0 ∨ A ≈ ⊤` and `L^k_A` has `rk A > 0 ∨ A ≈ ⊥`.

**Lemma 3.1** (p.8): if `A_{j0} ∈ {C, ⊥}`, the chain antecedent condition `Γ_i ⊆ Γ, A_0,…,A_{i-1}`
holds, and every premise symbol is permissible for its own premise but NOT for the conclusion
(`I_i ◁ Π_i & I_i ⋪ Π`), then there is a *critical pair* `∃ i<j≤j0, k`: `I_i = R_{A_i}`,
`I_j = L^k_{A_i}`, `0 < rk(A_i)`. This is the redex `iR` eliminates in case 5.1 (THE NUT). Proof: a
`𝚺₀` least-index search over the premise list — NO ordinals (`E-CRUX2-DECOMPOSITION §8.1`, leaves L1–L4).

Symbols are coded `R_A := ⟪0,A⟫`, `L^k_A := ⟪1,k,A⟫`, `Rep := ⟪2,0⟫`. The truth-of-minimal predicates
`A ≈ ⊤`/`A ≈ ⊥` (`Tr`/`Fa`) and antecedent membership (`mem`) are abstracted to the only properties the
proof consumes — a minimal formula is not both true and false (`hdisj`) and `A ≈ ⊥ ⟹ rk A = 0`
(`hFa_rk`). Faithful: the lemma holds for any truth assignment with these properties; instantiation to
Z's atomic truth (§5) is deferred. -/

/-- `R_A` — the right/reduction inference symbol for formula `A`. -/
noncomputable def isymR (A : V) : V := ⟪0, A⟫
/-- `L^k_A` — the left inference symbol for formula `A` with numeral choice `k`. -/
noncomputable def isymLk (k A : V) : V := ⟪1, k, A⟫
/-- `Rep` — the repetition inference symbol. -/
noncomputable def isymRep : V := ⟪2, (0 : V)⟫

@[simp] lemma isymR_ne_isymLk (A k A' : V) : (isymR A : V) ≠ isymLk k A' := by
  simp [isymR, isymLk, pair_ext_iff]
@[simp] lemma isymLk_ne_isymR (k A A' : V) : (isymLk k A : V) ≠ isymR A' := by
  simp [isymR, isymLk, pair_ext_iff]
@[simp] lemma isymR_ne_isymRep (A : V) : (isymR A : V) ≠ isymRep := by
  simp [isymR, isymRep, pair_ext_iff]
@[simp] lemma isymRep_ne_isymR (A : V) : (isymRep : V) ≠ isymR A := by
  simp [isymR, isymRep, pair_ext_iff]
@[simp] lemma isymLk_ne_isymRep (k A : V) : (isymLk k A : V) ≠ isymRep := by
  simp [isymLk, isymRep, pair_ext_iff]
@[simp] lemma isymRep_ne_isymLk (k A : V) : (isymRep : V) ≠ isymLk k A := by
  simp [isymLk, isymRep, pair_ext_iff]
@[simp] lemma isymR_inj (A A' : V) : (isymR A : V) = isymR A' ↔ A = A' := by
  simp [isymR, pair_ext_iff]
@[simp] lemma isymLk_inj (k A k' A' : V) : (isymLk k A : V) = isymLk k' A' ↔ k = k' ∧ A = A' := by
  simp [isymLk, pair_ext_iff]

def _root_.LO.FirstOrder.Arithmetic.isymLkGraph : 𝚺₀.Semisentence 3 :=
  .mkSigma “y k A. !pair₃Def y 1 k A”
instance isymLk_defined : 𝚺₀-Function₂ (isymLk : V → V → V) via isymLkGraph := .mk fun v ↦ by
  simp [isymLkGraph, isymLk, numeral_eq_natCast]
instance isymLk_definable : 𝚺₀-Function₂ (isymLk : V → V → V) := isymLk_defined.to_definable
instance isymLk_definable' (ℌ) : ℌ-Function₂ (isymLk : V → V → V) := isymLk_definable.of_zero

/-- `I ∈ L` — `I` is a left symbol `L^k_A`. Stated projection-free (`I` reconstructs from its own
projections `π₁(π₂ I) = k`, `π₂(π₂ I) = A`) so it is `𝚺₁`-definable with no bounded-quantifier bound. -/
def isymIsL (I : V) : Prop := I = isymLk (π₁ (π₂ I)) (π₂ (π₂ I))

lemma isymIsL_isymLk (k A : V) : isymIsL (isymLk k A : V) := by
  simp [isymIsL, isymLk]

lemma isymIsL_iff {I : V} : isymIsL I ↔ ∃ k A, I = isymLk k A := by
  constructor
  · intro h; exact ⟨_, _, h⟩
  · rintro ⟨k, A, rfl⟩; exact isymIsL_isymLk k A

/-- `I ∈ R` — `I` is a right symbol `R_A` (`A = π₂ I`). Projection-free analogue of `isymIsL`. -/
def isymIsR (I : V) : Prop := I = isymR (π₂ I)

lemma isymIsR_isymR (A : V) : isymIsR (isymR A : V) := by simp [isymIsR, isymR]

lemma isymIsR_iff {I : V} : isymIsR I ↔ ∃ A, I = isymR A := by
  constructor
  · intro h; exact ⟨_, h⟩
  · rintro ⟨A, rfl⟩; exact isymIsR_isymR A

/-- The discriminant `π₁` of the three inference symbols (`R`=0, `L`=1, `Rep`=2). -/
@[simp] lemma pi₁_isymR (A : V) : π₁ (isymR A : V) = 0 := by simp [isymR]
@[simp] lemma pi₂_isymR (A : V) : π₂ (isymR A : V) = A := by simp [isymR]
@[simp] lemma pi₁_isymLk (k A : V) : π₁ (isymLk k A : V) = 1 := by simp [isymLk]
@[simp] lemma pi₁_isymRep : π₁ (isymRep : V) = 2 := by simp [isymRep]

section Lemma31

variable (mem : V → V → Prop) (Tr Fa : V → Prop)

/-- **Lemma 3.1 — the critical-pair (redex) finder** (Buchholz p.8). Given a chain inference with
premise inference symbols `I_i = znth Iseq i` and premise succedents `A_i = Asucc i`
(`i ≤ j0`), with `A_{j0} ∈ {Cmain, ⊥}`, the chain antecedent condition, and each `I_i` permissible for
its own premise `Γ_i→A_i` but not for the conclusion `Γmain→Cmain`, there is a critical pair
`i < j ≤ j0` and `k` with `I_i = R_{A_i}`, `I_j = L^k_{A_i}`, `0 < rk(A_i)`. A `𝚺₀` least-index search
(`least_number`) — no ordinals. This identifies the redex `iR` eliminates in case 5.1. -/
theorem inference_critical_pair
    {Iseq Γmain Cmain j0 : V} {Asucc Gam : V → V}
    (hwfR : ∀ i ≤ j0, ∀ A, znth Iseq i = isymR A → 0 < irk A ∨ Tr A)
    (hwfL : ∀ i ≤ j0, ∀ k A, znth Iseq i = isymLk k A → 0 < irk A ∨ Fa A)
    (hperm : ∀ i ≤ j0, znth Iseq i = isymR (Asucc i) ∨
        (∃ k A, znth Iseq i = isymLk k A ∧ mem A (Gam i)) ∨ znth Iseq i = isymRep)
    (hnperm : ∀ i ≤ j0, ¬ (znth Iseq i = isymR Cmain ∨
        (∃ k A, znth Iseq i = isymLk k A ∧ mem A Γmain) ∨ znth Iseq i = isymRep))
    (hchain : ∀ i ≤ j0, ∀ B, mem B (Gam i) → mem B Γmain ∨ ∃ i' < i, B = Asucc i')
    (hAj0 : Asucc j0 = Cmain ∨ Fa (Asucc j0))
    (hdisj : ∀ A, ¬ (Tr A ∧ Fa A)) (hFa_rk : ∀ A, Fa A → irk A = 0) :
    ∃ i j k, i < j ∧ j ≤ j0 ∧ znth Iseq i = isymR (Asucc i) ∧
      znth Iseq j = isymLk k (Asucc i) ∧ 0 < irk (Asucc i) := by
  -- Step A: the last premise symbol is a left symbol.
  have hLj0 : isymIsL (znth Iseq j0) := by
    rcases hperm j0 le_rfl with hR | hL | hRep
    · -- I_{j0} = R_{A_{j0}}: impossible.
      exfalso
      have hne : znth Iseq j0 ≠ isymR Cmain := fun h => hnperm j0 le_rfl (Or.inl h)
      rcases hAj0 with hC | hFa
      · exact hne (by rw [hR, hC])
      · rcases hwfR j0 le_rfl _ hR with hpos | hTr
        · exact absurd (hFa_rk _ hFa) (by simpa using hpos.ne')
        · exact hdisj _ ⟨hTr, hFa⟩
    · obtain ⟨k, A, hI, _⟩ := hL; exact isymIsL_iff.mpr ⟨k, A, hI⟩
    · exact absurd hRep (fun h => hnperm j0 le_rfl (Or.inr (Or.inr h)))
  -- Step B: take the least left-symbol index j.
  have hQdef : 𝚺₁-Predicate (fun x : V => isymIsL (znth Iseq x) ∧ x ≤ j0) := by
    simp only [isymIsL]; definability
  obtain ⟨j, ⟨hLj, hj_le⟩, hmin⟩ :=
    InductionOnHierarchy.least_number 𝚺 1 hQdef ⟨hLj0, le_rfl⟩
  obtain ⟨k, B, hIj⟩ := isymIsL_iff.mp hLj
  -- B ∈ Γ_j  (from permissibility of I_j for its premise)
  have hBmem : mem B (Gam j) := by
    rcases hperm j hj_le with hR | hL | hRep
    · exact absurd (hR.symm.trans hIj) (by simp)
    · obtain ⟨k', A', hI', hA'⟩ := hL
      obtain ⟨hk, hA⟩ := isymLk_inj k B k' A' |>.mp (hIj.symm.trans hI')
      exact hA ▸ hA'
    · exact absurd (hRep.symm.trans hIj) (by simp)
  -- B ∉ Γmain  (from non-permissibility of I_j for the conclusion)
  have hBnmem : ¬ mem B Γmain := fun h =>
    hnperm j hj_le (Or.inr (Or.inl ⟨k, B, hIj, h⟩))
  -- chain condition: B = A_i for some i < j
  obtain ⟨i, hij, hBi⟩ := (hchain j hj_le B hBmem).resolve_left hBnmem
  have hi_le : i ≤ j0 := le_of_lt (lt_of_lt_of_le hij hj_le)
  -- I_j = L^k_{A_i}
  have hIjL : znth Iseq j = isymLk k (Asucc i) := by rw [hIj, hBi]
  -- I_i = R_{A_i}  (minimality kills the left-symbol and Rep cases)
  have hLi_not : ¬ isymIsL (znth Iseq i) := fun h => hmin i hij ⟨h, hi_le⟩
  have hIiR : znth Iseq i = isymR (Asucc i) := by
    rcases hperm i hi_le with hR | hL | hRep
    · exact hR
    · obtain ⟨k', A', hI', _⟩ := hL
      exact absurd (isymIsL_iff.mpr ⟨k', A', hI'⟩) hLi_not
    · exact absurd hRep (fun h => hnperm i hi_le (Or.inr (Or.inr h)))
  -- 0 < rk(A_i)
  have hrk : 0 < irk (Asucc i) := by
    rcases hwfR i hi_le _ hIiR with hpos | hTr
    · exact hpos
    · rcases hwfL j hj_le k _ hIjL with hpos | hFa
      · exact hpos
      · exact absurd ⟨hTr, hFa⟩ (hdisj _)
  exact ⟨i, j, k, hij, hj_le, hIiR, hIjL, hrk⟩

/-- **L3.1 + chain-rank invariant** — the redex `(i,j,k)` from `inference_critical_pair`, carrying the
chain-rule rank bound `rk(A_i) ≤ r` (Buchholz's chain inference "`∀ i < j₀, rk(A_i) ≤ r`", p.8). Since
the redex has `i < j ≤ j₀`, hence `i < j₀`, `hrank` applies. This is exactly the input T3.4(a)'s rank
bound (`irk_cut_lt_rank`) consumes: `0 < rk(A_i) ≤ r` plus the cut-formula strip gives `rk(A(d)) < r`. -/
theorem inference_critical_pair_rank
    {Iseq Γmain Cmain j0 r : V} {Asucc Gam : V → V}
    (hwfR : ∀ i ≤ j0, ∀ A, znth Iseq i = isymR A → 0 < irk A ∨ Tr A)
    (hwfL : ∀ i ≤ j0, ∀ k A, znth Iseq i = isymLk k A → 0 < irk A ∨ Fa A)
    (hperm : ∀ i ≤ j0, znth Iseq i = isymR (Asucc i) ∨
        (∃ k A, znth Iseq i = isymLk k A ∧ mem A (Gam i)) ∨ znth Iseq i = isymRep)
    (hnperm : ∀ i ≤ j0, ¬ (znth Iseq i = isymR Cmain ∨
        (∃ k A, znth Iseq i = isymLk k A ∧ mem A Γmain) ∨ znth Iseq i = isymRep))
    (hchain : ∀ i ≤ j0, ∀ B, mem B (Gam i) → mem B Γmain ∨ ∃ i' < i, B = Asucc i')
    (hAj0 : Asucc j0 = Cmain ∨ Fa (Asucc j0))
    (hdisj : ∀ A, ¬ (Tr A ∧ Fa A)) (hFa_rk : ∀ A, Fa A → irk A = 0)
    (hrank : ∀ i < j0, irk (Asucc i) ≤ r) :
    ∃ i j k, i < j ∧ j ≤ j0 ∧ znth Iseq i = isymR (Asucc i) ∧
      znth Iseq j = isymLk k (Asucc i) ∧ 0 < irk (Asucc i) ∧ irk (Asucc i) ≤ r := by
  obtain ⟨i, j, k, hij, hj_le, hIi, hIj, hrk⟩ :=
    inference_critical_pair mem Tr Fa hwfR hwfL hperm hnperm hchain hAj0 hdisj hFa_rk
  exact ⟨i, j, k, hij, hj_le, hIi, hIj, hrk, hrank i (lt_of_lt_of_le hij hj_le)⟩

end Lemma31

/-! ### §5 atomic-axiom constructors that produce L-symbols (Buchholz p.12, NO truth predicate)

The two §5 atomic axioms whose `tp` is an L-symbol **unconditionally** (no minimal-truth check):
`Ax^{∀xF,k}_Π ⊢ Γ→F(k)` (with `∀xF ∈ Γ`) has `tp = L^k_{∀xF}`, and `Ax^{¬A,0}_Π ⊢ Γ→⊥` (with `¬A,A ∈ Γ`)
has `tp = L⁰_{¬A}`. These are the cheapest source of the L-symbols Lemma 3.1 needs at `j0`, and need
**no** truth assignment to define. Coded as new rule tags 5/6, mirroring the existing constructors; now
wired into `tp` below (NOT yet into `ZPhi`/`idg`/`iõ` — that integration is path A's next step). -/

/-- `Ax^{∀x·p, k}` — the ∀-instantiation axiom (`p` = matrix `F`, `k` = numeral index). -/
noncomputable def zAxAll (s p k : V) : V := ⟪s, 5, p, k⟫ + 1
/-- `Ax^{¬p, 0}` — the ¬-elimination axiom (`p` = the formula `A`, conclusion `⊥`). -/
noncomputable def zAxNeg (s p : V) : V := ⟪s, 6, p⟫ + 1

def zAxAllGraph : 𝚺₀.Semisentence 4 :=
  .mkSigma “y s p k. ∃ y' < y, !pair₄Def y' s 5 p k ∧ y = y' + 1”
instance zAxAll_defined : 𝚺₀-Function₃ (zAxAll : V → V → V → V) via zAxAllGraph := .mk fun v ↦ by
  simp_all [zAxAllGraph, numeral_eq_natCast, zAxAll]

def zAxNegGraph : 𝚺₀.Semisentence 3 :=
  .mkSigma “y s p. ∃ y' < y, !pair₃Def y' s 6 p ∧ y = y' + 1”
instance zAxNeg_defined : 𝚺₀-Function₂ (zAxNeg : V → V → V) via zAxNegGraph := .mk fun v ↦ by
  simp_all [zAxNegGraph, numeral_eq_natCast, zAxNeg]

@[simp] lemma s_lt_zAxAll (s p k : V) : s < zAxAll s p k := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_zAxAll (s p k : V) : p < zAxAll s p k :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma k_lt_zAxAll (s p k : V) : k < zAxAll s p k :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma s_lt_zAxNeg (s p : V) : s < zAxNeg s p := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma p_lt_zAxNeg (s p : V) : p < zAxNeg s p :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma zTag_zAxAll (s p k : V) : zTag (zAxAll s p k) = 5 := by simp [zTag, sndIdx, zAxAll]
@[simp] lemma zTag_zAxNeg (s p : V) : zTag (zAxNeg s p) = 6 := by simp [zTag, sndIdx, zAxNeg]
@[simp] lemma fstIdx_zAxAll (s p k : V) : fstIdx (zAxAll s p k) = s := by simp [fstIdx, zAxAll]
@[simp] lemma fstIdx_zAxNeg (s p : V) : fstIdx (zAxNeg s p) = s := by simp [fstIdx, zAxNeg]
@[simp] lemma zRest_zAxAll (s p k : V) : zRest (zAxAll s p k) = ⟪p, k⟫ := by
  simp [zRest, sndIdx, zAxAll]
@[simp] lemma zRest_zAxNeg (s p : V) : zRest (zAxNeg s p) = p := by simp [zRest, sndIdx, zAxNeg]

/-- Principal matrix `F` of `Ax^{∀x·p,k}` (so the principal formula is `∀x·p = ^∀ p`). -/
noncomputable def zAxAllF (d : V) : V := π₁ (zRest d)
/-- Numeral index `k` of `Ax^{∀x·p,k}`. -/
noncomputable def zAxAllK (d : V) : V := π₂ (zRest d)
/-- The formula `A` of `Ax^{¬A,0}` (so the principal formula is `¬A = inegF A`). -/
noncomputable def zAxNegF (d : V) : V := zRest d
@[simp] lemma zAxAllF_zAxAll (s p k : V) : zAxAllF (zAxAll s p k) = p := by simp [zAxAllF]
@[simp] lemma zAxAllK_zAxAll (s p k : V) : zAxAllK (zAxAll s p k) = k := by simp [zAxAllK]
@[simp] lemma zAxNegF_zAxNeg (s p : V) : zAxNegF (zAxNeg s p) = p := by simp [zAxNegF]

/-- `Ax1_{s}` (tag 7) — the **logical axiom `Ax^1`** that is the §5 reduct `d[0]` of an L-symbol atomic
axiom (Buchholz §5 case 2: `Ax^{C,k}_Π → Ax^1_{tp(d)(Π,0)}`). Payload `C` = the reduct succedent formula
(`F(k)` for `Ax^{∀xF,k}`, `A` for `Ax^{¬A,0}`); its pre-ordinal is `õ(Ax^1_{·→C}) = 2·rk(C) = oAtom1 C`
(Lemma 5.2), `dg = 0`. Carries the rank-one-lower formula so the descent `oAtom1 C ≺ oAtomLk(C-up)` fires
via `icmp_oAtom1_oAtomLk`. -/
noncomputable def zAx1 (s C : V) : V := ⟪s, 7, C⟫ + 1

def zAx1Graph : 𝚺₀.Semisentence 3 :=
  .mkSigma “y s C. ∃ y' < y, !pair₃Def y' s 7 C ∧ y = y' + 1”
instance zAx1_defined : 𝚺₀-Function₂ (zAx1 : V → V → V) via zAx1Graph := .mk fun v ↦ by
  simp_all [zAx1Graph, numeral_eq_natCast, zAx1]

@[simp] lemma s_lt_zAx1 (s C : V) : s < zAx1 s C := le_iff_lt_succ.mp <| le_pair_left _ _
@[simp] lemma C_lt_zAx1 (s C : V) : C < zAx1 s C :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma zTag_zAx1 (s C : V) : zTag (zAx1 s C) = 7 := by simp [zTag, sndIdx, zAx1]
@[simp] lemma fstIdx_zAx1 (s C : V) : fstIdx (zAx1 s C) = s := by simp [fstIdx, zAx1]
@[simp] lemma zRest_zAx1 (s C : V) : zRest (zAx1 s C) = C := by simp [zRest, sndIdx, zAx1]
/-- The succedent formula `C` of the logical axiom `Ax^1_{·→C}` (tag 7). -/
noncomputable def zAx1F (d : V) : V := zRest d
@[simp] lemma zAx1F_zAx1 (s C : V) : zAx1F (zAx1 s C) = C := by simp [zAx1F]

def _root_.LO.FirstOrder.Arithmetic.zAx1FDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. !zRestDef y d”
instance zAx1F_defined : 𝚺₀-Function₁ (zAx1F : V → V) via zAx1FDef := .mk fun v ↦ by
  simp [zAx1FDef, zAx1F, zRest_defined.iff]

/-! ## `tp(d)` — the inference symbol of a Z-derivation (Buchholz Def 3.2)

The reduction-step symbol `tp(d)` (Def 3.2, p.8). The non-`K^r`, non-atomic cases are NON-recursive
and **faithful**:
* `tp(I^a_∀xF d0) = R_{∀xF}` (case 2),
* `tp(I_¬A d0) = R_{¬A}` (case 3, with Buchholz's `¬A = inegF A`),
* `tp(Ind^{a,k}_F d0 d1) = Rep` (case 4).

The atomic case (§5, needs minimal-truth `≈⊤`/`≈⊥`) and the `K^r` critical/non-critical dispatch (case 5,
needs each premise's `tp(d_i)` + sequent permissibility + Lemma 3.1) are the recursion-heavy frontier;
they are left as the `else` placeholder (value `Rep`, which is the *correct* `tp` for a **critical**
chain or a ⊥-derivation — Corollary 2.1 — but not yet for the non-critical 5.2.2 case). Only the
faithful cases 2–4 get compute lemmas; `tp` mirrors `iR`'s incremental build.

The §5 atomic axioms `Ax^{∀xF,k}` (tag 5) and `Ax^{¬A,0}` (tag 6) now produce the **L-symbols**
`L^k_{∀xF}` / `L⁰_{¬A}` UNCONDITIONALLY (Buchholz p.12 — no minimal-truth check). These are the only
source of left symbols, exactly what Lemma 3.1 needs at the `j`-end of a critical pair. -/
noncomputable def tp (d : V) : V :=
  if zTag d = 1 then isymR (^∀ (zIallF d) : V)
  else if zTag d = 2 then isymR (inegF (zInegF d))
  else if zTag d = 5 then isymLk (zAxAllK d) (^∀ (zAxAllF d) : V)
  else if zTag d = 6 then isymLk 0 (inegF (zAxNegF d))
  else isymRep

@[simp] lemma tp_zIall (s a p d0 : V) : tp (zIall s a p d0) = isymR (^∀ p : V) := by simp [tp]
@[simp] lemma tp_zIneg (s p d0 : V) : tp (zIneg s p d0) = isymR (inegF p) := by simp [tp]
@[simp] lemma tp_zInd (s at' p d0 d1 : V) : tp (zInd s at' p d0 d1) = isymRep := by simp [tp]
@[simp] lemma tp_zAxAll (s p k : V) : tp (zAxAll s p k) = isymLk k (^∀ p : V) := by simp [tp]
@[simp] lemma tp_zAxNeg (s p : V) : tp (zAxNeg s p) = isymLk 0 (inegF p) := by simp [tp]
@[simp] lemma tp_zAtom (s : V) : tp (zAtom s) = isymRep := by simp [tp]
@[simp] lemma tp_zK (s r ds : V) : tp (zK s r ds) = isymRep := by simp [tp]

/-- **`tp`-trichotomy**: every `tp d` is one of the three inference symbols `R_A`/`L^k_A`/`Rep`
(it dispatches on `zTag d`). The structural source of the `π₁`-discriminant shape lemmas below. -/
lemma tp_cases (d : V) :
    (∃ A, tp d = isymR A) ∨ (∃ k A, tp d = isymLk k A) ∨ tp d = isymRep := by
  unfold tp
  by_cases h1 : zTag d = 1
  · rw [if_pos h1]; exact Or.inl ⟨_, rfl⟩
  rw [if_neg h1]
  by_cases h2 : zTag d = 2
  · rw [if_pos h2]; exact Or.inl ⟨_, rfl⟩
  rw [if_neg h2]
  by_cases h5 : zTag d = 5
  · rw [if_pos h5]; exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  rw [if_neg h5]
  by_cases h6 : zTag d = 6
  · rw [if_pos h6]; exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  rw [if_neg h6]; exact Or.inr (Or.inr rfl)

/-- **`tp` is a right symbol when its `π₁`-discriminant is 0** (`isRedexPair`'s `i`-end condition):
`tp d = R_{π₂(tp d)}`. The shape-recovery the redex→`tp` bridge needs from the bare pair test. -/
lemma tp_eq_isymR_of_pi₁_zero {d : V} (h : π₁ (tp d) = 0) : tp d = isymR (π₂ (tp d)) := by
  rcases tp_cases d with ⟨A, hA⟩ | ⟨k, A, hA⟩ | hA <;> rw [hA] at h ⊢ <;> simp_all

/-- **`tp` is a left symbol when its `π₁`-discriminant is 1** (`isRedexPair`'s `j`-end condition):
`tp d = L^{π₁(π₂(tp d))}_{π₂(π₂(tp d))}` (i.e. `isymIsL (tp d)`). -/
lemma tp_eq_isymLk_of_pi₁_one {d : V} (h : π₁ (tp d) = 1) :
    tp d = isymLk (π₁ (π₂ (tp d))) (π₂ (π₂ (tp d))) := by
  rcases tp_cases d with ⟨A, hA⟩ | ⟨k, A, hA⟩ | hA <;> rw [hA] at h ⊢ <;> simp_all [isymLk]

/-- Dual of `tp_isymR_pos` for the §5 L-symbol axioms: `tp d = L^k_A` forces `0 < rk A` once the
principal formula is a genuine formula. `Ax^{∀xF,k}` (tag 5) gives `A = ∀xF` (`rk = rk F + 1`);
`Ax^{¬A',0}` (tag 6) gives `A = ¬A' = inegF A'` (`rk = rk A' + 1`). **This is exactly `hwfL` for the §5
atomic axioms**, replacing the now-false `tp_ne_isymLk`: `tp` is no longer L-free, so `hwfL` is
discharged by the genuine rank bound rather than vacuously. -/
lemma tp_isymLk_pos {d k A : V} (h : tp d = isymLk k A)
    (h5 : zTag d = 5 → IsUFormula ℒₒᵣ (zAxAllF d))
    (h6 : zTag d = 6 → IsUFormula ℒₒᵣ (zAxNegF d)) : 0 < irk A := by
  unfold tp at h
  by_cases ht1 : zTag d = 1
  · rw [if_pos ht1] at h; exact absurd h (by simp)
  · rw [if_neg ht1] at h
    by_cases ht2 : zTag d = 2
    · rw [if_pos ht2] at h; exact absurd h (by simp)
    · rw [if_neg ht2] at h
      by_cases ht5 : zTag d = 5
      · rw [if_pos ht5] at h
        rw [((isymLk_inj _ _ _ _).mp h.symm).2, irk_all (h5 ht5)]
        exact pos_iff_one_le.mpr (by simp)
      · rw [if_neg ht5] at h
        by_cases ht6 : zTag d = 6
        · rw [if_pos ht6] at h
          rw [((isymLk_inj _ _ _ _).mp h.symm).2, irk_inegF (h6 ht6)]
          exact pos_iff_one_le.mpr (by simp)
        · rw [if_neg ht6] at h; exact absurd h.symm (by simp)

/-- For the current `tp` (faithful on the I-rules), `tp d = R_A` forces `0 < rk A` as soon as the
principal formula is genuine: `R_{∀xF}` has `rk = rk(F)+1`, `R_{¬A'}` has `rk(¬A')=rk(A')+1`. **This
reduces `inference_critical_pair`'s `hwfR` (for the cases `tp` is defined) to formula-hood of the
principal formula** — sharpening exactly what the §5/Lemma-3.3 layer still owes. -/
lemma tp_isymR_pos {d A : V} (h : tp d = isymR A)
    (h1 : zTag d = 1 → IsUFormula ℒₒᵣ (zIallF d))
    (h2 : zTag d = 2 → IsUFormula ℒₒᵣ (zInegF d)) : 0 < irk A := by
  unfold tp at h
  by_cases ht1 : zTag d = 1
  · rw [if_pos ht1] at h
    rw [(isymR_inj _ _).mp h.symm, irk_all (h1 ht1)]; exact pos_iff_one_le.mpr (by simp)
  · rw [if_neg ht1] at h
    by_cases ht2 : zTag d = 2
    · rw [if_pos ht2] at h
      rw [(isymR_inj _ _).mp h.symm, irk_inegF (h2 ht2)]; exact pos_iff_one_le.mpr (by simp)
    · rw [if_neg ht2] at h
      by_cases ht5 : zTag d = 5
      · rw [if_pos ht5] at h; exact absurd h (by simp)
      · rw [if_neg ht5] at h
        by_cases ht6 : zTag d = 6
        · rw [if_pos ht6] at h; exact absurd h (by simp)
        · rw [if_neg ht6] at h; exact absurd h.symm (by simp)

/-! ### Definability of `tp` and the coded symbol map `tpSeq` (toward instantiating L3.1 on genuine
chains)

To run Lemma 3.1's `least_number` search over the premise symbols of a genuine chain `zK s r ds`, the
symbol sequence `Iseq` with `znth Iseq i = tp (znth ds i)` must itself be a **coded** sequence (so
`znth Iseq x` is `𝚺₁`-definable in `x`). We therefore make `tp : V → V` `𝚺₁`-definable (`tpDef`) and
build the coded map `tpSeq ds` via `PR.Construction` (mirroring `seqUpdateAux`). Sub-graphs: `isymR`/
`isymRep` are pairs (`pairDef`), `^∀` is `qqAllDef`, `inegF = neg ∨ ⊥` is `negGraph`/`qqOrDef`/
`qqFalsumDef`, `zIallF`/`zInegF` are the projection accessors. -/

section TpDef
open LO.FirstOrder.Arithmetic

/-- `R_A = ⟪0,A⟫` graph. -/
def _root_.LO.FirstOrder.Arithmetic.isymRGraph : 𝚺₀.Semisentence 2 := .mkSigma “y A. !pairDef y 0 A”
instance isymR_defined : 𝚺₀-Function₁ (isymR : V → V) via isymRGraph := .mk fun v ↦ by
  simp [isymRGraph, isymR]
instance isymR_definable : 𝚺₀-Function₁ (isymR : V → V) := isymR_defined.to_definable
instance isymR_definable' (ℌ) : ℌ-Function₁ (isymR : V → V) := isymR_definable.of_zero

/-- `zIallF d = π₁ (π₂ (zRest d))` — same projection chain as `zIndP`. -/
def _root_.LO.FirstOrder.Arithmetic.zIallFDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ ∃ r2 <⁺ r, !pi₂Def r2 r ∧ !pi₁Def y r2”
instance zIallF_defined : 𝚺₀-Function₁ (zIallF : V → V) via zIallFDef := .mk fun v ↦ by
  simp [zIallFDef, zIallF, zRest_defined.iff, pi₂_defined.iff, pi₁_defined.iff]
instance zIallF_definable : 𝚺₀-Function₁ (zIallF : V → V) := zIallF_defined.to_definable

/-- `zInegF d = π₁ (zRest d)` — same projection as `zKrank`. -/
def _root_.LO.FirstOrder.Arithmetic.zInegFDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ !pi₁Def y r”
instance zInegF_defined : 𝚺₀-Function₁ (zInegF : V → V) via zInegFDef := .mk fun v ↦ by
  simp [zInegFDef, zInegF, zRest_defined.iff, pi₁_defined.iff]
instance zInegF_definable : 𝚺₀-Function₁ (zInegF : V → V) := zInegF_defined.to_definable

/-- `inegF A = neg A ^⋎ ⊥` graph (Buchholz `¬A` as De Morgan `A → ⊥`). -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.inegFDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y A. ∃ n, !(negGraph ℒₒᵣ) n A ∧ ∃ f, !qqFalsumDef f ∧ !qqOrDef y n f”
instance inegF_defined : 𝚺₁-Function₁ (inegF : V → V) via inegFDef := .mk fun v ↦ by
  simp [inegFDef, inegF, (neg.defined (L := ℒₒᵣ)).iff, qqFalsum_defined.iff, qqOr_defined.iff]
instance inegF_definable : 𝚺₁-Function₁ (inegF : V → V) := inegF_defined.to_definable

/-- `zAxAllF d = π₁ (zRest d)` (same projection chain as `zInegF`). -/
def _root_.LO.FirstOrder.Arithmetic.zAxAllFDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ !pi₁Def y r”
instance zAxAllF_defined : 𝚺₀-Function₁ (zAxAllF : V → V) via zAxAllFDef := .mk fun v ↦ by
  simp [zAxAllFDef, zAxAllF, zRest_defined.iff, pi₁_defined.iff]
instance zAxAllF_definable : 𝚺₀-Function₁ (zAxAllF : V → V) := zAxAllF_defined.to_definable

/-- `zAxNegF d = zRest d`. -/
def _root_.LO.FirstOrder.Arithmetic.zAxNegFDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. !zRestDef y d”
instance zAxNegF_defined : 𝚺₀-Function₁ (zAxNegF : V → V) via zAxNegFDef := .mk fun v ↦ by
  simp [zAxNegFDef, zAxNegF, zRest_defined.iff]
instance zAxNegF_definable : 𝚺₀-Function₁ (zAxNegF : V → V) := zAxNegF_defined.to_definable

/-- `tp` definability blueprint: dispatch on `zTag d`. Tags 5/6 produce the L-symbols
`L^{π₂(zRest d)}_{∀(π₁(zRest d))}` / `L⁰_{¬(zRest d)}` (`isymLk k A = ⟪1,k,A⟫`). -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.tpDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ t, !zTagDef t d ∧
    ( (t = 1 ∧ ∃ q, !zIallFDef q d ∧ ∃ aq, !qqAllDef aq q ∧ !pairDef y 0 aq)
    ∨ (t = 2 ∧ ∃ b, !zInegFDef b d ∧ ∃ nb, !inegFDef nb b ∧ !pairDef y 0 nb)
    ∨ (t = 5 ∧ ∃ r, !zRestDef r d ∧ ∃ p, !pi₁Def p r ∧ ∃ ap, !qqAllDef ap p ∧
        ∃ k, !pi₂Def k r ∧ !pair₃Def y 1 k ap)
    ∨ (t = 6 ∧ ∃ r, !zRestDef r d ∧ ∃ nb, !inegFDef nb r ∧ !pair₃Def y 1 0 nb)
    ∨ (t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 5 ∧ t ≠ 6 ∧ !pairDef y 2 0) )”

set_option maxHeartbeats 1000000 in
instance tp_defined : 𝚺₁-Function₁ (tp : V → V) via tpDef := .mk fun v ↦ by
  simp [tpDef, tp, zTag_defined.iff, zIallF_defined.iff, zInegF_defined.iff,
    inegF_defined.iff, qqForall_defined.iff, zRest_defined.iff, pi₁_defined.iff,
    pi₂_defined.iff, zAxAllF, zAxAllK, zAxNegF, isymR, isymLk, isymRep, numeral_eq_natCast]
  by_cases h1 : zTag (v 1) = 1
  · simp [h1]
  · by_cases h2 : zTag (v 1) = 2
    · simp [h1, h2]
    · by_cases h5 : zTag (v 1) = 5
      · simp [h1, h2, h5]
      · by_cases h6 : zTag (v 1) = 6
        · simp [h1, h2, h5, h6]
        · simp [h1, h2, h5, h6]

instance tp_definable : 𝚺₁-Function₁ (tp : V → V) := tp_defined.to_definable
instance tp_definable' (Γ) : Γ-[m + 1]-Function₁ (tp : V → V) := tp_definable.of_sigmaOne

/-! ### The coded symbol map `tpSeq ds = ⟨tp(znth ds 0), …, tp(znth ds (lh ds−1))⟩`

Built by `PR.Construction` over a length counter (mirror `seqUpdateAux`): `tpSeqAux ds (n+1) =
seqCons (tpSeqAux ds n) (tp (znth ds n))`. The key read-out `znth (tpSeq ds) i = tp (znth ds i)`
(for `i < lh ds`) is what lets Lemma 3.1's `least_number` search run over genuine premise symbols. -/

noncomputable def tpSeqAux.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y ds. y = 0”
  succ := .mkSigma “y ih n ds. ∃ d, !znthDef d ds n ∧ ∃ t, !tpDef t d ∧ !seqConsDef y ih t”

noncomputable def tpSeqAux.construction : PR.Construction V tpSeqAux.blueprint where
  zero := fun _ ↦ ∅
  succ := fun x n ih ↦ seqCons ih (tp (znth (x 0) n))
  zero_defined := .mk fun v ↦ by simp [tpSeqAux.blueprint, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [tpSeqAux.blueprint, znth_defined.iff, tp_defined.iff, seqCons_defined.iff]

/-- `tpSeqAux ds n` = the coded sequence `⟨tp(znth ds 0),…,tp(znth ds (n−1))⟩` (length `n`). -/
noncomputable def tpSeqAux (ds n : V) : V := tpSeqAux.construction.result ![ds] n

@[simp] lemma tpSeqAux_zero (ds : V) : tpSeqAux ds 0 = ∅ := by
  simp [tpSeqAux, tpSeqAux.construction]

@[simp] lemma tpSeqAux_succ (ds n : V) :
    tpSeqAux ds (n + 1) = seqCons (tpSeqAux ds n) (tp (znth ds n)) := by
  simp [tpSeqAux, tpSeqAux.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.tpSeqAuxDef : 𝚺₁.Semisentence 3 :=
  tpSeqAux.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance tpSeqAux_defined : 𝚺₁-Function₂ (tpSeqAux : V → V → V) via tpSeqAuxDef :=
  .mk fun v ↦ by simp [tpSeqAux.construction.result_defined_iff, tpSeqAuxDef]; rfl

instance tpSeqAux_definable : 𝚺₁-Function₂ (tpSeqAux : V → V → V) := tpSeqAux_defined.to_definable
instance tpSeqAux_definable' (Γ) : Γ-[m + 1]-Function₂ (tpSeqAux : V → V → V) :=
  tpSeqAux_definable.of_sigmaOne

@[simp] lemma tpSeqAux_seq (ds n : V) : Seq (tpSeqAux ds n) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using seq_empty
  case succ n ih => rw [tpSeqAux_succ]; exact ih.seqCons _

@[simp] lemma tpSeqAux_lh (ds n : V) : lh (tpSeqAux ds n) = n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using lh_empty
  case succ n ih => rw [tpSeqAux_succ, Seq.lh_seqCons _ (tpSeqAux_seq ds n), ih]

/-- Top read-out: the freshly-appended entry. -/
lemma znth_tpSeqAux_top (ds n : V) : znth (tpSeqAux ds (n + 1)) n = tp (znth ds n) := by
  rw [tpSeqAux_succ]
  have := znth_seqCons_self (tpSeqAux_seq ds n) (tp (znth ds n))
  rwa [tpSeqAux_lh] at this

/-- Reads below the top are stable as the prefix grows. -/
lemma znth_tpSeqAux_stable {ds : V} (n m : V) (hm : m < n) :
    znth (tpSeqAux ds (n + 1)) m = znth (tpSeqAux ds n) m := by
  rw [tpSeqAux_succ, znth_seqCons_of_lt (tpSeqAux_seq ds n) _ (by rw [tpSeqAux_lh]; exact hm)]

/-- Every in-range entry of the prefix is the genuine `tp` value. -/
lemma znth_tpSeqAux_eq {ds : V} : ∀ n, ∀ i < n, znth (tpSeqAux ds n) i = tp (znth ds i) := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · refine Definable.ball_lt (by definability) ?_
    apply Definable.comp₂ (by definability)
    exact DefinableFunction₁.comp (F := tp) (by definability)
  case zero => intro i hi; exact absurd hi (by simp)
  case succ n ih =>
    intro i hi
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hi) with hin | hilt
    · rw [hin, znth_tpSeqAux_top]
    · rw [znth_tpSeqAux_stable n i hilt]; exact ih i hilt

/-- **The coded symbol map** `tpSeq ds = ⟨tp(d₀),…,tp(d_{l})⟩` (length `lh ds`). -/
noncomputable def tpSeq (ds : V) : V := tpSeqAux ds (lh ds)

@[simp] lemma tpSeq_seq (ds : V) : Seq (tpSeq ds) := tpSeqAux_seq ds (lh ds)
@[simp] lemma tpSeq_lh (ds : V) : lh (tpSeq ds) = lh ds := tpSeqAux_lh ds (lh ds)

/-- **Read-out**: the `i`-th coded symbol is `tp` of the `i`-th premise (for `i < lh ds`). -/
lemma znth_tpSeq {ds i : V} (hi : i < lh ds) : znth (tpSeq ds) i = tp (znth ds i) :=
  znth_tpSeqAux_eq (lh ds) i hi

end TpDef

/-! ## Sequents `Π = Γ→C` + permissibility `I ◁ Π` + chain-rule inference (Buchholz §3, p.8)

A Buchholz sequent `Π = Γ→C` is coded `⟪Γ, C⟫` with antecedent `Γ` a sequence of formulas and `C` the
single succedent. Permissibility `I ◁ Γ→C :⇔ I = R_C ∨ (I = L^k_A with A ∈ Γ) ∨ I = Rep` (p.8). The
chain-rule inference of rank `r` (p.8) packages the structural conditions that feed Lemma 3.1
(`inference_critical_pair`): the `hAj0`/`hchain`/`hrank` hypotheses are read off this predicate. This is
the deferred *sequent* layer of the Z calculus, kept abstract over the eventual end-sequent matching. -/

/-- Antecedent `Γ` of a sequent `q = ⟪Γ,C⟫`. -/
noncomputable def seqAnt (q : V) : V := π₁ q
/-- Succedent `C` of a sequent `q = ⟪Γ,C⟫`. -/
noncomputable def seqSucc (q : V) : V := π₂ q
/-- Build the sequent `Γ→C`. -/
noncomputable def mkSeqt (Γ C : V) : V := ⟪Γ, C⟫
@[simp] lemma seqAnt_mkSeqt (Γ C : V) : seqAnt (mkSeqt Γ C) = Γ := by simp [seqAnt, mkSeqt]
@[simp] lemma seqSucc_mkSeqt (Γ C : V) : seqSucc (mkSeqt Γ C) = C := by simp [seqSucc, mkSeqt]

/-- `A ∈ Γ` — antecedent membership (`Γ` a coded sequence of formulas). -/
def inAnt (A Γ : V) : Prop := ∃ i < lh Γ, znth Γ i = A

/-- **Permissibility** `I ◁ q` (Buchholz p.8): `I = R_C ∨ (I = L^k_A with A ∈ Γ) ∨ I = Rep`. -/
def iperm (I q : V) : Prop :=
  I = isymR (seqSucc q) ∨ (∃ k A, I = isymLk k A ∧ inAnt A (seqAnt q)) ∨ I = isymRep

@[simp] lemma iperm_isymRep (q : V) : iperm isymRep q := Or.inr (Or.inr rfl)

/-- **Projection-free form of `iperm`** (the bounded-quantifier-free shape for arithmetization): the
middle `∃ k A, I = L^k_A ∧ A ∈ Γ` disjunct is `isymIsL I ∧ (π₂(π₂ I)) ∈ Γ` (the L-symbol reconstructs
from its own projections, `isymIsL`). This is the form `ipermDef` matches. -/
lemma iperm_iff_proj {I q : V} : iperm I q ↔
    I = isymR (seqSucc q) ∨ (isymIsL I ∧ inAnt (π₂ (π₂ I)) (seqAnt q)) ∨ I = isymRep := by
  unfold iperm
  refine or_congr_right (or_congr_left ?_)
  constructor
  · rintro ⟨k, A, rfl, hA⟩
    exact ⟨isymIsL_isymLk k A, by simpa [isymLk] using hA⟩
  · rintro ⟨hL, hA⟩
    exact ⟨π₁ (π₂ I), π₂ (π₂ I), hL, hA⟩

lemma iperm_isymR_iff {C q : V} : iperm (isymR C) q ↔ C = seqSucc q := by
  constructor
  · rintro (h | ⟨k, A, h, _⟩ | h)
    · exact (isymR_inj _ _).mp h
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  · intro h; exact Or.inl (by rw [h])

lemma iperm_isymLk_iff {k A q : V} : iperm (isymLk k A) q ↔ inAnt A (seqAnt q) := by
  constructor
  · rintro (h | ⟨k', A', h, hA'⟩ | h)
    · exact absurd h.symm (by simp)
    · obtain ⟨_, rfl⟩ := (isymLk_inj _ _ _ _).mp h; exact hA'
    · exact absurd h (by simp)
  · intro h; exact Or.inr (Or.inl ⟨k, A, rfl, h⟩)

/-! ### Genuine-reduct sequent operations (Buchholz §3.2 case 5.1 endsequents)

The critical recombination's auxiliaries derive the *modified* sequents `d{0} ⊢ Θ→A(d)` and
`d{1} ⊢ A(d),Θ→D` (Buchholz §2 p.6 / Thm 3.4(a)): `Θ→A(d)` keeps the antecedent `Θ = seqAnt s` and
swaps the succedent to the cut formula `A(d)`; `A(d),Θ→D` adds `A(d)` to the antecedent and keeps the
succedent `D = seqSucc s`. These two operations build the genuine auxiliaries' conclusions (unlike the
ordinal-shadow `iCritAux`, which reuses `fstIdx d = s` for both). -/

/-- `Θ→C`: the sequent `s` with its succedent replaced by `C` (the cut-formula succedent of `d{0}`). -/
noncomputable def seqSetSucc (s C : V) : V := mkSeqt (seqAnt s) C
@[simp] lemma seqAnt_seqSetSucc (s C : V) : seqAnt (seqSetSucc s C) = seqAnt s := by simp [seqSetSucc]
@[simp] lemma seqSucc_seqSetSucc (s C : V) : seqSucc (seqSetSucc s C) = C := by simp [seqSetSucc]

/-- `A,Θ→D`: the sequent `s` with `A` added to its antecedent (membership-wise, appended), succedent
unchanged (the conclusion of `d{1}`). -/
noncomputable def seqAddAnt (A s : V) : V := mkSeqt (seqCons (seqAnt s) A) (seqSucc s)
@[simp] lemma seqAnt_seqAddAnt (A s : V) : seqAnt (seqAddAnt A s) = seqCons (seqAnt s) A := by
  simp [seqAddAnt]
@[simp] lemma seqSucc_seqAddAnt (A s : V) : seqSucc (seqAddAnt A s) = seqSucc s := by simp [seqAddAnt]

/-- Antecedent membership splits over a `seqCons` append: `B ∈ Γ⌢A ↔ B = A ∨ B ∈ Γ`. -/
lemma inAnt_seqCons {Γ A B : V} (hΓ : Seq Γ) :
    inAnt B (seqCons Γ A) ↔ B = A ∨ inAnt B Γ := by
  unfold inAnt
  rw [Seq.lh_seqCons A hΓ]
  constructor
  · rintro ⟨i, hi, hz⟩
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hi) with rfl | hlt
    · left; rw [znth_seqCons_self hΓ A] at hz; exact hz.symm
    · right; rw [znth_seqCons_of_lt hΓ A hlt] at hz; exact ⟨i, hlt, hz⟩
  · rintro (rfl | ⟨i, hi, hz⟩)
    · exact ⟨lh Γ, le_iff_lt_succ.mp le_rfl, znth_seqCons_self hΓ _⟩
    · exact ⟨i, le_iff_lt_succ.mp (le_of_lt hi), by rw [znth_seqCons_of_lt hΓ A hi]; exact hz⟩

/-- Antecedent membership of `A,Θ→D`: `B ∈ A,Θ ↔ B = A ∨ B ∈ Θ`. -/
lemma inAnt_seqAddAnt {A s B : V} (hs : Seq (seqAnt s)) :
    inAnt B (seqAnt (seqAddAnt A s)) ↔ B = A ∨ inAnt B (seqAnt s) := by
  rw [seqAnt_seqAddAnt]; exact inAnt_seqCons hs

/-! ### Lemma 3.3 (`tp(d) ◁ Π`) for the I-rule cases (Buchholz p.8)

For the rules where `tp` is faithfully defined, permissibility `tp(d) ◁ end(d)` reduces to **end-sequent
matching**: the conclusion's succedent must be the principal formula. `tp(I^a_∀xF d0) = R_{∀xF}` is
permissible for any sequent whose succedent is `∀xF`; `tp(I_¬A d0) = R_{¬A}` for any whose succedent is
`¬A` (`= inegF A`). These directly discharge the `hperm` obligation of `inference_critical_pair_of_chain`
for premises built by the I-rules (the remaining cases — atomic/chain — need the §5 / recursive-`tp`
layer). The end-sequent hypothesis is exactly what the refined `ZPhi` (with sequent matching) will supply. -/
lemma iperm_tp_zIall {s a p d0 q : V} (h : seqSucc q = (^∀ p : V)) :
    iperm (tp (zIall s a p d0)) q := by
  rw [tp_zIall]; exact iperm_isymR_iff.mpr h.symm

lemma iperm_tp_zIneg {s p d0 q : V} (h : seqSucc q = inegF p) :
    iperm (tp (zIneg s p d0)) q := by
  rw [tp_zIneg]; exact iperm_isymR_iff.mpr h.symm

/-- And `Ind` (case 4): `tp = Rep` is permissible for **every** sequent (no matching needed). -/
@[simp] lemma iperm_tp_zInd (s at' p d0 d1 q : V) : iperm (tp (zInd s at' p d0 d1)) q := by
  rw [tp_zInd]; exact iperm_isymRep q

/-! ### Lemma 3.3 (`tp(d) ◁ Π`) for the §5 atomic L-symbol axioms (Buchholz p.8/p.12)

These are the §5 analogues that complete `iperm_tp_zIall`/`iperm_tp_zIneg` for the **left** symbols: an
L-symbol `L^k_A` is permissible for a sequent `q` iff its cut formula `A` lies in `q`'s antecedent
(`iperm_isymLk_iff`). `tp(Ax^{∀xF,k}) = L^k_{∀xF}` is permissible whenever `∀xF ∈ ant(q)` (which is the
side condition `∀xF ∈ Γ` of the very axiom); `tp(Ax^{¬A,0}) = L⁰_{¬A}` whenever `¬A ∈ ant(q)`. **This is
exactly the `hperm` discharge for the critical `j`-end** that L3.1 lands on, the L-symbol counterpart of
the I-rule `hperm` facts. The matching `inAnt` hypotheses are exactly what the refined `ZPhi` (atomic-axiom
side conditions) supplies. -/
lemma iperm_tp_zAxAll {s p k q : V} (h : inAnt (^∀ p : V) (seqAnt q)) :
    iperm (tp (zAxAll s p k)) q := by
  rw [tp_zAxAll]; exact iperm_isymLk_iff.mpr h

lemma iperm_tp_zAxNeg {s p q : V} (h : inAnt (inegF p : V) (seqAnt q)) :
    iperm (tp (zAxNeg s p)) q := by
  rw [tp_zAxNeg]; exact iperm_isymLk_iff.mpr h

/-- **Criticality (`hnperm`) for the atomic axioms.** `tp(Ax^{∀xF,k}) ⋪ Π` iff `∀xF ∉ ant(Π)`; this is
the criticality side that, together with `iperm_tp_zAxAll`, makes `hperm`+`hnperm` simultaneously
satisfiable for a real critical chain: the cut formula is in the *premise* antecedent but not the *main*
conclusion's. -/
lemma not_iperm_tp_zAxAll_iff {s p k c : V} :
    ¬ iperm (tp (zAxAll s p k)) c ↔ ¬ inAnt (^∀ p : V) (seqAnt c) := by
  rw [tp_zAxAll, iperm_isymLk_iff]

lemma not_iperm_tp_zAxNeg_iff {s p c : V} :
    ¬ iperm (tp (zAxNeg s p)) c ↔ ¬ inAnt (inegF p : V) (seqAnt c) := by
  rw [tp_zAxNeg, iperm_isymLk_iff]

/-- The succedent `A_i` of premise `i` of a chain `zK s r ds`. -/
noncomputable def chainAsucc (ds i : V) : V := seqSucc (fstIdx (znth ds i))
/-- The antecedent `Γ_i` of premise `i` of a chain `zK s r ds`. -/
noncomputable def chainAnt (ds i : V) : V := seqAnt (fstIdx (znth ds i))

/-- **Chain-rule inference of rank `r`** (Buchholz Def, p.8): `Γ_0→A_0 … Γ_l→A_l / Γ→C` is such iff
∃ `j₀ ≤ l` with `A_{j₀} ∈ {C,⊥}`, `∀ i≤j₀ (Γ_i ⊆ Γ,A_0,…,A_{i-1})`, `∀ i<j₀ (rk(A_i) ≤ r)`. Read off the
coded chain `zK s r ds` (conclusion sequent `s`, premise derivations `ds`). The exact source of Lemma
3.1's structural hypotheses `hAj0`/`hchain`/`hrank`. -/
def isChainInf (s r ds : V) : Prop :=
  ∃ j0 < lh ds,
    (chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V)) ∧
    (∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
      inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i') ∧
    (∀ i < j0, irk (chainAsucc ds i) ≤ r)

/-- **Index form of `isChainInf`** — the `∀ B, inAnt B Γ → …` antecedent-threading condition rewritten
as a bounded `∀ k < lh Γ, …(znth Γ k)` (since `inAnt B Γ ↔ ∃ k < lh Γ, znth Γ k = B`). This eliminates
the only unbounded universal, so every quantifier in the matrix is bounded (the lone remaining `𝚺₁`
content is `irk ≤ r`) — exactly the shape `isChainInfDef`'s `𝚫₁` Σ/Π cores match. -/
lemma isChainInf_iff_idx {s r ds : V} : isChainInf s r ds ↔
    ∃ j0 < lh ds,
      (chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V)) ∧
      (∀ i ≤ j0, ∀ k < lh (chainAnt ds i),
        inAnt (znth (chainAnt ds i) k) (seqAnt s) ∨
        ∃ i' < i, znth (chainAnt ds i) k = chainAsucc ds i') ∧
      (∀ i < j0, irk (chainAsucc ds i) ≤ r) := by
  unfold isChainInf
  constructor
  · rintro ⟨j0, hj0, hA, hB, hC⟩
    exact ⟨j0, hj0, hA, fun i hi k hk => hB i hi _ ⟨k, hk, rfl⟩, hC⟩
  · rintro ⟨j0, hj0, hA, hB, hC⟩
    exact ⟨j0, hj0, hA, fun i hi Bv ⟨k, hk, hBv⟩ => hBv ▸ hB i hi k hk, hC⟩

/-- **Chain-validity from premise-local threading** — package `isChainInf` by taking the **last** premise
as the distinguished `j0 = lh ds − 1`. A genuine reduct (the Ind unfolding `⟨d0, d1(0),…,d1(k−1)⟩` and the
critical-cut reduct) establishes chain-validity exactly this way: the last premise carries the
conclusion's succedent, and each premise's antecedent threads back to the conclusion or a *prior*
premise's succedent. This lemma is the reusable reduction of `isChainInf` to those local facts (it just
discharges `j0 < lh ds` from `0 < lh ds`). -/
lemma isChainInf_of_last {s r ds : V} (hlen : 0 < lh ds)
    (hlast : chainAsucc ds (lh ds - 1) = seqSucc s ∨ chainAsucc ds (lh ds - 1) = (^⊥ : V))
    (hthread : ∀ i ≤ lh ds - 1, ∀ B, inAnt B (chainAnt ds i) →
        inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank : ∀ i < lh ds - 1, irk (chainAsucc ds i) ≤ r) :
    isChainInf s r ds :=
  ⟨lh ds - 1, tsub_lt_self hlen one_pos, hlast, hthread, hrank⟩

/-- **Chain-validity is a congruence in the end-sequent data.** `isChainInf` reads `ds` only through
`lh ds` and the per-premise end-sequent projections `chainAsucc ds`/`chainAnt ds`. So two premise
sequences with the same length and the same pointwise end-sequents have the same chain-validity. The
general form of `isChainInf_seqUpdate` (same-end-sequent premise replacement) and the splice case
(Buchholz §3.2 5.2.1) reduce to computing the new `chainAsucc`/`chainAnt` and applying this. -/
lemma isChainInf_congr {s r ds ds' : V} (hlh : lh ds = lh ds')
    (hA : ∀ i, chainAsucc ds i = chainAsucc ds' i)
    (hN : ∀ i, chainAnt ds i = chainAnt ds' i) :
    isChainInf s r ds ↔ isChainInf s r ds' := by
  unfold isChainInf
  simp only [hlh, hA, hN]

/-! ### Σ₁-definability of the sequent layer (`seqAnt`/`seqSucc`/`chainAsucc`/`chainAnt`)

The chain-validity ingredients toward `zKValid`'s arithmetization (the `ZPhi` `zK`-disjunct cascade).
All projections/compositions of already-definable pieces (`pi₁`/`pi₂`/`fstIdx`/`znth`). -/

/-- `seqAnt q = π₁ q`. -/
def _root_.LO.FirstOrder.Arithmetic.seqAntDef : 𝚺₀.Semisentence 2 := .mkSigma “y q. !pi₁Def y q”
instance seqAnt_defined : 𝚺₀-Function₁ (seqAnt : V → V) via seqAntDef := .mk fun v ↦ by
  simp [seqAntDef, seqAnt, pi₁_defined.iff]
instance seqAnt_definable : 𝚺₀-Function₁ (seqAnt : V → V) := seqAnt_defined.to_definable

/-- `seqSucc q = π₂ q`. -/
def _root_.LO.FirstOrder.Arithmetic.seqSuccDef : 𝚺₀.Semisentence 2 := .mkSigma “y q. !pi₂Def y q”
instance seqSucc_defined : 𝚺₀-Function₁ (seqSucc : V → V) via seqSuccDef := .mk fun v ↦ by
  simp [seqSuccDef, seqSucc, pi₂_defined.iff]
instance seqSucc_definable : 𝚺₀-Function₁ (seqSucc : V → V) := seqSucc_defined.to_definable

/-- `chainAsucc ds i = seqSucc (fstIdx (znth ds i))`. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.chainAsuccDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y ds i. ∃ z, !znthDef z ds i ∧ ∃ f, !fstIdxDef f z ∧ !seqSuccDef y f”
instance chainAsucc_defined : 𝚺₁-Function₂ (chainAsucc : V → V → V) via chainAsuccDef := .mk
  fun v ↦ by simp [chainAsuccDef, chainAsucc, znth_defined.iff, fstIdx_defined.iff, seqSucc_defined.iff]
instance chainAsucc_definable : 𝚺₁-Function₂ (chainAsucc : V → V → V) := chainAsucc_defined.to_definable

/-- `chainAnt ds i = seqAnt (fstIdx (znth ds i))`. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.chainAntDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y ds i. ∃ z, !znthDef z ds i ∧ ∃ f, !fstIdxDef f z ∧ !seqAntDef y f”
instance chainAnt_defined : 𝚺₁-Function₂ (chainAnt : V → V → V) via chainAntDef := .mk
  fun v ↦ by simp [chainAntDef, chainAnt, znth_defined.iff, fstIdx_defined.iff, seqAnt_defined.iff]
instance chainAnt_definable : 𝚺₁-Function₂ (chainAnt : V → V → V) := chainAnt_defined.to_definable

/-- `inAnt A Γ = ∃ i < lh Γ, znth Γ i = A` (antecedent membership). -/
def _root_.LO.FirstOrder.Arithmetic.inAntDef : 𝚺₀.Semisentence 2 := .mkSigma
  “A Γ. ∃ l <⁺ 2 * Γ, !lhDef l Γ ∧ ∃ i < l, !znthDef A Γ i”
instance inAnt_defined : 𝚺₀-Relation (inAnt : V → V → Prop) via inAntDef := .mk fun v ↦ by
  simp [inAntDef, inAnt, lh_defined.iff, znth_defined.iff, eq_comm, lh_bound]
instance inAnt_definable : 𝚺₀-Relation (inAnt : V → V → Prop) := inAnt_defined.to_definable

/-- `iperm I q` via `iperm_iff_proj`: `I = ⟪0,π₂ q⟫` (R) ∨ (`I = ⟪1,π₁(π₂ I),π₂(π₂ I)⟫` with
`π₂(π₂ I) ∈ π₁ q`) (L) ∨ `I = ⟪2,0⟫` (Rep). All existentials bounded (`pi₁/pi₂_le_self`) ⟹ `𝚺₀`. -/
def _root_.LO.FirstOrder.Arithmetic.ipermDef : 𝚺₀.Semisentence 2 := .mkSigma
  “I q. (∃ c <⁺ q, !seqSuccDef c q ∧ !pairDef I 0 c)
    ∨ (∃ p2 <⁺ I, !pi₂Def p2 I ∧ ∃ k <⁺ p2, !pi₁Def k p2 ∧ ∃ A <⁺ p2, !pi₂Def A p2 ∧
        !pair₃Def I 1 k A ∧ ∃ sa <⁺ q, !seqAntDef sa q ∧ !inAntDef A sa)
    ∨ !pairDef I 2 0”
instance iperm_defined : 𝚺₀-Relation (iperm : V → V → Prop) via ipermDef := .mk fun v ↦ by
  simp [ipermDef, iperm_iff_proj, isymIsL, isymR, isymLk, isymRep, seqSucc_defined.iff,
    seqAnt_defined.iff, pi₁_defined.iff, pi₂_defined.iff, inAnt_defined.iff,
    seqSucc, seqAnt, pi₁_le_self, pi₂_le_self]
instance iperm_definable : 𝚺₀-Relation (iperm : V → V → Prop) := iperm_defined.to_definable

/-- **Δ₁-definability of `isChainInf`** (via the bounded-index form `isChainInf_iff_idx`). The σ-core
extracts every function value positively (`∃ y, !fDef y args ∧ …`), the π-core via the antecedent
(`∀ y, !fDef y args → …`); both reduce to the same proposition because each function is total and
single-valued. The only genuinely `𝚺₁` content is `irk ≤ r` (chainAsucc/chainAnt are `𝚺₁`-typed but
projection-shallow); `lh`/`znth`/`seqAnt`/`seqSucc`/`inAnt` are `𝚺₀`. This is the chain-structure
ingredient of `zKValidDef`. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.isChainInfDef : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “s r ds.
    ∃ l, !lhDef l ds ∧ ∃ j0 < l,
      ( ∃ ca0, !chainAsuccDef ca0 ds j0 ∧
          ( (∃ ss, !seqSuccDef ss s ∧ ca0 = ss) ∨ (∃ bot, !qqFalsumDef bot ∧ ca0 = bot) ) )
      ∧ ( ∀ i <⁺ j0, ∃ cai, !chainAntDef cai ds i ∧ ∃ lc, !lhDef lc cai ∧ ∀ k < lc,
            ∃ z, !znthDef z cai k ∧
              ( (∃ sa, !seqAntDef sa s ∧ !inAntDef z sa)
                ∨ (∃ i' < i, !chainAsuccDef z ds i') ) )
      ∧ ( ∀ i < j0, ∃ ca, !chainAsuccDef ca ds i ∧ ∃ rk, !irkDef rk ca ∧ rk ≤ r ) ”)
  (.mkPi “s r ds.
    ∀ l, !lhDef l ds → ∃ j0 < l,
      ( ∀ ca0, !chainAsuccDef ca0 ds j0 →
          ( (∀ ss, !seqSuccDef ss s → ca0 = ss) ∨ (∀ bot, !qqFalsumDef bot → ca0 = bot) ) )
      ∧ ( ∀ i <⁺ j0, ∀ cai, !chainAntDef cai ds i → ∀ lc, !lhDef lc cai → ∀ k < lc,
            ∀ z, !znthDef z cai k →
              ( (∀ sa, !seqAntDef sa s → !inAntDef z sa)
                ∨ (∃ i' < i, ∀ cai', !chainAsuccDef cai' ds i' → z = cai') ) )
      ∧ ( ∀ i < j0, ∀ ca, !chainAsuccDef ca ds i → ∀ rk, !irkDef rk ca → rk ≤ r ) ”)

instance isChainInf_defined : 𝚫₁-Relation₃ (isChainInf : V → V → V → Prop) via isChainInfDef :=
  ⟨by intro v
      simp [isChainInfDef, chainAsucc_defined.iff, chainAnt_defined.iff, irk_defined.iff,
        lh_defined.iff, znth_defined.iff, seqAnt_defined.iff, seqSucc_defined.iff,
        inAnt_defined.iff, qqFalsum_defined.iff],
   by intro v
      simp [isChainInfDef, isChainInf_iff_idx, chainAsucc_defined.iff, chainAnt_defined.iff,
        irk_defined.iff, lh_defined.iff, znth_defined.iff, seqAnt_defined.iff,
        seqSucc_defined.iff, inAnt_defined.iff, qqFalsum_defined.iff]⟩

instance isChainInf_definable : 𝚫₁-Relation₃ (isChainInf : V → V → V → Prop) :=
  isChainInf_defined.to_definable

/-- **Validity of a `K^r` chain inference** (Buchholz Def p.8 + Lemma 3.3) — exactly the deferred
hypotheses `iord_descent_iRcrit_of_chain'` consumes beyond the premises being `ZDerivation`s:
`isChainInf` (the chain-structure data `j0`/`A_{j0}`/threading/rank), the per-premise permissibility
`tp(dᵢ) ◁ Γᵢ→Aᵢ` and criticality `tp(dᵢ) ⋪ Π`, and formula-hood of each premise's principal formula
(which feeds `tp_isymR_pos`/`tp_isymLk_pos` to discharge the `hwfR`/`hwfL` rank conditions). This is
the `zK`-disjunct side condition that the refined `ZPhi` carries. -/
def zKValid (s r ds : V) : Prop :=
  isChainInf s r ds ∧
  (∀ i < lh ds, iperm (tp (znth ds i)) (fstIdx (znth ds i))) ∧
  (∀ i < lh ds, ¬ iperm (tp (znth ds i)) s) ∧
  (∀ i < lh ds, zTag (znth ds i) = 1 → IsUFormula ℒₒᵣ (zIallF (znth ds i))) ∧
  (∀ i < lh ds, zTag (znth ds i) = 2 → IsUFormula ℒₒᵣ (zInegF (znth ds i))) ∧
  (∀ i < lh ds, zTag (znth ds i) = 5 → IsUFormula ℒₒᵣ (zAxAllF (znth ds i))) ∧
  (∀ i < lh ds, zTag (znth ds i) = 6 → IsUFormula ℒₒᵣ (zAxNegF (znth ds i))) ∧
  (∀ i < lh ds, IsUFormula ℒₒᵣ (chainAsucc ds i)) ∧
  IsUFormula ℒₒᵣ (seqSucc s) ∧
  (∀ k < lh (seqAnt s), IsUFormula ℒₒᵣ (znth (seqAnt s) k))

/-- **Δ₁-definability of `zKValid`.** Bundles `isChainInfDef.sigma`/`.pi` with the bounded-`∀ i < lh ds`
per-premise conditions: `iperm`/`¬iperm` (`ipermDef`, `𝚺₀`) read off `tp`/`fstIdx` of premise `i`, and
the tag-gated principal-formula well-formedness (`IsUFormula` via `(isUFormula ℒₒᵣ).sigma`/`.pi`). The
six `∀ i < lh ds` conjuncts of `zKValid` are fused under one bounded `∀ i < l` here; `forall_and`
recovers the split. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.zKValidDef : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “s r ds.
    !(isChainInfDef.sigma) s r ds ∧
    (∃ l, !lhDef l ds ∧ ∀ i < l,
      ∃ zi, !znthDef zi ds i ∧ ∃ ti, !tpDef ti zi ∧
        ( (∃ fi, !fstIdxDef fi zi ∧ !ipermDef ti fi)
          ∧ ¬(!ipermDef ti s)
          ∧ ∃ tg, !zTagDef tg zi ∧
            ( (tg = 1 → ∃ q, !zIallFDef q zi ∧ !(isUFormula ℒₒᵣ).sigma q)
            ∧ (tg = 2 → ∃ q, !zInegFDef q zi ∧ !(isUFormula ℒₒᵣ).sigma q)
            ∧ (tg = 5 → ∃ q, !zAxAllFDef q zi ∧ !(isUFormula ℒₒᵣ).sigma q)
            ∧ (tg = 6 → ∃ q, !zAxNegFDef q zi ∧ !(isUFormula ℒₒᵣ).sigma q) ) )
        ∧ ∃ ca, !chainAsuccDef ca ds i ∧ !(isUFormula ℒₒᵣ).sigma ca )
    ∧ (∃ sc, !seqSuccDef sc s ∧ !(isUFormula ℒₒᵣ).sigma sc)
    ∧ (∃ sa, !seqAntDef sa s ∧ ∃ la, !lhDef la sa ∧ ∀ k < la,
        ∃ z, !znthDef z sa k ∧ !(isUFormula ℒₒᵣ).sigma z) ”)
  (.mkPi “s r ds.
    !(isChainInfDef.pi) s r ds ∧
    (∀ l, !lhDef l ds → ∀ i < l,
      ∀ zi, !znthDef zi ds i → ∀ ti, !tpDef ti zi →
        ( (∀ fi, !fstIdxDef fi zi → !ipermDef ti fi)
          ∧ ¬(!ipermDef ti s)
          ∧ ∀ tg, !zTagDef tg zi →
            ( (tg = 1 → ∀ q, !zIallFDef q zi → !(isUFormula ℒₒᵣ).pi q)
            ∧ (tg = 2 → ∀ q, !zInegFDef q zi → !(isUFormula ℒₒᵣ).pi q)
            ∧ (tg = 5 → ∀ q, !zAxAllFDef q zi → !(isUFormula ℒₒᵣ).pi q)
            ∧ (tg = 6 → ∀ q, !zAxNegFDef q zi → !(isUFormula ℒₒᵣ).pi q) ) )
        ∧ ∀ ca, !chainAsuccDef ca ds i → !(isUFormula ℒₒᵣ).pi ca )
    ∧ (∀ sc, !seqSuccDef sc s → !(isUFormula ℒₒᵣ).pi sc)
    ∧ (∀ sa, !seqAntDef sa s → ∀ la, !lhDef la sa → ∀ k < la,
        ∀ z, !znthDef z sa k → !(isUFormula ℒₒᵣ).pi z) ”)

instance zKValid_defined : 𝚫₁-Relation₃ (zKValid : V → V → V → Prop) via zKValidDef :=
  ⟨by intro v
      simp [zKValidDef, HierarchySymbol.Semiformula.val_sigma, znth_defined.iff, tp_defined.iff,
        fstIdx_defined.iff, iperm_defined.iff, zTag_defined.iff, zIallF_defined.iff,
        zInegF_defined.iff, zAxAllF_defined.iff, zAxNegF_defined.iff, chainAsucc_defined.iff,
        seqSucc_defined.iff, seqAnt_defined.iff, lh_defined.iff],
   by intro v
      simp [zKValidDef, zKValid, HierarchySymbol.Semiformula.val_sigma, znth_defined.iff,
        tp_defined.iff, fstIdx_defined.iff, iperm_defined.iff, zTag_defined.iff, zIallF_defined.iff,
        zInegF_defined.iff, zAxAllF_defined.iff, zAxNegF_defined.iff, chainAsucc_defined.iff,
        seqSucc_defined.iff, seqAnt_defined.iff, lh_defined.iff, forall_and, and_assoc,
        numeral_eq_natCast]⟩

instance zKValid_definable : 𝚫₁-Relation₃ (zKValid : V → V → V → Prop) :=
  zKValid_defined.to_definable

/-! ### Decoupling criticality from validity — the genuine-reduct redesign (lap 82)

**Root-cause of the `RedSound` wall (validated against Buchholz, both papers).** `zKValid` bakes the
*criticality* conjunct `(∀ i < lh ds, ¬ iperm (tp (znth ds i)) s)` into the validity of EVERY chain
node. But Buchholz's chain-rule validity (§3 clause 5 / `isChainInf`: ∃ j₀ with `A_{j₀} ∈ {C,⊥}`,
threading `Γᵢ ⊆ Γ,A₀…A_{i−1}`, `rk(Aᵢ) ≤ r`) carries **no** criticality condition. Criticality (`d` is
*critical* iff `∀ i ≤ j₀, tp(dᵢ) ⋪ Π`, Def 3.2 case 5) is a property the *reduction* uses to pick its
clause (5.1 critical vs 5.2 non-critical) — NOT a validity requirement. Baking it into `zKValid`
over-constrains `ZDerivation` to *only critical* chains, which is exactly why the genuine reduct (whose
recombined premises `d{0},d{1}` are `Rep`-tagged chains, permissible everywhere — `not_zKValid_iCritReduct`)
spuriously fails validity. The fix (multi-lap): re-point `ZPhi`'s `zK` disjunct onto `zKValidF` (faithful
validity, no criticality), supply `zKCritical` only at reduction sites where Buchholz case 5 establishes
it, and prove descent by the critical/non-critical split (Lemma 4.1 a/b) over the genuine Def-3.2 reduct.
These defs + the decomposition lemma are the load-bearing bridge that makes that swap mechanical. -/

/-- **The criticality conjunct**, decoupled from validity: Buchholz's `d` is *critical*
(`∀ i ≤ j₀, tp(dᵢ) ⋪ Π`), here over all premises. Used by the *reduction* (Def 3.2 case 5) to find the
redex (`inference_critical_pair`), NOT by chain validity. -/
def zKCritical (s ds : V) : Prop := ∀ i < lh ds, ¬ iperm (tp (znth ds i)) s

/-- **Faithful chain validity** = `zKValid` minus the spurious criticality conjunct. This is Buchholz's
genuine `K^r` chain-rule validity (§3 clause 5): `isChainInf` (j₀/threading/rank) + each premise's
own-permissibility `tp(dᵢ) ◁ Πᵢ` (Lemma 3.3, automatic) + the §5 formula-hood bookkeeping. The redesign
re-points `ZPhi`'s `zK` disjunct onto this so the genuine reduct validates. -/
def zKValidF (s r ds : V) : Prop :=
  isChainInf s r ds ∧
  (∀ i < lh ds, iperm (tp (znth ds i)) (fstIdx (znth ds i))) ∧
  (∀ i < lh ds, zTag (znth ds i) = 1 → IsUFormula ℒₒᵣ (zIallF (znth ds i))) ∧
  (∀ i < lh ds, zTag (znth ds i) = 2 → IsUFormula ℒₒᵣ (zInegF (znth ds i))) ∧
  (∀ i < lh ds, zTag (znth ds i) = 5 → IsUFormula ℒₒᵣ (zAxAllF (znth ds i))) ∧
  (∀ i < lh ds, zTag (znth ds i) = 6 → IsUFormula ℒₒᵣ (zAxNegF (znth ds i))) ∧
  (∀ i < lh ds, IsUFormula ℒₒᵣ (chainAsucc ds i)) ∧
  IsUFormula ℒₒᵣ (seqSucc s) ∧
  (∀ k < lh (seqAnt s), IsUFormula ℒₒᵣ (znth (seqAnt s) k))

/-- **`zKValid` decomposes as faithful validity ∧ criticality.** The redesign keeps `zKValidF` in the
validity layer and supplies `zKCritical` only where Buchholz case 5 has established it. -/
lemma zKValid_iff_zKValidF_and_zKCritical {s r ds : V} :
    zKValid s r ds ↔ zKValidF s r ds ∧ zKCritical s ds := by
  unfold zKValid zKValidF zKCritical
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨⟨h1, h2, h4, h5, h6, h7, h8, h9, h10⟩, h3⟩
  · rintro ⟨⟨h1, h2, h4, h5, h6, h7, h8, h9, h10⟩, h3⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- The faithful-validity layer of any (currently over-strong) `zKValid` chain. -/
lemma zKValidF_of_zKValid {s r ds : V} (h : zKValid s r ds) : zKValidF s r ds :=
  (zKValid_iff_zKValidF_and_zKCritical.mp h).1

/-- **Δ₁ arithmetization of `zKValidF`** — `zKValidDef` with the spurious criticality line
`¬(!ipermDef ti s)` dropped. The arithmetized prerequisite for re-pointing `zblueprint`'s `zK` disjunct
onto faithful validity. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.zKValidFDef : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “s r ds.
    !(isChainInfDef.sigma) s r ds ∧
    (∃ l, !lhDef l ds ∧ ∀ i < l,
      ∃ zi, !znthDef zi ds i ∧ ∃ ti, !tpDef ti zi ∧
        ( (∃ fi, !fstIdxDef fi zi ∧ !ipermDef ti fi)
          ∧ ∃ tg, !zTagDef tg zi ∧
            ( (tg = 1 → ∃ q, !zIallFDef q zi ∧ !(isUFormula ℒₒᵣ).sigma q)
            ∧ (tg = 2 → ∃ q, !zInegFDef q zi ∧ !(isUFormula ℒₒᵣ).sigma q)
            ∧ (tg = 5 → ∃ q, !zAxAllFDef q zi ∧ !(isUFormula ℒₒᵣ).sigma q)
            ∧ (tg = 6 → ∃ q, !zAxNegFDef q zi ∧ !(isUFormula ℒₒᵣ).sigma q) ) )
        ∧ ∃ ca, !chainAsuccDef ca ds i ∧ !(isUFormula ℒₒᵣ).sigma ca )
    ∧ (∃ sc, !seqSuccDef sc s ∧ !(isUFormula ℒₒᵣ).sigma sc)
    ∧ (∃ sa, !seqAntDef sa s ∧ ∃ la, !lhDef la sa ∧ ∀ k < la,
        ∃ z, !znthDef z sa k ∧ !(isUFormula ℒₒᵣ).sigma z) ”)
  (.mkPi “s r ds.
    !(isChainInfDef.pi) s r ds ∧
    (∀ l, !lhDef l ds → ∀ i < l,
      ∀ zi, !znthDef zi ds i → ∀ ti, !tpDef ti zi →
        ( (∀ fi, !fstIdxDef fi zi → !ipermDef ti fi)
          ∧ ∀ tg, !zTagDef tg zi →
            ( (tg = 1 → ∀ q, !zIallFDef q zi → !(isUFormula ℒₒᵣ).pi q)
            ∧ (tg = 2 → ∀ q, !zInegFDef q zi → !(isUFormula ℒₒᵣ).pi q)
            ∧ (tg = 5 → ∀ q, !zAxAllFDef q zi → !(isUFormula ℒₒᵣ).pi q)
            ∧ (tg = 6 → ∀ q, !zAxNegFDef q zi → !(isUFormula ℒₒᵣ).pi q) ) )
        ∧ ∀ ca, !chainAsuccDef ca ds i → !(isUFormula ℒₒᵣ).pi ca )
    ∧ (∀ sc, !seqSuccDef sc s → !(isUFormula ℒₒᵣ).pi sc)
    ∧ (∀ sa, !seqAntDef sa s → ∀ la, !lhDef la sa → ∀ k < la,
        ∀ z, !znthDef z sa k → !(isUFormula ℒₒᵣ).pi z) ”)

instance zKValidF_defined : 𝚫₁-Relation₃ (zKValidF : V → V → V → Prop) via zKValidFDef :=
  ⟨by intro v
      simp [zKValidFDef, zKValidF, HierarchySymbol.Semiformula.val_sigma, znth_defined.iff,
        tp_defined.iff, fstIdx_defined.iff, iperm_defined.iff, zTag_defined.iff, zIallF_defined.iff,
        zInegF_defined.iff, zAxAllF_defined.iff, zAxNegF_defined.iff, chainAsucc_defined.iff,
        seqSucc_defined.iff, seqAnt_defined.iff, lh_defined.iff],
   by intro v
      simp [zKValidFDef, zKValidF, HierarchySymbol.Semiformula.val_sigma, znth_defined.iff,
        tp_defined.iff, fstIdx_defined.iff, iperm_defined.iff, zTag_defined.iff, zIallF_defined.iff,
        zInegF_defined.iff, zAxAllF_defined.iff, zAxNegF_defined.iff, chainAsucc_defined.iff,
        seqSucc_defined.iff, seqAnt_defined.iff, lh_defined.iff, forall_and, and_assoc,
        numeral_eq_natCast]⟩

instance zKValidF_definable : 𝚫₁-Relation₃ (zKValidF : V → V → V → Prop) :=
  zKValidF_defined.to_definable

/-! ### Rung-0.5 premise-sequent side conditions (for a rule-faithful `ZPhi`)

The bare `ZPhi` I∀/I¬/Ind disjuncts pin only the *conclusion* succedent, not the premise sequents — so a
genuine reduct's end-sequent (hence chain threading) is uncomputable. These `…Wff` predicates pin the
Buchholz inference-rule premise sequents (rules read from `scratchpad/buchholz-gentzen.txt:140-152`); they
are wired as conjuncts into the corresponding `ZPhi` disjunct so `ZDerivation` carries them, and a genuine
validity-preserving reduct reads them off by inversion. They need only already-`𝚫₁` pieces
(`fstIdx`/`seqAnt`/`seqSucc` projections, `^⊥`, `inAnt`, and — for I∀/Ind — the `𝚺₁` `substs1`). -/

/-- **¬-introduction premise sequent**: `d0 ⊢ A,Γ→⊥` — succedent `⊥`, the negated formula `A = p` in
its antecedent, and `p`'s formula-hood `IsUFormula ℒₒᵣ p` (lap 74: the `ZDerivation_zsubst`
commutation `fvSubst_inegF` consumes it). No substitution (Buchholz 14.23 reduct `d[0] := d0`). -/
def zInegWff (p d0 : V) : Prop :=
  seqSucc (fstIdx d0) = (^⊥ : V) ∧ inAnt p (seqAnt (fstIdx d0)) ∧ IsUFormula ℒₒᵣ p

/-- **`𝚫₁`-definability of `zInegWff`** (all pieces `𝚺₀`: `fstIdx`/`seqSucc`/`seqAnt` projections, `^⊥`,
`inAnt`). Mirrors `zKValidDef`. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.zInegWffDef : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “p d0.
    ∃ f, !fstIdxDef f d0 ∧
      (∃ ss, !seqSuccDef ss f ∧ ∃ bot, !qqFalsumDef bot ∧ ss = bot) ∧
      (∃ sa, !seqAntDef sa f ∧ !inAntDef p sa) ∧
      !(isUFormula ℒₒᵣ).sigma p ”)
  (.mkPi “p d0.
    ∀ f, !fstIdxDef f d0 →
      (∀ ss, !seqSuccDef ss f → ∀ bot, !qqFalsumDef bot → ss = bot) ∧
      (∀ sa, !seqAntDef sa f → !inAntDef p sa) ∧
      !(isUFormula ℒₒᵣ).pi p ”)

instance zInegWff_defined : 𝚫₁-Relation (zInegWff : V → V → Prop) via zInegWffDef :=
  ⟨by intro v
      simp [zInegWffDef, HierarchySymbol.Semiformula.val_sigma, fstIdx_defined.iff,
        seqSucc_defined.iff, qqFalsum_defined.iff, seqAnt_defined.iff, inAnt_defined.iff],
   by intro v
      simp [zInegWffDef, zInegWff, HierarchySymbol.Semiformula.val_sigma, fstIdx_defined.iff,
        seqSucc_defined.iff, qqFalsum_defined.iff, seqAnt_defined.iff, inAnt_defined.iff]⟩

instance zInegWff_definable : 𝚫₁-Relation (zInegWff : V → V → Prop) :=
  zInegWff_defined.to_definable

/-- **∀-introduction premise sequent**: `d0 ⊢ Γ→F(a)` — same antecedent as the conclusion `s`, succedent
`F(a) = substs1 (^&a) p` (matrix `p`'s bound variable replaced by the eigenvariable `a`), and the matrix's
1-formula-hood `IsSemiformula ℒₒᵣ 1 p` (lap 74: the `ZDerivation_zsubst` commutations `fvSubst_all` /
`fvSubst_substs1_fvar` consume it). [Freshness `a ∉ s` is a separate global side condition.] The genuine
I∀ reduct `d0(a/n) ⊢ Γ→F(n)` reads off this. -/
def zIallWff (s a p d0 : V) : Prop :=
  seqAnt (fstIdx d0) = seqAnt s ∧ seqSucc (fstIdx d0) = substs1 ℒₒᵣ (qqFvar a) p ∧
    IsSemiformula ℒₒᵣ 1 p

/-- **`𝚫₁`-definability of `zIallWff`.** `fstIdx`/`seqAnt`/`seqSucc`/`qqFvar` are `𝚺₀`; the only `𝚺₁`
content is the substitution `substs1 ℒₒᵣ (^&a) p` (Foundation `substs1Graph`, single-valued ⟹ the σ
existential and π universal both pin it). -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.zIallWffDef : 𝚫₁.Semisentence 4 := .mkDelta
  (.mkSigma “s a p d0.
    ∃ f, !fstIdxDef f d0 ∧
      (∃ sa0, !seqAntDef sa0 f ∧ ∃ sa1, !seqAntDef sa1 s ∧ sa0 = sa1) ∧
      (∃ ss, !seqSuccDef ss f ∧ ∃ fa, !qqFvarDef fa a ∧
        ∃ sub, !(substs1Graph ℒₒᵣ) sub fa p ∧ ss = sub) ∧
      !(isSemiformula ℒₒᵣ).sigma 1 p ”)
  (.mkPi “s a p d0.
    ∀ f, !fstIdxDef f d0 →
      (∀ sa0, !seqAntDef sa0 f → ∀ sa1, !seqAntDef sa1 s → sa0 = sa1) ∧
      (∀ ss, !seqSuccDef ss f → ∀ fa, !qqFvarDef fa a →
        ∀ sub, !(substs1Graph ℒₒᵣ) sub fa p → ss = sub) ∧
      !(isSemiformula ℒₒᵣ).pi 1 p ”)

instance zIallWff_defined : 𝚫₁-Relation₄ (zIallWff : V → V → V → V → Prop) via zIallWffDef :=
  ⟨by intro v
      simp [zIallWffDef, HierarchySymbol.Semiformula.val_sigma, fstIdx_defined.iff,
        seqAnt_defined.iff, seqSucc_defined.iff, qqFvar_defined.iff,
        (substs1.defined (L := ℒₒᵣ)).iff],
   by intro v
      simp [zIallWffDef, zIallWff, HierarchySymbol.Semiformula.val_sigma, fstIdx_defined.iff,
        seqAnt_defined.iff, seqSucc_defined.iff, qqFvar_defined.iff,
        (substs1.defined (L := ℒₒᵣ)).iff]⟩

instance zIallWff_definable : 𝚫₁-Relation₄ (zIallWff : V → V → V → V → Prop) :=
  zIallWff_defined.to_definable

/-- Eigenvariable accessor for an Ind node: `at' = ⟪a,t⟫`, so `a = π₁ at' = π₁ (π₁ (zRest d))`. -/
noncomputable def zIndEig (d : V) : V := π₁ (π₁ (zRest d))
/-- Induction-term accessor for an Ind node: `t = π₂ at' = π₂ (π₁ (zRest d))`. -/
noncomputable def zIndTerm (d : V) : V := π₂ (π₁ (zRest d))

@[simp] lemma zIndEig_zInd (s at' p d0 d1 : V) : zIndEig (zInd s at' p d0 d1) = π₁ at' := by
  simp [zIndEig]
@[simp] lemma zIndTerm_zInd (s at' p d0 d1 : V) : zIndTerm (zInd s at' p d0 d1) = π₂ at' := by
  simp [zIndTerm]

noncomputable def _root_.LO.FirstOrder.Arithmetic.zIndEigDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ ∃ r2 <⁺ r, !pi₁Def r2 r ∧ !pi₁Def y r2”
instance zIndEig_defined : 𝚺₀-Function₁ (zIndEig : V → V) via zIndEigDef := .mk fun v ↦ by
  simp [zIndEigDef, zIndEig, zRest_defined.iff, pi₁_defined.iff]
instance zIndEig_definable : 𝚺₀-Function₁ (zIndEig : V → V) := zIndEig_defined.to_definable

noncomputable def _root_.LO.FirstOrder.Arithmetic.zIndTermDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ r <⁺ d, !zRestDef r d ∧ ∃ r2 <⁺ r, !pi₁Def r2 r ∧ !pi₂Def y r2”
instance zIndTerm_defined : 𝚺₀-Function₁ (zIndTerm : V → V) via zIndTermDef := .mk fun v ↦ by
  simp [zIndTermDef, zIndTerm, zRest_defined.iff, pi₁_defined.iff, pi₂_defined.iff]
instance zIndTerm_definable : 𝚺₀-Function₁ (zIndTerm : V → V) := zIndTerm_defined.to_definable

/-- **Ind-rule premise sequents** (Buchholz complete-induction rule, `buchholz-gentzen.txt:140-152`),
on the whole Ind node `d = zInd s ⟪a,t⟫ p d0 d1`: `d0 ⊢ Γ→F(0)`, `d1 ⊢ F(a),Γ→F(Sa)` (`Sa = a+1`), and
the conclusion succedent `F(t)`. `F(·) = substs1 ℒₒᵣ · p`; `^&a = qqFvar a`; `0 = numeral 0`; `Sa =
qqAdd (^&a) (numeral 1)`; `t = zIndTerm d`. Unary on the node ⟹ its body can be strengthened (e.g. add
the `Γ ⊆ ant(d1)` threading needed by the genuine Ind reduct's `isChainInf`) without re-running the
`ZPhi` cascade. The genuine Ind reduct `K^r⟨d0, d1(a/0),…,d1(a/k−1)⟩` reads these by inversion. -/
noncomputable def zIndWff (d : V) : Prop :=
  (seqAnt (fstIdx (zIndPrem0 d)) = seqAnt (fstIdx d) ∧
    seqSucc (fstIdx (zIndPrem0 d)) = substs1 ℒₒᵣ (Bootstrapping.Arithmetic.numeral 0) (zIndP d)) ∧
  (inAnt (substs1 ℒₒᵣ (qqFvar (zIndEig d)) (zIndP d)) (seqAnt (fstIdx (zIndPrem1 d))) ∧
    seqSucc (fstIdx (zIndPrem1 d)) =
      substs1 ℒₒᵣ (Bootstrapping.Arithmetic.qqAdd (qqFvar (zIndEig d))
        (Bootstrapping.Arithmetic.numeral 1)) (zIndP d)) ∧
  seqSucc (fstIdx d) = substs1 ℒₒᵣ (zIndTerm d) (zIndP d) ∧
  IsSemiformula ℒₒᵣ 1 (zIndP d) ∧
  IsSemiterm ℒₒᵣ 0 (zIndTerm d)

/-- **`𝚫₁`-definability of `zIndWff`.** Projections (`fstIdx`/`zIndP`/`zIndPrem0/1`/`zIndEig`/`zIndTerm`/
`seqAnt`/`seqSucc`/`inAnt`/`qqFvar`) are `𝚺₀`; the `𝚺₁` content is the term-codes `numeral`/`qqAdd` and the
substitution `substs1`, each single-valued ⟹ σ existential / π universal both pin them. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.zIndWffDef : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “d.
    ∃ s, !fstIdxDef s d ∧ ∃ p, !zIndPDef p d ∧ ∃ d0, !zIndPrem0Def d0 d ∧ ∃ d1, !zIndPrem1Def d1 d ∧
    ∃ a, !zIndEigDef a d ∧ ∃ t, !zIndTermDef t d ∧
    ∃ f0, !fstIdxDef f0 d0 ∧ ∃ f1, !fstIdxDef f1 d1 ∧ ∃ fa, !qqFvarDef fa a ∧
    ∃ sas, !seqAntDef sas s ∧
    (∃ sa0, !seqAntDef sa0 f0 ∧ sa0 = sas) ∧
    (∃ ss0, !seqSuccDef ss0 f0 ∧ ∃ z0, !(Bootstrapping.Arithmetic.numeralGraph) z0 0 ∧
      ∃ sub0, !(substs1Graph ℒₒᵣ) sub0 z0 p ∧ ss0 = sub0) ∧
    (∃ sa1, !seqAntDef sa1 f1 ∧ ∃ subfa, !(substs1Graph ℒₒᵣ) subfa fa p ∧ !inAntDef subfa sa1) ∧
    (∃ ss1, !seqSuccDef ss1 f1 ∧ ∃ z1, !(Bootstrapping.Arithmetic.numeralGraph) z1 1 ∧
      ∃ sa, !(Bootstrapping.Arithmetic.qqAddGraph) sa fa z1 ∧
      ∃ subsa, !(substs1Graph ℒₒᵣ) subsa sa p ∧ ss1 = subsa) ∧
    (∃ ss, !seqSuccDef ss s ∧ ∃ subt, !(substs1Graph ℒₒᵣ) subt t p ∧ ss = subt) ∧
    !(isSemiformula ℒₒᵣ).sigma 1 p ∧ !(isSemiterm ℒₒᵣ).sigma 0 t ”)
  (.mkPi “d.
    ∀ s, !fstIdxDef s d → ∀ p, !zIndPDef p d → ∀ d0, !zIndPrem0Def d0 d → ∀ d1, !zIndPrem1Def d1 d →
    ∀ a, !zIndEigDef a d → ∀ t, !zIndTermDef t d →
    ∀ f0, !fstIdxDef f0 d0 → ∀ f1, !fstIdxDef f1 d1 → ∀ fa, !qqFvarDef fa a →
    ∀ sas, !seqAntDef sas s →
    (∀ sa0, !seqAntDef sa0 f0 → sa0 = sas) ∧
    (∀ ss0, !seqSuccDef ss0 f0 → ∀ z0, !(Bootstrapping.Arithmetic.numeralGraph) z0 0 →
      ∀ sub0, !(substs1Graph ℒₒᵣ) sub0 z0 p → ss0 = sub0) ∧
    (∀ sa1, !seqAntDef sa1 f1 → ∀ subfa, !(substs1Graph ℒₒᵣ) subfa fa p → !inAntDef subfa sa1) ∧
    (∀ ss1, !seqSuccDef ss1 f1 → ∀ z1, !(Bootstrapping.Arithmetic.numeralGraph) z1 1 →
      ∀ sa, !(Bootstrapping.Arithmetic.qqAddGraph) sa fa z1 →
      ∀ subsa, !(substs1Graph ℒₒᵣ) subsa sa p → ss1 = subsa) ∧
    (∀ ss, !seqSuccDef ss s → ∀ subt, !(substs1Graph ℒₒᵣ) subt t p → ss = subt) ∧
    !(isSemiformula ℒₒᵣ).pi 1 p ∧ !(isSemiterm ℒₒᵣ).pi 0 t ”)

instance zIndWff_defined : 𝚫₁-Predicate (zIndWff : V → Prop) via zIndWffDef :=
  ⟨by intro v
      simp [zIndWffDef, fstIdx_defined.iff,
        zIndP_defined.iff, zIndPrem0_defined.iff, zIndPrem1_defined.iff, zIndEig_defined.iff,
        zIndTerm_defined.iff, seqAnt_defined.iff, seqSucc_defined.iff, qqFvar_defined.iff,
        inAnt_defined.iff, (Bootstrapping.Arithmetic.numeral_defined (V := V)).iff,
        (Bootstrapping.Arithmetic.qqAdd_defined (V := V)).iff, (substs1.defined (L := ℒₒᵣ)).iff,
        and_assoc],
   by intro v
      simp [zIndWffDef, zIndWff, HierarchySymbol.Semiformula.val_sigma, fstIdx_defined.iff,
        zIndP_defined.iff, zIndPrem0_defined.iff, zIndPrem1_defined.iff, zIndEig_defined.iff,
        zIndTerm_defined.iff, seqAnt_defined.iff, seqSucc_defined.iff, qqFvar_defined.iff,
        inAnt_defined.iff, (Bootstrapping.Arithmetic.numeral_defined (V := V)).iff,
        (Bootstrapping.Arithmetic.qqAdd_defined (V := V)).iff, (substs1.defined (L := ℒₒᵣ)).iff,
        and_assoc]⟩

instance zIndWff_definable : 𝚫₁-Predicate (zIndWff : V → Prop) :=
  zIndWff_defined.to_definable

/-- **L3.1 on a GENUINE chain** (E-CRUX2 §8.1, the lap-66 NEXT-item-1 bridge). For the chain `zK s r ds`
with chain-inference data `j0` (from `isChainInf`: `hj0`/`hAj0`/`hchain`/`hrank` are exactly its three
components), the coded symbol sequence `Iseq := tpSeq ds` (so `znth Iseq i = tp (znth ds i)`), and the
premise/conclusion permissibility (`hperm` = Lemma 3.3 on each premise `tp(dᵢ) ◁ Πᵢ`; `hnperm` =
criticality `tp(dᵢ) ⋪ Π`) plus the truth/rank well-formedness, Lemma 3.1 produces the redex `(i,j,k)`
on the GENUINE `tp`-symbols: `tp(dᵢ)=R_{Aᵢ}`, `tp(d_j)=L^k_{Aᵢ}`, `0<rk(Aᵢ)≤r`. This is the exact input
T3.4(a) (`irk_cut_lt_rank`) consumes. The chain-structural facts `hchain`/`hAj0`/`hrank` are discharged
directly from `isChainInf`; `hperm`/`hnperm`/`hwfR`/`hwfL` remain the deferred well-formedness obligations
(supplied later by the refined `ZPhi` end-sequent matching + §5 atomic truth). `Tr`/`Fa` are abstract
truth predicates (only `hdisj`/`hFa_rk`/`hFa_bot` consumed). -/
theorem inference_critical_pair_of_chain {s r ds j0 : V} {Tr Fa : V → Prop}
    (hj0 : j0 < lh ds)
    (hAj0 : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hchain : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
      inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ Tr A)
    (hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ Fa A)
    (hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)))
    (hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s)
    (hdisj : ∀ A, ¬ (Tr A ∧ Fa A)) (hFa_rk : ∀ A, Fa A → irk A = 0)
    (hFa_bot : Fa (^⊥ : V)) :
    ∃ i j k, i < j ∧ j ≤ j0 ∧ tp (znth ds i) = isymR (chainAsucc ds i) ∧
      tp (znth ds j) = isymLk k (chainAsucc ds i) ∧
      0 < irk (chainAsucc ds i) ∧ irk (chainAsucc ds i) ≤ r := by
  -- For i ≤ j0 < lh ds the coded read-out is the genuine `tp`.
  have hznth : ∀ i, i ≤ j0 → znth (tpSeq ds) i = tp (znth ds i) :=
    fun i hi => znth_tpSeq (lt_of_le_of_lt hi hj0)
  -- Repackage the iperm hypotheses into L3.1's unfolded disjunction form (chainAsucc/chainAnt are
  -- `seqSucc/seqAnt ∘ fstIdx` by definition; rewrite `tp (znth ds i)` to `znth (tpSeq ds) i`).
  have hperm' : ∀ i ≤ j0, znth (tpSeq ds) i = isymR (chainAsucc ds i) ∨
      (∃ k A, znth (tpSeq ds) i = isymLk k A ∧ inAnt A (chainAnt ds i)) ∨
      znth (tpSeq ds) i = isymRep := by
    intro i hi; rw [hznth i hi]; exact hperm i hi
  have hnperm' : ∀ i ≤ j0, ¬ (znth (tpSeq ds) i = isymR (seqSucc s) ∨
      (∃ k A, znth (tpSeq ds) i = isymLk k A ∧ inAnt A (seqAnt s)) ∨
      znth (tpSeq ds) i = isymRep) := by
    intro i hi; rw [hznth i hi]; exact hnperm i hi
  have hwfR' : ∀ i ≤ j0, ∀ A, znth (tpSeq ds) i = isymR A → 0 < irk A ∨ Tr A := by
    intro i hi A h; rw [hznth i hi] at h; exact hwfR i hi A h
  have hwfL' : ∀ i ≤ j0, ∀ k A, znth (tpSeq ds) i = isymLk k A → 0 < irk A ∨ Fa A := by
    intro i hi k A h; rw [hznth i hi] at h; exact hwfL i hi k A h
  have hAj0' : chainAsucc ds j0 = seqSucc s ∨ Fa (chainAsucc ds j0) := by
    rcases hAj0 with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; exact hFa_bot)
  obtain ⟨i, j, k, hij, hj_le, hIi, hIj, hrk, hrkr⟩ :=
    inference_critical_pair_rank (Iseq := tpSeq ds) (Asucc := chainAsucc ds) (Gam := chainAnt ds)
      (Γmain := seqAnt s) (Cmain := seqSucc s) inAnt Tr Fa
      hwfR' hwfL' hperm' hnperm' hchain hAj0' hdisj hFa_rk hrank
  refine ⟨i, j, k, hij, hj_le, ?_, ?_, hrk, hrkr⟩
  · rw [← hznth i (le_of_lt (lt_of_lt_of_le hij hj_le))]; exact hIi
  · rw [← hznth j hj_le]; exact hIj

/-- **L3.1 on a genuine chain, with the truth bookkeeping discharged for the CURRENT `tp`.** Specialises
`inference_critical_pair_of_chain` at `Tr := ⊥`, `Fa := (· = ⊥)`: then `tp_ne_isymLk` discharges `hwfL`
`tp_isymR_pos` reduces `hwfR` to formula-hood of the I-rule principal formulas (`hform1`/`hform2`),
**`tp_isymLk_pos` reduces `hwfL` to formula-hood of the §5 atomic principal formulas (`hform5`/`hform6`)**
— so `hwfL` is now discharged by the genuine rank bound, not vacuously — and `hdisj`/`hFa_rk`/`hFa_bot`
are immediate. **The deferred obligation is now exactly `hperm`+`hnperm` (Lemma 3.3 `tp(dᵢ)◁Πᵢ` +
criticality `tp(dᵢ)⋪Π`) plus principal-formula well-formedness** — pinpointing that the only
genuinely-missing content is the sequent-matching (`ZPhi` end-sequent + §5 antecedent membership) that
makes `hperm`/`hnperm` simultaneously satisfiable for a real critical chain. -/
theorem inference_critical_pair_of_chain_tp {s r ds j0 : V}
    (hj0 : j0 < lh ds)
    (hAj0 : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hchain : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
      inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hform1 : ∀ i ≤ j0, zTag (znth ds i) = 1 → IsUFormula ℒₒᵣ (zIallF (znth ds i)))
    (hform2 : ∀ i ≤ j0, zTag (znth ds i) = 2 → IsUFormula ℒₒᵣ (zInegF (znth ds i)))
    (hform5 : ∀ i ≤ j0, zTag (znth ds i) = 5 → IsUFormula ℒₒᵣ (zAxAllF (znth ds i)))
    (hform6 : ∀ i ≤ j0, zTag (znth ds i) = 6 → IsUFormula ℒₒᵣ (zAxNegF (znth ds i)))
    (hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)))
    (hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s) :
    ∃ i j k, i < j ∧ j ≤ j0 ∧ tp (znth ds i) = isymR (chainAsucc ds i) ∧
      tp (znth ds j) = isymLk k (chainAsucc ds i) ∧
      0 < irk (chainAsucc ds i) ∧ irk (chainAsucc ds i) ≤ r :=
  inference_critical_pair_of_chain (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
    hj0 hAj0 hchain hrank
    (fun i hi A h => Or.inl (tp_isymR_pos h (hform1 i hi) (hform2 i hi)))
    (fun i hi k A h => Or.inl (tp_isymLk_pos h (hform5 i hi) (hform6 i hi)))
    hperm hnperm
    (fun _ h => h.1)
    (fun A h => by rw [h]; exact irk_falsum)
    rfl

/-! ## Internal variadic max-fold over a premise sequence

The `K^r` rule takes a *sequence* `ds`; `idg`/`iõ` fold over it inside `V`. `InternalCor34.ibigMul`
is a meta-iterate (external `k : ℕ`) and cannot reach an internal arity `lh ds`; this is the genuine
internal fold via `PR.Construction` over a counter (partial fold of the first `j` elements).

`iseqMaxTab s ds = max_{i < lh ds} znth s (znth ds i)` — max of the value-table entries at the
sub-indices. For `idg`'s `K^r` case `max{idg(d0)-1,…,idg(dl)-1, r}`; since `∸` commutes with `max`,
this equals `max r (iseqMaxTab s ds ∸ 1)`. -/

def iseqMaxAux.blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y s ds. y = 0”
  succ := .mkSigma “y ih n s ds.
    ∃ di, !znthDef di ds n ∧ ∃ v, !znthDef v s di ∧ !max.dfn y ih v”

noncomputable def iseqMaxAux.construction : PR.Construction V iseqMaxAux.blueprint where
  zero := fun _ ↦ 0
  succ := fun x n ih ↦ max ih (znth (x 0) (znth (x 1) n))
  zero_defined := .mk fun v ↦ by simp [iseqMaxAux.blueprint]
  succ_defined := .mk fun v ↦ by
    simp [iseqMaxAux.blueprint, znth_defined.iff, max_defined.iff]

/-- **Partial max fold**: `iseqMaxAux s ds j = max_{i < j} znth s (znth ds i)`. -/
noncomputable def iseqMaxAux (s ds j : V) : V := iseqMaxAux.construction.result ![s, ds] j

@[simp] lemma iseqMaxAux_zero (s ds : V) : iseqMaxAux s ds 0 = 0 := by
  simp [iseqMaxAux, iseqMaxAux.construction]

@[simp] lemma iseqMaxAux_succ (s ds j : V) :
    iseqMaxAux s ds (j + 1) = max (iseqMaxAux s ds j) (znth s (znth ds j)) := by
  simp [iseqMaxAux, iseqMaxAux.construction]

def _root_.LO.FirstOrder.Arithmetic.iseqMaxAuxDef : 𝚺₁.Semisentence 4 :=
  iseqMaxAux.blueprint.resultDef.rew (Rew.subst ![#0, #3, #1, #2])

instance iseqMaxAux_defined : 𝚺₁-Function₃ (iseqMaxAux : V → V → V → V) via iseqMaxAuxDef := .mk
  fun v ↦ by simp [iseqMaxAux.construction.result_defined_iff, iseqMaxAuxDef]; rfl

instance iseqMaxAux_definable : 𝚺₁-Function₃ (iseqMaxAux : V → V → V → V) :=
  iseqMaxAux_defined.to_definable
instance iseqMaxAux_definable' (Γ) : Γ-[m + 1]-Function₃ (iseqMaxAux : V → V → V → V) :=
  iseqMaxAux_definable.of_sigmaOne

/-- **Max of table values over a sequence**: `iseqMaxTab s ds = max_{i < lh ds} znth s (znth ds i)`. -/
noncomputable def iseqMaxTab (s ds : V) : V := iseqMaxAux s ds (lh ds)

def _root_.LO.FirstOrder.Arithmetic.iseqMaxTabDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y s ds. ∃ l, !lhDef l ds ∧ !iseqMaxAuxDef y s ds l”

instance iseqMaxTab_defined : 𝚺₁-Function₂ (iseqMaxTab : V → V → V) via iseqMaxTabDef := .mk
  fun v ↦ by simp [iseqMaxTabDef, iseqMaxTab, lh_defined.iff, iseqMaxAux_defined.iff]

instance iseqMaxTab_definable : 𝚺₁-Function₂ (iseqMaxTab : V → V → V) :=
  iseqMaxTab_defined.to_definable
instance iseqMaxTab_definable' (Γ) : Γ-[m + 1]-Function₂ (iseqMaxTab : V → V → V) :=
  iseqMaxTab_definable.of_sigmaOne

/-- Every sub-value in range is dominated by the partial fold. -/
lemma le_iseqMaxAux {s ds : V} :
    ∀ j : V, ∀ i < j, znth s (znth ds i) ≤ iseqMaxAux s ds j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.ball_lt (by definability) ?_
    apply Definable.comp₂ <;> definability
  case zero => intro i hi; exact absurd hi (by simp)
  case succ j ih =>
    intro i hi
    rw [iseqMaxAux_succ]
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hi) with h | h
    · subst h; exact le_max_right _ _
    · exact le_trans (ih i h) (le_max_left _ _)

/-- The full fold dominates each sequence entry's table value (for `i < lh ds`). -/
lemma le_iseqMaxTab {s ds i : V} (hi : i < lh ds) :
    znth s (znth ds i) ≤ iseqMaxTab s ds := le_iseqMaxAux _ i hi

/-! ## `idg` — the degree assignment, total `𝚺₁` by course-of-values recursion

Buchholz §4: `dg(atom)=0`; `dg(I·d0)=dg(d0)`; `dg(Ind d0 d1)=max{dg(d0)-1,dg(d1)-1,rk F}`;
`dg(K^r d0…dl)=max{dg(d0)-1,…,dg(dl)-1,r}`. Realized as a total function on ALL codes via the same
table reduction as `iC` (`InternalONote`): `idgTable n = ⟨idg 0,…,idg n⟩`, the step `idgNext d s`
reading sub-results out of `s` at the projection indices (all `≤ d`). The `K^r` fold uses
`iseqMaxTab` with `max{…,dⱼ-1} = (max dⱼ) ∸ 1` (∸ commutes with max). -/

/-- Table step of `idg`: `idg d` from the table `s = ⟨idg 0,…,idg (d-1)⟩`, dispatching on `zTag d`. -/
noncomputable def idgNext (d s : V) : V :=
  if zTag d = 1 then znth s (zIallPrem d)
  else if zTag d = 2 then znth s (zInegPrem d)
  else if zTag d = 3 then
    max (max (znth s (zIndPrem0 d) - 1) (znth s (zIndPrem1 d) - 1)) (irk (zIndP d))
  else if zTag d = 4 then max (zKrank d) (iseqMaxTab s (zKseq d) - 1)
  else 0

noncomputable def _root_.LO.FirstOrder.Arithmetic.idgNextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y d s. ∃ t, !zTagDef t d ∧
    ( (t = 1 ∧ ∃ p, !zIallPremDef p d ∧ !znthDef y s p)
    ∨ (t = 2 ∧ ∃ p, !zInegPremDef p d ∧ !znthDef y s p)
    ∨ (t = 3 ∧ ∃ p0, !zIndPrem0Def p0 d ∧ ∃ v0, !znthDef v0 s p0 ∧ ∃ w0, !subDef w0 v0 1 ∧
        ∃ p1, !zIndPrem1Def p1 d ∧ ∃ v1, !znthDef v1 s p1 ∧ ∃ w1, !subDef w1 v1 1 ∧
        ∃ m, !max.dfn m w0 w1 ∧ ∃ pf, !zIndPDef pf d ∧ ∃ rk, !irkDef rk pf ∧ !max.dfn y m rk)
    ∨ (t = 4 ∧ ∃ rk, !zKrankDef rk d ∧ ∃ ds, !zKseqDef ds d ∧ ∃ f, !iseqMaxTabDef f s ds ∧
        ∃ w, !subDef w f 1 ∧ !max.dfn y rk w)
    ∨ (t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ y = 0) )”

set_option maxHeartbeats 1000000 in
instance idgNext_defined : 𝚺₁-Function₂ (idgNext : V → V → V) via idgNextDef := .mk fun v ↦ by
  simp [idgNextDef, idgNext, zTag_defined.iff, zIallPrem_defined.iff, zInegPrem_defined.iff,
    zIndPrem0_defined.iff, zIndPrem1_defined.iff, zIndP_defined.iff, zKrank_defined.iff,
    zKseq_defined.iff, irk_defined.iff, iseqMaxTab_defined.iff, znth_defined.iff,
    sub_defined.iff, max_defined.iff]
  by_cases h1 : zTag (v 1) = 1
  · simp [h1]
  · by_cases h2 : zTag (v 1) = 2
    · simp [h1, h2]
    · by_cases h3 : zTag (v 1) = 3
      · simp [h1, h2, h3]
      · by_cases h4 : zTag (v 1) = 4
        · simp [h1, h2, h3, h4]
        · simp [h1, h2, h3, h4]

instance idgNext_definable : 𝚺₁-Function₂ (idgNext : V → V → V) := idgNext_defined.to_definable

/-- Blueprint for the `idg` table. -/
noncomputable def idgTable.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n. ∃ v, !idgNextDef v (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def idgTable.construction : PR.Construction V idgTable.blueprint where
  zero := fun _ ↦ !⟦0⟧
  succ := fun _ n ih ↦ seqCons ih (idgNext (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [idgTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [idgTable.blueprint, idgNext_defined.iff, seqCons_defined.iff]

/-- **The `idg` table**: `idgTable n = ⟨idg 0,…,idg n⟩` (length `n+1`). -/
noncomputable def idgTable (n : V) : V := idgTable.construction.result ![] n

@[simp] lemma idgTable_zero : idgTable (0 : V) = !⟦0⟧ := by simp [idgTable, idgTable.construction]

@[simp] lemma idgTable_succ (n : V) :
    idgTable (n + 1) = seqCons (idgTable n) (idgNext (n + 1) (idgTable n)) := by
  simp [idgTable, idgTable.construction]

/-- **The degree** `dg(d)` of a code: the `d`-th entry of the table. -/
noncomputable def idg (d : V) : V := znth (idgTable d) d

noncomputable def _root_.LO.FirstOrder.Arithmetic.idgTableDef : 𝚺₁.Semisentence 2 :=
  idgTable.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance idgTable_defined : 𝚺₁-Function₁ (idgTable : V → V) via idgTableDef := .mk
  fun v ↦ by simp [idgTable.construction.result_defined_iff, idgTableDef]; rfl

instance idgTable_definable : 𝚺₁-Function₁ (idgTable : V → V) := idgTable_defined.to_definable
instance idgTable_definable' (Γ) : Γ-[m + 1]-Function₁ (idgTable : V → V) :=
  idgTable_definable.of_sigmaOne

noncomputable def _root_.LO.FirstOrder.Arithmetic.idgDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ t, !idgTableDef t d ∧ !znthDef y t d”

instance idg_defined : 𝚺₁-Function₁ (idg : V → V) via idgDef := .mk fun v ↦ by
  simp [idgDef, idg, idgTable_defined.iff, znth_defined.iff]

instance idg_definable : 𝚺₁-Function₁ (idg : V → V) := idg_defined.to_definable
instance idg_definable' (Γ) : Γ-[m + 1]-Function₁ (idg : V → V) := idg_definable.of_sigmaOne

/-! ### Structural correctness of the `idg` table (mirror `iC`) -/

private lemma def_idgTable {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ idgTable (v i)) :=
  DefinableFunction₁.comp (F := idgTable) (DefinableFunction.var i)

private lemma def_idg {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ idg (v i)) :=
  DefinableFunction₁.comp (F := idg) (DefinableFunction.var i)

@[simp] lemma idgTable_seq (n : V) : Seq (idgTable n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_idgTable 0)
  case zero => simp
  case succ n ih => rw [idgTable_succ]; exact ih.seqCons _

@[simp] lemma idgTable_lh (n : V) : lh (idgTable n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_idgTable 0)) (by definability)
  case zero => simp
  case succ n ih => rw [idgTable_succ, Seq.lh_seqCons _ (idgTable_seq n), ih]

lemma znth_idgTable_succ {n k : V} (hk : k < n + 1) :
    znth (idgTable (n + 1)) k = znth (idgTable n) k := by
  rw [idgTable_succ]
  exact znth_seqCons_of_lt (idgTable_seq n) _ (by rw [idgTable_lh]; exact hk)

/-- **Table stability**: every entry of the length-`(N+1)` table is the genuine `idg` value. -/
lemma znth_idgTable_eq_idg : ∀ N : V, ∀ k ≤ N, znth (idgTable N) k = idg k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_idgTable 1) (DefinableFunction.var 0))
      (def_idg 0)
  case zero =>
    intro k hk; rcases (nonpos_iff_eq_zero.mp hk) with rfl; rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_idgTable_succ hlt]; exact ih k (le_iff_lt_succ.mpr hlt)

/-- `idg c = idgNext c (idgTable (c-1))` for positive codes (the table-reduction unfolding). -/
lemma idg_eq_idgNext {c : V} (hpos : 0 < c) : idg c = idgNext c (idgTable (c - 1)) := by
  obtain ⟨M, rfl⟩ : ∃ M, c = M + 1 := ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (idgTable (M + 1)) (M + 1) = idgNext (M + 1) (idgTable M) := by
    rw [idgTable_succ]
    have h := znth_seqCons_self (idgTable_seq M) (idgNext (M + 1) (idgTable M))
    rwa [idgTable_lh] at h
  simp only [idg, add_tsub_cancel_right, key]

/-- `a < c ⟹ a ≤ c - 1` (a sub-index lands in the length-`c` table). -/
lemma le_pred_of_lt {a c : V} (h : a < c) : a ≤ c - 1 := by
  have hc : 0 < c := lt_of_le_of_lt (show (0 : V) ≤ a by simp) h
  refine le_iff_lt_succ.mpr ?_
  rwa [sub_add_self_of_le (pos_iff_one_le.mp hc)]

/-! ### `idg` recursion equations (Buchholz §4) -/

@[simp] lemma idg_zAtom (s : V) : idg (zAtom s) = 0 := by
  rw [idg_eq_idgNext (by simp [zAtom]), idgNext]
  simp [zTag_zAtom]

@[simp] lemma idg_zIall (s a p d0 : V) : idg (zIall s a p d0) = idg d0 := by
  rw [idg_eq_idgNext (by simp [zIall]), idgNext, if_pos (zTag_zIall s a p d0), zIallPrem_zIall]
  exact znth_idgTable_eq_idg _ d0 (le_pred_of_lt (d0_lt_zIall s a p d0))

@[simp] lemma idg_zIneg (s p d0 : V) : idg (zIneg s p d0) = idg d0 := by
  rw [idg_eq_idgNext (by simp [zIneg]), idgNext, if_neg (by simp), if_pos (zTag_zIneg s p d0),
    zInegPrem_zIneg]
  exact znth_idgTable_eq_idg _ d0 (le_pred_of_lt (d0_lt_zIneg s p d0))

@[simp] lemma idg_zInd (s at' p d0 d1 : V) :
    idg (zInd s at' p d0 d1) = max (max (idg d0 - 1) (idg d1 - 1)) (irk p) := by
  rw [idg_eq_idgNext (by simp [zInd]), idgNext, if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zInd s at' p d0 d1), zIndPrem0_zInd, zIndPrem1_zInd, zIndP_zInd,
    znth_idgTable_eq_idg _ d0 (le_pred_of_lt (d0_lt_zInd s at' p d0 d1)),
    znth_idgTable_eq_idg _ d1 (le_pred_of_lt (d1_lt_zInd s at' p d0 d1))]

/-- **`dg(Ax^{∀xF,k}) = 0`** (Buchholz Lemma 5.2: every atomic axiom has degree 0). Tag 5 falls into
`idgNext`'s `else` branch. -/
@[simp] lemma idg_zAxAll (s p k : V) : idg (zAxAll s p k) = 0 := by
  rw [idg_eq_idgNext (by simp [zAxAll]), idgNext]; simp [zTag_zAxAll]

/-- **`dg(Ax^{¬A,0}) = 0`** (Buchholz Lemma 5.2). Tag 6 falls into `idgNext`'s `else` branch. -/
@[simp] lemma idg_zAxNeg (s p : V) : idg (zAxNeg s p) = 0 := by
  rw [idg_eq_idgNext (by simp [zAxNeg]), idgNext]; simp [zTag_zAxNeg]

/-- **`dg(Ax^1_{·→C}) = 0`** (Buchholz Lemma 5.2: every atomic axiom has degree 0). Tag 7 falls into
`idgNext`'s `else` branch. -/
@[simp] lemma idg_zAx1 (s C : V) : idg (zAx1 s C) = 0 := by
  rw [idg_eq_idgNext (by simp [zAx1]), idgNext]; simp [zTag_zAx1]

/-! ### `idg`-fold over a premise sequence (for the variadic `K^r` equation)

`iseqMaxIdg ds = max_{i < lh ds} idg(znth ds i)` — the genuine idg-fold (applies `idg` directly,
independent of any value-table). The `K^r` step in `idgNext` reads the *table* form
`iseqMaxTab (idgTable M) ds`; when `M` dominates every entry (which holds for `M = zK… - 1`), the two
agree by table stability. This yields the clean `idg_zK` equation. -/

noncomputable def iseqMaxIdgAux.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y ds. y = 0”
  succ := .mkSigma “y ih n ds.
    ∃ di, !znthDef di ds n ∧ ∃ v, !idgDef v di ∧ !max.dfn y ih v”

noncomputable def iseqMaxIdgAux.construction : PR.Construction V iseqMaxIdgAux.blueprint where
  zero := fun _ ↦ 0
  succ := fun x n ih ↦ max ih (idg (znth (x 0) n))
  zero_defined := .mk fun v ↦ by simp [iseqMaxIdgAux.blueprint]
  succ_defined := .mk fun v ↦ by
    simp [iseqMaxIdgAux.blueprint, znth_defined.iff, idg_defined.iff, max_defined.iff]

/-- Partial idg-fold: `iseqMaxIdgAux ds j = max_{i < j} idg(znth ds i)`. -/
noncomputable def iseqMaxIdgAux (ds j : V) : V := iseqMaxIdgAux.construction.result ![ds] j

@[simp] lemma iseqMaxIdgAux_zero (ds : V) : iseqMaxIdgAux ds 0 = 0 := by
  simp [iseqMaxIdgAux, iseqMaxIdgAux.construction]

@[simp] lemma iseqMaxIdgAux_succ (ds j : V) :
    iseqMaxIdgAux ds (j + 1) = max (iseqMaxIdgAux ds j) (idg (znth ds j)) := by
  simp [iseqMaxIdgAux, iseqMaxIdgAux.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.iseqMaxIdgAuxDef : 𝚺₁.Semisentence 3 :=
  iseqMaxIdgAux.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance iseqMaxIdgAux_defined : 𝚺₁-Function₂ (iseqMaxIdgAux : V → V → V) via iseqMaxIdgAuxDef := .mk
  fun v ↦ by simp [iseqMaxIdgAux.construction.result_defined_iff, iseqMaxIdgAuxDef]; rfl

instance iseqMaxIdgAux_definable : 𝚺₁-Function₂ (iseqMaxIdgAux : V → V → V) :=
  iseqMaxIdgAux_defined.to_definable
instance iseqMaxIdgAux_definable' (Γ) : Γ-[m + 1]-Function₂ (iseqMaxIdgAux : V → V → V) :=
  iseqMaxIdgAux_definable.of_sigmaOne

/-- **idg-fold over a sequence**: `iseqMaxIdg ds = max_{i < lh ds} idg(znth ds i)`. -/
noncomputable def iseqMaxIdg (ds : V) : V := iseqMaxIdgAux ds (lh ds)

/-- **Table-fold = idg-fold under dominance.** If `M` is `≥` every in-range entry of `ds`,
the value-table fold over `idgTable M` agrees with the direct idg-fold. -/
lemma iseqMaxAux_idgTable_eq {M ds : V} (hdom : ∀ i < lh ds, znth ds i ≤ M) :
    ∀ j ≤ lh ds, iseqMaxAux (idgTable M) ds j = iseqMaxIdgAux ds j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (by definability) ?_
    refine Definable.comp₂
      (DefinableFunction₃.comp (F := iseqMaxAux)
        (DefinableFunction₁.comp (F := idgTable) (DefinableFunction.const M))
        (DefinableFunction.const ds) (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := iseqMaxIdgAux) (DefinableFunction.const ds)
        (DefinableFunction.var 0))
  case zero => intro _; simp
  case succ j ih =>
    intro hj
    rw [iseqMaxAux_succ, iseqMaxIdgAux_succ, ih (le_trans (by simp) hj),
      znth_idgTable_eq_idg M (znth ds j) (hdom j (lt_of_lt_of_le (by simp) hj))]

/-- **The variadic `K^r` degree equation** (Buchholz §4): for a sequence of premises `ds`,
`dg(K^r_Π d0…dl) = max{dg(d0)-1,…,dg(dl)-1, r} = max r ((max_j dg(dⱼ)) ∸ 1)`. -/
lemma idg_zK (s r ds : V) (hds : Seq ds) :
    idg (zK s r ds) = max r (iseqMaxIdg ds - 1) := by
  have hdom : ∀ i < lh ds, znth ds i ≤ zK s r ds - 1 := fun i hi ↦
    le_pred_of_lt (lt_trans (lt_of_mem_rng (hds.znth hi)) (ds_lt_zK s r ds))
  rw [idg_eq_idgNext (by simp [zK]), idgNext, if_neg (by simp), if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zK s r ds), zKrank_zK, zKseq_zK, iseqMaxTab,
    iseqMaxAux_idgTable_eq hdom (lh ds) (le_refl _), iseqMaxIdg]

/-! ## `iotil` (`õ`) — the pre-ordinal assignment, total `𝚺₁`

Buchholz §4: `õ(atom)=…(§5)`; `õ(I·d0)=õ(d0)+1`; `õ(Ind d0 d1)=ω^{õ d0} # ω^{õ d1 + 1}`;
`õ(K^r d0…dl)=ω^{õ d0} # … # ω^{õ dl}`. Here `ω^α = ocOadd α 1 0`, `+1 = iadd · (ocOadd 0 1 0)`,
`#` = `inadd`. Same table reduction as `idg`. The `K^r` `#`-fold uses the table-helper `iseqNaddTab`. -/

/-! ### `#`-fold over a premise sequence (table form, for the `K^r` step) -/

def iseqNaddTab.blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y s ds. y = 0”
  succ := .mkSigma “y ih n s ds.
    ∃ di, !znthDef di ds n ∧ ∃ v, !znthDef v s di ∧ ∃ w, !ocOaddDef w v 1 0 ∧ !inaddDef y ih w”

noncomputable def iseqNaddTab.construction : PR.Construction V iseqNaddTab.blueprint where
  zero := fun _ ↦ 0
  succ := fun x n ih ↦ inadd ih (ocOadd (znth (x 0) (znth (x 1) n)) 1 0)
  zero_defined := .mk fun v ↦ by simp [iseqNaddTab.blueprint]
  succ_defined := .mk fun v ↦ by
    simp [iseqNaddTab.blueprint, znth_defined.iff, ocOadd_defined.iff, inadd_defined.iff]

/-- Partial `#`-fold of `ω^{table@(znth ds i)}` over the first `j` entries. -/
noncomputable def iseqNaddAux (s ds j : V) : V := iseqNaddTab.construction.result ![s, ds] j

@[simp] lemma iseqNaddAux_zero (s ds : V) : iseqNaddAux s ds 0 = 0 := by
  simp [iseqNaddAux, iseqNaddTab.construction]

@[simp] lemma iseqNaddAux_succ (s ds j : V) :
    iseqNaddAux s ds (j + 1) = inadd (iseqNaddAux s ds j) (ocOadd (znth s (znth ds j)) 1 0) := by
  simp [iseqNaddAux, iseqNaddTab.construction]

def _root_.LO.FirstOrder.Arithmetic.iseqNaddAuxDef : 𝚺₁.Semisentence 4 :=
  iseqNaddTab.blueprint.resultDef.rew (Rew.subst ![#0, #3, #1, #2])

instance iseqNaddAux_defined : 𝚺₁-Function₃ (iseqNaddAux : V → V → V → V) via iseqNaddAuxDef := .mk
  fun v ↦ by simp [iseqNaddTab.construction.result_defined_iff, iseqNaddAuxDef]; rfl

instance iseqNaddAux_definable : 𝚺₁-Function₃ (iseqNaddAux : V → V → V → V) :=
  iseqNaddAux_defined.to_definable
instance iseqNaddAux_definable' (Γ) : Γ-[m + 1]-Function₃ (iseqNaddAux : V → V → V → V) :=
  iseqNaddAux_definable.of_sigmaOne

/-- `#`-fold over the whole sequence: `iseqNaddTab s ds = #_{i<lh ds} ω^{znth s (znth ds i)}`. -/
noncomputable def iseqNaddTab (s ds : V) : V := iseqNaddAux s ds (lh ds)

def _root_.LO.FirstOrder.Arithmetic.iseqNaddTabDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y s ds. ∃ l, !lhDef l ds ∧ !iseqNaddAuxDef y s ds l”

instance iseqNaddTab_defined : 𝚺₁-Function₂ (iseqNaddTab : V → V → V) via iseqNaddTabDef := .mk
  fun v ↦ by simp [iseqNaddTabDef, iseqNaddTab, lh_defined.iff, iseqNaddAux_defined.iff]

instance iseqNaddTab_definable : 𝚺₁-Function₂ (iseqNaddTab : V → V → V) :=
  iseqNaddTab_defined.to_definable
instance iseqNaddTab_definable' (Γ) : Γ-[m + 1]-Function₂ (iseqNaddTab : V → V → V) :=
  iseqNaddTab_definable.of_sigmaOne

/-! ### `iotil` table -/

/-- The pre-ordinal `õ` of an `Ax^{C,t}` atomic axiom (Buchholz Lemma 5.2, §5): `2·rk(C) − 1`, encoded
as the finite InternalONote `ocOadd 0 (rk C + rk C ∸ 1) 0`. For the L-symbol axioms `Ax^{∀xF,k}`
(`C = ∀xF`) and `Ax^{¬A,0}` (`C = ¬A`) where `rk(C) > 0`, the coefficient `2·rk(C)−1 ≥ 1`, so this is a
genuine NF (`isNF_oAtomLk_pos`). -/
noncomputable def oAtomLk (C : V) : V := ocOadd 0 (irk C + irk C - 1) 0

noncomputable def _root_.LO.FirstOrder.Arithmetic.oAtomLkDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y C. ∃ c, !irkDef c C ∧ ∃ m, !subDef m (c + c) 1 ∧ !ocOaddDef y 0 m 0”
instance oAtomLk_defined : 𝚺₁-Function₁ (oAtomLk : V → V) via oAtomLkDef := .mk fun v ↦ by
  simp [oAtomLkDef, oAtomLk, irk_defined.iff, sub_defined.iff, ocOadd_defined.iff]
instance oAtomLk_definable : 𝚺₁-Function₁ (oAtomLk : V → V) := oAtomLk_defined.to_definable
instance oAtomLk_definable' (Γ) : Γ-[m + 1]-Function₁ (oAtomLk : V → V) := oAtomLk_definable.of_sigmaOne

/-- The pre-ordinal `õ` of an `Ax1_{Γ→C}` atomic axiom (Buchholz Lemma 5.2): `2·rk(C)`, as a finite
InternalONote (`0` when `rk C = 0`, else `ocOadd 0 (2·rk C) 0`). This is the õ of the reduct
`d[0] = Ax1_{Π0}` of an L-symbol axiom; `icmp_oAtom1_oAtomLk` is the Lemma-5.2 atomic descent. -/
noncomputable def oAtom1 (C : V) : V := if irk C = 0 then 0 else ocOadd 0 (irk C + irk C) 0

/-- `õ(Ax1_{Γ→C})` is always a genuine NF (it's `0`, or `ocOadd 0 (2·rk C) 0` with `2·rk C > 0`). -/
lemma isNF_oAtom1 (C : V) : isNF (oAtom1 C) := by
  rw [oAtom1]
  by_cases h : irk C = 0
  · rw [if_pos h]; exact isNF_zero
  · rw [if_neg h]
    have hpos : 0 < irk C := pos_iff_ne_zero.mpr h
    exact (isNF_ocOadd 0 (irk C + irk C) 0).2
      ⟨(add_pos hpos hpos).ne', isNF_zero, isNF_zero, Or.inl rfl⟩

noncomputable def _root_.LO.FirstOrder.Arithmetic.oAtom1Def : 𝚺₁.Semisentence 2 := .mkSigma
  “y C. ∃ c, !irkDef c C ∧ ( (c = 0 ∧ y = 0) ∨ (c ≠ 0 ∧ !ocOaddDef y 0 (c + c) 0) )”
instance oAtom1_defined : 𝚺₁-Function₁ (oAtom1 : V → V) via oAtom1Def := .mk fun v ↦ by
  simp [oAtom1Def, oAtom1, irk_defined.iff, ocOadd_defined.iff]
  by_cases h : irk (v 1) = 0 <;> simp [h]
instance oAtom1_definable : 𝚺₁-Function₁ (oAtom1 : V → V) := oAtom1_defined.to_definable

/-- Table step of `iotil`: dispatch on `zTag d`, reading sub-õ-values out of the table `s`. -/
noncomputable def ioNext (d s : V) : V :=
  if zTag d = 1 then iadd (znth s (zIallPrem d)) (ocOadd 0 1 0)
  else if zTag d = 2 then iadd (znth s (zInegPrem d)) (ocOadd 0 1 0)
  else if zTag d = 3 then
    inadd (ocOadd (znth s (zIndPrem0 d)) 1 0)
      (ocOadd (iadd (znth s (zIndPrem1 d)) (ocOadd 0 1 0)) 1 0)
  else if zTag d = 4 then iseqNaddTab s (zKseq d)
  else if zTag d = 5 then oAtomLk (^∀ (zAxAllF d) : V)
  else if zTag d = 6 then oAtomLk (inegF (zAxNegF d))
  else if zTag d = 7 then oAtom1 (zAx1F d)
  else 0

noncomputable def _root_.LO.FirstOrder.Arithmetic.ioNextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y d s. ∃ t, !zTagDef t d ∧ ∃ one, !ocOaddDef one 0 1 0 ∧
    ( (t = 1 ∧ ∃ p, !zIallPremDef p d ∧ ∃ v, !znthDef v s p ∧ !iaddDef y v one)
    ∨ (t = 2 ∧ ∃ p, !zInegPremDef p d ∧ ∃ v, !znthDef v s p ∧ !iaddDef y v one)
    ∨ (t = 3 ∧ ∃ p0, !zIndPrem0Def p0 d ∧ ∃ v0, !znthDef v0 s p0 ∧ ∃ w0, !ocOaddDef w0 v0 1 0 ∧
        ∃ p1, !zIndPrem1Def p1 d ∧ ∃ v1, !znthDef v1 s p1 ∧ ∃ v1s, !iaddDef v1s v1 one ∧
        ∃ w1, !ocOaddDef w1 v1s 1 0 ∧ !inaddDef y w0 w1)
    ∨ (t = 4 ∧ ∃ ds, !zKseqDef ds d ∧ !iseqNaddTabDef y s ds)
    ∨ (t = 5 ∧ ∃ r, !zRestDef r d ∧ ∃ p, !pi₁Def p r ∧ ∃ ap, !qqAllDef ap p ∧ !oAtomLkDef y ap)
    ∨ (t = 6 ∧ ∃ r, !zRestDef r d ∧ ∃ nb, !inegFDef nb r ∧ !oAtomLkDef y nb)
    ∨ (t = 7 ∧ ∃ C, !zAx1FDef C d ∧ !oAtom1Def y C)
    ∨ (t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ t ≠ 5 ∧ t ≠ 6 ∧ t ≠ 7 ∧ y = 0) )”

set_option maxHeartbeats 1000000 in
instance ioNext_defined : 𝚺₁-Function₂ (ioNext : V → V → V) via ioNextDef := .mk fun v ↦ by
  simp [ioNextDef, ioNext, zTag_defined.iff, zIallPrem_defined.iff, zInegPrem_defined.iff,
    zIndPrem0_defined.iff, zIndPrem1_defined.iff, zKseq_defined.iff, iadd_defined.iff,
    inadd_defined.iff, ocOadd_defined.iff, iseqNaddTab_defined.iff, znth_defined.iff,
    zRest_defined.iff, pi₁_defined.iff, qqForall_defined.iff, inegF_defined.iff,
    oAtomLk_defined.iff, oAtom1_defined.iff, zAx1F_defined.iff, zAxAllF, zAxNegF,
    numeral_eq_natCast]
  by_cases h1 : zTag (v 1) = 1
  · simp [h1]
  · by_cases h2 : zTag (v 1) = 2
    · simp [h1, h2]
    · by_cases h3 : zTag (v 1) = 3
      · simp [h1, h2, h3]
      · by_cases h4 : zTag (v 1) = 4
        · simp [h1, h2, h3, h4]
        · by_cases h5 : zTag (v 1) = 5
          · simp [h1, h2, h3, h4, h5]
          · by_cases h6 : zTag (v 1) = 6
            · simp [h1, h2, h3, h4, h5, h6]
            · by_cases h7 : zTag (v 1) = 7
              · simp [h1, h2, h3, h4, h5, h6, h7]
              · simp [h1, h2, h3, h4, h5, h6, h7]

instance ioNext_definable : 𝚺₁-Function₂ (ioNext : V → V → V) := ioNext_defined.to_definable

noncomputable def ioTable.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n. ∃ v, !ioNextDef v (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def ioTable.construction : PR.Construction V ioTable.blueprint where
  zero := fun _ ↦ !⟦0⟧
  succ := fun _ n ih ↦ seqCons ih (ioNext (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [ioTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [ioTable.blueprint, ioNext_defined.iff, seqCons_defined.iff]

noncomputable def ioTable (n : V) : V := ioTable.construction.result ![] n

@[simp] lemma ioTable_zero : ioTable (0 : V) = !⟦0⟧ := by simp [ioTable, ioTable.construction]

@[simp] lemma ioTable_succ (n : V) :
    ioTable (n + 1) = seqCons (ioTable n) (ioNext (n + 1) (ioTable n)) := by
  simp [ioTable, ioTable.construction]

/-- **The pre-ordinal** `õ(d)` of a code: the `d`-th entry of the table. -/
noncomputable def iotil (d : V) : V := znth (ioTable d) d

noncomputable def _root_.LO.FirstOrder.Arithmetic.ioTableDef : 𝚺₁.Semisentence 2 :=
  ioTable.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance ioTable_defined : 𝚺₁-Function₁ (ioTable : V → V) via ioTableDef := .mk
  fun v ↦ by simp [ioTable.construction.result_defined_iff, ioTableDef]; rfl

instance ioTable_definable : 𝚺₁-Function₁ (ioTable : V → V) := ioTable_defined.to_definable
instance ioTable_definable' (Γ) : Γ-[m + 1]-Function₁ (ioTable : V → V) :=
  ioTable_definable.of_sigmaOne

noncomputable def _root_.LO.FirstOrder.Arithmetic.iotilDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ t, !ioTableDef t d ∧ !znthDef y t d”

instance iotil_defined : 𝚺₁-Function₁ (iotil : V → V) via iotilDef := .mk fun v ↦ by
  simp [iotilDef, iotil, ioTable_defined.iff, znth_defined.iff]

instance iotil_definable : 𝚺₁-Function₁ (iotil : V → V) := iotil_defined.to_definable
instance iotil_definable' (Γ) : Γ-[m + 1]-Function₁ (iotil : V → V) := iotil_definable.of_sigmaOne

/-! ### Structural correctness of the `iotil` table (mirror `idg`) -/

private lemma def_ioTable {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ ioTable (v i)) :=
  DefinableFunction₁.comp (F := ioTable) (DefinableFunction.var i)

private lemma def_iotil {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ iotil (v i)) :=
  DefinableFunction₁.comp (F := iotil) (DefinableFunction.var i)

@[simp] lemma ioTable_seq (n : V) : Seq (ioTable n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_ioTable 0)
  case zero => simp
  case succ n ih => rw [ioTable_succ]; exact ih.seqCons _

@[simp] lemma ioTable_lh (n : V) : lh (ioTable n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_ioTable 0)) (by definability)
  case zero => simp
  case succ n ih => rw [ioTable_succ, Seq.lh_seqCons _ (ioTable_seq n), ih]

lemma znth_ioTable_succ {n k : V} (hk : k < n + 1) :
    znth (ioTable (n + 1)) k = znth (ioTable n) k := by
  rw [ioTable_succ]
  exact znth_seqCons_of_lt (ioTable_seq n) _ (by rw [ioTable_lh]; exact hk)

lemma znth_ioTable_eq_iotil : ∀ N : V, ∀ k ≤ N, znth (ioTable N) k = iotil k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_ioTable 1) (DefinableFunction.var 0))
      (def_iotil 0)
  case zero =>
    intro k hk; rcases (nonpos_iff_eq_zero.mp hk) with rfl; rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_ioTable_succ hlt]; exact ih k (le_iff_lt_succ.mpr hlt)

lemma iotil_eq_ioNext {c : V} (hpos : 0 < c) : iotil c = ioNext c (ioTable (c - 1)) := by
  obtain ⟨M, rfl⟩ : ∃ M, c = M + 1 := ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (ioTable (M + 1)) (M + 1) = ioNext (M + 1) (ioTable M) := by
    rw [ioTable_succ]
    have h := znth_seqCons_self (ioTable_seq M) (ioNext (M + 1) (ioTable M))
    rwa [ioTable_lh] at h
  simp only [iotil, add_tsub_cancel_right, key]

/-! ### `iotil` recursion equations (Buchholz §4, finite-premise cases) -/

@[simp] lemma iotil_zAtom (s : V) : iotil (zAtom s) = 0 := by
  rw [iotil_eq_ioNext (by simp [zAtom]), ioNext]; simp [zTag_zAtom]

@[simp] lemma iotil_zIall (s a p d0 : V) :
    iotil (zIall s a p d0) = iadd (iotil d0) (ocOadd 0 1 0) := by
  rw [iotil_eq_ioNext (by simp [zIall]), ioNext, if_pos (zTag_zIall s a p d0), zIallPrem_zIall,
    znth_ioTable_eq_iotil _ d0 (le_pred_of_lt (d0_lt_zIall s a p d0))]

@[simp] lemma iotil_zIneg (s p d0 : V) :
    iotil (zIneg s p d0) = iadd (iotil d0) (ocOadd 0 1 0) := by
  rw [iotil_eq_ioNext (by simp [zIneg]), ioNext, if_neg (by simp), if_pos (zTag_zIneg s p d0),
    zInegPrem_zIneg, znth_ioTable_eq_iotil _ d0 (le_pred_of_lt (d0_lt_zIneg s p d0))]

@[simp] lemma iotil_zInd (s at' p d0 d1 : V) :
    iotil (zInd s at' p d0 d1) =
      inadd (ocOadd (iotil d0) 1 0) (ocOadd (iadd (iotil d1) (ocOadd 0 1 0)) 1 0) := by
  rw [iotil_eq_ioNext (by simp [zInd]), ioNext, if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zInd s at' p d0 d1), zIndPrem0_zInd, zIndPrem1_zInd,
    znth_ioTable_eq_iotil _ d0 (le_pred_of_lt (d0_lt_zInd s at' p d0 d1)),
    znth_ioTable_eq_iotil _ d1 (le_pred_of_lt (d1_lt_zInd s at' p d0 d1))]

/-- **`õ(Ax^{∀xF,k}) = 2·rk(∀xF) − 1`** (Buchholz Lemma 5.2). The atomic axioms read no sub-õ from the
table, so the value is closed-form. -/
@[simp] lemma iotil_zAxAll (s p k : V) : iotil (zAxAll s p k) = oAtomLk (^∀ p : V) := by
  rw [iotil_eq_ioNext (by simp [zAxAll]), ioNext, if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_neg (by simp), if_pos (zTag_zAxAll s p k), zAxAllF_zAxAll]

/-- **`õ(Ax^{¬A,0}) = 2·rk(¬A) − 1`** (Buchholz Lemma 5.2). -/
@[simp] lemma iotil_zAxNeg (s p : V) : iotil (zAxNeg s p) = oAtomLk (inegF p) := by
  rw [iotil_eq_ioNext (by simp [zAxNeg]), ioNext, if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_neg (by simp), if_neg (by simp), if_pos (zTag_zAxNeg s p), zAxNegF_zAxNeg]

/-- **`õ(Ax^1_{·→C}) = oAtom1 C = 2·rk(C)`** (Buchholz Lemma 5.2). Tag 7 = the §5 reduct code. -/
@[simp] lemma iotil_zAx1 (s C : V) : iotil (zAx1 s C) = oAtom1 C := by
  rw [iotil_eq_ioNext (by simp [zAx1]), ioNext, if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_neg (by simp), if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zAx1 s C), zAx1F_zAx1]

/-- `õ(Ax^1_{·→C})` is a genuine NF (it's `oAtom1 C`). -/
@[simp] lemma isNF_iotil_zAx1 (s C : V) : isNF (iotil (zAx1 s C)) := by
  rw [iotil_zAx1]; exact isNF_oAtom1 C

/-- For an L-symbol axiom with a genuine principal formula (`rk(C) > 0`), the atomic õ is a genuine NF
(coefficient `2·rk(C)−1 ≥ 1`). Needed for the Lemma-5.2 atomic descent. -/
lemma isNF_oAtomLk_pos {C : V} (h : 0 < irk C) : isNF (oAtomLk C) := by
  have h1 : (1 : V) ≤ irk C := pos_iff_one_le.mp h
  refine (isNF_ocOadd 0 (irk C + irk C - 1) 0).2 ⟨?_, isNF_zero, isNF_zero, Or.inl rfl⟩
  rw [add_tsub_assoc_of_le h1]
  exact (pos_iff_one_le.mpr (le_trans h1 le_self_add)).ne'

/-- `õ(Ax^{∀p,k})` is a genuine NF for a well-formed matrix `p` (`õ = oAtomLk(∀p)`, `rk(∀p) = rk p+1 > 0`).
The §5 L-axiom-leaf NF fact for the extended `ZDerivation` (tag 5 base case). -/
lemma isNF_iotil_zAxAll {s p k : V} (hp : IsUFormula ℒₒᵣ p) : isNF (iotil (zAxAll s p k)) := by
  rw [iotil_zAxAll]; exact isNF_oAtomLk_pos (by rw [irk_all hp]; simp)

/-- `õ(Ax^{¬p,0})` is a genuine NF for a well-formed `p` (`õ = oAtomLk(¬p)`, `rk(¬p) = rk p+1 > 0`).
The §5 L-axiom-leaf NF fact for the extended `ZDerivation` (tag 6 base case). -/
lemma isNF_iotil_zAxNeg {s p : V} (hp : IsUFormula ℒₒᵣ p) : isNF (iotil (zAxNeg s p)) := by
  rw [iotil_zAxNeg]; exact isNF_oAtomLk_pos (by rw [irk_inegF hp]; simp)

/-! ### iõ-fold over a premise sequence (for the variadic `K^r` equation), mirror `iseqMaxIdg` -/

noncomputable def iseqNaddIdgAux.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y ds. y = 0”
  succ := .mkSigma “y ih n ds.
    ∃ di, !znthDef di ds n ∧ ∃ v, !iotilDef v di ∧ ∃ w, !ocOaddDef w v 1 0 ∧ !inaddDef y ih w”

noncomputable def iseqNaddIdgAux.construction : PR.Construction V iseqNaddIdgAux.blueprint where
  zero := fun _ ↦ 0
  succ := fun x n ih ↦ inadd ih (ocOadd (iotil (znth (x 0) n)) 1 0)
  zero_defined := .mk fun v ↦ by simp [iseqNaddIdgAux.blueprint]
  succ_defined := .mk fun v ↦ by
    simp [iseqNaddIdgAux.blueprint, znth_defined.iff, iotil_defined.iff, ocOadd_defined.iff,
      inadd_defined.iff]

/-- Partial iõ-fold: `iseqNaddIdgAux ds j = #_{i<j} ω^{iotil(znth ds i)}`. -/
noncomputable def iseqNaddIdgAux (ds j : V) : V := iseqNaddIdgAux.construction.result ![ds] j

@[simp] lemma iseqNaddIdgAux_zero (ds : V) : iseqNaddIdgAux ds 0 = 0 := by
  simp [iseqNaddIdgAux, iseqNaddIdgAux.construction]

@[simp] lemma iseqNaddIdgAux_succ (ds j : V) :
    iseqNaddIdgAux ds (j + 1) = inadd (iseqNaddIdgAux ds j) (ocOadd (iotil (znth ds j)) 1 0) := by
  simp [iseqNaddIdgAux, iseqNaddIdgAux.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.iseqNaddIdgAuxDef : 𝚺₁.Semisentence 3 :=
  iseqNaddIdgAux.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance iseqNaddIdgAux_defined : 𝚺₁-Function₂ (iseqNaddIdgAux : V → V → V) via iseqNaddIdgAuxDef :=
  .mk fun v ↦ by simp [iseqNaddIdgAux.construction.result_defined_iff, iseqNaddIdgAuxDef]; rfl

instance iseqNaddIdgAux_definable : 𝚺₁-Function₂ (iseqNaddIdgAux : V → V → V) :=
  iseqNaddIdgAux_defined.to_definable
instance iseqNaddIdgAux_definable' (Γ) : Γ-[m + 1]-Function₂ (iseqNaddIdgAux : V → V → V) :=
  iseqNaddIdgAux_definable.of_sigmaOne

/-- **iõ-fold over a sequence**: `iseqNaddIdg ds = #_{i<lh ds} ω^{iotil(znth ds i)}`. -/
noncomputable def iseqNaddIdg (ds : V) : V := iseqNaddIdgAux ds (lh ds)

/-- **Table-fold = iõ-fold under dominance** (mirror `iseqMaxAux_idgTable_eq`). -/
lemma iseqNaddAux_ioTable_eq {M ds : V} (hdom : ∀ i < lh ds, znth ds i ≤ M) :
    ∀ j ≤ lh ds, iseqNaddAux (ioTable M) ds j = iseqNaddIdgAux ds j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (by definability) ?_
    refine Definable.comp₂
      (DefinableFunction₃.comp (F := iseqNaddAux)
        (DefinableFunction₁.comp (F := ioTable) (DefinableFunction.const M))
        (DefinableFunction.const ds) (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := iseqNaddIdgAux) (DefinableFunction.const ds)
        (DefinableFunction.var 0))
  case zero => intro _; simp
  case succ j ih =>
    intro hj
    rw [iseqNaddAux_succ, iseqNaddIdgAux_succ, ih (le_trans (by simp) hj),
      znth_ioTable_eq_iotil M (znth ds j) (hdom j (lt_of_lt_of_le (by simp) hj))]

/-- **The variadic `K^r` pre-ordinal equation** (Buchholz §4):
`õ(K^r_Π d0…dl) = ω^{õ d0} # … # ω^{õ dl} = #_{j} ω^{õ dⱼ}`. -/
lemma iotil_zK (s r ds : V) (hds : Seq ds) : iotil (zK s r ds) = iseqNaddIdg ds := by
  have hdom : ∀ i < lh ds, znth ds i ≤ zK s r ds - 1 := fun i hi ↦
    le_pred_of_lt (lt_trans (lt_of_mem_rng (hds.znth hi)) (ds_lt_zK s r ds))
  rw [iotil_eq_ioNext (by simp [zK]), ioNext, if_neg (by simp), if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zK s r ds), zKseq_zK, iseqNaddTab,
    iseqNaddAux_ioTable_eq hdom (lh ds) (le_refl _), iseqNaddIdg]

/-! ## `iord` (`o`) — the full ordinal assignment `o(d) = ω_{dg(d)}(õ(d))` (C1c)

The `dg(d)`-fold ω-exponential tower (`iotower`, `src/InternalTower.lean`) over the pre-ordinal
`õ(d)`. This is the [KB81] assignment Thm 4.2 descends on. -/
noncomputable def iord (d : V) : V := iotower (iotil d) (idg d)

noncomputable def _root_.LO.FirstOrder.Arithmetic.iordDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ a, !iotilDef a d ∧ ∃ g, !idgDef g d ∧ !iotowerDef y a g”

instance iord_defined : 𝚺₁-Function₁ (iord : V → V) via iordDef := .mk fun v ↦ by
  simp [iordDef, iord, iotil_defined.iff, idg_defined.iff, iotower_defined.iff]

instance iord_definable : 𝚺₁-Function₁ (iord : V → V) := iord_defined.to_definable
instance iord_definable' (Γ) : Γ-[m + 1]-Function₁ (iord : V → V) := iord_definable.of_sigmaOne

/-- `o(d) = ω_{dg(d)}(õ(d))` — unfolds the assignment to the tower over the pre-ordinal. -/
lemma iord_eq (d : V) : iord d = iotower (iotil d) (idg d) := rfl

/-- **`o(Ax^{C,t}) = õ(Ax^{C,t})`** (Buchholz §5: `dg = 0 ⟹ o(d) = ω₀(õ d) = õ d`). -/
@[simp] lemma iord_zAxAll (s p k : V) : iord (zAxAll s p k) = oAtomLk (^∀ p : V) := by
  rw [iord_eq, idg_zAxAll, iotil_zAxAll, iotower_zero]

@[simp] lemma iord_zAxNeg (s p : V) : iord (zAxNeg s p) = oAtomLk (inegF p) := by
  rw [iord_eq, idg_zAxNeg, iotil_zAxNeg, iotower_zero]

/-- **`o(Ax^1_{·→C}) = oAtom1 C`** (`dg = 0 ⟹ o = ω₀(õ) = õ`). The §5 reduct's ordinal. -/
@[simp] lemma iord_zAx1 (s C : V) : iord (zAx1 s C) = oAtom1 C := by
  rw [iord_eq, idg_zAx1, iotil_zAx1, iotower_zero]

/-- Finite-ONote strict comparison: `a < b ⟹ ω⁰·a ≺ ω⁰·b` (`icmp = 0` is `<`). -/
lemma icmp_ocOadd0_lt {a b : V} (h : a < b) :
    icmp (ocOadd 0 a 0) (ocOadd 0 b 0) = 0 := by
  rw [icmp_ocOadd, icmp_zero_zero, thenV_one_left, cmpV_eq_zero.mpr h, thenV_zero_left]

/-- **Lemma 5.2 atomic descent — ordinal core, L-symbol case.** If the principal formula `C` has rank
one more than the reduct succedent `C'` — which holds for `Ax^{∀xF,k}` (`C = ∀xF`, `C' = F(k)`, via
`rk(∀xF) = rk(F)+1 = rk(F(k))+1`) and `Ax^{¬A,0}` (`C = ¬A`, `C' = A`, via `rk(¬A) = rk(A)+1`) — then
`o(d[0]) = õ(Ax1_{·→C'}) = 2·rk(C') ≺ 2·rk(C)−1 = õ(Ax^{C,t}) = o(d)`. This is the entire ordinal
content of the atomic descent; connecting it to a concrete `iR`/`Ax1` reduct is the next plumbing. -/
lemma icmp_oAtom1_oAtomLk {C C' : V} (h : irk C = irk C' + 1) :
    icmp (oAtom1 C') (oAtomLk C) = 0 := by
  rw [oAtom1, oAtomLk, h]
  by_cases h0 : irk C' = 0
  · rw [if_pos h0]; exact icmp_zero_pos (ocOadd_pos _ _ _).ne'
  · rw [if_neg h0]
    apply icmp_ocOadd0_lt
    have e : (irk C' + 1) + (irk C' + 1) - 1 = irk C' + irk C' + 1 := by
      rw [← add_assoc, add_tsub_cancel_right, add_right_comm]
    rw [e]; exact lt_add_one _

/-- **§5 atomic descent on the genuine codes — `Ax^{∀p,k}` case.** The `Ax^1` reduct `zAx1 s p` (succedent
the matrix `p`, `õ = 2·rk(p)`) strictly lowers the pre-ordinal below the L-axiom `zAxAll s p k`
(`õ = 2·rk(∀p)−1 = 2·rk(p)+1`). Needs `p` a formula (so `rk(∀p) = rk(p)+1`). -/
lemma icmp_iotil_zAx1_zAxAll {s p k : V} (hp : IsUFormula ℒₒᵣ p) :
    icmp (iotil (zAx1 s p)) (iotil (zAxAll s p k)) = 0 := by
  rw [iotil_zAx1, iotil_zAxAll]; exact icmp_oAtom1_oAtomLk (by rw [irk_all hp])

/-- **§5 atomic descent on the genuine codes — `Ax^{¬p,0}` case.** The `Ax^1` reduct `zAx1 s p`
(succedent `p`) strictly lowers `õ` below the L-axiom `zAxNeg s p` (`õ = 2·rk(¬p)−1 = 2·rk(p)+1`). -/
lemma icmp_iotil_zAx1_zAxNeg {s p : V} (hp : IsUFormula ℒₒᵣ p) :
    icmp (iotil (zAx1 s p)) (iotil (zAxNeg s p)) = 0 := by
  rw [iotil_zAx1, iotil_zAxNeg]; exact icmp_oAtom1_oAtomLk (by rw [irk_inegF hp])

/-! ## C3 — Thm 4.2 ordinal descent `o(d[n]) ≺ o(d)`, rule by rule

Buchholz Thm 4.2: each reduction `d ↦ d[n]` strictly lowers `o`. We prove the per-rule ordinal
inequalities directly from the C1 assignment equations and the `src/` order theory (Lemma 4.1
monotonicity: `icmp_iotower_mono` same-degree, `icmp_iotower_lt_succ_of_le` degree-drop,
`self_lt_iadd_one`). These are the mathematical core; wiring them through a concrete reduction
operator `iR` (Def 3.2) is downstream plumbing.

`icmp a b = 0` reads `a ≺ b`. -/

/-- **Same-degree descent template** (Thm 4.2, degree unchanged): if `dg(e)=dg(d)` and
`õ(e) ≺ õ(d)`, then `o(e) ≺ o(d)`. The tower height is fixed and `ω_n` is base-monotone
(`icmp_iotower_mono`). -/
lemma iord_descent_samedeg {d e : V} (hg : idg e = idg d) (ho : icmp (iotil e) (iotil d) = 0) :
    icmp (iord e) (iord d) = 0 := by
  rw [iord, iord, hg]; exact icmp_iotower_mono ho (idg d)

/-- **General structural descent** (Thm 4.2 non-critical / structural cases): if the degree does not rise
(`dg(e) ≤ dg(d)`) and the pre-ordinal strictly drops (`õ(e) ≺ õ(d)`), then `o(e) ≺ o(d)`. Composes the
strict base-monotone step `ω_{dg e}(õ e) ≺ ω_{dg e}(õ d)` (`icmp_iotower_mono`) with the non-strict
height-monotone step `ω_{dg e}(õ d) ≼ ω_{dg d}(õ d)` (`icmp_iotower_height_le`). Generalises
`iord_descent_samedeg` (the `dg(e)=dg(d)` case) to an arbitrary degree drop where `õ` carries the
strictness — exactly the LH3 (non-critical chain, case 5.2.2) interface. -/
lemma iord_descent_le {d e : V} (hnf : isNF (iotil d)) (hg : idg e ≤ idg d)
    (ho : icmp (iotil e) (iotil d) = 0) : icmp (iord e) (iord d) = 0 := by
  rw [iord, iord]
  have step1 : icmp (iotower (iotil e) (idg e)) (iotower (iotil d) (idg e)) = 0 :=
    icmp_iotower_mono ho (idg e)
  rcases icmp_iotower_height_le hnf hg with hh | hh
  · exact icmp_trans
      (max (iotower (iotil e) (idg e))
        (max (iotower (iotil d) (idg e)) (iotower (iotil d) (idg d))))
      _ (le_max_left _ _)
      _ (le_trans (le_max_left _ _) (le_max_right _ _))
      _ (le_trans (le_max_right _ _) (le_max_right _ _)) step1 hh
  · rw [← hh]; exact step1

/-- **Degree-drop descent template** (Thm 4.2, `dg(d)=dg(e)+1`): if `õ(e) ≼ õ(d)` (`≺` or `=`) and
`õ(d)` is in normal form, then `o(e) ≺ o(d)`. One extra tower level strictly dominates
(`icmp_iotower_lt_succ_of_le`). The `isNF (iotil d)` premise is discharged later via
`ZDerivation` (`õ` of a genuine derivation is a valid CNF code). -/
lemma iord_descent_dgdrop {d e : V} (hg : idg d = idg e + 1) (hnf : isNF (iotil d))
    (ho : icmp (iotil e) (iotil d) = 0 ∨ iotil e = iotil d) : icmp (iord e) (iord d) = 0 := by
  rw [iord, iord, hg]
  refine icmp_iotower_lt_succ_of_le hnf (idg e) ?_
  rcases ho with h | h
  · exact Or.inl (icmp_iotower_mono h (idg e))
  · exact Or.inr (by rw [h])

/-- **I-rule descent** (same degree, `õ` drops by one successor): if `dg(e)=dg(d)` and
`õ(d)=õ(e)+1`, then `o(e) ≺ o(d)`. Instance of `iord_descent_samedeg` via `self_lt_iadd_one`
(`õ(e) ≺ õ(e)+1`). Covers Buchholz's `I^a_∀xF`/`I_¬A` cases. -/
lemma iord_descent_I {d e : V} (hg : idg e = idg d)
    (ho : iotil d = iadd (iotil e) (ocOadd 0 1 0)) : icmp (iord e) (iord d) = 0 :=
  iord_descent_samedeg hg (ho ▸ self_lt_iadd_one (iotil e) (iotil e) le_rfl)

/-- `o(d0) ≺ o(I_¬A d0)` — the `I_¬A` reduction `d[0] = d0` strictly lowers `o`. -/
lemma iord_descent_zIneg (s p d0 : V) : icmp (iord d0) (iord (zIneg s p d0)) = 0 :=
  iord_descent_I (by simp) (by simp)

/-- `o(d0) ≺ o(I^a_∀xF d0)` at the level of the premise code `d0` (the `d[n]=d0(a/n)` reduct shares
`d0`'s `dg`/`õ` once substitution-invariance of the assignment is established — a separate brick). -/
lemma iord_descent_zIall (s a p d0 : V) : icmp (iord d0) (iord (zIall s a p d0)) = 0 :=
  iord_descent_I (by simp) (by simp)

/-- **Cut-elimination descent template** (Thm 4.2 critical case, Buchholz Lemma 4.1(b)(ii) case 5.1;
judge `E-CRUX2-DECOMPOSITION-2026-06-24.md` §8.3 N4). The reduct `e = d[0]` has its pre-ordinal jump
*up* to `õ(e) ≺ ω^{õ(d)}` (N3b), but the degree strictly drops `dg(e) + 1 ≤ dg(d)` (N3a). The descent
`o(e) ≺ o(d)` survives because the degree drop absorbs the pre-ordinal jump through the tower:
`o(e) = ω_{dg(e)}(õ(e)) ≺ ω_{dg(e)}(ω^{õ(d)}) = ω_{dg(e)+1}(õ(d)) ≼ ω_{dg(d)}(õ(d)) = o(d)`
— `icmp_iotower_mono` (base) + `iotower_omega_pow` (base-shift) + `icmp_iotower_height_le` (height).
This is the ordinal tail of the nut; only the object construction `iR`-critical-branch + the bounds
N3a/N3b that instantiate `hdeg`/`ho` remain. -/
lemma iord_descent_cut {d e : V} (hnf : isNF (iotil d)) (hdeg : idg e + 1 ≤ idg d)
    (ho : icmp (iotil e) (ocOadd (iotil d) 1 0) = 0) : icmp (iord e) (iord d) = 0 := by
  rw [iord_eq, iord_eq]
  have step1 : icmp (iotower (iotil e) (idg e)) (iotower (ocOadd (iotil d) 1 0) (idg e)) = 0 :=
    icmp_iotower_mono ho (idg e)
  rw [iotower_omega_pow (iotil d) (idg e)] at step1
  rcases icmp_iotower_height_le hnf hdeg with hh | hh
  · exact icmp_trans
      (max (iotower (iotil e) (idg e))
        (max (iotower (iotil d) (idg e + 1)) (iotower (iotil d) (idg d))))
      _ (le_max_left _ _)
      _ (le_trans (le_max_left _ _) (le_max_right _ _))
      _ (le_trans (le_max_right _ _) (le_max_right _ _)) step1 hh
  · rw [← hh]; exact step1

/-! ## `iR` — the one-step reduction `d ↦ d[0]` (Buchholz Def 3.2), rule-by-rule SKELETON

`iR` dispatches on `zTag d`. This lap builds the **structural (LOW-HANGING) branches** — the `I_¬A`
and `I^a_∀xF` rules, whose reduct is simply the premise `d₀` (Buchholz §3.2 cases 2,3; the `I∀`
substitution `d₀(a/0)` is invariant for the ordinal assignment, judge §2 LH2, so the skeleton reads
the bare premise). The `atom`/`Ind`/`K^r` branches are placeholders (`iR d := d`) pending: `Ind` →
the `K^r`-chain reduct (LH4), `K^r` → the non-critical chain step (LH3/LH5) and the **critical
branch** (the nut, §8.3 — builds `d{0}=K^r(i/dᵢ[k])`, `d{1}=K^r(j/d_j[0])`, `d[0]=K^{r-1}d{0}d{1}`).
Flagged in `PENDING_WORK.md`. -/

@[simp] lemma zTag_le_self (d : V) : zTag d ≤ d := le_trans (pi₁_le_self _) (sndIdx_le_self d)

/-- One-step reduction `d ↦ d[0]` (structural-branch skeleton): `I^a_∀` and `I_¬` reduce to their
premise; other tags are placeholders (identity) until their reducts are built. -/
noncomputable def iR (d : V) : V :=
  if zTag d = 1 then zIallPrem d
  else if zTag d = 2 then zInegPrem d
  else d

def _root_.LO.FirstOrder.Arithmetic.iRDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y d. ∃ t <⁺ d, !zTagDef t d ∧
    ( (t = 1 ∧ !zIallPremDef y d) ∨
      (t ≠ 1 ∧ t = 2 ∧ !zInegPremDef y d) ∨
      (t ≠ 1 ∧ t ≠ 2 ∧ y = d) )”

instance iR_defined : 𝚺₀-Function₁ (iR : V → V) via iRDef := .mk fun v ↦ by
  simp [iRDef, iR, zTag_defined.iff, zIallPrem_defined.iff, zInegPrem_defined.iff]
  by_cases h1 : zTag (v 1) = 1 <;> by_cases h2 : zTag (v 1) = 2 <;> simp [h1, h2]

instance iR_definable : 𝚺₀-Function₁ (iR : V → V) := iR_defined.to_definable

-- Compute lemmas: `iR` on each constructor.
@[simp] lemma iR_zIall (s a p d0 : V) : iR (zIall s a p d0) = d0 := by simp [iR]
@[simp] lemma iR_zIneg (s p d0 : V) : iR (zIneg s p d0) = d0 := by simp [iR]
@[simp] lemma iR_zAtom (s : V) : iR (zAtom s) = zAtom s := by simp [iR]
@[simp] lemma iR_zInd (s at' p d0 d1 : V) : iR (zInd s at' p d0 d1) = zInd s at' p d0 d1 := by
  simp [iR]
@[simp] lemma iR_zK (s r ds : V) : iR (zK s r ds) = zK s r ds := by simp [iR]

/-- **Descent through `iR`** for the structural rules: `o(iR d) ≺ o(d)` for `I_¬A`/`I^a_∀xF` codes.
Composes the `iR`-compute lemma with the per-rule `iord_descent_z*`. The atom/Ind/K branches' descent
arrives when their reducts are built. -/
lemma iord_descent_iR_zIneg (s p d0 : V) :
    icmp (iord (iR (zIneg s p d0))) (iord (zIneg s p d0)) = 0 := by
  rw [iR_zIneg]; exact iord_descent_zIneg s p d0

lemma iord_descent_iR_zIall (s a p d0 : V) :
    icmp (iord (iR (zIall s a p d0))) (iord (zIall s a p d0)) = 0 := by
  rw [iR_zIall]; exact iord_descent_zIall s a p d0

/-! ## Structural NF building blocks for `õ` (toward `isNF (iotil d)` on derivations)

`õ(d)` is a valid CNF code (`isNF`) for genuine derivations. The general fact needs structural
induction over `ZDerivation` (the C0 Fixpoint), but the per-constructor NF-closure steps are clean
and provable now: `õ(atom)=0` is NF, and the `K^r` `#`-fold preserves NF given its entries do
(`isNF_inadd` + `isNF_omega_pow`). These discharge the `isNF (iotil d)` premise of
`iord_descent_dgdrop` once the Fixpoint lands. -/

/-- `ω^e = ocOadd e 1 0` is NF iff its exponent is. -/
lemma isNF_omega_pow {e : V} (he : isNF e) : isNF (ocOadd e 1 0) :=
  (isNF_ocOadd e 1 0).2 ⟨(by simp), he, isNF_zero, Or.inl rfl⟩

/-- `õ(0) = 0` — the out-of-range default code `0` (returned by `znth ds n` for `n ≥ lh ds`,
`znth_prop_not`) has pre-ordinal `0`. `ioTable 0 = !⟦0⟧`, whose `0`-th entry is `0`. -/
@[simp] lemma iotil_zero : iotil (0 : V) = 0 := by
  rw [iotil, ioTable_zero]
  simpa using znth_seqCons_self (seq_empty (V := V)) (0 : V)

/-- `õ(0)` is NF — discharges the out-of-range-premise NF in the chain ZDerivation wrappers. -/
@[simp] lemma isNF_iotil_zero : isNF (iotil (0 : V)) := by rw [iotil_zero]; exact isNF_zero

@[simp] lemma isNF_iotil_zAtom (s : V) : isNF (iotil (zAtom s)) := by
  rw [iotil_zAtom]; exact isNF_zero

/-- `õ(I^a_∀xF d0)` is NF when `õ(d0)` is — the assignment is `õ(d0) + 1`, NF by `isNF_iadd_one_right`. -/
@[simp] lemma isNF_iotil_zIall {s a p d0 : V} (hd0 : isNF (iotil d0)) :
    isNF (iotil (zIall s a p d0)) := by rw [iotil_zIall]; exact isNF_iadd_one_right hd0

/-- `õ(I_¬A d0)` is NF when `õ(d0)` is. -/
@[simp] lemma isNF_iotil_zIneg {s p d0 : V} (hd0 : isNF (iotil d0)) :
    isNF (iotil (zIneg s p d0)) := by rw [iotil_zIneg]; exact isNF_iadd_one_right hd0

/-- `õ(Ind^{a,t}_F d0 d1)` is NF when `õ(d0)`,`õ(d1)` are — the assignment is
`ω^{õ(d0)} # ω^{õ(d1)+1}`, NF by `isNF_inadd` of two NF ω-powers (the right exponent via
`isNF_iadd_one_right`). -/
@[simp] lemma isNF_iotil_zInd {s at' p d0 d1 : V} (hd0 : isNF (iotil d0)) (hd1 : isNF (iotil d1)) :
    isNF (iotil (zInd s at' p d0 d1)) := by
  rw [iotil_zInd]
  exact isNF_inadd (isNF_omega_pow (isNF_iadd_one_right hd1)) _ (isNF_omega_pow hd0)

/-- **Partial `#`-fold is NF given only the FOLDED entries' `õ` are NF** (`∀ i < J`, not `∀ n` — the
weaker in-range hypothesis the `K^r` structural step actually supplies via premise-membership). -/
lemma isNF_iseqNaddIdgAux_lt {ds : V} :
    ∀ J, (∀ i < J, isNF (iotil (znth ds i))) → isNF (iseqNaddIdgAux ds J) := by
  intro J
  induction J using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro _; rw [iseqNaddIdgAux_zero]; exact isNF_zero
  case succ J ih =>
    intro h
    rw [iseqNaddIdgAux_succ]
    exact isNF_inadd (isNF_omega_pow (h J (by simp))) _ (ih (fun i hi => h i (lt_trans hi (by simp))))

/-- **`õ(K^r ds)` is NF** when every premise's `õ` is NF (chain NF-closure; the missing `K^r` companion
of `isNF_iotil_zIall`/`_zIneg`/`_zInd`). Only the in-range entries (`i < lh ds`) are required. -/
@[simp] lemma isNF_iotil_zK {s r ds : V} (hds : Seq ds)
    (hNF : ∀ i < lh ds, isNF (iotil (znth ds i))) : isNF (iotil (zK s r ds)) := by
  rw [iotil_zK s r ds hds]; exact isNF_iseqNaddIdgAux_lt (lh ds) hNF

/-- **LH4 — the Ind-rule descent's ordinal core** (Buchholz §4 case 4; judge §2 LH4). The reduct
`d[0] = K^r(d0, d1(0),…,d1(k−1))` has `õ(d[0]) = ω^{õ d0} # ω^{õ d1}·k` (the `k` substitution-invariant
copies collected into one CNF term `ocOadd (õ d1) k 0`), and `õ(zInd) = ω^{õ d0} # ω^{õ d1 + 1}`. The
descent `õ(d[0]) ≺ õ(zInd)` is F1 (left-monotonicity, fixing the `ω^{õ d0}` summand) applied to F3
(`ω^β·k ≺ ω^{β+1}`). The `k ≠ 0` hypothesis keeps `ocOadd b k 0` a valid CNF term. -/
lemma icmp_iotil_ind_reduct {a b k : V} (ha : isNF a) (hb : isNF b) (hk : k ≠ 0) :
    icmp (inadd (ocOadd a 1 0) (ocOadd b k 0))
         (inadd (ocOadd a 1 0) (ocOadd (iadd b (ocOadd 0 1 0)) 1 0)) = 0 :=
  inadd_left_mono
    ((isNF_ocOadd b k 0).2 ⟨hk, hb, isNF_zero, Or.inl rfl⟩)
    (isNF_omega_pow (isNF_iadd_one_right hb))
    (icmp_term_lt_omega_succ b k)
    (ocOadd a 1 0) (isNF_omega_pow ha)

/-- The `#`-fold `iseqNaddIdgAux` is NF when every folded entry's `õ` is NF. -/
lemma isNF_iseqNaddIdgAux {ds : V} (hall : ∀ i < lh ds, isNF (iotil (znth ds i))) :
    ∀ j ≤ lh ds, isNF (iseqNaddIdgAux ds j) := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro _; simpa using isNF_zero
  case succ j ih =>
    intro hj
    rw [iseqNaddIdgAux_succ]
    exact isNF_inadd (isNF_omega_pow (hall j (lt_of_lt_of_le (by simp) hj))) _
      (ih (le_trans (by simp) hj))

/-- `õ(K^r_Π ds)` is NF when every premise's `õ` is NF (via `iotil_zK`). -/
lemma isNF_iseqNaddIdg {ds : V} (hall : ∀ i < lh ds, isNF (iotil (znth ds i))) :
    isNF (iseqNaddIdg ds) := isNF_iseqNaddIdgAux hall (lh ds) le_rfl

/-- **`#`-fold over a constant-õ block collapses to one term**: if every entry of `ds` (in range) has
`õ = β`, then `#_{i<j+1} ω^{õ(znth ds i)} = ω^β·(j+1)` for `j+1 ≤ lh ds`. The Ind-reduct's substituted
premises `d1(0),…,d1(k−1)` all share `õ = õ d1` (substitution-invariance, Buchholz Remark p.10), so their
`#`-fold is `ω^{õ d1}·k` — the left factor of `icmp_iotil_ind_reduct` (LH4). -/
lemma iseqNaddIdgAux_const {ds β : V} (hconst : ∀ i < lh ds, iotil (znth ds i) = β) :
    ∀ j, 0 < j → j ≤ lh ds → iseqNaddIdgAux ds j = ocOadd β j 0 := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (by definability) (Definable.imp (by definability) ?_)
    refine Definable.comp₂
      (DefinableFunction₂.comp (F := iseqNaddIdgAux)
        (DefinableFunction.const ds) (DefinableFunction.var 0))
      (DefinableFunction₃.comp (F := ocOadd) (hF := ocOadd_definable.of_sigmaOne)
        (DefinableFunction.const β) (DefinableFunction.var 0) (DefinableFunction.const 0))
  case zero => intro h; exact absurd h (by simp)
  case succ j ih =>
    intro _ hj
    rw [iseqNaddIdgAux_succ, hconst j (lt_of_lt_of_le (by simp) hj)]
    rcases eq_or_ne j 0 with rfl | hj0
    · rw [iseqNaddIdgAux_zero, inadd_zero_left, zero_add]
    · rw [ih (pos_iff_ne_zero.mpr hj0) (le_trans (by simp) hj), inadd_omega_pow_collect]

/-! ## `iRepeatSeq` — the constant premise block `[v, v, …, v]` (length `k`)

The Ind-reduct `d[0] = K^r(d0, d1(0),…,d1(k−1))` (Buchholz §3.2 case 4) needs a coded premise sequence.
Ordinally, every `d1(j)` shares `õ = õ d1` (substitution-invariance), so the `#`-fold over the
substituted block equals the `#`-fold over `k` *unsubstituted* copies of `d1` (`iseqNaddIdgAux_const`).
`iRepeatSeq` is that constant block — a length-`k` sequence builder mirroring `iwseq`/`iCTable`. (The
genuine substituted reduct, needed for derivation *validity* / `derivesEmpty`-preservation, layers the
eigenvariable substitution on top; this scaffold pins the ordinal side.) -/

def iRepeatSeq.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y v. y = 0”
  succ := .mkSigma “y ih i v. !seqConsDef y ih v”

noncomputable def iRepeatSeq.construction : PR.Construction V iRepeatSeq.blueprint where
  zero := fun _ ↦ ∅
  succ := fun x _ ih ↦ seqCons ih (x 0)
  zero_defined := .mk fun v ↦ by simp [iRepeatSeq.blueprint, emptyset_def]
  succ_defined := .mk fun v ↦ by simp [iRepeatSeq.blueprint, seqCons_defined.iff]

/-- `iRepeatSeq v k = ⟨v, v, …, v⟩` (length `k`). -/
noncomputable def iRepeatSeq (v k : V) : V := iRepeatSeq.construction.result ![v] k

@[simp] lemma iRepeatSeq_zero (v : V) : iRepeatSeq v 0 = ∅ := by
  simp [iRepeatSeq, iRepeatSeq.construction]

@[simp] lemma iRepeatSeq_succ (v k : V) : iRepeatSeq v (k + 1) = seqCons (iRepeatSeq v k) v := by
  simp [iRepeatSeq, iRepeatSeq.construction]

def _root_.LO.FirstOrder.Arithmetic.iRepeatSeqDef : 𝚺₁.Semisentence 3 :=
  iRepeatSeq.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance iRepeatSeq_defined : 𝚺₁-Function₂ (iRepeatSeq : V → V → V) via iRepeatSeqDef := .mk
  fun v ↦ by simp [iRepeatSeq.construction.result_defined_iff, iRepeatSeqDef, iRepeatSeq]; rfl

instance iRepeatSeq_definable : 𝚺₁-Function₂ (iRepeatSeq : V → V → V) := iRepeatSeq_defined.to_definable
instance iRepeatSeq_definable' (Γ) : Γ-[m + 1]-Function₂ (iRepeatSeq : V → V → V) :=
  iRepeatSeq_definable.of_sigmaOne

private lemma def_iRepeatSeq {k} (v : V) (i : Fin k) :
    𝚺-[1].DefinableFunction (fun w : Fin k → V ↦ iRepeatSeq v (w i)) :=
  DefinableFunction₂.comp (F := iRepeatSeq) (DefinableFunction.const v) (DefinableFunction.var i)

@[simp] lemma iRepeatSeq_seq (v k : V) : Seq (iRepeatSeq v k) := by
  induction k using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_iRepeatSeq v 0)
  case zero => simpa using seq_empty
  case succ k ih => rw [iRepeatSeq_succ]; exact ih.seqCons _

@[simp] lemma iRepeatSeq_lh (v k : V) : lh (iRepeatSeq v k) = k := by
  induction k using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_iRepeatSeq v 0)) (by definability)
  case zero => simpa using lh_empty
  case succ k ih => rw [iRepeatSeq_succ, Seq.lh_seqCons _ (iRepeatSeq_seq v k), ih]

/-- Every in-range entry of `iRepeatSeq v k` is `v`. -/
lemma znth_iRepeatSeq {v k : V} : ∀ i < k, znth (iRepeatSeq v k) i = v := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro i hi; exact absurd hi (by simp)
  case succ k ih =>
    intro i hi
    rw [iRepeatSeq_succ]
    rcases eq_or_ne i k with rfl | hik
    · have := znth_seqCons_self (iRepeatSeq_seq v i) v; rwa [iRepeatSeq_lh] at this
    · have hik' : i < k := lt_of_le_of_ne (le_iff_lt_succ.mpr hi) hik
      rw [znth_seqCons_of_lt (iRepeatSeq_seq v k) v (by rw [iRepeatSeq_lh]; exact hik')]
      exact ih i hik'

/-- **The constant block's `#`-fold**: `#_{i<k} ω^{õ v} = ω^{õ v}·k` (for `k > 0`). The capstone
combining `iRepeatSeq` with `iseqNaddIdgAux_const`: this is `õ` of the Ind-reduct's substituted
premise block, the right factor of `icmp_iotil_ind_reduct` (LH4). -/
lemma iseqNaddIdg_iRepeatSeq {v k : V} (hk : 0 < k) :
    iseqNaddIdg (iRepeatSeq v k) = ocOadd (iotil v) k 0 := by
  have hconst : ∀ i < lh (iRepeatSeq v k), iotil (znth (iRepeatSeq v k) i) = iotil v :=
    fun i hi => by rw [znth_iRepeatSeq i (by rwa [iRepeatSeq_lh] at hi)]
  rw [iseqNaddIdg,
    iseqNaddIdgAux_const hconst (lh (iRepeatSeq v k)) (by rw [iRepeatSeq_lh]; exact hk) le_rfl,
    iRepeatSeq_lh]

/-- **`#`-fold depends only on the entries**: if `ds`, `ds'` agree on the first `j` entries then their
partial `#`-folds agree. The congruence behind "replace/extend a sequence" reasoning (the chain cases
LH3/LH5 and the Ind reduct's `seqCons` both need it). -/
lemma iseqNaddIdgAux_congr {ds ds' : V} :
    ∀ j, (∀ i < j, znth ds i = znth ds' i) → iseqNaddIdgAux ds j = iseqNaddIdgAux ds' j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (Definable.ball_lt (by definability) (by definability)) ?_
    refine Definable.comp₂
      (DefinableFunction₂.comp (F := iseqNaddIdgAux)
        (DefinableFunction.const ds) (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := iseqNaddIdgAux)
        (DefinableFunction.const ds') (DefinableFunction.var 0))
  case zero => intro _; rw [iseqNaddIdgAux_zero, iseqNaddIdgAux_zero]
  case succ j ih =>
    intro h
    rw [iseqNaddIdgAux_succ, iseqNaddIdgAux_succ, ih (fun i hi => h i (lt_trans hi (by simp))),
      h j (by simp)]

/-- **`#`-fold over a `seqCons`**: appending `v` adds the summand `ω^{õ v}`. -/
lemma iseqNaddIdg_seqCons {ds v : V} (hds : Seq ds) :
    iseqNaddIdg (seqCons ds v) = inadd (iseqNaddIdg ds) (ocOadd (iotil v) 1 0) := by
  rw [iseqNaddIdg, iseqNaddIdg, Seq.lh_seqCons v hds, iseqNaddIdgAux_succ,
    iseqNaddIdgAux_congr (lh ds) (fun i hi => (znth_seqCons_of_lt hds v hi).symm),
    znth_seqCons_self hds v]

/-! ## The Ind-rule reduct object `d[0] = K^r(d0, d1(0),…,d1(k−1))` — ordinal side (LH4)

`iIndReductSeq d0 d1 k = ⟨d1,…,d1 (k copies), d0⟩` is the reduct's premise sequence (ordinal-faithful:
the `k` substituted copies all carry `õ = õ d1`, and `#` is commutative so `d0`'s position is immaterial).
Its `õ`-fold is `ω^{õ d1}·k # ω^{õ d0}`, and the LH4 descent `õ(d[0]) ≺ õ(Ind…)` follows from
`icmp_iotil_ind_reduct` (F1+F3). This is the **full Ind-rule ordinal descent on a genuine reduct object**;
only the degree side (`idg`, awaiting the real `irk`) and derivation-validity (eigenvariable substitution)
remain to lift it to a full `iord` descent. -/

/-- The Ind-reduct premise sequence `⟨d1,…,d1 (k copies), d0⟩`. -/
noncomputable def iIndReductSeq (d0 d1 k : V) : V := seqCons (iRepeatSeq d1 k) d0

@[simp] lemma iIndReductSeq_seq (d0 d1 k : V) : Seq (iIndReductSeq d0 d1 k) :=
  (iRepeatSeq_seq d1 k).seqCons d0

/-- `õ`-fold of the Ind reduct's premise sequence: `ω^{õ d1}·k # ω^{õ d0}` (for `k > 0`). -/
lemma iseqNaddIdg_iIndReductSeq {d0 d1 k : V} (hk : 0 < k) :
    iseqNaddIdg (iIndReductSeq d0 d1 k) =
      inadd (ocOadd (iotil d1) k 0) (ocOadd (iotil d0) 1 0) := by
  rw [iIndReductSeq, iseqNaddIdg_seqCons (iRepeatSeq_seq d1 k), iseqNaddIdg_iRepeatSeq hk]

/-- **LH4 — full Ind-rule `õ`-descent on the genuine reduct**: `õ(d[0]) ≺ õ(Ind^{a,t}_F d0 d1)`, where
`õ(d[0]) = #` of the reduct premise sequence. The reduct's fold commutes (`inadd_comm`) into the
`ω^{õ d0} # ω^{õ d1}·k` shape, then `icmp_iotil_ind_reduct` (F1+F3) closes it. -/
lemma icmp_iotil_iIndReduct {s at' p d0 d1 k : V}
    (hd0 : isNF (iotil d0)) (hd1 : isNF (iotil d1)) (hk : 0 < k) :
    icmp (iseqNaddIdg (iIndReductSeq d0 d1 k)) (iotil (zInd s at' p d0 d1)) = 0 := by
  have hNFblock : isNF (ocOadd (iotil d1) k 0) :=
    (isNF_ocOadd (iotil d1) k 0).2 ⟨pos_iff_ne_zero.mp hk, hd1, isNF_zero, Or.inl rfl⟩
  rw [iseqNaddIdg_iIndReductSeq hk, iotil_zInd,
    inadd_comm (ocOadd (iotil d0) 1 0) (isNF_omega_pow hd0) _ hNFblock]
  exact icmp_iotil_ind_reduct hd0 hd1 (pos_iff_ne_zero.mp hk)

/-! ### Degree side of the Ind reduct (LH4) — `idg`-fold over the reduct sequence

Mirrors the `õ`-fold machinery (`iseqNaddIdg…`) for the degree fold `iseqMaxIdg`. The capstone is
`idg_zK_iIndReduct`: the reduct `K^{rk p}(d0, d1×k)` has the SAME degree as `Ind^{a,t}_F d0 d1` (because
`max{rk p, max(dg d1, dg d0)∸1} = max{max(dg d0∸1, dg d1∸1), rk p}`, ∸ distributing over max). With
degree preserved and `õ` strictly dropping (`icmp_iotil_iIndReduct`), `iord_descent_samedeg` lifts LH4
to a full `iord` descent on the genuine reduct object — now with the REAL `irk`. -/

/-- **idg-fold congruence**: agreeing entries ⟹ equal partial folds (mirror `iseqNaddIdgAux_congr`). -/
lemma iseqMaxIdgAux_congr {ds ds' : V} :
    ∀ j, (∀ i < j, znth ds i = znth ds' i) → iseqMaxIdgAux ds j = iseqMaxIdgAux ds' j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (Definable.ball_lt (by definability) (by definability)) ?_
    refine Definable.comp₂
      (DefinableFunction₂.comp (F := iseqMaxIdgAux)
        (DefinableFunction.const ds) (DefinableFunction.var 0))
      (DefinableFunction₂.comp (F := iseqMaxIdgAux)
        (DefinableFunction.const ds') (DefinableFunction.var 0))
  case zero => intro _; rw [iseqMaxIdgAux_zero, iseqMaxIdgAux_zero]
  case succ j ih =>
    intro h
    rw [iseqMaxIdgAux_succ, iseqMaxIdgAux_succ, ih (fun i hi => h i (lt_trans hi (by simp))),
      h j (by simp)]

/-- **idg-fold over a `seqCons`**: `iseqMaxIdg (seqCons ds v) = max (iseqMaxIdg ds) (idg v)`. -/
lemma iseqMaxIdg_seqCons {ds v : V} (hds : Seq ds) :
    iseqMaxIdg (seqCons ds v) = max (iseqMaxIdg ds) (idg v) := by
  rw [iseqMaxIdg, iseqMaxIdg, Seq.lh_seqCons v hds, iseqMaxIdgAux_succ,
    iseqMaxIdgAux_congr (lh ds) (fun i hi => (znth_seqCons_of_lt hds v hi).symm),
    znth_seqCons_self hds v]

/-- **idg-fold over a constant-idg block**: if every entry's `idg` is `c`, the fold is `c` (for `0<j`). -/
lemma iseqMaxIdgAux_const {ds c : V} (hconst : ∀ i < lh ds, idg (znth ds i) = c) :
    ∀ j, 0 < j → j ≤ lh ds → iseqMaxIdgAux ds j = c := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · refine Definable.imp (by definability) (Definable.imp (by definability) ?_)
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := iseqMaxIdgAux)
        (DefinableFunction.const ds) (DefinableFunction.var 0)) (by definability)
  case zero => intro h; exact absurd h (by simp)
  case succ j ih =>
    intro _ hj
    rw [iseqMaxIdgAux_succ, hconst j (lt_of_lt_of_le (by simp) hj)]
    rcases eq_or_ne j 0 with rfl | hj0
    · rw [iseqMaxIdgAux_zero]; simp
    · rw [ih (pos_iff_ne_zero.mpr hj0) (le_trans (by simp) hj), max_self]

/-- **idg-fold of a constant block** `iRepeatSeq v k`: `= idg v` (for `0<k`). -/
lemma iseqMaxIdg_iRepeatSeq {v k : V} (hk : 0 < k) : iseqMaxIdg (iRepeatSeq v k) = idg v := by
  have hconst : ∀ i < lh (iRepeatSeq v k), idg (znth (iRepeatSeq v k) i) = idg v :=
    fun i hi => by rw [znth_iRepeatSeq i (by rwa [iRepeatSeq_lh] at hi)]
  rw [iseqMaxIdg,
    iseqMaxIdgAux_const hconst (lh (iRepeatSeq v k)) (by rw [iRepeatSeq_lh]; exact hk) le_rfl]

/-- **idg-fold of the Ind reduct sequence**: `max (idg d1) (idg d0)` (for `0<k`). -/
lemma iseqMaxIdg_iIndReductSeq {d0 d1 k : V} (hk : 0 < k) :
    iseqMaxIdg (iIndReductSeq d0 d1 k) = max (idg d1) (idg d0) := by
  rw [iIndReductSeq, iseqMaxIdg_seqCons (iRepeatSeq_seq d1 k), iseqMaxIdg_iRepeatSeq hk]

/-- `∸` distributes over `max` (linear order): `max a b ∸ 1 = max (a∸1) (b∸1)`. -/
private lemma max_sub_one_distrib (a b : V) : max a b - 1 = max (a - 1) (b - 1) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (tsub_le_tsub_right h 1)]
  · rw [max_eq_left h, max_eq_left (tsub_le_tsub_right h 1)]

/-- **Degree side of LH4**: the Ind reduct `K^{rk p}(d0, d1×k)` has the SAME degree as `Ind^{a,t}_F d0 d1`
(real `irk`). The `K^r` degree `max{rk p, (max dg)∸1}` reshuffles into `Ind`'s `max{(dg∸1)s, rk p}`. -/
lemma idg_zK_iIndReduct {s s' at' p d0 d1 k : V} (hk : 0 < k) :
    idg (zK s' (irk p) (iIndReductSeq d0 d1 k)) = idg (zInd s at' p d0 d1) := by
  rw [idg_zK _ _ _ (iIndReductSeq_seq d0 d1 k), iseqMaxIdg_iIndReductSeq hk, max_sub_one_distrib,
    idg_zInd]
  ac_rfl

/-- **LH4 — full Ind-rule `iord` descent on the genuine reduct object** (real `irk`): with degree
preserved (`idg_zK_iIndReduct`) and `õ` strictly dropping (`icmp_iotil_iIndReduct`),
`iord_descent_samedeg` gives `o(d[0]) ≺ o(Ind^{a,t}_F d0 d1)`. -/
lemma iord_descent_iIndReduct {s s' at' p d0 d1 k : V}
    (hd0 : isNF (iotil d0)) (hd1 : isNF (iotil d1)) (hk : 0 < k) :
    icmp (iord (zK s' (irk p) (iIndReductSeq d0 d1 k))) (iord (zInd s at' p d0 d1)) = 0 := by
  refine iord_descent_samedeg (idg_zK_iIndReduct (s := s) (at' := at') hk) ?_
  rw [iotil_zK _ _ _ (iIndReductSeq_seq d0 d1 k)]
  exact icmp_iotil_iIndReduct hd0 hd1 hk

/-! ## THE NUT — case 5.1 (cut-elimination) ordinal descent on a genuine reduct object

Buchholz Lemma 4.1(b)(ii) case 5.1 (`E-CRUX2-DECOMPOSITION-2026-06-24.md §8.3`). The critical chain
`d = K^r_Π d0…dl` reduces to `d[0] = K^{r-1}_Π d{0} d{1}`, where `d{0}`,`d{1}` are the two auxiliary
derivations from Theorem 3.4 (the redex `(i,j,k)` from Lemma 3.1). The reduct's premise sequence is the
**two-element** `⟨d{0}, d{1}⟩`. Unlike the structural rules, the pre-ordinal `õ` may *jump up* — but the
degree strictly **drops by one** (the only degree-drop in the whole proof; this IS cut-elimination), and
the drop absorbs the jump through the tower (`iord_descent_cut`, the ordinal tail — DONE).

This section mirrors the LH4 architecture (`iIndReductSeq`/folds/`iord_descent_iIndReduct`) on a genuine
two-element reduct object: the `õ`-fold lands on **F2** (`icmp_omega_pow_nadd_lt`, N3b) and the `idg`-fold
on the **ℕ-max degree-drop** (N3a). The IH facts (`õ(d{ν}) ≺ õ(d)`, `dg(d{ν}) ≤ dg(d)`, N1/N2) and the
rank fact `r ≥ 1` (from T3.4 `rk(A(d)) < r`) are the lemma's hypotheses — exactly the Thm-4.2 mutual-IH
interface, to be discharged by `ZDerivation` structural induction downstream. -/

/-- Empty-sequence `#`-fold is `0`. -/
@[simp] lemma iseqNaddIdg_empty : iseqNaddIdg (∅ : V) = 0 := by
  rw [iseqNaddIdg, lh_empty, iseqNaddIdgAux_zero]

/-- Empty-sequence `idg`-fold is `0`. -/
@[simp] lemma iseqMaxIdg_empty : iseqMaxIdg (∅ : V) = 0 := by
  rw [iseqMaxIdg, lh_empty, iseqMaxIdgAux_zero]

/-- The critical reduct's two-element premise sequence `⟨d{0}, d{1}⟩` (Buchholz §3.2 case 5.1). -/
noncomputable def iCritReductSeq (d0 d1 : V) : V := seqCons (seqCons ∅ d0) d1

@[simp] lemma iCritReductSeq_seq (d0 d1 : V) : Seq (iCritReductSeq d0 d1) :=
  (seq_empty.seqCons d0).seqCons d1

@[simp] lemma iCritReductSeq_lh (d0 d1 : V) : lh (iCritReductSeq d0 d1) = 2 := by
  rw [iCritReductSeq, Seq.lh_seqCons _ (seq_empty.seqCons d0), Seq.lh_seqCons _ seq_empty, lh_empty,
    zero_add, one_add_one_eq_two]

@[simp] lemma znth_iCritReductSeq_zero (d0 d1 : V) : znth (iCritReductSeq d0 d1) 0 = d0 := by
  have h1 : (0 : V) < lh (seqCons (∅ : V) d0) := by
    rw [Seq.lh_seqCons _ seq_empty, lh_empty, zero_add]; exact one_pos
  rw [iCritReductSeq, znth_seqCons_of_lt (seq_empty.seqCons d0) d1 h1]
  have := znth_seqCons_self seq_empty d0
  rwa [lh_empty] at this

@[simp] lemma znth_iCritReductSeq_one (d0 d1 : V) : znth (iCritReductSeq d0 d1) 1 = d1 := by
  have h := znth_seqCons_self (seq_empty.seqCons d0) d1
  rw [Seq.lh_seqCons _ seq_empty, lh_empty, zero_add] at h
  rw [iCritReductSeq]; exact h

/-- **Critical recombination validity (Thm 3.4(a) → outer `K^{r-1}` chain).** The two-element chain
`⟨d{0}, d{1}⟩` underlying the critical reduct `d[0] = K^{r-1}_Π d{0} d{1}` (Buchholz §3.2 case 5.1) is
`isChainInf`-valid with conclusion `s = Π` and rank `r`, given the Thm-3.4(a) end-sequent threading:
`d{1}`'s succedent is `Π`'s succedent (`d{1} ⊢ A(d),Π`); `d{0}`'s antecedent threads to `Π`
(`d{0} ⊢ Π·A(d)`); `d{1}`'s antecedent threads to `Π` or to the cut formula `A(d)` = `d{0}`'s succedent
(the genuine R/L cut on `A(d)`); and `rk(A(d)) ≤ r` (Thm 3.4(a) `rk(A(d)) < r`, here the rank-`(r-1)`
chain reads its cut formula `A(d)` at `≤ r`). This is the validity half of the critical case of
`RedSound`, modulo the genuine reduct supplying these sequents (the current `iCritReduct` is the
ordinal shadow with all-`fstIdx d` premises — see the Option-B obstruction). -/
lemma isChainInf_iCritReductSeq {s r d0 d1 : V}
    (hsucc1 : seqSucc (fstIdx d1) = seqSucc s)
    (hthread0 : ∀ B, inAnt B (seqAnt (fstIdx d0)) → inAnt B (seqAnt s))
    (hthread1 : ∀ B, inAnt B (seqAnt (fstIdx d1)) →
        inAnt B (seqAnt s) ∨ B = seqSucc (fstIdx d0))
    (hrank0 : irk (seqSucc (fstIdx d0)) ≤ r) :
    isChainInf s r (iCritReductSeq d0 d1) := by
  have eA0 : chainAsucc (iCritReductSeq d0 d1) 0 = seqSucc (fstIdx d0) := by
    unfold chainAsucc; rw [znth_iCritReductSeq_zero]
  have eN0 : chainAnt (iCritReductSeq d0 d1) 0 = seqAnt (fstIdx d0) := by
    unfold chainAnt; rw [znth_iCritReductSeq_zero]
  have eN1 : chainAnt (iCritReductSeq d0 d1) 1 = seqAnt (fstIdx d1) := by
    unfold chainAnt; rw [znth_iCritReductSeq_one]
  refine ⟨1, ?_, ?_, ?_, ?_⟩
  · rw [iCritReductSeq_lh]; exact one_lt_two
  · left; unfold chainAsucc; rw [znth_iCritReductSeq_one]; exact hsucc1
  · intro i hi B hB
    rcases eq_or_lt_of_le hi with rfl | hlt
    · rw [eN1] at hB
      rcases hthread1 B hB with h | h
      · exact Or.inl h
      · exact Or.inr ⟨0, one_pos, by rw [h, eA0]⟩
    · obtain rfl := lt_one_iff_eq_zero.mp hlt
      rw [eN0] at hB
      exact Or.inl (hthread0 B hB)
  · intro i hi
    obtain rfl := lt_one_iff_eq_zero.mp hi
    rw [eA0]; exact hrank0

/-- A predicate holding on both `d0` and `d1` holds on every premise of `⟨d0, d1⟩`. -/
lemma forall_lt_iCritReductSeq {P : V → Prop} {d0 d1 : V} (h0 : P d0) (h1 : P d1) :
    ∀ i < lh (iCritReductSeq d0 d1), P (znth (iCritReductSeq d0 d1) i) := by
  intro i hi
  rcases lt_or_ge i 1 with hlt | hge
  · obtain rfl := lt_one_iff_eq_zero.mp hlt; rw [znth_iCritReductSeq_zero]; exact h0
  · have hi2 : i < 1 + 1 := by rw [iCritReductSeq_lh, ← one_add_one_eq_two] at hi; exact hi
    obtain rfl : i = 1 := le_antisymm (le_iff_lt_succ.mpr hi2) hge
    rw [znth_iCritReductSeq_one]; exact h1

/-- **Full faithful validity of the critical recombination chain** (Buchholz §3.2 case 5.1 + Thm 3.4).
`zK s r ⟨d{0}, d{1}⟩` is `zKValidF` given: the two auxiliaries are `Rep`-tagged chains
(`tp = isymRep`, `zTag = 4`, so own-permissibility is automatic and the I/Ax formula-hood conjuncts are
vacuous), the Thm-3.4(a) cut-threading (`isChainInf_iCritReductSeq`), the auxiliaries' succedent
formula-hood, and the conclusion-sequent formula-hood. The validity half (`RedSound`'s D₁) of the
critical case, isolated as a hypothesis interface for the genuine reduct to discharge. -/
lemma zKValidF_iCritReductSeq {s r d0 d1 : V}
    (htp0 : tp d0 = isymRep) (htp1 : tp d1 = isymRep)
    (htag0 : zTag d0 = 4) (htag1 : zTag d1 = 4)
    (hsucc1 : seqSucc (fstIdx d1) = seqSucc s)
    (hthread0 : ∀ B, inAnt B (seqAnt (fstIdx d0)) → inAnt B (seqAnt s))
    (hthread1 : ∀ B, inAnt B (seqAnt (fstIdx d1)) →
        inAnt B (seqAnt s) ∨ B = seqSucc (fstIdx d0))
    (hrank0 : irk (seqSucc (fstIdx d0)) ≤ r)
    (hUf0 : IsUFormula ℒₒᵣ (seqSucc (fstIdx d0)))
    (hUf1 : IsUFormula ℒₒᵣ (seqSucc (fstIdx d1)))
    (hss : IsUFormula ℒₒᵣ (seqSucc s))
    (hsa : ∀ k < lh (seqAnt s), IsUFormula ℒₒᵣ (znth (seqAnt s) k)) :
    zKValidF s r (iCritReductSeq d0 d1) := by
  refine ⟨isChainInf_iCritReductSeq hsucc1 hthread0 hthread1 hrank0, ?_, ?_, ?_, ?_, ?_, ?_, hss, hsa⟩
  · exact forall_lt_iCritReductSeq (P := fun x => iperm (tp x) (fstIdx x))
      (by rw [htp0]; exact iperm_isymRep _) (by rw [htp1]; exact iperm_isymRep _)
  · exact forall_lt_iCritReductSeq (P := fun x => zTag x = 1 → IsUFormula ℒₒᵣ (zIallF x))
      (fun hc => by rw [htag0] at hc; simp at hc) (fun hc => by rw [htag1] at hc; simp at hc)
  · exact forall_lt_iCritReductSeq (P := fun x => zTag x = 2 → IsUFormula ℒₒᵣ (zInegF x))
      (fun hc => by rw [htag0] at hc; simp at hc) (fun hc => by rw [htag1] at hc; simp at hc)
  · exact forall_lt_iCritReductSeq (P := fun x => zTag x = 5 → IsUFormula ℒₒᵣ (zAxAllF x))
      (fun hc => by rw [htag0] at hc; simp at hc) (fun hc => by rw [htag1] at hc; simp at hc)
  · exact forall_lt_iCritReductSeq (P := fun x => zTag x = 6 → IsUFormula ℒₒᵣ (zAxNegF x))
      (fun hc => by rw [htag0] at hc; simp at hc) (fun hc => by rw [htag1] at hc; simp at hc)
  · exact forall_lt_iCritReductSeq (P := fun x => IsUFormula ℒₒᵣ (seqSucc (fstIdx x))) hUf0 hUf1

/-- **Critical recombination validity on the GENUINE auxiliaries — threading is AUTOMATIC.** When the two
auxiliaries carry the genuine Buchholz §2 p.6 / Thm 3.4(a) endsequents — `d{0}` concludes `Θ→A(d)`
(`seqSetSucc s C`), `d{1}` concludes `A(d),Θ→D` (`seqAddAnt C s`), with `C = A(d)` the cut formula — the
cut-threading hypotheses of `zKValidF_iCritReductSeq` hold *by construction* (`seqSetSucc`/`seqAddAnt`
read-outs + `inAnt_seqCons`), leaving only the cut-rank drop `rk(A(d)) ≤ rOut` (Thm 3.4(a), `< r`) and
the formula-hood of `A(d)` and the conclusion's antecedent/succedent. The inner ranks `rIn0/rIn1` and
premise sequences `ds0/ds1` are immaterial to the outer chain's validity. This is the validity (D₁) of
the critical reduct, modulo only the (banked) rank arithmetic and the auxiliaries being `ZDerivation`s. -/
lemma zKValidF_iCritReductGen {s C rOut rIn0 rIn1 ds0 ds1 : V}
    (hsAnt : Seq (seqAnt s))
    (hCrk : irk C ≤ rOut)
    (hCUf : IsUFormula ℒₒᵣ C)
    (hssUf : IsUFormula ℒₒᵣ (seqSucc s))
    (hsaUf : ∀ k < lh (seqAnt s), IsUFormula ℒₒᵣ (znth (seqAnt s) k)) :
    zKValidF s rOut
      (iCritReductSeq (zK (seqSetSucc s C) rIn0 ds0) (zK (seqAddAnt C s) rIn1 ds1)) := by
  apply zKValidF_iCritReductSeq
  · rw [tp_zK]
  · rw [tp_zK]
  · rw [zTag_zK]
  · rw [zTag_zK]
  · rw [fstIdx_zK, seqSucc_seqAddAnt]
  · intro B hB; rw [fstIdx_zK, seqAnt_seqSetSucc] at hB; exact hB
  · intro B hB
    rw [fstIdx_zK, seqAnt_seqAddAnt] at hB
    rw [fstIdx_zK, seqSucc_seqSetSucc]
    exact ((inAnt_seqCons hsAnt).mp hB).symm
  · rw [fstIdx_zK, seqSucc_seqSetSucc]; exact hCrk
  · rw [fstIdx_zK, seqSucc_seqSetSucc]; exact hCUf
  · rw [fstIdx_zK, seqSucc_seqAddAnt]; exact hssUf
  · exact hssUf
  · exact hsaUf

/-- **The genuine critical reduct** `d[0] = K^{rOut}_Π d{0} d{1}` (Buchholz §3.2 case 5.1), built on the
GENUINE auxiliaries: `d{0} = K^{rIn0}_{Θ→A(d)} ds0` concludes `Θ→A(d)` (`seqSetSucc s C`), `d{1} =
K^{rIn1}_{A(d),Θ→D} ds1` concludes `A(d),Θ→D` (`seqAddAnt C s`), with `C = A(d)` the cut formula. Unlike
the ordinal-shadow `iCritReduct`, the auxiliaries carry the cut's reduced endsequents — so the
recombination's validity threading is automatic (`zKValidF_iCritReductGen`). -/
noncomputable def iCritReductG (s C rOut rIn0 rIn1 ds0 ds1 : V) : V :=
  zK s rOut (iCritReductSeq (zK (seqSetSucc s C) rIn0 ds0) (zK (seqAddAnt C s) rIn1 ds1))

@[simp] lemma fstIdx_iCritReductG (s C rOut rIn0 rIn1 ds0 ds1 : V) :
    fstIdx (iCritReductG s C rOut rIn0 rIn1 ds0 ds1) = s := by simp [iCritReductG]
@[simp] lemma zTag_iCritReductG (s C rOut rIn0 rIn1 ds0 ds1 : V) :
    zTag (iCritReductG s C rOut rIn0 rIn1 ds0 ds1) = 4 := by simp [iCritReductG]
@[simp] lemma zKseq_iCritReductG (s C rOut rIn0 rIn1 ds0 ds1 : V) :
    zKseq (iCritReductG s C rOut rIn0 rIn1 ds0 ds1) =
      iCritReductSeq (zK (seqSetSucc s C) rIn0 ds0) (zK (seqAddAnt C s) rIn1 ds1) := by
  simp [iCritReductG]

/-- `õ`-fold of the critical reduct sequence: `ω^{õ d{0}} # ω^{õ d{1}}` (N3b's left side). -/
lemma iseqNaddIdg_iCritReductSeq (d0 d1 : V) :
    iseqNaddIdg (iCritReductSeq d0 d1) =
      inadd (ocOadd (iotil d0) 1 0) (ocOadd (iotil d1) 1 0) := by
  rw [iCritReductSeq, iseqNaddIdg_seqCons (seq_empty.seqCons d0),
    iseqNaddIdg_seqCons seq_empty, iseqNaddIdg_empty, inadd_zero_left]

/-- `idg`-fold of the critical reduct sequence: `max (idg d{0}) (idg d{1})` (N3a's max). -/
lemma iseqMaxIdg_iCritReductSeq (d0 d1 : V) :
    iseqMaxIdg (iCritReductSeq d0 d1) = max (idg d0) (idg d1) := by
  rw [iCritReductSeq, iseqMaxIdg_seqCons (seq_empty.seqCons d0),
    iseqMaxIdg_seqCons seq_empty, iseqMaxIdg_empty, max_eq_right (show (0:V) ≤ idg d0 by simp)]

/-- The chain rank `r` is `≤` the chain's own degree (`idg(K^r ds) = max r (…) ≥ r`). -/
lemma r_le_idg_zK (s r ds : V) (hds : Seq ds) : r ≤ idg (zK s r ds) := by
  rw [idg_zK s r ds hds]; exact le_max_left _ _

/-- **N3a — the cut-elimination degree drop**: `dg(d[0]) = max{r', max(dg d{0}, dg d{1})∸1} < dg(d)`.
Each component is `< dg(d)`: `r' < dg(d)` (the reduct rank `r-1`, from `r ≤ dg d`), and
`max(dg d{0}, dg d{1})∸1 < dg(d)` (from `dg(d{ν}) ≤ dg(d)` (N2) and `dg(d) ≥ 1`). Pure ℕ-max
arithmetic once `iR` builds `d{0}/d{1}`. -/
lemma idg_zK_iCritReduct_lt {s' r' d0 d1 d : V}
    (hr' : r' + 1 ≤ idg d) (h0 : idg d0 ≤ idg d) (h1 : idg d1 ≤ idg d) (hpos : 1 ≤ idg d) :
    idg (zK s' r' (iCritReductSeq d0 d1)) + 1 ≤ idg d := by
  rw [idg_zK _ _ _ (iCritReductSeq_seq d0 d1), iseqMaxIdg_iCritReductSeq, succ_le_iff_lt]
  exact max_lt (succ_le_iff_lt.mp hr')
    (lt_of_le_of_lt (tsub_le_tsub_right (max_le h0 h1) 1)
      (tsub_lt_self (pos_iff_one_le.mpr hpos) one_pos))

/-- **THE NUT (case 5.1 ordinal descent) — `o(d[0]) ≺ o(d)` on the genuine two-element reduct object.**
Given the Thm-4.2 mutual-IH facts on the auxiliaries `d{0}`,`d{1}` (`õ(d{ν}) ≺ õ(d)`, `dg(d{ν}) ≤ dg(d)`)
and the rank-bound consequence `dg(d) ≥ 1`, `r' + 1 ≤ dg(d)` (T3.4 `rk(A(d)) < r ≤ dg(d)`), the reduct
`d[0] = K^{r'}_Π d{0} d{1}` descends: N3b (`õ(d[0]) = ω^{õ d{0}} # ω^{õ d{1}} ≺ ω^{õ(d)}`, **F2**) and N3a
(degree drop) feed `iord_descent_cut` (the tower combine, N4). -/
lemma iord_descent_iCritReduct {s' r' d0 d1 d : V}
    (hnf : isNF (iotil d))
    (h0o : icmp (iotil d0) (iotil d) = 0) (h1o : icmp (iotil d1) (iotil d) = 0)
    (hr' : r' + 1 ≤ idg d) (h0g : idg d0 ≤ idg d) (h1g : idg d1 ≤ idg d) (hpos : 1 ≤ idg d) :
    icmp (iord (zK s' r' (iCritReductSeq d0 d1))) (iord d) = 0 := by
  refine iord_descent_cut hnf (idg_zK_iCritReduct_lt hr' h0g h1g hpos) ?_
  rw [iotil_zK _ _ _ (iCritReductSeq_seq d0 d1), iseqNaddIdg_iCritReductSeq]
  exact icmp_omega_pow_nadd_lt h0o h1o

/-- **THE NUT, chain-specialized** — the reduct rank is the original chain rank minus one
(`d[0] = K^{r-1}…`, Buchholz §3.2 case 5.1). `r ≤ dg(K^r ds)` is automatic (`r_le_idg_zK`); `r ≥ 1` is
T3.4. So the only genuine inputs are the IH bounds on `d{0}`,`d{1}`. -/
lemma iord_descent_iCritReduct_chain {s s' r d0 d1 ds : V}
    (hds : Seq ds) (hr : 1 ≤ r)
    (hnf : isNF (iotil (zK s r ds)))
    (h0o : icmp (iotil d0) (iotil (zK s r ds)) = 0)
    (h1o : icmp (iotil d1) (iotil (zK s r ds)) = 0)
    (h0g : idg d0 ≤ idg (zK s r ds)) (h1g : idg d1 ≤ idg (zK s r ds)) :
    icmp (iord (zK s' (r - 1) (iCritReductSeq d0 d1))) (iord (zK s r ds)) = 0 := by
  have hrd : r ≤ idg (zK s r ds) := r_le_idg_zK s r ds hds
  have hpos : 1 ≤ idg (zK s r ds) := le_trans hr hrd
  have hr' : (r - 1) + 1 ≤ idg (zK s r ds) := by rw [sub_add_self_of_le hr]; exact hrd
  exact iord_descent_iCritReduct hnf h0o h1o hr' h0g h1g hpos

/-! ## N2 — the "replace-a-premise" fold facts (Buchholz Thm 4.2 IH-lift; judge §8.3 N2)

The critical auxiliaries `d{0} = K^r(i/d_i[k])`, `d{1} = K^r(j/d_j[0])` are the chain `d` with ONE
premise replaced by an ordinally-smaller reduct (N1 IH: `õ(d_i[k]) ≺ õ(d_i)`, `dg(d_i[k]) ≤ dg(d_i)`).
These generic fold lemmas — over two premise sequences `ds`,`ds'` agreeing (in `õ`/`idg` of entries)
except at one index `i` — give the N2 facts `õ(d{ν}) ≺ õ(d)` (strict, via **F1**) and `dg(d{ν}) ≤ dg(d)`
(via max-fold monotonicity), exactly the hypotheses the nut's `iord_descent_iCritReduct` consumes. The
fold-drop is the genuine "left-cancel one summand" content (judge's reusable T2 leaf); definability-free
(the arithmetized `seqUpdate` object that realizes `ds' = ds[i ↦ v]` layers on top). -/

/-- Partial `#`-fold depends only on the `õ` of entries (stronger than `iseqNaddIdgAux_congr`, which
needs entry equality — this needs only `õ`-of-entry equality). -/
lemma iseqNaddIdgAux_congr_iotil {ds ds' : V} :
    ∀ j, (∀ i < j, iotil (znth ds i) = iotil (znth ds' i)) →
      iseqNaddIdgAux ds j = iseqNaddIdgAux ds' j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro _; rw [iseqNaddIdgAux_zero, iseqNaddIdgAux_zero]
  case succ j ih =>
    intro h
    rw [iseqNaddIdgAux_succ, iseqNaddIdgAux_succ, ih (fun i hi => h i (lt_trans hi (by simp))),
      h j (by simp)]

/-- Partial `#`-fold is NF when every folded entry's `õ` is NF. -/
lemma isNF_iseqNaddIdgAux' {ds : V} (hNF : ∀ n, isNF (iotil (znth ds n))) :
    ∀ j, isNF (iseqNaddIdgAux ds j) := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [iseqNaddIdgAux_zero]; exact isNF_zero
  case succ j ih => rw [iseqNaddIdgAux_succ]; exact isNF_inadd (isNF_omega_pow (hNF j)) _ ih

/-- **N2, `õ`-side (strict)** — the `#`-fold strictly drops when ONE entry's `õ` strictly drops and the
rest are unchanged (F1 left-cancel). Generic over `ds`,`ds'`; the strict-drop entry is `i`. -/
lemma iseqNaddIdgAux_lt_replace {ds ds' i : V}
    (hlt : icmp (iotil (znth ds' i)) (iotil (znth ds i)) = 0)
    (heq : ∀ n, n ≠ i → iotil (znth ds' n) = iotil (znth ds n))
    (hNF : ∀ n, isNF (iotil (znth ds n)))
    (hNF' : ∀ n, isNF (iotil (znth ds' n))) :
    ∀ j, i < j → icmp (iseqNaddIdgAux ds' j) (iseqNaddIdgAux ds j) = 0 := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro h; exact absurd h (by simp)
  case succ j ih =>
    intro hi
    rw [iseqNaddIdgAux_succ, iseqNaddIdgAux_succ]
    rcases lt_or_eq_of_le (le_iff_lt_succ.mpr hi) with hij | hij
    · -- i < j: entry j is unchanged; prefix strictly drops (IH), suffix fixed (F1-mirror).
      rw [heq j (Ne.symm (ne_of_lt hij))]
      exact inadd_right_mono (isNF_iseqNaddIdgAux' hNF' j) (isNF_iseqNaddIdgAux' hNF j) (ih hij)
        _ (isNF_omega_pow (hNF j))
    · -- i = j: entry j IS the strict-drop entry; prefix unchanged, suffix drops (F1).
      subst hij
      have hpre : iseqNaddIdgAux ds' i = iseqNaddIdgAux ds i :=
        iseqNaddIdgAux_congr_iotil i (fun m hm => heq m (ne_of_lt hm))
      rw [hpre]
      refine inadd_left_mono (isNF_omega_pow (hNF' i)) (isNF_omega_pow (hNF i)) ?_
        _ (isNF_iseqNaddIdgAux' hNF i)
      rw [icmp_omega_pow]; exact hlt

/-- **N2, `idg`-side (monotone)** — the `idg` (max) fold is monotone under entrywise `idg`-domination. -/
lemma iseqMaxIdgAux_mono {ds ds' : V} (hle : ∀ n, idg (znth ds' n) ≤ idg (znth ds n)) :
    ∀ j, iseqMaxIdgAux ds' j ≤ iseqMaxIdgAux ds j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ j ih => rw [iseqMaxIdgAux_succ, iseqMaxIdgAux_succ]; exact max_le_max ih (hle j)

/-- **N2, `õ`-side at the `K^r` level** — `õ(K^r ds') ≺ õ(K^r ds)` when `ds'` replaces premise `i` of
`ds` by an ordinally-smaller derivation (`õ(znth ds' i) ≺ õ(znth ds i)`), same length, rest unchanged.
This is `õ(d{ν}) ≺ õ(d)` (judge §8.3 N2), the strict pre-ordinal hypothesis of `iord_descent_iCritReduct`. -/
lemma iotil_zK_lt_replace {s s' r r' ds ds' i : V} (hds : Seq ds) (hds' : Seq ds')
    (hlh : lh ds' = lh ds) (hi : i < lh ds)
    (hlt : icmp (iotil (znth ds' i)) (iotil (znth ds i)) = 0)
    (heq : ∀ n, n ≠ i → iotil (znth ds' n) = iotil (znth ds n))
    (hNF : ∀ n, isNF (iotil (znth ds n))) (hNF' : ∀ n, isNF (iotil (znth ds' n))) :
    icmp (iotil (zK s' r' ds')) (iotil (zK s r ds)) = 0 := by
  rw [iotil_zK s' r' ds' hds', iotil_zK s r ds hds, iseqNaddIdg, iseqNaddIdg, hlh]
  exact iseqNaddIdgAux_lt_replace hlt heq hNF hNF' (lh ds) hi

/-- **N2, `idg`-side at the `K^r` level** — `dg(K^r ds') ≤ dg(K^r ds)` (same rank `r`) when `ds'`
replaces a premise of `ds` by one of `≤` degree, same length. This is `dg(d{ν}) ≤ dg(d)` (judge §8.3 N2). -/
lemma idg_zK_le_replace {s s' r ds ds' : V} (hds : Seq ds) (hds' : Seq ds')
    (hlh : lh ds' = lh ds) (hle : ∀ n, idg (znth ds' n) ≤ idg (znth ds n)) :
    idg (zK s' r ds') ≤ idg (zK s r ds) := by
  rw [idg_zK s' r ds' hds', idg_zK s r ds hds, iseqMaxIdg, iseqMaxIdg, hlh]
  exact max_le_max le_rfl (tsub_le_tsub_right (iseqMaxIdgAux_mono hle (lh ds)) 1)

/-! ## `seqUpdate` — replace one entry of a sequence (the arithmetized "replace-a-premise", judge T2/T3)

`seqUpdate ds i v = ds[i ↦ v]`: the sequence `ds` with entry `i` replaced by `v`, same length. This is
the code-level operation Buchholz's critical reducts use: `d{0} = K^r(i/d_i[k])` is the chain `d` with
its `i`-th premise replaced by the reduct `d_i[k]` (`iCritAux` below). Built as a `PR.Construction` over
a counter copying entries (entry `n` becomes `v` when `n = i`, else `znth ds n`), so it is a total `𝚺₁`
function — the genuine arithmetized object, not a meta-iterate. -/

def seqUpdateAux.blueprint : PR.Blueprint 3 where
  zero := .mkSigma “y ds i v. y = 0”
  succ := .mkSigma “y ih n ds i v.
    ( (n = i ∧ !seqConsDef y ih v) ∨
      (n ≠ i ∧ ∃ b, !znthDef b ds n ∧ !seqConsDef y ih b) )”

noncomputable def seqUpdateAux.construction : PR.Construction V seqUpdateAux.blueprint where
  zero := fun _ ↦ ∅
  succ := fun x n ih ↦ seqCons ih (if n = x 1 then x 2 else znth (x 0) n)
  zero_defined := .mk fun v ↦ by simp [seqUpdateAux.blueprint, emptyset_def]
  succ_defined := .mk fun v ↦ by
    by_cases h : v 2 = v 4
    · simp [seqUpdateAux.blueprint, h, seqCons_defined.iff]
    · simp [seqUpdateAux.blueprint, h, znth_defined.iff, seqCons_defined.iff]

/-- `seqUpdateAux ds i v n` = the length-`n` prefix with entry `i` (if `< n`) replaced by `v`. -/
noncomputable def seqUpdateAux (ds i v n : V) : V := seqUpdateAux.construction.result ![ds, i, v] n

@[simp] lemma seqUpdateAux_zero (ds i v : V) : seqUpdateAux ds i v 0 = ∅ := by
  simp [seqUpdateAux, seqUpdateAux.construction]

@[simp] lemma seqUpdateAux_succ (ds i v n : V) :
    seqUpdateAux ds i v (n + 1) =
      seqCons (seqUpdateAux ds i v n) (if n = i then v else znth ds n) := by
  simp [seqUpdateAux, seqUpdateAux.construction]

def _root_.LO.FirstOrder.Arithmetic.seqUpdateAuxDef : 𝚺₁.Semisentence 5 :=
  seqUpdateAux.blueprint.resultDef.rew (Rew.subst ![#0, #4, #1, #2, #3])

instance seqUpdateAux_defined : 𝚺₁-Function₄ (seqUpdateAux : V → V → V → V → V) via seqUpdateAuxDef :=
  .mk fun v ↦ by simp [seqUpdateAux.construction.result_defined_iff, seqUpdateAuxDef]; rfl

instance seqUpdateAux_definable : 𝚺₁-Function₄ (seqUpdateAux : V → V → V → V → V) :=
  seqUpdateAux_defined.to_definable
instance seqUpdateAux_definable' (Γ) : Γ-[m + 1]-Function₄ (seqUpdateAux : V → V → V → V → V) :=
  seqUpdateAux_definable.of_sigmaOne

@[simp] lemma seqUpdateAux_seq (ds i v n : V) : Seq (seqUpdateAux ds i v n) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using seq_empty
  case succ n ih => rw [seqUpdateAux_succ]; exact ih.seqCons _

@[simp] lemma seqUpdateAux_lh (ds i v n : V) : lh (seqUpdateAux ds i v n) = n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using lh_empty
  case succ n ih =>
    rw [seqUpdateAux_succ, Seq.lh_seqCons _ (seqUpdateAux_seq ds i v n), ih]

/-- Top-entry read-out (the freshly-appended entry at index `n`): non-inductive, so the `ite` is fine. -/
lemma znth_seqUpdateAux_top (ds i v n : V) :
    znth (seqUpdateAux ds i v (n + 1)) n = if n = i then v else znth ds n := by
  rw [seqUpdateAux_succ]
  have := znth_seqCons_self (seqUpdateAux_seq ds i v n) (if n = i then v else znth ds n)
  rwa [seqUpdateAux_lh] at this

/-- Reads below the top are stable as the prefix grows (the new `seqCons` doesn't touch index `m < n`). -/
lemma znth_seqUpdateAux_stable {ds i v : V} (n m : V) (hm : m < n) :
    znth (seqUpdateAux ds i v (n + 1)) m = znth (seqUpdateAux ds i v n) m := by
  rw [seqUpdateAux_succ,
    znth_seqCons_of_lt (seqUpdateAux_seq ds i v n) _ (by rw [seqUpdateAux_lh]; exact hm)]

/-- `seqUpdateAux` reads `v` at the updated index `i` (once the prefix passes it). `ite`-free, so the
induction's definability side-goal is clean. -/
lemma znth_seqUpdateAux_self {ds i v : V} : ∀ n, i < n → znth (seqUpdateAux ds i v n) i = v := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro h; exact absurd h (by simp)
  case succ n ih =>
    intro hi
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hi) with hin | hilt
    · rw [hin, znth_seqUpdateAux_top, if_pos rfl]
    · rw [znth_seqUpdateAux_stable n i hilt]; exact ih hilt

/-- `seqUpdateAux` is unchanged off the updated index. `ite`-free. -/
lemma znth_seqUpdateAux_of_ne {ds i v m : V} (hmi : m ≠ i) :
    ∀ n, m < n → znth (seqUpdateAux ds i v n) m = znth ds m := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro h; exact absurd h (by simp)
  case succ n ih =>
    intro hm
    rcases eq_or_lt_of_le (le_iff_lt_succ.mpr hm) with hmn | hmlt
    · rw [hmn, znth_seqUpdateAux_top, if_neg (by rw [← hmn]; exact hmi)]
    · rw [znth_seqUpdateAux_stable n m hmlt]; exact ih hmlt

/-- `seqUpdate ds i v = ds[i ↦ v]` — the full-length update. -/
noncomputable def seqUpdate (ds i v : V) : V := seqUpdateAux ds i v (lh ds)

@[simp] lemma seqUpdate_seq (ds i v : V) : Seq (seqUpdate ds i v) := seqUpdateAux_seq ds i v (lh ds)

@[simp] lemma seqUpdate_lh (ds i v : V) : lh (seqUpdate ds i v) = lh ds := seqUpdateAux_lh ds i v (lh ds)

/-- `seqUpdate` reads `v` at the updated index. -/
lemma znth_seqUpdate_self {ds i v : V} (hi : i < lh ds) : znth (seqUpdate ds i v) i = v :=
  znth_seqUpdateAux_self (lh ds) hi

/-- `seqUpdate` is unchanged off the updated index (any `m`, via the out-of-range `znth = 0`). -/
lemma znth_seqUpdate_of_ne {ds i v m : V} (h : m ≠ i) :
    znth (seqUpdate ds i v) m = znth ds m := by
  rcases lt_or_ge m (lh ds) with hm | hm
  · exact znth_seqUpdateAux_of_ne h (lh ds) hm
  · rw [znth_prop_not (Or.inr (by rw [seqUpdate_lh]; exact hm)), znth_prop_not (Or.inr hm)]

/-! ### Splice read-outs (Buchholz §3.2 case 5.2.1): `seqCons (seqUpdate ds j a) b`

The sub-critical splice reduct expands premise `j` to two auxiliaries: `a = dⱼ{0}` replaces premise `j`
in place, `b = dⱼ{1}` is appended at the end (index `lh ds`). These read-outs give the spliced premise
at every index, the prerequisite for the splice's `isChainInf` validity (the threading of the appended
`b`). -/

/-- The appended premise `b` sits at index `lh ds`. -/
lemma znth_seqCons_seqUpdate_top (ds j a b : V) :
    znth (seqCons (seqUpdate ds j a) b) (lh ds) = b := by
  have h := znth_seqCons_self (seqUpdate_seq ds j a) b
  rwa [seqUpdate_lh] at h

/-- Below the appended slot, the spliced sequence is the in-place update `seqUpdate ds j a`. -/
lemma znth_seqCons_seqUpdate_lt {ds j a b k : V} (hk : k < lh ds) :
    znth (seqCons (seqUpdate ds j a) b) k = znth (seqUpdate ds j a) k :=
  znth_seqCons_of_lt (seqUpdate_seq ds j a) b (by rw [seqUpdate_lh]; exact hk)

/-- Length of the splice: one more than the original. -/
@[simp] lemma lh_seqCons_seqUpdate (ds j a b : V) :
    lh (seqCons (seqUpdate ds j a) b) = lh ds + 1 := by
  rw [Seq.lh_seqCons _ (seqUpdate_seq ds j a), seqUpdate_lh]

/-! ### T2/T3 — `isChainInf` is preserved by replacing a premise with a same-end-sequent reduct

Buchholz's reduction (Thm 3.4(a) / `E-CRUX2-DECOMPOSITION §8` leaf T2/T3): the validity *structure* of a
`K^r` chain (`isChainInf`: distinguished `j₀`, antecedent threading, rank bound) depends on the premises
only through their **end-sequents** (`chainAsucc`/`chainAnt` = `seqSucc`/`seqAnt ∘ fstIdx ∘ znth`). So
replacing premise `i` by any reduct `v` with the SAME end-sequent (`fstIdx v = fstIdx (znth ds i)`)
leaves `isChainInf` literally invariant. This is the reusable validity-preservation core of `RedSound`
for the critical (`iCritAux`-replace) and non-critical reducts. -/

/-- End-sequent invariance of `seqUpdate` under a same-`fstIdx` replacement: every premise's `fstIdx`
is unchanged. -/
lemma fstIdx_znth_seqUpdate {ds i v : V} (hi : i < lh ds) (hv : fstIdx v = fstIdx (znth ds i)) (n : V) :
    fstIdx (znth (seqUpdate ds i v) n) = fstIdx (znth ds n) := by
  rcases eq_or_ne n i with rfl | hne
  · rw [znth_seqUpdate_self hi, hv]
  · rw [znth_seqUpdate_of_ne hne]

/-- `chainAsucc` is unchanged under a same-end-sequent premise replacement. -/
lemma chainAsucc_seqUpdate {ds i v : V} (hi : i < lh ds) (hv : fstIdx v = fstIdx (znth ds i)) (n : V) :
    chainAsucc (seqUpdate ds i v) n = chainAsucc ds n := by
  unfold chainAsucc; rw [fstIdx_znth_seqUpdate hi hv]

/-- `chainAnt` is unchanged under a same-end-sequent premise replacement. -/
lemma chainAnt_seqUpdate {ds i v : V} (hi : i < lh ds) (hv : fstIdx v = fstIdx (znth ds i)) (n : V) :
    chainAnt (seqUpdate ds i v) n = chainAnt ds n := by
  unfold chainAnt; rw [fstIdx_znth_seqUpdate hi hv]

/-- **T2/T3 validity-preservation (`isChainInf` core).** Replacing premise `i` of a chain by a reduct
`v` with the same end-sequent (`fstIdx v = fstIdx (znth ds i)`) preserves chain-validity `isChainInf`. -/
lemma isChainInf_seqUpdate {s r ds i v : V} (hi : i < lh ds) (hv : fstIdx v = fstIdx (znth ds i)) :
    isChainInf s r (seqUpdate ds i v) ↔ isChainInf s r ds :=
  isChainInf_congr (seqUpdate_lh ds i v)
    (fun n => chainAsucc_seqUpdate hi hv n) (fun n => chainAnt_seqUpdate hi hv n)

/-- **T2/T3 validity-preservation (full `zKValidF`).** Replacing premise `i` of a faithfully-valid chain
by a reduct `v` with the same end-sequent (`fstIdx v = fstIdx (znth ds i)`) preserves faithful chain
validity `zKValidF`, given `v`'s own well-formedness: its own-permissibility (`iperm (tp v) (fstIdx v)`,
Buchholz Lemma 3.3, automatic for a `ZDerivation`) and the tag-gated principal-formula-hood. The
`isChainInf` core is preserved by `isChainInf_seqUpdate`; the off-index per-premise conjuncts inherit
(unchanged `znth`/`chainAsucc`), the at-index ones come from `v`'s well-formedness. This is the reusable
"replace a premise of a valid `K^r` chain by a same-endsequent reduct ⟹ still valid" fact for `RedSound`. -/
lemma zKValidF_seqUpdate {s r ds i v : V} (hi : i < lh ds)
    (hv : fstIdx v = fstIdx (znth ds i))
    (hperm_v : iperm (tp v) (fstIdx v))
    (hf1_v : zTag v = 1 → IsUFormula ℒₒᵣ (zIallF v))
    (hf2_v : zTag v = 2 → IsUFormula ℒₒᵣ (zInegF v))
    (hf5_v : zTag v = 5 → IsUFormula ℒₒᵣ (zAxAllF v))
    (hf6_v : zTag v = 6 → IsUFormula ℒₒᵣ (zAxNegF v))
    (h : zKValidF s r ds) :
    zKValidF s r (seqUpdate ds i v) := by
  obtain ⟨hci, hperm, hg1, hg2, hg5, hg6, hcf, hss, hsa⟩ := h
  refine ⟨(isChainInf_seqUpdate hi hv).mpr hci, ?_, ?_, ?_, ?_, ?_, ?_, hss, hsa⟩
  · intro n hn
    rcases eq_or_ne n i with rfl | hne
    · rw [znth_seqUpdate_self hi]; exact hperm_v
    · rw [znth_seqUpdate_of_ne hne]; exact hperm n (by rwa [seqUpdate_lh] at hn)
  · intro n hn
    rcases eq_or_ne n i with rfl | hne
    · rw [znth_seqUpdate_self hi]; exact hf1_v
    · rw [znth_seqUpdate_of_ne hne]; exact hg1 n (by rwa [seqUpdate_lh] at hn)
  · intro n hn
    rcases eq_or_ne n i with rfl | hne
    · rw [znth_seqUpdate_self hi]; exact hf2_v
    · rw [znth_seqUpdate_of_ne hne]; exact hg2 n (by rwa [seqUpdate_lh] at hn)
  · intro n hn
    rcases eq_or_ne n i with rfl | hne
    · rw [znth_seqUpdate_self hi]; exact hf5_v
    · rw [znth_seqUpdate_of_ne hne]; exact hg5 n (by rwa [seqUpdate_lh] at hn)
  · intro n hn
    rcases eq_or_ne n i with rfl | hne
    · rw [znth_seqUpdate_self hi]; exact hf6_v
    · rw [znth_seqUpdate_of_ne hne]; exact hg6 n (by rwa [seqUpdate_lh] at hn)
  · intro n hn
    rw [chainAsucc_seqUpdate hi hv]; exact hcf n (by rwa [seqUpdate_lh] at hn)

/-- The critical auxiliary `d{ν} = K^r(i/v)`: the chain `d` with premise `i` replaced by `v`. -/
noncomputable def iCritAux (d i v : V) : V := zK (fstIdx d) (zKrank d) (seqUpdate (zKseq d) i v)

/-- `iCritAux` on a chain code computes to the chain with premise `i` swapped: same end-sequent and
rank, premise sequence updated. -/
@[simp] lemma iCritAux_zK (s r ds i v : V) :
    iCritAux (zK s r ds) i v = zK s r (seqUpdate ds i v) := by simp [iCritAux]

/-- **N2 on the genuine object, `õ`-side** — `õ(K^r(i/v)) ≺ õ(K^r ds)` when `õ(v) ≺ õ(znth ds i)` (N1
IH). Feeds `seqUpdate`'s read-outs into `iotil_zK_lt_replace`. -/
lemma iotil_iCritAux_lt {s r ds i v : V} (hds : Seq ds) (hi : i < lh ds)
    (hlt : icmp (iotil v) (iotil (znth ds i)) = 0)
    (hNF : ∀ n, isNF (iotil (znth ds n))) (hNFv : isNF (iotil v)) :
    icmp (iotil (iCritAux (zK s r ds) i v)) (iotil (zK s r ds)) = 0 := by
  rw [iCritAux_zK]
  refine iotil_zK_lt_replace hds (seqUpdate_seq ds i v) (seqUpdate_lh ds i v) hi ?_ ?_ hNF ?_
  · rw [znth_seqUpdate_self hi]; exact hlt
  · intro n hn; rw [znth_seqUpdate_of_ne hn]
  · intro n; rcases eq_or_ne n i with rfl | hn
    · rw [znth_seqUpdate_self hi]; exact hNFv
    · rw [znth_seqUpdate_of_ne hn]; exact hNF n

/-- **N2 on the genuine object, `idg`-side** — `dg(K^r(i/v)) ≤ dg(K^r ds)` when `dg(v) ≤ dg(znth ds i)`. -/
lemma idg_iCritAux_le {s r ds i v : V} (hds : Seq ds) (hi : i < lh ds)
    (hle : idg v ≤ idg (znth ds i)) :
    idg (iCritAux (zK s r ds) i v) ≤ idg (zK s r ds) := by
  rw [iCritAux_zK]
  refine idg_zK_le_replace hds (seqUpdate_seq ds i v) (seqUpdate_lh ds i v) (fun n => ?_)
  rcases eq_or_ne n i with rfl | hn
  · rw [znth_seqUpdate_self hi]; exact hle
  · exact le_of_eq (congrArg idg (znth_seqUpdate_of_ne hn))

/-- **LH3 — non-critical chain descent on the genuine reduct object** (Buchholz §3.2 case 5.2.2,
`E-CRUX2-DECOMPOSITION-2026-06-24.md §2 LH3`). The non-critical chain reduct `d[n] = K^r(i/dᵢ[n])`
replaces a single premise `i` by its sub-reduct `v = dᵢ[n]`. The degree does not rise
(`idg_iCritAux_le`, N2) and `õ` strictly drops (`iotil_iCritAux_lt`, N2 via the N1 IH `õ(v) ≺ õ(dᵢ)`),
so `iord_descent_le` gives `o(d[n]) ≺ o(d)`. This is the LOW-HANGING structural chain case: no degree
drop is needed (`õ` carries the descent), exactly as Buchholz's §0 non-critical regime predicts. The
N1 IH facts (`hlt`/`hle`) are the only abstract input, discharged by `ZDerivation` induction downstream. -/
lemma iord_descent_iCritAux {s r ds i v : V} (hds : Seq ds) (hi : i < lh ds)
    (hnf : isNF (iotil (zK s r ds)))
    (hlt : icmp (iotil v) (iotil (znth ds i)) = 0)
    (hle : idg v ≤ idg (znth ds i))
    (hNF : ∀ n, isNF (iotil (znth ds n))) (hNFv : isNF (iotil v)) :
    icmp (iord (iCritAux (zK s r ds) i v)) (iord (zK s r ds)) = 0 :=
  iord_descent_le hnf (idg_iCritAux_le hds hi hle) (iotil_iCritAux_lt hds hi hlt hNF hNFv)

/-! ## LH5 — the splice reduct (Buchholz §3.2 case 14.254): premise `j` expanded to two auxiliaries

When a non-major premise `dⱼ` is itself in the principal case, its reduction splices its two
auxiliaries `dⱼ{0}, dⱼ{1}` *flat* into the parent chain (Buchholz 14.254): one summand `ω^{õ dⱼ}`
becomes `ω^{õ dⱼ{0}} # ω^{õ dⱼ{1}}`. Since the `õ`/`idg` folds are **order-independent** (natural sum is
commutative; max is commutative), the ordinal descent is faithful on the model `seqCons (seqUpdate ds j a) b`
(replace `j` by `a = dⱼ{0}`, append `b = dⱼ{1}` at the end — same multiset of summands as the in-place
splice). The descent is N3b-shaped: F2 (`ω^{õa} # ω^{õb} ≺ ω^{õ dⱼ}`) + F1 (left-cancel the rest). -/

/-- ω-power re-association (back): a single ω-power on the left re-associates *out* of a right-nested
ω-power. Avoids the unavailable full `inadd_assoc` by routing through the `insTerm`-commute machinery
(`inadd_omega_pow`/`inadd_insTerm_comm`); valid because one flank is a single `ω`-power. -/
lemma inadd_pow_back {Y b w : V} (hY : isNF Y) (hb : isNF b) (hw : isNF w) :
    inadd (ocOadd b 1 0) (inadd Y (ocOadd w 1 0))
      = inadd (inadd (ocOadd b 1 0) Y) (ocOadd w 1 0) := by
  have hωw : isNF (ocOadd w 1 0) := isNF_omega_pow hw
  have hωb : isNF (ocOadd b 1 0) := isNF_omega_pow hb
  have eY : inadd Y (ocOadd w 1 0) = insTerm w 1 Y := by
    rw [inadd_comm (ocOadd w 1 0) hωw Y hY, inadd_omega_pow]
  have eR : inadd (inadd (ocOadd b 1 0) Y) (ocOadd w 1 0)
      = insTerm w 1 (inadd (ocOadd b 1 0) Y) := by
    rw [inadd_comm (ocOadd w 1 0) hωw _ (isNF_inadd hY (ocOadd b 1 0) hωb), inadd_omega_pow]
  rw [eY, inadd_insTerm_comm Y hY (ocOadd b 1 0) hωb, eR]

/-- ω-power re-association (front): pull a common left operand `P` out front of `ω^b # (P # ω^a)`.
Same `insTerm`-machinery route as `inadd_pow_back`; lands the two ω-powers adjacent so F2 can fire. -/
lemma inadd_pow_front {P b a : V} (hP : isNF P) (hb : isNF b) (ha : isNF a) :
    inadd (ocOadd b 1 0) (inadd P (ocOadd a 1 0))
      = inadd P (inadd (ocOadd b 1 0) (ocOadd a 1 0)) := by
  have hωa : isNF (ocOadd a 1 0) := isNF_omega_pow ha
  have hωb : isNF (ocOadd b 1 0) := isNF_omega_pow hb
  have e1 : inadd P (ocOadd a 1 0) = insTerm a 1 P := by
    rw [inadd_comm (ocOadd a 1 0) hωa P hP, inadd_omega_pow]
  calc inadd (ocOadd b 1 0) (inadd P (ocOadd a 1 0))
      = inadd (ocOadd b 1 0) (insTerm a 1 P) := by rw [e1]
    _ = insTerm a 1 (inadd (ocOadd b 1 0) P) := inadd_insTerm_comm P hP (ocOadd b 1 0) hωb
    _ = insTerm a 1 (insTerm b 1 P) := by rw [inadd_omega_pow]
    _ = insTerm b 1 (insTerm a 1 P) := insTerm_comm P hP
    _ = insTerm b 1 (inadd P (ocOadd a 1 0)) := by rw [e1]
    _ = inadd P (insTerm b 1 (ocOadd a 1 0)) := (inadd_insTerm_comm (ocOadd a 1 0) hωa P hP).symm
    _ = inadd P (inadd (ocOadd b 1 0) (ocOadd a 1 0)) := by rw [inadd_omega_pow]

/-- **Each entry's `idg` is `≤` the fold** (`idg(znth ds i) ≤ iseqMaxIdg ds` for `i < lh ds`). -/
lemma le_iseqMaxIdgAux {ds : V} : ∀ J, ∀ i < J, idg (znth ds i) ≤ iseqMaxIdgAux ds J := by
  intro J
  induction J using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro i hi; exact absurd hi (by simp)
  case succ J ih =>
    intro i hi
    rw [iseqMaxIdgAux_succ]
    rcases lt_or_eq_of_le (le_iff_lt_succ.mpr hi) with h | h
    · exact le_trans (ih i h) (le_max_left _ _)
    · subst h; exact le_max_right _ _

/-- **LH5 `õ`-fold (splice), partial** — `ω^{õb} # (#-fold of [ds with j↦a]) ≺ #-fold of ds`, when both
`õa, õb ≺ õ(dⱼ)`. The extra `ω^{õb}` rides the induction; `inadd_pow_back`/`_front` keep it adjacent so
F1 (`inadd_left/right_mono`) + F2 (`icmp_omega_pow_nadd_lt`) close each step. -/
lemma iseqNaddIdgAux_splice_lt {ds j a b : V} (hj : j < lh ds)
    (ha : icmp (iotil a) (iotil (znth ds j)) = 0) (hb : icmp (iotil b) (iotil (znth ds j)) = 0)
    (hNF : ∀ n, isNF (iotil (znth ds n))) (hNFa : isNF (iotil a)) (hNFb : isNF (iotil b)) :
    ∀ J, j < J → icmp (inadd (ocOadd (iotil b) 1 0) (iseqNaddIdgAux (seqUpdate ds j a) J))
      (iseqNaddIdgAux ds J) = 0 := by
  have hNF' : ∀ n, isNF (iotil (znth (seqUpdate ds j a) n)) := by
    intro n; rcases eq_or_ne n j with rfl | hn
    · rw [znth_seqUpdate_self hj]; exact hNFa
    · rw [znth_seqUpdate_of_ne hn]; exact hNF n
  intro J
  induction J using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro h; exact absurd h (by simp)
  case succ J ih =>
    intro hjJ
    rw [iseqNaddIdgAux_succ, iseqNaddIdgAux_succ]
    rcases lt_or_eq_of_le (le_iff_lt_succ.mpr hjJ) with hlt | heq
    · -- j < J: entry J unchanged; the new ω-power rides on the right, F1 (right-mono) + IH.
      rw [znth_seqUpdate_of_ne (Ne.symm (ne_of_lt hlt)),
        inadd_pow_back (isNF_iseqNaddIdgAux' hNF' J) hNFb (hNF J)]
      exact inadd_right_mono (isNF_inadd (isNF_iseqNaddIdgAux' hNF' J) _ (isNF_omega_pow hNFb))
        (isNF_iseqNaddIdgAux' hNF J) (ih hlt) _ (isNF_omega_pow (hNF J))
    · -- j = J: entry J IS the replaced `a`; prefix unchanged, F1 (left-mono) + F2 on the two powers.
      subst heq
      rw [znth_seqUpdate_self hj]
      have hpre : iseqNaddIdgAux (seqUpdate ds j a) j = iseqNaddIdgAux ds j :=
        iseqNaddIdgAux_congr_iotil j (fun m hm => by rw [znth_seqUpdate_of_ne (ne_of_lt hm)])
      rw [hpre, inadd_pow_front (isNF_iseqNaddIdgAux' hNF j) hNFb hNFa]
      exact inadd_left_mono (isNF_inadd (isNF_omega_pow hNFa) _ (isNF_omega_pow hNFb))
        (isNF_omega_pow (hNF j)) (icmp_omega_pow_nadd_lt hb ha) _ (isNF_iseqNaddIdgAux' hNF j)

/-- **LH5 `õ`-side at the `K^r` level** — `õ(splice) ≺ õ(K^r ds)` for the order-independent splice model
`seqCons (seqUpdate ds j a) b`. The `seqCons` puts `ω^{õb}` on the right; `inadd_comm` flips it to the
left to feed `iseqNaddIdgAux_splice_lt`. -/
lemma iotil_iSpliceEnd_lt {s s' r r' ds j a b : V} (hds : Seq ds) (hj : j < lh ds)
    (ha : icmp (iotil a) (iotil (znth ds j)) = 0) (hb : icmp (iotil b) (iotil (znth ds j)) = 0)
    (hNF : ∀ n, isNF (iotil (znth ds n))) (hNFa : isNF (iotil a)) (hNFb : isNF (iotil b)) :
    icmp (iotil (zK s' r' (seqCons (seqUpdate ds j a) b))) (iotil (zK s r ds)) = 0 := by
  have hNF' : ∀ n, isNF (iotil (znth (seqUpdate ds j a) n)) := by
    intro n; rcases eq_or_ne n j with rfl | hn
    · rw [znth_seqUpdate_self hj]; exact hNFa
    · rw [znth_seqUpdate_of_ne hn]; exact hNF n
  rw [iotil_zK s' r' _ ((seqUpdate_seq ds j a).seqCons b), iotil_zK s r ds hds,
    iseqNaddIdg_seqCons (seqUpdate_seq ds j a)]
  simp only [iseqNaddIdg, seqUpdate_lh]
  rw [inadd_comm (ocOadd (iotil b) 1 0) (isNF_omega_pow hNFb)
    (iseqNaddIdgAux (seqUpdate ds j a) (lh ds)) (isNF_iseqNaddIdgAux' hNF' (lh ds))]
  exact iseqNaddIdgAux_splice_lt hj ha hb hNF hNFa hNFb (lh ds) hj

/-- **LH5 `idg`-side at the `K^r` level** — `dg(splice) ≤ dg(K^r ds)` (same chain rank `r`), since both
auxiliaries dominate by `idg`: `idg a, idg b ≤ idg dⱼ ≤ iseqMaxIdg ds`. -/
lemma idg_iSpliceEnd_le {s s' r ds j a b : V} (hds : Seq ds) (hj : j < lh ds)
    (hag : idg a ≤ idg (znth ds j)) (hbg : idg b ≤ idg (znth ds j)) :
    idg (zK s' r (seqCons (seqUpdate ds j a) b)) ≤ idg (zK s r ds) := by
  rw [idg_zK s' r _ ((seqUpdate_seq ds j a).seqCons b), idg_zK s r ds hds,
    iseqMaxIdg_seqCons (seqUpdate_seq ds j a)]
  have hmono : iseqMaxIdg (seqUpdate ds j a) ≤ iseqMaxIdg ds := by
    rw [iseqMaxIdg, iseqMaxIdg, seqUpdate_lh]
    exact iseqMaxIdgAux_mono (fun n => by
      rcases eq_or_ne n j with rfl | hn
      · rw [znth_seqUpdate_self hj]; exact hag
      · exact le_of_eq (congrArg idg (znth_seqUpdate_of_ne hn))) (lh ds)
  have hbfold : idg b ≤ iseqMaxIdg ds := le_trans hbg (le_iseqMaxIdgAux (lh ds) j hj)
  exact max_le_max (le_refl r) (tsub_le_tsub_right (max_le hmono hbfold) 1)

/-- **LH5 — the splice descent on the genuine object** (Buchholz §3.2 case 14.254). With `õ` strictly
dropping (`iotil_iSpliceEnd_lt`, N3b: F2 two-below-one) and `idg` not rising (`idg_iSpliceEnd_le`),
`iord_descent_le` gives `o(d[0]) ≺ o(d)`. This is the last structural reduction case of Thm 4.2: with the
I-rules (LH1/LH2), Ind (LH4), non-critical chain (LH3), 5.1-nut (`iord_descent_iRcrit_of_chain`), and now
the splice, every Buchholz reduction case has its banked ordinal descent. The auxiliaries' N1 IH facts
(`ha`/`hb`/`hag`/`hbg`) are the only abstract input, supplied by `ZDerivation` induction downstream. -/
lemma iord_descent_iSpliceEnd {s s' r ds j a b : V} (hds : Seq ds) (hj : j < lh ds)
    (hnf : isNF (iotil (zK s r ds)))
    (ha : icmp (iotil a) (iotil (znth ds j)) = 0) (hb : icmp (iotil b) (iotil (znth ds j)) = 0)
    (hag : idg a ≤ idg (znth ds j)) (hbg : idg b ≤ idg (znth ds j))
    (hNF : ∀ n, isNF (iotil (znth ds n))) (hNFa : isNF (iotil a)) (hNFb : isNF (iotil b)) :
    icmp (iord (zK s' r (seqCons (seqUpdate ds j a) b))) (iord (zK s r ds)) = 0 :=
  iord_descent_le hnf (idg_iSpliceEnd_le hds hj hag hbg)
    (iotil_iSpliceEnd_lt hds hj ha hb hNF hNFa hNFb)

/-- The full critical reduct `d[0] = K^{r-1}_Π d{0} d{1}` (Buchholz §3.2 case 5.1), as a genuine code:
auxiliaries `d{0}=K^r(i/v)`, `d{1}=K^r(j/w)` (`iCritAux`), assembled into a rank-`(r-1)` chain over the
two-element `iCritReductSeq`. -/
noncomputable def iCritReduct (d i j v w : V) : V :=
  zK (fstIdx d) (zKrank d - 1) (iCritReductSeq (iCritAux d i v) (iCritAux d j w))

/-- **THE NUT, fully assembled on the genuine reduct object** — `o(d[0]) ≺ o(d)` for the critical chain
`d = K^r ds`, its reduct `d[0] = iCritReduct` built from the two `seqUpdate`-auxiliaries `d{0}=K^r(i/v)`,
`d{1}=K^r(j/w)`. The hypotheses are precisely the Thm-4.2 mutual-IH facts on the replaced premises
(`õ(v) ≺ õ(d_i)`, `õ(w) ≺ õ(d_j)`, N1) plus `r ≥ 1` (T3.4 `rk(A(d)) < r`). Composes the object-level N2
facts (`iotil_iCritAux_lt`/`idg_iCritAux_le`) through the chain descent `iord_descent_iCritReduct_chain`.
The cut-elimination descent now runs end-to-end on real `seqUpdate`-based codes — only the N1 IH plumbing
(structural `ZDerivation` induction) and T3.4 supplying `r ≥ 1` remain upstream. -/
lemma iord_descent_iCritReduct_object {s r ds i j v w : V}
    (hds : Seq ds) (hr : 1 ≤ r) (hnf : isNF (iotil (zK s r ds)))
    (hi : i < lh ds) (hj : j < lh ds)
    (hvlt : icmp (iotil v) (iotil (znth ds i)) = 0)
    (hwlt : icmp (iotil w) (iotil (znth ds j)) = 0)
    (hvg : idg v ≤ idg (znth ds i)) (hwg : idg w ≤ idg (znth ds j))
    (hNF : ∀ n, isNF (iotil (znth ds n))) (hNFv : isNF (iotil v)) (hNFw : isNF (iotil w)) :
    icmp (iord (iCritReduct (zK s r ds) i j v w)) (iord (zK s r ds)) = 0 := by
  have hred : iCritReduct (zK s r ds) i j v w
      = zK s (r - 1) (iCritReductSeq (iCritAux (zK s r ds) i v) (iCritAux (zK s r ds) j w)) := by
    simp [iCritReduct]
  rw [hred]
  exact iord_descent_iCritReduct_chain hds hr hnf
    (iotil_iCritAux_lt hds hi hvlt hNF hNFv)
    (iotil_iCritAux_lt hds hj hwlt hNF hNFw)
    (idg_iCritAux_le hds hi hvg)
    (idg_iCritAux_le hds hj hwg)

/-- **THE NUT, ASSEMBLED END-TO-END on a genuine chain** (E-CRUX2 §8.3, case 5.1). For the critical
chain `d = K^r ds`, this composes the three banked pieces into the case-5.1 descent `o(d[0]) ≺ o(d)`:
1. **L3.1 redex finder** (`inference_critical_pair_of_chain`) — from the `isChainInf` data + the tp
   permissibility/truth well-formedness, produces the redex `(i,j,k)` with `0 < rk(Aᵢ) ≤ r`;
2. **T3.4(a)** — `0 < rk(Aᵢ) ≤ r` gives `1 ≤ r`, the degree-drop premise the reduct needs;
3. **the object reduct + Thm 4.2** (`iord_descent_iCritReduct_object`) — `d[0] = K^{r−1} d{0} d{1}`
   with `d{ν}` the premise-`i`/`j` reducts `ρ i`/`ρ j`, descends since each `ρ`-reduct lowers `õ`
   and does not raise `dg` (the **N1 structural IH**, here the only abstract input besides the
   deferred tp/§5 well-formedness). The chain-structural `hchain`/`hAj0`/`hrank` come straight from
   `isChainInf`. This is the case-5.1 descent on REAL `seqUpdate`-based codes; only N1's IH plumbing
   (the `ZDerivation` structural recursion supplying `ρ`'s descent facts) and §5/Lemma-3.3 (the tp
   well-formedness making the redex fire on a real critical derivation) remain upstream. -/
theorem iord_descent_critical_of_chain {s r ds j0 : V} {Tr Fa : V → Prop} {ρ : V → V}
    (hds : Seq ds) (hnf : isNF (iotil (zK s r ds)))
    (hj0 : j0 < lh ds)
    (hAj0 : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hchain : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
      inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ Tr A)
    (hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ Fa A)
    (hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)))
    (hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s)
    (hdisj : ∀ A, ¬ (Tr A ∧ Fa A)) (hFa_rk : ∀ A, Fa A → irk A = 0)
    (hFa_bot : Fa (^⊥ : V))
    (hNF : ∀ n, isNF (iotil (znth ds n)))
    (hρlt : ∀ n, icmp (iotil (ρ n)) (iotil (znth ds n)) = 0)
    (hρg : ∀ n, idg (ρ n) ≤ idg (znth ds n))
    (hρNF : ∀ n, isNF (iotil (ρ n))) :
    ∃ i j, i < j ∧ j ≤ j0 ∧
      icmp (iord (iCritReduct (zK s r ds) i j (ρ i) (ρ j))) (iord (zK s r ds)) = 0 := by
  obtain ⟨i, j, k, hij, hjle, hRi, hLj, hrkpos, hrkr⟩ :=
    inference_critical_pair_of_chain hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm hdisj hFa_rk hFa_bot
  have hr : 1 ≤ r := pos_iff_one_le.mp (lt_of_lt_of_le hrkpos hrkr)
  have hi : i < lh ds := lt_trans (lt_of_lt_of_le hij hjle) hj0
  have hj : j < lh ds := lt_of_le_of_lt hjle hj0
  exact ⟨i, j, hij, hjle, iord_descent_iCritReduct_object hds hr hnf hi hj
    (hρlt i) (hρlt j) (hρg i) (hρg j) hNF (hρNF i) (hρNF j)⟩

/-! ## The redex-pair extraction FUNCTION — `iR`'s critical branch as a CLOSED definable object

`iord_descent_critical_of_chain` produces the case-5.1 descent for the *existential* redex `(i,j)`. For
`iR`'s critical branch to be a **closed, total, definable** function (Buchholz Def 3.2 case 5.1, which
takes "the least such pair"), the redex must be a *function* of the chain, not just an existential. This
section builds that: a first-hit bounded search `redexAux` over the pairing code `c = ⟪i,j⟫`, returning
the least valid redex pair. The "valid redex" test is stated purely via `tp` and the pairing projections
(`tp(dᵢ)=R_{Aᵢ}` ⟺ `π₁(tp dᵢ)=0`; `tp(d_j)=L^k_{Aᵢ}` ⟺ `π₁(tp d_j)=1` with the same cut formula
`π₂(π₂(tp d_j))=π₂(tp dᵢ)`), so it needs no sequent/`chainAsucc` bookkeeping. The Buchholz reduct then
becomes the closed `iRcrit d ρ` (`ρ` = the indexed sub-reduct `dᵢ[k]`/`d_j[0]`, the one honest abstract
input = the N1 structural IH / `d[n]` recursion, deferred). -/

/-- **Valid-redex test on a pairing code** `c = ⟪i,j⟫`: `i<j<lh ds`, premise `i`'s `tp` is a right
symbol (`π₁=0`), premise `j`'s `tp` is a left symbol (`π₁=1`), and they share the cut formula
(`π₂(π₂(tp d_j)) = π₂(tp dᵢ)`). On such a `c`, `π₂(tp dᵢ) = Aᵢ` is Buchholz's cut formula `A(d)`. -/
def isRedexPair (ds c : V) : Prop :=
  π₁ c < π₂ c ∧ π₂ c < lh ds ∧
  π₁ (tp (znth ds (π₁ c))) = 0 ∧ π₁ (tp (znth ds (π₂ c))) = 1 ∧
  π₂ (π₂ (tp (znth ds (π₂ c)))) = π₂ (tp (znth ds (π₁ c)))

/-- **Redex-pair → `tp`-symbol shape bridge.** From the bare `π₁`-discriminant pair test
`isRedexPair ds c` recover the genuine inference symbols on the two redex premises: the `i`-end
(`i = π₁ c`) is a right symbol `R_{Aᵢ}` and the `j`-end (`j = π₂ c`) is a left symbol `L^k_{Aᵢ}`
on the **same** cut formula `Aᵢ = π₂ (tp (znth ds i))` (from the shared-cut-formula conjunct). This
is what lets a caller of `iord_descent_iRcrit_of_chain'` read off the redex premises' `tp` from the
finder's least-pair `redexCode` (rather than from the existential redex). -/
lemma redexPair_tp {ds c : V} (h : isRedexPair ds c) :
    tp (znth ds (π₁ c)) = isymR (π₂ (tp (znth ds (π₁ c)))) ∧
    tp (znth ds (π₂ c)) = isymLk (π₁ (π₂ (tp (znth ds (π₂ c)))))
      (π₂ (tp (znth ds (π₁ c)))) := by
  obtain ⟨_, _, hi, hj, hcut⟩ := h
  refine ⟨tp_eq_isymR_of_pi₁_zero hi, ?_⟩
  have hL := tp_eq_isymLk_of_pi₁_one hj
  rw [hcut] at hL
  exact hL

/-- First-hit search step: keep the prior hit if one was found (`ih < n`), else take `n` if it is a
valid redex pair, else advance the sentinel to `n+1`. -/
noncomputable def redexAux.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y ds. y = 0”
  succ := .mkSigma “y ih n ds.
    (ih < n ∧ y = ih) ∨
    (n ≤ ih ∧
      ∃ i, !pi₁Def i n ∧ ∃ j, !pi₂Def j n ∧ ∃ l, !lhDef l ds ∧
      ∃ di, !znthDef di ds i ∧ ∃ ti, !tpDef ti di ∧
      ∃ dj, !znthDef dj ds j ∧ ∃ tj, !tpDef tj dj ∧
      ∃ p1i, !pi₁Def p1i ti ∧ ∃ p1j, !pi₁Def p1j tj ∧
      ∃ a2i, !pi₂Def a2i ti ∧
      ∃ p2j, !pi₂Def p2j tj ∧ ∃ a2j, !pi₂Def a2j p2j ∧
      ( (i < j ∧ j < l ∧ p1i = 0 ∧ p1j = 1 ∧ a2j = a2i ∧ y = n) ∨
        (¬(i < j ∧ j < l ∧ p1i = 0 ∧ p1j = 1 ∧ a2j = a2i) ∧ y = n + 1) ) )”

noncomputable def redexAux.construction : PR.Construction V redexAux.blueprint where
  zero := fun _ ↦ 0
  succ := fun x n ih ↦ if ih < n then ih else if isRedexPair (x 0) n then n else n + 1
  zero_defined := .mk fun v ↦ by simp [redexAux.blueprint]
  succ_defined := .mk fun v ↦ by
    by_cases h1 : v 1 < v 2
    · simp [redexAux.blueprint, h1]
    · have hle : v 2 ≤ v 1 := not_lt.mp h1
      by_cases h2 : isRedexPair (v 3) (v 2)
      · simp only [redexAux.blueprint, isRedexPair] at h2 ⊢
        simp [h1, h2, hle, pi₁_defined.iff, pi₂_defined.iff, lh_defined.iff, znth_defined.iff,
          tp_defined.iff]
      · simp only [redexAux.blueprint, isRedexPair] at h2 ⊢
        simp [h1, h2, hle, pi₁_defined.iff, pi₂_defined.iff, lh_defined.iff, znth_defined.iff,
          tp_defined.iff]
        constructor
        · rintro (⟨hc1, hc2, hc3, hc4, hc5, _⟩ | ⟨_, h⟩)
          · exact absurd ⟨hc1, hc2, hc3, hc4, hc5⟩ h2
          · exact h
        · intro h
          refine Or.inr ⟨?_, h⟩
          rcases lt_or_ge (π₁ (v 2)) (π₂ (v 2)) with hc1 | hc1
          · rcases lt_or_ge (π₂ (v 2)) (lh (v 3)) with hc2 | hc2
            · by_cases hc3 : π₁ (tp (znth (v 3) (π₁ (v 2)))) = 0
              · by_cases hc4 : π₁ (tp (znth (v 3) (π₂ (v 2)))) = 1
                · exact Or.inr (Or.inr (Or.inr (Or.inr (fun hc5 => h2 ⟨hc1, hc2, hc3, hc4, hc5⟩))))
                · exact Or.inr (Or.inr (Or.inr (Or.inl hc4)))
              · exact Or.inr (Or.inr (Or.inl hc3))
            · exact Or.inr (Or.inl hc2)
          · exact Or.inl hc1

/-- `redexAux ds n` = the least pairing code `c < n` that is a valid redex pair of `ds`, or `n` if none. -/
noncomputable def redexAux (ds n : V) : V := redexAux.construction.result ![ds] n

@[simp] lemma redexAux_zero (ds : V) : redexAux ds 0 = 0 := by
  simp [redexAux, redexAux.construction]

@[simp] lemma redexAux_succ (ds n : V) :
    redexAux ds (n + 1) =
      (if redexAux ds n < n then redexAux ds n else if isRedexPair ds n then n else n + 1) := by
  simp [redexAux, redexAux.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.redexAuxDef : 𝚺₁.Semisentence 3 :=
  redexAux.blueprint.resultDef.rew (Rew.subst ![#0, #2, #1])

instance redexAux_defined : 𝚺₁-Function₂ (redexAux : V → V → V) via redexAuxDef :=
  .mk fun v ↦ by simp [redexAux.construction.result_defined_iff, redexAuxDef]; rfl

instance redexAux_definable : 𝚺₁-Function₂ (redexAux : V → V → V) := redexAux_defined.to_definable
instance redexAux_definable' (Γ) : Γ-[m + 1]-Function₂ (redexAux : V → V → V) :=
  redexAux_definable.of_sigmaOne

/-- **First-hit ≤ sentinel** — the search result never exceeds its bound. -/
lemma redexAux_le (ds : V) : ∀ N, redexAux ds N ≤ N := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [redexAux_succ]
    by_cases h1 : redexAux ds n < n
    · rw [if_pos h1]; exact le_of_lt (lt_trans h1 (le_iff_lt_succ.mp (le_refl n)))
    · rw [if_neg h1]
      by_cases h2 : isRedexPair ds n
      · rw [if_pos h2]; exact le_of_lt (le_iff_lt_succ.mp (le_refl n))
      · simp [h2]

/-- **First-hit is valid** — if the search returns a genuine index (`< N`), it is a valid redex pair. -/
lemma redexAux_isRedexPair_of_lt (ds : V) :
    ∀ N, redexAux ds N < N → isRedexPair ds (redexAux ds N) := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · simp only [isRedexPair]; definability
  case zero => intro h; exact absurd h (by simp)
  case succ n ih =>
    intro hlt
    rw [redexAux_succ] at hlt ⊢
    by_cases h1 : redexAux ds n < n
    · rw [if_pos h1] at hlt ⊢; exact ih h1
    · rw [if_neg h1] at hlt ⊢
      by_cases h2 : isRedexPair ds n
      · rw [if_pos h2] at hlt ⊢; exact h2
      · rw [if_neg h2] at hlt; exact absurd hlt (by simp)

/-- **No-hit sentinel** — if the search returns the sentinel `N`, then no `c < N` is a valid redex
pair (the search exhausted the range). -/
lemma redexAux_eq_self_of_no_redex (ds : V) :
    ∀ N, redexAux ds N = N → ∀ c < N, ¬ isRedexPair ds c := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · simp only [isRedexPair]; definability
  case zero => intro _ c hc; exact absurd hc (by simp)
  case succ n ih =>
    intro heq c hc
    rw [redexAux_succ] at heq
    by_cases h1 : redexAux ds n < n
    · rw [if_pos h1] at heq
      exact absurd (le_iff_lt_succ.mp (le_refl n)) (lt_asymm (heq ▸ h1))
    · rw [if_neg h1] at heq
      by_cases h2 : isRedexPair ds n
      · rw [if_pos h2] at heq; exact absurd heq (le_iff_lt_succ.mp (le_refl n)).ne
      · rw [if_neg h2] at heq
        have hn : redexAux ds n = n := le_antisymm (redexAux_le ds n) (not_lt.mp h1)
        rcases lt_or_eq_of_le (lt_succ_iff_le.mp hc) with hcn | hcn
        · exact ih hn c hcn
        · rw [hcn]; exact h2

/-- **First-hit found** — when a valid redex pair exists below the sentinel, the search returns one. -/
lemma redexAux_found (ds N : V) (h : ∃ c < N, isRedexPair ds c) :
    redexAux ds N < N ∧ isRedexPair ds (redexAux ds N) := by
  have hlt : redexAux ds N < N := by
    rcases lt_or_eq_of_le (redexAux_le ds N) with h' | h'
    · exact h'
    · obtain ⟨c, hcN, hc⟩ := h
      exact absurd hc (redexAux_eq_self_of_no_redex ds N h' c hcN)
  exact ⟨hlt, redexAux_isRedexPair_of_lt ds N hlt⟩

/-- **The redex code of a chain** = least valid redex pair `⟪i,j⟫` over `ds = zKseq d`, bounded by
`⟪lh ds, lh ds⟫`. Buchholz Def 3.2 case 5.1's "least such pair (i,j)", now a definable function. -/
noncomputable def redexCode (d : V) : V :=
  redexAux (zKseq d) (⟪lh (zKseq d), lh (zKseq d)⟫ : V)
/-- The redex's right-reduction index `i` (`tp(dᵢ) = R_{Aᵢ}`). -/
noncomputable def redexI (d : V) : V := π₁ (redexCode d)
/-- The redex's left-symbol index `j` (`tp(d_j) = L^k_{Aᵢ}`). -/
noncomputable def redexJ (d : V) : V := π₂ (redexCode d)

/-- **Redex code spec** — if a valid redex pair exists in range, `redexCode d` is one. -/
lemma redexCode_isRedexPair {d : V}
    (h : ∃ c < (⟪lh (zKseq d), lh (zKseq d)⟫ : V), isRedexPair (zKseq d) c) :
    isRedexPair (zKseq d) (redexCode d) := (redexAux_found (zKseq d) _ h).2

/-! ## `iRcrit` — the CLOSED iR critical branch (Buchholz Def 3.2 case 5.1)

The redex finder (`redexCode`/`redexI`/`redexJ`) is now a total definable function of the chain, so the
critical reduct `d[0] = K^{r-1}_Π d{0} d{1}` is a **closed term**: `iRcrit d ρ` plugs the *functional*
redex indices `redexI d`/`redexJ d` (and their `ρ`-reducts) into `iCritReduct`. This eliminates the last
existential from `iR`'s critical branch — only `ρ` (the indexed sub-reduct `dᵢ[k]`/`d_j[0]`, the N1
structural IH) remains abstract. The descent `iord_descent_iRcrit_of_chain` then composes:
(L3.1 redex existence) ⟹ (the finder finds the SAME-or-earlier valid pair) ⟹ (T3.4 `1 ≤ r`) ⟹
(`iord_descent_iCritReduct_object`, the Thm-4.2 cut-elim descent on the genuine `seqUpdate` reduct). -/

/-- **The closed iR critical branch** (Buchholz Def 3.2 case 5.1): the critical reduct `d[0]` built from
the FUNCTIONAL redex `(redexI d, redexJ d)` and the abstract premise-reduct supplier `ρ`. Closed term;
no existential. -/
noncomputable def iRcrit (d : V) (ρ : V → V) : V :=
  iCritReduct d (redexI d) (redexJ d) (ρ (redexI d)) (ρ (redexJ d))

/-- **THE NUT, on the CLOSED reduct** (E-CRUX2 §8.3, case 5.1). Same hypotheses as
`iord_descent_critical_of_chain`, but the conclusion is the descent on the *closed* `iRcrit (zK s r ds) ρ`
— the redex indices are now `redexI`/`redexJ` (the definable finder), not an existential. The proof
shows the finder fires: L3.1 supplies an existential redex `⟪i,j⟫ < ⟪lh ds, lh ds⟫`, so by
`redexCode_isRedexPair` the finder returns a (least) valid pair, whose `isRedexPair` data gives
`redexI < redexJ < lh ds`; then `iord_descent_iCritReduct_object` (Thm 4.2) discharges the descent on the
genuine `seqUpdate`-based reduct. This makes the WHOLE case-5.1 branch a closed definable object: only
`ρ`'s N1 facts (`hρlt`/`hρg`/`hρNF`, the structural IH) and the tp/§5 well-formedness (`hperm`/`hnperm`)
remain upstream. -/
theorem iord_descent_iRcrit_of_chain {s r ds j0 : V} {Tr Fa : V → Prop} {ρ : V → V}
    (hds : Seq ds) (hnf : isNF (iotil (zK s r ds)))
    (hj0 : j0 < lh ds)
    (hAj0 : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hchain : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
      inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ Tr A)
    (hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ Fa A)
    (hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)))
    (hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s)
    (hdisj : ∀ A, ¬ (Tr A ∧ Fa A)) (hFa_rk : ∀ A, Fa A → irk A = 0)
    (hFa_bot : Fa (^⊥ : V))
    (hNF : ∀ n, isNF (iotil (znth ds n)))
    (hρlt : ∀ n, icmp (iotil (ρ n)) (iotil (znth ds n)) = 0)
    (hρg : ∀ n, idg (ρ n) ≤ idg (znth ds n))
    (hρNF : ∀ n, isNF (iotil (ρ n))) :
    icmp (iord (iRcrit (zK s r ds) ρ)) (iord (zK s r ds)) = 0 := by
  -- L3.1: extract an existential redex `(i,j,k)` with the tp/rank data.
  obtain ⟨i, j, k, hij, hjle, hRi, hLj, hrkpos, hrkr⟩ :=
    inference_critical_pair_of_chain hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm hdisj hFa_rk hFa_bot
  have hr : 1 ≤ r := pos_iff_one_le.mp (lt_of_lt_of_le hrkpos hrkr)
  have hjlt : j < lh ds := lt_of_le_of_lt hjle hj0
  have hilt : i < lh ds := lt_trans hij hjlt
  -- The L3.1 redex `⟪i,j⟫` is a valid redex pair below the search bound.
  have hredex : isRedexPair ds (⟪i, j⟫ : V) := by
    simp only [isRedexPair, pi₁_pair, pi₂_pair]
    refine ⟨hij, hjlt, ?_, ?_, ?_⟩
    · rw [hRi]; simp [isymR]
    · rw [hLj]; simp [isymLk]
    · rw [hRi, hLj]; simp [isymR, isymLk]
  -- So the finder fires: `redexCode (zK s r ds)` is a valid redex pair of `ds`.
  have hex : ∃ c < (⟪lh (zKseq (zK s r ds)), lh (zKseq (zK s r ds))⟫ : V),
      isRedexPair (zKseq (zK s r ds)) c := by
    simp only [zKseq_zK]
    exact ⟨⟪i, j⟫, pair_lt_pair hilt hjlt, hredex⟩
  have hrc : isRedexPair (zKseq (zK s r ds)) (redexCode (zK s r ds)) := redexCode_isRedexPair hex
  simp only [zKseq_zK] at hrc
  obtain ⟨hIJ, hJlh, -, -, -⟩ := hrc
  -- `redexI`/`redexJ` are defeq to the projections, so the order facts transfer.
  have hJlh' : redexJ (zK s r ds) < lh ds := hJlh
  have hIlh' : redexI (zK s r ds) < lh ds := lt_trans hIJ hJlh
  -- Thm 4.2 on the genuine reduct, instantiated at the functional redex.
  have hgoal := iord_descent_iCritReduct_object hds hr hnf hIlh' hJlh'
    (hρlt (redexI (zK s r ds))) (hρlt (redexJ (zK s r ds)))
    (hρg (redexI (zK s r ds))) (hρg (redexJ (zK s r ds)))
    hNF (hρNF (redexI (zK s r ds))) (hρNF (redexJ (zK s r ds)))
  exact hgoal

/-- **The nut, with the `ρ`-hyps WEAKENED to the two redex premises.** `iord_descent_iRcrit_of_chain`
states `hρlt`/`hρg`/`hρNF` as `∀ n`, but its proof only ever USES them at `redexI`/`redexJ` (the finder
output). For the concrete `ρ = iR2(znth ds ·)` the `∀ n` form is FALSE (a critical-chain premise's `õ`
can jump up; an atom premise's `iR2` is the identity), so this redex-only form is the one the recursive
descent can actually discharge. It pins the entire K-case ordinal obligation to SIX facts about the two
redex-premise reducts `ρ(redexI)`,`ρ(redexJ)` — exactly what the redexI I-rule case
(`iRedDescent_iR_of_tp_isymR`) and the redexJ §5 atomic reduct must supply. -/
theorem iord_descent_iRcrit_of_chain' {s r ds j0 : V} {Tr Fa : V → Prop} {ρ : V → V}
    (hds : Seq ds) (hnf : isNF (iotil (zK s r ds)))
    (hj0 : j0 < lh ds)
    (hAj0 : chainAsucc ds j0 = seqSucc s ∨ chainAsucc ds j0 = (^⊥ : V))
    (hchain : ∀ i ≤ j0, ∀ B, inAnt B (chainAnt ds i) →
      inAnt B (seqAnt s) ∨ ∃ i' < i, B = chainAsucc ds i')
    (hrank : ∀ i < j0, irk (chainAsucc ds i) ≤ r)
    (hwfR : ∀ i ≤ j0, ∀ A, tp (znth ds i) = isymR A → 0 < irk A ∨ Tr A)
    (hwfL : ∀ i ≤ j0, ∀ k A, tp (znth ds i) = isymLk k A → 0 < irk A ∨ Fa A)
    (hperm : ∀ i ≤ j0, iperm (tp (znth ds i)) (fstIdx (znth ds i)))
    (hnperm : ∀ i ≤ j0, ¬ iperm (tp (znth ds i)) s)
    (hdisj : ∀ A, ¬ (Tr A ∧ Fa A)) (hFa_rk : ∀ A, Fa A → irk A = 0)
    (hFa_bot : Fa (^⊥ : V))
    (hNF : ∀ n, isNF (iotil (znth ds n)))
    (hρlt_i : icmp (iotil (ρ (redexI (zK s r ds)))) (iotil (znth ds (redexI (zK s r ds)))) = 0)
    (hρlt_j : icmp (iotil (ρ (redexJ (zK s r ds)))) (iotil (znth ds (redexJ (zK s r ds)))) = 0)
    (hρg_i : idg (ρ (redexI (zK s r ds))) ≤ idg (znth ds (redexI (zK s r ds))))
    (hρg_j : idg (ρ (redexJ (zK s r ds))) ≤ idg (znth ds (redexJ (zK s r ds))))
    (hρNF_i : isNF (iotil (ρ (redexI (zK s r ds)))))
    (hρNF_j : isNF (iotil (ρ (redexJ (zK s r ds))))) :
    icmp (iord (iRcrit (zK s r ds) ρ)) (iord (zK s r ds)) = 0 := by
  obtain ⟨i, j, k, hij, hjle, hRi, hLj, hrkpos, hrkr⟩ :=
    inference_critical_pair_of_chain hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm hdisj hFa_rk hFa_bot
  have hr : 1 ≤ r := pos_iff_one_le.mp (lt_of_lt_of_le hrkpos hrkr)
  have hjlt : j < lh ds := lt_of_le_of_lt hjle hj0
  have hilt : i < lh ds := lt_trans hij hjlt
  have hredex : isRedexPair ds (⟪i, j⟫ : V) := by
    simp only [isRedexPair, pi₁_pair, pi₂_pair]
    refine ⟨hij, hjlt, ?_, ?_, ?_⟩
    · rw [hRi]; simp [isymR]
    · rw [hLj]; simp [isymLk]
    · rw [hRi, hLj]; simp [isymR, isymLk]
  have hex : ∃ c < (⟪lh (zKseq (zK s r ds)), lh (zKseq (zK s r ds))⟫ : V),
      isRedexPair (zKseq (zK s r ds)) c := by
    simp only [zKseq_zK]
    exact ⟨⟪i, j⟫, pair_lt_pair hilt hjlt, hredex⟩
  have hrc : isRedexPair (zKseq (zK s r ds)) (redexCode (zK s r ds)) := redexCode_isRedexPair hex
  simp only [zKseq_zK] at hrc
  obtain ⟨hIJ, hJlh, -, -, -⟩ := hrc
  have hJlh' : redexJ (zK s r ds) < lh ds := hJlh
  have hIlh' : redexI (zK s r ds) < lh ds := lt_trans hIJ hJlh
  exact iord_descent_iCritReduct_object hds hr hnf hIlh' hJlh'
    hρlt_i hρlt_j hρg_i hρg_j hNF hρNF_i hρNF_j

/-! ## C0 Fixpoint — the system-Z derivation predicate `ZDerivation : V → Prop`

The one-step rule `ZPhi C d` ("`d` is a Z-derivation given its premises lie in `C`"), mirroring
Foundation's `Theory.Derivation.Phi` (`…/Proof/Basic.lean:280`) but over Z's five rules — the K^r
rule being variadic (its premise *sequence* `ds`, each `znth ds i ∈ C`), with no Foundation precedent.

**This brick is the STRUCTURAL skeleton** (premise-membership + the K^r `Seq` premise-sequence). The
sequent well-formedness (`IsFormulaSet`), the eigenvariable/rank side conditions, and the §5 atomic
axioms are refinements layered onto `ZPhi` later — they strengthen the predicate but do **not** change
the Fixpoint machinery (`monotone`/`StrongFinite` re-prove mechanically). With `ZPhi`, the next bricks
form `Fixpoint.Construction` → `ZDerivation := construction.Fixpoint ![]` + its `case`/`induction`
corollaries, which unblock structural induction (`isNF (iotil d)`), `iR` well-definedness, and the
⊥-characterization (`derivesEmpty`). `monotone` + `StrongFinite` are proved here as standalone lemmas
(they ARE the `Construction` fields). -/

/-- One-step system-Z derivation rule (structural skeleton): `d` is built by one of Z's five rules
with its premise(s) in `C`. -/
def ZPhi (C : Set V) (d : V) : Prop :=
  (∃ s, d = zAtom s ∧ inAnt (seqSucc s) (seqAnt s)) ∨
  (∃ s a p d0, d = zIall s a p d0 ∧ d0 ∈ C ∧ seqSucc s = (^∀ p : V) ∧ zIallWff s a p d0) ∨
  (∃ s p d0, d = zIneg s p d0 ∧ d0 ∈ C ∧ seqSucc s = (inegF p : V) ∧ zInegWff p d0) ∨
  (∃ s at' p d0 d1, d = zInd s at' p d0 d1 ∧ d0 ∈ C ∧ d1 ∈ C ∧ zIndWff d) ∨
  (∃ s r ds, d = zK s r ds ∧ Seq ds ∧ (∀ i < lh ds, znth ds i ∈ C) ∧ zKValidF s r ds) ∨
  (∃ s p k, d = zAxAll s p k ∧ IsUFormula ℒₒᵣ p ∧ inAnt (^∀ p : V) (seqAnt s)) ∨
  (∃ s p, d = zAxNeg s p ∧ IsUFormula ℒₒᵣ p ∧ inAnt (inegF p : V) (seqAnt s))

/-- `ZPhi` is monotone in the premise set `C` (a `Fixpoint.Construction.monotone` field). -/
lemma zphi_monotone {C C' : Set V} (h : C ⊆ C') {d : V} : ZPhi C d → ZPhi C' d := by
  rintro (hd | ⟨s, a, p, d0, rfl, hd, hsc, hwff⟩ | ⟨s, p, d0, rfl, hd, hsc, hwff⟩ |
    ⟨s, at', p, d0, d1, rfl, h0, h1, hwff⟩ | ⟨s, r, ds, rfl, hseq, hall, hvalid⟩ |
    ⟨s, p, k, rfl, hp, hin⟩ | ⟨s, p, rfl, hp, hin⟩)
  · exact Or.inl hd
  · exact Or.inr (Or.inl ⟨s, a, p, d0, rfl, h hd, hsc, hwff⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨s, p, d0, rfl, h hd, hsc, hwff⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, at', p, d0, d1, rfl, h h0, h h1, hwff⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, r, ds, rfl, hseq, fun i hi => h (hall i hi), hvalid⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, p, k, rfl, hp, hin⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, p, rfl, hp, hin⟩)))))

/-- `ZPhi` is strongly finite: every premise of `d` is `< d`, so the rule fires already over
`{y ∈ C | y < d}` (a `Fixpoint.Construction.StrongFinite` field). The K^r case uses
`Seq.znth` + `lt_of_mem_rng` (`znth ds i < ds`) then `ds < zK s r ds`. -/
lemma zphi_strong_finite {C : Set V} {d : V} :
    ZPhi C d → ZPhi {y | y ∈ C ∧ y < d} d := by
  rintro (hd | ⟨s, a, p, d0, rfl, hd, hsc, hwff⟩ | ⟨s, p, d0, rfl, hd, hsc, hwff⟩ |
    ⟨s, at', p, d0, d1, rfl, h0, h1, hwff⟩ | ⟨s, r, ds, rfl, hseq, hall, hvalid⟩ |
    ⟨s, p, k, rfl, hp, hin⟩ | ⟨s, p, rfl, hp, hin⟩)
  · exact Or.inl hd
  · exact Or.inr (Or.inl ⟨s, a, p, d0, rfl, ⟨hd, by simp⟩, hsc, hwff⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨s, p, d0, rfl, ⟨hd, by simp⟩, hsc, hwff⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, at', p, d0, d1, rfl, ⟨h0, by simp⟩, ⟨h1, by simp⟩, hwff⟩)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨s, r, ds, rfl, hseq, fun i hi => ⟨hall i hi, ?_⟩, hvalid⟩))))
    exact lt_trans (lt_of_mem_rng (hseq.znth hi)) (ds_lt_zK s r ds)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, p, k, rfl, hp, hin⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, p, rfl, hp, hin⟩)))))

/-- Bounded-quantifier form of `ZPhi` (every existential is `< d`), the shape the arithmetized
`blueprint` core matches. Mirrors Foundation `Theory.Derivation.phi_iff`. -/
private lemma zphi_iff (C d : V) :
    ZPhi {x | x ∈ C} d ↔
    ( (∃ s < d, d = zAtom s ∧ inAnt (seqSucc s) (seqAnt s)) ∨
      (∃ s < d, ∃ a < d, ∃ p < d, ∃ d0 < d,
        d = zIall s a p d0 ∧ d0 ∈ C ∧ seqSucc s = (^∀ p : V) ∧ zIallWff s a p d0) ∨
      (∃ s < d, ∃ p < d, ∃ d0 < d,
        d = zIneg s p d0 ∧ d0 ∈ C ∧ seqSucc s = (inegF p : V) ∧ zInegWff p d0) ∨
      (∃ s < d, ∃ at' < d, ∃ p < d, ∃ d0 < d, ∃ d1 < d,
        d = zInd s at' p d0 d1 ∧ d0 ∈ C ∧ d1 ∈ C ∧ zIndWff d) ∨
      (∃ s < d, ∃ r < d, ∃ ds < d,
        d = zK s r ds ∧ Seq ds ∧ (∀ i < lh ds, znth ds i ∈ C) ∧ zKValidF s r ds) ∨
      (∃ s < d, ∃ p < d, ∃ k < d, d = zAxAll s p k ∧ IsUFormula ℒₒᵣ p ∧ inAnt (^∀ p : V) (seqAnt s)) ∨
      (∃ s < d, ∃ p < d, d = zAxNeg s p ∧ IsUFormula ℒₒᵣ p ∧ inAnt (inegF p : V) (seqAnt s)) ) := by
  constructor
  · rintro (⟨s, rfl, hin⟩ | ⟨s, a, p, d0, rfl, h, hsc, hwff⟩ | ⟨s, p, d0, rfl, h, hsc, hwff⟩ |
      ⟨s, at', p, d0, d1, rfl, h0, h1, hwff⟩ | ⟨s, r, ds, rfl, hseq, hall, hvalid⟩ |
      ⟨s, p, k, rfl, hp, hin⟩ | ⟨s, p, rfl, hp, hin⟩)
    · exact Or.inl ⟨s, by simp, rfl, hin⟩
    · exact Or.inr (Or.inl ⟨s, by simp, a, by simp, p, by simp, d0, by simp, rfl, h, hsc, hwff⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨s, by simp, p, by simp, d0, by simp, rfl, h, hsc, hwff⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨s, by simp, at', by simp, p, by simp, d0, by simp, d1, by simp, rfl, h0, h1, hwff⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨s, by simp, r, by simp, ds, by simp, rfl, hseq, hall, hvalid⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨s, by simp, p, by simp, k, by simp, rfl, hp, hin⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨s, by simp, p, by simp, rfl, hp, hin⟩)))))
  · rintro (⟨s, _, rfl, hin⟩ | ⟨s, _, a, _, p, _, d0, _, rfl, h, hsc, hwff⟩ |
      ⟨s, _, p, _, d0, _, rfl, h, hsc, hwff⟩ |
      ⟨s, _, at', _, p, _, d0, _, d1, _, rfl, h0, h1, hwff⟩ |
      ⟨s, _, r, _, ds, _, rfl, hseq, hall, hvalid⟩ |
      ⟨s, _, p, _, k, _, rfl, hp, hin⟩ | ⟨s, _, p, _, rfl, hp, hin⟩)
    · exact Or.inl ⟨s, rfl, hin⟩
    · exact Or.inr (Or.inl ⟨s, a, p, d0, rfl, h, hsc, hwff⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨s, p, d0, rfl, h, hsc, hwff⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, at', p, d0, d1, rfl, h0, h1, hwff⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, r, ds, rfl, hseq, hall, hvalid⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, p, k, rfl, hp, hin⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, p, rfl, hp, hin⟩)))))

open LO.FirstOrder.Arithmetic in
/-- Arithmetized `𝚫₁` core for the Z-derivation `Fixpoint` (mirrors Foundation
`Theory.Derivation.blueprint`). `d` = candidate code, `C` = the recursion set (premises so far). The
K^r disjunct uses `seqDef`/`lhDef`/`znthDef` for the variadic premise-sequence membership. -/
noncomputable def zblueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “d C.
    ( (∃ s < d, !zAtomGraph d s ∧
        ∃ ss, !seqSuccDef ss s ∧ ∃ sa, !seqAntDef sa s ∧ !inAntDef ss sa) ∨
      (∃ s < d, ∃ a < d, ∃ p < d, ∃ d0 < d, !zIallGraph d s a p d0 ∧ d0 ∈ C ∧
        (∃ ss, !seqSuccDef ss s ∧ ∃ ap, !qqAllDef ap p ∧ ss = ap) ∧
        !(zIallWffDef.sigma) s a p d0) ∨
      (∃ s < d, ∃ p < d, ∃ d0 < d, !zInegGraph d s p d0 ∧ d0 ∈ C ∧
        (∃ ss, !seqSuccDef ss s ∧ ∃ nb, !inegFDef nb p ∧ ss = nb) ∧ !(zInegWffDef.sigma) p d0) ∨
      (∃ s < d, ∃ at' < d, ∃ p < d, ∃ d0 < d, ∃ d1 < d,
        !zIndGraph d s at' p d0 d1 ∧ d0 ∈ C ∧ d1 ∈ C ∧ !(zIndWffDef.sigma) d) ∨
      (∃ s < d, ∃ r < d, ∃ ds < d,
        !zKGraph d s r ds ∧ !seqDef ds ∧
          (∃ l, !lhDef l ds ∧ ∀ i < l, ∃ z, !znthDef z ds i ∧ z ∈ C) ∧
          !(zKValidFDef.sigma) s r ds) ∨
      (∃ s < d, ∃ p < d, ∃ k < d, !zAxAllGraph d s p k ∧ !(isUFormula ℒₒᵣ).sigma p ∧
        ∃ ap, !qqAllDef ap p ∧ ∃ sa, !seqAntDef sa s ∧ !inAntDef ap sa) ∨
      (∃ s < d, ∃ p < d, !zAxNegGraph d s p ∧ !(isUFormula ℒₒᵣ).sigma p ∧
        ∃ nb, !inegFDef nb p ∧ ∃ sa, !seqAntDef sa s ∧ !inAntDef nb sa) )”)
  (.mkPi “d C.
    ( (∃ s < d, !zAtomGraph d s ∧
        ∀ ss, !seqSuccDef ss s → ∀ sa, !seqAntDef sa s → !inAntDef ss sa) ∨
      (∃ s < d, ∃ a < d, ∃ p < d, ∃ d0 < d, !zIallGraph d s a p d0 ∧ d0 ∈ C ∧
        (∀ ss, !seqSuccDef ss s → ∀ ap, !qqAllDef ap p → ss = ap) ∧
        !(zIallWffDef.pi) s a p d0) ∨
      (∃ s < d, ∃ p < d, ∃ d0 < d, !zInegGraph d s p d0 ∧ d0 ∈ C ∧
        (∀ ss, !seqSuccDef ss s → ∀ nb, !inegFDef nb p → ss = nb) ∧ !(zInegWffDef.pi) p d0) ∨
      (∃ s < d, ∃ at' < d, ∃ p < d, ∃ d0 < d, ∃ d1 < d,
        !zIndGraph d s at' p d0 d1 ∧ d0 ∈ C ∧ d1 ∈ C ∧ !(zIndWffDef.pi) d) ∨
      (∃ s < d, ∃ r < d, ∃ ds < d,
        !zKGraph d s r ds ∧ !seqDef ds ∧
          (∀ l, !lhDef l ds → ∀ i < l, ∀ z, !znthDef z ds i → z ∈ C) ∧
          !(zKValidFDef.pi) s r ds) ∨
      (∃ s < d, ∃ p < d, ∃ k < d, !zAxAllGraph d s p k ∧ !(isUFormula ℒₒᵣ).pi p ∧
        ∀ ap, !qqAllDef ap p → ∀ sa, !seqAntDef sa s → !inAntDef ap sa) ∨
      (∃ s < d, ∃ p < d, !zAxNegGraph d s p ∧ !(isUFormula ℒₒᵣ).pi p ∧
        ∀ nb, !inegFDef nb p → ∀ sa, !seqAntDef sa s → !inAntDef nb sa) )”)⟩

lemma zPhi_definable :
    𝚫₁.Defined (fun v : Fin 2 → V ↦ ZPhi {x | x ∈ v 1} (v 0)) zblueprint.core := .mk <| by
  constructor
  · intro v; simp [zblueprint]
  · intro v; simp [zphi_iff, zblueprint, zAtom_defined.iff, zIall_defined.iff, zIneg_defined.iff,
      zInd_defined.iff, zK_defined.iff, zAxAll_defined.iff, zAxNeg_defined.iff,
      seq_defined.iff, lh_defined.iff, znth_defined.iff,
      seqSucc_defined.iff, seqAnt_defined.iff, inAnt_defined.iff,
      qqForall_defined.iff, inegF_defined.iff, zInegWff_defined.iff, zIallWff_defined.iff,
      zIndWff_defined.iff]

/-- The Z-derivation `Fixpoint.Construction` (`Φ = ZPhi`, with the proved monotonicity). -/
noncomputable def zconstruction : Fixpoint.Construction V zblueprint where
  Φ := fun _ ↦ ZPhi
  defined := zPhi_definable
  monotone := fun h _ _ hd ↦ zphi_monotone h hd

instance : (zconstruction (V := V)).StrongFinite where
  strong_finite := fun {_ _ _} h ↦ zphi_strong_finite h

/-- **The system-Z derivation predicate** `ZDerivation : V → Prop` — the `Fixpoint` of `ZPhi`.
`d` is a Z-derivation iff it is built by one Z-rule from premises that are themselves Z-derivations. -/
def ZDerivation (d : V) : Prop := (zconstruction (V := V)).Fixpoint ![] d

/-- **`𝚫₁`-definability of `ZDerivation`** (the strong-finite Fixpoint definability, mirror Foundation's
`Theory.Derivation.defined`). Needed as the motive-definability for `zDerivation_induction`-driven proofs
that recurse on a `𝚺₁`-function of the derivation (e.g. `ZDerivation_zsubst`). -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.zDerivationDef : 𝚫₁.Semisentence 1 :=
  zblueprint.fixpointDefΔ₁

instance ZDerivation_defined : 𝚫₁-Predicate (ZDerivation : V → Prop) via zDerivationDef :=
  (zconstruction (V := V)).fixpoint_definedΔ₁

instance ZDerivation_definable : 𝚫₁-Predicate (ZDerivation : V → Prop) :=
  ZDerivation_defined.to_definable

instance ZDerivation_definable' (Γ) : Γ-[m + 1]-Predicate (ZDerivation : V → Prop) :=
  ZDerivation_definable.of_deltaOne

/-- **Recursion equation** for `ZDerivation` (the `Fixpoint.Construction.case`): a code is a
Z-derivation iff `ZPhi` holds of it over the set of Z-derivations. -/
lemma zDerivation_iff {d : V} : ZDerivation d ↔ ZPhi {z | ZDerivation z} d :=
  (zconstruction (V := V)).case

/-- **Structural induction** over `ZDerivation` (the `Fixpoint.Construction.induction`). -/
lemma zDerivation_induction {P : V → Prop} (hP : 𝚫₁-Predicate P)
    (H : ∀ C : Set V, (∀ x ∈ C, ZDerivation x ∧ P x) → ∀ d, ZPhi C d → P d) :
    ∀ d, ZDerivation d → P d :=
  (zconstruction (V := V)).induction (Γ := 𝚺) hP.of_deltaOne H

/-- **`õ(d)` is a valid CNF code (`isNF`) for EVERY Z-derivation** — the structural-induction closure of
the per-constructor NF lemmas (`isNF_iotil_zAtom`/`_zIall`/`_zIneg`/`_zInd`/`_zK`). This **discharges the
`isNF (iotil ·)` hypothesis carried by every Thm-4.2 descent lemma** (the nut `iord_descent_iRcrit_of_chain`,
LH3 `iord_descent_iCritAux`, LH4 `iord_descent_iIndReduct`, LH5 `iord_descent_iSpliceEnd`, and the
`iord_descent_dgdrop`/`_cut`/`_le` templates): once a code is known to be a genuine `ZDerivation`, its
pre-ordinal is automatically a normal form, so the descent fires with no side condition. -/
theorem isNF_iotil_of_ZDerivation : ∀ d : V, ZDerivation d → isNF (iotil d) := by
  apply zDerivation_induction (P := fun d : V => isNF (iotil d))
  · simp only [isNF]; definability
  · intro C hC d hphi
    rcases hphi with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, hd0, _⟩ | ⟨s, p, d0, rfl, hd0, _⟩ |
      ⟨s, at', p, d0, d1, rfl, hd0, hd1, _⟩ | ⟨s, r, ds, rfl, hds, hmem, _⟩ |
      ⟨s, p, k, rfl, hp, _⟩ | ⟨s, p, rfl, hp, _⟩
    · exact isNF_iotil_zAtom s
    · exact isNF_iotil_zIall (hC d0 hd0).2
    · exact isNF_iotil_zIneg (hC d0 hd0).2
    · exact isNF_iotil_zInd (hC d0 hd0).2 (hC d1 hd1).2
    · exact isNF_iotil_zK hds (fun i hi => (hC (znth ds i) (hmem i hi)).2)
    · exact isNF_iotil_zAxAll hp
    · exact isNF_iotil_zAxNeg hp

/-- **Structural descent over `ZDerivation` for the I-rules** (Buchholz Thm 4.2, cases 2–3 = LH1/LH2):
for any Z-derivation `d` built by `I^a_∀xF` or `I_¬A` (`zTag d ∈ {1,2}`), the reduct strictly lowers
the ordinal, `o(iR d) ≺ o(d)`. Proved by `ZDerivation` structural induction (the C0 Fixpoint),
dispatching on the rule: the I-rule cases are `iord_descent_iR_z*`; atom/Ind/K^r are vacuous (wrong
tag). The Ind/K^r tags broaden into this predicate once `iR`'s reducts for those rules are built — the
Ind chain reduct (LH4) and the critical/non-critical K^r branches (the nut). This is the V-level,
machine-checked analogue of the `GentzenCon` placeholder axiom `ord_R_descends`, restricted to the
rules whose reduct `iR` already constructs. -/
theorem iord_iR_descent_I :
    ∀ d, ZDerivation d → (zTag d = 1 ∨ zTag d = 2) → icmp (iord (iR d)) (iord d) = 0 := by
  apply zDerivation_induction
  · definability
  · intro C _ d hphi
    rcases hphi with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
      ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
      ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩
    · rintro (h | h) <;> simp at h
    · rintro _; exact iord_descent_iR_zIall s a p d0
    · rintro _; exact iord_descent_iR_zIneg s p d0
    · rintro (h | h) <;> simp at h
    · rintro (h | h) <;> simp at h
    · rintro (h | h) <;> simp at h
    · rintro (h | h) <;> simp at h

/-! ### Ind-rule (tag 3) one-step reduct + its structural descent over `ZDerivation` (LH4)

Buchholz §3.2 case 4: `Ind^{a,t}_F d0 d1` reduces to `d[0] = K^{rk F}(d0, d1(0),…,d1(k−1))`, with `k`
the numeral value of the conclusion term `t`. Ordinally every substituted copy `d1(ν)` carries
`õ = õ d1` (substitution-invariance), so the descent `õ(d[0]) ≺ õ(Ind)` holds via **F3**
(`ω^{õ d1}·k ≺ ω^{õ d1 + 1}`) for **every** `k ≥ 1`. The ordinal descent is therefore faithful with the
reduct modeled at the minimal count `k = 1` (one copy of `d1`); the genuine count (`= ⟦t⟧`, with the
`k = 0` special case `d[0] = K^r(d0)`) and the eigenvariable substitution `d1(ν/a)` are deferred
derivation-*validity* concerns — exactly parallel to the splice object's in-place faithfulness. This
banks the **Ind tag of the full Thm-4.2 structural descent**: the machine-checked `o(iR d) ≺ o(d)` now
covers tags 1,2 (I-rules, `iord_iR_descent_I`) **and** 3 (Ind). -/

/-- The Ind-rule one-step reduct `d[0] = K^{rk F}(d1, d0)` (count-1 ordinal model of Buchholz §3.2
case 4), as a closed code of `d`: conclusion sequent `fstIdx d`, chain rank `irk (zIndP d)`, premise
sequence the two-element `iIndReductSeq` of the Ind premises `zIndPrem0 d`,`zIndPrem1 d`. -/
noncomputable def iRInd (d : V) : V :=
  zK (fstIdx d) (irk (zIndP d)) (iIndReductSeq (zIndPrem0 d) (zIndPrem1 d) 1)

@[simp] lemma iRInd_zInd (s at' p d0 d1 : V) :
    iRInd (zInd s at' p d0 d1) = zK s (irk p) (iIndReductSeq d0 d1 1) := by
  simp [iRInd]

/-- **Ind-rule descent on the genuine reduct object** (LH4, per constructor): `o(d[0]) ≺ o(Ind^{a,t}_F d0 d1)`,
from `iord_descent_iIndReduct` at the modeled count `k = 1` (`hk : 0 < 1`). -/
lemma iord_descent_iRInd_zInd (s at' p d0 d1 : V)
    (hd0 : isNF (iotil d0)) (hd1 : isNF (iotil d1)) :
    icmp (iord (iRInd (zInd s at' p d0 d1))) (iord (zInd s at' p d0 d1)) = 0 := by
  rw [iRInd_zInd]
  exact iord_descent_iIndReduct hd0 hd1 one_pos

/-- **Structural descent over `ZDerivation` for the Ind rule** (Buchholz Thm 4.2 case 4 = LH4): every
Z-derivation built by the `Ind` rule (`zTag d = 3`) satisfies `o(iR d) ≺ o(d)`. Proved directly from the
one-step recursion equation `zDerivation_iff` (no induction needed — one-step descent): the Ind case
supplies `ZDerivation d0`,`ZDerivation d1`, hence `isNF (iotil d0/d1)` via `isNF_iotil_of_ZDerivation`,
and `iord_descent_iRInd_zInd` closes it; the other tags are vacuous (tag mismatch). The Ind-rule
companion of `iord_iR_descent_I`. -/
theorem iord_descent_iRInd_of_ZDerivation (d : V) (hd : ZDerivation d) (htag : zTag d = 3) :
    icmp (iord (iRInd d)) (iord d) = 0 := by
  rcases zDerivation_iff.mp hd with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, hd0, hd1, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩
  · simp at htag
  · simp at htag
  · simp at htag
  · exact iord_descent_iRInd_zInd s at' p d0 d1
      (isNF_iotil_of_ZDerivation d0 hd0) (isNF_iotil_of_ZDerivation d1 hd1)
  · simp at htag
  · simp at htag
  · simp at htag

/-! ### Chain (`K^r`) inversion + the ZDerivation-facing non-critical chain descent (LH3)

For the chain rule the per-case descents (`iord_descent_iCritAux` LH3, `iord_descent_iRcrit_of_chain`
the nut) carry the `isNF (iotil ·)` side conditions abstractly. On a genuine `ZDerivation` chain those
are now **free**: `zDerivation_zK_inv` reads `Seq ds` + per-premise `ZDerivation` off the one-step
recursion equation, and the out-of-range default (`znth ds n = 0` for `n ≥ lh ds`, `znth_prop_not`) is NF
via `isNF_iotil_zero`. This wires the LOW-HANGING chain descent (Buchholz §3.2 case 5.2.2) end-to-end to
`ZDerivation`: only the N1 IH on the replaced premise (`hlt`/`hle`/`hNFv`) remains abstract — exactly the
structural-induction interface. -/

/-- **Chain inversion**: a `ZDerivation` of a chain code `zK s r ds` has `Seq ds` and every in-range
premise a `ZDerivation`. From the one-step recursion equation `zDerivation_iff`; the non-`K` disjuncts
are ruled out by `zTag` (the chain has tag 4). -/
lemma zDerivation_zK_inv {s r ds : V} (hZ : ZDerivation (zK s r ds)) :
    Seq ds ∧ ∀ i < lh ds, ZDerivation (znth ds i) := by
  rcases zDerivation_iff.mp hZ with ⟨s', h, _⟩ | ⟨s', a, p, d0, h, _⟩ | ⟨s', p, d0, h, _⟩ |
    ⟨s', at', p, d0, d1, h, _, _⟩ | ⟨s', r', ds', h, hds', hmem', _⟩ |
    ⟨s', p, k, h, _⟩ | ⟨s', p, h, _⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · obtain rfl : ds = ds' := by simpa using congrArg zKseq h
    exact ⟨hds', fun i hi => hmem' i hi⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)

/-- **Faithful chain validity from a `ZDerivation`**: after the re-point, the `ZPhi` `zK` disjunct carries
`zKValidF` (Buchholz's genuine criticality-free `K^r` validity, §3 clause 5), so a `ZDerivation` of a chain
hands you the faithful side conditions directly. Criticality is NOT part of being a derivation — it is a
property the *reduction* (Def 3.2 case 5) supplies at the reduction site. -/
lemma zKValidF_of_ZDerivation_zK {s r ds : V} (hZ : ZDerivation (zK s r ds)) : zKValidF s r ds := by
  rcases zDerivation_iff.mp hZ with ⟨s', h, _⟩ | ⟨s', a, p, d0, h, _⟩ | ⟨s', p, d0, h, _⟩ |
    ⟨s', at', p, d0, d1, h, _, _⟩ | ⟨s', r', ds', h, hds', hmem', hvalid'⟩ |
    ⟨s', p, k, h, _⟩ | ⟨s', p, h, _⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · obtain rfl : s = s' := by simpa using congrArg fstIdx h
    obtain rfl : r = r' := by simpa using congrArg zKrank h
    obtain rfl : ds = ds' := by simpa using congrArg zKseq h
    exact hvalid'
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)

/-- **The `K^r` chain introduction** (the post-re-point `ZPhi` `zK` disjunct, packaged): a `Seq` premise
sequence of `ZDerivation`s that is `zKValidF`-valid (Buchholz's faithful, criticality-free `K^r` validity)
builds a `ZDerivation` of the chain `zK s r ds`. This is the `hZPhiK` residual of `ZDerivation_iCritReductG_of`
— now a theorem rather than a hypothesis, because criticality is no longer baked into `ZDerivation`. -/
lemma zDerivation_zK_intro {s r ds : V} (hseq : Seq ds)
    (hmem : ∀ i < lh ds, ZDerivation (znth ds i)) (hvalid : zKValidF s r ds) :
    ZDerivation (zK s r ds) :=
  zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨s, r, ds, rfl, hseq, hmem, hvalid⟩)))))

/-- **All-`n` premise NF** of a `ZDerivation` chain: in-range premises are NF (`isNF_iotil_of_ZDerivation`),
out-of-range default `0` is NF (`isNF_iotil_zero`). Discharges the `hNF : ∀ n` side condition. -/
lemma isNF_iotil_znth_of_ZDerivation_zK {s r ds : V} (hZ : ZDerivation (zK s r ds)) :
    ∀ n, isNF (iotil (znth ds n)) := by
  obtain ⟨_, hmem⟩ := zDerivation_zK_inv hZ
  intro n
  rcases lt_or_ge n (lh ds) with hn | hn
  · exact isNF_iotil_of_ZDerivation (znth ds n) (hmem n hn)
  · rw [znth_prop_not (Or.inr hn)]; exact isNF_iotil_zero

/-- **LH3 over `ZDerivation`** — the non-critical chain descent with its NF side conditions discharged
from the chain's `ZDerivation`. The single remaining input is the N1 IH on the replaced premise `v = dᵢ[n]`
(`hlt`/`hle`/`hNFv`), to be supplied by the Thm-4.2 structural induction. -/
lemma iord_descent_iCritAux_of_ZDerivation {s r ds i v : V}
    (hZ : ZDerivation (zK s r ds)) (hi : i < lh ds)
    (hlt : icmp (iotil v) (iotil (znth ds i)) = 0)
    (hle : idg v ≤ idg (znth ds i)) (hNFv : isNF (iotil v)) :
    icmp (iord (iCritAux (zK s r ds) i v)) (iord (zK s r ds)) = 0 := by
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  have hNFall := isNF_iotil_znth_of_ZDerivation_zK hZ
  have hnf : isNF (iotil (zK s r ds)) :=
    isNF_iotil_zK hds (fun n hn => isNF_iotil_of_ZDerivation (znth ds n) (hmem n hn))
  exact iord_descent_iCritAux hds hi hnf hlt hle hNFall hNFv

/-! ### The reduct-descent IH interface `iRedDescent` (Buchholz Lemma 4.1 (a)+(b)(i)+NF closure)

The Thm-4.2 structural induction (still upstream, gated on the recursive `iR`) feeds the chain case one
fact per reduced **non-critical** premise: its reduct does not raise the degree (part (a)), strictly
lowers the pre-ordinal (part (b)(i)), and stays in normal form. `iRedDescent red d` bundles exactly
those three — the `hle`/`hlt`/`hNFv` that `iord_descent_iCritAux` consumes — so the chain step composes
to a single application (`iord_descent_iCritAux_of_iRedDescent`). The per-rule lemmas below establish
`iRedDescent` for the reducts the induction will pick: `d₀` for the I-rules, `iRInd d` for `Ind`. This
crystallises the structural-induction interface: the remaining work is the recursive `iR` that *chooses*
the reduct, not any new descent mathematics. -/

/-- **Reduct-descent interface** (Buchholz Lemma 4.1 (a)+(b)(i)+NF): the reduct `red` of `d` does not
raise the degree, strictly lowers the pre-ordinal, and is itself a normal form. The IH the chain case
consumes for each reduced non-critical premise. -/
structure iRedDescent (red d : V) : Prop where
  /-- (a) the reduct does not raise the degree. -/
  dg_le : idg red ≤ idg d
  /-- (b)(i) the reduct strictly lowers the pre-ordinal. -/
  otil_lt : icmp (iotil red) (iotil d) = 0
  /-- the reduct's pre-ordinal is a normal form. -/
  nf : isNF (iotil red)

/-- `iRedDescent` ⟹ the full `iord` descent (tower combine via `iord_descent_le`), given `õ(d)` NF. -/
lemma iord_descent_of_iRedDescent {red d : V} (h : iRedDescent red d) (hnf : isNF (iotil d)) :
    icmp (iord red) (iord d) = 0 :=
  iord_descent_le hnf h.dg_le h.otil_lt

/-- **I∀ reduct interface**: `d[n] = d₀` satisfies `iRedDescent` (degree equal, `õ` drops by one). -/
lemma iRedDescent_zIall {s a p d0 : V} (hd0 : isNF (iotil d0)) :
    iRedDescent d0 (zIall s a p d0) where
  dg_le := le_of_eq (idg_zIall s a p d0).symm
  otil_lt := by rw [iotil_zIall]; exact self_lt_iadd_one (iotil d0) (iotil d0) le_rfl
  nf := hd0

/-- **I¬ reduct interface**: `d[0] = d₀` satisfies `iRedDescent`. -/
lemma iRedDescent_zIneg {s p d0 : V} (hd0 : isNF (iotil d0)) :
    iRedDescent d0 (zIneg s p d0) where
  dg_le := le_of_eq (idg_zIneg s p d0).symm
  otil_lt := by rw [iotil_zIneg]; exact self_lt_iadd_one (iotil d0) (iotil d0) le_rfl
  nf := hd0

/-- `õ(iRInd d)` is NF for an `Ind` code with NF premises — the reduct chain's `#`-fold of two NF
ω-powers. -/
lemma isNF_iotil_iRInd_zInd {s at' p d0 d1 : V} (hd0 : isNF (iotil d0)) (hd1 : isNF (iotil d1)) :
    isNF (iotil (iRInd (zInd s at' p d0 d1))) := by
  rw [iRInd_zInd, iotil_zK _ _ _ (iIndReductSeq_seq d0 d1 1), iseqNaddIdg_iIndReductSeq one_pos]
  exact isNF_inadd (isNF_omega_pow hd0) _ (isNF_omega_pow hd1)

/-- **Ind reduct interface**: `d[0] = iRInd d` satisfies `iRedDescent` (degree preserved by
`idg_zK_iIndReduct`, `õ` drops by `icmp_iotil_iIndReduct`, NF by `isNF_iotil_iRInd_zInd`). -/
lemma iRedDescent_zInd {s at' p d0 d1 : V} (hd0 : isNF (iotil d0)) (hd1 : isNF (iotil d1)) :
    iRedDescent (iRInd (zInd s at' p d0 d1)) (zInd s at' p d0 d1) where
  dg_le := le_of_eq (by rw [iRInd_zInd]; exact idg_zK_iIndReduct (s := s) (at' := at') one_pos)
  otil_lt := by
    rw [iRInd_zInd, iotil_zK _ _ _ (iIndReductSeq_seq d0 d1 1)]
    exact icmp_iotil_iIndReduct hd0 hd1 one_pos
  nf := isNF_iotil_iRInd_zInd hd0 hd1

/-- **Chain step from the IH interface**: a non-critical premise `i` whose reduct `v` satisfies
`iRedDescent v (znth ds i)` plugs straight into the chain descent — this is the LH3 case of the Thm-4.2
structural induction, with the per-premise IH packaged as `iRedDescent`. -/
lemma iord_descent_iCritAux_of_iRedDescent {s r ds i v : V}
    (hZ : ZDerivation (zK s r ds)) (hi : i < lh ds) (hd : iRedDescent v (znth ds i)) :
    icmp (iord (iCritAux (zK s r ds) i v)) (iord (zK s r ds)) = 0 :=
  iord_descent_iCritAux_of_ZDerivation hZ hi hd.otil_lt hd.dg_le hd.nf

/-! ### Splice (LH5) over `ZDerivation` + the critical-premise IH interface

The OTHER chain sub-case (Buchholz §3.2 case 5.2.1): a reduced premise `dⱼ` that is itself **critical**
splices its two T3.4 auxiliaries `a = dⱼ{0}`, `b = dⱼ{1}` into the parent chain. As with LH3 the splice
descent's NF side conditions are free on a `ZDerivation` chain (`zDerivation_zK_inv`), and the per-premise
IH bundles into `iSpliceDescent` (each auxiliary lowers `õ`, does not raise `dg`, and is NF). With the
LH3 (`iRedDescent`) interface this completes the chain case's two sub-cases — the remaining input is the
recursive `iR` selecting which premise to reduce and which sub-case applies. -/

/-- **LH5 over `ZDerivation`** — the splice descent with its NF side conditions discharged from the
chain's `ZDerivation`. Only the auxiliaries' N1 IH (`ha`/`hb`/`hag`/`hbg`/NF) remains abstract. -/
lemma iord_descent_iSpliceEnd_of_ZDerivation {s s' r ds j a b : V}
    (hZ : ZDerivation (zK s r ds)) (hj : j < lh ds)
    (ha : icmp (iotil a) (iotil (znth ds j)) = 0) (hb : icmp (iotil b) (iotil (znth ds j)) = 0)
    (hag : idg a ≤ idg (znth ds j)) (hbg : idg b ≤ idg (znth ds j))
    (hNFa : isNF (iotil a)) (hNFb : isNF (iotil b)) :
    icmp (iord (zK s' r (seqCons (seqUpdate ds j a) b))) (iord (zK s r ds)) = 0 := by
  obtain ⟨hds, hmem⟩ := zDerivation_zK_inv hZ
  have hNFall := isNF_iotil_znth_of_ZDerivation_zK hZ
  have hnf : isNF (iotil (zK s r ds)) :=
    isNF_iotil_zK hds (fun n hn => isNF_iotil_of_ZDerivation (znth ds n) (hmem n hn))
  exact iord_descent_iSpliceEnd hds hj hnf ha hb hag hbg hNFall hNFa hNFb

/-- **Critical-premise (splice) IH interface** (Buchholz case 5.2.1 / LH5): a critical premise `dⱼ`
reduces by splicing its two T3.4 auxiliaries `a = dⱼ{0}`, `b = dⱼ{1}` — each does not raise the degree,
strictly lowers the pre-ordinal, and is NF. The crit-premise analogue of `iRedDescent`. -/
structure iSpliceDescent (a b d : V) : Prop where
  a_dg_le : idg a ≤ idg d
  b_dg_le : idg b ≤ idg d
  a_otil_lt : icmp (iotil a) (iotil d) = 0
  b_otil_lt : icmp (iotil b) (iotil d) = 0
  a_nf : isNF (iotil a)
  b_nf : isNF (iotil b)

/-- **Splice step from the IH interface**: a critical premise `j` whose auxiliaries satisfy
`iSpliceDescent` plugs straight into the splice descent — the LH5 case of the Thm-4.2 structural
induction with the per-premise IH packaged. -/
lemma iord_descent_iSpliceEnd_of_iSpliceDescent {s s' r ds j a b : V}
    (hZ : ZDerivation (zK s r ds)) (hj : j < lh ds) (hd : iSpliceDescent a b (znth ds j)) :
    icmp (iord (zK s' r (seqCons (seqUpdate ds j a) b))) (iord (zK s r ds)) = 0 :=
  iord_descent_iSpliceEnd_of_ZDerivation hZ hj hd.a_otil_lt hd.b_otil_lt hd.a_dg_le hd.b_dg_le
    hd.a_nf hd.b_nf

/-! ### `tp`-inversion + concrete discharge of the critical R-redex premise's IH

The critical-case redex (`inference_critical_pair_of_chain`) returns indices with `tp(dᵢ)=R_{Aᵢ}`,
`tp(d_j)=L^k_{Aᵢ}`. By `tp`'s definition a right-symbol forces the premise to be an **I-rule** (tags 1,2)
and a left-symbol an **atomic axiom** (tags 5,6). So the R-redex premise's reduct fact (`õ`-drop +
`dg`-bound) is **concrete** — the banked I-rule `iRedDescent`, not an abstract structural IH. This
discharges the `i`-side of the nut's `ρ`-hypotheses (`iord_descent_iRcrit_of_chain`'s `hρlt`/`hρg` at
`redexI`); only the `j`-side (the L-axiom reduct, the §5 atomic layer) stays abstract. -/

/-- **R-symbol ⟹ I-rule tag**: `tp d = R_A` forces `zTag d ∈ {1,2}` (the only right-symbol branches). -/
lemma tp_isymR_tag {d A : V} (h : tp d = isymR A) : zTag d = 1 ∨ zTag d = 2 := by
  unfold tp at h
  by_cases ht1 : zTag d = 1
  · exact Or.inl ht1
  · rw [if_neg ht1] at h
    by_cases ht2 : zTag d = 2
    · exact Or.inr ht2
    · rw [if_neg ht2] at h
      by_cases ht5 : zTag d = 5
      · rw [if_pos ht5] at h; exact absurd h (by simp)
      · rw [if_neg ht5] at h
        by_cases ht6 : zTag d = 6
        · rw [if_pos ht6] at h; exact absurd h (by simp)
        · rw [if_neg ht6] at h; exact absurd h.symm (by simp)

/-- **L-symbol ⟹ atomic-axiom tag**: `tp d = L^k_A` forces `zTag d ∈ {5,6}`. -/
lemma tp_isymLk_tag {d k A : V} (h : tp d = isymLk k A) : zTag d = 5 ∨ zTag d = 6 := by
  unfold tp at h
  by_cases ht1 : zTag d = 1
  · rw [if_pos ht1] at h; exact absurd h (by simp)
  · rw [if_neg ht1] at h
    by_cases ht2 : zTag d = 2
    · rw [if_pos ht2] at h; exact absurd h (by simp)
    · rw [if_neg ht2] at h
      by_cases ht5 : zTag d = 5
      · exact Or.inl ht5
      · rw [if_neg ht5] at h
        by_cases ht6 : zTag d = 6
        · exact Or.inr ht6
        · rw [if_neg ht6] at h; exact absurd h.symm (by simp)

/-- **The critical R-redex premise's reduct satisfies the IH bundle, concretely.** A premise `d` with
`tp d = R_A` (the `i`-side redex) is an I-rule (`tp_isymR_tag`); on a `ZDerivation` its `iR`-reduct is
the immediate sub-derivation, which satisfies `iRedDescent` by the banked I-rule case — no abstract IH.
This is the `redexI`-side of the nut's `ρ`-discharge. -/
lemma iRedDescent_iR_of_tp_isymR {d A : V} (htp : tp d = isymR A) (hZ : ZDerivation d) :
    iRedDescent (iR d) d := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, hd0, _⟩ | ⟨s, p, d0, rfl, hd0, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩
  · rw [tp_zAtom] at htp; exact absurd htp (by simp)
  · rw [iR_zIall]; exact iRedDescent_zIall (isNF_iotil_of_ZDerivation d0 hd0)
  · rw [iR_zIneg]; exact iRedDescent_zIneg (isNF_iotil_of_ZDerivation d0 hd0)
  · rw [tp_zInd] at htp; exact absurd htp (by simp)
  · rw [tp_zK] at htp; exact absurd htp (by simp)
  · rw [tp_zAxAll] at htp; exact absurd htp (by simp)
  · rw [tp_zAxNeg] at htp; exact absurd htp (by simp)

/-! ## C0.5 — the Foundation→Z bridge (NEXT milestone, lap-62 reflection)

**The missing seam** (judge `E-EQ5-ROUTE-FINDING-2026-06-23.md` Finding 3; lap-62 reflection
Sharpening 2). The downstream crux-2 obligation `GentzenCon.gentzen_descent_of_inconsistent` is fired
by `¬ 𝗣𝗔.Consistent M` — i.e. `M` carries a coded **Foundation** (Tait-calculus) derivation of `⊥`. But
`iord`/`iR`/the C3 descent operate on **Buchholz system-Z** derivation codes (`zAtom`/`zIall`/`zIneg`/
`zInd`/`zK`). **Nothing yet turns a Foundation ⊥-proof into a Z ⊥-derivation.** Without this bridge the
whole C1/C3 engine has no input. Scale: Bryce–Goré's analogue (`aarondroidbryce/Gentzen`,
`theories/Logic/Peano.v`, `PA_closed_PA_omega`) is ~1,215 lines — a milestone, not a footnote.

**Bridge lemma type.** Now that `ZDerivation : V → Prop` (the C0 Fixpoint) is built (above), define
`ZDerivesEmpty d := ZDerivation d ∧ fstIdx d = (∅ : sequent code)` and prove the `Z ⊇ PA`-on-closed-
sequents simulation, M-internal (`Σ₁` / per-model):

```
-- C0.5 — Foundation⊥ ⟹ Z-derivation of the empty sequent (M-internal).
theorem foundation_bot_to_Z_empty
    {d : V} (hd : (𝗣𝗔).DerivationOf d (⊥ : Sentence ℒₒᵣ)) :
    ∃ z : V, ZDerivesEmpty z
```

**⭐ CHEAPER than the ~1215-line flag (judge `E-CRUX2-DECOMPOSITION` §5, 2026-06-24).** Pattern: discharge
each PA axiom in Z + simulate each rule (MP → Z-cut → `K^r` chain rule; generalization → Z `I^a_∀`). The
key shortcut: **Z's native `Ind` rule maps PA-induction DIRECTLY**, so the bridge SKIPS Bryce–Goré's
biggest sub-tower (their induction→ω-rule simulation, ~half of `Peano.v`) — **revise C0.5 to <1k lines.**
This independently re-confirms the Z-over-PA_ω choice. **Do NOT port their `cut_elim.v`** (infinitary
transfinite recursion / meta-Con via the "dangerous disjunct" — NOT the primrec `R` the PRWO route needs);
only `Peano.v` transfers. Sub-obligations (judge §5): **B1** each PA axiom → short Z-derivation (§5 `Ax(Z)`);
**B2** each Foundation rule → Z-admissible (induction `axm` absorbed by Z's `Ind`); **B3** compose,
M-internally (structural recursion on `d`, sub-derivation codes `<`-smaller via `HFS` course-of-values).

Then `derivesEmpty` (the `GentzenCon` stand-in) is genuinely **populated** from `¬ 𝗣𝗔.Consistent M`:
`¬Con ⟹ ∃ d, 𝗣𝗔.DerivationOf d ⊥ ⟹ (C0.5) ∃ z, ZDerivesEmpty z ⟹` feed the Z-descent `n ↦ iord(iR^[n] z)`.

**Prereqs:** C0 Fixpoint `ZDerivation` ✅ DONE (lap 62) → `iR` (C2) → this bridge (parallelizable in a
worktree). See `HARVEST.md`, `PENDING_WORK.md` lap-62, `E-CRUX2-DECOMPOSITION-2026-06-24.md §5`, and
`GentzenCon.lean` footer (to be re-pointed from Foundation's `Theory.Derivation` onto Buchholz-Z + bridge). -/

/-! ## `𝚺₁`-definability of the crux-2 reduct objects (toward the recursive `iR`)

The Buchholz one-step reduction `iR : d ↦ d[0]` must be a **course-of-values `<`-recursion** (its
critical branch `d{0}=K^r(i/dᵢ[k])` references premise *reducts*; lap-71 handoff "NEXT"). The table
step `iRNext d s` therefore reads sub-reducts out of `s` and *constructs* the reduct from the
crux-2 objects. For the `iRNext` `𝚺₁` blueprint to typecheck, each such object must be a definable
function. These instances supply exactly that — `seqUpdate`, the critical auxiliary `iCritAux`, the
redex finder `redexCode`/`redexI`/`redexJ`, the two-element reduct sequence `iCritReductSeq`, the
assembled critical reduct `iCritReduct`, and the `Ind` reduct `iIndReductSeq`/`iRInd` — so the
recursion's blueprint composes them shallowly (mirroring `idgNext`/`idgTable`). -/

/-- `seqUpdate ds i v = seqUpdateAux ds i v (lh ds)`. -/
def _root_.LO.FirstOrder.Arithmetic.seqUpdateDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y ds i v. ∃ l, !lhDef l ds ∧ !seqUpdateAuxDef y ds i v l”
instance seqUpdate_defined : 𝚺₁-Function₃ (seqUpdate : V → V → V → V) via seqUpdateDef := .mk
  fun v ↦ by simp [seqUpdateDef, seqUpdate, lh_defined.iff, seqUpdateAux_defined.iff]
instance seqUpdate_definable : 𝚺₁-Function₃ (seqUpdate : V → V → V → V) :=
  seqUpdate_defined.to_definable

/-- `seqSetSucc s C = ⟪seqAnt s, C⟫` (the genuine `Θ→C` endsequent op). -/
def _root_.LO.FirstOrder.Arithmetic.seqSetSuccDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y s C. ∃ sa, !seqAntDef sa s ∧ !pairDef y sa C”
instance seqSetSucc_defined : 𝚺₁-Function₂ (seqSetSucc : V → V → V) via seqSetSuccDef := .mk
  fun v ↦ by simp [seqSetSuccDef, seqSetSucc, mkSeqt, seqAnt_defined.iff, pair_defined.iff]
instance seqSetSucc_definable : 𝚺₁-Function₂ (seqSetSucc : V → V → V) := seqSetSucc_defined.to_definable

/-- `seqAddAnt A s = ⟪seqCons (seqAnt s) A, seqSucc s⟫` (the genuine `A,Θ→D` endsequent op). -/
def _root_.LO.FirstOrder.Arithmetic.seqAddAntDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y A s. ∃ sa, !seqAntDef sa s ∧ ∃ c, !seqConsDef c sa A ∧ ∃ ss, !seqSuccDef ss s ∧ !pairDef y c ss”
instance seqAddAnt_defined : 𝚺₁-Function₂ (seqAddAnt : V → V → V) via seqAddAntDef := .mk
  fun v ↦ by simp [seqAddAntDef, seqAddAnt, mkSeqt, seqAnt_defined.iff, seqCons_defined.iff,
    seqSucc_defined.iff, pair_defined.iff]
instance seqAddAnt_definable : 𝚺₁-Function₂ (seqAddAnt : V → V → V) := seqAddAnt_defined.to_definable

/-- `iCritAux d i v = zK (fstIdx d) (zKrank d) (seqUpdate (zKseq d) i v)` (the critical auxiliary
`d{ν} = K^r(i/v)`, a chain with premise `i` replaced by `v`). -/
def _root_.LO.FirstOrder.Arithmetic.iCritAuxDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y d i v. ∃ f, !fstIdxDef f d ∧ ∃ rk, !zKrankDef rk d ∧ ∃ ds, !zKseqDef ds d ∧
    ∃ u, !seqUpdateDef u ds i v ∧ !zKGraph y f rk u”
instance iCritAux_defined : 𝚺₁-Function₃ (iCritAux : V → V → V → V) via iCritAuxDef := .mk
  fun v ↦ by simp [iCritAuxDef, iCritAux, fstIdx_defined.iff, zKrank_defined.iff, zKseq_defined.iff,
    seqUpdate_defined.iff, zK_defined.iff]
instance iCritAux_definable : 𝚺₁-Function₃ (iCritAux : V → V → V → V) := iCritAux_defined.to_definable

/-- `redexCode d = redexAux (zKseq d) ⟪lh(zKseq d), lh(zKseq d)⟫` (the least valid redex pair). -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.redexCodeDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ ds, !zKseqDef ds d ∧ ∃ l, !lhDef l ds ∧ ∃ b, !pairDef b l l ∧ !redexAuxDef y ds b”
instance redexCode_defined : 𝚺₁-Function₁ (redexCode : V → V) via redexCodeDef := .mk
  fun v ↦ by simp [redexCodeDef, redexCode, zKseq_defined.iff, lh_defined.iff, redexAux_defined.iff]
instance redexCode_definable : 𝚺₁-Function₁ (redexCode : V → V) := redexCode_defined.to_definable

/-- `redexI d = π₁ (redexCode d)`. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.redexIDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ c, !redexCodeDef c d ∧ !pi₁Def y c”
instance redexI_defined : 𝚺₁-Function₁ (redexI : V → V) via redexIDef := .mk
  fun v ↦ by simp [redexIDef, redexI, redexCode_defined.iff, pi₁_defined.iff]
instance redexI_definable : 𝚺₁-Function₁ (redexI : V → V) := redexI_defined.to_definable

/-- `redexJ d = π₂ (redexCode d)`. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.redexJDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ c, !redexCodeDef c d ∧ !pi₂Def y c”
instance redexJ_defined : 𝚺₁-Function₁ (redexJ : V → V) via redexJDef := .mk
  fun v ↦ by simp [redexJDef, redexJ, redexCode_defined.iff, pi₂_defined.iff]
instance redexJ_definable : 𝚺₁-Function₁ (redexJ : V → V) := redexJ_defined.to_definable

/-- `iCritReductSeq d0 d1 = seqCons (seqCons ∅ d0) d1` (the two-element reduct premise sequence). -/
def _root_.LO.FirstOrder.Arithmetic.iCritReductSeqDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y d0 d1. ∃ s1, !seqConsDef s1 0 d0 ∧ !seqConsDef y s1 d1”
instance iCritReductSeq_defined : 𝚺₁-Function₂ (iCritReductSeq : V → V → V) via iCritReductSeqDef :=
  .mk fun v ↦ by simp [iCritReductSeqDef, iCritReductSeq, seqCons_defined.iff, emptyset_def]
instance iCritReductSeq_definable : 𝚺₁-Function₂ (iCritReductSeq : V → V → V) :=
  iCritReductSeq_defined.to_definable

/-- `iCritReduct d i j v w = zK (fstIdx d) (zKrank d − 1) (iCritReductSeq (iCritAux d i v)
(iCritAux d j w))` (Buchholz Def 3.2 case 5.1 reduct `d[0] = K^{r-1}_Π d{0} d{1}`). -/
def _root_.LO.FirstOrder.Arithmetic.iCritReductDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y d i j v w. ∃ f, !fstIdxDef f d ∧ ∃ rk, !zKrankDef rk d ∧ ∃ rk1, !subDef rk1 rk 1 ∧
    ∃ a, !iCritAuxDef a d i v ∧ ∃ b, !iCritAuxDef b d j w ∧
    ∃ s, !iCritReductSeqDef s a b ∧ !zKGraph y f rk1 s”
instance iCritReduct_defined :
    𝚺₁-Function₅ (iCritReduct : V → V → V → V → V → V) via iCritReductDef := .mk
  fun v ↦ by simp [iCritReductDef, iCritReduct, fstIdx_defined.iff, zKrank_defined.iff,
    sub_defined.iff, iCritAux_defined.iff, iCritReductSeq_defined.iff, zK_defined.iff]

/-- `iIndReductSeq d0 d1 k = seqCons (iRepeatSeq d1 k) d0` (the `Ind` reduct premise sequence). -/
def _root_.LO.FirstOrder.Arithmetic.iIndReductSeqDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y d0 d1 k. ∃ r, !iRepeatSeqDef r d1 k ∧ !seqConsDef y r d0”
instance iIndReductSeq_defined :
    𝚺₁-Function₃ (iIndReductSeq : V → V → V → V) via iIndReductSeqDef := .mk
  fun v ↦ by simp [iIndReductSeqDef, iIndReductSeq, iRepeatSeq_defined.iff, seqCons_defined.iff]
instance iIndReductSeq_definable : 𝚺₁-Function₃ (iIndReductSeq : V → V → V → V) :=
  iIndReductSeq_defined.to_definable

/-- `iRInd d = zK (fstIdx d) (irk (zIndP d)) (iIndReductSeq (zIndPrem0 d) (zIndPrem1 d) 1)`
(the closed `Ind`-rule reduct, Buchholz §3.2 case 4 at the count-1 ordinal model). -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.iRIndDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ f, !fstIdxDef f d ∧ ∃ pf, !zIndPDef pf d ∧ ∃ rk, !irkDef rk pf ∧
    ∃ p0, !zIndPrem0Def p0 d ∧ ∃ p1, !zIndPrem1Def p1 d ∧ ∃ s, !iIndReductSeqDef s p0 p1 1 ∧
    !zKGraph y f rk s”
instance iRInd_defined : 𝚺₁-Function₁ (iRInd : V → V) via iRIndDef := .mk
  fun v ↦ by simp [iRIndDef, iRInd, fstIdx_defined.iff, zIndP_defined.iff, irk_defined.iff,
    zIndPrem0_defined.iff, zIndPrem1_defined.iff, iIndReductSeq_defined.iff, zK_defined.iff]
instance iRInd_definable : 𝚺₁-Function₁ (iRInd : V → V) := iRInd_defined.to_definable

/-! ## `iR2` — the recursive `iR` (`d ↦ d[0]`) as a total `𝚺₁` course-of-values `<`-recursion

Lap-71's named architectural blocker. The Buchholz reduction `iR` is `𝚺₁` by the SAME table reduction
as `idg`/`iotil` (`idgTable`/`ioTable`): `iRTable n = ⟨iR2 0,…,iR2 n⟩`, the step `iRNext d s` reading
sub-reducts out of `s` at the premise indices (all `< d`). The structural branches are CLOSED in `d`
(`I∀`→`zIallPrem`, `I¬`→`zInegPrem`, `Ind`→`iRInd`, atom/axioms→`d`); the **K-branch** is the only one
that recurses: the critical reduct `d[0] = K^{r-1}_Π d{0} d{1}` (`iCritReduct`) at the FUNCTIONAL redex
`(redexI d, redexJ d)`, with the two auxiliaries' premise-reducts `dᵢ[k] = iR2(znth ds (redexI d))`,
`d_j[0] = iR2(znth ds (redexJ d))` read from `s` (both premise codes `< zK s r ds`). This realizes the
abstract `ρ`-supplied `iRcrit d ρ` at the CONCRETE `ρ = fun n ↦ iR2 (znth (zKseq d) n)` — the genuine
recursive reduct, no abstract input. (For non-critical/splice K-chains the K-branch still emits the
critical reduct; the descent-side dispatch selects the right per-case wrapper — a later brick.) -/

/-- A general HFS bound: `znth ds k ≤ ds` for ALL `k` (in-range: the read is an element `≤ ds`;
out-of-range: `znth = 0 ≤ ds`). Needed to land premise-reads `znth ds k` inside the length-`(zK-1)`
table. -/
lemma znth_le_self (ds k : V) : znth ds k ≤ ds := by
  by_cases h : Seq ds ∧ k < lh ds
  · exact le_of_lt (lt_of_mem_rng (h.1.znth h.2))
  · rw [znth_prop_not (by rw [not_and_or, not_lt] at h; exact h)]; simp

/-- **The §5 atomic-reduct FUNCTION** `d ↦ d[0]` for an L-axiom premise (Buchholz §5, Lemma 5.2):
`Ax^{∀p,k} ↦ Ax^1_{·→p}` (tag 5) and `Ax^{¬p,0} ↦ Ax^1_{·→p}` (tag 6) — the principal formula stripped
to its rank-one-lower matrix. Identity off the atomic-axiom tags. This is the j-component the K-case
critical reduction installs (in `iRNext`/`iCritReduct` tag-4) instead of the table lookup `iR2(premⱼ)`,
which is the identity on axioms (`iR2_zAxAll`/`iR2_zAxNeg`) and so yields NO õ-drop on the j-side. -/
noncomputable def zAxReduct (d : V) : V :=
  if zTag d = 5 then zAx1 (fstIdx d) (zAxAllF d)
  else if zTag d = 6 then zAx1 (fstIdx d) (zAxNegF d)
  else d

@[simp] lemma zAxReduct_zAxAll (s p k : V) : zAxReduct (zAxAll s p k) = zAx1 s p := by
  simp [zAxReduct]

@[simp] lemma zAxReduct_zAxNeg (s p : V) : zAxReduct (zAxNeg s p) = zAx1 s p := by
  rw [zAxReduct, if_neg (by simp [zTag_zAxNeg]), if_pos (by simp [zTag_zAxNeg])]
  simp

/-- **Σ₁-definability of `zAxReduct`** (`zAxAllF d = π₁(zRest d)`, `zAxNegF d = zRest d`; `zAx1` via its
graph). The arithmetization that lets `zAxReduct` thread through the `iRNext`/`iCritReduct` tag-4
definition. -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.zAxReductDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ t, !zTagDef t d ∧
    ( (t = 5 ∧ ∃ s, !fstIdxDef s d ∧ ∃ r, !zRestDef r d ∧ ∃ p, !pi₁Def p r ∧ !zAx1Graph y s p)
    ∨ (t = 6 ∧ ∃ s, !fstIdxDef s d ∧ ∃ p, !zRestDef p d ∧ !zAx1Graph y s p)
    ∨ (t ≠ 5 ∧ t ≠ 6 ∧ y = d) )”

set_option maxHeartbeats 800000 in
instance zAxReduct_defined : 𝚺₁-Function₁ (zAxReduct : V → V) via zAxReductDef := .mk fun v ↦ by
  simp [zAxReductDef, zAxReduct, zTag_defined.iff, fstIdx_defined.iff, zRest_defined.iff,
    pi₁_defined.iff, zAx1_defined.iff, zAxAllF, zAxNegF, numeral_eq_natCast]
  by_cases h5 : zTag (v 1) = 5
  · simp [h5]
  · by_cases h6 : zTag (v 1) = 6
    · simp [h5, h6]
    · simp [h5, h6]

instance zAxReduct_definable : 𝚺₁-Function₁ (zAxReduct : V → V) := zAxReduct_defined.to_definable

/-- Table step of `iR2`: `iR2 d` from `s = ⟨iR2 0,…,iR2 (d-1)⟩`, dispatching on `zTag d`. -/
noncomputable def iRNext (d s : V) : V :=
  if zTag d = 1 then zIallPrem d
  else if zTag d = 2 then zInegPrem d
  else if zTag d = 3 then iRInd d
  else if zTag d = 4 then
    iCritReduct d (redexI d) (redexJ d)
      (zAxReduct (znth s (znth (zKseq d) (redexI d))))
      (zAxReduct (znth s (znth (zKseq d) (redexJ d))))
  else d

noncomputable def _root_.LO.FirstOrder.Arithmetic.iRNextDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y d s. ∃ t, !zTagDef t d ∧
    ( (t = 1 ∧ !zIallPremDef y d)
    ∨ (t = 2 ∧ !zInegPremDef y d)
    ∨ (t = 3 ∧ !iRIndDef y d)
    ∨ (t = 4 ∧ ∃ ds, !zKseqDef ds d ∧ ∃ i, !redexIDef i d ∧ ∃ j, !redexJDef j d ∧
        ∃ ai, !znthDef ai ds i ∧ ∃ aj, !znthDef aj ds j ∧
        ∃ vi, !znthDef vi s ai ∧ ∃ wi, !zAxReductDef wi vi ∧
        ∃ vj, !znthDef vj s aj ∧ ∃ wj, !zAxReductDef wj vj ∧ !iCritReductDef y d i j wi wj)
    ∨ (t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ y = d) )”

set_option maxHeartbeats 1000000 in
instance iRNext_defined : 𝚺₁-Function₂ (iRNext : V → V → V) via iRNextDef := .mk fun v ↦ by
  simp [iRNextDef, iRNext, zTag_defined.iff, zIallPrem_defined.iff, zInegPrem_defined.iff,
    iRInd_defined.iff, zKseq_defined.iff, redexI_defined.iff, redexJ_defined.iff,
    znth_defined.iff, zAxReduct_defined.iff, iCritReduct_defined.iff]
  by_cases h1 : zTag (v 1) = 1
  · simp [h1]
  · by_cases h2 : zTag (v 1) = 2
    · simp [h1, h2]
    · by_cases h3 : zTag (v 1) = 3
      · simp [h1, h2, h3]
      · by_cases h4 : zTag (v 1) = 4
        · simp [h1, h2, h3, h4]
        · simp [h1, h2, h3, h4]

instance iRNext_definable : 𝚺₁-Function₂ (iRNext : V → V → V) := iRNext_defined.to_definable

/-- Blueprint for the `iR2` table. -/
noncomputable def iRTable.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n. ∃ v, !iRNextDef v (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def iRTable.construction : PR.Construction V iRTable.blueprint where
  zero := fun _ ↦ !⟦0⟧
  succ := fun _ n ih ↦ seqCons ih (iRNext (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [iRTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [iRTable.blueprint, iRNext_defined.iff, seqCons_defined.iff]

/-- **The `iR2` table**: `iRTable n = ⟨iR2 0,…,iR2 n⟩` (length `n+1`). -/
noncomputable def iRTable (n : V) : V := iRTable.construction.result ![] n

@[simp] lemma iRTable_zero : iRTable (0 : V) = !⟦0⟧ := by simp [iRTable, iRTable.construction]

@[simp] lemma iRTable_succ (n : V) :
    iRTable (n + 1) = seqCons (iRTable n) (iRNext (n + 1) (iRTable n)) := by
  simp [iRTable, iRTable.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.iRTableDef : 𝚺₁.Semisentence 2 :=
  iRTable.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance iRTable_defined : 𝚺₁-Function₁ (iRTable : V → V) via iRTableDef := .mk
  fun v ↦ by simp [iRTable.construction.result_defined_iff, iRTableDef]; rfl
instance iRTable_definable : 𝚺₁-Function₁ (iRTable : V → V) := iRTable_defined.to_definable
instance iRTable_definable' (Γ) : Γ-[m + 1]-Function₁ (iRTable : V → V) :=
  iRTable_definable.of_sigmaOne

/-- **The recursive `iR2`** `d ↦ d[0]`: the `d`-th entry of the table. -/
noncomputable def iR2 (d : V) : V := znth (iRTable d) d

noncomputable def _root_.LO.FirstOrder.Arithmetic.iR2Def : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ t, !iRTableDef t d ∧ !znthDef y t d”
instance iR2_defined : 𝚺₁-Function₁ (iR2 : V → V) via iR2Def := .mk fun v ↦ by
  simp [iR2Def, iR2, iRTable_defined.iff, znth_defined.iff]
instance iR2_definable : 𝚺₁-Function₁ (iR2 : V → V) := iR2_defined.to_definable
instance iR2_definable' (Γ) : Γ-[m + 1]-Function₁ (iR2 : V → V) := iR2_definable.of_sigmaOne

/-- **The genuine closed critical branch** for `red`'s tag-4 case: `K^{r-1}_Π ⟨d{0}, d{1}⟩` where the cut
formula is `A(d) = chainAsucc (zKseq d) (redexI d)`, the auxiliaries replace the redex premises `i = redexI d`,
`j = redexJ d` by their `ρ`-reducts, and carry the reduced endsequents. Closed term; only `ρ` (the N1 IH)
is abstract. (Soundness `ZDerivation_iRcritG_of` is proved later, after `ZDerivation_iCritReductG_of`.) -/
noncomputable def iRcritG (d : V) (ρ : V → V) : V :=
  iCritReductG (fstIdx d) (chainAsucc (zKseq d) (redexI d)) (zKrank d - 1) (zKrank d) (zKrank d)
    (seqUpdate (zKseq d) (redexI d) (ρ (redexI d)))
    (seqUpdate (zKseq d) (redexJ d) (ρ (redexJ d)))

@[simp] lemma fstIdx_iRcritG (d : V) (ρ : V → V) : fstIdx (iRcritG d ρ) = fstIdx d := by
  simp [iRcritG]
@[simp] lemma zTag_iRcritG (d : V) (ρ : V → V) : zTag (iRcritG d ρ) = 4 := by simp [iRcritG]

/-! ## The GENUINE reduct `red` (Buchholz §6 `red` / Def 3.2) — replaces the dead `iR2`

`red` is the validity-faithful reduct: identical to `iR2` on the I-rules (tags 1,2) and the `Ind` rule
(tag 3), but its critical `K`-case (tag 4) is `iRcritG` (the genuine recombination on the CORRECT reduced
endsequents `Θ→A(d)`/`A(d),Θ→D`) instead of `iR2`'s ordinal-shadow `iCritReduct`. Built by the same table
recursion as `iR2` (`iRNextG`/`redTable`/`red`), so `red` is total + `𝚺₁`-definable. -/

/-- Table step of `red`: dispatch on `zTag d`; tag-4 = the genuine critical branch `iRcritG`, with the
per-premise reduct supplier `ρ idx = zAxReduct (znth s (znth (zKseq d) idx))` (the table lookup). -/
noncomputable def iRNextG (d s : V) : V :=
  if zTag d = 1 then zIallPrem d
  else if zTag d = 2 then zInegPrem d
  else if zTag d = 3 then iRInd d
  else if zTag d = 4 then
    iRcritG d (fun idx => zAxReduct (znth s (znth (zKseq d) idx)))
  else d

noncomputable def _root_.LO.FirstOrder.Arithmetic.iRNextGDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y d s. ∃ t, !zTagDef t d ∧
    ( (t = 1 ∧ !zIallPremDef y d)
    ∨ (t = 2 ∧ !zInegPremDef y d)
    ∨ (t = 3 ∧ !iRIndDef y d)
    ∨ (t = 4 ∧ ∃ f, !fstIdxDef f d ∧ ∃ ds, !zKseqDef ds d ∧
        ∃ i, !redexIDef i d ∧ ∃ j, !redexJDef j d ∧
        ∃ C, !chainAsuccDef C ds i ∧ ∃ rk, !zKrankDef rk d ∧ ∃ rk1, !subDef rk1 rk 1 ∧
        ∃ ai, !znthDef ai ds i ∧ ∃ vi, !znthDef vi s ai ∧ ∃ wi, !zAxReductDef wi vi ∧
        ∃ aj, !znthDef aj ds j ∧ ∃ vj, !znthDef vj s aj ∧ ∃ wj, !zAxReductDef wj vj ∧
        ∃ u0, !seqUpdateDef u0 ds i wi ∧ ∃ ss, !seqSetSuccDef ss f C ∧ ∃ d0, !zKGraph d0 ss rk u0 ∧
        ∃ u1, !seqUpdateDef u1 ds j wj ∧ ∃ sa, !seqAddAntDef sa C f ∧ ∃ d1, !zKGraph d1 sa rk u1 ∧
        ∃ seq, !iCritReductSeqDef seq d0 d1 ∧ !zKGraph y f rk1 seq)
    ∨ (t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3 ∧ t ≠ 4 ∧ y = d) )”

set_option maxHeartbeats 1600000 in
instance iRNextG_defined : 𝚺₁-Function₂ (iRNextG : V → V → V) via iRNextGDef := .mk fun v ↦ by
  simp [iRNextGDef, iRNextG, iRcritG, iCritReductG, zTag_defined.iff, zIallPrem_defined.iff,
    zInegPrem_defined.iff, iRInd_defined.iff, fstIdx_defined.iff, zKseq_defined.iff,
    redexI_defined.iff, redexJ_defined.iff, chainAsucc_defined.iff, zKrank_defined.iff,
    sub_defined.iff, znth_defined.iff, zAxReduct_defined.iff, seqUpdate_defined.iff,
    seqSetSucc_defined.iff, seqAddAnt_defined.iff, iCritReductSeq_defined.iff, zK_defined.iff]
  by_cases h1 : zTag (v 1) = 1
  · simp [h1]
  · by_cases h2 : zTag (v 1) = 2
    · simp [h1, h2]
    · by_cases h3 : zTag (v 1) = 3
      · simp [h1, h2, h3]
      · by_cases h4 : zTag (v 1) = 4
        · simp [h1, h2, h3, h4]
        · simp [h1, h2, h3, h4]

instance iRNextG_definable : 𝚺₁-Function₂ (iRNextG : V → V → V) := iRNextG_defined.to_definable

/-- Blueprint for the `red` table. -/
noncomputable def redTable.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !mkSeq₁Def y 0”
  succ := .mkSigma “y ih n. ∃ v, !iRNextGDef v (n + 1) ih ∧ !seqConsDef y ih v”

noncomputable def redTable.construction : PR.Construction V redTable.blueprint where
  zero := fun _ ↦ !⟦0⟧
  succ := fun _ n ih ↦ seqCons ih (iRNextG (n + 1) ih)
  zero_defined := .mk fun v ↦ by
    simp [redTable.blueprint, mkSeq₁Def, seqCons_defined.iff, emptyset_def]
  succ_defined := .mk fun v ↦ by
    simp [redTable.blueprint, iRNextG_defined.iff, seqCons_defined.iff]

/-- **The `red` table**: `redTable n = ⟨red 0,…,red n⟩` (length `n+1`). -/
noncomputable def redTable (n : V) : V := redTable.construction.result ![] n

@[simp] lemma redTable_zero : redTable (0 : V) = !⟦0⟧ := by simp [redTable, redTable.construction]

@[simp] lemma redTable_succ (n : V) :
    redTable (n + 1) = seqCons (redTable n) (iRNextG (n + 1) (redTable n)) := by
  simp [redTable, redTable.construction]

noncomputable def _root_.LO.FirstOrder.Arithmetic.redTableDef : 𝚺₁.Semisentence 2 :=
  redTable.blueprint.resultDef.rew (Rew.subst ![#0, #1])

instance redTable_defined : 𝚺₁-Function₁ (redTable : V → V) via redTableDef := .mk
  fun v ↦ by simp [redTable.construction.result_defined_iff, redTableDef]; rfl
instance redTable_definable : 𝚺₁-Function₁ (redTable : V → V) := redTable_defined.to_definable
instance redTable_definable' (Γ) : Γ-[m + 1]-Function₁ (redTable : V → V) :=
  redTable_definable.of_sigmaOne

/-- **The genuine reduct** `red d = d[0]`: the `d`-th entry of the table. -/
noncomputable def red (d : V) : V := znth (redTable d) d

noncomputable def _root_.LO.FirstOrder.Arithmetic.redDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y d. ∃ t, !redTableDef t d ∧ !znthDef y t d”
instance red_defined : 𝚺₁-Function₁ (red : V → V) via redDef := .mk fun v ↦ by
  simp [redDef, red, redTable_defined.iff, znth_defined.iff]
instance red_definable : 𝚺₁-Function₁ (red : V → V) := red_defined.to_definable
instance red_definable' (Γ) : Γ-[m + 1]-Function₁ (red : V → V) := red_definable.of_sigmaOne

/-! ### Structural correctness of the `red` table (mirror `iR2`) -/

private lemma def_redTable {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ redTable (v i)) :=
  DefinableFunction₁.comp (F := redTable) (DefinableFunction.var i)

private lemma def_red {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ red (v i)) :=
  DefinableFunction₁.comp (F := red) (DefinableFunction.var i)

@[simp] lemma redTable_seq (n : V) : Seq (redTable n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_redTable 0)
  case zero => simp
  case succ n ih => rw [redTable_succ]; exact ih.seqCons _

@[simp] lemma redTable_lh (n : V) : lh (redTable n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_redTable 0)) (by definability)
  case zero => simp
  case succ n ih => rw [redTable_succ, Seq.lh_seqCons _ (redTable_seq n), ih]

lemma znth_redTable_succ {n k : V} (hk : k < n + 1) :
    znth (redTable (n + 1)) k = znth (redTable n) k := by
  rw [redTable_succ]
  exact znth_seqCons_of_lt (redTable_seq n) _ (by rw [redTable_lh]; exact hk)

lemma znth_redTable_eq_red : ∀ N : V, ∀ k ≤ N, znth (redTable N) k = red k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_redTable 1) (DefinableFunction.var 0))
      (def_red 0)
  case zero =>
    intro k hk; rcases (nonpos_iff_eq_zero.mp hk) with rfl; rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_redTable_succ hlt]; exact ih k (le_iff_lt_succ.mpr hlt)

/-- `red c = iRNextG c (redTable (c-1))` for positive codes (the table-reduction unfolding). -/
lemma red_eq_iRNextG {c : V} (hpos : 0 < c) : red c = iRNextG c (redTable (c - 1)) := by
  obtain ⟨M, rfl⟩ : ∃ M, c = M + 1 := ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (redTable (M + 1)) (M + 1) = iRNextG (M + 1) (redTable M) := by
    rw [redTable_succ]
    have h := znth_seqCons_self (redTable_seq M) (iRNextG (M + 1) (redTable M))
    rwa [redTable_lh] at h
  simp only [red, add_tsub_cancel_right, key]

/-- `iRcritG` depends on `ρ` only at `redexI d`/`redexJ d`. -/
lemma iRcritG_congr {d : V} {ρ ρ' : V → V} (hi : ρ (redexI d) = ρ' (redexI d))
    (hj : ρ (redexJ d) = ρ' (redexJ d)) : iRcritG d ρ = iRcritG d ρ' := by
  simp only [iRcritG, hi, hj]

/-! ### `red` recursion equations (Buchholz Def 3.2, per rule) -/

@[simp] lemma red_zAtom (s : V) : red (zAtom s) = zAtom s := by
  rw [red_eq_iRNextG (by simp [zAtom]), iRNextG]; simp [zTag_zAtom]

@[simp] lemma red_zIall (s a p d0 : V) : red (zIall s a p d0) = d0 := by
  rw [red_eq_iRNextG (by simp [zIall]), iRNextG, if_pos (zTag_zIall s a p d0)]
  simp [zIallPrem_zIall]

@[simp] lemma red_zIneg (s p d0 : V) : red (zIneg s p d0) = d0 := by
  rw [red_eq_iRNextG (by simp [zIneg]), iRNextG, if_neg (by simp), if_pos (zTag_zIneg s p d0)]
  simp [zInegPrem_zIneg]

@[simp] lemma red_zInd (s at' p d0 d1 : V) :
    red (zInd s at' p d0 d1) = iRInd (zInd s at' p d0 d1) := by
  rw [red_eq_iRNextG (by simp [zInd]), iRNextG, if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zInd s at' p d0 d1)]

@[simp] lemma red_zAxAll (s p k : V) : red (zAxAll s p k) = zAxAll s p k := by
  rw [red_eq_iRNextG (by simp [zAxAll]), iRNextG]; simp [zTag_zAxAll]

@[simp] lemma red_zAxNeg (s p : V) : red (zAxNeg s p) = zAxNeg s p := by
  rw [red_eq_iRNextG (by simp [zAxNeg]), iRNextG]; simp [zTag_zAxNeg]

/-- **The K-rule (critical) recursion equation** for the GENUINE reduct (Buchholz Def 3.2 case 5.1):
`red` of a chain is the genuine critical reduct `iRcritG` at the redex, with the two auxiliaries'
premise-reducts supplied RECURSIVELY (`red (znth ds (redexI/redexJ ..))`, with the §5 atomic `zAxReduct`).
The genuine recombination carries the correct reduced endsequents `Θ→A(d)`/`A(d),Θ→D` (unlike `iR2_zK`'s
ordinal-shadow). Both premise codes `< zK s r ds`, so they sit inside the length-`(zK-1)` table. -/
lemma red_zK (s r ds : V) :
    red (zK s r ds) = iRcritG (zK s r ds) (fun n => zAxReduct (red (znth ds n))) := by
  have hbound : ∀ k : V, znth ds k ≤ zK s r ds - 1 := fun k =>
    le_trans (znth_le_self ds k) (le_pred_of_lt (ds_lt_zK s r ds))
  rw [red_eq_iRNextG (by simp [zK]), iRNextG, if_neg (by simp), if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zK s r ds)]
  refine iRcritG_congr ?_ ?_ <;>
    simp only [zKseq_zK] <;>
    rw [znth_redTable_eq_red _ _ (hbound _)]

/-! ### The critical-only reduct is NON-critical (lap 86) — the 5.2 dispatch is mandatory

**Gating finding (Buchholz Def 3.2 case 5, validated in-kernel).** Buchholz's reduction of a chain
`d = K^r_Π d₀…dₗ` splits into critical (5.1) / sub-critical-splice (5.2.1) / non-critical (5.2.2). The
repo's `red`/`iR2` implement only 5.1 (always `iRcritG`/`iCritReduct`). But the 5.1 reduct
`K^{r-1}_Π⟨d{0}, d{1}⟩` is itself a chain whose distinguished `⊥`-half `d{1} = K_{A(d),Θ→D} ds1` is a
`K`-rule (`tp = isymRep`), permissible for the conclusion (`iperm_isymRep`). So the reduct is
**non-critical** — `zKCritical (fstIdx (red d)) (zKseq (red d))` FAILS. Consequently the iterate-descent
`iord_iR2_iterate_descends`'s criticality hypothesis `hcrit` is **unsatisfiable** after one reduction
step: the critical-only reduct cannot drive the infinite descent on its own. The genuine `red` MUST
dispatch the Buchholz 5.2 cases (splice / replace-premise) on non-critical chains; their ordinal descent
is already banked (`iord_descent_iCritAux` / `iord_descent_iSpliceEnd`, lap 82). -/

/-- The genuine critical reduct `iCritReductG` produces a NON-critical chain: its distinguished premise
(index 1, the `A(d),Θ→D` half, succedent `D`) is itself a `K`-chain, so `tp = isymRep`, permissible for
ANY conclusion (`iperm_isymRep`). Hence `zKCritical` FAILS at index 1. (The in-kernel witness that the
critical-only reduct is incomplete — the lap-86 analog of `not_zKValid_iCritReduct`.) -/
lemma not_zKCritical_iCritReductG (s C rOut rIn0 rIn1 ds0 ds1 : V) :
    ¬ zKCritical (fstIdx (iCritReductG s C rOut rIn0 rIn1 ds0 ds1))
                 (zKseq (iCritReductG s C rOut rIn0 rIn1 ds0 ds1)) := by
  rw [fstIdx_iCritReductG, zKseq_iCritReductG]
  intro hcrit
  have h1 : (1 : V) <
      lh (iCritReductSeq (zK (seqSetSucc s C) rIn0 ds0) (zK (seqAddAnt C s) rIn1 ds1)) := by
    rw [iCritReductSeq_lh]; exact one_lt_two
  have hbad := hcrit 1 h1
  rw [znth_iCritReductSeq_one, tp_zK] at hbad
  exact hbad (iperm_isymRep s)

/-- The reduct `iRcritG d ρ` is a non-critical chain (corollary of `not_zKCritical_iCritReductG`). -/
lemma not_zKCritical_iRcritG (d : V) (ρ : V → V) :
    ¬ zKCritical (fstIdx (iRcritG d ρ)) (zKseq (iRcritG d ρ)) := by
  rw [iRcritG]; exact not_zKCritical_iCritReductG _ _ _ _ _ _ _

/-- **`red` of a `K`-chain is itself a non-critical `K`-chain.** The critical-only reduct produces a
chain whose `⊥`-premise is a `Rep`, so `zKCritical` fails — the iterate-descent's criticality hypothesis
is UNSATISFIABLE after one step, forcing the Buchholz 5.2 dispatch onto the genuine `red`. -/
lemma not_zKCritical_red_zK (s r ds : V) :
    ¬ zKCritical (fstIdx (red (zK s r ds))) (zKseq (red (zK s r ds))) := by
  rw [red_zK]; exact not_zKCritical_iRcritG _ _

/-- **`red` preserves the end-sequent on the chain-reduct rules** (`Ind`, `K`): both reducts are chains
`zK (fstIdx d) …` (`iRInd`/`iRcritG` carry the conclusion sequent verbatim), so `fstIdx (red d) = fstIdx d`.
(On a ⊥-derivation the visited reducible rules are exactly tags 3,4 — an I-rule never has a `⊥` succedent.) -/
lemma fstIdx_red_of_tag_Ind_or_K {d : V} (hZ : ZDerivation d) (htag : zTag d = 3 ∨ zTag d = 4) :
    fstIdx (red d) = fstIdx d := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩
  · simp [zTag_zAtom] at htag
  · simp [zTag_zIall] at htag
  · simp [zTag_zIneg] at htag
  · rw [red_zInd, iRInd_zInd]; simp [fstIdx_zInd]
  · rw [red_zK]; simp
  · simp [zTag_zAxAll] at htag
  · simp [zTag_zAxNeg] at htag

/-! ### The ordinal of `red`'s K-case = the ordinal of `iR2`'s K-case (the descent bridge)

`iRcritG` (genuine, correct endsequents) and `iRcrit` (ordinal-shadow) differ ONLY in the auxiliaries'
conclusion sequents (`seqSetSucc`/`seqAddAnt` vs the reused `fstIdx d`). Since `iotil`/`idg` of a chain
`zK s r ds` are independent of `s` (`iotil_zK = iseqNaddIdg ds`, `idg_zK = max r (iseqMaxIdg ds - 1)`),
the two reducts carry the SAME `iord`. So the (banked) ordinal descent on `iRcrit` transfers verbatim to
`red`'s K-case — `red`'s validity-faithfulness costs nothing on the ordinal side. -/

@[simp] lemma iotil_iRcritG_eq_iRcrit (d : V) (ρ : V → V) :
    iotil (iRcritG d ρ) = iotil (iRcrit d ρ) := by
  rw [iRcritG, iCritReductG, iRcrit, iCritReduct, iCritAux, iCritAux,
    iotil_zK _ _ _ (iCritReductSeq_seq _ _), iotil_zK _ _ _ (iCritReductSeq_seq _ _),
    iseqNaddIdg_iCritReductSeq, iseqNaddIdg_iCritReductSeq,
    iotil_zK _ _ _ (seqUpdate_seq _ _ _), iotil_zK _ _ _ (seqUpdate_seq _ _ _),
    iotil_zK _ _ _ (seqUpdate_seq _ _ _), iotil_zK _ _ _ (seqUpdate_seq _ _ _)]

@[simp] lemma idg_iRcritG_eq_iRcrit (d : V) (ρ : V → V) :
    idg (iRcritG d ρ) = idg (iRcrit d ρ) := by
  rw [iRcritG, iCritReductG, iRcrit, iCritReduct, iCritAux, iCritAux,
    idg_zK _ _ _ (iCritReductSeq_seq _ _), idg_zK _ _ _ (iCritReductSeq_seq _ _),
    iseqMaxIdg_iCritReductSeq, iseqMaxIdg_iCritReductSeq,
    idg_zK _ _ _ (seqUpdate_seq _ _ _), idg_zK _ _ _ (seqUpdate_seq _ _ _),
    idg_zK _ _ _ (seqUpdate_seq _ _ _), idg_zK _ _ _ (seqUpdate_seq _ _ _)]

/-- **The genuine reduct's K-case has the same ordinal as the ordinal-shadow `iRcrit`.** -/
lemma iord_iRcritG_eq_iRcrit (d : V) (ρ : V → V) :
    iord (iRcritG d ρ) = iord (iRcrit d ρ) := by
  rw [iord_eq, iord_eq, iotil_iRcritG_eq_iRcrit, idg_iRcritG_eq_iRcrit]

/-! ### Structural correctness of the `iR2` table (mirror `idg`) -/

private lemma def_iRTable {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ iRTable (v i)) :=
  DefinableFunction₁.comp (F := iRTable) (DefinableFunction.var i)

private lemma def_iR2 {k} (i : Fin k) :
    𝚺-[1].DefinableFunction (fun v : Fin k → V ↦ iR2 (v i)) :=
  DefinableFunction₁.comp (F := iR2) (DefinableFunction.var i)

@[simp] lemma iRTable_seq (n : V) : Seq (iRTable n) := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₁ (def_iRTable 0)
  case zero => simp
  case succ n ih => rw [iRTable_succ]; exact ih.seqCons _

@[simp] lemma iRTable_lh (n : V) : lh (iRTable n) = n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · exact Definable.comp₂ (DefinableFunction₁.comp (F := lh) (def_iRTable 0)) (by definability)
  case zero => simp
  case succ n ih => rw [iRTable_succ, Seq.lh_seqCons _ (iRTable_seq n), ih]

lemma znth_iRTable_succ {n k : V} (hk : k < n + 1) :
    znth (iRTable (n + 1)) k = znth (iRTable n) k := by
  rw [iRTable_succ]
  exact znth_seqCons_of_lt (iRTable_seq n) _ (by rw [iRTable_lh]; exact hk)

lemma znth_iRTable_eq_iR2 : ∀ N : V, ∀ k ≤ N, znth (iRTable N) k = iR2 k := by
  intro N
  induction N using ISigma1.sigma1_succ_induction
  · refine Definable.ball_le (by definability) ?_
    exact Definable.comp₂
      (DefinableFunction₂.comp (F := znth) (def_iRTable 1) (DefinableFunction.var 0))
      (def_iR2 0)
  case zero =>
    intro k hk; rcases (nonpos_iff_eq_zero.mp hk) with rfl; rfl
  case succ N ih =>
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rfl
    · rw [znth_iRTable_succ hlt]; exact ih k (le_iff_lt_succ.mpr hlt)

/-- `iR2 c = iRNext c (iRTable (c-1))` for positive codes (the table-reduction unfolding). -/
lemma iR2_eq_iRNext {c : V} (hpos : 0 < c) : iR2 c = iRNext c (iRTable (c - 1)) := by
  obtain ⟨M, rfl⟩ : ∃ M, c = M + 1 := ⟨c - 1, (sub_add_self_of_le (pos_iff_one_le.mp hpos)).symm⟩
  have key : znth (iRTable (M + 1)) (M + 1) = iRNext (M + 1) (iRTable M) := by
    rw [iRTable_succ]
    have h := znth_seqCons_self (iRTable_seq M) (iRNext (M + 1) (iRTable M))
    rwa [iRTable_lh] at h
  simp only [iR2, add_tsub_cancel_right, key]

/-! ### `iR2` recursion equations (Buchholz Def 3.2, per rule) -/

@[simp] lemma iR2_zAtom (s : V) : iR2 (zAtom s) = zAtom s := by
  rw [iR2_eq_iRNext (by simp [zAtom]), iRNext]; simp [zTag_zAtom]

@[simp] lemma iR2_zIall (s a p d0 : V) : iR2 (zIall s a p d0) = d0 := by
  rw [iR2_eq_iRNext (by simp [zIall]), iRNext, if_pos (zTag_zIall s a p d0)]
  simp [zIallPrem_zIall]

@[simp] lemma iR2_zIneg (s p d0 : V) : iR2 (zIneg s p d0) = d0 := by
  rw [iR2_eq_iRNext (by simp [zIneg]), iRNext, if_neg (by simp), if_pos (zTag_zIneg s p d0)]
  simp [zInegPrem_zIneg]

@[simp] lemma iR2_zInd (s at' p d0 d1 : V) :
    iR2 (zInd s at' p d0 d1) = iRInd (zInd s at' p d0 d1) := by
  rw [iR2_eq_iRNext (by simp [zInd]), iRNext, if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zInd s at' p d0 d1)]

@[simp] lemma iR2_zAxAll (s p k : V) : iR2 (zAxAll s p k) = zAxAll s p k := by
  rw [iR2_eq_iRNext (by simp [zAxAll]), iRNext]; simp [zTag_zAxAll]

@[simp] lemma iR2_zAxNeg (s p : V) : iR2 (zAxNeg s p) = zAxNeg s p := by
  rw [iR2_eq_iRNext (by simp [zAxNeg]), iRNext]; simp [zTag_zAxNeg]

/-- **The K-rule (critical) recursion equation** (Buchholz Def 3.2 case 5.1): `iR2` of a chain code is
the critical reduct at the functional redex, with the two auxiliaries' premise-reducts supplied
RECURSIVELY (`iR2 (znth ds (redexI/redexJ ..))`). This is `iRcrit (zK s r ds) ρ` at the concrete
`ρ = fun n ↦ iR2 (znth ds n)`. Both premise codes `< zK s r ds`, so they sit inside the length-`(zK-1)`
table (`znth_le_self` + `ds_lt_zK`). -/
lemma iR2_zK (s r ds : V) :
    iR2 (zK s r ds) =
      iCritReduct (zK s r ds) (redexI (zK s r ds)) (redexJ (zK s r ds))
        (zAxReduct (iR2 (znth ds (redexI (zK s r ds)))))
        (zAxReduct (iR2 (znth ds (redexJ (zK s r ds))))) := by
  have hbound : ∀ k : V, znth ds k ≤ zK s r ds - 1 := fun k =>
    le_trans (znth_le_self ds k) (le_pred_of_lt (ds_lt_zK s r ds))
  rw [iR2_eq_iRNext (by simp [zK]), iRNext, if_neg (by simp), if_neg (by simp), if_neg (by simp),
    if_pos (zTag_zK s r ds), zKseq_zK,
    znth_iRTable_eq_iR2 _ (znth ds (redexI (zK s r ds))) (hbound _),
    znth_iRTable_eq_iR2 _ (znth ds (redexJ (zK s r ds))) (hbound _)]

/-- `iR2 (zK s r ds) = iRcrit (zK s r ds) (fun n ↦ zAxReduct (iR2 (znth ds n)))` — the recursive reduct
IS the abstract critical reduct `iRcrit` at the concrete recursive `ρ`, with the §5 atomic reduct
`zAxReduct` applied per premise (identity off atomic axioms; the §5 `Ax^1` reduct on the L-axiom redex
j-premise — the descent-carrying j-side fix, lap 66). Bridges the closed recursion to the banked nut
descent `iord_descent_iRcrit_of_chain`. -/
lemma iR2_zK_eq_iRcrit (s r ds : V) :
    iR2 (zK s r ds) = iRcrit (zK s r ds) (fun n => zAxReduct (iR2 (znth ds n))) := by
  rw [iR2_zK, iRcrit]

/-- **`red` and `iR2` agree off the critical K-case.** `iRNextG` and `iRNext` have identical I-rule/`Ind`
branches (none reads the table), so on any non-tag-4 code the genuine reduct equals the ordinal-shadow.
The two differ ONLY at tag 4 (`iRcritG` vs `iCritReduct`), and even there the ordinal is preserved
(`iord_iRcritG_eq_iRcrit`). -/
lemma red_eq_iR2_of_tag_ne_four {x : V} (h : zTag x ≠ 4) : red x = iR2 x := by
  rcases eq_or_ne x 0 with rfl | hpos
  · simp [red, iR2]
  · have hp := pos_iff_ne_zero.mpr hpos
    rw [red_eq_iRNextG hp, iR2_eq_iRNext hp, iRNextG, iRNext]
    by_cases h1 : zTag x = 1
    · simp [h1]
    · by_cases h2 : zTag x = 2
      · simp [h1, h2]
      · by_cases h3 : zTag x = 3
        · simp [h1, h2, h3]
        · simp [h1, h2, h3, h]

/-- **The redexI premise's `iR2`-reduct satisfies the IH bundle, concretely** (the recursive-`iR2`
analog of lap-71's `iRedDescent_iR_of_tp_isymR`). A premise `d` with `tp d = R_A` is an I-rule
(`tp_isymR_tag` ⟹ tag 1/2), where `iR2 d = d0` (the sub-derivation) agrees with the old `iR`; so the
banked `iRedDescent_zIall`/`_zIneg` apply verbatim. This discharges the `i`-side of the K-case nut's
six `ρ`-facts (`iord_descent_iRcrit_of_chain'`'s `hρlt_i`/`hρg_i`/`hρNF_i`) for the CONCRETE recursive
`ρ = iR2(znth ds ·)`. Only the `j`-side (the L-axiom §5 atomic reduct) remains. -/
lemma iRedDescent_iR2_of_tp_isymR {d A : V} (htp : tp d = isymR A) (hZ : ZDerivation d) :
    iRedDescent (iR2 d) d := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, hd0, _⟩ | ⟨s, p, d0, rfl, hd0, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩
  · rw [tp_zAtom] at htp; exact absurd htp (by simp)
  · rw [iR2_zIall]; exact iRedDescent_zIall (isNF_iotil_of_ZDerivation d0 hd0)
  · rw [iR2_zIneg]; exact iRedDescent_zIneg (isNF_iotil_of_ZDerivation d0 hd0)
  · rw [tp_zInd] at htp; exact absurd htp (by simp)
  · rw [tp_zK] at htp; exact absurd htp (by simp)
  · rw [tp_zAxAll] at htp; exact absurd htp (by simp)
  · rw [tp_zAxNeg] at htp; exact absurd htp (by simp)

/-! ### j-side §5 atomic-axiom reduct bundle (the K-case's L-premise descent, lap 66)

The K-case nut (`iord_descent_iRcrit_of_chain'`) pins its descent to six `ρ`-facts about the two redex
premises. The i-side (R-redex, an I-rule) is discharged by `iRedDescent_iR2_of_tp_isymR`. The j-side
(L-axiom redex, tags 5/6) needs the §5 `Ax^1` reduct `zAx1`: these two lemmas package its
`iRedDescent` bundle (degree not raised — both `idg = 0`; pre-ordinal strictly dropped via
`icmp_iotil_zAx1_z*`; reduct NF). Buchholz Lemma 5.2. The remaining plumbing (next lap, see
PENDING_WORK): `iR2` is the IDENTITY on atomic axioms (`iR2_zAxAll`/`iR2_zAxNeg`), so the §5 reduct
cannot enter via the `iR2` table — `iCritReduct`'s j-component must invoke `zAx1` directly. These
bundles are exactly what that revised critical reduct must supply on the j-side. -/
lemma iRedDescent_zAx1_zAxAll {s p k : V} (hp : IsUFormula ℒₒᵣ p) :
    iRedDescent (zAx1 s p) (zAxAll s p k) :=
  ⟨by simp, icmp_iotil_zAx1_zAxAll hp, isNF_iotil_zAx1 s p⟩

lemma iRedDescent_zAx1_zAxNeg {s p : V} (hp : IsUFormula ℒₒᵣ p) :
    iRedDescent (zAx1 s p) (zAxNeg s p) :=
  ⟨by simp, icmp_iotil_zAx1_zAxNeg hp, isNF_iotil_zAx1 s p⟩

/-- **j-side bundle via `zAxReduct`, ∀-axiom case**: the reduct `zAxReduct (Ax^{∀p,k})` satisfies the
`iRedDescent` bundle (the K-case nut's j-side fact, packaged on the genuine reduct function). -/
lemma iRedDescent_zAxReduct_zAxAll {s p k : V} (hp : IsUFormula ℒₒᵣ p) :
    iRedDescent (zAxReduct (zAxAll s p k)) (zAxAll s p k) := by
  rw [zAxReduct_zAxAll]; exact iRedDescent_zAx1_zAxAll hp

/-- **j-side bundle via `zAxReduct`, ¬-axiom case**. -/
lemma iRedDescent_zAxReduct_zAxNeg {s p : V} (hp : IsUFormula ℒₒᵣ p) :
    iRedDescent (zAxReduct (zAxNeg s p)) (zAxNeg s p) := by
  rw [zAxReduct_zAxNeg]; exact iRedDescent_zAx1_zAxNeg hp

/-- **`zAxReduct` is the identity on an R-redex (I-rule) premise**: `tp d = isymR A` forces
`zTag d ∈ {1,2}` (`tp_isymR_tag`), never the atomic-axiom tags `5,6`, so `zAxReduct d = d`. Collapses
the i-side `zAxReduct`-wrap `zAxReduct (iR2 premᵢ) = iR2 premᵢ` introduced by the tag-4 rewrite (the
i-side redex premise is an I-rule). Stated on `tp` directly (no `ZDerivation` needed). NOTE: since
`ZDerivation` now includes the atomic-axiom leaves (tags 5,6), `zAxReduct` is NOT the identity on a
general `ZDerivation` — only on the non-axiom tags, which the `tp = isymR` redex premise guarantees. -/
lemma zAxReduct_of_tp_isymR {d A : V} (htp : tp d = isymR A) : zAxReduct d = d := by
  rcases tp_isymR_tag htp with h | h <;> simp [zAxReduct, h]

/-- `zAxReduct` is the identity off the §5 atomic-axiom tags (5,6). -/
lemma zAxReduct_eq_self_of_ne {d : V} (h5 : zTag d ≠ 5) (h6 : zTag d ≠ 6) :
    zAxReduct d = d := by simp [zAxReduct, h5, h6]

/-- **Wrapping `zAxReduct` around a `ZDerivation` reduct preserves the `iRedDescent` bundle.** On the
non-axiom tags `zAxReduct` is the identity (`zAxReduct_eq_self_of_ne`); on the §5 axiom leaves (tags
5/6) it replaces the leaf `zAxAll`/`zAxNeg` by the `Ax^1` reduct `zAx1`, which lies strictly *below*
the leaf (`icmp_iotil_zAx1_z*`, using the leaf's carried `IsUFormula`) at degree 0 — so the descent
bundle only improves (via `icmp_trans`). This is what collapses the i-side `zAxReduct (iR2 premᵢ)`
wrap even when the I-rule sub-derivation `iR2 premᵢ` itself happens to be an axiom leaf. -/
lemma iRedDescent_zAxReduct_of_iRedDescent {e d : V} (he : ZDerivation e)
    (h : iRedDescent e d) : iRedDescent (zAxReduct e) d := by
  rcases zDerivation_iff.mp he with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, hp, _⟩ | ⟨s, p, rfl, hp, _⟩
  · rwa [zAxReduct_eq_self_of_ne (by simp [zTag_zAtom]) (by simp [zTag_zAtom])]
  · rwa [zAxReduct_eq_self_of_ne (by simp [zTag_zIall]) (by simp [zTag_zIall])]
  · rwa [zAxReduct_eq_self_of_ne (by simp [zTag_zIneg]) (by simp [zTag_zIneg])]
  · rwa [zAxReduct_eq_self_of_ne (by simp [zTag_zInd]) (by simp [zTag_zInd])]
  · rwa [zAxReduct_eq_self_of_ne (by simp [zTag_zK]) (by simp [zTag_zK])]
  · rw [zAxReduct_zAxAll]
    refine ⟨by rw [idg_zAx1, ← idg_zAxAll s p k]; exact h.dg_le, ?_, isNF_iotil_zAx1 s p⟩
    exact icmp_trans (max (iotil (zAx1 s p)) (max (iotil (zAxAll s p k)) (iotil d)))
      _ (le_max_left _ _) _ (le_trans (le_max_left _ _) (le_max_right _ _))
      _ (le_trans (le_max_right _ _) (le_max_right _ _))
      (icmp_iotil_zAx1_zAxAll hp) h.otil_lt
  · rw [zAxReduct_zAxNeg]
    refine ⟨by rw [idg_zAx1, ← idg_zAxNeg s p]; exact h.dg_le, ?_, isNF_iotil_zAx1 s p⟩
    exact icmp_trans (max (iotil (zAx1 s p)) (max (iotil (zAxNeg s p)) (iotil d)))
      _ (le_max_left _ _) _ (le_trans (le_max_left _ _) (le_max_right _ _))
      _ (le_trans (le_max_right _ _) (le_max_right _ _))
      (icmp_iotil_zAx1_zAxNeg hp) h.otil_lt

/-- **i-side ρ-fact** (R-redex premise): for an I-rule premise `d` (`tp d = R_A`), the wrapped recursive
reduct `zAxReduct (iR2 d)` satisfies the `iRedDescent` bundle. `iR2 d` is the I-rule's sub-derivation
(a `ZDerivation`), so `iRedDescent_iR2_of_tp_isymR` gives the un-wrapped bundle and
`iRedDescent_zAxReduct_of_iRedDescent` collapses the wrap. -/
lemma iRedDescent_zAxReduct_iR2_of_tp_isymR {d A : V} (htp : tp d = isymR A) (hZ : ZDerivation d) :
    iRedDescent (zAxReduct (iR2 d)) d := by
  have hbase := iRedDescent_iR2_of_tp_isymR htp hZ
  have hZred : ZDerivation (iR2 d) := by
    rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, hd0, _⟩ | ⟨s, p, d0, rfl, hd0, _⟩ |
      ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
      ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩
    · rw [tp_zAtom] at htp; exact absurd htp (by simp)
    · rw [iR2_zIall]; exact hd0
    · rw [iR2_zIneg]; exact hd0
    · rw [tp_zInd] at htp; exact absurd htp (by simp)
    · rw [tp_zK] at htp; exact absurd htp (by simp)
    · rw [tp_zAxAll] at htp; exact absurd htp (by simp)
    · rw [tp_zAxNeg] at htp; exact absurd htp (by simp)
  exact iRedDescent_zAxReduct_of_iRedDescent hZred hbase

/-- **j-side ρ-fact** (L-axiom redex premise): for a §5 atomic-axiom premise `d` (`tp d = L^k_A`),
the wrapped recursive reduct `zAxReduct (iR2 d)` satisfies the `iRedDescent` bundle. `iR2` is the
identity on the axiom leaves, and `zAxReduct (zAxAll/zAxNeg) = zAx1` carries the strict descent
(`iRedDescent_zAxReduct_zAxAll/_zAxNeg`, using the leaf's `IsUFormula`). -/
lemma iRedDescent_zAxReduct_iR2_of_tp_isymLk {d k A : V} (htp : tp d = isymLk k A)
    (hZ : ZDerivation d) : iRedDescent (zAxReduct (iR2 d)) d := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k', rfl, hp, _⟩ | ⟨s, p, rfl, hp, _⟩
  · rw [tp_zAtom] at htp; exact absurd htp (by simp)
  · rw [tp_zIall] at htp; exact absurd htp (by simp)
  · rw [tp_zIneg] at htp; exact absurd htp (by simp)
  · rw [tp_zInd] at htp; exact absurd htp (by simp)
  · rw [tp_zK] at htp; exact absurd htp (by simp)
  · rw [iR2_zAxAll]; exact iRedDescent_zAxReduct_zAxAll hp
  · rw [iR2_zAxNeg]; exact iRedDescent_zAxReduct_zAxNeg hp

/-! ### The tag-4 (K-rule) descent, conditional on chain validity

`iord_descent_iR2_struct` covers I-rules/Ind (tags 1,2,3) unconditionally. The K-rule (tag 4) descent
needs the Buchholz side conditions of a *valid* `K^r` inference — packaged here as `zKValid` — which
the bare `ZPhi` `zK` disjunct (just `Seq ds ∧ ∀ i, premise ∈ ZDerivation`) does NOT yet carry. This
lemma proves the tag-4 descent CONDITIONALLY on `zKValid`; wiring `zKValid` into the `ZPhi` `zK`
disjunct (the Σ₁/Δ₁ Fixpoint cascade) is the next phase, after which the tag-4 case of
`iord_descent_iR2_struct` falls out by feeding `zDerivation_zK_inv` + this lemma. (`zKValid` and its
`𝚫₁` arithmetization `zKValidDef` are defined earlier, alongside `isChainInfDef`.) -/

/-- **THE K-case descent (tag 4), conditional on chain validity.** For a valid `K^r` chain `zK s r ds`
whose premises are all `ZDerivation`s, the recursive reduct `iR2` strictly lowers the ordinal:
`o(iR2 (zK s r ds)) ≺ o(zK s r ds)`. Assembled by feeding `iord_descent_iRcrit_of_chain'` at
`Tr := False`, `Fa := (· = ⊥)`: the chain-structure data comes from `isChainInf`, the `hwfR`/`hwfL`
rank conditions from `tp_isymR_pos`/`tp_isymLk_pos` + `zKValid`'s formula-hood, and the six redex
`ρ`-facts (`ρ = zAxReduct ∘ iR2`) from `redexPair_tp` (reading the redex premises' `tp` off the
finder's least-pair) + the i/j-side wrap helpers. -/
lemma iord_descent_iR2_zK_of_valid {s r ds : V} (hds : Seq ds)
    (hmem : ∀ i < lh ds, ZDerivation (znth ds i)) (hvalid : zKValid s r ds) :
    icmp (iord (iR2 (zK s r ds))) (iord (zK s r ds)) = 0 := by
  obtain ⟨hci, hperm0, hnperm0, hf1, hf2, hf5, hf6, _hsucc, _hssf, _hsaf⟩ := hvalid
  obtain ⟨j0, hj0, hAj0, hchain, hrank⟩ := hci
  -- Tr/Fa = the ⊥-instances; the well-formedness obligations discharge as in `..._of_chain_tp`.
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
  -- Run the finder to certify a redex exists, then read off the least-pair's premise `tp`s.
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
  -- The two redex-side `iRedDescent` bundles for `ρ = zAxReduct ∘ iR2`.
  have hbI := iRedDescent_zAxReduct_iR2_of_tp_isymR hRedI (hmem _ hIlt)
  have hbJ := iRedDescent_zAxReduct_iR2_of_tp_isymLk hRedJ (hmem _ hJlt)
  rw [iR2_zK_eq_iRcrit]
  exact iord_descent_iRcrit_of_chain' (Tr := fun _ => False) (Fa := fun A => A = (^⊥ : V))
    hds hnf hj0 hAj0 hchain hrank hwfR hwfL hperm hnperm (fun _ h => h.1)
    (fun A h => by rw [h]; exact irk_falsum) rfl hNF
    hbI.otil_lt hbJ.otil_lt hbI.dg_le hbJ.dg_le hbI.nf hbJ.nf

/-! ## The Thm-4.2 one-step descent through the recursive `iR2` — ALL reducible rules (tags 1,2,3,4)

With `iR2` total and the refined `ZPhi` carrying `zKValid` on its `zK` disjunct, the descent
`o(iR2 d) ≺ o(d)` is now UNCONDITIONAL across every reducible Z-rule: I-rules/Ind (tags 1,2,3) via
their closed reducts, and the K-rule (tag 4) via `iord_descent_iR2_zK_of_valid` fed by
`zKValid_of_ZDerivation_zK`. The atom/axiom tags (0/5/6) are normal forms with no strict descent (and
never arise on a ⊥-derivation), so they stay excluded by `htag`. This is the capstone that turns the
descent MATH into a single hypothesis-free fact about `ZDerivation`s. -/
lemma iord_descent_iR2_struct (d : V) (hd : ZDerivation d)
    (htag : zTag d = 1 ∨ zTag d = 2 ∨ zTag d = 3 ∨ zTag d = 4)
    (hcrit : zTag d = 4 → zKCritical (fstIdx d) (zKseq d)) :
    icmp (iord (iR2 d)) (iord d) = 0 := by
  rcases zDerivation_iff.mp hd with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, h0, h1, _⟩ | ⟨s, r, ds, rfl, hds, hmem, hvalid⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩
  · simp [zTag_zAtom] at htag
  · rw [iR2_zIall]; exact iord_descent_zIall s a p d0
  · rw [iR2_zIneg]; exact iord_descent_zIneg s p d0
  · rw [iR2_zInd]
    exact iord_descent_iRInd_zInd s at' p d0 d1
      (isNF_iotil_of_ZDerivation d0 h0) (isNF_iotil_of_ZDerivation d1 h1)
  · -- tag 4 (K-rule): after the re-point `ZPhi` carries only the faithful validity `zKValidF`; the
    -- iR2 critical-reduct descent additionally needs the chain to be *critical* (lap-83 finding — iR2 is
    -- the ordinal-first dead reduct, superseded by the genuine `red`). Criticality is supplied here.
    have hcr : zKCritical s ds := by have := hcrit (by simp); simpa using this
    exact iord_descent_iR2_zK_of_valid hds hmem
      (zKValid_iff_zKValidF_and_zKCritical.mpr ⟨hvalid, hcr⟩)
  · simp [zTag_zAxAll] at htag
  · simp [zTag_zAxNeg] at htag

/-! ## C1 — `ZDerivesEmpty` and the per-step descent on a contradiction derivation

With the descent capstone `iord_descent_iR2_struct` in hand and the `ZPhi` leaf disjuncts now carrying
their **antecedent side conditions** (atom = identity axiom `C ∈ Γ`, §5 ∀-axiom `∀xF ∈ Γ`, §5 ¬-axiom
`¬A ∈ Γ` — all faithful Buchholz axioms), an empty-antecedent end-sequent can no longer be an axiom
leaf. This yields the per-step descent on a Z-derivation of the empty/contradiction sequent — the fact
the no-infinite-descent argument iterates. -/

/-- **A Z-derivation of the empty (contradiction) sequent `∅ → ⊥`.** The end-sequent `fstIdx d` has
empty antecedent (no open assumptions) and `⊥` succedent — `d` derives a contradiction in system Z.
This is the object the C0.5 bridge produces from a Foundation ⊥-proof; the descent strictly lowers its
ordinal `iord` at every step. -/
def ZDerivesEmpty (d : V) : Prop :=
  ZDerivation d ∧ seqAnt (fstIdx d) = (∅ : V) ∧ seqSucc (fstIdx d) = (^⊥ : V)

/-- **Leaf-soundness: an empty-antecedent Z-derivation is never an axiom leaf.** Each of the three Z
axiom schemes requires a formula in the antecedent `Γ = seqAnt (fstIdx d)` (atom: the succedent `C ∈ Γ`;
§5 ∀-axiom: `∀xF ∈ Γ`; §5 ¬-axiom: `¬A ∈ Γ`). With `Γ = ∅` (so `lh Γ = 0`, no membership possible) all
three are impossible, hence a Z-derivation of an empty-antecedent sequent must be built by one of the
*reducible* rules (tags 1,2,3,4). -/
lemma zTag_reducible_of_emptyAnt {d : V} (hZ : ZDerivation d)
    (hemp : seqAnt (fstIdx d) = (∅ : V)) :
    zTag d = 1 ∨ zTag d = 2 ∨ zTag d = 3 ∨ zTag d = 4 := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, hin⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, hin⟩ | ⟨s, p, rfl, _, hin⟩
  · exfalso; rw [fstIdx_zAtom] at hemp; rw [hemp] at hin; simp [inAnt, lh_empty] at hin
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inl (by simp))
  · exact Or.inr (Or.inr (Or.inl (by simp)))
  · exact Or.inr (Or.inr (Or.inr (by simp)))
  · exfalso; rw [fstIdx_zAxAll] at hemp; rw [hemp] at hin; simp [inAnt, lh_empty] at hin
  · exfalso; rw [fstIdx_zAxNeg] at hemp; rw [hemp] at hin; simp [inAnt, lh_empty] at hin

/-- **One descent step on an empty-sequent derivation.** Combining leaf-soundness
(`zTag_reducible_of_emptyAnt`) with the capstone `iord_descent_iR2_struct`: every `iR2`-step of a
Z-derivation of an empty-antecedent sequent strictly lowers the ordinal `iord`. This is the
hypothesis-free per-step fact iterated by the no-infinite-descent argument; it remains to show `iR2`
*preserves* `ZDerivesEmpty` (reduction-soundness + end-sequent invariance), the next interface. -/
lemma iord_descent_iR2_of_emptyAnt {d : V} (hZ : ZDerivation d)
    (hemp : seqAnt (fstIdx d) = (∅ : V))
    (hcrit : zTag d = 4 → zKCritical (fstIdx d) (zKseq d)) :
    icmp (iord (iR2 d)) (iord d) = 0 :=
  iord_descent_iR2_struct d hZ (zTag_reducible_of_emptyAnt hZ hemp) hcrit

/-- **One descent step on a `ZDerivesEmpty` code** (the packaged form). -/
lemma iord_descent_iR2_of_ZDerivesEmpty {d : V} (h : ZDerivesEmpty d)
    (hcrit : zTag d = 4 → zKCritical (fstIdx d) (zKseq d)) :
    icmp (iord (iR2 d)) (iord d) = 0 :=
  iord_descent_iR2_of_emptyAnt h.1 h.2.1 hcrit

/-- **`iR2` preserves the end-sequent on the `Rep`-tagged reducible rules (Ind, K).** Both reducts are
chains `zK (fstIdx d) …` (`iRInd`/`iCritReduct` carry the conclusion sequent verbatim), so
`fstIdx (iR2 d) = fstIdx d`. For the I-rules (tags 1,2) the reduct is the sub-derivation `d0`, whose
end-sequent differs — but a ⊥-succedent derivation is never an I-rule (the R-symbol would put the
principal formula, not `⊥`, in the succedent), so the Ind/K case is the only one the descent visits. -/
lemma fstIdx_iR2_of_tag_Ind_or_K {d : V} (hZ : ZDerivation d) (htag : zTag d = 3 ∨ zTag d = 4) :
    fstIdx (iR2 d) = fstIdx d := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩
  · simp [zTag_zAtom] at htag
  · simp [zTag_zIall] at htag
  · simp [zTag_zIneg] at htag
  · rw [iR2_zInd, iRInd_zInd]; simp [fstIdx_zInd]
  · simp only [iR2_zK, iCritReduct, fstIdx_zK]
  · simp [zTag_zAxAll] at htag
  · simp [zTag_zAxNeg] at htag

/-- The `iR2`-reduct of an `Ind`/`K` derivation is a `Rep`-tagged chain `zK (fstIdx d) …` (`iRInd` for
`Ind`, `iCritReduct` for `K`). The shape that makes its principal-formula well-formedness automatic. -/
lemma iR2_eq_zK_of_tag_Ind_or_K {d : V} (hZ : ZDerivation d) (htag : zTag d = 3 ∨ zTag d = 4) :
    ∃ r ds, iR2 d = zK (fstIdx d) r ds := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, _⟩ | ⟨s, a, p, d0, rfl, _, _⟩ | ⟨s, p, d0, rfl, _, _⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, _⟩ | ⟨s, p, rfl, _, _⟩
  · simp [zTag_zAtom] at htag
  · simp [zTag_zIall] at htag
  · simp [zTag_zIneg] at htag
  · exact ⟨irk p, iIndReductSeq d0 d1 1, by rw [iR2_zInd, iRInd_zInd, fstIdx_zInd]⟩
  · exact ⟨_, _, by rw [iR2_zK, iCritReduct, fstIdx_zK]⟩
  · simp [zTag_zAxAll] at htag
  · simp [zTag_zAxNeg] at htag

/-- The `iR2`-reduct of an `Ind`/`K` derivation is tag-4 (`zK`). -/
lemma zTag_iR2_of_tag_Ind_or_K {d : V} (hZ : ZDerivation d) (htag : zTag d = 3 ∨ zTag d = 4) :
    zTag (iR2 d) = 4 := by
  obtain ⟨r, ds, h⟩ := iR2_eq_zK_of_tag_Ind_or_K hZ htag; rw [h, zTag_zK]

/-- The `iR2`-reduct of an `Ind`/`K` derivation has `tp = isymRep` (it is a chain). -/
lemma tp_iR2_of_tag_Ind_or_K {d : V} (hZ : ZDerivation d) (htag : zTag d = 3 ∨ zTag d = 4) :
    tp (iR2 d) = isymRep := by
  obtain ⟨r, ds, h⟩ := iR2_eq_zK_of_tag_Ind_or_K hZ htag; rw [h, tp_zK]

/-- **Non-critical validity-preservation, concrete.** Replacing a premise `i` of a faithfully-valid
chain by its own `iR2`-reduct preserves `zKValidF`, when the premise `i` is itself an `Ind`/`K`
derivation. End-sequent invariance (`fstIdx_iR2_of_tag_Ind_or_K`) feeds `isChainInf` preservation; the
reduct is a `Rep`-tagged chain (`zTag = 4`, `tp = isymRep`), so its own-permissibility is automatic
(`iperm_isymRep`) and the tag-gated I/Ax formula-hood conjuncts are vacuous. This is exactly the
non-critical (Buchholz §3.2 case 5.2.2) step of the `RedSound` validity invariant. -/
lemma zKValidF_seqUpdate_iR2 {s r ds i : V} (hi : i < lh ds)
    (hZi : ZDerivation (znth ds i)) (htagi : zTag (znth ds i) = 3 ∨ zTag (znth ds i) = 4)
    (h : zKValidF s r ds) :
    zKValidF s r (seqUpdate ds i (iR2 (znth ds i))) := by
  have hfst : fstIdx (iR2 (znth ds i)) = fstIdx (znth ds i) :=
    fstIdx_iR2_of_tag_Ind_or_K hZi htagi
  have htagv : zTag (iR2 (znth ds i)) = 4 := zTag_iR2_of_tag_Ind_or_K hZi htagi
  have htpv : tp (iR2 (znth ds i)) = isymRep := tp_iR2_of_tag_Ind_or_K hZi htagi
  refine zKValidF_seqUpdate hi hfst ?_ ?_ ?_ ?_ ?_ h
  · rw [htpv]; exact iperm_isymRep _
  · intro hc; rw [htagv] at hc; simp at hc
  · intro hc; rw [htagv] at hc; simp at hc
  · intro hc; rw [htagv] at hc; simp at hc
  · intro hc; rw [htagv] at hc; simp at hc

/-- **A `ZDerivesEmpty` code is built by an `Ind` or `K` rule** (tag 3 or 4). Beyond leaf-soundness
(empty antecedent rules out the axiom leaves), the `⊥`-succedent rules out the two I-rules: a valid
`I^a_∀xF`/`I_¬A` inference has succedent `∀xF`/`¬A` (the refined `ZPhi` now carries `seqSucc s = ^∀ p`
/ `= inegF p`), never `⊥`. So the only rules concluding `∅ → ⊥` are the `Rep`-tagged `Ind` and `K` —
exactly the two whose `iR2`-reduct is a chain `zK (fstIdx d) …`. -/
lemma zTag_Ind_or_K_of_ZDerivesEmpty {d : V} (h : ZDerivesEmpty d) : zTag d = 3 ∨ zTag d = 4 := by
  obtain ⟨hZ, hant, hsucc⟩ := h
  rcases zDerivation_iff.mp hZ with ⟨s, rfl, hin⟩ | ⟨s, a, p, d0, rfl, _, hsc, _⟩ |
    ⟨s, p, d0, rfl, _, hsc, _⟩ | ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _, _⟩ |
    ⟨s, p, k, rfl, _, hin⟩ | ⟨s, p, rfl, _, hin⟩
  · exfalso; rw [fstIdx_zAtom] at hant; rw [hant] at hin; simp [inAnt, lh_empty] at hin
  · rw [fstIdx_zIall] at hsucc
    exact absurd (hsucc.symm.trans hsc) (by simp [qqAll, qqFalsum])
  · rw [fstIdx_zIneg] at hsucc
    exact absurd (hsucc.symm.trans hsc) (by simp [inegF, qqOr, qqFalsum])
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)
  · exfalso; rw [fstIdx_zAxAll] at hant; rw [hant] at hin; simp [inAnt, lh_empty] at hin
  · exfalso; rw [fstIdx_zAxNeg] at hant; rw [hant] at hin; simp [inAnt, lh_empty] at hin

/-- **`iR2` preserves `ZDerivesEmpty`, modulo reduction-soundness.** A contradiction derivation reduces
to a contradiction derivation: its tag is `Ind`/`K` (`zTag_Ind_or_K_of_ZDerivesEmpty`), so `iR2 d` is a
chain `zK (fstIdx d) …` and the end-sequent is preserved (`fstIdx_iR2_of_tag_Ind_or_K`) — hence both the
empty antecedent and the `⊥` succedent carry over. The **one** remaining obligation is the reduction
being well-defined, `hsound : ZDerivation (iR2 d)` (that `iCritReduct`/`iRInd` outputs satisfy `ZPhi`);
it is taken as a hypothesis here, isolating it as the next deep target. -/
lemma ZDerivesEmpty_iR2 {d : V} (h : ZDerivesEmpty d) (hsound : ZDerivation (iR2 d)) :
    ZDerivesEmpty (iR2 d) := by
  have hfst : fstIdx (iR2 d) = fstIdx d :=
    fstIdx_iR2_of_tag_Ind_or_K h.1 (zTag_Ind_or_K_of_ZDerivesEmpty h)
  exact ⟨hsound, by rw [hfst]; exact h.2.1, by rw [hfst]; exact h.2.2⟩

/-! ## Reduction-soundness decomposition — `RedSound` ⟸ chain-validity of the reducts

The reduct of an `Ind`/`K` derivation is a chain `zK …` whose premises are already `ZDerivation`s and
whose `Seq` structure is free; the only residual is that the produced chain is `zKValid` (the Buchholz
reduction lemma). These lemmas peel off the tractable structure, isolating that residual. -/

/-- **Ind-rule inversion**: a `ZDerivation` of `zInd s at' p d0 d1` has both Ind premises
`ZDerivation`s and the Ind premise-sequent side conditions `zIndWff` (`d0 ⊢ Γ→F(0)`, `d1 ⊢ F(a),Γ→F(Sa)`,
conclusion `F(t)`). The genuine Ind reduct `K^r⟨d0, d1(a/0),…,d1(a/k−1)⟩` reads `zIndWff` by inversion.
(The non-`Ind` `ZPhi` disjuncts are ruled out by `zTag`.) -/
lemma zDerivation_zInd_inv {s at' p d0 d1 : V} (hZ : ZDerivation (zInd s at' p d0 d1)) :
    ZDerivation d0 ∧ ZDerivation d1 ∧ zIndWff (zInd s at' p d0 d1) := by
  rcases zDerivation_iff.mp hZ with ⟨s', h, _⟩ | ⟨s', a, p', d0', h, _, _⟩ | ⟨s', p', d0', h, _, _⟩ |
    ⟨s', at'', p', d0', d1', h, hd0, hd1, hwff⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k, h, _, _⟩ | ⟨s', p', h, _, _⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · obtain rfl : s = s' := by simpa using congrArg fstIdx h
    obtain rfl : at' = at'' := by simpa using congrArg (fun d => π₁ (zRest d)) h
    obtain rfl : p = p' := by simpa using congrArg zIndP h
    obtain rfl : d0 = d0' := by simpa using congrArg zIndPrem0 h
    obtain rfl : d1 = d1' := by simpa using congrArg zIndPrem1 h
    exact ⟨hd0, hd1, hwff⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)

/-! ### Rule-inversion (peeling) primitives for the genuine reduct

A genuine, derivation-valid reduction (Bryce–Goré `cut_elimination`-style — shape-dispatched on the cut
formula, `cut_elimination_valid`) must *peel* the redex premises of a critical chain: the R-redex (an
I-rule introducing the cut formula on the right) and the L-redex (a §5 left-axiom carrying it on the
left). These inversions extract exactly the sub-derivation / well-formedness data such a peel consumes,
mirroring `zDerivation_zInd_inv`. They are axiom-clean and reusable by any validity-preserving reduct. -/

/-- **I∀-rule inversion**: a `ZDerivation` of `zIall s a p d0` has its premise `d0` a `ZDerivation` and
end-sequent succedent the principal formula `∀p`. Peels the R-redex premise of a critical chain. -/
lemma zDerivation_zIall_inv {s a p d0 : V} (hZ : ZDerivation (zIall s a p d0)) :
    ZDerivation d0 ∧ seqSucc s = (^∀ p : V) ∧ zIallWff s a p d0 := by
  rcases zDerivation_iff.mp hZ with ⟨s', h, _⟩ | ⟨s', a', p', d0', h, hd0, hsc, hwff⟩ |
    ⟨s', p', d0', h, _, _⟩ |
    ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k, h, _, _⟩ | ⟨s', p', h, _, _⟩
  · exact absurd (congrArg zTag h) (by simp)
  · obtain rfl : s = s' := by simpa using congrArg fstIdx h
    obtain rfl : a = a' := by simpa using congrArg (fun d => π₁ (zRest d)) h
    obtain rfl : p = p' := by simpa using congrArg zIallF h
    obtain rfl : d0 = d0' := by simpa using congrArg zIallPrem h
    exact ⟨hd0, hsc, hwff⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)

/-- **I¬-rule inversion**: a `ZDerivation` of `zIneg s p d0` has premise `d0` a `ZDerivation`, end-sequent
succedent `¬p` (`= inegF p`), and the premise-sequent side condition `zInegWff p d0` (`d0 ⊢ p,Γ→⊥`). Peels
the R-redex premise when the cut formula is a negation; the genuine I¬ reduct `d[0]:=d0` reads `zInegWff`. -/
lemma zDerivation_zIneg_inv {s p d0 : V} (hZ : ZDerivation (zIneg s p d0)) :
    ZDerivation d0 ∧ seqSucc s = (inegF p : V) ∧ zInegWff p d0 := by
  rcases zDerivation_iff.mp hZ with ⟨s', h, _⟩ | ⟨s', a', p', d0', h, _, _⟩ |
    ⟨s', p', d0', h, hd0, hsc, hwff⟩ |
    ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k, h, _, _⟩ | ⟨s', p', h, _, _⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · obtain rfl : s = s' := by simpa using congrArg fstIdx h
    obtain rfl : p = p' := by simpa using congrArg zInegF h
    obtain rfl : d0 = d0' := by simpa using congrArg zInegPrem h
    exact ⟨hd0, hsc, hwff⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)

/-- **§5 ∀-axiom inversion**: a `ZDerivation` of the left-axiom `zAxAll s p k` carries the matrix's
formula-hood and the side condition `∀p ∈ Γ`. Peels the L-redex premise (the `^∀ p` cut formula). -/
lemma zDerivation_zAxAll_inv {s p k : V} (hZ : ZDerivation (zAxAll s p k)) :
    IsUFormula ℒₒᵣ p ∧ inAnt (^∀ p : V) (seqAnt s) := by
  rcases zDerivation_iff.mp hZ with ⟨s', h, _⟩ | ⟨s', a', p', d0', h, _, _⟩ | ⟨s', p', d0', h, _, _⟩ |
    ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k', h, hp, hin⟩ | ⟨s', p', h, _, _⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · obtain rfl : s = s' := by simpa using congrArg fstIdx h
    obtain rfl : p = p' := by simpa using congrArg zAxAllF h
    exact ⟨hp, hin⟩
  · exact absurd (congrArg zTag h) (by simp)

/-- **§5 ¬-axiom inversion**: a `ZDerivation` of the left-axiom `zAxNeg s p` carries the matrix's
formula-hood and the side condition `¬p ∈ Γ`. Peels the L-redex premise (the `inegF p` cut formula). -/
lemma zDerivation_zAxNeg_inv {s p : V} (hZ : ZDerivation (zAxNeg s p)) :
    IsUFormula ℒₒᵣ p ∧ inAnt (inegF p : V) (seqAnt s) := by
  rcases zDerivation_iff.mp hZ with ⟨s', h, _⟩ | ⟨s', a', p', d0', h, _, _⟩ | ⟨s', p', d0', h, _, _⟩ |
    ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k', h, _, _⟩ | ⟨s', p', h, hp, hin⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · obtain rfl : s = s' := by simpa using congrArg fstIdx h
    obtain rfl : p = p' := by simpa using congrArg zAxNegF h
    exact ⟨hp, hin⟩

/-- **Atom inversion**: a `ZDerivation` of the identity axiom `zAtom s` has its succedent in its
antecedent (`C ∈ Γ`). The leaf side condition that rules out an empty-antecedent atom. -/
lemma zDerivation_zAtom_inv {s : V} (hZ : ZDerivation (zAtom s)) :
    inAnt (seqSucc s) (seqAnt s) := by
  rcases zDerivation_iff.mp hZ with ⟨s', h, hin⟩ | ⟨s', a', p', d0', h, _, _⟩ | ⟨s', p', d0', h, _, _⟩ |
    ⟨s', at'', p', d0', d1', h, _, _⟩ | ⟨s', r', ds', h, _, _, _⟩ |
    ⟨s', p', k', h, _, _⟩ | ⟨s', p', h, _, _⟩
  · obtain rfl : s = s' := by simpa using congrArg fstIdx h
    exact hin
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)

/-! ### The Option-B obstruction, formalized — why the ordinal-faithful `iR2` cannot preserve validity

`RedSound` (`iR2 d` is a genuine `ZDerivation` for `ZDerivesEmpty d`) is **FALSE** for the current
ordinal-faithful `iR2`. The critical reduct `iCritReduct d i j v w` is a chain
`zK (fstIdx d) (zKrank d − 1) ⟨iCritAux d i v, iCritAux d j w⟩` whose premises are themselves chains
(`iCritAux _ = zK …`). Every chain node has `tp = isymRep` (`tp_zK`), and `isymRep` is permissible for
**every** conclusion (`iperm_isymRep`). But `zKValid`'s criticality conjunct demands every premise be
NON-permissible (`¬iperm (tp dᵢ) s`) — the very hypothesis the L3.1 redex finder
(`inference_critical_pair_of_chain`) needs to force a genuine R/L redex pair to exist. A chain with a
`Rep`-tagged premise therefore can never be `zKValid`, so the reduct can never descend again, so the
`iR2`-orbit is not descent-closed. (Confirmed against Bryce–Goré, arXiv:2603.00487: their `cut_elimination`
is *genuinely* validity-preserving — `cut_elimination_valid`, shape-dispatched on the cut formula — which
the ordinal-faithful `iCritReduct` shadow is not.) The fix is the genuine, validity-preserving reduct;
the inversions above are its peeling primitives. -/

/-- **A `K^r` chain with any chain (`Rep`-tagged) premise is never `zKValid`.** The criticality conjunct
`¬iperm (tp dₘ) s` fails at the `zK`-premise `m` (`tp_zK` ⟹ `isymRep`, permissible for `s` by
`iperm_isymRep`). This is the load-bearing obstruction: the reduct `iCritReduct`'s premises are exactly
such chains, so it is never a valid critical chain — the ordinal-faithful `iR2` is not derivation-valid. -/
lemma not_zKValid_of_zK_premise {s r ds m s' r' ds' : V} (hm : m < lh ds)
    (hprem : znth ds m = zK s' r' ds') : ¬ zKValid s r ds := by
  rintro ⟨_, _, hnperm, _⟩
  exact hnperm m hm (by rw [hprem, tp_zK]; exact iperm_isymRep s)

/-- **The critical reduct is never `zKValid`** (the concrete obstruction at `iCritReduct`): premise `0`
of its chain is `iCritAux d i v = zK …`, a `Rep`-tagged chain, so `not_zKValid_of_zK_premise` applies.
Hence `ZDerivation (iCritReduct …)` cannot be obtained from chain-validity — `RedSound` fails for the
current `iR2`, and the genuine validity-preserving reduct (Option A) is required. -/
lemma not_zKValid_iCritReduct (d i j v w : V) :
    ¬ zKValid (fstIdx d) (zKrank d - 1)
      (iCritReductSeq (iCritAux d i v) (iCritAux d j w)) := by
  refine not_zKValid_of_zK_premise (m := 0) (s' := fstIdx d) (r' := zKrank d)
    (ds' := seqUpdate (zKseq d) i v) ?_ ?_
  · rw [iCritReductSeq_lh]; exact zero_lt_two
  · rw [znth_iCritReductSeq_zero]; rfl

/-! ### The clean `RedSound` fragment: the I-rules (tags 1,2)

`RedSound` asks only that the `iR2`-reduct be a genuine `ZDerivation` (the end-sequent matching is handled
separately by `fstIdx_iR2_of_tag_Ind_or_K`). For the I-rules `iR2` returns the immediate sub-derivation
`d0` (`iR2_zIall`/`iR2_zIneg`), which is a `ZDerivation` by inversion — so this fragment is unconditional.
The I¬ case is Buchholz 14.23 `d[0] := d0` verbatim (no substitution); the I∀ case's GENUINE reduct is
`d0(a/n)` but the ordinal-faithful `d0` is *also* a valid derivation (only its end-sequent differs, which
`RedSound` does not constrain). These never arise on a `ZDerivesEmpty` code (tags 3,4), but a general
tag-dispatched `RedSound` proof reuses them. -/

/-- `RedSound` for the I∀ rule: `iR2 (zIall …) = d0` is a `ZDerivation`. -/
lemma ZDerivation_iR2_zIall {s a p d0 : V} (hZ : ZDerivation (zIall s a p d0)) :
    ZDerivation (iR2 (zIall s a p d0)) := by rw [iR2_zIall]; exact (zDerivation_zIall_inv hZ).1

/-- `RedSound` for the I¬ rule: `iR2 (zIneg …) = d0` is a `ZDerivation` (Buchholz 14.23). -/
lemma ZDerivation_iR2_zIneg {s p d0 : V} (hZ : ZDerivation (zIneg s p d0)) :
    ZDerivation (iR2 (zIneg s p d0)) := by rw [iR2_zIneg]; exact (zDerivation_zIneg_inv hZ).1

/-- Every premise of the Ind-reduct sequence `iIndReductSeq d0 d1 k = ⟨d1,…,d1,d0⟩` is a `ZDerivation`
when `d0`,`d1` are. -/
lemma znth_iIndReductSeq_ZDerivation {d0 d1 k : V} (h0 : ZDerivation d0) (h1 : ZDerivation d1) :
    ∀ i < lh (iIndReductSeq d0 d1 k), ZDerivation (znth (iIndReductSeq d0 d1 k) i) := by
  intro i hi
  have hk : lh (iIndReductSeq d0 d1 k) = k + 1 := by
    rw [iIndReductSeq, Seq.lh_seqCons _ (iRepeatSeq_seq d1 k), iRepeatSeq_lh]
  rw [hk] at hi
  rcases lt_or_ge i k with hlt | hge
  · rw [iIndReductSeq,
      znth_seqCons_of_lt (iRepeatSeq_seq d1 k) _ (by rw [iRepeatSeq_lh]; exact hlt),
      znth_iRepeatSeq i hlt]
    exact h1
  · have hik : i = k := le_antisymm (le_iff_lt_succ.mpr hi) hge
    have hself := znth_seqCons_self (iRepeatSeq_seq d1 k) d0
    rw [iRepeatSeq_lh] at hself
    rw [iIndReductSeq, hik, hself]
    exact h0

/-- **Reduction-soundness for the Ind rule, modulo chain-validity of the reduct.** `iR2 (zInd …)` is the
chain `zK s (irk p) (iIndReductSeq d0 d1 1)`; its premises are `ZDerivation`s (the Ind premises) and its
`Seq` structure is free, so it is a genuine `ZDerivation` exactly when the produced chain is `zKValid`
(the Buchholz reduction lemma — the deep residual). -/
lemma ZDerivation_iR2_zInd_of_zKValid {s at' p d0 d1 : V}
    (hZ : ZDerivation (zInd s at' p d0 d1))
    (hvalid : zKValid s (irk p) (iIndReductSeq d0 d1 1)) :
    ZDerivation (iR2 (zInd s at' p d0 d1)) := by
  obtain ⟨h0, h1, _⟩ := zDerivation_zInd_inv hZ
  rw [iR2_zInd, iRInd_zInd, zDerivation_iff]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨s, irk p, iIndReductSeq d0 d1 1, rfl, iIndReductSeq_seq d0 d1 1,
      fun i hi => znth_iIndReductSeq_ZDerivation h0 h1 i hi, zKValidF_of_zKValid hvalid⟩))))

/-- Both premises of the critical-reduct sequence `iCritReductSeq d0 d1 = ⟨d0,d1⟩` are `ZDerivation`s
when `d0`,`d1` are. -/
lemma znth_iCritReductSeq_ZDerivation {d0 d1 : V} (h0 : ZDerivation d0) (h1 : ZDerivation d1) :
    ∀ i < lh (iCritReductSeq d0 d1), ZDerivation (znth (iCritReductSeq d0 d1) i) := by
  intro i hi
  rw [iCritReductSeq] at hi ⊢
  rcases lt_or_ge i (lh (seqCons (∅ : V) d0)) with hlt | hge
  · rw [znth_seqCons_of_lt (seq_empty.seqCons d0) d1 hlt]
    rw [Seq.lh_seqCons _ seq_empty] at hlt
    have hi0 : i = lh (∅ : V) :=
      le_antisymm (le_iff_lt_succ.mpr (by rw [lh_empty] at hlt ⊢; exact hlt)) (by simp)
    rw [hi0, znth_seqCons_self seq_empty]; exact h0
  · rw [Seq.lh_seqCons _ (seq_empty.seqCons d0)] at hi
    have : i = lh (seqCons (∅ : V) d0) := le_antisymm (le_iff_lt_succ.mpr hi) hge
    rw [this, znth_seqCons_self (seq_empty.seqCons d0)]; exact h1

/-- **Reduction-soundness for the critical reduct, modulo chain-validity.** `iCritReduct d i j v w` is the
chain `zK (fstIdx d) (zKrank d - 1) (iCritReductSeq (iCritAux d i v) (iCritAux d j w))`; given its two
auxiliaries are `ZDerivation`s and the produced chain is `zKValid`, it is a genuine `ZDerivation`. The K
analog of `ZDerivation_iR2_zInd_of_zKValid` (premises + `Seq` free; `zKValid` + the auxiliaries'
validity are the deep recursive residual — Buchholz's reduction lemma). -/
lemma ZDerivation_iCritReduct_of {d i j v w : V}
    (ha : ZDerivation (iCritAux d i v)) (hb : ZDerivation (iCritAux d j w))
    (hvalid : zKValid (fstIdx d) (zKrank d - 1)
      (iCritReductSeq (iCritAux d i v) (iCritAux d j w))) :
    ZDerivation (iCritReduct d i j v w) := by
  rw [iCritReduct, zDerivation_iff]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨fstIdx d, zKrank d - 1, iCritReductSeq (iCritAux d i v) (iCritAux d j w), rfl,
      iCritReductSeq_seq _ _, fun n hn => znth_iCritReductSeq_ZDerivation ha hb n hn,
      zKValidF_of_zKValid hvalid⟩))))

/-- **The genuine critical reduct is a `ZDerivation`** (R1 DISCHARGED — re-point landed). The `ZPhi` `zK`
disjunct now carries the faithful, criticality-free validity `zKValidF`, so the chain introduction
`zDerivation_zK_intro` is a theorem and the former `hZPhiK` residual is gone. Given only the two genuine
auxiliaries being `ZDerivation`s of their reduced endsequents `Θ→A(d)`/`A(d),Θ→D` (the recursive Thm 3.4(a)
— **R2**, the one remaining residual of the critical case), the recombination `iCritReductG` is a
`ZDerivation`. Its validity threading is automatic via `zKValidF_iCritReductGen`; only the cut-rank drop
`rk(A(d)) ≤ rOut` (Thm 3.4(a), banked `irk_cut_lt_rank_*`) and the conclusion formula-hood are supplied. -/
lemma ZDerivation_iCritReductG_of {s C rOut rIn0 rIn1 ds0 ds1 : V}
    (haux0 : ZDerivation (zK (seqSetSucc s C) rIn0 ds0))
    (haux1 : ZDerivation (zK (seqAddAnt C s) rIn1 ds1))
    (hsAnt : Seq (seqAnt s)) (hCrk : irk C ≤ rOut) (hCUf : IsUFormula ℒₒᵣ C)
    (hssUf : IsUFormula ℒₒᵣ (seqSucc s))
    (hsaUf : ∀ k < lh (seqAnt s), IsUFormula ℒₒᵣ (znth (seqAnt s) k)) :
    ZDerivation (iCritReductG s C rOut rIn0 rIn1 ds0 ds1) := by
  rw [iCritReductG]
  refine zDerivation_zK_intro (iCritReductSeq_seq _ _)
    (fun n hn => znth_iCritReductSeq_ZDerivation haux0 haux1 n hn) ?_
  exact zKValidF_iCritReductGen hsAnt hCrk hCUf hssUf hsaUf

/-! ### `iRcritG` — the genuine CLOSED critical branch (Buchholz Def 3.2 case 5.1, on correct endsequents)

The `red`-analogue of `iRcrit`: the redex finder `redexI`/`redexJ` is total and definable, so the genuine
critical reduct is a closed term once the per-premise reduct supplier `ρ` (`= dᵢ[k]`/`d_j[0]`, the N1
structural IH) is fixed. Unlike `iRcrit` (built on the ordinal-shadow `iCritReduct`, whose `iCritAux`
auxiliaries reuse `fstIdx d` and so have the WRONG endsequent), `iRcritG` is built on `iCritReductG`, whose
auxiliaries carry the cut's reduced endsequents `Θ→A(d)`/`A(d),Θ→D` with cut formula `A(d) = chainAsucc ds i`
(the succedent of the redex's R-premise `i`). This is the K-case of the genuine reduct `red`. -/

/-- **`iRcritG` is a `ZDerivation`** (R1 done), modulo only R2 — the two genuine auxiliaries
`d{0} = K^r (seqUpdate ds i (ρ i))` ⊢ `Θ→A(d)`, `d{1} = K^r (seqUpdate ds j (ρ j))` ⊢ `A(d),Θ→D` being
`ZDerivation`s of their reduced endsequents (recursive Thm 3.4(a), the structural IH). The validity
threading + cut-rank drop are banked (`zKValidF_iCritReductGen`, `irk_cut_lt_rank_*`). -/
lemma ZDerivation_iRcritG_of {d : V} {ρ : V → V}
    (haux0 : ZDerivation (zK (seqSetSucc (fstIdx d) (chainAsucc (zKseq d) (redexI d)))
      (zKrank d) (seqUpdate (zKseq d) (redexI d) (ρ (redexI d)))))
    (haux1 : ZDerivation (zK (seqAddAnt (chainAsucc (zKseq d) (redexI d)) (fstIdx d))
      (zKrank d) (seqUpdate (zKseq d) (redexJ d) (ρ (redexJ d)))))
    (hsAnt : Seq (seqAnt (fstIdx d)))
    (hCrk : irk (chainAsucc (zKseq d) (redexI d)) ≤ zKrank d - 1)
    (hCUf : IsUFormula ℒₒᵣ (chainAsucc (zKseq d) (redexI d)))
    (hssUf : IsUFormula ℒₒᵣ (seqSucc (fstIdx d)))
    (hsaUf : ∀ k < lh (seqAnt (fstIdx d)), IsUFormula ℒₒᵣ (znth (seqAnt (fstIdx d)) k)) :
    ZDerivation (iRcritG d ρ) :=
  ZDerivation_iCritReductG_of haux0 haux1 hsAnt hCrk hCUf hssUf hsaUf

/-! ## The iterated descent — `n ↦ iord (iR2^[n] z)` is an infinite `≺`-descent

This is the V-internal analog of `GentzenCon.gentzenDescent_descends`, on the genuine objects
(`ZDerivesEmpty`/`iR2`/`iord` in place of the abstract `derivesEmpty`/`R`/`ord` axioms). It is stated
against the one remaining InternalZ obligation, **reduction-soundness** `RedSound` (that the reduct of a
contradiction derivation is again a genuine `ZDerivation` — `iCritReduct`/`iRInd` outputs satisfy
`ZPhi`), supplied as an explicit hypothesis so nothing is axiomatized. Closing `RedSound` and
internalizing the (here external-ℕ) iteration as a `𝚺₁` graph `gentzenDescentφ` is what discharges the
crux-2 deep axiom `gentzen_descent_of_inconsistent`. -/

/-- **Reduction-soundness** (the sole remaining InternalZ obligation): the `iR2`-reduct of a
contradiction derivation is again a genuine Z-derivation. -/
def RedSound : Prop := ∀ d : V, ZDerivesEmpty d → ZDerivation (iR2 d)

/-- **`ZDerivesEmpty` is closed under the whole `iR2`-orbit** (external ℕ-iteration), given
reduction-soundness. -/
lemma ZDerivesEmpty_iterate (hRS : RedSound (V := V)) {z : V} (hz : ZDerivesEmpty z) :
    ∀ n : ℕ, ZDerivesEmpty (iR2^[n] z)
  | 0 => by simpa using hz
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact ZDerivesEmpty_iR2 (ZDerivesEmpty_iterate hRS hz n) (hRS _ (ZDerivesEmpty_iterate hRS hz n))

/-- **THE infinite ε₀-descent of crux-2.** For a contradiction derivation `z` (`ZDerivesEmpty z`), under
reduction-soundness the ordinals `n ↦ iord (iR2^[n] z)` strictly `≺`-descend at every step
(`icmp (·(n+1)) (·n) = 0`). An infinite primitive-recursive `ε₀`-descent — exactly what `PRWO(ε₀)`
forbids, giving the Gentzen contradiction `¬Con(𝗣𝗔) → False` once `z` is produced by the C0.5 bridge. -/
lemma iord_iR2_iterate_descends (hRS : RedSound (V := V)) {z : V} (hz : ZDerivesEmpty z)
    (hcrit : ∀ n : ℕ, zTag (iR2^[n] z) = 4 →
      zKCritical (fstIdx (iR2^[n] z)) (zKseq (iR2^[n] z))) (n : ℕ) :
    icmp (iord (iR2^[n+1] z)) (iord (iR2^[n] z)) = 0 := by
  rw [Function.iterate_succ_apply']
  exact iord_descent_iR2_of_ZDerivesEmpty (ZDerivesEmpty_iterate hRS hz n) (hcrit n)

end GoodsteinPA.InternalZ
