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
  (∃ s, d = zAtom s) ∨
  (∃ s a p d0, d = zIall s a p d0 ∧ d0 ∈ C) ∨
  (∃ s p d0, d = zIneg s p d0 ∧ d0 ∈ C) ∨
  (∃ s at' p d0 d1, d = zInd s at' p d0 d1 ∧ d0 ∈ C ∧ d1 ∈ C) ∨
  (∃ s r ds, d = zK s r ds ∧ Seq ds ∧ ∀ i < lh ds, znth ds i ∈ C) ∨
  (∃ s p k, d = zAxAll s p k ∧ IsUFormula ℒₒᵣ p) ∨
  (∃ s p, d = zAxNeg s p ∧ IsUFormula ℒₒᵣ p)

/-- `ZPhi` is monotone in the premise set `C` (a `Fixpoint.Construction.monotone` field). -/
lemma zphi_monotone {C C' : Set V} (h : C ⊆ C') {d : V} : ZPhi C d → ZPhi C' d := by
  rintro (hd | ⟨s, a, p, d0, rfl, hd⟩ | ⟨s, p, d0, rfl, hd⟩ |
    ⟨s, at', p, d0, d1, rfl, h0, h1⟩ | ⟨s, r, ds, rfl, hseq, hall⟩ |
    ⟨s, p, k, rfl, hp⟩ | ⟨s, p, rfl, hp⟩)
  · exact Or.inl hd
  · exact Or.inr (Or.inl ⟨s, a, p, d0, rfl, h hd⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨s, p, d0, rfl, h hd⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, at', p, d0, d1, rfl, h h0, h h1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, r, ds, rfl, hseq, fun i hi => h (hall i hi)⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, p, k, rfl, hp⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, p, rfl, hp⟩)))))

/-- `ZPhi` is strongly finite: every premise of `d` is `< d`, so the rule fires already over
`{y ∈ C | y < d}` (a `Fixpoint.Construction.StrongFinite` field). The K^r case uses
`Seq.znth` + `lt_of_mem_rng` (`znth ds i < ds`) then `ds < zK s r ds`. -/
lemma zphi_strong_finite {C : Set V} {d : V} :
    ZPhi C d → ZPhi {y | y ∈ C ∧ y < d} d := by
  rintro (hd | ⟨s, a, p, d0, rfl, hd⟩ | ⟨s, p, d0, rfl, hd⟩ |
    ⟨s, at', p, d0, d1, rfl, h0, h1⟩ | ⟨s, r, ds, rfl, hseq, hall⟩ |
    ⟨s, p, k, rfl, hp⟩ | ⟨s, p, rfl, hp⟩)
  · exact Or.inl hd
  · exact Or.inr (Or.inl ⟨s, a, p, d0, rfl, hd, by simp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨s, p, d0, rfl, hd, by simp⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, at', p, d0, d1, rfl, ⟨h0, by simp⟩, ⟨h1, by simp⟩⟩)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, r, ds, rfl, hseq, fun i hi => ⟨hall i hi, ?_⟩⟩))))
    exact lt_trans (lt_of_mem_rng (hseq.znth hi)) (ds_lt_zK s r ds)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, p, k, rfl, hp⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, p, rfl, hp⟩)))))

/-- Bounded-quantifier form of `ZPhi` (every existential is `< d`), the shape the arithmetized
`blueprint` core matches. Mirrors Foundation `Theory.Derivation.phi_iff`. -/
private lemma zphi_iff (C d : V) :
    ZPhi {x | x ∈ C} d ↔
    ( (∃ s < d, d = zAtom s) ∨
      (∃ s < d, ∃ a < d, ∃ p < d, ∃ d0 < d, d = zIall s a p d0 ∧ d0 ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d0 < d, d = zIneg s p d0 ∧ d0 ∈ C) ∨
      (∃ s < d, ∃ at' < d, ∃ p < d, ∃ d0 < d, ∃ d1 < d,
        d = zInd s at' p d0 d1 ∧ d0 ∈ C ∧ d1 ∈ C) ∨
      (∃ s < d, ∃ r < d, ∃ ds < d, d = zK s r ds ∧ Seq ds ∧ ∀ i < lh ds, znth ds i ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ k < d, d = zAxAll s p k ∧ IsUFormula ℒₒᵣ p) ∨
      (∃ s < d, ∃ p < d, d = zAxNeg s p ∧ IsUFormula ℒₒᵣ p) ) := by
  constructor
  · rintro (⟨s, rfl⟩ | ⟨s, a, p, d0, rfl, h⟩ | ⟨s, p, d0, rfl, h⟩ |
      ⟨s, at', p, d0, d1, rfl, h0, h1⟩ | ⟨s, r, ds, rfl, hseq, hall⟩ |
      ⟨s, p, k, rfl, hp⟩ | ⟨s, p, rfl, hp⟩)
    · exact Or.inl ⟨s, by simp, rfl⟩
    · exact Or.inr (Or.inl ⟨s, by simp, a, by simp, p, by simp, d0, by simp, rfl, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨s, by simp, p, by simp, d0, by simp, rfl, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨s, by simp, at', by simp, p, by simp, d0, by simp, d1, by simp, rfl, h0, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨s, by simp, r, by simp, ds, by simp, rfl, hseq, hall⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨s, by simp, p, by simp, k, by simp, rfl, hp⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨s, by simp, p, by simp, rfl, hp⟩)))))
  · rintro (⟨s, _, rfl⟩ | ⟨s, _, a, _, p, _, d0, _, rfl, h⟩ | ⟨s, _, p, _, d0, _, rfl, h⟩ |
      ⟨s, _, at', _, p, _, d0, _, d1, _, rfl, h0, h1⟩ | ⟨s, _, r, _, ds, _, rfl, hseq, hall⟩ |
      ⟨s, _, p, _, k, _, rfl, hp⟩ | ⟨s, _, p, _, rfl, hp⟩)
    · exact Or.inl ⟨s, rfl⟩
    · exact Or.inr (Or.inl ⟨s, a, p, d0, rfl, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨s, p, d0, rfl, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, at', p, d0, d1, rfl, h0, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, r, ds, rfl, hseq, hall⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, p, k, rfl, hp⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, p, rfl, hp⟩)))))

open LO.FirstOrder.Arithmetic in
/-- Arithmetized `𝚫₁` core for the Z-derivation `Fixpoint` (mirrors Foundation
`Theory.Derivation.blueprint`). `d` = candidate code, `C` = the recursion set (premises so far). The
K^r disjunct uses `seqDef`/`lhDef`/`znthDef` for the variadic premise-sequence membership. -/
noncomputable def zblueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “d C.
    ( (∃ s < d, !zAtomGraph d s) ∨
      (∃ s < d, ∃ a < d, ∃ p < d, ∃ d0 < d, !zIallGraph d s a p d0 ∧ d0 ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d0 < d, !zInegGraph d s p d0 ∧ d0 ∈ C) ∨
      (∃ s < d, ∃ at' < d, ∃ p < d, ∃ d0 < d, ∃ d1 < d,
        !zIndGraph d s at' p d0 d1 ∧ d0 ∈ C ∧ d1 ∈ C) ∨
      (∃ s < d, ∃ r < d, ∃ ds < d,
        !zKGraph d s r ds ∧ !seqDef ds ∧
          ∃ l, !lhDef l ds ∧ ∀ i < l, ∃ z, !znthDef z ds i ∧ z ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ k < d, !zAxAllGraph d s p k ∧ !(isUFormula ℒₒᵣ).sigma p) ∨
      (∃ s < d, ∃ p < d, !zAxNegGraph d s p ∧ !(isUFormula ℒₒᵣ).sigma p) )”)
  (.mkPi “d C.
    ( (∃ s < d, !zAtomGraph d s) ∨
      (∃ s < d, ∃ a < d, ∃ p < d, ∃ d0 < d, !zIallGraph d s a p d0 ∧ d0 ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ d0 < d, !zInegGraph d s p d0 ∧ d0 ∈ C) ∨
      (∃ s < d, ∃ at' < d, ∃ p < d, ∃ d0 < d, ∃ d1 < d,
        !zIndGraph d s at' p d0 d1 ∧ d0 ∈ C ∧ d1 ∈ C) ∨
      (∃ s < d, ∃ r < d, ∃ ds < d,
        !zKGraph d s r ds ∧ !seqDef ds ∧
          ∀ l, !lhDef l ds → ∀ i < l, ∀ z, !znthDef z ds i → z ∈ C) ∨
      (∃ s < d, ∃ p < d, ∃ k < d, !zAxAllGraph d s p k ∧ !(isUFormula ℒₒᵣ).pi p) ∨
      (∃ s < d, ∃ p < d, !zAxNegGraph d s p ∧ !(isUFormula ℒₒᵣ).pi p) )”)⟩

lemma zPhi_definable :
    𝚫₁.Defined (fun v : Fin 2 → V ↦ ZPhi {x | x ∈ v 1} (v 0)) zblueprint.core := .mk <| by
  constructor
  · intro v; simp [zblueprint]
  · intro v; simp [zphi_iff, zblueprint, zAtom_defined.iff, zIall_defined.iff, zIneg_defined.iff,
      zInd_defined.iff, zK_defined.iff, zAxAll_defined.iff, zAxNeg_defined.iff,
      seq_defined.iff, lh_defined.iff, znth_defined.iff]

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
    rcases hphi with ⟨s, rfl⟩ | ⟨s, a, p, d0, rfl, hd0⟩ | ⟨s, p, d0, rfl, hd0⟩ |
      ⟨s, at', p, d0, d1, rfl, hd0, hd1⟩ | ⟨s, r, ds, rfl, hds, hmem⟩ |
      ⟨s, p, k, rfl, hp⟩ | ⟨s, p, rfl, hp⟩
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
    rcases hphi with ⟨s, rfl⟩ | ⟨s, a, p, d0, rfl, _⟩ | ⟨s, p, d0, rfl, _⟩ |
      ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _⟩ |
      ⟨s, p, k, rfl, _⟩ | ⟨s, p, rfl, _⟩
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
  rcases zDerivation_iff.mp hd with ⟨s, rfl⟩ | ⟨s, a, p, d0, rfl, _⟩ | ⟨s, p, d0, rfl, _⟩ |
    ⟨s, at', p, d0, d1, rfl, hd0, hd1⟩ | ⟨s, r, ds, rfl, _, _⟩ |
    ⟨s, p, k, rfl, _⟩ | ⟨s, p, rfl, _⟩
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
  rcases zDerivation_iff.mp hZ with ⟨s', h⟩ | ⟨s', a, p, d0, h, _⟩ | ⟨s', p, d0, h, _⟩ |
    ⟨s', at', p, d0, d1, h, _, _⟩ | ⟨s', r', ds', h, hds', hmem'⟩ |
    ⟨s', p, k, h, _⟩ | ⟨s', p, h, _⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)
  · obtain rfl : ds = ds' := by simpa using congrArg zKseq h
    exact ⟨hds', fun i hi => hmem' i hi⟩
  · exact absurd (congrArg zTag h) (by simp)
  · exact absurd (congrArg zTag h) (by simp)

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
  rcases zDerivation_iff.mp hZ with ⟨s, rfl⟩ | ⟨s, a, p, d0, rfl, hd0⟩ | ⟨s, p, d0, rfl, hd0⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _⟩ |
    ⟨s, p, k, rfl, _⟩ | ⟨s, p, rfl, _⟩
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

/-! ## The Thm-4.2 descent through the recursive `iR2` — structural + Ind assembly (tags 1,2,3)

With `iR2` total, the descent `o(iR2 d) ≺ o(d)` assembles from `zDerivation_iff` (one-step, NO
induction needed for the I-rules/Ind because their reducts are CLOSED codes). The atom/axiom tags
(0/5/6) are normal forms with no strict descent (and never arise on a ⊥-derivation); the K-rule (tag 4)
needs the nut's hyps (`iord_descent_iRcrit_of_chain`), deferred to the §5 layer. This lemma banks the
genuinely-now-available part: every I-rule (tag 1,2) and `Ind` (tag 3) Z-derivation descends through the
*recursive* `iR2`. -/
lemma iord_descent_iR2_struct (d : V) (hd : ZDerivation d)
    (htag : zTag d = 1 ∨ zTag d = 2 ∨ zTag d = 3) :
    icmp (iord (iR2 d)) (iord d) = 0 := by
  rcases zDerivation_iff.mp hd with ⟨s, rfl⟩ | ⟨s, a, p, d0, rfl, _⟩ | ⟨s, p, d0, rfl, _⟩ |
    ⟨s, at', p, d0, d1, rfl, h0, h1⟩ | ⟨s, r, ds, rfl, _, _⟩ |
    ⟨s, p, k, rfl, _⟩ | ⟨s, p, rfl, _⟩
  · simp [zTag_zAtom] at htag
  · rw [iR2_zIall]; exact iord_descent_zIall s a p d0
  · rw [iR2_zIneg]; exact iord_descent_zIneg s p d0
  · rw [iR2_zInd]
    exact iord_descent_iRInd_zInd s at' p d0 d1
      (isNF_iotil_of_ZDerivation d0 h0) (isNF_iotil_of_ZDerivation d1 h1)
  · simp [zTag_zK] at htag
  · simp [zTag_zAxAll] at htag
  · simp [zTag_zAxNeg] at htag

/-- **The redexI premise's `iR2`-reduct satisfies the IH bundle, concretely** (the recursive-`iR2`
analog of lap-71's `iRedDescent_iR_of_tp_isymR`). A premise `d` with `tp d = R_A` is an I-rule
(`tp_isymR_tag` ⟹ tag 1/2), where `iR2 d = d0` (the sub-derivation) agrees with the old `iR`; so the
banked `iRedDescent_zIall`/`_zIneg` apply verbatim. This discharges the `i`-side of the K-case nut's
six `ρ`-facts (`iord_descent_iRcrit_of_chain'`'s `hρlt_i`/`hρg_i`/`hρNF_i`) for the CONCRETE recursive
`ρ = iR2(znth ds ·)`. Only the `j`-side (the L-axiom §5 atomic reduct) remains. -/
lemma iRedDescent_iR2_of_tp_isymR {d A : V} (htp : tp d = isymR A) (hZ : ZDerivation d) :
    iRedDescent (iR2 d) d := by
  rcases zDerivation_iff.mp hZ with ⟨s, rfl⟩ | ⟨s, a, p, d0, rfl, hd0⟩ | ⟨s, p, d0, rfl, hd0⟩ |
    ⟨s, at', p, d0, d1, rfl, _, _⟩ | ⟨s, r, ds, rfl, _, _⟩ |
    ⟨s, p, k, rfl, _⟩ | ⟨s, p, rfl, _⟩
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

end GoodsteinPA.InternalZ
