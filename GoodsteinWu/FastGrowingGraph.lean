/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinWu.InternalFund

/-!
# A Σ₁ graph for the fast-growing hierarchy on ordinal-notation codes

`fgGraph c n y` says "`f_c(n) = y`", where `f` is `ONote.fastGrowing` read through the internal
coding.  It is Σ₁: a single unbounded existential over a **witness set** `w`, all of whose
members are justified by other members of `w` (`fgWit`).

The witness is an HFS *set*, not a sequence, and a justifier may be any member — there is no
index ordering.  That is what makes witnesses mergeable: `fgWit w → fgWit w' → fgWit (w ∪ w')`
is immediate from monotonicity of `fgJust`, so the progressiveness proof never has to
concatenate or reindex anything.  Well-foundedness is not needed inside PA at all; it is only
used *externally*, at ℕ, to read a witness back (each justifier's ordinal is `≺`-smaller, by
`icmp_ifdVal_lt`).

An entry is `⟪⟪d, m⟫, ⟪v, u⟫⟫`: "`f_d(m) = v`, witnessed by the iteration sequence `u`"
(`u` is only used in the successor clause, and is `0` otherwise).
-/

open scoped FFL.FirstOrder.Bounding

set_option autoImplicit false

namespace GoodsteinWu.FastGrowingGraph

open Classical
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding.HierarchySymbol
  OrdinalAnalysis.Compat OrdinalAnalysis.Compat.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote GoodsteinWu.InternalFund

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `w` contains an entry saying `f_p(a) = b`. -/
def fgStepIn (w p a b : V) : Prop := ∃ uu < w, ⟪⟪p, a⟫, ⟪b, uu⟫⟫ ∈ w

def _root_.FFL.FirstOrder.Arithmetic.fgStepInDef : 𝚺₁.Semisentence 4 := .mkSigma
  “w p a b. ∃ uu < w, ∃ q, !pairDef q p a ∧ ∃ r, !pairDef r b uu ∧ ∃ e, !pairDef e q r ∧ e ∈ w”

instance fgStepIn_defined : 𝚺₁-Relation₄ (fgStepIn : V → V → V → V → Prop) via fgStepInDef :=
  .mk fun v ↦ by
    simp only [fgStepInDef, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp [fgStepIn, pair_defined.iff]

instance fgStepIn_definable : 𝚺₁-Relation₄ (fgStepIn : V → V → V → V → Prop) :=
  fgStepIn_defined.to_definable

/-- The entry `ent` is justified by the members of `w`. -/
def fgJust (w ent : V) : Prop :=
  (π₁ (π₁ ent) = 0 ∧ π₁ (π₂ ent) = π₂ (π₁ ent) + 1)
  ∨ (π₁ (ifd (π₁ (π₁ ent)) 0) = 1 ∧
      Seq (π₂ (π₂ ent)) ∧ lh (π₂ (π₂ ent)) = π₂ (π₁ ent) + 1 ∧
      znth (π₂ (π₂ ent)) 0 = π₂ (π₁ ent) ∧
      znth (π₂ (π₂ ent)) (π₂ (π₁ ent)) = π₁ (π₂ ent) ∧
      ∀ j < π₂ (π₁ ent),
        fgStepIn w (π₂ (ifd (π₁ (π₁ ent)) 0)) (znth (π₂ (π₂ ent)) j)
          (znth (π₂ (π₂ ent)) (j + 1)))
  ∨ (π₁ (ifd (π₁ (π₁ ent)) (π₂ (π₁ ent))) = 2 ∧
      fgStepIn w (π₂ (ifd (π₁ (π₁ ent)) (π₂ (π₁ ent)))) (π₂ (π₁ ent)) (π₁ (π₂ ent)))

def _root_.FFL.FirstOrder.Arithmetic.fgJustDef : 𝚺₁.Semisentence 2 := .mkSigma
  “w ent. ∃ dm, !pi₁Def dm ent ∧ ∃ vu, !pi₂Def vu ent ∧
      ∃ d, !pi₁Def d dm ∧ ∃ m, !pi₂Def m dm ∧ ∃ val, !pi₁Def val vu ∧ ∃ u, !pi₂Def u vu ∧
      ( (d = 0 ∧ val = m + 1)
      ∨ (∃ z, !ifdDef z d 0 ∧ ∃ zk, !pi₁Def zk z ∧ ∃ zv, !pi₂Def zv z ∧ zk = 1 ∧
           !seqDef u ∧ ∃ l, !lhDef l u ∧ l = m + 1 ∧
           ∃ u0, !znthDef u0 u 0 ∧ u0 = m ∧ ∃ um, !znthDef um u m ∧ um = val ∧
           ∀ j < m, ∃ a, !znthDef a u j ∧ ∃ b, !znthDef b u (j + 1) ∧ !fgStepInDef w zv a b)
      ∨ (∃ z, !ifdDef z d m ∧ ∃ zk, !pi₁Def zk z ∧ ∃ zv, !pi₂Def zv z ∧ zk = 2 ∧
           !fgStepInDef w zv m val) )”

instance fgJust_defined : 𝚺₁-Relation (fgJust : V → V → Prop) via fgJustDef := .mk fun v ↦ by
  simp only [fgJustDef, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
  simp [fgJust, pi₁_defined.iff, pi₂_defined.iff, ifd_defined.iff, seq_defined.iff,
    lh_defined.iff, znth_defined.iff, fgStepIn_defined.iff]

instance fgJust_definable : 𝚺₁-Relation (fgJust : V → V → Prop) := fgJust_defined.to_definable

/-- `w` is a witness set: every member is justified inside `w`. -/
def fgWit (w : V) : Prop := ∀ ent ∈ w, fgJust w ent

def _root_.FFL.FirstOrder.Arithmetic.fgWitDef : 𝚺₁.Semisentence 1 := .mkSigma
  “w. ∀ ent < w, ent ∈ w → !fgJustDef w ent”

instance fgWit_defined : 𝚺₁-Predicate (fgWit : V → Prop) via fgWitDef := .mk fun v ↦ by
  simp only [fgWitDef, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
  simp only [fgWit]
  simp only [Semiformula.eval_ballLT]
  simp
  constructor
  · intro h ent hent; exact h ent (lt_of_mem hent) hent
  · intro h ent _ hent; exact h ent hent

instance fgWit_definable : 𝚺₁-Predicate (fgWit : V → Prop) := fgWit_defined.to_definable

/-- **The Σ₁ graph of the fast-growing hierarchy**: `f_c(n) = y`. -/
def fgGraph (c n y : V) : Prop := ∃ w, fgWit w ∧ fgStepIn w c n y

def _root_.FFL.FirstOrder.Arithmetic.fgGraphDef : 𝚺₁.Semisentence 3 := .mkSigma
  “c n y. ∃ w, !fgWitDef w ∧ !fgStepInDef w c n y”

instance fgGraph_defined : 𝚺₁-Relation₃ (fgGraph : V → V → V → Prop) via fgGraphDef :=
  .mk fun v ↦ by
    simp only [fgGraphDef, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp [fgGraph, fgWit_defined.iff, fgStepIn_defined.iff]

instance fgGraph_definable : 𝚺₁-Relation₃ (fgGraph : V → V → V → Prop) :=
  fgGraph_defined.to_definable

/-! ### Monotonicity and merging -/

lemma fgStepIn_mono {w w' p a b : V} (hsub : w ⊆ w')
    (h : fgStepIn w p a b) : fgStepIn w' p a b := by
  obtain ⟨uu, huu, hmem⟩ := h
  exact ⟨uu, lt_of_lt_of_le huu (le_of_subset hsub), hsub hmem⟩

lemma fgJust_mono {w w' ent : V} (hsub : w ⊆ w')
    (h : fgJust w ent) : fgJust w' ent := by
  rcases h with h | h | h
  · exact Or.inl h
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact Or.inr (Or.inl ⟨h1, h2, h3, h4, h5,
      fun j hj => fgStepIn_mono hsub (h6 j hj)⟩)
  · exact Or.inr (Or.inr ⟨h.1, fgStepIn_mono hsub h.2⟩)

lemma fgWit_union {w w' : V} (h : fgWit w) (h' : fgWit w') : fgWit (w ∪ w') := by
  intro ent hent
  rcases mem_cup_iff.mp hent with hm | hm
  · exact fgJust_mono (union_succ_union_left w w') (h ent hm)
  · exact fgJust_mono (union_succ_union_right w w') (h' ent hm)

end GoodsteinWu.FastGrowingGraph
