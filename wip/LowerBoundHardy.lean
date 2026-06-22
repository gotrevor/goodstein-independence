/-
# The witness-bounded cut-free lower bound, over the **concrete** Hardy hierarchy (M6)

`wip/WitnessBound.lean` proved the ∃-fragment lower bound (`lowerBound_existential`) *modulo* an
abstract Hardy monotonicity hypothesis `Hmono : β < α → τ β < k → h β k ≤ h α k`.  This file
**discharges that hypothesis concretely**: it re-states the witness-bounded calculus over `ONote`
(Towsner's ordinals `< ε₀` ARE the notation system), instantiates the Hardy data with the real
`hardy`/`norm` from `src/GoodsteinPA/Hardy.lean` (ported Track-1), and supplies `Hmono` from
`hardy_le_of_lt` — the index-monotonicity lemma whose budget side condition `norm α ≤ x` is exactly
Towsner's `τ β < k`.  The Goodstein atom-truth + `G` are the real ones (from `Defs.lean`).

**Result:** `lowerBound_existential_hardy` — the ∀-free Goodstein-fragment lower bound with **zero
abstract hypotheses**, over the genuine Hardy hierarchy and genuine Goodstein function.  Axiom-clean.

This is the M6 ∃-fragment, fully grounded.  The remaining frontier is the `gAll`/`I∀` case (the full
Thm 17.1), tracked in `wip/WitnessBound.lean : bounding` + `ON-LINE-REQUEST.md` (the disjunctive
Schwichtenberg–Wainer / Arai boundedness invariant).  WIP — not in build target.
-/
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Order.Lattice.Nat
import GoodsteinPA.Defs
import GoodsteinPA.Hardy

namespace GoodsteinPA.LowerBoundHardy

open ONote Ordinal GoodsteinPA.FastGrowing

/-! ## Goodstein fragment formulas + the real `G` (mirrors `wip/WitnessBound.lean`) -/

inductive GForm
  | atom (m n : ℕ)   -- `g_m(n) = 0`
  | gEx (n : ℕ)      -- `∃y g_y(n) = 0`
  | gAll             -- `∀x ∃y g_y(x) = 0`
  deriving DecidableEq

abbrev Seq := Finset GForm
open GForm

/-- `g_m(n)=0` true in ℕ. -/
def atomTrue (m n : ℕ) : Prop := goodsteinSeq n m = 0
instance (m n : ℕ) : Decidable (atomTrue m n) := by unfold atomTrue; infer_instance

/-- The Goodstein function: least zero step (Towsner Def 7.1). -/
noncomputable def G (n : ℕ) : ℕ := sInf {m | goodsteinSeq n m = 0}

/-- `HG`, concretely: a true atom forces `m ≥ G n`. -/
theorem G_le_of_atomTrue {m n : ℕ} (h : atomTrue m n) : G n ≤ m := Nat.sInf_le h

/-! ## The witness-bounded cut-free calculus over `ONote`

Identical rule shape to `wip/WitnessBound.lean : B`, but the height index is an `ONote` (so
`h := hardy`, `τ := norm` are *concrete*).  `NF` hypotheses are carried where `hardy_le_of_lt`
needs them; the well-founded descent uses only `ONote.lt_def` (`β < α ↔ repr β < repr α`). -/
inductive B : ONote → ℕ → Seq → Prop
  | trueR {α : ONote} {k : ℕ} {Γ : Seq} {m n : ℕ}
      (hmem : atom m n ∈ Γ) (htrue : atomTrue m n) (hτ : norm α < k) : B α k Γ
  | weak {α β : ONote} {k : ℕ} {Δ Γ : Seq}
      (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k)
      (hsub : Δ ⊆ Γ) (d : B β k Δ) : B α k Γ
  | exI {α β : ONote} {k : ℕ} {Γ : Seq} {n v : ℕ}
      (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k) (hbound : v ≤ hardy α k)
      (hmem : gEx n ∈ Γ) (d : B β k (insert (atom v n) Γ)) : B α k Γ
  | allI {α : ONote} {k : ℕ} {Γ : Seq} (β : ℕ → ONote)
      (hmem : gAll ∈ Γ) (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF)
      (hτ : ∀ n, norm (β n) < max k n)
      (d : ∀ n, B (β n) (max k n) (insert (gEx n) Γ)) : B α k Γ

/-- **Hardy index monotonicity = `Hmono`, concretely.**  For NF notations `β < α` with the budget
`norm β < k`, `hardy β k ≤ hardy α k`.  This is `hardy_le_of_lt` with `x := k` and the strict
budget weakened to `≤`. -/
theorem hardy_mono_of_lt {β α : ONote} {k : ℕ} (hβNF : β.NF) (hαNF : α.NF)
    (hβα : β < α) (hτ : norm β < k) : hardy β k ≤ hardy α k :=
  hardy_le_of_lt hβNF hαNF hβα (Nat.le_of_lt hτ)

/-- **The ∃-fragment lower bound, fully concrete (Towsner Thm 17.1, ∀-free part).**

Over the real Hardy hierarchy (`hardy`) and the real Goodstein function (`G`), the witness-bounded
cut-free calculus cannot derive a sequent of pending existentials + false atoms all of which are
"out of reach": every `gEx n` with `hardy α k < G n`, every `atom m n` with `m < G n`.  No abstract
hypotheses — `Hmono` is `hardy_le_of_lt`, `HG` is `G_le_of_atomTrue`. -/
theorem lowerBound_existential_hardy :
    ∀ (α : ONote) (k : ℕ) (Γ : Seq),
      (∀ f ∈ Γ, (∃ n, f = gEx n ∧ hardy α k < G n) ∨ (∃ m n, f = atom m n ∧ m < G n)) →
      ¬ B α k Γ := by
  suffices H : ∀ (g : Ordinal.{0}) (α : ONote), α.repr = g →
      ∀ (k : ℕ) (Γ : Seq),
        (∀ f ∈ Γ, (∃ n, f = gEx n ∧ hardy α k < G n) ∨ (∃ m n, f = atom m n ∧ m < G n)) →
        ¬ B α k Γ from
    fun α k Γ h => H α.repr α rfl k Γ h
  intro g
  induction g using WellFoundedLT.induction with
  | _ g IH =>
    intro α ho k Γ hcond hB
    cases hB with
    | trueR hmem htrue hτ =>
      rename_i m n
      rcases hcond _ hmem with ⟨n', hf, _⟩ | ⟨m', n', hf, hlt⟩
      · exact absurd hf (by simp)
      · obtain ⟨rfl, rfl⟩ : m = m' ∧ n = n' := by simpa [GForm.atom.injEq] using hf
        exact absurd (G_le_of_atomTrue htrue) (by omega)
    | weak hβ hβNF hαNF hτ hsub d =>
      rename_i β Δ
      have hrβ : β.repr < g := by rw [← ho]; exact lt_def.mp hβ
      refine IH β.repr hrβ β rfl k Δ (fun f hf => ?_) d
      rcases hcond f (hsub hf) with ⟨n, hfn, hgt⟩ | ⟨m, n, hfm, hlt⟩
      · exact Or.inl ⟨n, hfn, lt_of_le_of_lt (hardy_mono_of_lt hβNF hαNF hβ hτ) hgt⟩
      · exact Or.inr ⟨m, n, hfm, hlt⟩
    | exI hβ hβNF hαNF hτ hbound hmem d =>
      rename_i β n v
      have hrβ : β.repr < g := by rw [← ho]; exact lt_def.mp hβ
      have hgtn : hardy α k < G n := by
        rcases hcond _ hmem with ⟨n', hfn, hgt⟩ | ⟨_, _, hf, _⟩
        · obtain rfl : n = n' := by simpa [GForm.gEx.injEq] using hfn
          exact hgt
        · exact absurd hf (by simp)
      refine IH β.repr hrβ β rfl k (insert (atom v n) Γ) (fun f hf => ?_) d
      rcases Finset.mem_insert.mp hf with rfl | hfΓ
      · exact Or.inr ⟨v, n, rfl, lt_of_le_of_lt hbound hgtn⟩
      · rcases hcond f hfΓ with ⟨n', hfn, hgt⟩ | ⟨m, n', hfm, hlt⟩
        · exact Or.inl ⟨n', hfn, lt_of_le_of_lt (hardy_mono_of_lt hβNF hαNF hβ hτ) hgt⟩
        · exact Or.inr ⟨m, n', hfm, hlt⟩
    | allI β hmem _ _ _ _ =>
      rcases hcond _ hmem with ⟨_, hf, _⟩ | ⟨_, _, hf, _⟩ <;> exact absurd hf (by simp)

end GoodsteinPA.LowerBoundHardy
