/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinWu.FundBridge
import GoodsteinWu.FastGrowingGraph

/-!
# Reading `fgGraph` back at the standard model

Step 6 of the route: the *soundness* half of the frozen statement.  A witness set for
`fgGraph (code o) n y` at `ℕ` forces `y = ONote.fastGrowing o n`.

Well-foundedness is used only here, and only externally: the recursion is Lean's, on `o : ONote`
with the very order `ONote.fastGrowing` itself recurses on.  Each `fgJust` clause hands back a
justifier whose code is `code (fsVal o ·)`, and `fsVal o n < o` holds for **every** `o` (no normal
form needed) because that is exactly what mathlib's `fundamentalSequence_has_prop` provides.
-/

open scoped FFL.FirstOrder.Bounding

set_option autoImplicit false

namespace GoodsteinWu.Readoff

open Classical
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding.HierarchySymbol
  OrdinalAnalysis.Compat OrdinalAnalysis.Compat.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote OrdinalAnalysis.Gentzen.NotationBridge
open GoodsteinWu.InternalFund GoodsteinWu.FastGrowingGraph

/-! ### External facts about `ONote.fundamentalSequence` -/

lemma code_eq_zero_iff (o : ONote) : code o = 0 ↔ o = 0 := by
  cases o with
  | zero => simp [code]
  | oadd e n r => simp [code]

/-- The fundamental-sequence value of a nonzero notation is strictly smaller. -/
lemma fsVal_lt {o : ONote} (h : fsKind o ≠ 0) (n : ℕ) : fsVal o n < o := by
  have hp := ONote.fundamentalSequence_has_prop o
  rcases ho : o.fundamentalSequence with ⟨_ | a⟩ | f
  · exact absurd (fsKind_eq_of_none ho) h
  · rw [ho] at hp
    rw [fsVal_eq_of_some ho, ONote.lt_def, hp.1]
    exact Order.lt_succ _
  · rw [ho] at hp
    rw [fsVal_eq_of_inr ho]
    exact (hp.2.1 n).2.1

lemma exists_pred_of_kind_one {o : ONote} (h : fsKind o = 1) :
    o.fundamentalSequence = Sum.inl (some (fsVal o 0)) := by
  rcases ho : o.fundamentalSequence with ⟨_ | a⟩ | f
  · rw [fsKind_eq_of_none ho] at h; exact absurd h (by decide)
  · rw [fsVal_eq_of_some ho]
  · rw [fsKind_eq_of_inr ho] at h; exact absurd h (by decide)

lemma exists_seq_of_kind_two {o : ONote} (h : fsKind o = 2) (n : ℕ) :
    ∃ f : ℕ → ONote, o.fundamentalSequence = Sum.inr f ∧ f n = fsVal o n := by
  rcases ho : o.fundamentalSequence with ⟨_ | a⟩ | f
  · rw [fsKind_eq_of_none ho] at h; exact absurd h (by decide)
  · rw [fsKind_eq_of_some ho] at h; exact absurd h (by decide)
  · exact ⟨f, rfl, (fsVal_eq_of_inr ho n).symm⟩

/-! ### The internal datum at the standard model -/

/-- `ifd_modelCode` specialised to `V = ℕ`, where `modelCode o` is literally `code o`. -/
lemma ifd_code (o : ONote) (n : ℕ) :
    ifd (V := ℕ) (code o) n = ⟪fsKind o, code (fsVal o n)⟫ := by
  have h := ifd_modelCode (V := ℕ) o n
  simpa [modelCode] using h

@[simp] lemma pi₁_ifd_code (o : ONote) (n : ℕ) :
    π₁ (ifd (V := ℕ) (code o) n) = fsKind o := by rw [ifd_code]; simp

@[simp] lemma pi₂_ifd_code (o : ONote) (n : ℕ) :
    π₂ (ifd (V := ℕ) (code o) n) = code (fsVal o n) := by rw [ifd_code]; simp

/-! ### Soundness -/

/-- **The ℕ read-off.**  Any witness set that asserts `f_{code o}(n) = y` is telling the truth. -/
theorem fgStepIn_sound {w : ℕ} (hw : fgWit (V := ℕ) w) (o : ONote) :
    ∀ n y : ℕ, fgStepIn (V := ℕ) w (code o) n y → y = ONote.fastGrowing o n := by
  have wf : WellFounded ((· < ·) : ONote → ONote → Prop) :=
    InvImage.wf ONote.repr Ordinal.lt_wf
  induction o using wf.induction with
  | _ o ih =>
    intro n y h
    obtain ⟨uu, -, hmem⟩ := h
    have hj := hw _ hmem
    simp only [fgJust, pi₁_pair, pi₂_pair, pi₁_ifd_code, pi₂_ifd_code] at hj
    rcases hj with ⟨h0, hv⟩ | ⟨hk, -, hlh, hz0, hzn, hstep⟩ | ⟨hk, hstep⟩
    · -- zero: `code o = 0`, so `o = 0` and `f_0(n) = n + 1`
      have ho : o = 0 := (code_eq_zero_iff o).mp h0
      subst ho
      rw [ONote.fastGrowing_zero]
      exact hv
    · -- successor: iterate `f_{o[0]}` along the sequence `uu`
      set a := fsVal o 0 with ha
      have hao : a < o := fsVal_lt (by rw [hk]; decide) 0
      have ihA := ih a hao
      have key : ∀ j : ℕ, j ≤ n → znth uu (j : ℕ) = (ONote.fastGrowing a)^[j] n := by
        intro j
        induction j with
        | zero => intro _; simpa using hz0
        | succ j ihj =>
          intro hjn
          have hj : (j : ℕ) < n := by omega
          have hstepj := ihA (znth uu j) (znth uu (j + 1)) (hstep j hj)
          rw [Function.iterate_succ_apply', ← ihj (by omega)]
          exact hstepj
      rw [ONote.fastGrowing_succ o (exists_pred_of_kind_one hk), ← hzn]
      exact key n le_rfl
    · -- limit: one step down to `o[n]`
      obtain ⟨f, hf, hfn⟩ := exists_seq_of_kind_two hk n
      have hao : fsVal o n < o := fsVal_lt (by rw [hk]; decide) n
      have hfg : ONote.fastGrowing o n = ONote.fastGrowing (fsVal o n) n := by
        simp only [ONote.fastGrowing_limit o hf, hfn]
      rw [hfg]
      exact ih (fsVal o n) hao n y hstep

/-- **The ℕ read-off, for `fgGraph`.** -/
theorem fgGraph_sound {o : ONote} {n y : ℕ} (h : fgGraph (V := ℕ) (code o) n y) :
    y = ONote.fastGrowing o n := by
  obtain ⟨w, hw, hstep⟩ := h
  exact fgStepIn_sound hw o n y hstep

end GoodsteinWu.Readoff
