/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinWu.InternalFund

/-!
# `ifd` computes mathlib's `ONote.fundamentalSequence` on standard codes

The external counterpart of `GoodsteinWu/InternalFund.lean`: for every fixed `o : ONote` and every
standard index `n : ℕ`, the internal datum `ifd (modelCode o) n` is exactly
`⟪fsKind o, modelCode (fsVal o n)⟫`, in every model of `𝗜𝚺₁`.

This is the clause-by-clause check of the transcription (in particular that mathlib's
`i.succPNat` is the internal `n + 1`), and it is what makes the ℕ-reading of the final Σ₁ graph
possible.
-/

open scoped FFL.FirstOrder.Bounding

set_option autoImplicit false

namespace GoodsteinWu.InternalFund

open Classical
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding.HierarchySymbol
  OrdinalAnalysis.Compat OrdinalAnalysis.Compat.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote OrdinalAnalysis.Gentzen.NotationBridge

/-! ### Unfolding `ONote.fundamentalSequence` at `oadd` -/

section External

variable (a : ONote) (m : ℕ+) (b : ONote)

lemma fs_oadd_tail_inr {f : ℕ → ONote} (h : b.fundamentalSequence = Sum.inr f) :
    (ONote.oadd a m b).fundamentalSequence = Sum.inr fun i => ONote.oadd a m (f i) := by
  rw [ONote.fundamentalSequence.eq_def]; simp only [h]

lemma fs_oadd_tail_some {b' : ONote} (h : b.fundamentalSequence = Sum.inl (some b')) :
    (ONote.oadd a m b).fundamentalSequence = Sum.inl (some (ONote.oadd a m b')) := by
  rw [ONote.fundamentalSequence.eq_def]; simp only [h]

lemma fs_oadd_zz (ha : a.fundamentalSequence = Sum.inl none) (hm : m.natPred = 0) :
    (ONote.oadd a m 0).fundamentalSequence = Sum.inl (some 0) := by
  rw [ONote.fundamentalSequence.eq_def]; simp only [ha, hm]; rfl

lemma fs_oadd_zs {k : ℕ} (ha : a.fundamentalSequence = Sum.inl none) (hm : m.natPred = k + 1) :
    (ONote.oadd a m 0).fundamentalSequence =
      Sum.inl (some (ONote.oadd 0 k.succPNat 0)) := by
  rw [ONote.fundamentalSequence.eq_def]; simp only [ha, hm]; rfl

lemma fs_oadd_sz {a' : ONote} (ha : a.fundamentalSequence = Sum.inl (some a'))
    (hm : m.natPred = 0) :
    (ONote.oadd a m 0).fundamentalSequence =
      Sum.inr fun i => ONote.oadd a' i.succPNat 0 := by
  rw [ONote.fundamentalSequence.eq_def]; simp only [ha, hm]; rfl

lemma fs_oadd_ss {a' : ONote} {k : ℕ} (ha : a.fundamentalSequence = Sum.inl (some a'))
    (hm : m.natPred = k + 1) :
    (ONote.oadd a m 0).fundamentalSequence =
      Sum.inr fun i => ONote.oadd a k.succPNat (ONote.oadd a' i.succPNat 0) := by
  rw [ONote.fundamentalSequence.eq_def]; simp only [ha, hm]; rfl

lemma fs_oadd_lz {f : ℕ → ONote} (ha : a.fundamentalSequence = Sum.inr f) (hm : m.natPred = 0) :
    (ONote.oadd a m 0).fundamentalSequence = Sum.inr fun i => ONote.oadd (f i) 1 0 := by
  rw [ONote.fundamentalSequence.eq_def]; simp only [ha, hm]; rfl

lemma fs_oadd_ls {f : ℕ → ONote} {k : ℕ} (ha : a.fundamentalSequence = Sum.inr f)
    (hm : m.natPred = k + 1) :
    (ONote.oadd a m 0).fundamentalSequence =
      Sum.inr fun i => ONote.oadd a k.succPNat (ONote.oadd (f i) 1 0) := by
  rw [ONote.fundamentalSequence.eq_def]; simp only [ha, hm]; rfl

end External

/-! ### The external kind/value split of `fundamentalSequence` -/

/-- `0` if `o = 0`, `1` if `o` is a successor, `2` if `o` is a limit. -/
def fsKind (o : ONote) : ℕ :=
  match o.fundamentalSequence with
  | Sum.inl none => 0
  | Sum.inl (some _) => 1
  | Sum.inr _ => 2

/-- The predecessor of a successor, the `n`-th member of the fundamental sequence of a limit. -/
def fsVal (o : ONote) (n : ℕ) : ONote :=
  match o.fundamentalSequence with
  | Sum.inl none => 0
  | Sum.inl (some a) => a
  | Sum.inr f => f n

lemma fsKind_eq_of_none {o : ONote} (h : o.fundamentalSequence = Sum.inl none) :
    fsKind o = 0 := by simp [fsKind, h]

lemma fsVal_eq_of_none {o : ONote} (h : o.fundamentalSequence = Sum.inl none) (n : ℕ) :
    fsVal o n = 0 := by simp [fsVal, h]

lemma fsKind_eq_of_some {o a : ONote} (h : o.fundamentalSequence = Sum.inl (some a)) :
    fsKind o = 1 := by simp [fsKind, h]

lemma fsVal_eq_of_some {o a : ONote} (h : o.fundamentalSequence = Sum.inl (some a)) (n : ℕ) :
    fsVal o n = a := by simp [fsVal, h]

lemma fsKind_eq_of_inr {o : ONote} {f : ℕ → ONote} (h : o.fundamentalSequence = Sum.inr f) :
    fsKind o = 2 := by simp [fsKind, h]

lemma fsVal_eq_of_inr {o : ONote} {f : ℕ → ONote} (h : o.fundamentalSequence = Sum.inr f)
    (n : ℕ) : fsVal o n = f n := by simp [fsVal, h]

lemma eq_zero_of_fundamentalSequence_inl_none {o : ONote}
    (h : o.fundamentalSequence = Sum.inl none) : o = 0 := by
  have := ONote.fundamentalSequence_has_prop o
  rw [h] at this
  exact this

@[simp] lemma fundamentalSequence_zero :
    (0 : ONote).fundamentalSequence = Sum.inl none := rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Small cast facts -/

private lemma coe_sub_one (m : ℕ) (hm : 1 ≤ m) : ((m : V)) - 1 = ((m - 1 : ℕ) : V) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp

private lemma modelCode_eq_zero_iff (o : ONote) : modelCode (V := V) o = 0 ↔ o = 0 := by
  cases o with
  | zero => simp
  | oadd e n r =>
      simp only [modelCode_oadd]
      constructor
      · intro h; exact absurd h (ocOadd_pos _ _ _).ne'
      · intro h; exact absurd h (by simp)

private lemma cast_succPNat (k : ℕ) : (((k.succPNat : ℕ+) : ℕ) : V) = (k : V) + 1 := by
  simp [Nat.succPNat]

private lemma cast_ne_one {j : ℕ} (h : j ≠ 1) : ((j : ℕ) : V) ≠ 1 := by
  simp only [ne_eq, show (1 : V) = ((1 : ℕ) : V) by simp, nat_cast_inj]
  exact h

/-! ### The bridge -/

/-- **`ifd` computes `ONote.fundamentalSequence` on standard codes.** -/
theorem ifd_modelCode : ∀ (o : ONote) (n : ℕ),
    ifd (modelCode (V := V) o) (n : V) = ⟪(fsKind o : V), modelCode (V := V) (fsVal o n)⟫ := by
  intro o
  induction o with
  | zero => intro n; simp [fsKind, fsVal]
  | oadd a m b iha ihb =>
      intro n
      rw [modelCode_oadd, ifd_ocOadd]
      by_cases hb : b = 0
      · subst hb
        rw [if_neg (by simp)]
        rw [iha n]
        simp only [pi₁_pair, pi₂_pair]
        have hcoe1 : (((m : ℕ) : V) = 1) ↔ (m : ℕ) = 1 := by
          rw [show (1 : V) = ((1 : ℕ) : V) by simp, nat_cast_inj]
        have hmpos : 1 ≤ (m : ℕ) := m.2
        rcases ha : a.fundamentalSequence with ⟨_ | a'⟩ | f
        · rw [fsKind_eq_of_none ha]
          simp only [Nat.cast_zero, if_true]
          rcases hm : m.natPred with _ | k
          · have hm1 : (m : ℕ) = 1 := by simp only [PNat.natPred] at hm; omega
            have hfs := fs_oadd_zz a m ha hm
            rw [fsKind_eq_of_some hfs, fsVal_eq_of_some hfs]
            simp [hm1]
          · have hmk : (m : ℕ) = k + 2 := by simp only [PNat.natPred] at hm; omega
            have hmne : (m : ℕ) ≠ 1 := by omega
            have hfs := fs_oadd_zs a m ha hm
            rw [fsKind_eq_of_some hfs, fsVal_eq_of_some hfs]
            rw [if_neg (fun h => hmne (hcoe1.mp h))]
            rw [coe_sub_one (m : ℕ) hmpos]
            have hmm : (m : ℕ) - 1 = ((k.succPNat : ℕ+) : ℕ) := by simp [Nat.succPNat]; omega
            rw [hmm]
            simp only [modelCode_oadd, modelCode_zero, Nat.cast_one]
        · rw [fsKind_eq_of_some ha, fsVal_eq_of_some ha]
          simp only [Nat.cast_one, if_neg (one_ne_zero' V), if_true]
          rcases hm : m.natPred with _ | k
          · have hm1 : (m : ℕ) = 1 := by simp only [PNat.natPred] at hm; omega
            have hfs := fs_oadd_sz a m ha hm
            rw [fsKind_eq_of_inr hfs, fsVal_eq_of_inr hfs]
            rw [if_pos (hcoe1.mpr hm1)]
            simp only [modelCode_oadd, modelCode_zero, Nat.cast_ofNat, cast_succPNat]
          · have hmk : (m : ℕ) = k + 2 := by simp only [PNat.natPred] at hm; omega
            have hmne : (m : ℕ) ≠ 1 := by omega
            have hfs := fs_oadd_ss a m ha hm
            rw [fsKind_eq_of_inr hfs, fsVal_eq_of_inr hfs]
            rw [if_neg (fun h => hmne (hcoe1.mp h))]
            rw [coe_sub_one (m : ℕ) hmpos]
            have hmm : (m : ℕ) - 1 = ((k.succPNat : ℕ+) : ℕ) := by simp [Nat.succPNat]; omega
            rw [hmm]
            simp only [modelCode_oadd, modelCode_zero, Nat.cast_ofNat, cast_succPNat]
        · rw [fsKind_eq_of_inr ha, fsVal_eq_of_inr ha]
          have h2 : ((2 : ℕ) : V) ≠ 0 := by
            simp only [ne_eq, show (0 : V) = ((0 : ℕ) : V) by simp, nat_cast_inj]; omega
          have h2' : ((2 : ℕ) : V) ≠ 1 := cast_ne_one (by omega)
          rw [if_neg h2, if_neg h2']
          rcases hm : m.natPred with _ | k
          · have hm1 : (m : ℕ) = 1 := by simp only [PNat.natPred] at hm; omega
            have hfs := fs_oadd_lz a m ha hm
            rw [fsKind_eq_of_inr hfs, fsVal_eq_of_inr hfs]
            rw [if_pos (hcoe1.mpr hm1)]
            simp only [modelCode_oadd, modelCode_zero, Nat.cast_ofNat]
            norm_num
          · have hmk : (m : ℕ) = k + 2 := by simp only [PNat.natPred] at hm; omega
            have hmne : (m : ℕ) ≠ 1 := by omega
            have hfs := fs_oadd_ls a m ha hm
            rw [fsKind_eq_of_inr hfs, fsVal_eq_of_inr hfs]
            rw [if_neg (fun h => hmne (hcoe1.mp h))]
            rw [coe_sub_one (m : ℕ) hmpos]
            have hmm : (m : ℕ) - 1 = ((k.succPNat : ℕ+) : ℕ) := by simp [Nat.succPNat]; omega
            rw [hmm]
            simp only [modelCode_oadd, modelCode_zero, Nat.cast_ofNat, cast_succPNat]
            norm_num
      · -- the tail is nonzero: recurse into it
        have hbc : modelCode (V := V) b ≠ 0 := by
          simp only [ne_eq, modelCode_eq_zero_iff]; exact hb
        rw [if_pos hbc, ihb n]
        simp only [pi₁_pair, pi₂_pair]
        rcases hbf : b.fundamentalSequence with ⟨_ | b'⟩ | f
        · exact absurd (eq_zero_of_fundamentalSequence_inl_none hbf) hb
        · rw [fsKind_eq_of_some hbf, fsVal_eq_of_some hbf,
            fsKind_eq_of_some (fs_oadd_tail_some a m b hbf),
            fsVal_eq_of_some (fs_oadd_tail_some a m b hbf), modelCode_oadd]
        · rw [fsKind_eq_of_inr hbf, fsVal_eq_of_inr hbf,
            fsKind_eq_of_inr (fs_oadd_tail_inr a m b hbf),
            fsVal_eq_of_inr (fs_oadd_tail_inr a m b hbf), modelCode_oadd]

end GoodsteinWu.InternalFund
