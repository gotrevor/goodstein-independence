/-
# `src/GoodsteinPA/Epsilon0Complete.lean` — ε₀-completeness of CNF notations

mathlib's `Mathlib/SetTheory/Ordinal/Notation.lean` proves that `ONote.repr` is order-preserving and
injective on normal forms — an *embedding* `NONote ↪ ε₀` — but it does NOT prove surjectivity onto the
ordinals `< ε₀`. That surjectivity is the real F-girder of this project (`PENDING_WORK.md`, lap-18
reflection): the lower bound `ε₀ ≤ orderType lt` for the seam order `lt` ultimately needs every ordinal
below ε₀ to be *named* by a CNF notation.

This file fills that gap with a pure-mathlib proof (zero Foundation dependency):

  `exists_NF_repr_eq : ∀ o < ε₀, ∃ x : ONote, x.NF ∧ x.repr = o`.

The proof is the standard Cantor-normal-form recursion. For `o ≠ 0` write `o = ω^e · c + r` with
`e = log ω o`, `c = o / ω^e` (a positive natural number, since `1 ≤ c < ω`), `r = o % ω^e < ω^e`.
Both `e` and `r` are `< o` (the key fact `log ω o < o` for `o < ε₀` is `log_omega0_lt_self`, which
uses that `ω^·` has no fixed point below ε₀), so well-founded recursion on `o` supplies CNF notations
`ē, r̄` for them, and `ONote.oadd ē c r̄` is the notation for `o`.
-/
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.SetTheory.Ordinal.Veblen

namespace GoodsteinPA.Epsilon0Complete

open Ordinal ONote
open scoped Ordinal

/-- For `0 ≠ o < ε₀`, the leading CNF exponent `log ω o` is strictly below `o`.
Equality would force `ω ^ o ≤ o`, i.e. `o` to be an ε-number, contradicting `o < ε₀`. -/
theorem log_omega0_lt_self {o : Ordinal} (ho : o ≠ 0) (hε : o < ε₀) :
    Ordinal.log ω o < o := by
  have h1 : ω ^ Ordinal.log ω o ≤ o := opow_log_le_self ω ho
  have h2 : Ordinal.log ω o ≤ ω ^ Ordinal.log ω o :=
    (isNormal_opow one_lt_omega0).strictMono.le_apply
  rcases lt_or_eq_of_le (h2.trans h1) with h | h
  · exact h
  · rw [h] at h1
    exact absurd (epsilon_zero_le_of_omega0_opow_le h1) (not_le.2 hε)

/-- **ε₀-completeness of CNF notations.** Every ordinal `< ε₀` is `repr` of some normal-form `ONote`.
This is the surjectivity direction missing from mathlib's `Ordinal/Notation.lean`. -/
theorem exists_NF_repr_eq :
    ∀ o : Ordinal, o < ε₀ → ∃ x : ONote, ONote.NF x ∧ ONote.repr x = o := by
  intro o
  induction o using WellFoundedLT.induction with
  | _ o IH =>
    intro hε
    rcases eq_or_ne o 0 with rfl | ho
    · exact ⟨0, ONote.NF.zero, ONote.repr_zero⟩
    · -- leading exponent
      set e := Ordinal.log ω o with he
      have hee : e < o := log_omega0_lt_self ho hε
      obtain ⟨eN, heNF, heRepr⟩ := IH e hee (hee.trans hε)
      -- remainder
      set r := o % ω ^ e with hr
      have hre : r < o := mod_opow_log_lt_self ω ho
      obtain ⟨rN, hrNF, hrRepr⟩ := IH r hre (hre.trans hε)
      -- coefficient `c = o / ω^e` is a positive natural number
      have hcpos : 0 < o / ω ^ e := div_opow_log_pos ω ho
      have hclt : o / ω ^ e < ω := div_opow_log_lt o one_lt_omega0
      obtain ⟨m, hm⟩ := lt_omega0.1 hclt
      have hmpos : 0 < m := by rw [hm] at hcpos; exact_mod_cast hcpos
      have hωe : ω ^ e ≠ 0 := (opow_pos e omega0_pos).ne'
      refine ⟨ONote.oadd eN ⟨m, hmpos⟩ rN, ?_, ?_⟩
      · -- normal form
        refine ONote.NF.oadd heNF _ (ONote.NF.below_of_lt' ?_ hrNF)
        rw [hrRepr, heRepr]
        exact mod_lt _ hωe
      · -- value
        have hval : ONote.repr (ONote.oadd eN ⟨m, hmpos⟩ rN)
            = ω ^ ONote.repr eN * (m : Ordinal) + ONote.repr rN := by
          simp [ONote.repr]
        rw [hval, heRepr, hrRepr, hr, ← hm]
        exact div_add_mod o (ω ^ e)

end GoodsteinPA.Epsilon0Complete
