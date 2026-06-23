/-
# `InternalONote.lean` — internal ONote (CNF) codes inside `V ⊧ₘ* 𝗜𝚺₁`

The lone remaining wall (`hbound` in `DescentSemantic.no_min_descent_absurd_of_goodstein`) needs
the Rathjen §3 slow-down run inside a model `M`, on an `≺`-descent. The deep content is the
**order-reflection** of the descent (see `ANALYSIS-2026-06-23-lap37-order-reflection-opacity.md`):
to compute the slow-down `βₖ` one must read the **Cantor normal form** of the descent elements
inside `M`. That requires ONote CNF terms presented as `M`-elements with `𝚺₁`-definable structure.

This file lays the foundation: **CNF codes as nested HFS pairs**, the decode projections, and the
**subterm-bound lemmas** (`ocExp/ocCoeff/ocTail` of an `oadd`-code are `<` the code). The bounds are
exactly what a course-of-values recursion over the code value needs (à la `InternalBump.ibumpTable`),
so the next bricks — `isONoteCode`, `iC` (max coefficient), `ievalNat`, the CNF comparison `icmp`
with internal `evalNat_lt_iff` — can recurse on the code. Pure HFS pairing; no `sorry`.

Coding: `0 ↦ (0 : V)`, and `oadd e n r ↦ ⟪⟪ec, n⟫, rc⟫ + 1` (the `+1` tags every non-zero ONote with
a positive code, so `0` is the *unique* code of the ordinal `0`).
-/
import GoodsteinPA.InternalBump

namespace GoodsteinPA.InternalONote

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- Code of `oadd e n r` from the subcodes `ec` (exponent), `n` (coefficient), `rc` (tail). -/
noncomputable def ocOadd (ec n rc : V) : V := ⟪⟪ec, n⟫, rc⟫ + 1

/-- The exponent subcode of a code: `π₁ (fstIdx c)` (`fstIdx c = π₁ (c-1) = ⟪ec,n⟫`). -/
noncomputable def ocExp (c : V) : V := π₁ (fstIdx c)

/-- The coefficient of a code: `π₂ (fstIdx c)`. -/
noncomputable def ocCoeff (c : V) : V := π₂ (fstIdx c)

/-- The tail subcode of a code: `sndIdx c = π₂ (c-1) = rc`. -/
noncomputable def ocTail (c : V) : V := sndIdx c

@[simp] lemma ocOadd_pos (ec n rc : V) : 0 < ocOadd ec n rc := by simp [ocOadd]

@[simp] lemma ocOadd_ne_zero (ec n rc : V) : ocOadd ec n rc ≠ 0 :=
  (ocOadd_pos ec n rc).ne'

/-! ### Round-trip: decode recovers the subcodes -/

@[simp] lemma fstIdx_ocOadd (ec n rc : V) : fstIdx (ocOadd ec n rc) = ⟪ec, n⟫ := by
  simp [fstIdx, ocOadd]

@[simp] lemma sndIdx_ocOadd (ec n rc : V) : sndIdx (ocOadd ec n rc) = rc := by
  simp [sndIdx, ocOadd]

@[simp] lemma ocExp_ocOadd (ec n rc : V) : ocExp (ocOadd ec n rc) = ec := by
  simp [ocExp]

@[simp] lemma ocCoeff_ocOadd (ec n rc : V) : ocCoeff (ocOadd ec n rc) = n := by
  simp [ocCoeff]

@[simp] lemma ocTail_ocOadd (ec n rc : V) : ocTail (ocOadd ec n rc) = rc := by
  simp [ocTail]

/-! ### Subterm bounds (course-of-values decrease)

Each subcode of an `oadd`-code is strictly smaller than the code itself: the pairing places the
subterm `≤` the inner pair `≤` the outer pair `< (+1) =` the code. These are the strict-decrease
facts a course-of-values recursion on the code value relies on. -/

lemma ocExp_lt (ec n rc : V) : ocExp (ocOadd ec n rc) < ocOadd ec n rc := by
  rw [ocExp_ocOadd]
  calc ec ≤ ⟪ec, n⟫ := le_pair_left ec n
    _ ≤ ⟪⟪ec, n⟫, rc⟫ := le_pair_left _ rc
    _ < ⟪⟪ec, n⟫, rc⟫ + 1 := by simp
    _ = ocOadd ec n rc := rfl

lemma ocCoeff_lt (ec n rc : V) : ocCoeff (ocOadd ec n rc) < ocOadd ec n rc := by
  rw [ocCoeff_ocOadd]
  calc n ≤ ⟪ec, n⟫ := le_pair_right ec n
    _ ≤ ⟪⟪ec, n⟫, rc⟫ := le_pair_left _ rc
    _ < ⟪⟪ec, n⟫, rc⟫ + 1 := by simp
    _ = ocOadd ec n rc := rfl

lemma ocTail_lt (ec n rc : V) : ocTail (ocOadd ec n rc) < ocOadd ec n rc := by
  rw [ocTail_ocOadd]
  calc rc ≤ ⟪⟪ec, n⟫, rc⟫ := le_pair_right _ rc
    _ < ⟪⟪ec, n⟫, rc⟫ + 1 := by simp
    _ = ocOadd ec n rc := rfl

/-- The exponent subcode of any positive code is `< c` (via `ocExp = π₁ (fstIdx c)` and the pairing
bounds, with `fstIdx c ≤ c - 1 < c`). The form a recursion uses when it only knows `0 < c`. -/
lemma ocExp_lt_of_pos {c : V} (hc : 0 < c) : ocExp c < c := by
  have h1 : ocExp c ≤ fstIdx c := by simp [ocExp]
  have h2 : fstIdx c ≤ c - 1 := by simp [fstIdx]
  have h3 : c - 1 < c := pred_lt_self_of_pos hc
  exact lt_of_le_of_lt (le_trans h1 h2) h3

lemma ocTail_lt_of_pos {c : V} (hc : 0 < c) : ocTail c < c := by
  have h1 : ocTail c ≤ c - 1 := by simp [ocTail, sndIdx]
  exact lt_of_le_of_lt h1 (pred_lt_self_of_pos hc)

end GoodsteinPA.InternalONote
