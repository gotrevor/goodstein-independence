/-
# `DescentCore.lean` — E-core semantic bricks: `evalNat` order-monotonicity (Rathjen 2.3(iii))

The descent wall **E** factors (see `DESCENT-PLAN.md`) into the proof-translation **E-lift**
(`DescentLift.lean`, done) and **E-core** — Rathjen 2014 §3 "slowing down", whose workhorse is the
order-reflection of `T̂^b_ω` (= `Domination.evalNat`): for ordinals/notations with bounded
coefficients (`Canon`), `α < β ⇔ T̂(α) < T̂(β)` (Rathjen Lemma 2.2/2.3(iii)).

`Domination.lean` already proves the round-trip `canon_repr : toOrdinal (b+1) (evalNat b E) = repr E`
for `Canon`/`NF` notations. Since `toOrdinal (b+1)` is strictly monotone on `ℕ`
(`toOrdinal_mono_and_bound`), `evalNat b` therefore reflects and preserves the notation order
*exactly* on the `Canon` domain. This file records that reflection — the comparison fact Lemma 3.6's
inequality (6) runs on. Pure mathlib/ONote, `#print axioms`-clean, zero `Foundation` dependency.
-/
import GoodsteinPA.Domination

namespace GoodsteinPA.Dom

open ONote Ordinal

/-- `toOrdinal b` reflects strict order (it is strictly monotone on `ℕ`, hence an order embedding). -/
theorem toOrdinal_lt_iff (b : ℕ) (hb : 2 ≤ b) (m n : ℕ) :
    toOrdinal b m < toOrdinal b n ↔ m < n := by
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    rcases lt_or_eq_of_le hle with h' | h'
    · exact absurd ((toOrdinal_mono_and_bound b hb m).1 n h') (by simpa using h.le)
    · simp [h'] at h
  · exact (toOrdinal_mono_and_bound b hb n).1 m

/-- `toOrdinal b` reflects `≤`. -/
theorem toOrdinal_le_iff (b : ℕ) (hb : 2 ≤ b) (m n : ℕ) :
    toOrdinal b m ≤ toOrdinal b n ↔ m ≤ n := by
  rw [← not_lt, ← not_lt, toOrdinal_lt_iff b hb]

/-- **Rathjen Lemma 2.3(iii) (`evalNat` form).** On the `Canon`/`NF` domain, `evalNat b`
order-reflects: `evalNat b o < evalNat b p ↔ o.repr < p.repr` (equivalently `↔ o < p`). Immediate
from the round-trip `canon_repr` plus strict monotonicity of `toOrdinal (b+1)`. -/
theorem evalNat_lt_iff (b : ℕ) (hb : 2 ≤ b) {o p : ONote}
    (hco : Canon b o) (hcp : Canon b p) (hno : o.NF) (hnp : p.NF) :
    evalNat b o < evalNat b p ↔ o.repr < p.repr := by
  rw [← canon_repr b hb o hco hno, ← canon_repr b hb p hcp hnp]
  exact (toOrdinal_lt_iff (b + 1) (by omega) _ _).symm

/-- `evalNat b` order-reflects `≤` on the `Canon`/`NF` domain. -/
theorem evalNat_le_iff (b : ℕ) (hb : 2 ≤ b) {o p : ONote}
    (hco : Canon b o) (hcp : Canon b p) (hno : o.NF) (hnp : p.NF) :
    evalNat b o ≤ evalNat b p ↔ o.repr ≤ p.repr := by
  rw [← not_lt, ← not_lt, evalNat_lt_iff b hb hcp hco hnp hno]

/-- `evalNat` is strictly monotone in the notation order on the `Canon`/`NF` domain
(`o < p ⇒ evalNat b o < evalNat b p`). The `T̂` half of Rathjen's order isomorphism. -/
theorem evalNat_lt_of_lt (b : ℕ) (hb : 2 ≤ b) {o p : ONote}
    (hco : Canon b o) (hcp : Canon b p) (hno : o.NF) (hnp : p.NF) (h : o < p) :
    evalNat b o < evalNat b p :=
  (evalNat_lt_iff b hb hco hcp hno hnp).2 (ONote.lt_def.1 h)

end GoodsteinPA.Dom
