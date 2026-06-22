/-
# Fast-growing hierarchy infrastructure (toward the Hardy facts `Hmono`/`Hmono_n`/`Hdom`)

The witness-bounded lower bound (`wip/WitnessBound.lean`) consumes a fast-growing/Hardy function with
monotonicity + Goodstein domination.  mathlib has `ONote.fastGrowing` but **no** lemmas about its
growth (it is deliberately minimal).  This file starts that infrastructure.

**`fastGrowing_id_le`** — `n ≤ fastGrowing o n` for every notation `o` — is the *inflationary* half,
which (contra a first guess) is **separable** from the hard τ-controlled ordinal-monotonicity: its
successor case needs only that `fastGrowing a` is inflationary (iterating a `≥ id` map keeps `≥ id`),
and its limit case is a direct appeal to the smaller-ordinal IH.  Axiom-clean.  WIP — not in build.
-/
import Mathlib.SetTheory.Ordinal.Notation

namespace GoodsteinPA.FastGrowing

open ONote Ordinal

/-- Iterating an inflationary map keeps the value `≥` the start: if `id ≤ g` pointwise then
`m ≤ g^[i] m`. -/
theorem le_iterate_of_id_le {g : ℕ → ℕ} (hg : ∀ m, m ≤ g m) (i m : ℕ) : m ≤ g^[i] m := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ']; exact le_trans ih (hg _)

/-- **The fast-growing hierarchy is inflationary:** `n ≤ fastGrowing o n` for every `o`.
By well-founded recursion on `o`, following `fastGrowing`'s own fundamental-sequence case split. -/
theorem fastGrowing_id_le (o : ONote) (n : ℕ) : n ≤ fastGrowing o n := by
  -- ONote lacks a `WellFoundedLT` instance, so induct on the ordinal `repr o`.
  suffices H : ∀ (g : Ordinal.{0}) (o : ONote), ONote.repr o = g → ∀ n, n ≤ fastGrowing o n from
    H (ONote.repr o) o rfl n
  intro g
  induction g using WellFoundedLT.induction with
  | _ g IH =>
    intro o ho n
    have hprop := fundamentalSequence_has_prop o
    rcases e : fundamentalSequence o with (_ | a) | f
    · -- `o = 0`: `fastGrowing o = Nat.succ`.
      rw [fastGrowing_zero' o e]; exact Nat.le_succ n
    · -- `o = succ a`: `fastGrowing o n = (fastGrowing a)^[n] n`, with `ONote.repr a < g`.
      rw [e] at hprop
      have ha : ONote.repr a < g := by rw [← ho, hprop.1]; exact Order.lt_succ a.repr
      rw [fastGrowing_succ o e]
      exact le_iterate_of_id_le (IH (ONote.repr a) ha a rfl) n n
    · -- `o` limit: `fastGrowing o n = fastGrowing (f n) n`, with `ONote.repr (f n) < g`.
      rw [e] at hprop
      have hlt : ONote.repr (f n) < g := by rw [← ho]; exact lt_def.mp (hprop.2.1 n).2.1
      rw [fastGrowing_limit o e]
      exact IH (ONote.repr (f n)) hlt (f n) rfl n

end GoodsteinPA.FastGrowing
