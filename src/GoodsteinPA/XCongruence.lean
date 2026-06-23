/-
# `XCongruence.lean` — discharging the X-congruence axiom into the `PXFc`/`Z∞` carrier (lap-31, Task A1)

**Why.** The lap-30 completeness redirect needs `[Structure.Eq LX M]` (real equality) to run the
internal Goodstein substrate in a model `M ⊧ paLX`. Supplying it (`EQ.provOf` over `[Structure.Eq]`-
models) requires `𝗘𝗤 ⪯ paLX`. The lap-31 analysis pinned the EXACT gap: the single axiom
**X-congruence** `Eq.relExt Xsym = ∀x y, x = y → X(x) → X(y)` (every other `𝗘𝗤(LX)` axiom is an
`lMap Φ`-image of an `𝗘𝗤(ℒₒᵣ)` axiom, already in `lMap Φ 𝗣𝗔⁻ ⊆ paLX`). To keep `peano_not_proves_TI`
alive after augmenting `paLX ⊇ 𝗘𝗤`, the embedding's axiom-discharge `hax` must produce a
bounded-ordinal `PXFc` derivation of (the `asgX`-image of) X-congruence. Unlike the X-free base axioms
(which use `provable_true_x`), X-congruence MENTIONS `X`, so it needs a hand derivation — this file.

**The derivation.** Strip `∀⁰*` (via `PXFc_allClosure`) to per-numeral `(m, n)` instances of the matrix
`(m = n) → X(m) → X(n)`, i.e. the Tait sequent `[m ≠ n, ¬X(m), X(n)]`. Two cases close it cut-free,
`XFreeAx`-safe:
- `m = n`: `PXFc.axLv Xsym ![n] ![m]` (the value-congruent literal axiom — `X(n)` vs `¬X(m)` with
  `val (nm n) = val (nm m)`), the X-pair axiom built lap-16 for exactly this purpose.
- `m ≠ n`: `PXFc.axTrue false Eq.eq ![nm m, nm n]` — the X-free true literal `m ≠ n`.

This brick is sorry-free + `#print axioms`-clean; it is NOT yet wired into `paLX`/`hax_paLX` (that
augmentation has a 6-file blast radius and re-validates `peano_not_proves_TI`, a later lap — see
`PENDING_WORK.md` lap-31 Task A1). It stands as the verified crux of that task.
-/
import GoodsteinPA.EmbeddingX

namespace GoodsteinPA.XCongruence

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open GoodsteinPA GoodsteinPA.LangX GoodsteinPA.EmbeddingX GoodsteinPA.ZinftyGen
open GoodsteinPA.XFreeCutElim

/-- **The `=`-atom's ℕ-truth.** `m = n` (as the lifted `LX`-literal at numerals) is `LitTrue` iff
`m = n`, since `LX`'s `=`-symbol is `Sum.inl Eq.eq` and the `ℒₒᵣ`-reduct of `structLX` is the standard
model. Drives the `m ≠ n` close of the X-congruence matrix. -/
theorem litTrue_eq_iff (m n : ℕ) :
    LitTrue (Semiformula.rel (Language.Eq.eq : LX.Rel 2) ![nm m, nm n]) ↔ m = n := by
  unfold LitTrue
  rw [Semiformula.eval_rel]
  have hfun : (fun i => Semiterm.valm ℕ ![] (id : ℕ → ℕ)
        ((![nm m, nm n] : Fin 2 → Semiterm LX ℕ 0) i)) = ![m, n] := by
    funext i
    refine i.cases ?_ (fun j => j.cases ?_ (fun k => k.elim0))
    · simp
    · simp
  show Structure.rel (Language.Eq.eq : LX.Rel 2)
      (fun i => Semiterm.valm ℕ ![] (id : ℕ → ℕ) ((![nm m, nm n] : Fin 2 → Semiterm LX ℕ 0) i)) ↔ m = n
  rw [hfun]
  -- ambient `= structLX False`; `Eq.eq = Sum.inl Eq.eq` picks the standard `ℒₒᵣ`-reduct, whose
  -- `=`-relation is real equality — all definitional.
  exact Iff.rfl

/-- The Tait matrix of X-congruence at numerals `(m, n)`: `m ≠ n ∨ (¬X(m) ∨ X(n))`. -/
noncomputable def xcMatrix (m n : ℕ) : Form LX :=
  (Semiformula.nrel Language.Eq.eq ![nm m, nm n]) ⋎
    ((Semiformula.nrel Xsym ![nm m]) ⋎ (Semiformula.rel Xsym ![nm n]))

/-- **The matrix derivation (cut-free, `XFreeAx`-safe).** For any `(m, n)` and side sequent `Δ`, the
matrix `xcMatrix m n` is `PXFc`-derivable at finite ordinal, cut rank `0`. `m = n` closes via the
value-congruent X-literal axiom `axLv Xsym`; `m ≠ n` via the true literal `m ≠ n` (`axTrue`). -/
theorem pxfc_xcMatrix (m n : ℕ) (Δ : Seq LX) :
    ∃ a : Ordinal.{0}, PXFc a 0 (insert (xcMatrix m n) Δ) := by
  -- the three literals of the matrix
  set A : Form LX := Semiformula.nrel Language.Eq.eq ![nm m, nm n] with hA
  set B : Form LX := Semiformula.nrel Xsym ![nm m] with hB
  set C : Form LX := Semiformula.rel Xsym ![nm n] with hC
  -- close the flat 3-literal sequent `{A, B, C} ∪ Δ` (cut-free)
  have hclose : PXFc 0 0 (insert A (insert B (insert C Δ))) := by
    by_cases h : m = n
    · -- equal: axLv on Xsym (`C = X(n)` vs `B = ¬X(m)`, equal values)
      subst h
      refine (PXFc.axLv Xsym ![nm m] ![nm m] (fun i => rfl) ?_ ?_)
      · show Semiformula.rel Xsym ![nm m] ∈ _; simp [hC]
      · show Semiformula.nrel Xsym ![nm m] ∈ _; simp [hB]
    · -- unequal: the literal `A = (m ≠ n)` is true
      have htrue : LitTrue (signedLit (L := LX) false Language.Eq.eq ![nm m, nm n]) := by
        show LitTrue (Semiformula.nrel (Language.Eq.eq : LX.Rel 2) ![nm m, nm n])
        rw [← Semiformula.neg_rel, litTrue_neg, litTrue_eq_iff]
        exact h
      have hmem : signedLit (L := LX) false Language.Eq.eq ![nm m, nm n]
          ∈ insert A (insert B (insert C Δ)) := by
        show Semiformula.nrel Language.Eq.eq ![nm m, nm n] ∈ _; simp [hA]
      exact PXFc.axTrue false Language.Eq.eq ![nm m, nm n] (by rfl) htrue hmem
  -- wrap the two `⋎`: first `B ⋎ C`, then `A ⋎ (B ⋎ C)`
  have hsub1 : insert A (insert B (insert C Δ)) ⊆ insert B (insert C (insert A Δ)) := by
    intro x hx; simp only [Finset.mem_insert] at hx ⊢; tauto
  have h1 : PXFc (0 + 1) 0 (insert (B ⋎ C) (insert A Δ)) :=
    PXFc.orI B C (hclose.weakening hsub1)
  have hsub2 : insert (B ⋎ C) (insert A Δ) ⊆ insert A (insert (B ⋎ C) Δ) := by
    intro x hx; simp only [Finset.mem_insert] at hx ⊢; tauto
  have h2 : PXFc ((0 + 1) + 1) 0 (insert (A ⋎ (B ⋎ C)) Δ) :=
    PXFc.orI A (B ⋎ C) (h1.weakening hsub2)
  exact ⟨_, h2.cast (by rw [xcMatrix, ← hA, ← hB, ← hC])⟩

end GoodsteinPA.XCongruence
