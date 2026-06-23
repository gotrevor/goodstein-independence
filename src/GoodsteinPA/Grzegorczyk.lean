/-
# `Grzegorczyk.lean` — the ℕ-template for Rathjen 2014 §3 "slowing down" (Lemma 3.3 / Cor 3.4)

This file is the **self-contained ℕ-template** for the genuine remaining wall of the `hbound`
obligation (`DescentSemantic.no_min_descent_absurd_of_goodstein`): Rathjen's **Corollary 3.4**, the
slow-down of an arbitrary ε₀-descent into a *slow* one (`|αᵢ| ≤ K·(i+1)`), whose workhorse is
**Lemma 3.3** — a primitive-recursive `g : ℕ² → ω^ω` with

  (1) `g(n,m) > g(n,m+1)` whenever `m < f(n)`   (strict descent within a block of length `f(n)`)
  (2) `|g(n,m)| ≤ K·(n+m+1)`                     (linearly-bounded max-coefficient `C`)

built by induction on the Grzegorczyk hierarchy `(fₗ)` (Rathjen Lemma 3.2). Everything here is pure
`ℕ`/`ONote`, zero `Foundation` dependency — it typechecks or it doesn't, no faithfulness risk. It is
the proof skeleton the *M-internal* slow-down (`InternalONote` codes) ports onto.

Downstream consumer (already built, `DescentCore.lean`): Thm 3.5 reindex (`C_betaTail_le`,
`repr_betaTail_within/_boundary`) + Lemma 3.6 (`lemma36_nonterminating`). This file supplies the
missing *input* to Thm 3.5: the slow descent.
-/
import GoodsteinPA.DescentCore

namespace GoodsteinPA.Grz

open ONote Ordinal
open GoodsteinPA.Dom (C C_zero C_one C_oadd)

/-! ## The max-coefficient `C` on finite notations -/

/-- `C (ofNat m) = m`: a finite ordinal's only coefficient is its value. -/
@[simp] theorem C_ofNat (m : ℕ) : C (ONote.ofNat m) = m := by
  cases m with
  | zero => simp
  | succ k => simp [ONote.ofNat_succ, C_oadd, C_zero]

/-! ## Rathjen's Grzegorczyk-style hierarchy `(fₗ)`

`F 0 n = n+1`, `F (l+1) n = (F l)^[n] n` (the diagonalization `(fₗ)ⁿ(n)`). Lemma 3.2 says every
primitive-recursive function is pointwise dominated by some `F l` (mathlib's `ack`/`exists_lt_ack`
gives the same domination, used only at the very end of Lemma 3.3 to reduce an arbitrary `f`). -/
def F : ℕ → ℕ → ℕ
  | 0,     n => n + 1
  | l + 1, n => (F l)^[n] n

@[simp] theorem F_zero (n : ℕ) : F 0 n = n + 1 := rfl

@[simp] theorem F_succ (l n : ℕ) : F (l + 1) n = (F l)^[n] n := rfl

/-! ## Base case `g₀` of Lemma 3.3 (for `f = F 0 = (·+1)`)

Rathjen: `g(n,m) = (n+2) -· m` (truncated subtraction), a finite ordinal. Descends for `m < n+1`
(i.e. `m ≤ n`), and `C(g₀ n m) = (n+2)-m ≤ n+2 ≤ 2·(n+m+1)`, so `K = 2`. -/
def g0 (n m : ℕ) : ONote := ONote.ofNat ((n + 2) - m)

@[simp] theorem g0_NF (n m : ℕ) : (g0 n m).NF := by
  unfold g0; infer_instance

/-- Lemma 3.3(1), base case: `g₀` strictly descends in `m` while `m < F 0 n`. -/
theorem g0_desc (n m : ℕ) (hm : m < F 0 n) : (g0 n (m + 1)).repr < (g0 n m).repr := by
  have hmn : m ≤ n := by simpa [F] using Nat.lt_succ_iff.1 (by simpa using hm)
  simp only [g0, ONote.repr_ofNat]
  have h : (n + 2) - (m + 1) < (n + 2) - m := by omega
  exact_mod_cast h

/-- Lemma 3.3(2), base case: `C(g₀ n m) ≤ 2·(n+m+1)` (so `K = 2` works for `F 0`). -/
theorem g0_bound (n m : ℕ) : C (g0 n m) ≤ 2 * (n + m + 1) := by
  simp only [g0, C_ofNat]; omega

end GoodsteinPA.Grz
