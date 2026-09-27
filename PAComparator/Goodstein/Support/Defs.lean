/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Data.Nat.Log

/-!
# Comparator challenge support — the Mathlib-native Goodstein trio

`base`, `bump`, `goodsteinSeq`, verbatim from `src/GoodsteinPA/Defs.lean` (Goodstein 1944), with the
same single import.  Kept out of `Challenge.lean` because the heavier Foundation imports there change
how `b ^ e` elaborates (`Monoid.toPow` instead of `instPowNat`), so `bump`'s body would no longer be
byte-identical to the solution's.
-/

namespace GoodsteinPA

/-- The base used to read `G k` at step `k`: `base k = k + 2` (so `G 0` is read in base 2,
the first bump sends `2 ↦ 3`, and so on). Verbatim from `Defs.lean:25`. -/
def base (k : ℕ) : ℕ := k + 2

/-- **Hereditary-base bump.** `bump b n` reads `n` in hereditary base `b` and replaces every
occurrence of `b` by `b + 1`. Peeling the top power (`e = log b n`, `c = n / b^e`,
`r = n % b^e`): `bump b n = c · (b+1)^(bump b e) + bump b r`, with `bump b 0 = 0`. Defined by
well-founded recursion (Lean marks it irreducible) — verbatim from `Defs.lean:30`, including the
`termination_by`/`decreasing_by`. -/
def bump (b : ℕ) (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    n / b ^ Nat.log b n * (b + 1) ^ bump b (Nat.log b n) + bump b (n % b ^ Nat.log b n)
termination_by n
decreasing_by
  · exact Nat.log_lt_self b h
  · have hb : 0 < b ^ Nat.log b n := by
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · subst hb0; simp [Nat.log_zero_left]
      · exact Nat.pow_pos hbpos
    exact lt_of_lt_of_le (Nat.mod_lt _ hb) (Nat.pow_log_le_self b h)

/-- **Goodstein sequence** seeded at `m`: `goodsteinSeq m k = G k`. `G 0 = m`; `G (k+1)`
bumps the hereditary base `k+2 ↦ k+3` in `G k` and subtracts one (`0` a fixed point, as
`bump b 0 = 0` and `0 - 1 = 0`). Verbatim from `Defs.lean:46`. -/
def goodsteinSeq (m : ℕ) : ℕ → ℕ
  | 0 => m
  | k + 1 => bump (base k) (goodsteinSeq m k) - 1

end GoodsteinPA
