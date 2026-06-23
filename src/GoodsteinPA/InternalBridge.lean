/-
# `InternalBridge.lean` — E-core(b) brick 6: the standard-model bridge (faithfulness)

The internal `ipow`/`ilog`/`ibump`/`igoodstein` were built inside an arbitrary `V ⊧ₘ* 𝗜𝚺₁`. For the
expedition's **anti-fraud** guarantee they must agree with the *audited* `Defs.bump`/`Defs.goodsteinSeq`
on the standard model `ℕ` (itself a model of `𝗜𝚺₁`). This file establishes that absoluteness:

* `ipow b n = b ^ n`              (over `ℕ`)
* `ilog b n = Nat.log b n`        (over `ℕ`)
* `ibump b n = Defs.bump b n`     (over `ℕ`, base `2 ≤ b` — the only case Goodstein uses)
* `igoodstein m k = goodsteinSeq m k`

so the `𝚺₁`-definable internal run is the genuine Goodstein process, not a look-alike.
-/
import GoodsteinPA.InternalGoodstein
import GoodsteinPA.Defs
import Mathlib.Data.Nat.Log

namespace GoodsteinPA.InternalPow

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- Over `ℕ`, the internal power is `Nat.pow`. -/
@[simp] lemma ipow_nat (b n : ℕ) : ipow b n = b ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [ipow_succ, ih, pow_succ]

/-- Over `ℕ`, the internal logarithm is `Nat.log`. (Foundation's scoped `≤` on `ℕ` is `=∨<`, so we
convert it to `Nat.le` via `LO.FirstOrder.Arithmetic.le_def`; the `<` underneath is already `Nat.lt`.) -/
@[simp] lemma ilog_nat (b n : ℕ) : ilog b n = Nat.log b n := by
  symm
  rw [ilog_graph]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hb, hn⟩ := h
    rw [LO.FirstOrder.Arithmetic.le_def] at hb
    rw [ipow_nat, ipow_nat, LO.FirstOrder.Arithmetic.le_def]
    exact ⟨Nat.eq_or_lt_of_le (Nat.pow_log_le_self b hn.ne'),
      Nat.lt_pow_succ_log_self (by omega) n⟩
  · rcases not_and_or.mp h with h1 | h1
    · rw [LO.FirstOrder.Arithmetic.le_def] at h1
      push_neg at h1
      exact Nat.log_of_left_le_one (by omega) n
    · have : n = 0 := by omega
      subst this; simp

end GoodsteinPA.InternalPow
