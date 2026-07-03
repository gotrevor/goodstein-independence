import GoodsteinPA.OperatorZef2

/-!
# 2b growth conversion — `ewIter` → `hardy` majorization (lap 207 start)

The route-(c) splice's LAST piece: dominate the read-off's master bound
`ewIter S γ (S (max m C))` by `fastGrowing o` at ONE fixed NF `o`, eventually.  Design
(PENDING_WORK lap-207 2b analysis):

* the naive Nlog-gated hardy ordinal-monotonicity is FALSE (coefficient `2^x` vs argument `x`);
  the banked `hardy_le_of_lt` gates on the LINEAR `norm`;
* so the majorization must pay the norm/log mismatch EXPLICITLY: the ball bound
  `Nlog β ≤ K` converts to `norm β < 2^(K+1)` (the bridge below), and the master induction
  keeps the argument pre-inflated past that;
* per level the two-fold branch composes by `hardy_add_comp` (EXACT when no absorption) and
  the ordinal assignment `g α ≈ h·ω^(1+α)` leaves room: `g β · 2 + corrections < g α`.

This file banks the majorization prerequisites, starting with THE bridge.
-/

namespace GoodsteinPA.HardyMajorization

open ONote GoodsteinPA.FastGrowing GoodsteinPA.OperatorZeh

/-- **The norm/Nlog bridge**: the linear norm is at most one binary order above the log-norm.
(Sharp shape: `norm ≤ 2^Nlog` FAILS at coefficient 5 — `clog 5 = 2`, `2^2 = 4 < 5`.) -/
theorem norm_lt_two_pow_Nlog : ∀ (β : ONote), norm β < 2 ^ (Nlog β + 1)
  | 0 => by simp [norm]
  | oadd e n a => by
      have he := norm_lt_two_pow_Nlog e
      have ha := norm_lt_two_pow_Nlog a
      have hn : (n : ℕ) < 2 ^ (clog (n : ℕ) + 1) := by
        have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ((n : ℕ) + 1)
        unfold clog
        omega
      simp only [norm_oadd, Nlog_oadd]
      have hpow_mono : ∀ {i j : ℕ}, i ≤ j → (2:ℕ) ^ i ≤ 2 ^ j :=
        fun h => Nat.pow_le_pow_right (by norm_num) h
      apply max_lt
      · exact lt_of_lt_of_le he
          (hpow_mono (by have := Nat.zero_le (clog (n : ℕ)); omega))
      apply max_lt
      · exact lt_of_lt_of_le hn
          (hpow_mono (by have := Nat.zero_le (Nlog e); omega))
      · exact lt_of_lt_of_le ha (hpow_mono (by omega))

/-- The ball-membership corollary the master induction consumes: a branch ordinal passing the
`Nlog β ≤ K` gate has linear norm `< 2^(K+1)`. -/
theorem norm_lt_of_Nlog_le {β : ONote} {K : ℕ} (h : Nlog β ≤ K) :
    norm β < 2 ^ (K + 1) :=
  lt_of_lt_of_le (norm_lt_two_pow_Nlog β)
    (Nat.pow_le_pow_right (by norm_num) (by omega))

#print axioms GoodsteinPA.HardyMajorization.norm_lt_two_pow_Nlog
#print axioms GoodsteinPA.HardyMajorization.norm_lt_of_Nlog_le

end GoodsteinPA.HardyMajorization
