/-
# B-1 CRACK — the 12 `native_decide` base cases, kernel-only (lap 211)

`goodsteinLength_base_cases` (src/GoodsteinPA/Domination.lean:3053) currently pays 12
`native_decide` calls (`Lean.ofReduceBool`), the heaviest a 65551-step forward pass (M = 15).

**The collapse**: `le_bump` means the sequence drops by AT MOST 1 per step, so a checkpoint
value `v` at step `k` certifies `goodsteinLength M ≥ k + v` (`glen_ge_of_seq_value` below).
The needed bound `2^{M+1}+M ≤ 65551` is reached by step k ≤ 4 for every seed 4 ≤ M < 16
(values ≤ 326593). The checkpoint value is computed IN THE KERNEL by `gvalF`, a fuel-based
structural clone of the forward evaluator (`bump` is WF-recursion → kernel-stuck; `bumpF` with
fuel = n is structural; mathlib's `Nat.log` is already structural/kernel-reducible).

`base_cases_kernel` below = the VERBATIM statement of `goodsteinLength_base_cases`, proven on
`[propext, Classical.choice, Quot.sound]` — NO `Lean.ofReduceBool`. Compiles in seconds.

NEXT (mechanical, grind-legal): swap the proof body of `goodsteinLength_base_cases` in
Domination.lean to this route (statement FROZEN — swap satisfies it verbatim); the helper
defs/lemmas move in above it. That removes ofReduceBool from the growth headline's axiom set.
-/
import GoodsteinPA.Domination
open GoodsteinPA GoodsteinPA.Dom

example : Nat.log 3 100 = 4 := rfl  -- kernel-reducibility of Nat.log

/-- Fuel-based structural clone of `bump` (kernel-reducible). `fuel ≥ n` suffices. -/
def bumpF : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, b, n =>
    if n = 0 then 0
    else
      n / b ^ Nat.log b n * (b + 1) ^ bumpF fuel b (Nat.log b n)
        + bumpF fuel b (n % b ^ Nat.log b n)

theorem bumpF_eq : ∀ fuel n, n ≤ fuel → ∀ b, bumpF fuel b n = bump b n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn b
    have hn0 : n = 0 := by omega
    subst hn0
    rw [bumpF, bump]
    simp
  | succ fuel ih =>
    intro n hn b
    rw [bumpF, bump]
    by_cases h0 : n = 0
    · simp [h0]
    · rw [dif_neg h0, if_neg h0]
      have hlog : Nat.log b n ≤ fuel := by
        have := Nat.log_lt_self b h0; omega
      have hmod : n % b ^ Nat.log b n ≤ fuel := by
        have hb : 0 < b ^ Nat.log b n := by
          rcases Nat.eq_zero_or_pos b with hb0 | hbpos
          · subst hb0; simp [Nat.log_zero_left]
          · exact Nat.pow_pos hbpos
        have := Nat.mod_lt n hb
        have := Nat.pow_log_le_self b h0
        omega
      rw [ih _ hlog, ih _ hmod]

/-- Kernel-reducible forward Goodstein evaluator: value after `s` more steps from `(k, v)`. -/
def gvalF : ℕ → ℕ → ℕ → ℕ
  | _, v, 0 => v
  | k, v, s + 1 => gvalF (k + 1) (bumpF v (base k) v - 1) s

theorem gvalF_goodstein (M : ℕ) : ∀ s k, gvalF k (goodsteinSeq M k) s = goodsteinSeq M (k + s) := by
  intro s
  induction s with
  | zero => intro k; rfl
  | succ s ih =>
    intro k
    rw [gvalF, bumpF_eq _ _ le_rfl]
    have hstep : bump (base k) (goodsteinSeq M k) - 1 = goodsteinSeq M (k + 1) := rfl
    rw [hstep, ih (k + 1)]
    congr 1; omega

/-- Zero is absorbing for the Goodstein sequence. -/
theorem goodsteinSeq_zero_absorb (M : ℕ) {n : ℕ} (h : goodsteinSeq M n = 0) :
    ∀ i, goodsteinSeq M (n + i) = 0 := by
  intro i
  induction i with
  | zero => exact h
  | succ i ih =>
    show bump (base (n + i)) (goodsteinSeq M (n + i)) - 1 = 0
    rw [ih, bump]; simp

/-- **Survival from any checkpoint**: the sequence drops by at most 1 per step, so a value `v`
at step `k` certifies `goodsteinLength M ≥ k + v`. -/
theorem glen_ge_of_seq_value {M k v : ℕ} (hv : 1 ≤ v) (h : goodsteinSeq M k = v) :
    k + v ≤ goodsteinLength M := by
  have hsub : ∀ j, v - j ≤ goodsteinSeq M (k + j) := by
    intro j
    induction j with
    | zero => rw [Nat.add_zero, h]; omega
    | succ j ih =>
      have hb : goodsteinSeq M (k + j) ≤ bump (base (k + j)) (goodsteinSeq M (k + j)) :=
        le_bump (base (k + j)) (Nat.le_add_left 2 _) _
      have : goodsteinSeq M (k + (j + 1)) = bump (base (k + j)) (goodsteinSeq M (k + j)) - 1 := by
        rw [show k + (j + 1) = (k + j) + 1 from by omega]; rfl
      omega
  rw [goodsteinLength, Nat.le_find_iff]
  intro n hn hzero
  rcases Nat.lt_or_ge n k with hnk | hnk
  · have := goodsteinSeq_zero_absorb M hzero (k - n)
    rw [show n + (k - n) = k from by omega, h] at this; omega
  · have := hsub (n - k)
    rw [show k + (n - k) = n from by omega, hzero] at this; omega

-- the 12 base cases, kernel-only
theorem base_cases_kernel (M : ℕ) (h4 : 4 ≤ M) (h16 : M < 16) :
    2 ^ (M + 1) + M ≤ goodsteinLength M := by
  have hM : M = 4 ∨ M = 5 ∨ M = 6 ∨ M = 7 ∨ M = 8 ∨ M = 9 ∨ M = 10 ∨ M = 11 ∨ M = 12 ∨
      M = 13 ∨ M = 14 ∨ M = 15 := by omega
  have key : ∀ (m k v : ℕ), 1 ≤ v → gvalF 0 m k = v → 2 ^ (m + 1) + m ≤ k + v →
      2 ^ (m + 1) + m ≤ goodsteinLength m := by
    intro m k v hv hval hle
    have := gvalF_goodstein m k 0
    rw [Nat.zero_add] at this
    exact le_trans hle (glen_ge_of_seq_value hv (by rw [← this]; exact hval))
  rcases hM with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
  · exact key 4 2 41 (by omega) (by decide) (by norm_num)
  · exact key 5 2 255 (by omega) (by decide) (by norm_num)
  · exact key 6 2 257 (by omega) (by decide) (by norm_num)
  · exact key 7 3 3127 (by omega) (by decide) (by norm_num)
  · exact key 8 2 553 (by omega) (by decide) (by norm_num)
  · exact key 9 3 9842 (by omega) (by decide) (by norm_num)
  · exact key 10 3 15625 (by omega) (by decide) (by norm_num)
  · exact key 11 3 15627 (by omega) (by decide) (by norm_num)
  · exact key 12 3 15685 (by omega) (by decide) (by norm_num)
  · exact key 13 4 280711 (by omega) (by decide) (by norm_num)
  · exact key 14 4 326591 (by omega) (by decide) (by norm_num)
  · exact key 15 4 326593 (by omega) (by decide) (by norm_num)

#print axioms base_cases_kernel
