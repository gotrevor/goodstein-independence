/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinPA.PH.Statement
import Mathlib.Combinatorics.Colex
import Mathlib.Computability.Primrec.List
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The Paris–Harrington property is primitive recursive

`PH e r k N` quantifies over colourings and subsets of `{1, …, N}`.  Encoding a subset by its
bitmask (`Nat.equivBitIndices`) and a colouring by the base-`r` digits of one number (digit `t` is
the colour of the subset with bitmask `t`) turns it into a formula with bounded quantifiers only
(`PHbits`), which Mathlib's `PrimrecRel.forall_lt` / `exists_lt` handle.
-/

namespace GoodsteinPA.PH

open Finset

/-! ### Base-`r` digit packing -/

/-- Pack a list of base-`r` digits (least significant first). -/
def pack (r : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + r * pack r ds

theorem digit_pack {r : ℕ} (hr : 0 < r) :
    ∀ (ds : List ℕ), (∀ d ∈ ds, d < r) → ∀ t, pack r ds / r ^ t % r = ds.getD t 0
  | [], _, t => by simp [pack]
  | d :: ds, hd, 0 => by
    simp only [pack, pow_zero, Nat.div_one, List.getD_cons_zero]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hd d (by simp))]
  | d :: ds, hd, t + 1 => by
    simp only [pack, List.getD_cons_succ]
    rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hr,
      Nat.div_eq_of_lt (hd d (by simp)), zero_add]
    exact digit_pack hr ds (fun x hx => hd x (by simp [hx])) t

theorem pack_lt {r : ℕ} (hr : 0 < r) :
    ∀ (ds : List ℕ), (∀ d ∈ ds, d < r) → pack r ds < r ^ ds.length
  | [], _ => by simp [pack]
  | d :: ds, hd => by
    have ih := pack_lt hr ds (fun x hx => hd x (by simp [hx]))
    have hd0 := hd d (by simp)
    simp only [pack, List.length_cons, pow_succ']
    calc d + r * pack r ds < r + r * pack r ds := by omega
      _ = r * (pack r ds + 1) := by ring
      _ ≤ r * r ^ ds.length := Nat.mul_le_mul_left r ih

/-! ### Bitmasks -/

/-- The finite set with bitmask `n`. -/
abbrev bits (n : ℕ) : Finset ℕ := Nat.equivBitIndices n

theorem mem_bits {n i : ℕ} : i ∈ bits n ↔ n.testBit i = true := by
  simp [bits, Nat.equivBitIndices, Nat.mem_bitIndices]

/-- The bitmask of a finite set. -/
abbrev code (s : Finset ℕ) : ℕ := Nat.equivBitIndices.symm s

@[simp] theorem bits_code (s : Finset ℕ) : bits (code s) = s := Nat.equivBitIndices.apply_symm_apply s
@[simp] theorem code_bits (n : ℕ) : code (bits n) = n := Nat.equivBitIndices.symm_apply_apply n

theorem lt_two_pow_iff {n B : ℕ} : n < 2 ^ B ↔ ∀ i ∈ bits n, i < B := by
  constructor
  · intro h i hi
    have := Nat.two_pow_le_of_mem_bitIndices (by simpa [bits, Nat.equivBitIndices] using hi)
    by_contra hc
    exact absurd (lt_of_le_of_lt (le_trans (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hc)) this) h)
      (lt_irrefl _)
  · intro h
    rw [← code_bits n]
    show ∑ i ∈ bits n, 2 ^ i < 2 ^ B
    calc ∑ i ∈ bits n, 2 ^ i ≤ ∑ i ∈ range B, 2 ^ i :=
          sum_le_sum_of_subset (fun i hi => mem_range.mpr (h i hi))
      _ < 2 ^ B := by rw [Nat.geomSum_eq (le_refl 2)]; omega

/-- Population count of the first `B` bits. -/
def pop (B n : ℕ) : ℕ := (List.range B).foldr (fun j acc => (if n.testBit j then 1 else 0) + acc) 0

theorem pop_eq_card {B n : ℕ} (h : n < 2 ^ B) : pop B n = (bits n).card := by
  have hsub : bits n = (range B).filter (fun j => n.testBit j = true) := by
    ext i; simp only [mem_filter, mem_range, mem_bits]
    exact ⟨fun hi => ⟨lt_two_pow_iff.mp h i (mem_bits.mpr hi), hi⟩, fun hi => hi.2⟩
  rw [hsub, card_filter, pop, ← List.sum_toFinset _ (List.nodup_range)]
  · simp [List.foldr_eq_sum?]
  all_goals sorry

end GoodsteinPA.PH
