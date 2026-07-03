import GoodsteinPA.WainerLadder

/-!
# SERIES-2 Stage D-2 probe — the E–W-literal shift relativization `rel1'` : cost assessment

**Question (`REBUILD-Z-SERIES-2-ORDER-2026-07-03.md` Stage D-2).**  E–W Def 23's literal
relativization is the SHIFT `f[n] = f (n + ·)`; the repo's ratified `rel1 f n = f (max n ·)`.
The lap-192 trilemma named base-additivity `hg_base : ∀ k, g 0 + k ≤ g k` as destroyed by
`rel1` in nested ω-contexts (banked kernel refutation).  Would swapping `rel1 → rel1'` (the
shift) restore it, and at what cost?

**KERNEL ANSWERS (all `[propext, Classical.choice, Quot.sound]`, no `native_decide`):**

1. **`rel1'` preserves the EwLow triple** (`rel1'_monotone`/`rel1'_infl`/`rel1'_low`) — same
   as `rel1`.  No cost on the pass-threading side.

2. **`rel1'` does NOT preserve `hg_base`** (`rel1'_not_base : ` concrete counterexample).
   The four ratified hypotheses {Monotone, infl, `2m+1` floor, `hg_base`} do NOT imply
   `hg_base` for the shifted slot: `fBad` below satisfies all four, yet
   `rel1' fBad 1` violates base-additivity at `k = 2` (`fBad 1 + 2 = 102 > 101 = fBad 3` —
   a one-step jump at the shift origin that the base at `0` never sees).  **So the naive
   "swap `rel1 → rel1'` and keep `hg_base`" amendment does NOT re-close the pins' node
   gates: the `allω` branches' shifted slots lose the very property the swap was meant to
   rescue.**  This kernel-confirms the lap-192 review's parenthetical ("`rel1` max→+ ALONE is
   insufficient") in the sharpest form: it is insufficient even before the `ewIter` plateau
   enters.

3. **The property that DOES survive the shift is uniform step-additivity**
   `StepAdd f := ∀ m k, f m + k ≤ f (m + k)`:
   - `StepAdd → hg_base` trivially (`stepAdd_base`);
   - **`StepAdd` is closed under `rel1'`** (`stepAdd_rel1'`) — the shift is
     self-reproducing, so a `StepAdd`-based (f.1) class threads through nested ω-contexts
     with NO per-level loss;
   - **`StepAdd` is NOT closed under `rel1`** (`stepAdd_not_rel1`, kernel counterexample:
     `rel1 f 5` at `m = 0, k = 1` demands `f 5 + 1 ≤ f 5`) — the max-relativization is
     exactly what breaks it, consistent with the banked `hg_base` refutation;
   - **the CONCRETE root slot is `StepAdd`** (`ewRootSlot_stepAdd`) — so upgrading the pins'
     hypothesis `hg_base → StepAdd` costs nothing at the root instantiation.

**Blast radius (measured, prose).**  `rel1` occurs 88× in `OperatorZeh.lean`, 68× in
`OperatorZef2.lean`, 13× in `EwIter.lean`.  Decisively: **the `allω` constructors of `Zef`,
`Zef2` (and the probe clone `Zef2T`) BIND `rel1` structurally** (premise family
`dd : ∀ n, … (rel1 f n) …`) — `rel1` is NOT a hypothesis-slot that a lemma can re-instantiate;
swapping to `rel1'` is a NEW-INDUCTIVE change (a `Zef2'` clone) plus a re-proof of the full
lemma suite (`mono_f` via a `rel1'_mono` analog, `toZef` ✂, pins 1–2, `stepAllω`,
`allInv_Zef2`, `readoffD_aux`, `ewIter_rel1_le` → `ewIter_rel1'_le`, …).  Also note the small
ripple: the lap-195 branch-0 mechanism `rel1 f 0 = f` holds by `max 0 x = x`; its shift
analog `rel1' f 0 = f` holds by `zero_add` — both propositional, neither definitional, so
that mechanism carries over.
**Amendment cost verdict for the ruling**: `rel1 → rel1'` alone is POINTLESS (item 2); the
viable shift amendment is `rel1 → rel1'` TOGETHER WITH `hg_base → StepAdd` in the pins
(items 3a–3d make that package self-reproducing and concretely instantiable), at
new-inductive + full-suite re-proof cost.  Compare: the D-1 absorbing-norm amendment
(`ewN → Nlog`) dissolves the same node gate with NO constructor change and NO slot property —
strictly dominating on cost.  Stage D evidence therefore ranks: absorbing norm ≫ shift+StepAdd.

wip-only ruling input (SERIES-2 order Stage D-2 / ladder P2).  `src` untouched.
-/

namespace GoodsteinPA.Rel1ShiftProbe

open GoodsteinPA.OperatorZeh

/-- **The E–W-literal shift relativization** `f[n] = f (n + ·)` (E–W Def 23), the alternative
to the ratified `rel1 f n = f (max n ·)`. -/
def rel1' (f : ℕ → ℕ) (n : ℕ) : ℕ → ℕ := fun x => f (n + x)

/-! ## 1. The EwLow triple survives the shift -/

theorem rel1'_monotone {f : ℕ → ℕ} (hf : Monotone f) (n : ℕ) : Monotone (rel1' f n) :=
  fun _ _ h => hf (by omega)

theorem rel1'_infl {f : ℕ → ℕ} (_hmono : Monotone f) (hf : ∀ x, x ≤ f x) (n : ℕ) :
    ∀ x, x ≤ rel1' f n x :=
  fun x => le_trans (le_trans (by omega : x ≤ n + x) (hf (n + x))) (le_refl _)

theorem rel1'_low {f : ℕ → ℕ} (_hmono : Monotone f) (hlow : ∀ m, 2 * m + 1 ≤ f m) (n : ℕ) :
    ∀ m, 2 * m + 1 ≤ rel1' f n m :=
  fun m => le_trans (by omega : 2 * m + 1 ≤ 2 * (n + m) + 1) (hlow (n + m))

/-! ## 2. `hg_base` does NOT survive the shift — kernel counterexample -/

/-- The adversary: satisfies ALL FOUR ratified slot hypotheses, but jumps by `99` at step
`0 → 1` and then crawls (`+1`) for two steps — so the SHIFTED base at `1` (value `100`)
outruns `f (1 + k)` at `k = 2`. -/
def fBad : ℕ → ℕ
  | 0 => 1
  | 1 => 100
  | 2 => 101
  | 3 => 101
  | (n + 4) => 2 * n + 103

theorem fBad_monotone : Monotone fBad := by
  apply monotone_nat_of_le_succ
  intro n
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | (m + 4) => simp only [fBad]; omega

theorem fBad_infl : ∀ x, x ≤ fBad x := by
  intro x
  match x with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | (m + 4) => simp only [fBad]; omega

theorem fBad_low : ∀ m, 2 * m + 1 ≤ fBad m := by
  intro m
  match m with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | (k + 4) => simp only [fBad]; omega

theorem fBad_base : ∀ k, fBad 0 + k ≤ fBad k := by
  intro k
  match k with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | (m + 4) => simp only [fBad]; omega

/-- **The shift destroys `hg_base`**: `rel1' fBad 1` violates base-additivity at `k = 2`
(`100 + 2 ≤ 101` is false), although `fBad` satisfies Monotone + infl + `2m+1` floor +
`hg_base`.  So `rel1 → rel1'` alone does NOT rescue the pins' base-additivity. -/
theorem rel1'_not_base :
    ¬ (∀ k, rel1' fBad 1 0 + k ≤ rel1' fBad 1 k) := by
  intro h
  have := h 2
  simp [rel1', fBad] at this

/-! ## 3. The property that DOES survive: uniform step-additivity -/

/-- Uniform step-additivity — the E–W-faithful strengthening of `hg_base`. -/
def StepAdd (f : ℕ → ℕ) : Prop := ∀ m k, f m + k ≤ f (m + k)

theorem stepAdd_base {f : ℕ → ℕ} (h : StepAdd f) : ∀ k, f 0 + k ≤ f k := by
  intro k; simpa using h 0 k

/-- **`StepAdd` is closed under the shift** — the self-reproducing (f.1)-class for `rel1'`. -/
theorem stepAdd_rel1' {f : ℕ → ℕ} (h : StepAdd f) (n : ℕ) : StepAdd (rel1' f n) := by
  intro m k
  simpa [rel1', Nat.add_assoc] using h (n + m) k

/-- **`StepAdd` is NOT closed under the ratified `rel1`** (max-relativization): at `n = 5`,
`m = 0`, `k = 1` it demands `f 5 + 1 ≤ f 5`.  Witness `f = id` (which IS `StepAdd`). -/
theorem stepAdd_not_rel1 :
    ¬ (∀ f : ℕ → ℕ, StepAdd f → ∀ n, StepAdd (rel1 f n)) := by
  intro h
  have hid : StepAdd (fun x : ℕ => x) := fun m k => le_refl _
  have := h _ hid 5 0 1
  simp [rel1] at this

/-- **The concrete root slot is `StepAdd`** — upgrading the pins' `hg_base → StepAdd` costs
nothing at the root instantiation (`ewRootSlot e m x = 2·(x + hardy e (max m x)) + 3`). -/
theorem ewRootSlot_stepAdd (e : ONote) (m : ℕ) : StepAdd (ewRootSlot e m) := by
  intro x k
  have hr : GoodsteinPA.FastGrowing.hardy e (max m x)
      ≤ GoodsteinPA.FastGrowing.hardy e (max m (x + k)) :=
    GoodsteinPA.FastGrowing.hardy_monotone e (max_le_max (le_refl m) (by omega))
  simp only [ewRootSlot, rel1]
  omega

end GoodsteinPA.Rel1ShiftProbe
