import GoodsteinPA.EwIter

/-!
# lap-9 gate-composition probe — the reduction's `osucc` +1 is the irreducible obstruction

Kernel-grounded sharpening of the lap-8 escalation (`REBUILD-Z-LAP8-VERDICT.md` §2).

The reduction `cutReduceAllAuxRunning_Zf2` synthesizes a fresh node at `osucc (α + γ)` over the
composed slot `g ∘ f`; the `Zef2` gate on that node is `ewN (osucc (α + γ)) ≤ (g ∘ f) 0 = g (f 0)`.
By the banked `ewN_osucc_add_le` this is implied by (and, in the saturating case, equivalent to)

    ewN α + ewN γ + 1 ≤ g (f 0).

The gates the derivation carries are `ewN α ≤ g 0` (∀-family, ∀-side base `g`) and `ewN γ ≤ f 0`
(∃-side, base `f`).  The lap-8 verdict asked: does adding an `(f.1)-class` hypothesis (`EwF1`/`EwF2`)
close it?  **This file settles that in the kernel: NO.**

Two facts, both `#print axioms`-clean:

* `noOsucc_closes` — if the fresh node were at the *additive* norm `ewN α + ewN γ` (NO `osucc`
  `+1`), then `StrictMono g` ALONE closes the gate: `a ≤ g 0 → b ≤ f 0 → a + b ≤ g (f 0)`.
  (Strict monotonicity gives `g (f 0) ≥ g 0 + f 0` — exactly the additive budget.)

* `osucc_plus_one_refutes` — WITH the `osucc` `+1`, the gate is refuted by a concrete pair of
  `EwF1` (hence also mono/inflationary) slots: `g 0 + f 0 + 1 > g (f 0)` while both input gates
  hold with equality.  So no `(f.1)-class` hypothesis on `f`/`g` alone can discharge the pin
  as-stated — the obstruction is the successor step's `+1`, not a missing growth bound.

**Conclusion for the judge.**  Pins 1–2 do not re-thread over `Zef2` with the output ordinal
`osucc (α + γ)` and slot `g ∘ f`, for ANY `(f.1)-class` hypotheses.  The fix is statement-level and
must remove the `+1` slack deficit — either (a) an output ordinal whose `ewN` is exactly additive
(natural-sum shape; `Ordinal.nadd` was deleted at v4.31 so this is ~bespoke), or (b) a gate that
absorbs the norm into the slot *argument* (`f (ewN α + ·)`, the genuine E–W design) rather than
comparing to the fixed base `f 0`.  Architect-owned.
-/

namespace GoodsteinPA.OperatorZeh

open GoodsteinPA.FastGrowing

/-- A strictly monotone `g : ℕ → ℕ` grows by at least one per step: `g 0 + k ≤ g k`. -/
theorem strictMono_base_add_le {g : ℕ → ℕ} (hg : StrictMono g) : ∀ k, g 0 + k ≤ g k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : g k + 1 ≤ g (k + 1) := hg (Nat.lt_succ_self k)
      omega

/-- **Claim A (no `osucc`).**  If the reduction's fresh node sat at the additive norm
`ewN α + ewN γ` (no successor `+1`), `StrictMono g` alone closes the composed-slot gate. -/
theorem noOsucc_closes {f g : ℕ → ℕ} (hg : StrictMono g) {a b : ℕ}
    (ha : a ≤ g 0) (hb : b ≤ f 0) : a + b ≤ g (f 0) := by
  have := strictMono_base_add_le hg (f 0)
  omega

/-- The concrete `∃`-side slot for the refutation: `f m = 2 m + 1` (an `EwF1` slot; `f 0 = 1`). -/
def fBad : ℕ → ℕ := fun m => 2 * m + 1

/-- The concrete `∀`-side slot: `g 0 = 2`, `g m = 2 m + 1` for `m ≥ 1` (an `EwF1` slot with a
minimal step `g 0 → g 1`, so `g (f 0) = g 1 = 3 = g 0 + f 0`). -/
def gBad : ℕ → ℕ := fun m => if m = 0 then 2 else 2 * m + 1

theorem fBad_EwF1 : EwF1 fBad := by
  constructor
  · intro a b hab; simp only [fBad]; omega
  · intro m; simp only [fBad]; omega

theorem gBad_EwF1 : EwF1 gBad := by
  constructor
  · intro a b hab
    unfold gBad
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · have hb : b ≠ 0 := by omega
      rw [if_pos rfl, if_neg hb]; omega
    · have ha' : a ≠ 0 := by omega
      have hb : b ≠ 0 := by omega
      rw [if_neg ha', if_neg hb]; omega
  · intro m; unfold gBad
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [if_pos rfl]; omega
    · rw [if_neg (by omega : m ≠ 0)]

/-- **Claim B (with `osucc`).**  The concrete `EwF1` slots refute the gate `a + b + 1 ≤ g (f 0)`
even though both input gates hold with equality: here `g 0 = 2`, `f 0 = 1`, `g (f 0) = 3`, so
`a + b + 1 = 2 + 1 + 1 = 4 > 3`.  No `(f.1)-class` hypothesis recovers the successor `+1`. -/
theorem osucc_plus_one_refutes :
    ∃ (f g : ℕ → ℕ), EwF1 f ∧ EwF1 g ∧ ∃ a b : ℕ,
      a ≤ g 0 ∧ b ≤ f 0 ∧ ¬ (a + b + 1 ≤ g (f 0)) := by
  refine ⟨fBad, gBad, fBad_EwF1, gBad_EwF1, 2, 1, ?_, ?_, ?_⟩
  · simp [gBad]
  · simp [fBad]
  · simp only [fBad, gBad]; norm_num

end GoodsteinPA.OperatorZeh

-- Axiom audit (kernel-verified 2026-07-02, lap-9):
--   noOsucc_closes        depends on [propext, Quot.sound]
--   osucc_plus_one_refutes depends on [propext, Classical.choice, Quot.sound]
-- Both sorryAx-free / no custom axioms: the refutation is real.
