import GoodsteinPA.EwIter

/-!
# Route-(c) gadget probe — the value-budget read-off's master bound (lap 206)

Mandated by the lap-206 DEEP REFLECTION (DIRECTION lap-206 block, step (1)): kernel-check the
S-iterate threading algebra BEFORE re-grinding `readoffTC_core`.  The design (PENDING_WORK
lap-206 top):

* master bound `BND V α := ewIter S α (S V)` — the banked norm-gated max-iterate applied to the
  combined step `S x := max (f x) (P x)` (`f` = the root slot, `P` = the φ-subterm value bound),
  seeded ONE `S` ahead of the running value budget `V`;
* the slot along the descent is always `rel1 f j` with `j ≤ V` (`rel1_rel1` collapses towers),
  so every calculus gate `Nlog β ≤ (slot) 0 = f j` yields `Nlog β ≤ S (S V)` — the ONLY gate
  shape the threading lemmas below consume.

Probed here (all sorry-free, `S` abstract monotone+inflationary):

* `T1_extract`   — a witness read at the current slot fits under the master bound;
* `T3_descent`   — THE decisive inequality: a premise at ordinal `β < α` with a bumped budget
  `V' ≤ S V` has its master bound absorbed by the node's (covers the trap descent `V' = max V k₀`,
  `k₀ ≤ P V`, the vacuous-`exI` bump `V' = max V (f j)`, and — at `V' = V` — the same-budget
  `andI`/`orI`/branch-0 descents);
* `T4_slot_read` — the running slot's 0-read is within the budget frame (`f j ≤ S V` for `j ≤ V`),
  which is what converts calculus gates/witness reads into `T1`/`T3` inputs.

VERDICT: the algebra CLOSES on the banked `ewIter` lemmas alone (`ewIter_lower`,
`ewIter_monotone`, `ewIter_infl`) — no new transfinite gadget is needed; `ewIter` itself serves,
applied to `S`.  The re-grind of `readoffTC_core` may proceed against this bound shape.
-/

namespace GoodsteinPA.ReadoffValueGadgetProbe

open ONote GoodsteinPA.OperatorZeh

variable {S : ℕ → ℕ}

/-- Seed inflation: `S V ≤ ewIter S α (S V)` — any value read at the current frame fits under
the master bound (with `T4_slot_read` this covers the tracked-`exI` extraction `n ≤ f j`). -/
theorem T1_extract (hS_infl : ∀ m, m ≤ S m) (α : ONote) (V : ℕ) :
    S V ≤ ewIter S α (S V) :=
  ewIter_infl hS_infl α (S V)

/-- One-step absorption at a nonzero ordinal: `S (S x) ≤ ewIter S β x` for `β ≠ 0`. -/
theorem SS_le_ewIter {β : ONote} (hβ : β ≠ 0) (x : ℕ) :
    S (S x) ≤ ewIter S β x := by
  have h0β : (0 : ONote) < β := by
    cases β with
    | zero => exact (hβ rfl).elim
    | oadd e n a => exact oadd_pos e n a
  have h := ewIter_lower (f := S) (β := 0) (α := β) (m := x) NF.zero h0β (Nat.zero_le _)
  simpa [ewIter_zero] using h

/-- **T3 — the decisive descent inequality.**  A premise node at ordinal `β < α` whose value
budget bumped to any `V' ≤ S V` (trap descent `max V k₀` with `k₀ ≤ P V ≤ S V`; vacuous-`exI`
bump `max V (f j) ≤ S V`; or unchanged `V' = V`) has its master bound absorbed by the node's
master bound.  Gate shape: the calculus's node condition at the premise is `Nlog β ≤ (slot) 0 =
f j'` with `j' ≤ V' ≤ S V`, hence `Nlog β ≤ S (S V)` — exactly the hypothesis here. -/
theorem T3_descent (hS_mono : Monotone S) (hS_infl : ∀ m, m ≤ S m)
    {β α : ONote} (hβNF : β.NF) (hβα : β < α)
    {V V' : ℕ} (hV' : V' ≤ S V)
    (hgate : Nlog β ≤ S (S V)) :
    ewIter S β (S V') ≤ ewIter S α (S V) := by
  -- a) raise the seed `S V' ≤ S (S V)`
  have ha : ewIter S β (S V') ≤ ewIter S β (S (S V)) :=
    ewIter_monotone hS_mono hS_infl β (hS_mono hV')
  -- b) `S (S V) ≤ ewIter S β (S V)`
  have hb : S (S V) ≤ ewIter S β (S V) := by
    by_cases hβ0 : β = 0
    · subst hβ0
      simp [ewIter_zero]
    · exact le_trans (hS_infl (S (S V))) (SS_le_ewIter hβ0 (S V))
  -- c) monotone composition + d) two-fold collapse at `β < α`
  have hc : ewIter S β (S (S V)) ≤ ewIter S β (ewIter S β (S V)) :=
    ewIter_monotone hS_mono hS_infl β hb
  have hd : ewIter S β (ewIter S β (S V)) ≤ ewIter S α (S V) :=
    ewIter_lower hβNF hβα (le_trans hgate (hS_mono (by omega)))
  exact le_trans ha (le_trans hc hd)

/-- **T4 — slot reads live in the budget frame.**  The running slot is `rel1 f j` with `j ≤ V`;
its 0-read `f j` is `≤ S V`, so calculus gates (`Nlog β ≤ f j`) convert to `T3`'s `hgate`
(via one more `S`-application) and `exI` witness reads convert to `T1`. -/
theorem T4_slot_read {f P : ℕ → ℕ} (hf_mono : Monotone f) {j V : ℕ} (hj : j ≤ V) :
    rel1 f j 0 ≤ max (f V) (P V) := by
  have : rel1 f j 0 = f j := by simp [rel1]
  rw [this]
  exact le_trans (hf_mono hj) (le_max_left _ _)

/-- The concrete step `S x := max (f x) (P x)` is monotone + inflationary from `f`'s
Monotone+inflationary and `P`'s Monotone — the read-off's standing slot hypotheses. -/
theorem S_max_mono_infl {f P : ℕ → ℕ} (hf_mono : Monotone f) (hf_infl : ∀ m, m ≤ f m)
    (hP_mono : Monotone P) :
    Monotone (fun x => max (f x) (P x)) ∧ ∀ m, m ≤ max (f m) (P m) :=
  ⟨fun _ _ h => max_le_max (hf_mono h) (hP_mono h),
   fun m => le_trans (hf_infl m) (le_max_left _ _)⟩

#print axioms GoodsteinPA.ReadoffValueGadgetProbe.T1_extract
#print axioms GoodsteinPA.ReadoffValueGadgetProbe.T3_descent
#print axioms GoodsteinPA.ReadoffValueGadgetProbe.T4_slot_read
#print axioms GoodsteinPA.ReadoffValueGadgetProbe.S_max_mono_infl

end GoodsteinPA.ReadoffValueGadgetProbe
