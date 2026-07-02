/-
# `Trap8Probe` — the EIGHTH statement trap: the diagonalizing `iterSlot` is NOT
ordinal-monotone, so the LOCKED pin-3 output slot `iterSlot f α` cannot be threaded
through the cut-elimination induction.

The pin (`cutElimPass_Zf`, judge-LOCKED lap-5 form) reads
    `Zef α e H f (c+1) Γ → … → ZefProv (collapse α) e H (iterSlot f α) c Γ`.
A structural induction on the derivation produces, at every sub-derivation of recorded
height `β < α` (the `weak`, `exI`, `allω`, `cut` premises), the IH
    `ZefProv (collapse β) e H (iterSlot f β) c …`,
because the motive keys the output slot to the node's height.  To re-assemble at the
PARENT node (output slot `iterSlot f α`) the ONLY available slot move is `Zef.mono_f`,
which RAISES a slot: it needs `∀ x, iterSlot f β x ≤ iterSlot f α x`.

**Kernel refutation below**: with `f = (·+1)` (monotone + inflationary), `β = ofNat 2`,
`α = ω = oadd 1 1 0` (both NF, `β < α`), we have `iterSlot f 2 0 = 3 > 2 = iterSlot f ω 0`.
So the `mono_f` premise the induction requires is FALSE.  Root cause: the diagonalizing
iterate (trap-7's fix) DIPS at the base of a limit — `iterSlot f ω 0` rides the
fundamental-sequence value `ω[0] = 1` (`iterSlot f ω 0 = iterSlot f 1 0 = f^[2] 0`), which
is *smaller* than a finite `β = 2` sitting below ω (`iterSlot f 2 0 = f^[3] 0`).  trap-7
fixed the `allω`-branch unboundedness (branch index rides a LARGE argument `max n x`); the
fix reintroduced a BASE-argument domination failure that bites at every node whose slot is
read near argument 0 (`weak` slot-lift; `exI`/`cut` witness at 0).

Same evidence grade as traps 6/7: kernel-localized + structurally forced (the slot algebra
offers only the one-directional `mono_f`; no auxiliary with a bare-`iterSlot f α` conclusion
can dodge it — the IH is pinned to `iterSlot f β` by the theorem's own motive).  NOT a
falsity proof of the full pin — an unprovable-as-stated obstruction with the wall
kernel-anchored, sufficient for a statement amendment under the mandate.

Read-only evidence artifact; do NOT wire into `src`.  Escalation:
`REBUILD-Z-TRAP8-2026-07-02.md`.
-/
import GoodsteinPA.OperatorZeh
open GoodsteinPA.OperatorZeh ONote
open GoodsteinPA.FastGrowing

namespace GoodsteinPA.OperatorZeh

/-- The witness slot: `f = (·+1)`, monotone + inflationary (both hypotheses the pin carries). -/
def ftest : ℕ → ℕ := fun n => n + 1

theorem ftest_mono : Monotone ftest := fun a b h => by simp only [ftest]; omega
theorem ftest_infl : ∀ x, x ≤ ftest x := fun x => by simp only [ftest]; omega

/-- The two decisive iterate values at argument 0 (kernel-computed). -/
theorem iterSlot_two_zero : iterSlot ftest 2 0 = 3 := by native_decide
theorem iterSlot_omega_zero : iterSlot ftest (oadd 1 1 0) 0 = 2 := by native_decide

/-- **The obstruction, kernel-anchored.**  The `mono_f`-lift the induction needs —
`∀ x, iterSlot ftest 2 x ≤ iterSlot ftest ω x` — is FALSE at `x = 0`:
`iterSlot ftest 2 0 = 3` but `iterSlot ftest ω 0 = 2`.  (`ω = oadd 1 1 0`; `2 < ω` in NF.) -/
theorem trap8_mono_f_lift_fails :
    ¬ (∀ x, iterSlot ftest 2 x ≤ iterSlot ftest (oadd 1 1 0) x) := by
  intro h
  have hx := h 0
  rw [iterSlot_two_zero, iterSlot_omega_zero] at hx
  omega

/-- Restated as non-monotonicity of `iterSlot f · 0` along the ordinals: a finite level below
ω STRICTLY exceeds ω itself at argument 0 — the exact fact that dooms the bare-`iterSlot f α`
output slot in every case with a `β < α` sub-derivation (`weak`/`exI`/`allω`/`cut`). -/
theorem trap8_dips_at_limit_base :
    iterSlot ftest (oadd 1 1 0) 0 < iterSlot ftest 2 0 := by
  rw [iterSlot_two_zero, iterSlot_omega_zero]; omega

end GoodsteinPA.OperatorZeh
