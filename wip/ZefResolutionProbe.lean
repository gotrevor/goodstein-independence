/-
# `ZefResolutionProbe` — the DECISIVE numeric experiment for REBUILD-Z resolution (2)

Companion to `REBUILD-Z-LAP2-FINDING-2026-07-02-fixed-stage-reduction-wall.md` (the lap-2
escalation) and this lap's finding.  The lap-2 finding localized pins 1–2 to ONE gap — the
principal-`exI` cut cannot lower the running-family output stage — and named resolution (2)
(a function-slot exI bound in the judgment, the faithful E–W shape) as the fix, but flagged it
"architect-level, reopens the judgment form."

**This probe settles resolution (2)'s CRUX numerically, in-kernel:** in the slot calculus, the
principal-`exI` cut re-slots the ∀-family member (slot `g`, relativized `rel1 g n`) and the
∃-side reduct (slot `f`) to ONE output slot, and the whole reduction closes iff that output slot
DOMINATES both.  The E–W table (Lemma 25) writes the update as `f∘g`, but with the pins' naming
(`g` = the inverted-∀ family slot, `f` = the ∃-side slot) the DOMINATING order is **`g∘f`**, not
`f∘g` — E–W's `f∘g` is `(¬C-slot)∘(C-slot)` = (∀-slot)∘(∃-slot) = `g∘f` in pin naming.

Two kernel facts, both `#print axioms`-clean:

1. **`reslot_fog_FAILS`** — the pins' literal `f∘g` output does NOT dominate the family member,
   even for slots that are monotone, inflationary, AND `NormControlled` at the SAME control:
   concrete `f = hardy ω` (minimal), `g = x²+2x+1` at `(ω, 0)`, witness `n = 1 ≤ f 0`, gives
   `(rel1 g n) 0 = g 1 = 4 > 3 = f (g 0) = (f∘g) 0`.  So a family witness overflows the `f∘g`
   bound — the naive resolution-2 with output `f∘g` is refuted.

2. **`reslot_gof_dominates`** — the corrected `g∘f` output DOES dominate BOTH premises, for ANY
   monotone + inflationary slots (which every `NormControlled` slot is): the family member's slot
   `rel1 g n` is `≤ g∘f` (given `n ≤ f 0`) and the ∃-side slot `f` is `≤ g∘f`.  So a slot
   calculus with output slot `g∘f` re-slots both cut premises with a plain `mono_f` — the gap the
   fixed-`hardy e m` bound could not cross closes.

Consequence for the architect: resolution (2) is VIABLE with arbitrary `NormControlled` slots
(no E–W `(f.1)/(f.2)` growth class needed for the REDUCTION step — only the composition ORDER
`g∘f`).  The `NormControlled (g∘f) e m` conjunct is still dischargeable
(`normControlled_comp_running` with the roles swapped).

Off the live build (`wip/`, not in a `lean_lib`); `lake env lean wip/ZefResolutionProbe.lean`.
-/
import GoodsteinPA.OperatorZeh

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.FastGrowing

/-! ## The concrete refuting pair for the `f∘g` order -/

/-- The ∃-side minimal slot: `f = hardy ω = fun x => 2x+1`. -/
private def fEx : ℕ → ℕ := fun x => 2 * x + 1
/-- The ∀-family slot: `g = x²+2x+1`, strictly super-affine, still `NormControlled` at `(ω,0)`. -/
private def gEx : ℕ → ℕ := fun x => x * x + 2 * x + 1

/-- Both slots are `NormControlled` at the headline control `ω` and stage `0`
(`hardy ω x = 2x+1 ≤ both`). -/
theorem fEx_normControlled : NormControlled fEx ONote.omega 0 := by
  intro x
  rw [show ONote.omega = oadd 1 1 0 from rfl, hardy_omega]
  simp only [fEx]; omega
theorem gEx_normControlled : NormControlled gEx ONote.omega 0 := by
  intro x
  rw [show ONote.omega = oadd 1 1 0 from rfl, hardy_omega]
  simp only [gEx]; omega

/-- **The `f∘g` output order is REFUTED.**  The ∀-family member `fam 1` carries the relativized
slot `rel1 g 1`, whose witness budget at `0` is `(rel1 g 1) 0 = g 1 = 4`.  The candidate output
slot `f∘g` bounds witnesses at `0` by `(f∘g) 0 = f (g 0) = f 1 = 3`.  Since `4 > 3`, `fam 1`'s
own witnesses do not fit under `f∘g` — the re-slot to `f∘g` is impossible.  (The witness `n = 1`
is legal: `n ≤ f 0 = 1`.) -/
theorem reslot_fog_FAILS :
    ∃ (f g : ℕ → ℕ) (n : ℕ),
      NormControlled f ONote.omega 0 ∧ NormControlled g ONote.omega 0 ∧
      n ≤ f 0 ∧ ¬ (rel1 g n 0 ≤ (f ∘ g) 0) := by
  refine ⟨fEx, gEx, 1, fEx_normControlled, gEx_normControlled, by simp [fEx], ?_⟩
  simp only [rel1, fEx, gEx, Function.comp]
  decide

/-! ## The `g∘f` output order dominates both premises (general slots) -/

/-- Every `NormControlled` slot is inflationary (`x ≤ f x`) — via `le_hardy`. -/
theorem normControlled_infl {f : ℕ → ℕ} {e : ONote} {m : ℕ}
    (hf : NormControlled f e m) : ∀ x, x ≤ f x :=
  fun x => le_trans (le_trans (le_max_right m x) (le_hardy e (max m x))) (hf x)

/-- **The ∀-family member re-slots to `g∘f`.**  For monotone `g` and inflationary `f`, and a
witness `n ≤ f 0`, the relativized family slot `rel1 g n` is pointwise `≤ g∘f`: `g (max n x) ≤
g (f x)` because `max n x ≤ f x` (`n ≤ f 0 ≤ f x`, `x ≤ f x`).  This is the domination the
fixed-`hardy e m` bound could NOT provide. -/
theorem reslot_gof_family {f g : ℕ → ℕ} (hg_mono : Monotone g)
    (hf_infl : ∀ x, x ≤ f x) (hf_mono : Monotone f) {n : ℕ} (hn : n ≤ f 0) :
    ∀ x, rel1 g n x ≤ (g ∘ f) x := by
  intro x
  simp only [rel1, Function.comp]
  refine hg_mono ?_
  rcases le_total n x with h | h
  · rw [max_eq_right h]; exact hf_infl x
  · rw [max_eq_left h]; exact le_trans hn (hf_mono (Nat.zero_le x))

/-- **The ∃-side reduct re-slots to `g∘f`.**  For inflationary `g`, the ∃-side slot `f` is
pointwise `≤ g∘f` (`f x ≤ g (f x)`). -/
theorem reslot_gof_exside {f g : ℕ → ℕ} (hg_infl : ∀ x, x ≤ g x) :
    ∀ x, f x ≤ (g ∘ f) x := fun x => hg_infl (f x)

/-- **The corrected reduction conjunct is dischargeable.**  `g∘f` is `NormControlled` at the
output control/stage — the `normControlled_comp_running` plumbing with the composition ORDER
swapped (outer = the ∀-family slot `g`, inner = the ∃-side slot `f`). -/
theorem gof_normControlled {f g : ℕ → ℕ} {e : ONote} {m₀ m : ℕ}
    (hf : NormControlled f e m₀) (hg : NormControlled g e m) :
    NormControlled (g ∘ f) e m :=
  normControlled_comp_running hf hg

end GoodsteinPA.OperatorZeh
