/-
# `DescentSlowdown.lean` — the slow-down → non-termination assembly (Rathjen Lemma 3.6, internal)

The **standalone** half of the `hbound` obligation (`DescentSemantic.no_min_descent_absurd_of_goodstein`).
Abstracting over the slowed-down code sequence `β : V → V` itself, this packages the three structural
facts of the Rathjen §3 construction —

* `β` is `𝚺₁`-definable,
* every `β k` is in normal form with `C(β k) ≤ k+1` (`iCanon (k+1)`),
* the codes strictly descend, `icmp (β (k+1)) (β k) = 0`,

— into exactly the data `hbound` needs: a seed `m₀` and a `𝚺₁` bound `b` dominating the internal
Goodstein run, via the proved internalized inequality (6) (`InternalONote.ineq6_step_internal`).

This does **not** depend on the M-internal extraction of `β` from the `Mlt`-descent (the remaining
SEAM): it is the reusable Lemma-3.6 engine. The bound is `b k = ievalNat (k+1) (β k) = T̂^{k+2}_ω(βₖ)`,
the seed `m₀ = b 0 = T̂²_ω(β₀)`, and `step` is one application of `ineq6_step_internal` per Goodstein
step (no well-foundedness — the finite Π₁ kernel). With `DescentArith.nonterminating_internal` this
gives the non-terminating run that contradicts the lifted `goodsteinSentence`.
-/
import GoodsteinPA.InternalGoodstein
import GoodsteinPA.InternalONote
import GoodsteinPA.DescentArith

namespace GoodsteinPA.DescentSlowdown

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open GoodsteinPA.InternalONote GoodsteinPA.InternalPow

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- **Slow-down → `hbound` data** (Rathjen Lemma 3.6, internalized, abstracted over `β`).
Given the slowed-down code sequence `β` (`𝚺₁`-definable, NF + `C(β k) ≤ k+1`, `icmp`-descending), the
internal Goodstein run seeded at `m₀ = T̂²_ω(β₀)` is dominated at every stage by the positive bound
`b k = T̂^{k+2}_ω(βₖ)`. The `step` is the proved `ineq6_step_internal`; `hpos` is `ievalNat_pos`
(a descending code is non-zero). -/
theorem hbound_of_slowdown {β : V → V}
    (hβ : 𝚺₁-Function₁ β)
    (hNF : ∀ k, isNF (β k))
    (hCanon : ∀ k, iCanon (k + 1) (β k))
    (hdesc : ∀ k, icmp (β (k + 1)) (β k) = 0) :
    ∃ (m₀ : V) (b : V → V), (𝚺₁-Function₁ b) ∧
      b 0 ≤ igoodstein m₀ 0 ∧
      (∀ k, b k ≤ igoodstein m₀ k → b (k + 1) ≤ igoodstein m₀ (k + 1)) ∧
      (∀ k, 0 < b k) := by
  haveI := hβ
  have hb : 𝚺₁-Function₁ (fun k : V => ievalNat (k + 1) (β k)) := by definability
  refine ⟨ievalNat (0 + 1) (β 0), fun k => ievalNat (k + 1) (β k), hb, ?_, ?_, ?_⟩
  · -- base: `b 0 = igoodstein (b 0) 0`
    simp [igoodstein_zero]
  · -- step: one Goodstein step preserves domination, via the internalized inequality (6)
    intro k hk
    have hk2 : k + 1 + 1 = k + 2 := by rw [add_assoc, one_add_one_eq_two]
    rw [igoodstein_succ]
    -- `hCanon (k+1) : iCanon (k+1+1) (β (k+1))`; reindex to `iCanon (k+2)`.
    have hck1 : iCanon (k + 2) (β (k + 1)) := by rw [← hk2]; exact hCanon (k + 1)
    have hstep := ineq6_step_internal (hNF k) (hNF (k + 1)) (hCanon k) hck1 (hdesc k) hk
    simpa only [hk2] using hstep
  · -- hpos: a descending code is non-zero, so its value is positive
    intro k
    have hβk0 : β k ≠ 0 := fun h => icmp_right_zero_ne_zero (β (k + 1)) (h ▸ hdesc k)
    exact ievalNat_pos (hNF k) hβk0

/-- **Slow-down → non-terminating internal Goodstein run** (the contradiction `hbound` feeds the
descent). Composes `hbound_of_slowdown` with `DescentArith.nonterminating_internal`: from the slowed
descent `β`, there is a seed `m₀` whose internal Goodstein run never reaches `0`. -/
theorem nonterminating_of_slowdown {β : V → V}
    (hβ : 𝚺₁-Function₁ β)
    (hNF : ∀ k, isNF (β k))
    (hCanon : ∀ k, iCanon (k + 1) (β k))
    (hdesc : ∀ k, icmp (β (k + 1)) (β k) = 0) :
    ∃ m₀ : V, ∀ k : V, 0 < igoodstein m₀ k := by
  obtain ⟨m₀, b, hb, base, step, hpos⟩ := hbound_of_slowdown hβ hNF hCanon hdesc
  exact ⟨m₀, DescentArith.nonterminating_internal (by definability) hb base step hpos⟩

end GoodsteinPA.DescentSlowdown
