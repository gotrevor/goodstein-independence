# E — JUDGE validation of SPIKE-W3 (Ren, 2026-07-02)

> Host-side judge pass on the W3 spike (`83e4bca`), per the don't-trust-box-handoffs rule.
> Scope: independent re-verification + one architect-level statement catch. **No `.lean` edits here**
> (the W4 spike box is live in this working tree); the corrected exit statement below is the binding
> input to the W3 grind's step (1).

## 1. Verdict RATIFIED — independently re-verified

- `lake env lean wip/SpikeW3Embedding.lean` → **exit 0**, warnings = the disclosed case-lemma sorries
  only; in-file `#print axioms GoodsteinPA.SpikeW3.budgetedEmbedding` →
  `[propext, sorryAx, Classical.choice, Quot.sound]`. **No new `axiom` declarations.** Matches the
  box's report exactly.
- Commit `83e4bca` scope: the spike file + verdict only. LOCK files, `DIRECTION.md`, calculus files
  untouched. Assignment discipline held (skeleton + verdict + stop).
- The finding itself (the ω-rule case cannot consume `∀branch.∃budgets`; uniformity must be
  structural) is **correct and correctly classified as an amendment, not a wall** — the
  probe-consistency argument (esp. `inductionLeaf_allOmegaFromStep_someK_probe`'s `∃ k … max k n`
  hypothesis) is genuine corroboration. **T-W3 does not fire.** PASS stands.

## 2. The catch: the verdict's recommended signature does not implement its own prose note

The verdict's "Recommended amended master statement" hoists `α, e` structural but keeps
`ZekdSomeK` (= `∃ K, …`) **inside** `∀ env`:

```lean
∃ (c d₀ : ℕ) (α e : ONote), α.NF ∧ e.NF ∧ ∀ env, ZekdSomeK α e d₀ c (Γ.image …)
```

Its own Notes then (correctly) say the *base index `K` must be structural too*. The signature as
displayed does not deliver that — and the gap re-opens the SAME `∀∃`-vs-`∃∀` failure one level down:
in the `all` case the IH is instantiated per ω-branch at the **shifted assignment** `env' = n :>ₙ env`,
so each branch yields an **opaque per-branch `K_n`** (the `∃K` sits under `∀env`, and `env` varies
with the branch). `ZekdSomeK.allω` needs `∃K.∀n` at running index `max K n`; opaque `K_n` admit no
uniform base (`Zekd.mono_k` raises a derivation's index, it cannot cap `K_n`). The statement would
elaborate — and the `all` case lemma would be **unprovable**, discovered mid-grind.

## 3. The corrected W3 exit statement (binding for grind step (1)) — the Towsner §16 shape

Expose the env↦index dependence as a **hypothesis** (the index dominates the assignment), instead of
hiding it in `∃K`. Then the branch's contribution is *literally* the running index, by max-algebra:

```lean
theorem budgetedEmbedding {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (d : Derivation2 (𝗣𝗔 : Schema ℒₒᵣ) Γ) :
    ∃ (c d₀ K₀ : ℕ) (α e : ONote), α.NF ∧ e.NF ∧
      ∀ (K : ℕ) (env : ℕ → ℕ), (∀ i, env i ≤ K) →
        ZekdProv α e (max K₀ K) d₀ c (Γ.image (fun φ => Embedding.asg env ▹ φ))
```

Everything is structural except the explicit, *hypothesis-controlled* `K`. Why this composes where
the `∃K` form cannot — the `all` case, checked by hand:

- Given `env ≤ K` (pointwise). Branch `n`: `env' = n :>ₙ env` is dominated by `max K n`.
- IH at `(max K n, env')` → `ZekdProv α e (max K₀ (max K n)) d₀ c (premise-image)`.
- `max K₀ (max K n) = max (max K₀ K) n` — i.e. **base `B := max K₀ K`, running index `max B n`**,
  which is *exactly* `ZekdSomeK.allω`'s demanded premise shape, with the constant family `β n = α`
  (uniform `< osucc α`, NF) and the single structural `e`. The rule fires; the node concludes at
  base `B = max K₀ K` — the master's own conclusion shape. **No quantifier swap needed anywhere.**
- `exs` stays fine: the witness value `val (asg env ▹ t)` is polynomial in `K` with
  structure-determined coefficients, and structural `(e, d₀)` dominate any fixed-term polynomial via
  the witness bound `≤ hardy e (max K₀ K + d₀)` (the banked `closedTerm_witnessBound_of_budget` /
  `embedding_closedTermExI_someK_probe` shape).
- **Headline instantiation is vacuous as promised**: `γ` closed → take `env := fun _ => 0`, `K := 0`
  → `ZekdProv α e K₀ d₀ c {γ}`, all budgets structural. The verdict's `BudgetedEmbeds`/someK form is
  recoverable as a trivial corollary (weaken `ZekdProv → ∃K` form), so nothing downstream breaks.

Caveat, stated honestly: this composition is hand-checked (max-algebra + rule signatures), not yet
machine-checked — the W3 grind's step (1) is to re-state the skeleton on this signature and re-run
the real-induction assembly BEFORE touching any case lemma. If the assembly elaborates, the
amendment cycle is closed; if it doesn't, that is judge-escalation material, not grind material.

## 4. Effect on the masterplan risk picture

- Hard bet #1 (global embedding shape) is now **type-level de-risked twice over**: the global
  induction elaborates, and the one located uniformity gap has a closed-form statement fix grounded
  in the exact leaf machinery that is already kernel-clean. W3 residual = the `EmbeddingBound`
  uniform-family port (`all` case) + the W1/W2 leaves it dispatches to. No estimate change.
- The catch itself is the process working as designed: two statement-level quantifier bugs have now
  been caught at statement time (spike + judge), each of which would otherwise have surfaced ~10
  laps into a grind as a mysterious unprovable case.
