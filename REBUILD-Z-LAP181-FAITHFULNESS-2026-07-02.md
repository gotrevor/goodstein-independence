# REBUILD-Z LAP 181 — headline faithfulness cross-check (Aristotle NL→formalization)

> Sanctioned independent-formalization audit of the LOCKED headline audit surface
> (`Statement.peano_not_proves_goodstein`). Aristotle was handed the Kirby–Paris theorem
> **prose only** (`scratchpad/goodstein-headline-prose.txt`) — never the repo's Lean — and asked
> to formalize the STATEMENT (proof `sorry`). Job `f56c8524-1108-4e2c-bc69-07260fc4811b`,
> `Build: succeeded`, single intended `sorry`. Its `RequestProject/Goodstein.lean` was downloaded
> and adjudicated below. This is faithfulness hygiene, NOT calculus proof work — inside Scope-A.

## Verdict: **PASS — logically equivalent in essential content; no vacuity gap surfaced.**

The repo headline is `𝗣𝗔 ⊬ ↑goodsteinSentence` (Foundation/LO), non-vacuous because
`Encoding.lean`'s `goodsteinSentence` is the faithful encoding AND `Bridge.lean` proves
`(ℕ ⊨ goodsteinSentence) ↔ Goodstein-terminates` (LOCKED anchors).

Aristotle, independently, produced (Mathlib `FirstOrder.Language`, no `LO`):

```
theorem peano_not_proves_goodstein :
    ∃ φ : LA.Formula (Fin 3),
      DefinesGoodsteinGraph φ ∧ ¬ PAProves (goodsteinSentenceOf φ)
```

### Point-by-point equivalence

1. **Theory PA.** Aristotle's `peano = orderedSemiringAxioms ∪ inductionScheme` = PA⁻ (discretely
   ordered commutative semiring: assoc/comm `+`/`·`, distrib, nontriviality, linear order with 0
   least, `+`/`·` order-compatibility, existence of differences, discreteness) + the **full
   first-order induction schema** (one axiom per formula, with parameters). This is exactly the
   standard PA⁻+IND that Foundation's `𝗣𝗔` denotes. ✓ Match.

2. **Non-provability.** Repo uses syntactic `⊬`. Aristotle uses `PAProves σ := peano ⊨ᵇ σ`
   (semantic consequence over all models) and documents the justification: by **Gödel completeness**
   `T ⊢ σ ↔ T ⊨ᵇ σ` for first-order logic, so `¬ PAProves` faithfully renders `⊬`. Equivalent by a
   Mathlib-available theorem; a modelling choice, truth-preserving. ✓ (minor caveat: routes through
   completeness rather than a primitive `⊢`, because Mathlib packages no syntactic derivation
   relation — noted, not a discrepancy).

3. **Goodstein content (the anti-vacuity crux).** Aristotle's concrete `goodsteinSeq` on ℕ matches
   the standard definition exactly: `goodsteinSeq m 0 = m`; `goodsteinSeq m (k+1) =
   goodsteinStep (k+2) (goodsteinSeq m k)` (base at step `k` is `k+2`, i.e. step 0 in base 2);
   `goodsteinStep b n = bumpBase b (b+1) n - 1` (bump base `b→b+1`, then `−1`); `bumpBase` reads `n`
   in **hereditary** base `b` via `Nat.digits b n` and recursively rewrites each exponent
   (`bumpBaseFuel` on the digit position), re-evaluating in `b+1`. `GoodsteinTerminates := ∀ m, ∃ k,
   goodsteinSeq m k = 0`. This is a faithful arithmetization of Goodstein termination, identical in
   content to the repo's intended `goodsteinSentence`. ✓

4. **Anti-vacuity discipline.** `DefinesGoodsteinGraph φ := ∀ m k val, φ.Realize ℕ ![m,k,val] ↔
   goodsteinSeq m k = val` pins φ to the TRUE sequence in the standard model — the exact analogue of
   the repo's `Bridge.lean` anchor. Both bar the vacuous "PA fails to prove some unrelated
   independent sentence." ✓

### The one shape difference (faithful variant, not a discrepancy)

Aristotle wraps the claim existentially — `∃ φ, DefinesGoodsteinGraph φ ∧ ¬PAProves(…)` — because
Mathlib packages no Σ₁-arithmetization, so it asserts *some* graph-defining φ is independent rather
than exhibiting one. The repo instead **fixes one concrete `goodsteinSentence` and proves its
bridge**. The repo form is thus MORE specific/stronger (a named witness + proven equivalence) than
the existential; both assert the same Kirby–Paris independence and both guard vacuity by tying the
arithmetization to the real sequence. No divergence in mathematical claim.

## Bottom line

An outside formalizer, working from prose alone, independently reconstructed the Kirby–Paris
independence of Goodstein termination over PA⁻+full-induction, with the anti-vacuity anchor tying
the sentence to the concrete Goodstein sequence — the same statement the repo headline encodes.
This corroborates that `goodsteinSentence` + `Bridge.lean` faithfully capture the headline and that
`peano_not_proves_goodstein` is non-vacuous. No action required on the audit surface; the LOCKED
anchors stand. (Evidence: `scratchpad/ex/goodstein-headline-prose_aristotle/RequestProject/Goodstein.lean`.)
