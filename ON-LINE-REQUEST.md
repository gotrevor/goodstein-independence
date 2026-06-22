# ON-LINE-REQUEST — Towsner §17–§19: how the numeric index `k` / norm `τ` threads through cut-elimination

**Filed:** 2026-06-22 (lap 6). **Asker:** box (offline). **Unblocks:** completing the witness-bounded
cut-elimination for `Zᵏ` (`wip/BoundedZinfty.lean`) — the step-1 keystone of the connecting spine.

## Context
We built the witness-bounded `Z_∞` calculus `Zᵏ ⊢^{α}_{k,c}` over real `ℒₒᵣ` syntax (ONote-indexed),
with Towsner's §15 side conditions: truth-atom rule needs `τ(α) < k` (our `norm α < k`), `∃`-rule needs
witness `v ≤ h_α(k)`. The §19.2–19.5 layer (inversions + ∧/∨ cut-reduction) is done and axiom-clean.
The lower bound (Thm 17.1) is done and consumes a *cut-free* `Zᵏ`-derivation whose rules satisfy
`norm < k`. So **cut-elimination must output a derivation still satisfying `norm < k`.**

## The precise question
Cut-elimination grows the ordinal bound, and **`norm`/`τ` is NOT preserved by ordinal addition**:
machine-checked, `norm ω = 1` but `norm (ω + ω) = norm (ω·2) = 2` (addition merges CNF coefficients of
equal-exponent terms). The `ω^α` blow-up of §19.7 is fine (`norm(ω^α) = max(norm α, 1)`, coefficient
stays 1), but the §19.6 ∀/∃ reduction combines the ∀-family bound `α` with the ∃-side bound `γ` by
*addition*, bumping `norm`.

In **Towsner, *Goodstein's Theorem, ε₀, and Unprovability*** (`papers/towsner-…pdf`), §17–§19:

1. **What exactly is the `(α, k)` bound on the cut-elimination output?** Does `k` stay FIXED through
   the whole cut-elimination, or is it re-chosen / increased? I.e. is the theorem
   "`⊢^{α}_{k, c+1} ⟹ ⊢^{ω^α}_{k, c}`" (same `k`) or "`⟹ ⊢^{ω^α}_{k', c}`" for some `k' ≥ k`?

2. **Where precisely does the `τ(·) < k` / `τ(·) < k'` condition appear** — on every rule's ordinal,
   only on the True-rule and `∃`-rule, or as a global invariant? (Our calculus currently puts
   `norm β < k` on `weak`/`∃`/`∀`/cut premises, matching the lower-bound needs — is that Towsner's, or
   does he attach `τ < k` only to the truth axiom + existential witness?)

3. **How is `τ` of the cut-elimination output bounded?** Specifically, in the §19.6 ∀/∃ reduction, what
   is the ordinal bound of the conclusion in terms of the ∀-family bound and the ∃-side bound, and how
   does Towsner show its `τ` stays below the relevant `k`? (Natural/Hessenberg sum does NOT help — it
   merges coefficients the same way ordinary `+` does. So either the bound is structured to avoid
   equal-exponent merges, or `k` is chosen large enough to absorb a bounded number of additive bumps,
   or `τ` is tracked differently.)

4. If helpful: the analogous bookkeeping in **Schwichtenberg–Wainer, *Proofs and Computations*, Ch. 4**
   (the bounding lemma for `PA_∞`) or **Buchholz–Wainer 1987** — how the Σ₁-witness bound `H_α(k)`
   relates to the cut-elimination ordinal growth and what plays the role of `k`.

A short paraphrase of Towsner's exact §19.6/§19.7 bound statement (with the `k`/`τ` conditions written
out) would unblock the parameter-style port directly. The PDF is on disk (`papers/`), so a careful
read of §17–§19 should answer 1–3 without external sources.

## Why it matters
We will NOT claim cut-elimination closed (and hence will NOT chain toward the headline) until this is
pinned down — otherwise the cut-free output might violate `norm < k` and the subformula bridge to the
lower bound `B` would silently fail. This is the one genuinely-unresolved design point in the otherwise
mechanical cut-elimination port.
