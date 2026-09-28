/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import PAComparator.PH.Support.Statement
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# The Paris–Harrington principle is true but unprovable in PA — comparator CHALLENGE

**The audit surface** is this file plus `Support/Statement.lean`, which re-declares the
development's definitions verbatim under their own names:

* `RelLarge H` — `H` is relatively large: its least element is at most `H.card`.
* `Homog c H` — every `e`-subset of `{1, …, N}` inside `H` gets one colour under `c`.
* `PH e r k N` — every `r`-colouring of the `e`-subsets of `{1, …, N}` has a relatively large
  homogeneous `H ⊆ {1, …, N}` with `k ≤ |H|` (Paris–Harrington 1977).
* `PHx x N` — `PH` with the parameters packed as `x = ⟪e, ⟪r, k⟫⟫` (`Nat.unpair`).

**The statements.**
* `ph_true` — for all `e r k` some `N` has `PH e r k N` (true in ℕ).
* `pa_not_proves_ph` — for every Σ₁ formula `φ(x, N)` defining `PHx` pointwise in ℕ, Peano
  Arithmetic does not prove `∀ x, ∃ N, φ(x, N)`.
* `exists_sigma1_ph_def` — anti-vacuity: such a `φ` exists.

Bound variables of `φ`: `#0 = N` (the inner `∃`), `#1 = x` (the outer `∀`), hence `![N, x]`.

Trust base: Mathlib + Foundation.  Stated with `sorry`; `Solution.lean` supplies the proofs.
-/

set_option warningAsError false

open FFL FFL.FirstOrder

namespace GoodsteinPA.PH

theorem pa_not_proves_ph
    (φ : Semisentence ℒₒᵣ 2) (hφ : Bounding.Hierarchy ℬ[<, ℒₒᵣ] 𝚺 1 φ)
    (hdef : ∀ x N : ℕ, (ℕ ⊧/![N, x] φ) ↔ PHx x N) :
    𝗣𝗔 ⊬ ↑(∀¹ ∃¹ φ : Sentence ℒₒᵣ) := sorry

theorem exists_sigma1_ph_def :
    ∃ φ : Semisentence ℒₒᵣ 2, Bounding.Hierarchy ℬ[<, ℒₒᵣ] 𝚺 1 φ ∧
      ∀ x N : ℕ, (ℕ ⊧/![N, x] φ) ↔ PHx x N := sorry

theorem ph_true (e r k : ℕ) : ∃ N, PH e r k N := sorry

end GoodsteinPA.PH
