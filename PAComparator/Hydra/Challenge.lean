/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import PAComparator.Hydra.Support.Canonical
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# PA does not prove that the canonical hydra battle terminates — comparator CHALLENGE

**The audit surface** is this file plus `Support/{Basic,Ordinal,Canonical}.lean`, which re-declare
lean-gallery's definitions verbatim under their own names (inductives are generative):

* `Hydra` — a finite rooted tree; `leaf = node []` is a single head.
* `ord` — the Kirby–Paris ordinal, the natural sum `♯ ω^{ord c}` over the children, as a Cantor
  normal form (`insertTerm`, `sumTerms`).
* `canonStep n` — Hercules' move at turn `n`: descend along the first child of minimal `ord` to a
  head and chop it; a non-root chop regrows `n + 1` copies of the cut node one level up.
* `battle h k` — the hydra after `k` canonical moves from `h`, move `j` at turn `j`.
* `ofCode` — a bijection `ℕ ≃ Hydra` (`0 ↦ leaf`, `⟪a, b⟫ + 1 ↦ ofCode b` with child `ofCode a`).

**The statement.**  For every Σ₁ formula `φ(m, N)` that defines the battle pointwise in ℕ —
`ℕ ⊧ φ(m, N)` iff the canonical battle from hydra `m` is dead after `N` moves — Peano Arithmetic
does not prove `∀ m, ∃ N, φ(m, N)`, i.e. it cannot prove that the canonical battle always ends
(Kirby–Paris 1982, for this computable strategy).  That such a `φ` exists is proved separately
(`GoodsteinPA.Hydra.exists_sigma1_battle_def`, pinned in `scripts/AxiomCheck.lean`).

Trust base: Mathlib + Foundation.  Stated with `sorry`; `Solution.lean` supplies the proof.
-/

set_option warningAsError false

open LO LO.FirstOrder LeanGallery.Logic.Hydra

namespace GoodsteinPA.Hydra

theorem pa_not_proves_hydra
    (φ : Semisentence ℒₒᵣ 2) (hφ : Arithmetic.Hierarchy 𝚺 1 φ)
    (hdef : ∀ m N : ℕ, (ℕ ⊧/![N, m] φ) ↔ battle (ofCode m) N = Hydra.leaf) :
    𝗣𝗔 ⊬ ↑(∀⁰ ∃⁰ φ : Sentence ℒₒᵣ) := sorry

end GoodsteinPA.Hydra
