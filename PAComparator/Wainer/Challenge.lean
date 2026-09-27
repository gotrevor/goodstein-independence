/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.SetTheory.Ordinal.Notation
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# Wainer's bound — comparator CHALLENGE (the audit surface)

**Wainer's bound** (the upper half of the Kreisel–Wainer classification of the PA-provably total
functions; Buchholz–Wainer 1987).  If Peano Arithmetic proves a Π₂ sentence `∀ m, ∃ N, φ(m, N)`
with `φ` a Σ₁ formula, then there is an ordinal notation `o` in Cantor normal form (so `o < ε₀`)
and a threshold `M` such that for every `m ≥ M` some witness `N ≤ f_o(m)` makes `φ(m, N)` true in
the standard model.  `f_o` is Mathlib's fast-growing hierarchy `ONote.fastGrowing`.

Bound variables of `φ`: `#0 = N` (the inner `∃`), `#1 = m` (the outer `∀`), hence `![N, m]`.

Every constant in the statement is from Mathlib or Foundation (the FormalizedFormalLogic library:
`𝗣𝗔`, `⊢`, `Hierarchy`, `Evalb`), so nothing is re-declared; the trust base is Mathlib +
Foundation.  Stated with `sorry`; `Solution.lean` supplies the development's proof.
-/

set_option warningAsError false

open LO LO.FirstOrder

namespace GoodsteinPA.Wainer

theorem pa_provable_pi2_eventually_witnessed_below_fastGrowing
    (φ : Semisentence ℒₒᵣ 2) (hφ : Arithmetic.Hierarchy 𝚺 1 φ)
    (h : 𝗣𝗔 ⊢ ↑(∀⁰ ∃⁰ φ : Sentence ℒₒᵣ)) :
    ∃ o : ONote, o.NF ∧ ∃ M : ℕ, ∀ m, M ≤ m →
      ∃ N ≤ ONote.fastGrowing o m, ℕ ⊧/![N, m] φ := sorry

end GoodsteinPA.Wainer
