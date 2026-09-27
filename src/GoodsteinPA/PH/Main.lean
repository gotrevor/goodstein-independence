/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinPA.PH.Independence
import GoodsteinPA.PH.Computable

/-!
# PA does not prove the Paris–Harrington principle (stage 3 headline)

The two statements below are RATIFIED (Astra, 2026-09-26, in Trevor's place).  Their statements
are frozen: do not weaken, generalise, or re-state them.  The treadmill's job is to discharge the
`sorry`s; see `PH-TREADMILL.md`.

This file is deliberately not imported by `GoodsteinPA.lean` until it is sorry-free (the main lib
builds warnings-as-errors).  Check it with `lake env lean src/GoodsteinPA/PH/Main.lean`.
-/

namespace GoodsteinPA.PH

open LO LO.FirstOrder

/-- **PA does not prove Paris–Harrington**: for every Σ₁ `φ` defining `PHx` pointwise in ℕ, PA does
not prove `∀ x, ∃ N, φ(x, N)`. -/
theorem pa_not_proves_ph
    (φ : Semisentence ℒₒᵣ 2) (hφ : Arithmetic.Hierarchy 𝚺 1 φ)
    (hdef : ∀ x N : ℕ, (ℕ ⊧/![N, x] φ) ↔ PHx x N) :
    𝗣𝗔 ⊬ ↑(∀⁰ ∃⁰ φ : Sentence ℒₒᵣ) := sorry

/-- **Anti-vacuity**: some Σ₁ formula defines `PHx` pointwise in ℕ. -/
theorem exists_sigma1_ph_def :
    ∃ φ : Semisentence ℒₒᵣ 2, Arithmetic.Hierarchy 𝚺 1 φ ∧
      ∀ x N : ℕ, (ℕ ⊧/![N, x] φ) ↔ PHx x N := exists_sigma1_PHx_def

end GoodsteinPA.PH
