/-
# `Zᵏ` — the witness-bounded `Z_∞` ω-rule calculus over real `ℒₒᵣ` syntax (step 1, Towsner §15)

The connecting spine (`ANALYSIS-2026-06-22-bounding-resolution.md` §"M4 scoping") needs ONE calculus
that the embedding (M4) lands in, cut-elimination (M5′) operates on, and whose cut-free fragment the
subformula bridge maps to the **done** lower bound `B` (`src/GoodsteinPA/LowerBound.lean`,
`lowerBound_hardy_selfcontained`).  `src/GoodsteinPA/Zinfty.lean` has the right rule shapes + a full
ε₀ cut-elimination but for the **unbounded** `(α,c)` calculus — the lap-4 finding showed that one is
off the headline path (no witness bound ⇒ the lower bound is false for it).

`Zᵏ` is that calculus, built **B-style** (`Prop`-valued, `ONote`-indexed, bound-as-parameter so there
are no `⨆`-suprema to represent in `ONote`) over Foundation's real `SyntacticFormula ℒₒᵣ`.  It adds to
`B` the two `(α,k)` side conditions Towsner §15 puts on the rules — the **truth-atom rule** (`τ α < k`)
and the **`∃`-witness bound** (`v ≤ h_α(k)`) — plus the connective/cut rules (`∧`,`∨`,`cut`) needed
because the embedding's cut formulas (PA induction instances) are arbitrary `ℒₒᵣ` formulas.

Indices: ordinal bound `α : ONote` (`< ε₀`, carried with `α.NF`), numeric Hardy index `k`, cut rank
`c`.  The ω-rule's `n`-th premise lives at the **raised** numeric index `max k n` (Towsner's `I∀`),
exactly as in `B.allI`.  This file: the inductive + the basic structural lemmas (`mono_k`, `weakening`,
`mono_c`).  Inversions, cut-reduction, and the embedding follow on later laps.  WIP — not in build target.
-/
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Foundation.FirstOrder.Arithmetic.Basic.Model
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Order.Lattice.Nat
import GoodsteinPA.Hardy

namespace GoodsteinPA.BoundedZinfty

open LO LO.FirstOrder ONote
open GoodsteinPA.FastGrowing

/-- The closed formulas of `ℒₒᵣ` (full FO syntax, total de-Morgan `∼`, finite `complexity`). -/
abbrev Form := SyntacticFormula ℒₒᵣ

/-- The `n`-th numeral as a closed term, ready for substitution `φ/[nm n]`. -/
noncomputable def nm (n : ℕ) : Semiterm ℒₒᵣ ℕ 0 := (Semiterm.Operator.numeral ℒₒᵣ n).const

/-- A sequent is a finite **set** of formulas (Towsner's `Γ`); set sequents ⇒ contraction is free. -/
abbrev Seq := Finset Form

/-- Atomic truth in the standard model `ℕ` (assignment-free once free vars are numeral-substituted —
the O2′-validated form; `=`/`<` are decidable in `ℕ`). -/
noncomputable def atomTrue (φ : Form) : Prop := Semiformula.Evalm ℕ (fun _ => 0) (fun _ => 0) φ

/-- **The witness-bounded `Z_∞` calculus** `Zᵏ ⊢^{α}_{k,c} Γ` over real `ℒₒᵣ` syntax (Towsner §15).

* `axL` — clash identity axiom (`rel`/`nrel` together), no `k`-condition.
* `verumR` — `⊤` closes.
* `trueRel`/`trueNrel` — **truth axiom**: a true atom closes, side condition `τ α < k` (= `norm α < k`).
* `weak` — sequent + ordinal weakening (Towsner Lemma 19.1 / 16.4), budget `norm β < k`.
* `andI`/`orI` — the connective rules (premises at `β < α`).
* `allω` — the **ω-rule**: one premise per numeral `n`, the `n`-th at numeric index `max k n`.
* `exI` — **witness-bounded `∃`**: the numeral witness `n ≤ h_α(k)` (= `hardy α k`).
* `cut` — cut on a formula of `complexity < c`. -/
inductive Zk : ONote → ℕ → ℕ → Seq → Prop
  | axL {α k c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zk α k c Γ
  | verumR {α k c Γ} (h : (⊤ : Form) ∈ Γ) : Zk α k c Γ
  | trueRel {α k c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.rel r v))
      (hτ : norm α < k) (hmem : Semiformula.rel r v ∈ Γ) : Zk α k c Γ
  | trueNrel {α k c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.nrel r v))
      (hτ : norm α < k) (hmem : Semiformula.nrel r v ∈ Γ) : Zk α k c Γ
  | weak {α β k c Δ Γ} (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k)
      (hsub : Δ ⊆ Γ) (d : Zk β k c Δ) : Zk α k c Γ
  | andI {α βφ βψ k c Γ} (φ ψ : Form) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF) (hτφ : norm βφ < k) (hτψ : norm βψ < k)
      (dφ : Zk βφ k c (insert φ Γ)) (dψ : Zk βψ k c (insert ψ Γ)) :
      Zk α k c (insert (φ ⋏ ψ) Γ)
  | orI {α β k c Γ} (φ ψ : Form) (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k)
      (d : Zk β k c (insert φ (insert ψ Γ))) : Zk α k c (insert (φ ⋎ ψ) Γ)
  | allω {α k c Γ} (φ : SyntacticSemiformula ℒₒᵣ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF) (hτ : ∀ n, norm (β n) < max k n)
      (d : ∀ n, Zk (β n) (max k n) c (insert (φ/[nm n]) Γ)) : Zk α k c (insert (∀⁰ φ) Γ)
  | exI {α β k c Γ} (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k) (hbound : n ≤ hardy α k)
      (d : Zk β k c (insert (φ/[nm n]) Γ)) : Zk α k c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ k c Γ} (φ : Form) (hcompl : φ.complexity < c) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF) (hτφ : norm βφ < k) (hτψ : norm βψ < k)
      (d₁ : Zk βφ k c (insert φ Γ)) (d₂ : Zk βψ k c (insert (∼φ) Γ)) : Zk α k c Γ

namespace Zk

/-- **`k`-monotonicity** (Towsner Lemma 16.4, numeric part): raising the Hardy index relaxes every
side condition (`τ α < k` easier, witness bound `hardy α k` larger by `hardy_monotone`). -/
theorem mono_k : ∀ {α k c Γ}, Zk α k c Γ → ∀ {k'}, k ≤ k' → Zk α k' c Γ := by
  intro α k c Γ d
  induction d with
  | axL r v hp hn => intro k' _; exact Zk.axL r v hp hn
  | verumR h => intro k' _; exact Zk.verumR h
  | trueRel r v htrue hτ hmem => intro k' hk; exact Zk.trueRel r v htrue (lt_of_lt_of_le hτ hk) hmem
  | trueNrel r v htrue hτ hmem =>
      intro k' hk; exact Zk.trueNrel r v htrue (lt_of_lt_of_le hτ hk) hmem
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      intro k' hk; exact Zk.weak hβ hβNF hαNF (lt_of_lt_of_le hτ hk) hsub (ih hk)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro k' hk
      exact Zk.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ hk) (lt_of_lt_of_le hτψ hk)
        (ihφ hk) (ihψ hk)
  | orI φ ψ hβ hβNF hαNF hτ _ ih =>
      intro k' hk; exact Zk.orI φ ψ hβ hβNF hαNF (lt_of_lt_of_le hτ hk) (ih hk)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      intro k' hk
      exact Zk.allω φ β hβ hβNF hαNF (fun n => lt_of_lt_of_le (hτ n) (max_le_max hk le_rfl))
        (fun n => ih n (max_le_max hk le_rfl))
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro k' hk
      exact Zk.exI φ n hβ hβNF hαNF (lt_of_lt_of_le hτ hk)
        (le_trans hbound (hardy_monotone _ hk)) (ih hk)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro k' hk
      exact Zk.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ hk) (lt_of_lt_of_le hτψ hk)
        (ih₁ hk) (ih₂ hk)

/-- **`c`-monotonicity**: raising the cut-rank bound preserves derivability (only `cut`'s
`complexity < c` side condition is affected). -/
theorem mono_c : ∀ {α k c Γ}, Zk α k c Γ → ∀ {c'}, c ≤ c' → Zk α k c' Γ := by
  intro α k c Γ d
  induction d with
  | axL r v hp hn => intro c' _; exact Zk.axL r v hp hn
  | verumR h => intro c' _; exact Zk.verumR h
  | trueRel r v htrue hτ hmem => intro c' _; exact Zk.trueRel r v htrue hτ hmem
  | trueNrel r v htrue hτ hmem => intro c' _; exact Zk.trueNrel r v htrue hτ hmem
  | weak hβ hβNF hαNF hτ hsub _ ih => intro c' hc; exact Zk.weak hβ hβNF hαNF hτ hsub (ih hc)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro c' hc
      exact Zk.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ihφ hc) (ihψ hc)
  | orI φ ψ hβ hβNF hαNF hτ _ ih => intro c' hc; exact Zk.orI φ ψ hβ hβNF hαNF hτ (ih hc)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      intro c' hc; exact Zk.allω φ β hβ hβNF hαNF hτ (fun n => ih n hc)
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro c' hc; exact Zk.exI φ n hβ hβNF hαNF hτ hbound (ih hc)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro c' hc
      exact Zk.cut φ (lt_of_lt_of_le hcompl hc) hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ih₁ hc) (ih₂ hc)

/-- **Sequent weakening** (Towsner Lemma 19.1): enlarge the sequent, raising the ordinal to any
`NF` `α' > α` (with budget `norm α < k`). Direct application of the `weak` constructor. -/
theorem weakening {α α' k c Δ Γ} (hα : α < α') (hαNF : α.NF) (hα'NF : α'.NF) (hτ : norm α < k)
    (hsub : Δ ⊆ Γ) (d : Zk α k c Δ) : Zk α' k c Γ :=
  Zk.weak hα hαNF hα'NF hτ hsub d

end Zk

end GoodsteinPA.BoundedZinfty
