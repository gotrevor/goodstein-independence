/-
# `Zᵏᵈ` — the split-index `(k, d)` witness-bounded `Z_∞` calculus (Towsner §15 + §19, lap-7 design)

The lap-7 obstruction analysis (`ANALYSIS-2026-06-22-cutelim-k-threading.md`, ADDENDA 1–3) showed that
the single-numeric-index calculus `Zk` (`wip/BoundedZinfty.lean`) cannot complete §19.6 cut-elimination:
the ω-rule index `max k n` is good for `allInv` (idempotent) but breaks the §19.6-commuting case (the
`+norm α` bound shift overflows the `max{k,n}~n` budget for large `n`); switching to `k + n` fixes
§19.6 but breaks `allInv` (no idempotent collapse ⟹ slope-2 index ⟹ lower bound needs multiplicative
Hardy rescaling).

**The fix (ADDENDUM 3): split the index into `(k, d)`** — `k` the cofinal/`max` part (transformed by
the inversions, idempotently), `d` the additive cut-shift budget (transformed by cut-elimination,
additively). The effective norm budget of a node is `k + d`; the ω-rule's `n`-th premise sits at
`(max k n, d)`, i.e. budget `max(k,n) + d` (the `+d` OUTSIDE the `max`, shifting uniformly).

* `allInv` transforms only `k` (via `max`, leaving `d`) ⟹ idempotent, as in `Zk`.
* §19.6-commuting transforms only `d` (`d ↦ d + norm α`, leaving `k`) ⟹ absorbs the `+α` shift.
* Slope stays 1: `max(k,n) + d ≤ n + (k+d)`, so the lower bound's I∀ case is discharged by the banked
  `hardy_shift_lt_goodsteinLength` (`hardy α (max(k,n)+d) ≤ hardy α (n+(k+d)) < G n`). No rescaling.

This file: the inductive + the structural monotonicity lemmas (`mono_k`, `mono_d`, `mono_c`). The
inversion suite, cut reductions, `cutReduceAll`, `cutElimStep`, `cutElim` port from
`wip/BoundedZinfty.lean` by threading the inert `d` (inversions) / bumping `d` (the §19.6 payoff). WIP —
not in the build target.
-/
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Foundation.FirstOrder.Arithmetic.Basic.Model
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Order.Lattice.Nat
import GoodsteinPA.Hardy

namespace GoodsteinPA.SplitZinfty

open LO LO.FirstOrder ONote
open GoodsteinPA.FastGrowing

abbrev Form := SyntacticFormula ℒₒᵣ
noncomputable def nm (n : ℕ) : Semiterm ℒₒᵣ ℕ 0 := (Semiterm.Operator.numeral ℒₒᵣ n).const
abbrev Seq := Finset Form
noncomputable def atomTrue (φ : Form) : Prop := Semiformula.Evalm ℕ (fun _ => 0) (fun _ => 0) φ

/-- **The split-index witness-bounded `Z_∞` calculus** `Zᵏᵈ ⊢^{α}_{k,d,c} Γ`.
Effective norm budget `k + d`; ω-premise `n` at `(max k n, d)` (budget `max(k,n)+d`); witness bound
`hardy α (k+d)`. -/
inductive Zkd : ONote → ℕ → ℕ → ℕ → Seq → Prop
  | axL {α k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zkd α k d c Γ
  | verumR {α k d c Γ} (h : (⊤ : Form) ∈ Γ) : Zkd α k d c Γ
  | trueRel {α k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.rel r v))
      (hτ : norm α < k + d) (hmem : Semiformula.rel r v ∈ Γ) : Zkd α k d c Γ
  | trueNrel {α k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.nrel r v))
      (hτ : norm α < k + d) (hmem : Semiformula.nrel r v ∈ Γ) : Zkd α k d c Γ
  | wk {α k d c Δ Γ} (hsub : Δ ⊆ Γ) (dd : Zkd α k d c Δ) : Zkd α k d c Γ
  | weak {α β k d c Δ Γ} (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k + d)
      (hsub : Δ ⊆ Γ) (dd : Zkd β k d c Δ) : Zkd α k d c Γ
  | andI {α βφ βψ k d c Γ} (φ ψ : Form) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF) (hτφ : norm βφ < k + d) (hτψ : norm βψ < k + d)
      (dφ : Zkd βφ k d c (insert φ Γ)) (dψ : Zkd βψ k d c (insert ψ Γ)) :
      Zkd α k d c (insert (φ ⋏ ψ) Γ)
  | orI {α β k d c Γ} (φ ψ : Form) (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k + d)
      (dd : Zkd β k d c (insert φ (insert ψ Γ))) : Zkd α k d c (insert (φ ⋎ ψ) Γ)
  | allω {α k d c Γ} (φ : SyntacticSemiformula ℒₒᵣ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF) (hτ : ∀ n, norm (β n) < max k n + d)
      (dd : ∀ n, Zkd (β n) (max k n) d c (insert (φ/[nm n]) Γ)) : Zkd α k d c (insert (∀⁰ φ) Γ)
  | exI {α β k d c Γ} (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k + d) (hbound : n ≤ hardy α (k + d))
      (dd : Zkd β k d c (insert (φ/[nm n]) Γ)) : Zkd α k d c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ k d c Γ} (φ : Form) (hcompl : φ.complexity < c) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF) (hτφ : norm βφ < k + d) (hτψ : norm βψ < k + d)
      (d₁ : Zkd βφ k d c (insert φ Γ)) (d₂ : Zkd βψ k d c (insert (∼φ) Γ)) : Zkd α k d c Γ

namespace Zkd

/-- **`k`-monotonicity** (the `max`/cofinal part; inversions raise this idempotently). -/
theorem mono_k : ∀ {α k d c Γ}, Zkd α k d c Γ → ∀ {k'}, k ≤ k' → Zkd α k' d c Γ := by
  intro α k d c Γ dd
  induction dd with
  | axL r v hp hn => intro k' _; exact Zkd.axL r v hp hn
  | verumR h => intro k' _; exact Zkd.verumR h
  | trueRel r v htrue hτ hmem =>
      intro k' hk; exact Zkd.trueRel r v htrue (lt_of_lt_of_le hτ (by omega)) hmem
  | trueNrel r v htrue hτ hmem =>
      intro k' hk; exact Zkd.trueNrel r v htrue (lt_of_lt_of_le hτ (by omega)) hmem
  | wk hsub _ ih => intro k' hk; exact Zkd.wk hsub (ih hk)
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      intro k' hk; exact Zkd.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) hsub (ih hk)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro k' hk
      exact Zkd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ihφ hk) (ihψ hk)
  | orI φ ψ hβ hβNF hαNF hτ _ ih =>
      intro k' hk; exact Zkd.orI φ ψ hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) (ih hk)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      intro k' hk
      exact Zkd.allω φ β hβ hβNF hαNF (fun n => lt_of_lt_of_le (hτ n) (by have := Nat.add_le_add_right (max_le_max hk (le_refl n)) d; omega))
        (fun n => ih n (max_le_max hk (le_refl n)))
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro k' hk
      exact Zkd.exI φ n hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega))
        (le_trans hbound (hardy_monotone _ (by omega))) (ih hk)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro k' hk
      exact Zkd.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ih₁ hk) (ih₂ hk)

/-- **`d`-monotonicity** (the additive cut-shift budget; the §19.6-commuting case raises this). -/
theorem mono_d : ∀ {α k d c Γ}, Zkd α k d c Γ → ∀ {d'}, d ≤ d' → Zkd α k d' c Γ := by
  intro α k d c Γ dd
  induction dd with
  | axL r v hp hn => intro d' _; exact Zkd.axL r v hp hn
  | verumR h => intro d' _; exact Zkd.verumR h
  | trueRel r v htrue hτ hmem =>
      intro d' hd; exact Zkd.trueRel r v htrue (lt_of_lt_of_le hτ (by omega)) hmem
  | trueNrel r v htrue hτ hmem =>
      intro d' hd; exact Zkd.trueNrel r v htrue (lt_of_lt_of_le hτ (by omega)) hmem
  | wk hsub _ ih => intro d' hd; exact Zkd.wk hsub (ih hd)
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      intro d' hd; exact Zkd.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) hsub (ih hd)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro d' hd
      exact Zkd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ihφ hd) (ihψ hd)
  | orI φ ψ hβ hβNF hαNF hτ _ ih =>
      intro d' hd; exact Zkd.orI φ ψ hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) (ih hd)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      intro d' hd
      exact Zkd.allω φ β hβ hβNF hαNF (fun n => lt_of_lt_of_le (hτ n) (by omega))
        (fun n => ih n hd)
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro d' hd
      exact Zkd.exI φ n hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega))
        (le_trans hbound (hardy_monotone _ (by omega))) (ih hd)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro d' hd
      exact Zkd.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ih₁ hd) (ih₂ hd)

/-- **`c`-monotonicity** (cut-rank). -/
theorem mono_c : ∀ {α k d c Γ}, Zkd α k d c Γ → ∀ {c'}, c ≤ c' → Zkd α k d c' Γ := by
  intro α k d c Γ dd
  induction dd with
  | axL r v hp hn => intro c' _; exact Zkd.axL r v hp hn
  | verumR h => intro c' _; exact Zkd.verumR h
  | trueRel r v htrue hτ hmem => intro c' _; exact Zkd.trueRel r v htrue hτ hmem
  | trueNrel r v htrue hτ hmem => intro c' _; exact Zkd.trueNrel r v htrue hτ hmem
  | wk hsub _ ih => intro c' hc; exact Zkd.wk hsub (ih hc)
  | weak hβ hβNF hαNF hτ hsub _ ih => intro c' hc; exact Zkd.weak hβ hβNF hαNF hτ hsub (ih hc)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro c' hc; exact Zkd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ihφ hc) (ihψ hc)
  | orI φ ψ hβ hβNF hαNF hτ _ ih => intro c' hc; exact Zkd.orI φ ψ hβ hβNF hαNF hτ (ih hc)
  | allω φ β hβ hβNF hαNF hτ _ ih => intro c' hc; exact Zkd.allω φ β hβ hβNF hαNF hτ (fun n => ih n hc)
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro c' hc; exact Zkd.exI φ n hβ hβNF hαNF hτ hbound (ih hc)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro c' hc
      exact Zkd.cut φ (lt_of_lt_of_le hcompl hc) hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ih₁ hc) (ih₂ hc)

/-- Sequent weakening (height-preserving). -/
theorem weakening {α k d c Δ Γ} (hsub : Δ ⊆ Γ) (dd : Zkd α k d c Δ) : Zkd α k d c Γ := Zkd.wk hsub dd

end Zkd

end GoodsteinPA.SplitZinfty
