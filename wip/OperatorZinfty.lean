/-
# `Zᵉᵏᵈ` — the control-ordinal operator witness-bounded `Z_∞` calculus (Towsner §15 + §19, lap-8)

The lap-7 ADDENDUM 4 finding: the split-index `(k,d)` calculus (`wip/SplitZinfty.lean`) closes the
§19.6 **norm-budget** obstruction (the `d`-bump `d ↦ d + norm α`) but NOT the **witness-index** one —
the principal `exI` cut's witness `hardy γ(·)` makes the witness bound grow super-linearly through
commuting ω-rules, and a witness bound tied to the *derivation* ordinal `α` cannot absorb that under
cut-elim (which grows `α ↦ α + γ`).

**The fix (lap-8 design): a control ordinal `e`.** Decouple the `exI` witness bound from the
derivation ordinal `α` onto a separate **control ordinal** `e`: the witness bound becomes
`n ≤ hardy e (k + d)` (was `hardy α (k + d)`). Cut-elimination then *raises `e`* to dominate the
cut-formula bounds while `α` grows freely; the witness stays controlled by `hardy e`, a `hardy`-closed
quantity (Buchholz operator-controlled derivations, specialized to PA, numeric-`e` form).

The Hardy infrastructure this needs is **banked** (lap 8, `src/Hardy.lean` + `src/LowerBound.lean`):
- `hardy_add_collapse` : `H_{e+α} = H_e ∘ H_α` (control-side: collapse nested control under cut-elim).
- `hardy_comp_lt_goodsteinLength` : `H_α(H_e(m)) < G(m)` eventually (lower-bound side: a nested
  control index is still Goodstein-dominated, so the witness-bounded lower bound survives).

This file: the inductive `Zekd` + structural layer (`mono_k`, `mono_d`, `mono_c`, `mono_e`, `weakening`).
The inversion suite + §19.5/§19.6 cut reductions port from `wip/SplitZinfty.lean` (mechanical: thread
the inert `e`, plus the §19.6 witness-control step using the banked Hardy lemmas).
-/
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Foundation.FirstOrder.Arithmetic.Basic.Model
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Order.Lattice.Nat
import GoodsteinPA.Hardy

namespace GoodsteinPA.OperatorZinfty

open LO LO.FirstOrder ONote
open GoodsteinPA.FastGrowing

abbrev Form := SyntacticFormula ℒₒᵣ
noncomputable def nm (n : ℕ) : Semiterm ℒₒᵣ ℕ 0 := (Semiterm.Operator.numeral ℒₒᵣ n).const
abbrev Seq := Finset Form
noncomputable def atomTrue (φ : Form) : Prop := Semiformula.Evalm ℕ (fun _ => 0) (fun _ => 0) φ

/-- **The control-ordinal operator witness-bounded `Z_∞` calculus** `Zᵉᵏᵈ ⊢^{α,e}_{k,d,c} Γ`.
Derivation ordinal `α`; **control ordinal `e`** (governs the witness bound, raised by cut-elim);
effective norm budget `k + d`; ω-premise `n` at `(max k n, d)`; **witness bound `hardy e (k+d)`**
(decoupled from `α`). Cf. `SplitZinfty.Zkd` — identical except the `exI` bound uses `e` not `α`, and
every rule carries the inert `e`. -/
inductive Zekd : ONote → ONote → ℕ → ℕ → ℕ → Seq → Prop
  | axL {α e k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zekd α e k d c Γ
  | verumR {α e k d c Γ} (h : (⊤ : Form) ∈ Γ) : Zekd α e k d c Γ
  | trueRel {α e k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.rel r v))
      (hτ : norm α < k + d) (hmem : Semiformula.rel r v ∈ Γ) : Zekd α e k d c Γ
  | trueNrel {α e k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.nrel r v))
      (hτ : norm α < k + d) (hmem : Semiformula.nrel r v ∈ Γ) : Zekd α e k d c Γ
  | wk {α e k d c Δ Γ} (hsub : Δ ⊆ Γ) (dd : Zekd α e k d c Δ) : Zekd α e k d c Γ
  | weak {α β e k d c Δ Γ} (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k + d)
      (hsub : Δ ⊆ Γ) (dd : Zekd β e k d c Δ) : Zekd α e k d c Γ
  | andI {α βφ βψ e k d c Γ} (φ ψ : Form) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF) (hτφ : norm βφ < k + d) (hτψ : norm βψ < k + d)
      (dφ : Zekd βφ e k d c (insert φ Γ)) (dψ : Zekd βψ e k d c (insert ψ Γ)) :
      Zekd α e k d c (insert (φ ⋏ ψ) Γ)
  | orI {α β e k d c Γ} (φ ψ : Form) (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k + d)
      (dd : Zekd β e k d c (insert φ (insert ψ Γ))) : Zekd α e k d c (insert (φ ⋎ ψ) Γ)
  | allω {α e k d c Γ} (φ : SyntacticSemiformula ℒₒᵣ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF) (hτ : ∀ n, norm (β n) < max k n + d)
      (dd : ∀ n, Zekd (β n) e (max k n) d c (insert (φ/[nm n]) Γ)) :
      Zekd α e k d c (insert (∀⁰ φ) Γ)
  | exI {α β e k d c Γ} (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k + d) (hbound : n ≤ hardy e (k + d))
      (dd : Zekd β e k d c (insert (φ/[nm n]) Γ)) : Zekd α e k d c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ e k d c Γ} (φ : Form) (hcompl : φ.complexity < c) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF) (hτφ : norm βφ < k + d) (hτψ : norm βψ < k + d)
      (d₁ : Zekd βφ e k d c (insert φ Γ)) (d₂ : Zekd βψ e k d c (insert (∼φ) Γ)) :
      Zekd α e k d c Γ

namespace Zekd

/-- **`k`-monotonicity** (the `max`/cofinal part; inversions raise this idempotently). The witness
bound `hardy e (k+d)` rises with `k` via `hardy_monotone`. -/
theorem mono_k : ∀ {α e k d c Γ}, Zekd α e k d c Γ → ∀ {k'}, k ≤ k' → Zekd α e k' d c Γ := by
  intro α e k d c Γ dd
  induction dd with
  | axL r v hp hn => intro k' _; exact Zekd.axL r v hp hn
  | verumR h => intro k' _; exact Zekd.verumR h
  | trueRel r v htrue hτ hmem =>
      intro k' hk; exact Zekd.trueRel r v htrue (lt_of_lt_of_le hτ (by omega)) hmem
  | trueNrel r v htrue hτ hmem =>
      intro k' hk; exact Zekd.trueNrel r v htrue (lt_of_lt_of_le hτ (by omega)) hmem
  | wk hsub _ ih => intro k' hk; exact Zekd.wk hsub (ih hk)
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      intro k' hk; exact Zekd.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) hsub (ih hk)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro k' hk
      exact Zekd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ihφ hk) (ihψ hk)
  | orI φ ψ hβ hβNF hαNF hτ _ ih =>
      intro k' hk; exact Zekd.orI φ ψ hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) (ih hk)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      intro k' hk
      exact Zekd.allω φ β hβ hβNF hαNF
        (fun n => lt_of_lt_of_le (hτ n) (by have := Nat.add_le_add_right (max_le_max hk (le_refl n)) d; omega))
        (fun n => ih n (max_le_max hk (le_refl n)))
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro k' hk
      exact Zekd.exI φ n hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega))
        (le_trans hbound (hardy_monotone _ (by omega))) (ih hk)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro k' hk
      exact Zekd.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ih₁ hk) (ih₂ hk)

/-- **`d`-monotonicity** (the additive cut-shift budget; the §19.6-commuting case raises this by
`norm α`). The witness bound `hardy e (k+d)` rises with `d` via `hardy_monotone`. -/
theorem mono_d : ∀ {α e k d c Γ}, Zekd α e k d c Γ → ∀ {d'}, d ≤ d' → Zekd α e k d' c Γ := by
  intro α e k d c Γ dd
  induction dd with
  | axL r v hp hn => intro d' _; exact Zekd.axL r v hp hn
  | verumR h => intro d' _; exact Zekd.verumR h
  | trueRel r v htrue hτ hmem =>
      intro d' hd; exact Zekd.trueRel r v htrue (lt_of_lt_of_le hτ (by omega)) hmem
  | trueNrel r v htrue hτ hmem =>
      intro d' hd; exact Zekd.trueNrel r v htrue (lt_of_lt_of_le hτ (by omega)) hmem
  | wk hsub _ ih => intro d' hd; exact Zekd.wk hsub (ih hd)
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      intro d' hd; exact Zekd.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) hsub (ih hd)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro d' hd
      exact Zekd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ihφ hd) (ihψ hd)
  | orI φ ψ hβ hβNF hαNF hτ _ ih =>
      intro d' hd; exact Zekd.orI φ ψ hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) (ih hd)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      intro d' hd
      exact Zekd.allω φ β hβ hβNF hαNF (fun n => lt_of_lt_of_le (hτ n) (by omega))
        (fun n => ih n hd)
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro d' hd
      exact Zekd.exI φ n hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega))
        (le_trans hbound (hardy_monotone _ (by omega))) (ih hd)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro d' hd
      exact Zekd.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ih₁ hd) (ih₂ hd)

/-- **`c`-monotonicity** (cut-rank). -/
theorem mono_c : ∀ {α e k d c Γ}, Zekd α e k d c Γ → ∀ {c'}, c ≤ c' → Zekd α e k d c' Γ := by
  intro α e k d c Γ dd
  induction dd with
  | axL r v hp hn => intro c' _; exact Zekd.axL r v hp hn
  | verumR h => intro c' _; exact Zekd.verumR h
  | trueRel r v htrue hτ hmem => intro c' _; exact Zekd.trueRel r v htrue hτ hmem
  | trueNrel r v htrue hτ hmem => intro c' _; exact Zekd.trueNrel r v htrue hτ hmem
  | wk hsub _ ih => intro c' hc; exact Zekd.wk hsub (ih hc)
  | weak hβ hβNF hαNF hτ hsub _ ih => intro c' hc; exact Zekd.weak hβ hβNF hαNF hτ hsub (ih hc)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro c' hc; exact Zekd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ihφ hc) (ihψ hc)
  | orI φ ψ hβ hβNF hαNF hτ _ ih => intro c' hc; exact Zekd.orI φ ψ hβ hβNF hαNF hτ (ih hc)
  | allω φ β hβ hβNF hαNF hτ _ ih => intro c' hc; exact Zekd.allω φ β hβ hβNF hαNF hτ (fun n => ih n hc)
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro c' hc; exact Zekd.exI φ n hβ hβNF hαNF hτ hbound (ih hc)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro c' hc
      exact Zekd.cut φ (lt_of_lt_of_le hcompl hc) hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ih₁ hc) (ih₂ hc)

/-- **`e`-monotonicity** (the NEW control axis; cut-elimination raises `e` to dominate cut-formula
bounds). Only the `exI` witness bound `hardy e (k+d)` depends on `e`, and it rises with `e` via
the index-monotonicity `hardy_le_of_lt` (with the budget side condition `norm e ≤ k+d`). -/
theorem mono_e : ∀ {α e k d c Γ}, Zekd α e k d c Γ → ∀ {e'}, e.NF → e'.NF → e < e' →
    norm e ≤ k + d → Zekd α e' k d c Γ := by
  intro α e k d c Γ dd
  induction dd with
  | axL r v hp hn => intro e' _ _ _ _; exact Zekd.axL r v hp hn
  | verumR h => intro e' _ _ _ _; exact Zekd.verumR h
  | trueRel r v htrue hτ hmem => intro e' _ _ _ _; exact Zekd.trueRel r v htrue hτ hmem
  | trueNrel r v htrue hτ hmem => intro e' _ _ _ _; exact Zekd.trueNrel r v htrue hτ hmem
  | wk hsub _ ih => intro e' he heN' hlt hnorm; exact Zekd.wk hsub (ih he heN' hlt hnorm)
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      intro e' he heN' hlt hnorm; exact Zekd.weak hβ hβNF hαNF hτ hsub (ih he heN' hlt hnorm)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro e' he heN' hlt hnorm
      exact Zekd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ihφ he heN' hlt hnorm) (ihψ he heN' hlt hnorm)
  | orI φ ψ hβ hβNF hαNF hτ _ ih =>
      intro e' he heN' hlt hnorm; exact Zekd.orI φ ψ hβ hβNF hαNF hτ (ih he heN' hlt hnorm)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      intro e' he heN' hlt hnorm
      refine Zekd.allω φ β hβ hβNF hαNF hτ (fun n => ih n he heN' hlt ?_)
      -- premise n runs at index (max k n, d): budget `norm e ≤ max k n + d` from `norm e ≤ k + d`
      have : k ≤ max k n := le_max_left _ _
      omega
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro e' he heN' hlt hnorm
      refine Zekd.exI φ n hβ hβNF hαNF hτ ?_ (ih he heN' hlt hnorm)
      exact le_trans hbound (hardy_le_of_lt he heN' hlt hnorm)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro e' he heN' hlt hnorm
      exact Zekd.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ih₁ he heN' hlt hnorm) (ih₂ he heN' hlt hnorm)

/-- Sequent weakening (height-preserving). -/
theorem weakening {α e k d c Δ Γ} (hsub : Δ ⊆ Γ) (dd : Zekd α e k d c Δ) : Zekd α e k d c Γ :=
  Zekd.wk hsub dd

end Zekd

end GoodsteinPA.OperatorZinfty
