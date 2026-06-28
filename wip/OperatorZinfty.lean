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
      (hτ : norm α < k + d) (hαNF : α.NF) (hmem : Semiformula.rel r v ∈ Γ) : Zekd α e k d c Γ
  | trueNrel {α e k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.nrel r v))
      (hτ : norm α < k + d) (hαNF : α.NF) (hmem : Semiformula.nrel r v ∈ Γ) : Zekd α e k d c Γ
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
  | trueRel r v htrue hτ hαNF hmem =>
      intro k' hk; exact Zekd.trueRel r v htrue (lt_of_lt_of_le hτ (by omega)) hαNF hmem
  | trueNrel r v htrue hτ hαNF hmem =>
      intro k' hk; exact Zekd.trueNrel r v htrue (lt_of_lt_of_le hτ (by omega)) hαNF hmem
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
  | trueRel r v htrue hτ hαNF hmem =>
      intro d' hd; exact Zekd.trueRel r v htrue (lt_of_lt_of_le hτ (by omega)) hαNF hmem
  | trueNrel r v htrue hτ hαNF hmem =>
      intro d' hd; exact Zekd.trueNrel r v htrue (lt_of_lt_of_le hτ (by omega)) hαNF hmem
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
  | trueRel r v htrue hτ hαNF hmem => intro c' _; exact Zekd.trueRel r v htrue hτ hαNF hmem
  | trueNrel r v htrue hτ hαNF hmem => intro c' _; exact Zekd.trueNrel r v htrue hτ hαNF hmem
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
  | trueRel r v htrue hτ hαNF hmem => intro e' _ _ _ _; exact Zekd.trueRel r v htrue hτ hαNF hmem
  | trueNrel r v htrue hτ hαNF hmem => intro e' _ _ _ _; exact Zekd.trueNrel r v htrue hτ hαNF hmem
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

private theorem invPush (A b : Form) (s : Seq) {φ ψ : Form} :
    insert φ (insert ψ ((insert b s).erase A)) ⊆ insert b (insert φ (insert ψ (s.erase A))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

private theorem invPull (A : Form) {b : Form} (h : b ≠ A) (s : Seq) {φ ψ : Form} :
    insert b (insert φ (insert ψ (s.erase A))) ⊆ insert φ (insert ψ ((insert b s).erase A)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | rfl | rfl | hx
  · exact Or.inr (Or.inr ⟨h, Or.inl rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨hx.1, Or.inr hx.2⟩)

private theorem invPush2 (A b₁ b₂ : Form) (s : Seq) {φ ψ : Form} :
    insert φ (insert ψ ((insert b₁ (insert b₂ s)).erase A))
      ⊆ insert b₁ (insert b₂ (insert φ (insert ψ (s.erase A)))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

private theorem princOrSub {A : Form} (s : Seq) {φ ψ : Form} :
    insert φ (insert ψ ((insert φ (insert ψ s)).erase A)) ⊆ insert φ (insert ψ (s.erase A)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- **∨-inversion.** Replace `φ ⋎ ψ` by `φ`, `ψ`, same `(α,k,d,c)`. -/
theorem orInv {φ ψ : Form} : ∀ {α e k d c Γ}, Zekd α e k d c Γ → (φ ⋎ ψ) ∈ Γ →
    Zekd α e k d c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  have hφ0 : φ ≠ (φ ⋎ ψ) := Semiformula.ne_or_left φ ψ
  have hψ0 : ψ ≠ (φ ⋎ ψ) := Semiformula.ne_or_right φ ψ
  intro α e k d c Γ dd
  induction dd with
  | @axL α e k d c Γ ar r v hp hn =>
      intro _
      refine Zekd.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩))
  | @verumR α e k d c Γ h =>
      intro _
      exact Zekd.verumR (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩)))
  | @trueRel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      intro _
      exact Zekd.trueRel r v htrue hτ hαNF (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩)))
  | @trueNrel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      intro _
      exact Zekd.trueNrel r v htrue hτ hαNF (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩)))
  | @wk α e k d c Δ Γ hsub _ ih =>
      intro hmem
      by_cases hd : (φ ⋎ ψ) ∈ Δ
      · exact Zekd.wk (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub))) (ih hd)
      · refine Zekd.wk ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @weak α β e k d c Δ Γ hβ hβNF hαNF hτ hsub _ ih =>
      intro hmem
      by_cases hd : (φ ⋎ ψ) ∈ Δ
      · exact Zekd.weak hβ hβNF hαNF hτ (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub))) (ih hd)
      · refine Zekd.weak hβ hβNF hαNF hτ ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @andI α βφ' βψ' e k d c Γ₀ φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro hmem
      have hhead : (φ' ⋏ ψ') ≠ (φ ⋎ ψ) := by intro h; simp [Wedge.wedge, Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have Pφ := Zekd.wk (invPush (φ ⋎ ψ) φ' Γ₀) (ihφ (Finset.mem_insert_of_mem hmem0))
      have Pψ := Zekd.wk (invPush (φ ⋎ ψ) ψ' Γ₀) (ihψ (Finset.mem_insert_of_mem hmem0))
      exact Zekd.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zekd.andI φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ Pφ Pψ)
  | @orI α β e k d c Γ₀ φ' ψ' hβ hβNF hαNF hτ _ ih =>
      intro hmem
      by_cases hhd : (φ' ⋎ ψ') = (φ ⋎ ψ)
      · obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp hhd.symm
        rw [Finset.erase_insert_eq_erase]
        by_cases hd : (φ ⋎ ψ) ∈ Γ₀
        · exact Zekd.weak hβ hβNF hαNF hτ (princOrSub Γ₀)
            (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hd)))
        · rw [Finset.erase_eq_of_notMem hd]
          exact Zekd.weak hβ hβNF hαNF hτ (Finset.Subset.refl _) (by assumption)
      · have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have P := Zekd.wk (invPush2 (φ ⋎ ψ) φ' ψ' Γ₀)
          (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0)))
        exact Zekd.wk (invPull (φ ⋎ ψ) hhd Γ₀) (Zekd.orI φ' ψ' hβ hβNF hαNF hτ P)
  | @allω α e k d c Γ₀ χ β hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (∀⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zekd (β n) e (max k n) d c
          (insert (χ/[nm n]) (insert φ (insert ψ (Γ₀.erase (φ ⋎ ψ))))) := fun n =>
        Zekd.wk (invPush (φ ⋎ ψ) (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zekd.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zekd.allω χ β hβ hβNF hαNF hτ key)
  | @exI α β e k d c Γ₀ χ n hβ hβNF hαNF hτ hbound _ ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zekd.wk (invPush (φ ⋎ ψ) (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zekd.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zekd.exI χ n hβ hβNF hαNF hτ hbound P)
  | @cut α βφ' βψ' e k d c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zekd.wk (invPush (φ ⋎ ψ) χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zekd.wk (invPush (φ ⋎ ψ) (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zekd.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ P₁ P₂

/-! ### Single-insert reshuffle helpers (for ∧-inversion and the ∀-inversion). -/

private theorem inv1Push (A e b : Form) (s : Seq) :
    insert e ((insert b s).erase A) ⊆ insert b (insert e (s.erase A)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

private theorem inv1Pull (A e : Form) {b : Form} (h : b ≠ A) (s : Seq) :
    insert b (insert e (s.erase A)) ⊆ insert e ((insert b s).erase A) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | rfl | hx
  · exact Or.inr ⟨h, Or.inl rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hx.1, Or.inr hx.2⟩

private theorem inv1Push2 (A e b₁ b₂ : Form) (s : Seq) :
    insert e ((insert b₁ (insert b₂ s)).erase A) ⊆ insert b₁ (insert b₂ (insert e (s.erase A))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

private theorem princAllSub (A e : Form) (s : Seq) :
    insert e ((insert e s).erase A) ⊆ insert e (s.erase A) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- **∧-inversion, left** (Towsner §19.3): replace `φ ⋏ ψ` by `φ`, same `(α,k,d,c)`. -/
theorem andInvL {φ ψ : Form} : ∀ {α e k d c Γ}, Zekd α e k d c Γ → (φ ⋏ ψ) ∈ Γ →
    Zekd α e k d c (insert φ (Γ.erase (φ ⋏ ψ))) := by
  intro α e k d c Γ dd
  induction dd with
  | @axL α e k d c Γ ar r v hp hn =>
      intro _
      refine Zekd.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @verumR α e k d c Γ h =>
      intro _
      exact Zekd.verumR (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩))
  | @trueRel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      intro _
      exact Zekd.trueRel r v htrue hτ hαNF (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @trueNrel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      intro _
      exact Zekd.trueNrel r v htrue hτ hαNF (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @wk α e k d c Δ Γ hsub _ ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zekd.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zekd.wk ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e k d c Δ Γ hβ hβNF hαNF hτ hsub _ ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zekd.weak hβ hβNF hαNF hτ
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zekd.weak hβ hβNF hαNF hτ ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @andI α βφ' βψ' e k d c Γ₀ φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ dφ _ ihφ ihψ =>
      intro hmem
      by_cases hhd : (φ' ⋏ ψ') = (φ ⋏ ψ)
      · obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp hhd.symm
        rw [Finset.erase_insert_eq_erase]
        by_cases hh : (φ ⋏ ψ) ∈ Γ₀
        · exact Zekd.weak hβφ hβφNF hαNF hτφ (princAllSub (φ ⋏ ψ) _ Γ₀)
            (ihφ (Finset.mem_insert_of_mem hh))
        · rw [Finset.erase_eq_of_notMem hh]
          exact Zekd.weak hβφ hβφNF hαNF hτφ (Finset.Subset.refl _) dφ
      · have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have Pφ := Zekd.wk (inv1Push (φ ⋏ ψ) _ φ' Γ₀) (ihφ (Finset.mem_insert_of_mem hmem0))
        have Pψ := Zekd.wk (inv1Push (φ ⋏ ψ) _ ψ' Γ₀) (ihψ (Finset.mem_insert_of_mem hmem0))
        exact Zekd.wk (inv1Pull (φ ⋏ ψ) _ hhd Γ₀)
          (Zekd.andI φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ Pφ Pψ)
  | @orI α β e k d c Γ₀ φ' ψ' hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (φ' ⋎ ψ') ≠ (φ ⋏ ψ) := by intro h; simp [Vee.vee, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zekd.wk (inv1Push2 (φ ⋏ ψ) _ φ' ψ' Γ₀)
        (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0)))
      exact Zekd.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zekd.orI φ' ψ' hβ hβNF hαNF hτ P)
  | @allω α e k d c Γ₀ χ β hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (∀⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [UnivQuantifier.all, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zekd (β n) e (max k n) d c (insert (χ/[nm n]) (insert φ (Γ₀.erase (φ ⋏ ψ)))) :=
        fun n => Zekd.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zekd.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zekd.allω χ β hβ hβNF hαNF hτ key)
  | @exI α β e k d c Γ₀ χ n hβ hβNF hαNF hτ hbound _ ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zekd.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zekd.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zekd.exI χ n hβ hβNF hαNF hτ hbound P)
  | @cut α βφ' βψ' e k d c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zekd.wk (inv1Push (φ ⋏ ψ) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zekd.wk (inv1Push (φ ⋏ ψ) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zekd.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ P₁ P₂

/-- **∧-inversion, right** (Towsner §19.3): replace `φ ⋏ ψ` by `ψ`, same `(α,k,d,c)`. -/
theorem andInvR {φ ψ : Form} : ∀ {α e k d c Γ}, Zekd α e k d c Γ → (φ ⋏ ψ) ∈ Γ →
    Zekd α e k d c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  intro α e k d c Γ dd
  induction dd with
  | @axL α e k d c Γ ar r v hp hn =>
      intro _
      refine Zekd.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @verumR α e k d c Γ h =>
      intro _
      exact Zekd.verumR (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩))
  | @trueRel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      intro _
      exact Zekd.trueRel r v htrue hτ hαNF (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @trueNrel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      intro _
      exact Zekd.trueNrel r v htrue hτ hαNF (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @wk α e k d c Δ Γ hsub _ ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zekd.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zekd.wk ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e k d c Δ Γ hβ hβNF hαNF hτ hsub _ ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zekd.weak hβ hβNF hαNF hτ
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zekd.weak hβ hβNF hαNF hτ ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @andI α βφ' βψ' e k d c Γ₀ φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ dψ ihφ ihψ =>
      intro hmem
      by_cases hhd : (φ' ⋏ ψ') = (φ ⋏ ψ)
      · obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp hhd.symm
        rw [Finset.erase_insert_eq_erase]
        by_cases hh : (φ ⋏ ψ) ∈ Γ₀
        · exact Zekd.weak hβψ hβψNF hαNF hτψ (princAllSub (φ ⋏ ψ) _ Γ₀)
            (ihψ (Finset.mem_insert_of_mem hh))
        · rw [Finset.erase_eq_of_notMem hh]
          exact Zekd.weak hβψ hβψNF hαNF hτψ (Finset.Subset.refl _) dψ
      · have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have Pφ := Zekd.wk (inv1Push (φ ⋏ ψ) _ φ' Γ₀) (ihφ (Finset.mem_insert_of_mem hmem0))
        have Pψ := Zekd.wk (inv1Push (φ ⋏ ψ) _ ψ' Γ₀) (ihψ (Finset.mem_insert_of_mem hmem0))
        exact Zekd.wk (inv1Pull (φ ⋏ ψ) _ hhd Γ₀)
          (Zekd.andI φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ Pφ Pψ)
  | @orI α β e k d c Γ₀ φ' ψ' hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (φ' ⋎ ψ') ≠ (φ ⋏ ψ) := by intro h; simp [Vee.vee, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zekd.wk (inv1Push2 (φ ⋏ ψ) _ φ' ψ' Γ₀)
        (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0)))
      exact Zekd.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zekd.orI φ' ψ' hβ hβNF hαNF hτ P)
  | @allω α e k d c Γ₀ χ β hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (∀⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [UnivQuantifier.all, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zekd (β n) e (max k n) d c (insert (χ/[nm n]) (insert ψ (Γ₀.erase (φ ⋏ ψ)))) :=
        fun n => Zekd.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zekd.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zekd.allω χ β hβ hβNF hαNF hτ key)
  | @exI α β e k d c Γ₀ χ n hβ hβNF hαNF hτ hbound _ ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zekd.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zekd.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zekd.exI χ n hβ hβNF hαNF hτ hbound P)
  | @cut α βφ' βψ' e k d c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zekd.wk (inv1Push (φ ⋏ ψ) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zekd.wk (inv1Push (φ ⋏ ψ) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zekd.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ P₁ P₂

/-- **∀-inversion** (Towsner §19.4) — the bound-critical one (the subformula bridge to `B` consumes it).
Result raises the **`k`-part** to `max k n₀` (`d` inert): the principal case's idempotent collapse
`max (max k n₀) n₀ = max k n₀` is exactly why the split index keeps `allInv` working. -/
theorem allInv {φ₀ : SyntacticSemiformula ℒₒᵣ 1} (n₀ : ℕ) :
    ∀ {α e k d c Γ}, Zekd α e k d c Γ → (∀⁰ φ₀) ∈ Γ →
      Zekd α e (max k n₀) d c (insert (φ₀/[nm n₀]) (Γ.erase (∀⁰ φ₀))) := by
  have hI0 : (φ₀/[nm n₀]) ≠ (∀⁰ φ₀) := Semiformula.ne_of_ne_complexity (by simp)
  intro α e k d c Γ dd
  induction dd with
  | @axL α e k d c Γ ar r v hp hn =>
      intro _
      refine Zekd.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @verumR α e k d c Γ h =>
      intro _
      exact Zekd.verumR (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩))
  | @trueRel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      intro _
      exact Zekd.trueRel r v htrue (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d)) hαNF
        (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @trueNrel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      intro _
      exact Zekd.trueNrel r v htrue (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d)) hαNF
        (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @wk α e k d c Δ Γ hsub _ ih =>
      intro hmem
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Zekd.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zekd.wk ?_ (Zekd.mono_k (by assumption) (le_max_left _ _))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e k d c Δ Γ hβ hβNF hαNF hτ hsub _ ih =>
      intro hmem
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Zekd.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d))
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zekd.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d)) ?_
          (Zekd.mono_k (by assumption) (le_max_left _ _))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @andI α βφ' βψ' e k d c Γ₀ φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro hmem
      have hhead : (φ' ⋏ ψ') ≠ (∀⁰ φ₀) := by intro h; simp [Wedge.wedge, UnivQuantifier.all] at h
      have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have Pφ := Zekd.wk (inv1Push (∀⁰ φ₀) _ φ' Γ₀) (ihφ (Finset.mem_insert_of_mem hmem0))
      have Pψ := Zekd.wk (inv1Push (∀⁰ φ₀) _ ψ' Γ₀) (ihψ (Finset.mem_insert_of_mem hmem0))
      exact Zekd.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Zekd.andI φ' ψ' hβφ hβψ hβφNF hβψNF hαNF
          (lt_of_lt_of_le hτφ (Nat.add_le_add_right (le_max_left _ _) d))
          (lt_of_lt_of_le hτψ (Nat.add_le_add_right (le_max_left _ _) d)) Pφ Pψ)
  | @orI α β e k d c Γ₀ φ' ψ' hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (φ' ⋎ ψ') ≠ (∀⁰ φ₀) := by intro h; simp [Vee.vee, UnivQuantifier.all] at h
      have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zekd.wk (inv1Push2 (∀⁰ φ₀) _ φ' ψ' Γ₀)
        (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0)))
      exact Zekd.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Zekd.orI φ' ψ' hβ hβNF hαNF (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d)) P)
  | @allω α e k d c Γ₀ χ β hβ hβNF hαNF hτ dd ih =>
      intro hmem
      by_cases hhd : (∀⁰ χ) = (∀⁰ φ₀)
      · obtain rfl := (Semiformula.all_inj _ _).mp hhd
        rw [Finset.erase_insert_eq_erase]
        by_cases hh : (∀⁰ χ) ∈ Γ₀
        · have h := ih n₀ (Finset.mem_insert_of_mem hh)
          rw [max_eq_left (le_max_right k n₀)] at h
          exact Zekd.weak (hβ n₀) (hβNF n₀) hαNF (hτ n₀) (princAllSub (∀⁰ χ) _ Γ₀) h
        · rw [Finset.erase_eq_of_notMem hh]
          exact Zekd.weak (hβ n₀) (hβNF n₀) hαNF (hτ n₀) (Finset.Subset.refl _) (dd n₀)
      · have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have key : ∀ n, Zekd (β n) e (max (max k n₀) n) d c
            (insert (χ/[nm n]) (insert (φ₀/[nm n₀]) (Γ₀.erase (∀⁰ φ₀)))) := by
          intro n
          have h := Zekd.wk (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
          rw [show max (max k n₀) n = max (max k n) n₀ from by omega]
          exact h
        exact Zekd.wk (inv1Pull (∀⁰ φ₀) _ hhd Γ₀)
          (Zekd.allω χ β hβ hβNF hαNF (fun n => lt_of_lt_of_le (hτ n) (by omega)) key)
  | @exI α β e k d c Γ₀ χ n hβ hβNF hαNF hτ hbound _ ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (∀⁰ φ₀) := by intro h; simp [ExsQuantifier.exs, UnivQuantifier.all] at h
      have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zekd.wk (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zekd.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Zekd.exI χ n hβ hβNF hαNF (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d))
          (le_trans hbound (hardy_monotone _ (Nat.add_le_add_right (le_max_left _ _) d))) P)
  | @cut α βφ' βψ' e k d c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zekd.wk (inv1Push (∀⁰ φ₀) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zekd.wk (inv1Push (∀⁰ φ₀) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zekd.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF
        (lt_of_lt_of_le hτφ (Nat.add_le_add_right (le_max_left _ _) d))
        (lt_of_lt_of_le hτψ (Nat.add_le_add_right (le_max_left _ _) d)) P₁ P₂

theorem lt_osucc {o : ONote} (h : o.NF) : o < osucc o :=
  lt_def.mpr (by rw [repr_osucc h]; exact lt_add_one _)

/-- **`osucc` strict monotonicity** (the §19.6 descent: `βᵢ < γ ⟹ osucc(α+βᵢ) < osucc(α+γ)`). -/
theorem osucc_lt_osucc {x y : ONote} (hx : x.NF) (hy : y.NF) (h : x < y) : osucc x < osucc y := by
  refine lt_def.mpr ?_
  rw [repr_osucc hx, repr_osucc hy, ← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
  exact Order.succ_lt_succ (lt_def.mp h)

/-- `x < y ⟹ x < osucc y` (NF). -/
theorem lt_osucc_of_lt {x y : ONote} (hy : y.NF) (h : x < y) : x < osucc y :=
  lt_trans h (lt_osucc hy)

/-! #### Ordinal/`norm` bookkeeping for §19.6/§19.7 (copied from `BoundedZinfty`; all axiom-clean). -/

theorem add_lt_add_left_NF {α γ' γ : ONote} (hαNF : α.NF) (hγ'NF : γ'.NF) (hγNF : γ.NF)
    (h : γ' < γ) : α + γ' < α + γ := by
  haveI := hαNF; haveI := hγ'NF; haveI := hγNF
  exact lt_def.mpr (by rw [repr_add, repr_add]; exact (add_lt_add_iff_left _).mpr (lt_def.mp h))

theorem le_add_left_NF {α γ : ONote} (hαNF : α.NF) (hγNF : γ.NF) : γ ≤ α + γ := by
  haveI := hαNF; haveI := hγNF
  exact le_def.mpr (by rw [repr_add]; exact le_add_self)

theorem le_add_right_NF {α γ : ONote} (hαNF : α.NF) (hγNF : γ.NF) : α ≤ α + γ := by
  haveI := hαNF; haveI := hγNF
  exact le_def.mpr (by rw [repr_add]; exact le_self_add)

/-- **The §19.6 descent step**, assembled: `γ' < γ ⟹ osucc (α + γ') < osucc (α + γ)`. -/
theorem add_osucc_descent {α γ' γ : ONote} (hαNF : α.NF) (hγ'NF : γ'.NF) (hγNF : γ.NF)
    (h : γ' < γ) : osucc (α + γ') < osucc (α + γ) :=
  osucc_lt_osucc (ONote.add_nf α γ') (ONote.add_nf α γ) (add_lt_add_left_NF hαNF hγ'NF hγNF h)

@[simp] theorem norm_omegaPow {α : ONote} : norm (oadd α 1 0) = max (norm α) 1 := by
  simp [norm_oadd]

theorem norm_addAux_le (e : ONote) (n : ℕ+) (r : ONote) :
    norm (addAux e n r) ≤ max (norm e) (n : ℕ) + norm r := by
  unfold addAux
  match r with
  | 0 => simp only [norm_oadd, norm_zero]; omega
  | oadd e' n' a' =>
    simp only []
    rcases ONote.cmp e e' with _ | _ | _ <;>
      simp only [norm_oadd, PNat.add_coe] <;> omega

theorem norm_add_le : ∀ {α : ONote}, α.NF → ∀ {γ : ONote}, γ.NF →
    norm (α + γ) ≤ norm α + norm γ := by
  intro α
  induction α with
  | zero => intro _ γ _; simp
  | oadd e n a ihe iha =>
    intro hα γ hγ
    have ha : a.NF := hα.snd
    haveI := ha; haveI := hγ
    have iha' : norm (a + γ) ≤ norm a + norm γ := iha ha hγ
    rw [oadd_add]
    rcases hr : a + γ with _ | ⟨e', n', a'⟩
    · simp only [addAux, norm_oadd, norm_zero]; omega
    · rw [hr] at iha'
      simp only [norm_oadd] at iha'
      simp only [addAux]
      rcases hcmp : ONote.cmp e e' with _ | _ | _
      · simp only [norm_oadd]; omega
      · have hee : e = e' := eq_of_cmp_eq hcmp
        have hge : Ordinal.omega0 ^ ONote.repr e ≤ ONote.repr (a + γ) := by
          rw [hr, hee]; exact omega0_le_oadd e' n' a'
        have hra : ONote.repr a < Ordinal.omega0 ^ ONote.repr e := hα.snd'.repr_lt
        have hgγ : Ordinal.omega0 ^ ONote.repr e ≤ ONote.repr γ := by
          by_contra hlt
          push Not at hlt
          have : ONote.repr a + ONote.repr γ < Ordinal.omega0 ^ ONote.repr e :=
            (Ordinal.isPrincipal_add_omega0_opow (ONote.repr e)) hra hlt
          rw [repr_add] at hge
          exact absurd (lt_of_le_of_lt hge this) (lt_irrefl _)
        have habs : a + γ = γ := by
          have : ONote.repr (a + γ) = ONote.repr γ := by
            rw [repr_add]; exact Ordinal.add_of_omega0_opow_le hra hgγ
          exact repr_inj.mp this
        have hnγ : norm γ = max (norm e') (max (n':ℕ) (norm a')) := by
          rw [← habs, hr]; simp [norm_oadd]
        simp only [norm_oadd, PNat.add_coe]; omega
      · simp only [norm_oadd]; omega

/-- **∧/∨ cut reduction, conjunction case** (Towsner §19.5). -/
theorem cutReduceConj {a b : Form} {c k d : ℕ} {α β δ e : ONote} {Γ : Seq}
    (ha : a.complexity < c) (hb : b.complexity < c)
    (hαδ : α < δ) (hβδ : β < δ) (hαNF : α.NF) (hβNF : β.NF) (hδNF : δ.NF)
    (hτα : norm α < k + d) (hτβ : norm β < k + d) (hτδ : norm δ < k + d)
    (hC : Zekd α e k d c (insert (a ⋏ b) Γ)) (hNC : Zekd β e k d c (insert (∼a ⋎ ∼b) Γ)) :
    Zekd (osucc δ) e k d c Γ := by
  have hA : Zekd α e k d c (insert a Γ) := Zekd.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hC.andInvL (Finset.mem_insert_self _ _))
  have hB : Zekd α e k d c (insert b Γ) := Zekd.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hC.andInvR (Finset.mem_insert_self _ _))
  have hNab : Zekd β e k d c (insert (∼a) (insert (∼b) Γ)) := Zekd.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hNC.orInv (Finset.mem_insert_self _ _))
  have cutA : Zekd δ e k d c (insert (∼b) Γ) :=
    Zekd.cut a ha hαδ hβδ hαNF hβNF hδNF hτα hτβ
      (Zekd.wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) hA) hNab
  exact Zekd.cut b hb (lt_trans hαδ (lt_osucc hδNF)) (lt_osucc hδNF) hαNF hδNF (osucc_NF hδNF)
    hτα hτδ hB cutA

/-- **∧/∨ cut reduction, disjunction case** (dual). -/
theorem cutReduceDisj {a b : Form} {c k d : ℕ} {α β δ e : ONote} {Γ : Seq}
    (ha : a.complexity < c) (hb : b.complexity < c)
    (hαδ : α < δ) (hβδ : β < δ) (hαNF : α.NF) (hβNF : β.NF) (hδNF : δ.NF)
    (hτα : norm α < k + d) (hτβ : norm β < k + d) (hτδ : norm δ < k + d)
    (hC : Zekd α e k d c (insert (a ⋎ b) Γ)) (hNC : Zekd β e k d c (insert (∼a ⋏ ∼b) Γ)) :
    Zekd (osucc δ) e k d c Γ := by
  have hAB : Zekd α e k d c (insert a (insert b Γ)) := Zekd.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hC.orInv (Finset.mem_insert_self _ _))
  have hNa : Zekd β e k d c (insert (∼a) Γ) := Zekd.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hNC.andInvL (Finset.mem_insert_self _ _))
  have hNb : Zekd β e k d c (insert (∼b) Γ) := Zekd.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hNC.andInvR (Finset.mem_insert_self _ _))
  have cutA : Zekd δ e k d c (insert b Γ) :=
    Zekd.cut a ha hαδ hβδ hαNF hβNF hδNF hτα hτβ hAB
      (Zekd.wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) hNa)
  exact Zekd.cut b hb (lt_osucc hδNF) (lt_trans hβδ (lt_osucc hδNF)) hδNF hβNF (osucc_NF hδNF)
    hτδ hτβ cutA hNb

/-- Sequent weakening (height-preserving). -/
theorem weakening {α e k d c Δ Γ} (hsub : Δ ⊆ Γ) (dd : Zekd α e k d c Δ) : Zekd α e k d c Γ :=
  Zekd.wk hsub dd

end Zekd

/-! ### `ZekdProv` — the `Provable`-style wrapper (bound-as-upper-bound)

`Zekd` carries an *exact* derivation ordinal, so every ordinal-raise (e.g. `wk`'s
`γ ↦ osucc(α+γ)` in cut-elimination) needs `NF` of the source. The wrapper bundles an upper
bound + the source's `NF`, so the `≤`-slack absorbs the `osucc`/`+1` bookkeeping uniformly and
`NF` is always available. This is the surface §19.6 `cutReduceAll` is stated over (matching the
unbounded `Zinfty.lean Provable`). -/
def ZekdProv (α e : ONote) (k d c : ℕ) (Γ : Seq) : Prop :=
  ∃ α', α' ≤ α ∧ α'.NF ∧ norm α' < k + d ∧ Zekd α' e k d c Γ

namespace ZekdProv

/-- Monotonicity in `α` (≤), `k`, `d`, `c` (the control `e` is raised separately by `mono_e`,
which carries a budget side condition). The carried norm bound `norm α' < k+d` rides up to `k'+d'`. -/
theorem mono {α β e : ONote} {k d c k' d' c' : ℕ} {Γ : Seq}
    (hα : α ≤ β) (hk : k ≤ k') (hd : d ≤ d') (hc : c ≤ c') :
    ZekdProv α e k d c Γ → ZekdProv β e k' d' c' Γ := by
  rintro ⟨α', hα', hNF, hnorm, D⟩
  exact ⟨α', le_trans hα' hα, hNF, by omega, ((D.mono_k hk).mono_d hd).mono_c hc⟩

/-- Control-ordinal raising at the wrapper level. -/
theorem mono_e {α e e' : ONote} {k d c : ℕ} {Γ : Seq}
    (heNF : e.NF) (he'NF : e'.NF) (hlt : e < e') (hbudget : norm e ≤ k + d) :
    ZekdProv α e k d c Γ → ZekdProv α e' k d c Γ := by
  rintro ⟨α', hα', hNF, hnorm, D⟩
  exact ⟨α', hα', hNF, hnorm, D.mono_e heNF he'NF hlt hbudget⟩

/-- Sequent weakening. -/
theorem weakening {α e : ONote} {k d c : ℕ} {Γ Δ : Seq} (h : Γ ⊆ Δ) :
    ZekdProv α e k d c Γ → ZekdProv α e k d c Δ := by
  rintro ⟨α', hα', hNF, hnorm, D⟩
  exact ⟨α', hα', hNF, hnorm, D.wk h⟩

/-- Respect set-equality of sequents. -/
theorem cast {α e : ONote} {k d c : ℕ} {Γ Δ : Seq} (e0 : Γ = Δ) :
    ZekdProv α e k d c Γ → ZekdProv α e k d c Δ := fun h => e0 ▸ h

/-- Lift a raw `Zekd` derivation (NF ordinal + norm bound) into the wrapper. -/
theorem of {α e : ONote} {k d c : ℕ} {Γ : Seq} (hNF : α.NF) (hnorm : norm α < k + d)
    (D : Zekd α e k d c Γ) : ZekdProv α e k d c Γ := ⟨α, le_refl _, hNF, hnorm, D⟩

end ZekdProv

/-! ### §19.6 ∀/∃ cut reduction `cutReduceAllAux` — **norm-budget half PROVED** (lap 12, axiom-clean)

The induction core of Towsner §19.6, ported from `src/Zinfty.lean:854 cutReduceAllAux` to the
control-ordinal witness-bounded calculus over the **norm-carrying** `ZekdProv` wrapper. Cut the
∀-inversion family `fam` (over `φ`, control `e`, index `(k₀,dd₀)`) against an ∃-side derivation
`D : Zekd γ e k dd c Δ` containing `∃∼φ`, producing a `Zekd`-derivation of `Δ.erase(∃∼φ) ∪ Γ` at
ordinal `osucc(α+γ)`, control `e` (inert), index `(k, dd+norm α+1)`.

⚠️ **SCOPE (lap-12, see `ANALYSIS-…-cutelim-k-threading.md` ADDENDUM 7).** This statement takes `fam`
at the **FIXED** index `k₀` and keeps `e` inert — proving the NORM-budget half cleanly (the lap-6→11
friction), but it is **NOT yet feedable by `cutReduceAll`**: `allInv` produces the ∀-family at the
*running* index `max k₀ n` (the n-th ω-premise lives higher), and a derivation with witnesses up to
`hardy e (max k₀ n + dd₀)` does NOT exist at the smaller fixed index `k₀`. Closing the **witness-budget**
half needs `fam` at `max k₀ n` AND the control `e` *raised* — the numeric single-index bound is provably
FALSE (`h_{βₙ#ω}(max{k,n}) ≰ max{h_{β#ω}(k),n}` for large `n`). The literature-correct fix is Buchholz
**operator-controlled** derivations (on disk: `papers/buchholz-beweistheorie-skriptum.pdf`). This proof
is the reusable **norm-machinery + structural port**: every case carries to the `H`-calculus verbatim
except the `exI`/`allω` witness side-condition (`n ≤ hardy e (k+d)` ⤳ `n ∈ H`). Banked, off the live chain.

**Norm-budget resolution (the lap-6→11 friction; see ADDENDUM 6).** The historical blocker — the
commuting `allω` norm budget — is closed by THREE coupled moves:
1. **norm-carrying wrapper** `ZekdProv α e k d c Γ := ∃ α', α'≤α ∧ α'.NF ∧ norm α'<k+d ∧ Zekd α' …`,
   so the IH EXPOSES `norm α' < (its k)+(its d)` — exactly the `allω` premise's norm budget (a plain
   `α'≤α` wrapper threw this away, since `norm` is not `≤`-monotone — the 5-lap wall);
2. **thread `norm γ < k+dd`** through the induction (each case's child budget is supplied by that rule's
   own `hτ` side-condition; used only to bound `norm(osucc(α+γ))` at the result);
3. **d-bump `dd ↦ dd+norm α+1`** — the `+1` absorbs the `osucc`, giving STRICT budgets everywhere
   (and killing the leaf `k+dd=0` edge). Control `e` stays inert (witnesses stay `≤ hardy e (·)`); it is
   raised only at the top-level cut in `cutReduceAll` via `mono_e`.

`induction D` generalizes `e k dd c Δ` (and reverts `fam`/`heNF`/`hφc`, re-supplied per-case via the
IH), keeping `α k₀ dd₀ Γ φ hαNF` fixed — the `allInv` precedent scaled to carry the external family. -/
set_option maxHeartbeats 1600000 in
theorem cutReduceAllAux {φ : SyntacticSemiformula ℒₒᵣ 1} {c k₀ dd₀ : ℕ} {α e : ONote} {Γ : Seq}
    (hφc : φ.complexity < c) (hαNF : α.NF) (heNF : e.NF)
    (fam : ∀ n, Zekd α e k₀ dd₀ c (insert (φ/[nm n]) Γ)) :
    ∀ {γ : ONote} {k dd : ℕ} {Δ : Seq}, Zekd γ e k dd c Δ → γ.NF → norm γ < k + dd →
      k₀ ≤ k → dd₀ ≤ dd → (∃⁰ ∼φ) ∈ Δ →
      ZekdProv (osucc (α + γ)) e k (dd + norm α + 1) c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  intro γ k dd Δ D
  induction D with
  | axL r v hp hn =>
      intro hγNF hγb hk hdd hmem
      exact ⟨0, le_def.mpr (by simp), NF.zero, by simp only [norm_zero]; omega, Zekd.axL r v
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩))
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩))⟩
  | verumR h =>
      intro hγNF hγb hk hdd hmem
      exact ⟨0, le_def.mpr (by simp), NF.zero, by simp only [norm_zero]; omega, Zekd.verumR
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩))⟩
  | trueRel r v htrue hτ hαNF' hmemA =>
      intro hγNF hγb hk hdd hmem
      refine ⟨_, le_trans (Zekd.le_add_left_NF hαNF hγNF) (le_of_lt (Zekd.lt_osucc (ONote.add_nf α _))),
        hγNF, by omega, Zekd.trueRel r v htrue (by omega) hγNF
          (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmemA⟩))⟩
  | trueNrel r v htrue hτ hαNF' hmemA =>
      intro hγNF hγb hk hdd hmem
      refine ⟨_, le_trans (Zekd.le_add_left_NF hαNF hγNF) (le_of_lt (Zekd.lt_osucc (ONote.add_nf α _))),
        hγNF, by omega, Zekd.trueNrel r v htrue (by omega) hγNF
          (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmemA⟩))⟩
  | @wk γ' e' k' dd' c' Δsub Δsup hsub D' ih =>
      intro hγNF hγb hk hdd hmem
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact (ih hφc heNF fam hγNF hγb hk hdd hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)
      · refine ⟨γ', le_trans (Zekd.le_add_left_NF hαNF hγNF) (le_of_lt (Zekd.lt_osucc (ONote.add_nf α _))),
          hγNF, by omega, (D'.mono_d (by omega)).wk (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩
  | @weak γ' β e' k' dd' c' Δsub Δsup hβ hβNF hαNF' hτ hsub D' ih =>
      intro hγNF hγb hk hdd hmem
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact ((ih hφc heNF fam hβNF (by omega) hk hdd hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)).mono
          (le_of_lt (Zekd.add_osucc_descent hαNF hβNF hγNF hβ)) le_rfl le_rfl le_rfl
      · refine ⟨β, le_of_lt (lt_of_lt_of_le hβ (le_trans (Zekd.le_add_left_NF hαNF hγNF)
          (le_of_lt (Zekd.lt_osucc (ONote.add_nf α _))))), hβNF, by omega,
          (D'.mono_d (by omega)).wk (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩
  | @andI γ' βφ βψ e' k' dd' c' Γ₀ ψ₁ ψ₂ hβφ hβψ hβφNF hβψNF hαNF' hτφ hτψ dφ dψ ihφ ihψ =>
      intro hγNF hγb hk hdd hmem
      have hhead : (ψ₁ ⋏ ψ₂) ≠ (∃⁰ ∼φ) := by intro h; simp [Wedge.wedge, ExsQuantifier.exs] at h
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      obtain ⟨aφ, haφle, haφNF, haφnorm, Dφ⟩ := ihφ hφc heNF fam hβφNF (by omega) hk hdd
        (Finset.mem_insert_of_mem hmem0)
      obtain ⟨aψ, haψle, haψNF, haψnorm, Dψ⟩ := ihψ hφc heNF fam hβψNF (by omega) hk hdd
        (Finset.mem_insert_of_mem hmem0)
      have hsuccNF : (osucc (α + γ')).NF := osucc_NF (ONote.add_nf α γ')
      have Dφ' : Zekd aφ e' k' (dd' + norm α + 1) c' (insert ψ₁ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Dφ.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      have Dψ' : Zekd aψ e' k' (dd' + norm α + 1) c' (insert ψ₂ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Dψ.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      have hAnd : Zekd (osucc (α + γ')) e' k' (dd' + norm α + 1) c'
          (insert (ψ₁ ⋏ ψ₂) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Zekd.andI ψ₁ ψ₂
          (lt_of_le_of_lt haφle (Zekd.add_osucc_descent hαNF hβφNF hγNF hβφ))
          (lt_of_le_of_lt haψle (Zekd.add_osucc_descent hαNF hβψNF hγNF hβψ))
          haφNF haψNF hsuccNF haφnorm haψnorm Dφ' Dψ'
      refine ZekdProv.of hsuccNF
        (lt_of_le_of_lt norm_osucc_le (by have := Zekd.norm_add_le hαNF hγNF; omega))
        (hAnd.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl ⟨hhead, Or.inl rfl⟩
          · tauto))
  | @orI γ' β e' k' dd' c' Γ₀ ψ₁ ψ₂ hβ hβNF hαNF' hτ dχ ih =>
      intro hγNF hγb hk hdd hmem
      have hhead : (ψ₁ ⋎ ψ₂) ≠ (∃⁰ ∼φ) := by intro h; simp [Vee.vee, ExsQuantifier.exs] at h
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      obtain ⟨a, hale, haNF, hanorm, Da⟩ := ih hφc heNF fam hβNF (by omega) hk hdd
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))
      have hsuccNF : (osucc (α + γ')).NF := osucc_NF (ONote.add_nf α γ')
      have Da' : Zekd a e' k' (dd' + norm α + 1) c'
          (insert ψ₁ (insert ψ₂ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ))) :=
        Da.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      have hOr : Zekd (osucc (α + γ')) e' k' (dd' + norm α + 1) c'
          (insert (ψ₁ ⋎ ψ₂) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Zekd.orI ψ₁ ψ₂ (lt_of_le_of_lt hale (Zekd.add_osucc_descent hαNF hβNF hγNF hβ))
          haNF hsuccNF hanorm Da'
      refine ZekdProv.of hsuccNF
        (lt_of_le_of_lt norm_osucc_le (by have := Zekd.norm_add_le hαNF hγNF; omega))
        (hOr.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl ⟨hhead, Or.inl rfl⟩
          · tauto))
  | @allω γ' e' k' dd' c' Γ₀ χ β hβ hβNF hαNF' hτ dχ ih =>
      intro hγNF hγb hk hdd hmem
      have hhead : (∀⁰ χ) ≠ (∃⁰ ∼φ) := by intro h; simp [UnivQuantifier.all, ExsQuantifier.exs] at h
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have hsuccNF : (osucc (α + γ')).NF := osucc_NF (ONote.add_nf α γ')
      have ihn : ∀ n, ZekdProv (osucc (α + β n)) e' (max k' n) (dd' + norm α + 1) c'
          (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
        intro n
        exact (ih n hφc heNF fam (hβNF n) (by have := hτ n; omega)
          (le_trans hk (le_max_left _ _)) hdd (Finset.mem_insert_of_mem hmem0)).weakening (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      choose β' hβ'le hβ'NF hβ'norm Dβ' using ihn
      have hAll : Zekd (osucc (α + γ')) e' k' (dd' + norm α + 1) c'
          (insert (∀⁰ χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Zekd.allω χ β'
          (fun n => lt_of_le_of_lt (hβ'le n) (Zekd.add_osucc_descent hαNF (hβNF n) hγNF (hβ n)))
          hβ'NF hsuccNF hβ'norm Dβ'
      refine ZekdProv.of hsuccNF
        (lt_of_le_of_lt norm_osucc_le (by have := Zekd.norm_add_le hαNF hγNF; omega))
        (hAll.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl ⟨hhead, Or.inl rfl⟩
          · tauto))
  | @exI γ' β e' k' dd' c' Γ₀ χ n hβ hβNF hαNF' hτ hbound dχ ih =>
      intro hγNF hγb hk hdd hmem
      have hsuccNF : (osucc (α + γ')).NF := osucc_NF (ONote.add_nf α γ')
      by_cases hhd : (∃⁰ χ) = (∃⁰ ∼φ)
      · -- principal exI: χ = ∼φ; cut `fam n` against the ∃-premise at the cut formula `φ/[nm n]`.
        have hχ : χ = ∼φ := by have := hhd; simpa [ExsQuantifier.exs] using this
        subst hχ
        rw [Finset.erase_insert_eq_erase]
        have hNeg : (∼φ)/[nm n] = ∼(φ/[nm n]) := by simp
        have hcompl : (φ/[nm n]).complexity < c' := by simpa using hφc
        have hαlt : α < osucc (α + γ') :=
          lt_of_le_of_lt (Zekd.le_add_right_NF hαNF hγNF) (Zekd.lt_osucc (ONote.add_nf α γ'))
        have famn : Zekd α e' k' (dd' + norm α + 1) c'
            (insert (φ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          (((fam n).mono_k hk).mono_d (by omega)).wk (by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_union] at hx ⊢; tauto)
        by_cases hd : (∃⁰ ∼φ) ∈ Γ₀
        · obtain ⟨a, hale, haNF, hanorm, Da⟩ := ih hφc heNF fam hβNF (by omega) hk hdd
            (Finset.mem_insert_of_mem hd)
          have Da' : Zekd a e' k' (dd' + norm α + 1) c'
              (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
            Da.wk (by
              intro x hx
              simp only [hNeg, Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
          have hCut : Zekd (osucc (α + γ')) e' k' (dd' + norm α + 1) c' (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) :=
            Zekd.cut (φ/[nm n]) hcompl hαlt
              (lt_of_le_of_lt hale (Zekd.add_osucc_descent hαNF hβNF hγNF hβ))
              hαNF haNF hsuccNF (by omega) hanorm famn Da'
          exact ZekdProv.of hsuccNF
            (lt_of_le_of_lt norm_osucc_le (by have := Zekd.norm_add_le hαNF hγNF; omega)) hCut
        · have Dβ' : Zekd β e' k' (dd' + norm α + 1) c'
              (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
            (dχ.mono_d (by omega)).wk (by
              intro x hx
              simp only [hNeg, Finset.mem_insert] at hx
              simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
              rcases hx with rfl | hxΓ₀
              · exact Or.inl rfl
              · exact Or.inr (Or.inl ⟨fun e0 => hd (e0 ▸ hxΓ₀), hxΓ₀⟩))
          have hCut : Zekd (osucc (α + γ')) e' k' (dd' + norm α + 1) c' (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) :=
            Zekd.cut (φ/[nm n]) hcompl hαlt
              (lt_of_lt_of_le hβ (le_trans (Zekd.le_add_left_NF hαNF hγNF)
                (le_of_lt (Zekd.lt_osucc (ONote.add_nf α γ')))))
              hαNF hβNF hsuccNF (by omega) (by omega) famn Dβ'
          exact ZekdProv.of hsuccNF
            (lt_of_le_of_lt norm_osucc_le (by have := Zekd.norm_add_le hαNF hγNF; omega)) hCut
      · have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        obtain ⟨a, hale, haNF, hanorm, Da⟩ := ih hφc heNF fam hβNF (by omega) hk hdd
          (Finset.mem_insert_of_mem hmem0)
        have Da' : Zekd a e' k' (dd' + norm α + 1) c' (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          Da.wk (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
        have hExI : Zekd (osucc (α + γ')) e' k' (dd' + norm α + 1) c'
            (insert (∃⁰ χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          Zekd.exI χ n (lt_of_le_of_lt hale (Zekd.add_osucc_descent hαNF hβNF hγNF hβ))
            haNF hsuccNF hanorm (le_trans hbound (hardy_monotone _ (by omega))) Da'
        refine ZekdProv.of hsuccNF
          (lt_of_le_of_lt norm_osucc_le (by have := Zekd.norm_add_le hαNF hγNF; omega))
          (hExI.wk (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
            rcases hx with rfl | hx
            · exact Or.inl ⟨hhd, Or.inl rfl⟩
            · tauto))
  | @cut γ' βφ βψ e' k' dd' c' Γ₀ χ hχc hβφ hβψ hβφNF hβψNF hαNF' hτφ hτψ d₁ d₂ ih₁ ih₂ =>
      intro hγNF hγb hk hdd hmem
      obtain ⟨a₁, ha₁le, ha₁NF, ha₁norm, D₁⟩ := ih₁ hφc heNF fam hβφNF (by omega) hk hdd
        (Finset.mem_insert_of_mem hmem)
      obtain ⟨a₂, ha₂le, ha₂NF, ha₂norm, D₂⟩ := ih₂ hφc heNF fam hβψNF (by omega) hk hdd
        (Finset.mem_insert_of_mem hmem)
      have hsuccNF : (osucc (α + γ')).NF := osucc_NF (ONote.add_nf α γ')
      have D₁' : Zekd a₁ e' k' (dd' + norm α + 1) c' (insert χ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        D₁.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      have D₂' : Zekd a₂ e' k' (dd' + norm α + 1) c' (insert (∼χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        D₂.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      have hCut : Zekd (osucc (α + γ')) e' k' (dd' + norm α + 1) c' (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) :=
        Zekd.cut χ hχc
          (lt_of_le_of_lt ha₁le (Zekd.add_osucc_descent hαNF hβφNF hγNF hβφ))
          (lt_of_le_of_lt ha₂le (Zekd.add_osucc_descent hαNF hβψNF hγNF hβψ))
          ha₁NF ha₂NF hsuccNF ha₁norm ha₂norm D₁' D₂'
      exact ZekdProv.of hsuccNF
        (lt_of_le_of_lt norm_osucc_le (by have := Zekd.norm_add_le hαNF hγNF; omega)) hCut

/-! ### Path-B hard probe: the PA-induction leaf's witness side condition

The unbounded `PXFc` induction-axiom construction in `EmbeddingBound.metaInduction_cong_bdd`
uses an `∃`-introduction with witness `n` at the `n`-th step of the cut tower.  In `Zekd` that
move is legal only when the witness is bounded by `hardy e (k+d)`.

These lemmas isolate the decisive arithmetic.  A fixed numeric index cannot support all
witnesses, but the running `allω` index `max k n` can.  So the induction leaf is not blocked
at the witness side condition; any remaining difficulty is the structural port of the finite
EM/cut/value-substitution tower.
-/

/-- A fixed numeric index cannot bound the witnesses `n` needed by the induction cut tower. -/
theorem inductionLeaf_fixedIndex_witnessBound_impossible (e : ONote) (k d : ℕ) :
    ¬ ∀ n : ℕ, n ≤ hardy e (k + d) := by
  intro h
  have := h (hardy e (k + d) + 1)
  omega

/-- The `n`-th `allω` premise runs at index `max k n`, which is large enough to pay for
the `∃`-witness `n`. -/
theorem inductionLeaf_runningIndex_witnessBound (e : ONote) (k d n : ℕ) :
    n ≤ hardy e (max k n + d) :=
  le_trans (by omega) (le_hardy e (max k n + d))

/-- The actual `Zekd.exI` move needed in the induction-axiom leaf is legal at the running
index.  This is the local replacement for the unbounded proof's free `PXFc.exI` step. -/
theorem inductionLeaf_exI_runningIndex_probe {α β e : ONote} {k d c n : ℕ} {Γ : Seq}
    {φ : SyntacticSemiformula ℒₒᵣ 1}
    (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < max k n + d)
    (D : Zekd β e (max k n) d c (insert (φ/[nm n]) Γ)) :
    Zekd α e (max k n) d c (insert (∃⁰ φ) Γ) :=
  Zekd.exI φ n hβ hβNF hαNF hτ (inductionLeaf_runningIndex_witnessBound e k d n) D

/-! #### Bounded embedding leaves: value-congruent atomic closure -/

/-- The standard value of a closed arithmetic term, in the evaluator used by `atomTrue`. -/
noncomputable abbrev stdClosedVal (t : SyntacticTerm ℒₒᵣ) : ℕ :=
  Semiterm.val (Arithmetic.standardModel ℕ) (fun _ => 0) (fun _ => 0) t

/-- The standard value of the numeral term `nm m` is `m`. -/
@[simp] lemma stdClosedVal_nm (m : ℕ) : stdClosedVal (nm m) = m := by
  simp [stdClosedVal, nm]

/-- Substitution-composition for extending an assignment by a numeral in the freed variable. -/
lemma embedding_subst_q_cons {n : ℕ} (w : Fin n → SyntacticTerm ℒₒᵣ) (m : ℕ) :
    (Rew.subst ![nm m]).comp (Rew.subst w).q = Rew.subst (nm m :> w) := by
  ext x
  · cases x using Fin.cases with
    | zero => simp [Rew.comp_app]
    | succ i => simp [Rew.comp_app]
  · simp [Rew.comp_app]

/-- Formula form of `embedding_subst_q_cons`. -/
lemma embedding_subst_q_cons_app {n : ℕ} (w : Fin n → SyntacticTerm ℒₒᵣ) (m : ℕ)
    (ψ : SyntacticSemiformula ℒₒᵣ (n + 1)) :
    ((Rew.subst w).q ▹ ψ)/[nm m] = Rew.subst (nm m :> w) ▹ ψ := by
  show Rew.subst ![nm m] ▹ ((Rew.subst w).q ▹ ψ) = Rew.subst (nm m :> w) ▹ ψ
  rw [← TransitiveRewriting.comp_app, embedding_subst_q_cons]

/-- Standard-value congruence for renamed terms, ported to the `Zekd` embedding probes. -/
lemma embedding_valm_subst_congr {n : ℕ} (w w' : Fin n → SyntacticTerm ℒₒᵣ)
    (hval : ∀ i, stdClosedVal (w i) = stdClosedVal (w' i))
    (t : SyntacticSemiterm ℒₒᵣ n) :
    stdClosedVal (Rew.subst w t) = stdClosedVal (Rew.subst w' t) := by
  simp only [stdClosedVal, Semiterm.val_substs]
  congr 1
  funext x; exact hval x

/-- Extending two value-equal assignments by the same numeral preserves pointwise value equality. -/
lemma embedding_valm_cons_nm_congr {n : ℕ} (w w' : Fin n → SyntacticTerm ℒₒᵣ) (m : ℕ)
    (hval : ∀ i, stdClosedVal (w i) = stdClosedVal (w' i)) :
    ∀ i, stdClosedVal ((nm m :> w) i) = stdClosedVal ((nm m :> w') i) := by
  intro i
  cases i using Fin.cases with
  | zero => simp
  | succ j => simpa using hval j

/-- Truth of a closed atomic relation only depends on the standard values of its terms. -/
lemma atomTrue_rel_congr {ar : ℕ} (r : (ℒₒᵣ).Rel ar)
    (v v' : Fin ar → SyntacticTerm ℒₒᵣ)
    (hval : ∀ i, stdClosedVal (v i) = stdClosedVal (v' i)) :
    atomTrue (Semiformula.rel r v) ↔ atomTrue (Semiformula.rel r v') := by
  have hv : (fun i => Semiterm.val (Arithmetic.standardModel ℕ) (fun _ => 0) (fun _ => 0) (v i))
      = (fun i => Semiterm.val (Arithmetic.standardModel ℕ) (fun _ => 0) (fun _ => 0) (v' i)) := by
    funext i; exact hval i
  simp only [atomTrue, Semiformula.eval_rel, hv]

/-- Truth of a closed negated atomic relation only depends on the standard values of its terms. -/
lemma atomTrue_nrel_congr {ar : ℕ} (r : (ℒₒᵣ).Rel ar)
    (v v' : Fin ar → SyntacticTerm ℒₒᵣ)
    (hval : ∀ i, stdClosedVal (v i) = stdClosedVal (v' i)) :
    atomTrue (Semiformula.nrel r v) ↔ atomTrue (Semiformula.nrel r v') := by
  have hv : (fun i => Semiterm.val (Arithmetic.standardModel ℕ) (fun _ => 0) (fun _ => 0) (v i))
      = (fun i => Semiterm.val (Arithmetic.standardModel ℕ) (fun _ => 0) (fun _ => 0) (v' i)) := by
    funext i; exact hval i
  simp only [atomTrue, Semiformula.eval_nrel, hv]

lemma atomTrue_nrel_iff_not_rel {ar : ℕ} (r : (ℒₒᵣ).Rel ar)
    (v : Fin ar → SyntacticTerm ℒₒᵣ) :
    atomTrue (Semiformula.nrel r v) ↔ ¬ atomTrue (Semiformula.rel r v) := by
  simp [atomTrue, Semiformula.eval_rel, Semiformula.eval_nrel]

lemma atomTrue_rel_iff_not_nrel {ar : ℕ} (r : (ℒₒᵣ).Rel ar)
    (v : Fin ar → SyntacticTerm ℒₒᵣ) :
    atomTrue (Semiformula.rel r v) ↔ ¬ atomTrue (Semiformula.nrel r v) := by
  simp [atomTrue, Semiformula.eval_rel, Semiformula.eval_nrel]

/--
Bounded value-congruent atomic closure, relation-positive side.

This is the `Zekd` base leaf needed by assignment-carrying embedding: if the sequent contains
`R(v)` and `¬R(v')`, and the closed term vectors have equal standard values, a bounded truth leaf
closes the sequent at any normal ordinal whose norm fits the current budget.
-/
theorem embedding_valueCongruentRelAtom_probe {α e : ONote} {k d c ar : ℕ} {Γ : Seq}
    (r : (ℒₒᵣ).Rel ar) (v v' : Fin ar → SyntacticTerm ℒₒᵣ)
    (hval : ∀ i, stdClosedVal (v i) = stdClosedVal (v' i))
    (hαNF : α.NF) (hτ : norm α < k + d)
    (hp : Semiformula.rel r v ∈ Γ) (hn : Semiformula.nrel r v' ∈ Γ) :
    Zekd α e k d c Γ := by
  by_cases hrel : atomTrue (Semiformula.rel r v)
  · exact Zekd.trueRel r v hrel hτ hαNF hp
  · have hrel' : ¬ atomTrue (Semiformula.rel r v') := by
      intro hv'
      exact hrel ((atomTrue_rel_congr r v v' hval).mpr hv')
    exact Zekd.trueNrel r v' ((atomTrue_nrel_iff_not_rel r v').mpr hrel') hτ hαNF hn

/--
Bounded value-congruent atomic closure, negated-relation-positive side.

This is the polarity twin of `embedding_valueCongruentRelAtom_probe`.
-/
theorem embedding_valueCongruentNrelAtom_probe {α e : ONote} {k d c ar : ℕ} {Γ : Seq}
    (r : (ℒₒᵣ).Rel ar) (v v' : Fin ar → SyntacticTerm ℒₒᵣ)
    (hval : ∀ i, stdClosedVal (v i) = stdClosedVal (v' i))
    (hαNF : α.NF) (hτ : norm α < k + d)
    (hp : Semiformula.nrel r v ∈ Γ) (hn : Semiformula.rel r v' ∈ Γ) :
    Zekd α e k d c Γ := by
  by_cases hnrel : atomTrue (Semiformula.nrel r v)
  · exact Zekd.trueNrel r v hnrel hτ hαNF hp
  · have hnrel' : ¬ atomTrue (Semiformula.nrel r v') := by
      intro hv'
      exact hnrel ((atomTrue_nrel_congr r v v' hval).mpr hv')
    exact Zekd.trueRel r v' ((atomTrue_rel_iff_not_nrel r v').mpr hnrel') hτ hαNF hn

/-- Substituted-term form of the bounded value-congruent relation atom leaf. -/
theorem embedding_valueCongruentRelSubstAtom_probe {α e : ONote} {k d c ar n : ℕ} {Γ : Seq}
    (r : (ℒₒᵣ).Rel ar) (w w' : Fin n → SyntacticTerm ℒₒᵣ)
    (v : Fin ar → SyntacticSemiterm ℒₒᵣ n)
    (hval : ∀ i, stdClosedVal (w i) = stdClosedVal (w' i))
    (hαNF : α.NF) (hτ : norm α < k + d)
    (hp : Semiformula.rel r (fun i => Rew.subst w (v i)) ∈ Γ)
    (hn : Semiformula.nrel r (fun i => Rew.subst w' (v i)) ∈ Γ) :
    Zekd α e k d c Γ :=
  embedding_valueCongruentRelAtom_probe r
    (fun i => Rew.subst w (v i)) (fun i => Rew.subst w' (v i))
    (fun i => embedding_valm_subst_congr w w' hval (v i)) hαNF hτ hp hn

/-- Substituted-term form of the bounded value-congruent negated-relation atom leaf. -/
theorem embedding_valueCongruentNrelSubstAtom_probe {α e : ONote} {k d c ar n : ℕ} {Γ : Seq}
    (r : (ℒₒᵣ).Rel ar) (w w' : Fin n → SyntacticTerm ℒₒᵣ)
    (v : Fin ar → SyntacticSemiterm ℒₒᵣ n)
    (hval : ∀ i, stdClosedVal (w i) = stdClosedVal (w' i))
    (hαNF : α.NF) (hτ : norm α < k + d)
    (hp : Semiformula.nrel r (fun i => Rew.subst w (v i)) ∈ Γ)
    (hn : Semiformula.rel r (fun i => Rew.subst w' (v i)) ∈ Γ) :
    Zekd α e k d c Γ :=
  embedding_valueCongruentNrelAtom_probe r
    (fun i => Rew.subst w (v i)) (fun i => Rew.subst w' (v i))
    (fun i => embedding_valm_subst_congr w w' hval (v i)) hαNF hτ hp hn

/-- Closed-term specialization of the value-congruent relation atom leaf. -/
theorem embedding_valueCongruentRelClosedTermAtom_probe
    {α e : ONote} {k d c ar : ℕ} {Γ : Seq}
    (r : (ℒₒᵣ).Rel ar) (s s' : SyntacticTerm ℒₒᵣ)
    (v : Fin ar → SyntacticSemiterm ℒₒᵣ 1)
    (hval : stdClosedVal s = stdClosedVal s')
    (hαNF : α.NF) (hτ : norm α < k + d)
    (hp : (Semiformula.rel r v)/[s] ∈ Γ)
    (hn : (Semiformula.nrel r v)/[s'] ∈ Γ) :
    Zekd α e k d c Γ := by
  refine embedding_valueCongruentRelSubstAtom_probe r ![s] ![s'] v ?_ hαNF hτ ?_ ?_
  · intro i
    cases i using Fin.cases with
    | zero => simpa using hval
    | succ j => exact Fin.elim0 j
  · simpa [Semiformula.rew_rel] using hp
  · simpa [Semiformula.rew_nrel] using hn

/-- Closed-term specialization of the value-congruent negated-relation atom leaf. -/
theorem embedding_valueCongruentNrelClosedTermAtom_probe
    {α e : ONote} {k d c ar : ℕ} {Γ : Seq}
    (r : (ℒₒᵣ).Rel ar) (s s' : SyntacticTerm ℒₒᵣ)
    (v : Fin ar → SyntacticSemiterm ℒₒᵣ 1)
    (hval : stdClosedVal s = stdClosedVal s')
    (hαNF : α.NF) (hτ : norm α < k + d)
    (hp : (Semiformula.nrel r v)/[s] ∈ Γ)
    (hn : (Semiformula.rel r v)/[s'] ∈ Γ) :
    Zekd α e k d c Γ := by
  refine embedding_valueCongruentNrelSubstAtom_probe r ![s] ![s'] v ?_ hαNF hτ ?_ ?_
  · intro i
    cases i using Fin.cases with
    | zero => simpa using hval
    | succ j => exact Fin.elim0 j
  · simpa [Semiformula.rew_nrel] using hp
  · simpa [Semiformula.rew_rel] using hn

/-- Constant-true base case for the bounded value-congruent EM engine. -/
theorem embedding_valueCongruentVerum_probe {α e : ONote} {k d c n : ℕ} {Γ : Seq}
    (w : Fin n → SyntacticTerm ℒₒᵣ)
    (hp : (Rew.subst w ▹ (⊤ : SyntacticSemiformula ℒₒᵣ n)) ∈ Γ) :
    Zekd α e k d c Γ :=
  Zekd.verumR (by simpa using hp)

/-- Constant-false base case for the bounded value-congruent EM engine. -/
theorem embedding_valueCongruentFalsum_probe {α e : ONote} {k d c n : ℕ} {Γ : Seq}
    (w' : Fin n → SyntacticTerm ℒₒᵣ)
    (hn : (∼(Rew.subst w' ▹ (⊥ : SyntacticSemiformula ℒₒᵣ n))) ∈ Γ) :
    Zekd α e k d c Γ :=
  Zekd.verumR (by simpa using hn)

/--
Bounded closed-term existential introduction, reduced to the genuine remaining EM/congruence premise.

This is the assignment-carrying embedding adapter for Foundation's `exs` rule: after an open witness term
has been closed by an assignment, its standard value `stdClosedVal s` is used as the numeral witness.
The only non-structural input is the value-congruent premise converting `ψ[s]` to `ψ[nm (stdClosedVal s)]`.
-/
theorem embedding_closedTermExI_of_valueCongruentEM_probe
    {βSrc βCong αCut αOut e : ONote} {k d c : ℕ} {Γ : Seq}
    {ψ : SyntacticSemiformula ℒₒᵣ 1} (s : SyntacticTerm ℒₒᵣ)
    (hψc : (ψ/[s]).complexity < c)
    (hSrcLt : βSrc < αCut) (hCongLt : βCong < αCut) (hCutLt : αCut < αOut)
    (hSrcNF : βSrc.NF) (hCongNF : βCong.NF) (hCutNF : αCut.NF) (hOutNF : αOut.NF)
    (hτSrc : norm βSrc < k + d) (hτCong : norm βCong < k + d)
    (hτCut : norm αCut < k + d)
    (hbound : stdClosedVal s ≤ hardy e (k + d))
    (dSrc : Zekd βSrc e k d c (insert (ψ/[s]) Γ))
    (dCong : Zekd βCong e k d c
      (insert (∼(ψ/[s])) (insert (ψ/[nm (stdClosedVal s)]) Γ))) :
    Zekd αOut e k d c (insert (∃⁰ ψ) Γ) := by
  have dSrc' : Zekd βSrc e k d c
      (insert (ψ/[s]) (insert (ψ/[nm (stdClosedVal s)]) Γ)) :=
    Zekd.wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) dSrc
  have dNumeral : Zekd αCut e k d c (insert (ψ/[nm (stdClosedVal s)]) Γ) :=
    Zekd.cut (ψ/[s]) hψc hSrcLt hCongLt hSrcNF hCongNF hCutNF hτSrc hτCong
      dSrc' dCong
  exact Zekd.exI ψ (stdClosedVal s) hCutLt hCutNF hOutNF hτCut hbound dNumeral

/--
Conjunction step for the bounded value-congruent EM engine.

Given child derivations closing `a` against its value-congruent negation and `b` against its
value-congruent negation, this composes them into the parent sequent containing
`(a ∧ b)[w]` and `¬(a ∧ b)[w']`.  The theorem is intentionally phrased with explicit child
ordinals: the future recursive engine can choose any ordinal schedule and discharge these
side conditions separately.
-/
theorem embedding_valueCongruentAndFromChildren_probe
    {n : ℕ} {βA βB αAnd αOut e : ONote} {k d c : ℕ} {Γ : Seq}
    (w w' : Fin n → SyntacticTerm ℒₒᵣ) (a b : SyntacticSemiformula ℒₒᵣ n)
    (hA_lt : βA < αAnd) (hB_lt : βB < αAnd) (hAnd_lt : αAnd < αOut)
    (hANF : βA.NF) (hBNF : βB.NF) (hAndNF : αAnd.NF) (hOutNF : αOut.NF)
    (hτA : norm βA < k + d) (hτB : norm βB < k + d) (hτAnd : norm αAnd < k + d)
    (hp : (Rew.subst w ▹ (a ⋏ b)) ∈ Γ)
    (hn : (∼(Rew.subst w' ▹ (a ⋏ b))) ∈ Γ)
    (dA : Zekd βA e k d c
      (insert (Rew.subst w ▹ a)
        (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ))))
    (dB : Zekd βB e k d c
      (insert (Rew.subst w ▹ b)
        (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ)))) :
    Zekd αOut e k d c Γ := by
  have hp' : ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b)) ∈ Γ := by
    simpa using hp
  have hn' : (∼(Rew.subst w' ▹ a) ⋎ ∼(Rew.subst w' ▹ b)) ∈ Γ := by
    simpa using hn
  have hand : Zekd αAnd e k d c
      (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ)) := by
    have h := Zekd.andI (Rew.subst w ▹ a) (Rew.subst w ▹ b)
      hA_lt hB_lt hANF hBNF hAndNF hτA hτB dA dB
    rw [Finset.insert_eq_self.mpr
      (show ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b))
          ∈ insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ) by
        simp [hp'])] at h
    exact h
  have hor := Zekd.orI (∼(Rew.subst w' ▹ a)) (∼(Rew.subst w' ▹ b))
    hAnd_lt hAndNF hOutNF hτAnd hand
  rwa [Finset.insert_eq_self.mpr hn'] at hor

/--
Disjunction step for the bounded value-congruent EM engine.

This is the polarity-dual parent constructor to
`embedding_valueCongruentAndFromChildren_probe`: child closures for `a` and `b` build
`¬a[w'] ∧ ¬b[w']`, then `Zekd.orI` packages the positive `a[w] ∨ b[w]` parent.
-/
theorem embedding_valueCongruentOrFromChildren_probe
    {n : ℕ} {βA βB αAnd αOut e : ONote} {k d c : ℕ} {Γ : Seq}
    (w w' : Fin n → SyntacticTerm ℒₒᵣ) (a b : SyntacticSemiformula ℒₒᵣ n)
    (hA_lt : βA < αAnd) (hB_lt : βB < αAnd) (hAnd_lt : αAnd < αOut)
    (hANF : βA.NF) (hBNF : βB.NF) (hAndNF : αAnd.NF) (hOutNF : αOut.NF)
    (hτA : norm βA < k + d) (hτB : norm βB < k + d) (hτAnd : norm αAnd < k + d)
    (hp : (Rew.subst w ▹ (a ⋎ b)) ∈ Γ)
    (hn : (∼(Rew.subst w' ▹ (a ⋎ b))) ∈ Γ)
    (dA : Zekd βA e k d c
      (insert (∼(Rew.subst w' ▹ a))
        (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ))))
    (dB : Zekd βB e k d c
      (insert (∼(Rew.subst w' ▹ b))
        (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ)))) :
    Zekd αOut e k d c Γ := by
  have hp' : ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) ∈ Γ := by
    simpa using hp
  have hn' : (∼(Rew.subst w' ▹ a) ⋏ ∼(Rew.subst w' ▹ b)) ∈ Γ := by
    simpa using hn
  have hand : Zekd αAnd e k d c
      (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ)) := by
    have h := Zekd.andI (∼(Rew.subst w' ▹ a)) (∼(Rew.subst w' ▹ b))
      hA_lt hB_lt hANF hBNF hAndNF hτA hτB dA dB
    rw [Finset.insert_eq_self.mpr
      (show (∼(Rew.subst w' ▹ a) ⋏ ∼(Rew.subst w' ▹ b))
          ∈ insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ) by
        simp [hn'])] at h
    exact h
  have hor := Zekd.orI (Rew.subst w ▹ a) (Rew.subst w ▹ b)
    hAnd_lt hAndNF hOutNF hτAnd hand
  rwa [Finset.insert_eq_self.mpr hp'] at hor

/-- Closed-term specialization of the conjunction parent constructor. -/
theorem embedding_valueCongruentAndClosedTermFromChildren_probe
    {βA βB αAnd αOut e : ONote} {k d c : ℕ} {Γ : Seq}
    (s s' : SyntacticTerm ℒₒᵣ) (a b : SyntacticSemiformula ℒₒᵣ 1)
    (hA_lt : βA < αAnd) (hB_lt : βB < αAnd) (hAnd_lt : αAnd < αOut)
    (hANF : βA.NF) (hBNF : βB.NF) (hAndNF : αAnd.NF) (hOutNF : αOut.NF)
    (hτA : norm βA < k + d) (hτB : norm βB < k + d) (hτAnd : norm αAnd < k + d)
    (hp : ((a ⋏ b)/[s]) ∈ Γ)
    (hn : (∼((a ⋏ b)/[s'])) ∈ Γ)
    (dA : Zekd βA e k d c
      (insert (a/[s]) (insert (∼(a/[s'])) (insert (∼(b/[s'])) Γ))))
    (dB : Zekd βB e k d c
      (insert (b/[s]) (insert (∼(a/[s'])) (insert (∼(b/[s'])) Γ)))) :
    Zekd αOut e k d c Γ := by
  refine embedding_valueCongruentAndFromChildren_probe ![s] ![s'] a b
    hA_lt hB_lt hAnd_lt hANF hBNF hAndNF hOutNF hτA hτB hτAnd ?_ ?_ ?_ ?_
  · simpa using hp
  · simpa using hn
  · simpa using dA
  · simpa using dB

/-- Closed-term specialization of the disjunction parent constructor. -/
theorem embedding_valueCongruentOrClosedTermFromChildren_probe
    {βA βB αAnd αOut e : ONote} {k d c : ℕ} {Γ : Seq}
    (s s' : SyntacticTerm ℒₒᵣ) (a b : SyntacticSemiformula ℒₒᵣ 1)
    (hA_lt : βA < αAnd) (hB_lt : βB < αAnd) (hAnd_lt : αAnd < αOut)
    (hANF : βA.NF) (hBNF : βB.NF) (hAndNF : αAnd.NF) (hOutNF : αOut.NF)
    (hτA : norm βA < k + d) (hτB : norm βB < k + d) (hτAnd : norm αAnd < k + d)
    (hp : ((a ⋎ b)/[s]) ∈ Γ)
    (hn : (∼((a ⋎ b)/[s'])) ∈ Γ)
    (dA : Zekd βA e k d c
      (insert (∼(a/[s'])) (insert (a/[s]) (insert (b/[s]) Γ))))
    (dB : Zekd βB e k d c
      (insert (∼(b/[s'])) (insert (a/[s]) (insert (b/[s]) Γ)))) :
    Zekd αOut e k d c Γ := by
  refine embedding_valueCongruentOrFromChildren_probe ![s] ![s'] a b
    hA_lt hB_lt hAnd_lt hANF hBNF hAndNF hOutNF hτA hτB hτAnd ?_ ?_ ?_ ?_
  · simpa using hp
  · simpa using hn
  · simpa using dA
  · simpa using dB

/-! #### A first recursive bounded value-congruence shell -/

/-- Quantifier-free arithmetic formulas.  This is the first bounded EM shell needed by the
embedding probes; the quantifier cases are handled separately by the `allω`/`exI` layer. -/
def QFreeForm {ξ n} : Semiformula ℒₒᵣ ξ n → Prop :=
  Semiformula.rec' (C := fun _ _ => Prop)
    True True
    (fun {_ _} _ _ => True)
    (fun {_ _} _ _ => True)
    (fun {_} _ _ p q => p ∧ q)
    (fun {_} _ _ p q => p ∧ q)
    (fun {_} _ _ => False)
    (fun {_} _ _ => False)

@[simp] lemma qFreeForm_verum {ξ n} : QFreeForm (⊤ : Semiformula ℒₒᵣ ξ n) := trivial
@[simp] lemma qFreeForm_falsum {ξ n} : QFreeForm (⊥ : Semiformula ℒₒᵣ ξ n) := trivial
@[simp] lemma qFreeForm_rel {ξ n ar} (r : (ℒₒᵣ).Rel ar) (v : Fin ar → Semiterm ℒₒᵣ ξ n) :
    QFreeForm (Semiformula.rel r v) := trivial
@[simp] lemma qFreeForm_nrel {ξ n ar} (r : (ℒₒᵣ).Rel ar) (v : Fin ar → Semiterm ℒₒᵣ ξ n) :
    QFreeForm (Semiformula.nrel r v) := trivial
@[simp] lemma qFreeForm_and {ξ n} (φ ψ : Semiformula ℒₒᵣ ξ n) :
    QFreeForm (φ ⋏ ψ) ↔ QFreeForm φ ∧ QFreeForm ψ := Iff.rfl
@[simp] lemma qFreeForm_or {ξ n} (φ ψ : Semiformula ℒₒᵣ ξ n) :
    QFreeForm (φ ⋎ ψ) ↔ QFreeForm φ ∧ QFreeForm ψ := Iff.rfl
@[simp] lemma qFreeForm_all {ξ n} (φ : Semiformula ℒₒᵣ ξ (n + 1)) :
    QFreeForm (∀⁰ φ) ↔ False := Iff.rfl
@[simp] lemma qFreeForm_exs {ξ n} (φ : Semiformula ℒₒᵣ ξ (n + 1)) :
    QFreeForm (∃⁰ φ) ↔ False := Iff.rfl

lemma embedding_ofNat_lt_of_lt {m n : ℕ} (h : m < n) : ONote.ofNat m < ONote.ofNat n := by
  rw [ONote.lt_def, ONote.repr_ofNat, ONote.repr_ofNat]
  exact_mod_cast h

@[simp] lemma embedding_norm_ofNat (n : ℕ) : norm (ONote.ofNat n) = n := by
  cases n with
  | zero => rfl
  | succ k => rw [ONote.ofNat_succ, norm_oadd, norm_zero]; simp

/--
Quantifier-free closed-term value-congruent EM at explicit finite `ONote` height.

For a one-variable quantifier-free formula `ψ`, closed terms with the same standard value close any
sequent containing `ψ[s]` and `¬ψ[s']` at height `ofNat (2*q)`, provided that finite height fits the
current norm budget.
-/
theorem embedding_valueCongruentQFreeClosedTerm_probe :
    ∀ (q : ℕ) {K d c : ℕ} {e : ONote} {Γ : Seq}
      (s s' : SyntacticTerm ℒₒᵣ) (ψ : SyntacticSemiformula ℒₒᵣ 1),
      ψ.complexity ≤ q → QFreeForm ψ → stdClosedVal s = stdClosedVal s' →
      2 * q < K + d → (ψ/[s]) ∈ Γ → (∼(ψ/[s'])) ∈ Γ →
      Zekd (ONote.ofNat (2 * q)) e K d c Γ := by
  intro q
  induction q with
  | zero =>
      intro K d c e Γ s s' ψ hψq hqf hval hbudget hp hn
      cases ψ using Semiformula.cases' with
      | hverum =>
          exact embedding_valueCongruentVerum_probe ![s] (by simpa using hp)
      | hfalsum =>
          exact embedding_valueCongruentFalsum_probe ![s'] (by simpa using hn)
      | hrel r v =>
          exact embedding_valueCongruentRelClosedTermAtom_probe r s s' v hval inferInstance
            (by rw [embedding_norm_ofNat]; omega) hp
            (by simpa [Semiformula.rew_rel, Semiformula.rew_nrel] using hn)
      | hnrel r v =>
          exact embedding_valueCongruentNrelClosedTermAtom_probe r s s' v hval inferInstance
            (by rw [embedding_norm_ofNat]; omega) hp
            (by simpa [Semiformula.rew_rel, Semiformula.rew_nrel] using hn)
      | hand a b =>
          simp only [Semiformula.complexity_and] at hψq
          omega
      | hor a b =>
          simp only [Semiformula.complexity_or] at hψq
          omega
      | hall a =>
          simp at hqf
      | hexs a =>
          simp at hqf
  | succ q ih =>
      intro K d c e Γ s s' ψ hψq hqf hval hbudget hp hn
      cases ψ using Semiformula.cases' with
      | hverum =>
          exact embedding_valueCongruentVerum_probe ![s] (by simpa using hp)
      | hfalsum =>
          exact embedding_valueCongruentFalsum_probe ![s'] (by simpa using hn)
      | hrel r v =>
          exact embedding_valueCongruentRelClosedTermAtom_probe r s s' v hval inferInstance
            (by rw [embedding_norm_ofNat]; omega) hp
            (by simpa [Semiformula.rew_rel, Semiformula.rew_nrel] using hn)
      | hnrel r v =>
          exact embedding_valueCongruentNrelClosedTermAtom_probe r s s' v hval inferInstance
            (by rw [embedding_norm_ofNat]; omega) hp
            (by simpa [Semiformula.rew_rel, Semiformula.rew_nrel] using hn)
      | hand a b =>
          have haq : a.complexity ≤ q := by
            simp only [Semiformula.complexity_and] at hψq
            omega
          have hbq : b.complexity ≤ q := by
            simp only [Semiformula.complexity_and] at hψq
            omega
          obtain ⟨hqfa, hqfb⟩ : QFreeForm a ∧ QFreeForm b := by simpa using hqf
          have dA : Zekd (ONote.ofNat (2 * q)) e K d c
              (insert (a/[s]) (insert (∼(a/[s'])) (insert (∼(b/[s'])) Γ))) :=
            ih (K := K) (d := d) (c := c) (e := e)
              (Γ := insert (a/[s]) (insert (∼(a/[s'])) (insert (∼(b/[s'])) Γ)))
              s s' a haq hqfa hval (by omega) (by simp) (by simp)
          have dB : Zekd (ONote.ofNat (2 * q)) e K d c
              (insert (b/[s]) (insert (∼(a/[s'])) (insert (∼(b/[s'])) Γ))) :=
            ih (K := K) (d := d) (c := c) (e := e)
              (Γ := insert (b/[s]) (insert (∼(a/[s'])) (insert (∼(b/[s'])) Γ)))
              s s' b hbq hqfb hval (by omega) (by simp) (by simp)
          exact embedding_valueCongruentAndClosedTermFromChildren_probe
            (βA := ONote.ofNat (2 * q)) (βB := ONote.ofNat (2 * q))
            (αAnd := ONote.ofNat (2 * q + 1)) s s' a b
            (embedding_ofNat_lt_of_lt (by omega)) (embedding_ofNat_lt_of_lt (by omega))
            (embedding_ofNat_lt_of_lt (by omega))
            inferInstance inferInstance inferInstance inferInstance
            (by rw [embedding_norm_ofNat]; omega)
            (by rw [embedding_norm_ofNat]; omega)
            (by rw [embedding_norm_ofNat]; omega)
            hp hn dA dB
      | hor a b =>
          have haq : a.complexity ≤ q := by
            simp only [Semiformula.complexity_or] at hψq
            omega
          have hbq : b.complexity ≤ q := by
            simp only [Semiformula.complexity_or] at hψq
            omega
          obtain ⟨hqfa, hqfb⟩ : QFreeForm a ∧ QFreeForm b := by simpa using hqf
          have dA : Zekd (ONote.ofNat (2 * q)) e K d c
              (insert (∼(a/[s'])) (insert (a/[s]) (insert (b/[s]) Γ))) :=
            ih (K := K) (d := d) (c := c) (e := e)
              (Γ := insert (∼(a/[s'])) (insert (a/[s]) (insert (b/[s]) Γ)))
              s s' a haq hqfa hval (by omega) (by simp) (by simp)
          have dB : Zekd (ONote.ofNat (2 * q)) e K d c
              (insert (∼(b/[s'])) (insert (a/[s]) (insert (b/[s]) Γ))) :=
            ih (K := K) (d := d) (c := c) (e := e)
              (Γ := insert (∼(b/[s'])) (insert (a/[s]) (insert (b/[s]) Γ)))
              s s' b hbq hqfb hval (by omega) (by simp) (by simp)
          exact embedding_valueCongruentOrClosedTermFromChildren_probe
            (βA := ONote.ofNat (2 * q)) (βB := ONote.ofNat (2 * q))
            (αAnd := ONote.ofNat (2 * q + 1)) s s' a b
            (embedding_ofNat_lt_of_lt (by omega)) (embedding_ofNat_lt_of_lt (by omega))
            (embedding_ofNat_lt_of_lt (by omega))
            inferInstance inferInstance inferInstance inferInstance
            (by rw [embedding_norm_ofNat]; omega)
            (by rw [embedding_norm_ofNat]; omega)
            (by rw [embedding_norm_ofNat]; omega)
            hp hn dA dB
      | hall a =>
          simp at hqf
      | hexs a =>
          simp at hqf

set_option maxHeartbeats 1000000 in
/--
Bounded value-congruent EM for arbitrary formulas at explicit finite `ONote` height.

This is the arity-general recursive shell needed by the bounded embedding route.  The quantifier
cases are the decisive check: each `allω` premise runs at `max K m`, so the corresponding `exI`
witness `m` is paid by `inductionLeaf_runningIndex_witnessBound`.
-/
theorem embedding_valueCongruentEM_probe :
    ∀ (q : ℕ) {K d c : ℕ} {e : ONote} {Γ : Seq} {n : ℕ}
      (w w' : Fin n → SyntacticTerm ℒₒᵣ) (ψ : SyntacticSemiformula ℒₒᵣ n),
      ψ.complexity ≤ q →
      (∀ i, stdClosedVal (w i) = stdClosedVal (w' i)) →
      2 * q < K + d → (Rew.subst w ▹ ψ) ∈ Γ → (∼(Rew.subst w' ▹ ψ)) ∈ Γ →
      Zekd (ONote.ofNat (2 * q)) e K d c Γ := by
  intro q
  induction q with
  | zero =>
      intro K d c e Γ n w w' ψ hψq hval hbudget hp hn
      cases ψ using Semiformula.cases' with
      | hverum =>
          exact embedding_valueCongruentVerum_probe w (by simpa using hp)
      | hfalsum =>
          exact embedding_valueCongruentFalsum_probe w' (by simpa using hn)
      | hrel r v =>
          exact embedding_valueCongruentRelSubstAtom_probe r w w' v hval inferInstance
            (by rw [embedding_norm_ofNat]; omega)
            (by simpa [Semiformula.rew_rel] using hp)
            (by simpa [Semiformula.rew_rel, Semiformula.rew_nrel] using hn)
      | hnrel r v =>
          exact embedding_valueCongruentNrelSubstAtom_probe r w w' v hval inferInstance
            (by rw [embedding_norm_ofNat]; omega)
            (by simpa [Semiformula.rew_nrel] using hp)
            (by simpa [Semiformula.rew_rel, Semiformula.rew_nrel] using hn)
      | hand a b =>
          simp only [Semiformula.complexity_and] at hψq
          omega
      | hor a b =>
          simp only [Semiformula.complexity_or] at hψq
          omega
      | hall a =>
          simp only [Semiformula.complexity_all] at hψq
          omega
      | hexs a =>
          simp only [Semiformula.complexity_exs] at hψq
          omega
  | succ q ih =>
      intro K d c e Γ n w w' ψ hψq hval hbudget hp hn
      cases ψ using Semiformula.cases' with
      | hverum =>
          exact embedding_valueCongruentVerum_probe w (by simpa using hp)
      | hfalsum =>
          exact embedding_valueCongruentFalsum_probe w' (by simpa using hn)
      | hrel r v =>
          exact embedding_valueCongruentRelSubstAtom_probe r w w' v hval inferInstance
            (by rw [embedding_norm_ofNat]; omega)
            (by simpa [Semiformula.rew_rel] using hp)
            (by simpa [Semiformula.rew_rel, Semiformula.rew_nrel] using hn)
      | hnrel r v =>
          exact embedding_valueCongruentNrelSubstAtom_probe r w w' v hval inferInstance
            (by rw [embedding_norm_ofNat]; omega)
            (by simpa [Semiformula.rew_nrel] using hp)
            (by simpa [Semiformula.rew_rel, Semiformula.rew_nrel] using hn)
      | hand a b =>
          have haq : a.complexity ≤ q := by
            simp only [Semiformula.complexity_and] at hψq
            omega
          have hbq : b.complexity ≤ q := by
            simp only [Semiformula.complexity_and] at hψq
            omega
          have dA : Zekd (ONote.ofNat (2 * q)) e K d c
              (insert (Rew.subst w ▹ a)
                (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ))) :=
            ih (K := K) (d := d) (c := c) (e := e) (n := n) w w' a haq hval
              (by omega) (by simp) (by simp)
          have dB : Zekd (ONote.ofNat (2 * q)) e K d c
              (insert (Rew.subst w ▹ b)
                (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ))) :=
            ih (K := K) (d := d) (c := c) (e := e) (n := n) w w' b hbq hval
              (by omega) (by simp) (by simp)
          exact embedding_valueCongruentAndFromChildren_probe
            (βA := ONote.ofNat (2 * q)) (βB := ONote.ofNat (2 * q))
            (αAnd := ONote.ofNat (2 * q + 1)) w w' a b
            (embedding_ofNat_lt_of_lt (by omega)) (embedding_ofNat_lt_of_lt (by omega))
            (embedding_ofNat_lt_of_lt (by omega))
            inferInstance inferInstance inferInstance inferInstance
            (by rw [embedding_norm_ofNat]; omega)
            (by rw [embedding_norm_ofNat]; omega)
            (by rw [embedding_norm_ofNat]; omega)
            hp hn dA dB
      | hor a b =>
          have haq : a.complexity ≤ q := by
            simp only [Semiformula.complexity_or] at hψq
            omega
          have hbq : b.complexity ≤ q := by
            simp only [Semiformula.complexity_or] at hψq
            omega
          have dA : Zekd (ONote.ofNat (2 * q)) e K d c
              (insert (∼(Rew.subst w' ▹ a))
                (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ))) :=
            ih (K := K) (d := d) (c := c) (e := e) (n := n) w w' a haq hval
              (by omega) (by simp) (by simp)
          have dB : Zekd (ONote.ofNat (2 * q)) e K d c
              (insert (∼(Rew.subst w' ▹ b))
                (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ))) :=
            ih (K := K) (d := d) (c := c) (e := e) (n := n) w w' b hbq hval
              (by omega) (by simp) (by simp)
          exact embedding_valueCongruentOrFromChildren_probe
            (βA := ONote.ofNat (2 * q)) (βB := ONote.ofNat (2 * q))
            (αAnd := ONote.ofNat (2 * q + 1)) w w' a b
            (embedding_ofNat_lt_of_lt (by omega)) (embedding_ofNat_lt_of_lt (by omega))
            (embedding_ofNat_lt_of_lt (by omega))
            inferInstance inferInstance inferInstance inferInstance
            (by rw [embedding_norm_ofNat]; omega)
            (by rw [embedding_norm_ofNat]; omega)
            (by rw [embedding_norm_ofNat]; omega)
            hp hn dA dB
      | hall a =>
          have haq : a.complexity ≤ q := by
            simp only [Semiformula.complexity_all] at hψq
            omega
          have hp' : (∀⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by simpa using hp
          have hn' : (∃⁰ ((Rew.subst w').q ▹ ∼a)) ∈ Γ := by simpa using hn
          have fam : ∀ m, Zekd (ONote.ofNat (2 * q + 1)) e (max K m) d c
              (insert (((Rew.subst w).q ▹ a)/[nm m]) Γ) := by
            intro m
            have hvalm : ∀ i, stdClosedVal ((nm m :> w) i) = stdClosedVal ((nm m :> w') i) :=
              embedding_valm_cons_nm_congr w w' m hval
            have hx : Zekd (ONote.ofNat (2 * q)) e (max K m) d c
                (insert (((Rew.subst w).q ▹ a)/[nm m])
                  (insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ)) :=
              ih (K := max K m) (d := d) (c := c) (e := e) (n := n + 1)
                (nm m :> w) (nm m :> w') a haq hvalm (by omega)
                (by rw [← embedding_subst_q_cons_app]; simp)
                (by rw [← embedding_subst_q_cons_app]; simp)
            have hx' : Zekd (ONote.ofNat (2 * q)) e (max K m) d c
                (insert ((((Rew.subst w').q ▹ ∼a)/[nm m])
                  ) (insert (((Rew.subst w).q ▹ a)/[nm m]) Γ)) := by
              have heq : (((Rew.subst w').q ▹ ∼a)/[nm m])
                  = ∼(((Rew.subst w').q ▹ a)/[nm m]) := by simp
              rw [heq, Finset.insert_comm]
              exact hx
            have hexI : Zekd (ONote.ofNat (2 * q + 1)) e (max K m) d c
                (insert (∃⁰ ((Rew.subst w').q ▹ ∼a))
                  (insert (((Rew.subst w).q ▹ a)/[nm m]) Γ)) :=
              Zekd.exI ((Rew.subst w').q ▹ ∼a) m
                (embedding_ofNat_lt_of_lt (by omega)) inferInstance inferInstance
                (by rw [embedding_norm_ofNat]; omega)
                (inductionLeaf_runningIndex_witnessBound e K d m) hx'
            rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hn')] at hexI
            exact hexI
          have hallω : Zekd (ONote.ofNat (2 * (q + 1))) e K d c
              (insert (∀⁰ ((Rew.subst w).q ▹ a)) Γ) :=
            Zekd.allω ((Rew.subst w).q ▹ a) (fun _ => ONote.ofNat (2 * q + 1))
              (fun _ => embedding_ofNat_lt_of_lt (by omega))
              (fun _ => inferInstance) inferInstance
              (fun m => by rw [embedding_norm_ofNat]; omega) fam
          rwa [Finset.insert_eq_self.mpr hp'] at hallω
      | hexs a =>
          have haq : a.complexity ≤ q := by
            simp only [Semiformula.complexity_exs] at hψq
            omega
          have hp' : (∃⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by simpa using hp
          have hn' : (∀⁰ ((Rew.subst w').q ▹ ∼a)) ∈ Γ := by simpa using hn
          have fam : ∀ m, Zekd (ONote.ofNat (2 * q + 1)) e (max K m) d c
              (insert (((Rew.subst w').q ▹ ∼a)/[nm m]) Γ) := by
            intro m
            have hvalm : ∀ i, stdClosedVal ((nm m :> w) i) = stdClosedVal ((nm m :> w') i) :=
              embedding_valm_cons_nm_congr w w' m hval
            have hx : Zekd (ONote.ofNat (2 * q)) e (max K m) d c
                (insert (((Rew.subst w).q ▹ a)/[nm m])
                  (insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ)) :=
              ih (K := max K m) (d := d) (c := c) (e := e) (n := n + 1)
                (nm m :> w) (nm m :> w') a haq hvalm (by omega)
                (by rw [← embedding_subst_q_cons_app]; simp)
                (by rw [← embedding_subst_q_cons_app]; simp)
            have hx' : Zekd (ONote.ofNat (2 * q)) e (max K m) d c
                (insert (((Rew.subst w).q ▹ a)/[nm m])
                  (insert (((Rew.subst w').q ▹ ∼a)/[nm m]) Γ)) := by
              have heq : (((Rew.subst w').q ▹ ∼a)/[nm m])
                  = ∼(((Rew.subst w').q ▹ a)/[nm m]) := by simp
              rw [heq]
              exact hx
            have hexI : Zekd (ONote.ofNat (2 * q + 1)) e (max K m) d c
                (insert (∃⁰ ((Rew.subst w).q ▹ a))
                  (insert (((Rew.subst w').q ▹ ∼a)/[nm m]) Γ)) :=
              Zekd.exI ((Rew.subst w).q ▹ a) m
                (embedding_ofNat_lt_of_lt (by omega)) inferInstance inferInstance
                (by rw [embedding_norm_ofNat]; omega)
                (inductionLeaf_runningIndex_witnessBound e K d m) hx'
            rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hp')] at hexI
            exact hexI
          have hallω : Zekd (ONote.ofNat (2 * (q + 1))) e K d c
              (insert (∀⁰ ((Rew.subst w').q ▹ ∼a)) Γ) :=
            Zekd.allω ((Rew.subst w').q ▹ ∼a) (fun _ => ONote.ofNat (2 * q + 1))
              (fun _ => embedding_ofNat_lt_of_lt (by omega))
              (fun _ => inferInstance) inferInstance
              (fun m => by rw [embedding_norm_ofNat]; omega) fam
          rwa [Finset.insert_eq_self.mpr hn'] at hallω

/--
Closed-term existential introduction using the checked bounded value-congruence EM engine.

This is the direct `Zekd` adapter for the Foundation `exs` shape after an open witness term has been
closed by an assignment.  The only semantic side condition still exposed is the real witness bound
`stdClosedVal s ≤ hardy e (K+d)`.
-/
theorem embedding_closedTermExI_probe
    {βSrc αCut αOut e : ONote} {K d c q : ℕ} {Γ : Seq}
    {ψ : SyntacticSemiformula ℒₒᵣ 1} (s : SyntacticTerm ℒₒᵣ)
    (hψq : ψ.complexity ≤ q) (hψc : (ψ/[s]).complexity < c)
    (hSrcLt : βSrc < αCut) (hCongLt : ONote.ofNat (2 * q) < αCut)
    (hCutLt : αCut < αOut)
    (hSrcNF : βSrc.NF) (hCutNF : αCut.NF) (hOutNF : αOut.NF)
    (hτSrc : norm βSrc < K + d) (hτCong : norm (ONote.ofNat (2 * q)) < K + d)
    (hτCut : norm αCut < K + d)
    (hbudget : 2 * q < K + d)
    (hbound : stdClosedVal s ≤ hardy e (K + d))
    (dSrc : Zekd βSrc e K d c (insert (ψ/[s]) Γ)) :
    Zekd αOut e K d c (insert (∃⁰ ψ) Γ) := by
  have hval : ∀ i, stdClosedVal ((![nm (stdClosedVal s)] : Fin 1 → SyntacticTerm ℒₒᵣ) i)
      = stdClosedVal ((![s] : Fin 1 → SyntacticTerm ℒₒᵣ) i) := by
    intro i
    cases i using Fin.cases with
    | zero => simp
    | succ j => exact Fin.elim0 j
  have dCong : Zekd (ONote.ofNat (2 * q)) e K d c
      (insert (∼(ψ/[s])) (insert (ψ/[nm (stdClosedVal s)]) Γ)) := by
    refine embedding_valueCongruentEM_probe q
      (![nm (stdClosedVal s)] : Fin 1 → SyntacticTerm ℒₒᵣ)
      (![s] : Fin 1 → SyntacticTerm ℒₒᵣ) ψ hψq hval hbudget ?_ ?_
    · simp
    · simp
  exact embedding_closedTermExI_of_valueCongruentEM_probe s hψc hSrcLt hCongLt hCutLt
    hSrcNF inferInstance hCutNF hOutNF hτSrc hτCong hτCut hbound dSrc dCong

/-- A finite numeric budget bound on a closed witness term is enough for the `Zekd.exI`
witness side condition, because every Hardy level is expansive. -/
theorem closedTerm_witnessBound_of_budget
    (e : ONote) {K d : ℕ} {s : SyntacticTerm ℒₒᵣ}
    (hterm : stdClosedVal s ≤ K + d) :
    stdClosedVal s ≤ hardy e (K + d) :=
  le_trans hterm (le_hardy e (K + d))

/--
Closed-term existential introduction with the witness bound paid by raising the `K` index.

This is the local `exs` budget adapter needed by the bounded embedding route: if a source derivation
is available at index `K`, then it can be used at `max K (stdClosedVal s)`, where the closed witness
term is automatically within the Hardy witness budget.  No extra logical premise is introduced.
-/
theorem embedding_closedTermExI_raiseK_probe
    {βSrc αCut αOut e : ONote} {K d c q : ℕ} {Γ : Seq}
    {ψ : SyntacticSemiformula ℒₒᵣ 1} (s : SyntacticTerm ℒₒᵣ)
    (hψq : ψ.complexity ≤ q) (hψc : (ψ/[s]).complexity < c)
    (hSrcLt : βSrc < αCut) (hCongLt : ONote.ofNat (2 * q) < αCut)
    (hCutLt : αCut < αOut)
    (hSrcNF : βSrc.NF) (hCutNF : αCut.NF) (hOutNF : αOut.NF)
    (hτSrc : norm βSrc < K + d) (hτCong : norm (ONote.ofNat (2 * q)) < K + d)
    (hτCut : norm αCut < K + d)
    (hbudget : 2 * q < K + d)
    (dSrc : Zekd βSrc e K d c (insert (ψ/[s]) Γ)) :
    Zekd αOut e (max K (stdClosedVal s)) d c (insert (∃⁰ ψ) Γ) := by
  refine embedding_closedTermExI_probe (K := max K (stdClosedVal s)) s hψq hψc
    hSrcLt hCongLt hCutLt hSrcNF hCutNF hOutNF ?_ ?_ ?_ ?_ ?_ ?_
  · exact lt_of_lt_of_le hτSrc (by omega)
  · exact lt_of_lt_of_le hτCong (by omega)
  · exact lt_of_lt_of_le hτCut (by omega)
  · exact lt_of_lt_of_le hbudget (by omega)
  · exact closedTerm_witnessBound_of_budget e (by omega)
  · exact dSrc.mono_k (le_max_left K (stdClosedVal s))

/--
One bounded cut-tower step for the PA-induction leaf.

This is the structural kernel behind `EmbeddingBound.metaInduction_cong_bdd`, ported to `Zekd`:
given the finite excluded-middle premises for `ψ(n)` and `ψ(n+1)`, combine them into the bad-step
formula, introduce `∃ badStep` using the running witness bound, then cut against the current
`ψ(n)` derivation to obtain `ψ(n+1)`.

The EM/value-substitution premises are still external to this probe.  The point of the theorem is
that the witness-bounded `andI`/`exI`/`cut` wiring itself is tractable at index `max k n`.
-/
theorem inductionLeaf_cutTowerStep_probe
    {βIH βA βB βAnd βEx α e : ONote} {k d c n : ℕ} {Δ : Seq}
    {ψ step : SyntacticSemiformula ℒₒᵣ 1}
    (hstep : (∼step)/[nm n] = (ψ/[nm n]) ⋏ ∼(ψ/[nm (n + 1)]))
    (hmemEx : (∃⁰ ∼step) ∈ Δ)
    (hψc : (ψ/[nm n]).complexity < c)
    (hIHlt : βIH < α) (hExlt : βEx < α)
    (hAlt : βA < βAnd) (hBlt : βB < βAnd) (hAndlt : βAnd < βEx)
    (hIHNF : βIH.NF) (hANF : βA.NF) (hBNF : βB.NF)
    (hAndNF : βAnd.NF) (hExNF : βEx.NF) (hαNF : α.NF)
    (hτIH : norm βIH < max k n + d) (hτA : norm βA < max k n + d)
    (hτB : norm βB < max k n + d) (hτAnd : norm βAnd < max k n + d)
    (hτEx : norm βEx < max k n + d)
    (dIH : Zekd βIH e (max k n) d c (insert (ψ/[nm n]) Δ))
    (dA : Zekd βA e (max k n) d c
      (insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ))))
    (dB : Zekd βB e (max k n) d c
      (insert (∼(ψ/[nm (n + 1)])) (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ)))) :
    Zekd α e (max k n) d c (insert (ψ/[nm (n + 1)]) Δ) := by
  have hAnd : Zekd βAnd e (max k n) d c
      (insert ((ψ/[nm n]) ⋏ ∼(ψ/[nm (n + 1)]))
        (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ))) :=
    Zekd.andI (ψ/[nm n]) (∼(ψ/[nm (n + 1)]))
      hAlt hBlt hANF hBNF hAndNF hτA hτB dA dB
  have hBadStep : Zekd βAnd e (max k n) d c
      (insert ((∼step)/[nm n])
        (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ))) := by
    rw [hstep]
    exact hAnd
  have hEx : Zekd βEx e (max k n) d c
      (insert (∃⁰ ∼step) (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ))) :=
    Zekd.exI (∼step) n hAndlt hAndNF hExNF hτAnd
      (inductionLeaf_runningIndex_witnessBound e k d n) hBadStep
  have hEx' : Zekd βEx e (max k n) d c
      (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ)) := by
    rw [Finset.insert_eq_self.mpr
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmemEx))] at hEx
    exact hEx
  have hIH' : Zekd βIH e (max k n) d c
      (insert (ψ/[nm n]) (insert (ψ/[nm (n + 1)]) Δ)) :=
    Zekd.wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) dIH
  exact Zekd.cut (ψ/[nm n]) hψc hIHlt hExlt hIHNF hExNF hαNF hτIH hτEx hIH' hEx'

/-- Value-substitution by a cut against a value-congruent excluded-middle premise.

This is the `Zekd` analogue of the cut used by
`EmbeddingBound.subst_value_subst_bdd`; the actual proof of the congruent EM premise is still
outside this probe, but the cut interface and budgets are now checked. -/
theorem inductionLeaf_valueSubst_cut_probe
    {βSrc βCong α e : ONote} {k d c : ℕ} {Γ : Seq}
    {ψ : SyntacticSemiformula ℒₒᵣ 1} {s t : SyntacticTerm ℒₒᵣ}
    (hψc : (ψ/[s]).complexity < c)
    (hSrcLt : βSrc < α) (hCongLt : βCong < α)
    (hSrcNF : βSrc.NF) (hCongNF : βCong.NF) (hαNF : α.NF)
    (hτSrc : norm βSrc < k + d) (hτCong : norm βCong < k + d)
    (dSrc : Zekd βSrc e k d c (insert (ψ/[s]) Γ))
    (dCong : Zekd βCong e k d c (insert (∼(ψ/[s])) (insert (ψ/[t]) Γ))) :
    Zekd α e k d c (insert (ψ/[t]) Γ) :=
  Zekd.cut (ψ/[s]) hψc hSrcLt hCongLt hSrcNF hCongNF hαNF hτSrc hτCong
    (Zekd.wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) dSrc) dCong

/--
The same cut-tower step, but with the successor occurrence still written as an arbitrary closed
term `succT`.  After the bad-step cut yields `ψ/[succT]`, a value-substitution cut turns it into
the numeral instance `ψ/[nm (n+1)]`.

This mirrors the real `succInd` leaf more closely than `inductionLeaf_cutTowerStep_probe`.
-/
theorem inductionLeaf_cutTowerStepWithTerm_probe
    {βIH βA βB βAnd βEx βCong αStep α e : ONote} {k d c n : ℕ} {Δ : Seq}
    {ψ step : SyntacticSemiformula ℒₒᵣ 1} (succT : SyntacticTerm ℒₒᵣ)
    (hstep : (∼step)/[nm n] = (ψ/[nm n]) ⋏ ∼(ψ/[succT]))
    (hmemEx : (∃⁰ ∼step) ∈ Δ)
    (hψc : (ψ/[nm n]).complexity < c) (hsuccc : (ψ/[succT]).complexity < c)
    (hIHlt : βIH < αStep) (hExlt : βEx < αStep)
    (hAlt : βA < βAnd) (hBlt : βB < βAnd) (hAndlt : βAnd < βEx)
    (hStepLt : αStep < α) (hCongLt : βCong < α)
    (hIHNF : βIH.NF) (hANF : βA.NF) (hBNF : βB.NF)
    (hAndNF : βAnd.NF) (hExNF : βEx.NF) (hStepNF : αStep.NF)
    (hCongNF : βCong.NF) (hαNF : α.NF)
    (hτIH : norm βIH < max k n + d) (hτA : norm βA < max k n + d)
    (hτB : norm βB < max k n + d) (hτAnd : norm βAnd < max k n + d)
    (hτEx : norm βEx < max k n + d) (hτStep : norm αStep < max k n + d)
    (hτCong : norm βCong < max k n + d)
    (dIH : Zekd βIH e (max k n) d c (insert (ψ/[nm n]) Δ))
    (dA : Zekd βA e (max k n) d c
      (insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) (insert (ψ/[succT]) Δ))))
    (dB : Zekd βB e (max k n) d c
      (insert (∼(ψ/[succT])) (insert (∼(ψ/[nm n])) (insert (ψ/[succT]) Δ))))
    (dCong : Zekd βCong e (max k n) d c
      (insert (∼(ψ/[succT])) (insert (ψ/[nm (n + 1)]) Δ))) :
    Zekd α e (max k n) d c (insert (ψ/[nm (n + 1)]) Δ) := by
  have hAnd : Zekd βAnd e (max k n) d c
      (insert ((ψ/[nm n]) ⋏ ∼(ψ/[succT]))
        (insert (∼(ψ/[nm n])) (insert (ψ/[succT]) Δ))) :=
    Zekd.andI (ψ/[nm n]) (∼(ψ/[succT]))
      hAlt hBlt hANF hBNF hAndNF hτA hτB dA dB
  have hBadStep : Zekd βAnd e (max k n) d c
      (insert ((∼step)/[nm n])
        (insert (∼(ψ/[nm n])) (insert (ψ/[succT]) Δ))) := by
    rw [hstep]
    exact hAnd
  have hEx : Zekd βEx e (max k n) d c
      (insert (∃⁰ ∼step) (insert (∼(ψ/[nm n])) (insert (ψ/[succT]) Δ))) :=
    Zekd.exI (∼step) n hAndlt hAndNF hExNF hτAnd
      (inductionLeaf_runningIndex_witnessBound e k d n) hBadStep
  have hEx' : Zekd βEx e (max k n) d c
      (insert (∼(ψ/[nm n])) (insert (ψ/[succT]) Δ)) := by
    rw [Finset.insert_eq_self.mpr
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmemEx))] at hEx
    exact hEx
  have hIH' : Zekd βIH e (max k n) d c
      (insert (ψ/[nm n]) (insert (ψ/[succT]) Δ)) :=
    Zekd.wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) dIH
  have hStep : Zekd αStep e (max k n) d c (insert (ψ/[succT]) Δ) :=
    Zekd.cut (ψ/[nm n]) hψc hIHlt hExlt hIHNF hExNF hStepNF hτIH hτEx hIH' hEx'
  exact inductionLeaf_valueSubst_cut_probe hsuccc hStepLt hCongLt hStepNF hCongNF hαNF
    hτStep hτCong hStep dCong

/--
Package a running finite induction chain into the `allω` rule.

This is the outer shape of `EmbeddingBound.metaInduction_cong_bdd` in the witness-bounded
`Zekd` calculus: the successor step is allowed to run at the old index `max k n`; monotonicity
then raises it to the next `allω` premise index `max k (n+1)`.
-/
theorem inductionLeaf_allOmegaFromStep_probe
    {αAll e : ONote} {k d c : ℕ} {Δ : Seq}
    {ψ : SyntacticSemiformula ℒₒᵣ 1} (β : ℕ → ONote)
    (hβlt : ∀ n, β n < αAll) (hβNF : ∀ n, (β n).NF)
    (hαAllNF : αAll.NF) (hβτ : ∀ n, norm (β n) < max k n + d)
    (hbase : Zekd (β 0) e k d c (insert (ψ/[nm 0]) Δ))
    (hnext : ∀ n,
      Zekd (β n) e (max k n) d c (insert (ψ/[nm n]) Δ) →
      Zekd (β (n + 1)) e (max k n) d c (insert (ψ/[nm (n + 1)]) Δ)) :
    Zekd αAll e k d c (insert (∀⁰ ψ) Δ) := by
  have chain : ∀ n, Zekd (β n) e (max k n) d c (insert (ψ/[nm n]) Δ) := by
    intro n
    induction n with
    | zero =>
        simpa using hbase
    | succ n ih =>
        exact (hnext n ih).mono_k (by omega)
  exact Zekd.allω ψ β hβlt hβNF hαAllNF hβτ chain

/--
The `allω` packaging for the numeral-successor cut tower.

This is the value-congruence-free core of the bounded PA-induction leaf: the local step already concludes
`ψ(n+1)`, so the outer finite induction and `allω` rule do not need any extra congruent-value premise.
-/
theorem inductionLeaf_allOmegaCutTowerNumeral_probe
    {αAll e : ONote} {k d c : ℕ} {Δ : Seq}
    {ψ step : SyntacticSemiformula ℒₒᵣ 1}
    (β βA βB βAnd βEx : ℕ → ONote)
    (hβAllLt : ∀ n, β n < αAll)
    (hIHlt : ∀ n, β n < β (n + 1)) (hExlt : ∀ n, βEx n < β (n + 1))
    (hAlt : ∀ n, βA n < βAnd n) (hBlt : ∀ n, βB n < βAnd n)
    (hAndlt : ∀ n, βAnd n < βEx n)
    (hβNF : ∀ n, (β n).NF) (hANF : ∀ n, (βA n).NF) (hBNF : ∀ n, (βB n).NF)
    (hAndNF : ∀ n, (βAnd n).NF) (hExNF : ∀ n, (βEx n).NF)
    (hαAllNF : αAll.NF)
    (hβτ : ∀ n, norm (β n) < max k n + d)
    (hAτ : ∀ n, norm (βA n) < max k n + d)
    (hBτ : ∀ n, norm (βB n) < max k n + d)
    (hAndτ : ∀ n, norm (βAnd n) < max k n + d)
    (hExτ : ∀ n, norm (βEx n) < max k n + d)
    (hstep : ∀ n, (∼step)/[nm n] = (ψ/[nm n]) ⋏ ∼(ψ/[nm (n + 1)]))
    (hmemEx : (∃⁰ ∼step) ∈ Δ)
    (hψc : ∀ n, (ψ/[nm n]).complexity < c)
    (hbase : Zekd (β 0) e k d c (insert (ψ/[nm 0]) Δ))
    (dA : ∀ n, Zekd (βA n) e (max k n) d c
      (insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ))))
    (dB : ∀ n, Zekd (βB n) e (max k n) d c
      (insert (∼(ψ/[nm (n + 1)])) (insert (∼(ψ/[nm n])) (insert (ψ/[nm (n + 1)]) Δ)))) :
    Zekd αAll e k d c (insert (∀⁰ ψ) Δ) :=
  inductionLeaf_allOmegaFromStep_probe β hβAllLt hβNF hαAllNF hβτ hbase
    (fun n dIH =>
      inductionLeaf_cutTowerStep_probe (hstep n) hmemEx (hψc n)
        (hIHlt n) (hExlt n) (hAlt n) (hBlt n) (hAndlt n)
        (hβNF n) (hANF n) (hBNF n) (hAndNF n) (hExNF n) (hβNF (n + 1))
        (hβτ n) (hAτ n) (hBτ n) (hAndτ n) (hExτ n)
        dIH (dA n) (dB n))

/--
The `allω` packaging specialized to the bounded PA-induction cut tower.

All finite EM/congruence premises are still explicit hypotheses.  The theorem checks the important
interface: the local `andI`/`exI`/`cut`/value-substitution step composes through ordinary finite
induction and then through `Zekd.allω` without losing the running witness index.
-/
theorem inductionLeaf_allOmegaCutTowerWithTerm_probe
    {αAll e : ONote} {k d c : ℕ} {Δ : Seq}
    {ψ step : SyntacticSemiformula ℒₒᵣ 1}
    (β βA βB βAnd βEx βStep βCong : ℕ → ONote)
    (succT : ℕ → SyntacticTerm ℒₒᵣ)
    (hβAllLt : ∀ n, β n < αAll)
    (hIHlt : ∀ n, β n < βStep n) (hExlt : ∀ n, βEx n < βStep n)
    (hAlt : ∀ n, βA n < βAnd n) (hBlt : ∀ n, βB n < βAnd n)
    (hAndlt : ∀ n, βAnd n < βEx n)
    (hStepLt : ∀ n, βStep n < β (n + 1)) (hCongLt : ∀ n, βCong n < β (n + 1))
    (hβNF : ∀ n, (β n).NF) (hANF : ∀ n, (βA n).NF) (hBNF : ∀ n, (βB n).NF)
    (hAndNF : ∀ n, (βAnd n).NF) (hExNF : ∀ n, (βEx n).NF)
    (hStepNF : ∀ n, (βStep n).NF) (hCongNF : ∀ n, (βCong n).NF)
    (hαAllNF : αAll.NF)
    (hβτ : ∀ n, norm (β n) < max k n + d)
    (hAτ : ∀ n, norm (βA n) < max k n + d)
    (hBτ : ∀ n, norm (βB n) < max k n + d)
    (hAndτ : ∀ n, norm (βAnd n) < max k n + d)
    (hExτ : ∀ n, norm (βEx n) < max k n + d)
    (hStepτ : ∀ n, norm (βStep n) < max k n + d)
    (hCongτ : ∀ n, norm (βCong n) < max k n + d)
    (hstep : ∀ n, (∼step)/[nm n] = (ψ/[nm n]) ⋏ ∼(ψ/[succT n]))
    (hmemEx : (∃⁰ ∼step) ∈ Δ)
    (hψc : ∀ n, (ψ/[nm n]).complexity < c)
    (hsuccc : ∀ n, (ψ/[succT n]).complexity < c)
    (hbase : Zekd (β 0) e k d c (insert (ψ/[nm 0]) Δ))
    (dA : ∀ n, Zekd (βA n) e (max k n) d c
      (insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) (insert (ψ/[succT n]) Δ))))
    (dB : ∀ n, Zekd (βB n) e (max k n) d c
      (insert (∼(ψ/[succT n])) (insert (∼(ψ/[nm n])) (insert (ψ/[succT n]) Δ))))
    (dCong : ∀ n, Zekd (βCong n) e (max k n) d c
      (insert (∼(ψ/[succT n])) (insert (ψ/[nm (n + 1)]) Δ))) :
    Zekd αAll e k d c (insert (∀⁰ ψ) Δ) :=
  inductionLeaf_allOmegaFromStep_probe β hβAllLt hβNF hαAllNF hβτ hbase
    (fun n dIH =>
      inductionLeaf_cutTowerStepWithTerm_probe (succT n) (hstep n) hmemEx (hψc n) (hsuccc n)
        (hIHlt n) (hExlt n) (hAlt n) (hBlt n) (hAndlt n)
        (hStepLt n) (hCongLt n)
        (hβNF n) (hANF n) (hBNF n) (hAndNF n) (hExNF n) (hStepNF n)
        (hCongNF n) (hβNF (n + 1))
        (hβτ n) (hAτ n) (hBτ n) (hAndτ n) (hExτ n) (hStepτ n) (hCongτ n)
        dIH (dA n) (dB n) (dCong n))

end GoodsteinPA.OperatorZinfty
