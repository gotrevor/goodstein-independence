/-
# `XFreeCutElim.lean` — C₁: `XFreeAx`-preserving cut-elimination over `LX`

The corollary `orderType_le_of_TIderiv` (Boundedness, lap 14) consumes a **cut-free** (`d.cr = 0`)
`XFreeAx` derivation of `{TI}`. The embedding (C₂) supplies a derivation of some finite cut rank `c`
with `XFreeAx`; this file reduces it to cut rank `0` **while preserving `XFreeAx`** — the missing
input to the corollary, hence to Thm 5.6 (`Z ⊢ TI_≺(X) ⟹ ‖≺‖ < ε₀`).

## Why a port (not a transport of `ZinftyGen.cutElim`)
`ZinftyGen.Provable.cutElim` already cut-eliminates generically over `{L}` — but it returns
`Provable` (`∃ d, …`), discarding the derivation, so the `XFreeAx` of its *output* is unrecoverable.
We therefore carry the leaf predicate through every reduction in a cut-rank-bearing twin
`PXFc α c Γ := ∃ d, d.o ≤ α ∧ d.cr ≤ c ∧ XFreeAx d` (generalising lap-14's `PXF = PXFc · 0`).

## The one faithfulness subtlety, resolved (lap-15 review)
Cut-elimination's only truth-layer steps are the **atomic** ones (`atomCut`/`removeFalseLit`), which
emit `axTrue` leaves on the cut atom. On an X-atom that would be a lone X-`axTrue` ⟹ break `XFreeAx`.
But it never happens: (i) our `Deriv.axL` is the **same-atom** EM axiom `{Xs,¬Xs}`, so an X-atomic
cut closes by **set idempotence** (the `axL` branch, truth-free); (ii) the truth-surgery branch fires
only on an `axTrue` leaf *equal to* the cut atom — i.e. an X-`axTrue` leaf — which `XFreeAx` forbids,
so it is **vacuous**. Hence `removeFalseLit` is only ever invoked on X-FREE cut atoms (emitting X-free
`axTrue`, fine for `XFreeAx`). The full chain therefore preserves `XFreeAx` at cut rank 0.
-/
import GoodsteinPA.Boundedness

namespace GoodsteinPA.XFreeCutElim

open LO LO.FirstOrder
open GoodsteinPA.ZinftyGen GoodsteinPA.LangX GoodsteinPA.Boundedness

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-- **Cut-rank-carrying `XFreeAx` provability** over `LX`: a derivation of ordinal height `≤ α`, cut
rank `≤ c`, all of whose `axTrue` leaves are X-free. `PXFc α 0 ↔ PXF α` (cut-free case, lap 14). -/
def PXFc (α : Ordinal.{0}) (c : ℕ) (Γ : Seq LX) : Prop :=
  ∃ d : Deriv Γ, d.o ≤ α ∧ d.cr ≤ (c : ℕ∞) ∧ XFreeAx d

/-! ### Bridge to the lap-14 cut-free carrier `PXF` -/

theorem PXF.toPXFc {α : Ordinal.{0}} {Γ : Seq LX} : PXF α Γ → PXFc α 0 Γ
  | ⟨d, ho, hcr, hxf⟩ => ⟨d, ho, by simp [hcr], hxf⟩

theorem PXFc.toPXF {α : Ordinal.{0}} {Γ : Seq LX} : PXFc α 0 Γ → PXF α Γ
  | ⟨d, ho, hcr, hxf⟩ => ⟨d, ho, nonpos_iff_eq_zero.mp (by simpa using hcr), hxf⟩

/-! ### Smart builders (mirror `ZinftyGen.Provable.*`, carrying `XFreeAx`) -/

theorem PXFc.mono {α β : Ordinal.{0}} {c c' : ℕ} (hα : α ≤ β) (hc : c ≤ c') {Γ : Seq LX} :
    PXFc α c Γ → PXFc β c' Γ
  | ⟨d, ho, hcr, hxf⟩ => ⟨d, ho.trans hα, hcr.trans (by exact_mod_cast hc), hxf⟩

theorem PXFc.weakening {α : Ordinal.{0}} {c : ℕ} {Γ Δ : Seq LX} (h : Γ ⊆ Δ) :
    PXFc α c Γ → PXFc α c Δ
  | ⟨d, ho, hcr, hxf⟩ =>
    ⟨Deriv.weak d h, by simpa only [Deriv.o] using ho, by simpa only [Deriv.cr] using hcr, hxf⟩

theorem PXFc.cast {α : Ordinal.{0}} {c : ℕ} {Γ Δ : Seq LX} (e : Γ = Δ) :
    PXFc α c Γ → PXFc α c Δ := fun h => e ▸ h

theorem PXFc.axL {Γ : Seq LX} {k} (r : LX.Rel k) (v) (hp : Semiformula.rel r v ∈ Γ)
    (hn : Semiformula.nrel r v ∈ Γ) : PXFc 0 0 Γ :=
  ⟨Deriv.axL r v hp hn, by simp [Deriv.o], by simp [Deriv.cr], by simp [XFreeAx]⟩

theorem PXFc.axTrue {Γ : Seq LX} {k} (b : Bool) (r : LX.Rel k) (v) (hxfree : Sum.isLeft r = true)
    (htrue : LitTrue (signedLit b r v)) (hmem : signedLit b r v ∈ Γ) : PXFc 0 0 Γ :=
  ⟨Deriv.axTrue b r v htrue hmem, by simp [Deriv.o], by simp [Deriv.cr], hxfree⟩

theorem PXFc.verumR {Γ : Seq LX} (h : (⊤ : Form LX) ∈ Γ) : PXFc 0 0 Γ :=
  ⟨Deriv.verumR h, by simp [Deriv.o], by simp [Deriv.cr], by simp [XFreeAx]⟩

theorem PXFc.andI {α β : Ordinal.{0}} {c : ℕ} {Γ : Seq LX} (φ ψ : Form LX)
    (hφ : PXFc α c (insert φ Γ)) (hψ : PXFc β c (insert ψ Γ)) :
    PXFc (max α β + 1) c (insert (φ ⋏ ψ) Γ) :=
  match hφ, hψ with
  | ⟨dφ, hoφ, hcφ, hxφ⟩, ⟨dψ, hoψ, hcψ, hxψ⟩ =>
    ⟨Deriv.andI φ ψ dφ dψ, by simp only [Deriv.o]; exact add_le_add (max_le_max hoφ hoψ) le_rfl,
      by simp only [Deriv.cr]; exact max_le hcφ hcψ, ⟨hxφ, hxψ⟩⟩

theorem PXFc.orI {α : Ordinal.{0}} {c : ℕ} {Γ : Seq LX} (φ ψ : Form LX)
    (h : PXFc α c (insert φ (insert ψ Γ))) : PXFc (α + 1) c (insert (φ ⋎ ψ) Γ) :=
  match h with
  | ⟨d, ho, hc, hx⟩ =>
    ⟨Deriv.orI φ ψ d, by simp only [Deriv.o]; gcongr, by simp only [Deriv.cr]; exact hc, hx⟩

theorem PXFc.exI {α : Ordinal.{0}} {c : ℕ} {Γ : Seq LX} (φ : SyntacticSemiformula LX 1) (n : ℕ)
    (h : PXFc α c (insert (φ/[nm n]) Γ)) : PXFc (α + 1) c (insert (∃⁰ φ) Γ) :=
  match h with
  | ⟨d, ho, hc, hx⟩ =>
    ⟨Deriv.exI φ n d, by simp only [Deriv.o]; gcongr, by simp only [Deriv.cr]; exact hc, hx⟩

theorem PXFc.allω {β : ℕ → Ordinal.{0}} {c : ℕ} {Γ : Seq LX} (φ : SyntacticSemiformula LX 1)
    (h : ∀ n, PXFc (β n) c (insert (φ/[nm n]) Γ)) : PXFc ((⨆ n, β n) + 1) c (insert (∀⁰ φ) Γ) := by
  choose d ho hc hx using h
  refine ⟨Deriv.allω φ d, ?_, ?_, hx⟩
  · simp only [Deriv.o]
    exact add_le_add (Ordinal.iSup_le fun n => (ho n).trans (Ordinal.le_iSup β n)) le_rfl
  · simp only [Deriv.cr]; exact iSup_le hc

theorem PXFc.cut {α β : Ordinal.{0}} {c : ℕ} {Γ : Seq LX} (χ : Form LX)
    (hc : (χ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞))
    (h₁ : PXFc α c (insert χ Γ)) (h₂ : PXFc β c (insert (∼χ) Γ)) :
    PXFc (max α β + 1) c Γ :=
  match h₁, h₂ with
  | ⟨d₁, ho₁, hcr₁, hx₁⟩, ⟨d₂, ho₂, hcr₂, hx₂⟩ =>
    ⟨Deriv.cut χ d₁ d₂, by simp only [Deriv.o]; exact add_le_add (max_le_max ho₁ ho₂) le_rfl,
      by simp only [Deriv.cr]; exact max_le hc (max_le hcr₁ hcr₂), ⟨hx₁, hx₂⟩⟩

theorem PXFc.contr {α : Ordinal.{0}} {c : ℕ} {Γ : Seq LX} (φ : Form LX)
    (h : PXFc α c (insert φ (insert φ Γ))) : PXFc α c (insert φ Γ) := by
  simpa [Finset.insert_idem] using h

end GoodsteinPA.XFreeCutElim
