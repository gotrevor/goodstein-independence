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

/-! ### Inversions at cut rank `≤ c`, preserving `XFreeAx` (port of `ZinftyGen.{orInvAux,andInvAux,
allInvAux}`). The `cut` case is now real (recurse on both premises, re-cut on the cut formula —
truth-free, `XFreeAx` threads); the lap-14 cr=0 inversions made it vacuous. -/

theorem orInvAux_x {φ ψ : Form LX} {c : ℕ} : ∀ {Γ : Seq LX} (d : Deriv Γ),
    XFreeAx d → d.cr ≤ (c : ℕ∞) → (φ ⋎ ψ) ∈ Γ →
    PXFc d.o c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  intro Γ d
  induction d with
  | @axL Γ k r v hp hn =>
    intro _ _ _
    have hr : Semiformula.rel r v ∈ Γ.erase (φ ⋎ ψ) :=
      Finset.mem_erase.mpr ⟨by intro h; simp [Vee.vee] at h, hp⟩
    have hn' : Semiformula.nrel r v ∈ Γ.erase (φ ⋎ ψ) :=
      Finset.mem_erase.mpr ⟨by intro h; simp [Vee.vee] at h, hn⟩
    simp only [Deriv.o]
    exact (PXFc.axL r v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn'))).mono le_rfl (Nat.zero_le c)
  | @axTrue Γ k b r v htrue hmem =>
    intro hxf _ _
    have hl : signedLit b r v ∈ Γ.erase (φ ⋎ ψ) :=
      Finset.mem_erase.mpr ⟨by cases b <;> simp [signedLit, Vee.vee], hmem⟩
    simp only [Deriv.o]
    exact (PXFc.axTrue b r v hxf htrue
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hl))).mono le_rfl (Nat.zero_le c)
  | @verumR Γ h =>
    intro _ _ _
    have ht : (⊤ : Form LX) ∈ Γ.erase (φ ⋎ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩
    simp only [Deriv.o]
    exact (PXFc.verumR (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ht))).mono
      le_rfl (Nat.zero_le c)
  | @weak Δ Γ d' hsub ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hd : (φ ⋎ ψ) ∈ Δ
    · exact (ih hxf hcr hd).weakening
        (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub)))
    · have base : PXFc d'.o c Δ := ⟨d', le_rfl, hcr, hxf⟩
      refine base.weakening ?_
      intro x hx
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @andI Γ₀ φ' ψ' dφ dψ ihφ ihψ =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (φ' ⋏ ψ') ≠ (φ ⋎ ψ) := by intro h; simp [Wedge.wedge, Vee.vee] at h
    have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hcrφ : dφ.cr ≤ (c : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcrψ : dψ.cr ≤ (c : ℕ∞) := le_trans (le_max_right _ _) hcr
    have Pφ := (ihφ hxf.1 hcrφ (Finset.mem_insert_of_mem hmem0)).weakening (invPushOr φ ψ φ' Γ₀)
    have Pψ := (ihψ hxf.2 hcrψ (Finset.mem_insert_of_mem hmem0)).weakening (invPushOr φ ψ ψ' Γ₀)
    exact (PXFc.andI φ' ψ' Pφ Pψ).weakening (invPullOr φ ψ hhead Γ₀)
  | @orI Γ₀ φ' ψ' d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hhd : (φ' ⋎ ψ') = (φ ⋎ ψ)
    · obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp hhd.symm
      by_cases hd : (φ ⋎ ψ) ∈ Γ₀
      · have P := ih hxf hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hd))
        refine (P.weakening ?_).mono (le_of_lt (lt_add_of_pos_right _ one_pos)) le_rfl
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
      · have base : PXFc d'.o c (insert φ (insert ψ Γ₀)) := ⟨d', le_rfl, hcr, hxf⟩
        refine (base.weakening ?_).mono (le_of_lt (lt_add_of_pos_right _ one_pos)) le_rfl
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        rcases hx with rfl | rfl | hx
        · tauto
        · tauto
        · exact Or.inr (Or.inr ⟨fun e => hd (e ▸ hx), Or.inr hx⟩)
    · have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
      have hsub : insert φ (insert ψ ((insert φ' (insert ψ' Γ₀)).erase (φ ⋎ ψ)))
            ⊆ insert φ' (insert ψ' (insert φ (insert ψ (Γ₀.erase (φ ⋎ ψ))))) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
      have P := (ih hxf hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening hsub
      exact (PXFc.orI φ' ψ' P).weakening (invPullOr φ ψ hhd Γ₀)
  | @allω Γ₀ χ d ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∀⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
    have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have key : ∀ n, PXFc (d n).o c (insert (χ/[nm n]) (insert φ (insert ψ (Γ₀.erase (φ ⋎ ψ))))) :=
      fun n => (ih n (hxf n) (le_trans (le_iSup (fun m => (d m).cr) n) hcr)
        (Finset.mem_insert_of_mem hmem0)).weakening (invPushOr φ ψ (χ/[nm n]) Γ₀)
    exact (PXFc.allω χ key).weakening (invPullOr φ ψ hhead Γ₀)
  | @exI Γ₀ χ n d ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∃⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
    have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P := (ih hxf hcr (Finset.mem_insert_of_mem hmem0)).weakening (invPushOr φ ψ (χ/[nm n]) Γ₀)
    exact (PXFc.exI χ n P).weakening (invPullOr φ ψ hhead Γ₀)
  | @cut Γ₀ χ d₁ d₂ ih₁ ih₂ =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hcχ : (χ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞) := (le_max_left _ _).trans hcr
    have hcr1 : d₁.cr ≤ (c : ℕ∞) := (le_max_left d₁.cr d₂.cr).trans ((le_max_right _ _).trans hcr)
    have hcr2 : d₂.cr ≤ (c : ℕ∞) := (le_max_right d₁.cr d₂.cr).trans ((le_max_right _ _).trans hcr)
    have P₁ := (ih₁ hxf.1 hcr1 (Finset.mem_insert_of_mem hmem)).weakening (invPushOr φ ψ χ Γ₀)
    have P₂ := (ih₂ hxf.2 hcr2 (Finset.mem_insert_of_mem hmem)).weakening (invPushOr φ ψ (∼χ) Γ₀)
    exact PXFc.cut χ hcχ P₁ P₂

/-- **∨-inversion at a relaxed bound**, `XFreeAx`-preserving. -/
theorem PXFc.orInv {α : Ordinal.{0}} {c : ℕ} {Γ : Seq LX} {φ ψ : Form LX} (hmem : (φ ⋎ ψ) ∈ Γ)
    (h : PXFc α c Γ) : PXFc α c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  rcases h with ⟨d, ho, hcr, hxf⟩
  exact (orInvAux_x d hxf hcr hmem).mono ho le_rfl

/-- **∧-inversion** (both conjuncts), cut rank `≤ c`, `XFreeAx`-preserving. -/
theorem andInvAux_x {φ ψ : Form LX} {c : ℕ} : ∀ {Γ : Seq LX} (d : Deriv Γ),
    XFreeAx d → d.cr ≤ (c : ℕ∞) → (φ ⋏ ψ) ∈ Γ →
    PXFc d.o c (insert φ (Γ.erase (φ ⋏ ψ))) ∧ PXFc d.o c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  intro Γ d
  induction d with
  | @axL Γ k r v hp hn =>
    intro _ _ _
    have hr : Semiformula.rel r v ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩
    have hn' : Semiformula.nrel r v ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩
    simp only [Deriv.o]
    exact ⟨(PXFc.axL r v (Finset.mem_insert_of_mem hr) (Finset.mem_insert_of_mem hn')).mono
        le_rfl (Nat.zero_le c),
      (PXFc.axL r v (Finset.mem_insert_of_mem hr) (Finset.mem_insert_of_mem hn')).mono
        le_rfl (Nat.zero_le c)⟩
  | @axTrue Γ k b r v htrue hmem =>
    intro hxf _ _
    have hl : signedLit b r v ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by cases b <;> simp [signedLit]), hmem⟩
    simp only [Deriv.o]
    exact ⟨(PXFc.axTrue b r v hxf htrue (Finset.mem_insert_of_mem hl)).mono le_rfl (Nat.zero_le c),
      (PXFc.axTrue b r v hxf htrue (Finset.mem_insert_of_mem hl)).mono le_rfl (Nat.zero_le c)⟩
  | @verumR Γ h =>
    intro _ _ _
    have ht : (⊤ : Form LX) ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩
    simp only [Deriv.o]
    exact ⟨(PXFc.verumR (Finset.mem_insert_of_mem ht)).mono le_rfl (Nat.zero_le c),
      (PXFc.verumR (Finset.mem_insert_of_mem ht)).mono le_rfl (Nat.zero_le c)⟩
  | @weak Δ Γ d' hsub ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hd : (φ ⋏ ψ) ∈ Δ
    · exact ⟨(ih hxf hcr hd).1.weakening
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)),
        (ih hxf hcr hd).2.weakening
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub))⟩
    · have base : PXFc d'.o c Δ := ⟨d', le_rfl, hcr, hxf⟩
      have hΔ : Δ ⊆ Γ.erase (φ ⋏ ψ) := fun x hx =>
        Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩
      exact ⟨base.weakening (fun x hx => Finset.mem_insert_of_mem (hΔ hx)),
        base.weakening (fun x hx => Finset.mem_insert_of_mem (hΔ hx))⟩
  | @andI Γ₀ φ' ψ' dφ dψ ihφ ihψ =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hcrφ : dφ.cr ≤ (c : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcrψ : dψ.cr ≤ (c : ℕ∞) := le_trans (le_max_right _ _) hcr
    have hbφ : dφ.o ≤ max dφ.o dψ.o + 1 :=
      le_trans (le_max_left _ _) (le_of_lt (lt_add_of_pos_right _ one_pos))
    have hbψ : dψ.o ≤ max dφ.o dψ.o + 1 :=
      le_trans (le_max_right _ _) (le_of_lt (lt_add_of_pos_right _ one_pos))
    by_cases hhd : (φ' ⋏ ψ') = (φ ⋏ ψ)
    · obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp hhd.symm
      have hL : PXFc (max dφ.o dψ.o + 1) c (insert φ ((insert (φ ⋏ ψ) Γ₀).erase (φ ⋏ ψ))) := by
        by_cases hd : (φ ⋏ ψ) ∈ Γ₀
        · refine ((ihφ hxf.1 hcrφ (Finset.mem_insert_of_mem hd)).1.weakening ?_).mono hbφ le_rfl
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
        · have base : PXFc dφ.o c (insert φ Γ₀) := ⟨dφ, le_rfl, hcrφ, hxf.1⟩
          refine (base.weakening ?_).mono hbφ le_rfl
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr ⟨fun e => hd (e ▸ hx), Or.inr hx⟩
      have hR : PXFc (max dφ.o dψ.o + 1) c (insert ψ ((insert (φ ⋏ ψ) Γ₀).erase (φ ⋏ ψ))) := by
        by_cases hd : (φ ⋏ ψ) ∈ Γ₀
        · refine ((ihψ hxf.2 hcrψ (Finset.mem_insert_of_mem hd)).2.weakening ?_).mono hbψ le_rfl
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
        · have base : PXFc dψ.o c (insert ψ Γ₀) := ⟨dψ, le_rfl, hcrψ, hxf.2⟩
          refine (base.weakening ?_).mono hbψ le_rfl
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr ⟨fun e => hd (e ▸ hx), Or.inr hx⟩
      exact ⟨hL, hR⟩
    · have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
      refine ⟨?_, ?_⟩
      · have Pφ := ((ihφ hxf.1 hcrφ (Finset.mem_insert_of_mem hmem0)).1).weakening
          (invPush1' φ φ' (φ ⋏ ψ) Γ₀)
        have Pψ := ((ihψ hxf.2 hcrψ (Finset.mem_insert_of_mem hmem0)).1).weakening
          (invPush1' φ ψ' (φ ⋏ ψ) Γ₀)
        exact (PXFc.andI φ' ψ' Pφ Pψ).weakening (invPull1' φ hhd Γ₀)
      · have Pφ := ((ihφ hxf.1 hcrφ (Finset.mem_insert_of_mem hmem0)).2).weakening
          (invPush1' ψ φ' (φ ⋏ ψ) Γ₀)
        have Pψ := ((ihψ hxf.2 hcrψ (Finset.mem_insert_of_mem hmem0)).2).weakening
          (invPush1' ψ ψ' (φ ⋏ ψ) Γ₀)
        exact (PXFc.andI φ' ψ' Pφ Pψ).weakening (invPull1' ψ hhd Γ₀)
  | @orI Γ₀ φ' ψ' d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (φ' ⋎ ψ') ≠ (φ ⋏ ψ) := by intro h; simp [Vee.vee, Wedge.wedge] at h
    have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have mk : ∀ b : Form LX,
        PXFc d'.o c (insert b ((insert φ' (insert ψ' Γ₀)).erase (φ ⋏ ψ))) →
        PXFc (d'.o + 1) c (insert b ((insert (φ' ⋎ ψ') Γ₀).erase (φ ⋏ ψ))) := by
      intro b P
      have hsub : insert b ((insert φ' (insert ψ' Γ₀)).erase (φ ⋏ ψ))
            ⊆ insert φ' (insert ψ' (insert b (Γ₀.erase (φ ⋏ ψ)))) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
      exact (PXFc.orI φ' ψ' (P.weakening hsub)).weakening (invPull1' b hhead Γ₀)
    exact ⟨mk φ ((ih hxf hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).1),
      mk ψ ((ih hxf hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).2)⟩
  | @allω Γ₀ χ' d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∀⁰ χ') ≠ (φ ⋏ ψ) := by intro h; simp [Wedge.wedge] at h
    have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have mk : ∀ b : Form LX,
        (∀ m, PXFc (d' m).o c (insert b ((insert (χ'/[nm m]) Γ₀).erase (φ ⋏ ψ)))) →
        PXFc ((⨆ m, (d' m).o) + 1) c (insert b ((insert (∀⁰ χ') Γ₀).erase (φ ⋏ ψ))) := by
      intro b P
      have key : ∀ m, PXFc (d' m).o c (insert (χ'/[nm m]) (insert b (Γ₀.erase (φ ⋏ ψ)))) :=
        fun m => (P m).weakening (invPush1' b (χ'/[nm m]) (φ ⋏ ψ) Γ₀)
      exact (PXFc.allω χ' key).weakening (invPull1' b hhead Γ₀)
    refine ⟨mk φ (fun m => ?_), mk ψ (fun m => ?_)⟩
    · exact (ih m (hxf m) (le_trans (le_iSup (fun j => (d' j).cr) m) hcr)
        (Finset.mem_insert_of_mem hmem0)).1
    · exact (ih m (hxf m) (le_trans (le_iSup (fun j => (d' j).cr) m) hcr)
        (Finset.mem_insert_of_mem hmem0)).2
  | @exI Γ₀ χ' n d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∃⁰ χ') ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
    have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    refine ⟨?_, ?_⟩
    · have P := ((ih hxf hcr (Finset.mem_insert_of_mem hmem0)).1).weakening
        (invPush1' φ (χ'/[nm n]) (φ ⋏ ψ) Γ₀)
      exact (PXFc.exI χ' n P).weakening (invPull1' φ hhead Γ₀)
    · have P := ((ih hxf hcr (Finset.mem_insert_of_mem hmem0)).2).weakening
        (invPush1' ψ (χ'/[nm n]) (φ ⋏ ψ) Γ₀)
      exact (PXFc.exI χ' n P).weakening (invPull1' ψ hhead Γ₀)
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hcξ : (ξ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞) := (le_max_left _ _).trans hcr
    have hcr1 : d₁.cr ≤ (c : ℕ∞) := (le_max_left d₁.cr d₂.cr).trans ((le_max_right _ _).trans hcr)
    have hcr2 : d₂.cr ≤ (c : ℕ∞) := (le_max_right d₁.cr d₂.cr).trans ((le_max_right _ _).trans hcr)
    refine ⟨?_, ?_⟩
    · have P₁ := ((ih₁ hxf.1 hcr1 (Finset.mem_insert_of_mem hmem)).1).weakening
        (invPush1' φ ξ (φ ⋏ ψ) Γ₀)
      have P₂ := ((ih₂ hxf.2 hcr2 (Finset.mem_insert_of_mem hmem)).1).weakening
        (invPush1' φ (∼ξ) (φ ⋏ ψ) Γ₀)
      exact PXFc.cut ξ hcξ P₁ P₂
    · have P₁ := ((ih₁ hxf.1 hcr1 (Finset.mem_insert_of_mem hmem)).2).weakening
        (invPush1' ψ ξ (φ ⋏ ψ) Γ₀)
      have P₂ := ((ih₂ hxf.2 hcr2 (Finset.mem_insert_of_mem hmem)).2).weakening
        (invPush1' ψ (∼ξ) (φ ⋏ ψ) Γ₀)
      exact PXFc.cut ξ hcξ P₁ P₂

/-- **∧-inversion, left conjunct, relaxed bound**, `XFreeAx`-preserving. -/
theorem PXFc.andInvL {α : Ordinal.{0}} {c : ℕ} {Γ : Seq LX} {φ ψ : Form LX} (hmem : (φ ⋏ ψ) ∈ Γ)
    (h : PXFc α c Γ) : PXFc α c (insert φ (Γ.erase (φ ⋏ ψ))) := by
  rcases h with ⟨d, ho, hcr, hxf⟩
  exact (andInvAux_x d hxf hcr hmem).1.mono ho le_rfl

/-- **∧-inversion, right conjunct, relaxed bound**, `XFreeAx`-preserving. -/
theorem PXFc.andInvR {α : Ordinal.{0}} {c : ℕ} {Γ : Seq LX} {φ ψ : Form LX} (hmem : (φ ⋏ ψ) ∈ Γ)
    (h : PXFc α c Γ) : PXFc α c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  rcases h with ⟨d, ho, hcr, hxf⟩
  exact (andInvAux_x d hxf hcr hmem).2.mono ho le_rfl

/-- **ω/∀-inversion** at cut rank `≤ c`, `XFreeAx`-preserving. For the universal instance `i`. -/
theorem allInvAux_x {χ : SyntacticSemiformula LX 1} {c : ℕ} (i : ℕ) : ∀ {Γ : Seq LX} (d : Deriv Γ),
    XFreeAx d → d.cr ≤ (c : ℕ∞) → (∀⁰ χ) ∈ Γ →
    PXFc d.o c (insert (χ/[nm i]) (Γ.erase (∀⁰ χ))) := by
  intro Γ d
  induction d with
  | @axL Γ k r v hp hn =>
    intro _ _ _
    have hr : Semiformula.rel r v ∈ Γ.erase (∀⁰ χ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩
    have hn' : Semiformula.nrel r v ∈ Γ.erase (∀⁰ χ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩
    simp only [Deriv.o]
    exact (PXFc.axL r v (Finset.mem_insert_of_mem hr)
      (Finset.mem_insert_of_mem hn')).mono le_rfl (Nat.zero_le c)
  | @axTrue Γ k b r v htrue hmem =>
    intro hxf _ _
    have hl : signedLit b r v ∈ Γ.erase (∀⁰ χ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by cases b <;> simp [signedLit]), hmem⟩
    simp only [Deriv.o]
    exact (PXFc.axTrue b r v hxf htrue (Finset.mem_insert_of_mem hl)).mono le_rfl (Nat.zero_le c)
  | @verumR Γ h =>
    intro _ _ _
    have ht : (⊤ : Form LX) ∈ Γ.erase (∀⁰ χ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩
    simp only [Deriv.o]
    exact (PXFc.verumR (Finset.mem_insert_of_mem ht)).mono le_rfl (Nat.zero_le c)
  | @weak Δ Γ d' hsub ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hd : (∀⁰ χ) ∈ Δ
    · exact (ih hxf hcr hd).weakening
        (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub))
    · have base : PXFc d'.o c Δ := ⟨d', le_rfl, hcr, hxf⟩
      refine base.weakening ?_
      intro x hx
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
  | @andI Γ₀ φ' ψ' dφ dψ ihφ ihψ =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (φ' ⋏ ψ') ≠ (∀⁰ χ) := by intro h; simp [Wedge.wedge] at h
    have hmem0 : (∀⁰ χ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hcrφ : dφ.cr ≤ (c : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcrψ : dψ.cr ≤ (c : ℕ∞) := le_trans (le_max_right _ _) hcr
    have Pφ := (ihφ hxf.1 hcrφ (Finset.mem_insert_of_mem hmem0)).weakening
      (invPush1' (χ/[nm i]) φ' (∀⁰ χ) Γ₀)
    have Pψ := (ihψ hxf.2 hcrψ (Finset.mem_insert_of_mem hmem0)).weakening
      (invPush1' (χ/[nm i]) ψ' (∀⁰ χ) Γ₀)
    exact (PXFc.andI φ' ψ' Pφ Pψ).weakening (invPull1' (χ/[nm i]) hhead Γ₀)
  | @orI Γ₀ φ' ψ' d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (φ' ⋎ ψ') ≠ (∀⁰ χ) := by intro h; simp [Vee.vee] at h
    have hmem0 : (∀⁰ χ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hsub : insert (χ/[nm i]) ((insert φ' (insert ψ' Γ₀)).erase (∀⁰ χ))
          ⊆ insert φ' (insert ψ' (insert (χ/[nm i]) (Γ₀.erase (∀⁰ χ)))) := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
    have P := (ih hxf hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening hsub
    exact (PXFc.orI φ' ψ' P).weakening (invPull1' (χ/[nm i]) hhead Γ₀)
  | @allω Γ₀ χ' d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hhd : (∀⁰ χ') = (∀⁰ χ)
    · obtain rfl := (Semiformula.all_inj _ _).mp hhd
      have hcrn : (d' i).cr ≤ (c : ℕ∞) := le_trans (le_iSup (fun m => (d' m).cr) i) hcr
      have hbound : (d' i).o ≤ (⨆ m, (d' m).o) + 1 :=
        le_trans (Ordinal.le_iSup (fun m => (d' m).o) i) (le_of_lt (lt_add_of_pos_right _ one_pos))
      by_cases hd : (∀⁰ χ') ∈ Γ₀
      · have P := ih i (hxf i) hcrn (Finset.mem_insert_of_mem hd)
        refine (P.weakening ?_).mono hbound le_rfl
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
      · have base : PXFc (d' i).o c (insert (χ'/[nm i]) Γ₀) := ⟨d' i, le_rfl, hcrn, hxf i⟩
        refine (base.weakening ?_).mono hbound le_rfl
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · exact Or.inr ⟨fun e => hd (e ▸ hx), Or.inr hx⟩
    · have hmem0 : (∀⁰ χ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
      have key : ∀ m, PXFc (d' m).o c
          (insert (χ'/[nm m]) (insert (χ/[nm i]) (Γ₀.erase (∀⁰ χ)))) := fun m =>
        (ih m (hxf m) (le_trans (le_iSup (fun j => (d' j).cr) m) hcr)
          (Finset.mem_insert_of_mem hmem0)).weakening (invPush1' (χ/[nm i]) (χ'/[nm m]) (∀⁰ χ) Γ₀)
      exact (PXFc.allω χ' key).weakening (invPull1' (χ/[nm i]) hhd Γ₀)
  | @exI Γ₀ χ' n d' ih =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∃⁰ χ') ≠ (∀⁰ χ) := by intro h; simp [ExsQuantifier.exs, UnivQuantifier.all] at h
    have hmem0 : (∀⁰ χ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P := (ih hxf hcr (Finset.mem_insert_of_mem hmem0)).weakening
      (invPush1' (χ/[nm i]) (χ'/[nm n]) (∀⁰ χ) Γ₀)
    exact (PXFc.exI χ' n P).weakening (invPull1' (χ/[nm i]) hhead Γ₀)
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hxf hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hcξ : (ξ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞) := (le_max_left _ _).trans hcr
    have hcr1 : d₁.cr ≤ (c : ℕ∞) := (le_max_left d₁.cr d₂.cr).trans ((le_max_right _ _).trans hcr)
    have hcr2 : d₂.cr ≤ (c : ℕ∞) := (le_max_right d₁.cr d₂.cr).trans ((le_max_right _ _).trans hcr)
    have P₁ := (ih₁ hxf.1 hcr1 (Finset.mem_insert_of_mem hmem)).weakening
      (invPush1' (χ/[nm i]) ξ (∀⁰ χ) Γ₀)
    have P₂ := (ih₂ hxf.2 hcr2 (Finset.mem_insert_of_mem hmem)).weakening
      (invPush1' (χ/[nm i]) (∼ξ) (∀⁰ χ) Γ₀)
    exact PXFc.cut ξ hcξ P₁ P₂

/-- **ω-inversion at a relaxed bound**, `XFreeAx`-preserving. -/
theorem PXFc.allInv {α : Ordinal.{0}} {c : ℕ} {Γ : Seq LX} {χ : SyntacticSemiformula LX 1}
    (hmem : (∀⁰ χ) ∈ Γ) (i : ℕ) (h : PXFc α c Γ) :
    PXFc α c (insert (χ/[nm i]) (Γ.erase (∀⁰ χ))) := by
  rcases h with ⟨d, ho, hcr, hxf⟩
  exact (allInvAux_x i d hxf hcr hmem).mono ho le_rfl

end GoodsteinPA.XFreeCutElim
