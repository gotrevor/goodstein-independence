/-
# `ZefSlotCalculus` — the resolution-(2) slot calculus, and the running-family reduction closing SORRY-FREE

Capstone of REBUILD-Z laps 2–3.  Lap 2 localized pins 1–2 to ONE gap (the principal-`exI`
running-family stage can't be lowered under the fixed `hardy e m` bound); lap 3
(`wip/ZefResolutionProbe.lean`) verified the fix numerically: a CARRIED slot `f : ℕ → ℕ` (E–W's
number-theoretic operator, witness bound `n ≤ f 0`, ω-branch relativization `rel1 f n`) with the
reduction output slot **`g∘f`** (∀-family slot ∘ ∃-side slot) — NOT the pins' `f∘g`.

**This file is the definitive proof of viability:** the minimal slot calculus `Zef` (`Zeh` with
the stage `m` replaced by the slot `f`) plus `redDeriv_slot` — the FULL running-family reduction,
closing SORRY-FREE.  The gap that the fixed-`hardy e m` bound could not cross is gone: the
principal `exI` re-slots both cut premises to `g∘f`, and the `allω` reassembly threads by
`rel1_comp` (`rel1 (g∘f) n = g ∘ rel1 f n`, definitional).

Slots are taken monotone + inflationary (every E–W / `NormControlled` operator is; `rel1` and `∘`
preserve both) — the only extra bookkeeping vs the stage calculus, threaded through the induction.

Off the live build (`wip/`, not in a `lean_lib`); `lake env lean wip/ZefSlotCalculus.lean`.
-/
import GoodsteinPA.OperatorZeh

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.FastGrowing
open GoodsteinPA.OperatorZinfty

/-! ## The slot calculus `Zef` (`Zeh` with stage `m` ⤳ slot `f : ℕ → ℕ`) -/

inductive Zef : ONote → ONote → (ONote → Prop) → (ℕ → ℕ) → ℕ → Seq → Prop
  | axL {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq} {ar : ℕ}
      (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zef α e H f c Γ
  | wk {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Seq}
      (hsub : Δ ⊆ Γ) (dd : Zef α e H f c Δ) : Zef α e H f c Γ
  | weak {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Seq}
      (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β)
      (hsub : Δ ⊆ Γ) (dd : Zef β e H f c Δ) : Zef α e H f c Γ
  | allω {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (φ : SyntacticSemiformula ℒₒᵣ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF)
      (hβH : ∀ n, relOp H n (β n))
      (dd : ∀ n, Zef (β n) e (adjoin H n) (rel1 f n) c (insert (φ/[nm n]) Γ)) :
      Zef α e H f c (insert (∀⁰ φ) Γ)
  | exI {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β) (hbound : n ≤ f 0)
      (dd : Zef β e H f c (insert (φ/[nm n]) Γ)) : Zef α e H f c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (φ : Form) (hcompl : φ.complexity < c) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
      (hβφH : Cl H βφ) (hβψH : Cl H βψ)
      (d₁ : Zef βφ e H f c (insert φ Γ)) (d₂ : Zef βψ e H f c (insert (∼φ) Γ)) :
      Zef α e H f c Γ

namespace Zef

/-- Sequent weakening (height-preserving). -/
theorem weakening {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Seq}
    (hsub : Δ ⊆ Γ) (dd : Zef α e H f c Δ) : Zef α e H f c Γ :=
  Zef.wk hsub dd

/-- **Slot weakening** (`mono_f` — the slot analog of `Zeh.mono_H`'s stage-raise): a larger slot
is more permissive.  `exI` rides `n ≤ f 0 ≤ f' 0`; `allω` rides `rel1_mono`. -/
theorem mono_f : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef α e H f c Γ → ∀ {f' : ℕ → ℕ}, (∀ x, f x ≤ f' x) → Zef α e H f' c Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL r v hp hn => intro f' _; exact Zef.axL r v hp hn
  | wk hsub _ ih => intro f' hff'; exact Zef.wk hsub (ih hff')
  | weak hβ hβNF hαNF hβH hsub _ ih =>
      intro f' hff'; exact Zef.weak hβ hβNF hαNF hβH hsub (ih hff')
  | allω φ β hβ hβNF hαNF hβH _ ih =>
      intro f' hff'
      exact Zef.allω φ β hβ hβNF hαNF hβH (fun n => ih n (rel1_mono hff' n))
  | exI φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro f' hff'
      exact Zef.exI φ n hβ hβNF hαNF hβH (le_trans hbound (hff' 0)) (ih hff')
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro f' hff'
      exact Zef.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH (ih₁ hff') (ih₂ hff')

/-- **Operator irrelevance** (R1, slot form): the generator slot `H` carries no information
(every `Cl H β` side condition is at an NF ordinal — `Cl_of_NF`), so a derivation at `H` is one
at any `H'`, same `(α, e, f, c, Γ)`.  Mirrors `Zeh.change_H`. -/
theorem change_H : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef α e H f c Γ → ∀ {H' : ONote → Prop}, Zef α e H' f c Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL r v hp hn => intro H'; exact Zef.axL r v hp hn
  | wk hsub _ ih => intro H'; exact Zef.wk hsub ih
  | weak hβ hβNF hαNF _ hsub _ ih => intro H'; exact Zef.weak hβ hβNF hαNF (Cl_of_NF hβNF) hsub ih
  | allω φ β hβ hβNF hαNF _ _ ih =>
      intro H'; exact Zef.allω φ β hβ hβNF hαNF (fun n => Cl_of_NF (hβNF n)) (fun n => ih n)
  | exI φ n hβ hβNF hαNF _ hbound _ ih =>
      intro H'; exact Zef.exI φ n hβ hβNF hαNF (Cl_of_NF hβNF) hbound ih
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF _ _ _ _ ih₁ ih₂ =>
      intro H'; exact Zef.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF
        (Cl_of_NF hβφNF) (Cl_of_NF hβψNF) ih₁ ih₂

end Zef

/-- The `≤`-slack wrapper (slot form of `ZehProv`). -/
def ZefProv (α e : ONote) (H : ONote → Prop) (f : ℕ → ℕ) (c : ℕ) (Γ : Seq) : Prop :=
  ∃ α', α' ≤ α ∧ α'.NF ∧ Cl H α' ∧ Zef α' e H f c Γ

namespace ZefProv

theorem of {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
    (hNF : α.NF) (hH : Cl H α) (D : Zef α e H f c Γ) : ZefProv α e H f c Γ :=
  ⟨α, le_refl _, hNF, hH, D⟩

theorem mono {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
    (hα : α ≤ β) : ZefProv α e H f c Γ → ZefProv β e H f c Γ := by
  rintro ⟨α', hα', hNF, hH, D⟩
  exact ⟨α', le_trans hα' hα, hNF, hH, D⟩

theorem weakening {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ Δ : Seq}
    (h : Γ ⊆ Δ) : ZefProv α e H f c Γ → ZefProv α e H f c Δ := by
  rintro ⟨α', hα', hNF, hH, D⟩
  exact ⟨α', hα', hNF, hH, D.wk h⟩

end ZefProv

/-! ## The re-slot domination facts (lap-3 probe, restated for `rel1 · ·` slots) -/

/-- `rel1 f n` inherits monotonicity from `f`. -/
theorem rel1_monotone {f : ℕ → ℕ} (hf : Monotone f) (n : ℕ) : Monotone (rel1 f n) :=
  fun _ _ h => hf (max_le_max (le_refl n) h)

/-- `rel1 f n` inherits inflationarity from `f` (`x ≤ rel1 f n x`). -/
theorem rel1_infl {f : ℕ → ℕ} (hf : ∀ x, x ≤ f x) (n : ℕ) : ∀ x, x ≤ rel1 f n x :=
  fun x => le_trans (le_max_right n x) (hf (max n x))

/-- **The ∀-family member re-slots to `g∘f`** (lap-3 `reslot_gof_family`): for `g` monotone, `f`
monotone + inflationary, and witness `n ≤ f 0`, `rel1 g n ≤ g∘f` pointwise. -/
theorem reslot_family {f g : ℕ → ℕ} (hg_mono : Monotone g)
    (hf_infl : ∀ x, x ≤ f x) (hf_mono : Monotone f) {n : ℕ} (hn : n ≤ f 0) :
    ∀ x, rel1 g n x ≤ (g ∘ f) x := by
  intro x
  simp only [rel1, Function.comp]
  refine hg_mono ?_
  rcases le_total n x with h | h
  · rw [max_eq_right h]; exact hf_infl x
  · rw [max_eq_left h]; exact le_trans hn (hf_mono (Nat.zero_le x))

/-- **The ∃-side reduct re-slots to `g∘f`** (lap-3 `reslot_gof_exside`): `f ≤ g∘f` for `g`
inflationary. -/
theorem reslot_exside {f g : ℕ → ℕ} (hg_infl : ∀ x, x ≤ g x) :
    ∀ x, f x ≤ (g ∘ f) x := fun x => hg_infl (f x)

/-! ## The running-family reduction, SORRY-FREE (the lap-2 gap, now closed) -/

/-- **`redDeriv_slot`** — the full Towsner §19.6 running-family cut-reduction in the slot
calculus, output slot `g∘f`.  The lap-2 `redDeriv` port with the stage `m` replaced by the
current slot `f'` (threaded monotone + inflationary) and the two axis-critical moves:
- **principal `exI`** — both cut premises re-slot to `g∘f'` (`reslot_family` / `reslot_exside`),
  cut lands at `g∘f'` (the conclusion slot) with NO leak — the gap the fixed `hardy e m` bound
  could not cross;
- **`allω`** — each branch's IH output slot `g ∘ rel1 f' n` is `rel1 (g∘f') n` by `rel1_comp`
  (definitional), exactly the `allω` node's branch slot. -/
theorem redDeriv_slot {φ : SyntacticSemiformula ℒₒᵣ 1} {c : ℕ} {α e : ONote} {Γ : Seq}
    {g : ℕ → ℕ} (hφc : φ.complexity < c) (hαNF : α.NF) (heNF : e.NF)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (fam : ∀ n (H' : ONote → Prop), Zef α e H' (rel1 g n) c (insert (φ/[nm n]) Γ)) :
    ∀ {γ : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Δ : Seq}, Zef γ e H f c Δ → γ.NF →
      Monotone f → (∀ x, x ≤ f x) → (∃⁰ ∼φ) ∈ Δ →
      ZefProv (osucc (α + γ)) e H (g ∘ f) c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  intro γ H f Δ D
  induction D with
  | @axL γ e H f c Δ ar r v hp hn =>
      intro hγNF _ _ hmem
      refine ZefProv.of (osucc_NF (ONote.add_nf α γ)) (Cl_of_NF (osucc_NF (ONote.add_nf α γ))) ?_
      exact Zef.axL r v
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩))
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩))
  | @wk γ e H f c Δsub Δsup hsub D' ih =>
      intro hγNF hmono hinfl hmem
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact (ih hφc heNF fam hγNF hmono hinfl hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)
      · refine ⟨γ, le_trans (Zekd.le_add_left_NF hαNF hγNF)
          (le_of_lt (Zekd.lt_osucc (ONote.add_nf α γ))), hγNF, Cl_of_NF hγNF,
          (D'.mono_f (reslot_exside hg_infl)).wk (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩
  | @weak γ β e H f c Δsub Δsup hβ hβNF hγNF' hβH hsub D' ih =>
      intro hγNF hmono hinfl hmem
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact ((ih hφc heNF fam hβNF hmono hinfl hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)).mono
          (le_of_lt (Zekd.add_osucc_descent hαNF hβNF hγNF hβ))
      · refine ⟨β, le_of_lt (lt_of_lt_of_le hβ (le_trans (Zekd.le_add_left_NF hαNF hγNF)
          (le_of_lt (Zekd.lt_osucc (ONote.add_nf α γ))))), hβNF, Cl_of_NF hβNF,
          (D'.mono_f (reslot_exside hg_infl)).wk (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩
  | @allω γ e H f c Γ₀ χ β hβ hβNF hγNF' hβH dd ih =>
      intro hγNF hmono hinfl hmem
      have hhead : (∀⁰ χ) ≠ (∃⁰ ∼φ) := by intro h; simp [UnivQuantifier.all, ExsQuantifier.exs] at h
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have hsuccNF : (osucc (α + γ)).NF := osucc_NF (ONote.add_nf α γ)
      have ihn : ∀ n, ZefProv (osucc (α + β n)) e (adjoin H n) (g ∘ rel1 f n) c
          (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
        intro n
        exact (ih n hφc heNF fam (hβNF n) (rel1_monotone hmono n) (rel1_infl hinfl n)
          (Finset.mem_insert_of_mem hmem0)).weakening (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine ZefProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
      have hAll : Zef (osucc (α + γ)) e H (g ∘ f) c
          (insert (∀⁰ χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
        -- branch slot `g ∘ rel1 f n` is `rel1 (g∘f) n` by `rel1_comp` (definitional)
        refine Zef.allω χ (fun n => (ihn n).choose)
          (fun n => lt_of_le_of_lt (ihn n).choose_spec.1
            (Zekd.add_osucc_descent hαNF (hβNF n) hγNF (hβ n)))
          (fun n => (ihn n).choose_spec.2.1) hsuccNF
          (fun n => Cl_of_NF (ihn n).choose_spec.2.1)
          (fun n => (ihn n).choose_spec.2.2.2)
      exact hAll.wk (by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl ⟨hhead, Or.inl rfl⟩
        · tauto)
  | @exI γ β e H f c Γ₀ χ n hβ hβNF hγNF' hβH hbound dχ ih =>
      intro hγNF hmono hinfl hmem
      have hsuccNF : (osucc (α + γ)).NF := osucc_NF (ONote.add_nf α γ)
      by_cases hhd : (∃⁰ χ) = (∃⁰ ∼φ)
      · -- PRINCIPAL: χ = ∼φ; cut `fam n` (re-slotted to `g∘f`) against the ∃-premise.
        have hχ : χ = ∼φ := by simpa [ExsQuantifier.exs] using hhd
        subst hχ
        rw [Finset.erase_insert_eq_erase]
        have hNeg : (∼φ)/[nm n] = ∼(φ/[nm n]) := by simp
        have hcompl : (φ/[nm n]).complexity < c := by simpa using hφc
        -- `fam n` re-slots `rel1 g n → g∘f` (both premises land at the conclusion slot `g∘f`)
        have famn : Zef α e H (g ∘ f) c (insert (φ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          ((fam n H).mono_f (reslot_family hg_mono hinfl hmono hbound)).wk (by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_union] at hx ⊢; tauto)
        have hαlt : α < osucc (α + γ) :=
          lt_of_le_of_lt (Zekd.le_add_right_NF hαNF hγNF) (Zekd.lt_osucc (ONote.add_nf α γ))
        by_cases hd : (∃⁰ ∼φ) ∈ Γ₀
        · obtain ⟨a, hale, haNF, haH, Da⟩ := ih hφc heNF fam hβNF hmono hinfl
            (Finset.mem_insert_of_mem hd)
          have Da' : Zef a e H (g ∘ f) c
              (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
            Da.wk (by
              intro x hx
              simp only [hNeg, Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
          refine ZefProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
          exact Zef.cut (φ/[nm n]) hcompl hαlt
            (lt_of_le_of_lt hale (Zekd.add_osucc_descent hαNF hβNF hγNF hβ))
            hαNF haNF hsuccNF (Cl_of_NF hαNF) haH famn Da'
        · -- ∃-premise `dχ` re-slots `f → g∘f`
          have Dβ' : Zef β e H (g ∘ f) c
              (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
            (dχ.mono_f (reslot_exside hg_infl)).wk (by
              intro x hx
              simp only [hNeg, Finset.mem_insert] at hx
              simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
              rcases hx with rfl | hxΓ₀
              · exact Or.inl rfl
              · exact Or.inr (Or.inl ⟨fun e0 => hd (e0 ▸ hxΓ₀), hxΓ₀⟩))
          refine ZefProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
          exact Zef.cut (φ/[nm n]) hcompl hαlt
            (lt_of_lt_of_le hβ (le_trans (Zekd.le_add_left_NF hαNF hγNF)
              (le_of_lt (Zekd.lt_osucc (ONote.add_nf α γ)))))
            hαNF hβNF hsuccNF (Cl_of_NF hαNF) (Cl_of_NF hβNF) famn Dβ'
      · have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        obtain ⟨a, hale, haNF, haH, Da⟩ := ih hφc heNF fam hβNF hmono hinfl
          (Finset.mem_insert_of_mem hmem0)
        have Da' : Zef a e H (g ∘ f) c (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          Da.wk (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
        refine ZefProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
        -- non-principal `exI`: witness bound `n ≤ f 0 ≤ (g∘f) 0` (via `hg_infl` at `f 0`)
        have hbound' : n ≤ (g ∘ f) 0 := le_trans hbound (hg_infl (f 0))
        have hExI : Zef (osucc (α + γ)) e H (g ∘ f) c
            (insert (∃⁰ χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          Zef.exI χ n (lt_of_le_of_lt hale (Zekd.add_osucc_descent hαNF hβNF hγNF hβ))
            haNF hsuccNF haH hbound' Da'
        exact hExI.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl ⟨hhd, Or.inl rfl⟩
          · tauto)
  | @cut γ βφ βψ e H f c Γ₀ χ hχc hβφ hβψ hβφNF hβψNF hγNF' hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hγNF hmono hinfl hmem
      obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, D₁⟩ := ih₁ hφc heNF fam hβφNF hmono hinfl (Finset.mem_insert_of_mem hmem)
      obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, D₂⟩ := ih₂ hφc heNF fam hβψNF hmono hinfl (Finset.mem_insert_of_mem hmem)
      have hsuccNF : (osucc (α + γ)).NF := osucc_NF (ONote.add_nf α γ)
      have D₁' : Zef a₁ e H (g ∘ f) c (insert χ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        D₁.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      have D₂' : Zef a₂ e H (g ∘ f) c (insert (∼χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        D₂.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine ZefProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
      exact Zef.cut χ hχc
        (lt_of_le_of_lt ha₁le (Zekd.add_osucc_descent hαNF hβφNF hγNF hβφ))
        (lt_of_le_of_lt ha₂le (Zekd.add_osucc_descent hαNF hβψNF hγNF hβψ))
        ha₁NF ha₂NF hsuccNF ha₁H ha₂H D₁' D₂'

end GoodsteinPA.OperatorZeh
