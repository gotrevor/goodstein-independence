/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import OrdinalAnalysis.Gentzen.UpperBound

/-!
# `PA[X]` is conservative over `PA` for `X`-free sentences

Wu's `paLX_of_peano` transports a `𝗣𝗔` proof into `paLX`.  This file proves the converse for
sentences in the image of `Semiformula.lMap toLX`, which is what lets the Gentzen upper bound
be used as a lemma inside ordinary `PA`.

The proof is semantic, and follows `OrdinalAnalysis.Ramified.LiftR` (which does the same thing
for the ramified language): read `X` as the empty predicate.  Then every `LX`-formula has an
`ℒₒᵣ`-companion `eraseX φ` with the same truth value (`eval_eraseX`), so the induction scheme of
`paLX` — which is induction for *every* `LX`-formula — is discharged by `𝗣𝗔`'s induction for
`eraseX φ`.  Hence every model of `𝗣𝗔` expands to a model of `paLX`, and completeness does the
rest.

Main results:
* `lxStr`               the `LX`-structure on a model of arithmetic, `X` read as `P`
* `eval_eraseX`         `eraseX` is truth-preserving when `P` is empty
* `models_paLX_lxStrF`  every `𝗣𝗔`-model, with `X := ∅`, is a `paLX`-model
* `peano_of_paLX`       **conservation**
-/

open FFL.FirstOrder.Tarski

set_option autoImplicit false

namespace GoodsteinWu.Conservation

open Classical
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen

variable {M : Type} [s : Structure ℒₒᵣ M]

set_option warn.classDefReducibility false in
/-- The `LX`-structure on a model of arithmetic: the same arithmetic, `X` read as `P`. -/
def lxStr (P : M → Prop) : Structure LX M where
  func := fun {k} f v => match k, f with
    | _, Sum.inl f => s.func f v
    | _, Sum.inr (e : PEmpty) => e.elim
  rel := fun {k} r v => match k, r with
    | _, Sum.inl r => s.rel r v
    | _, Sum.inr XRel.X => P (v 0)

/-- Reading `X` does not disturb the arithmetic reduct. -/
theorem lxStr_lMap (P : M → Prop) : (lxStr P).lMap toLX = s := rfl

/-- `lxStr P` has true equality when `M` has. -/
theorem lxStr_eq (P : M → Prop) [Structure.Eq ℒₒᵣ M] :
    letI := lxStr P; Structure.Eq LX M :=
  letI := lxStr P
  ⟨fun a b => Structure.Eq.eq (L := ℒₒᵣ) a b⟩

/-! ### Erasing `X` -/

/-- Every function symbol of `LX` is arithmetic. -/
def lxFunc : {k : ℕ} → LX.Func k → (ℒₒᵣ : Language).Func k
  | _, Sum.inl f => f
  | _, Sum.inr (e : PEmpty) => e.elim

/-- Every `LX`-term comes from arithmetic. -/
def trmX {n : ℕ} : Semiterm LX ℕ n → Semiterm ℒₒᵣ ℕ n
  | Semiterm.bvar x => Semiterm.bvar x
  | Semiterm.fvar x => Semiterm.fvar x
  | Semiterm.func f v => Semiterm.func (lxFunc f) fun i => trmX (v i)

/-- `φ` with every atom `X t` replaced by `⊥`. -/
def eraseX : {n : ℕ} → Semiformula LX ℕ n → Semiformula ℒₒᵣ ℕ n
  | _, .verum => ⊤
  | _, .falsum => ⊥
  | _, .rel (arity := k) r v =>
      match k, r with
      | _, Sum.inl r => Semiformula.rel r fun i => trmX (v i)
      | _, Sum.inr XRel.X => ⊥
  | _, .nrel (arity := k) r v =>
      match k, r with
      | _, Sum.inl r => Semiformula.nrel r fun i => trmX (v i)
      | _, Sum.inr XRel.X => ⊤
  | _, .and φ ψ => eraseX φ ⋏ eraseX ψ
  | _, .or φ ψ => eraseX φ ⋎ eraseX ψ
  | _, .all φ => ∀¹ eraseX φ
  | _, .exs φ => ∃¹ eraseX φ

theorem val_trmX (P : M → Prop) (f : ℕ → M) {n : ℕ} (e : Fin n → M) (t : Semiterm LX ℕ n) :
    Semiterm.val (s := s) e f (trmX t) = Semiterm.val (s := lxStr P) e f t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func F v ih =>
      rcases F with F | F
      · show s.func (lxFunc (Sum.inl F))
            (fun i => Semiterm.val (s := s) e f (trmX (v i))) = _
        simp only [ih]
        rfl
      · exact F.elim

/-- **`eraseX` is truth-preserving when `X` is empty.** -/
theorem eval_eraseX (f : ℕ → M) {n : ℕ} (φ : Semiformula LX ℕ n) (e : Fin n → M) :
    Semiformula.Eval (s := s) e f (eraseX φ) ↔
      Semiformula.Eval (s := lxStr (fun _ => False)) e f φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact Iff.rfl
  | hfalsum => exact Iff.rfl
  | hrel r v =>
      rcases r with r | r
      · show s.rel r (fun i => Semiterm.val (s := s) e f (trmX (v i))) ↔
          s.rel r (fun i => Semiterm.val (s := lxStr _) e f (v i))
        rw [funext fun i => val_trmX (fun _ => False) f e (v i)]
      · cases r
        exact Iff.rfl
  | hnrel r v =>
      rcases r with r | r
      · show ¬s.rel r (fun i => Semiterm.val (s := s) e f (trmX (v i))) ↔
          ¬s.rel r (fun i => Semiterm.val (s := lxStr _) e f (v i))
        rw [funext fun i => val_trmX (fun _ => False) f e (v i)]
      · cases r
        show Semiformula.Eval (s := s) e f (⊤ : Semiformula ℒₒᵣ ℕ _) ↔ ¬ False
        simp
  | hand φ ψ ihφ ihψ =>
      show Semiformula.Eval (s := s) e f (eraseX φ ⋏ eraseX ψ) ↔ _
      rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and, ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
      show Semiformula.Eval (s := s) e f (eraseX φ ⋎ eraseX ψ) ↔ _
      rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or, ihφ, ihψ]
  | hall φ ih =>
      show Semiformula.Eval (s := s) e f (∀¹ eraseX φ) ↔ _
      rw [Semiformula.eval_all, Semiformula.eval_all]
      exact forall_congr' fun x => ih (x :> e)
  | hexs φ ih =>
      show Semiformula.Eval (s := s) e f (∃¹ eraseX φ) ↔ _
      rw [Semiformula.eval_ex, Semiformula.eval_ex]
      exact exists_congr fun x => ih (x :> e)

/-! ### The model expansion -/

theorem val_lMap_toLX (P : M → Prop) {n : ℕ} (e : Fin n → M) (f : ℕ → M)
    (t : Semiterm ℒₒᵣ ℕ n) :
    Semiterm.val (s := lxStr P) e f (Semiterm.lMap toLX t) = Semiterm.val (s := s) e f t := by
  rw [Semiterm.val_lMap, lxStr_lMap]

theorem lMap_zero_LX :
    Semiterm.lMap toLX ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 0) = ((0 : ℕ) : Semiterm LX ℕ 0) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.Zero.term_eq, toLX]

theorem lMap_succ_LX :
    Semiterm.lMap toLX (‘(#0 + 1)’ : Semiterm ℒₒᵣ ℕ 1) = (‘(#0 + 1)’ : Semiterm LX ℕ 1) := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.One.term_eq, Semiterm.Operator.Add.term_eq, toLX]
  apply funext
  rw [Fin.forall_fin_two]
  refine ⟨by simp [Function.comp_def], ?_⟩
  simp [Function.comp_def]
  exact Matrix.empty_eq _


theorem eval_succInd_iff {L : Language} [L.ORing] {N : Type} [Structure L N]
    (φ : Semiformula L ℕ 1) (f : ℕ → N) :
    Semiformula.Eval ![] f (succInd φ) ↔
      (Semiformula.Eval ![Semiterm.val ![] f ((0 : ℕ) : Semiterm L ℕ 0)] f φ →
        (∀ x, Semiformula.Eval ![x] f φ →
          Semiformula.Eval ![Semiterm.val ![x] f (‘(#0 + 1)’ : Semiterm L ℕ 1)] f φ) →
        ∀ x, Semiformula.Eval ![x] f φ) := by
  show Semiformula.Eval ![] f ((φ/[((0 : ℕ) : Semiterm L ℕ 0)]) 🡒
      (∀¹ (φ/[(#0 : Semiterm L ℕ 1)] 🡒 φ/[(‘(#0 + 1)’ : Semiterm L ℕ 1)])) 🡒
      ∀¹ (φ/[(#0 : Semiterm L ℕ 1)])) ↔ _
  simp only [LogicalConnective.HomClass.map_imply, Semiformula.eval_all, Semiformula.eval_substs]
  simp [Matrix.empty_eq]

/-- **Every model of `𝗣𝗔`, with `X` read as the empty predicate, is a model of `paLX`.** -/
theorem models_paLX_lxStrF [Nonempty M] [Structure.Eq ℒₒᵣ M] (hM : M↓[ℒₒᵣ] ⊧* 𝗣𝗔) :
    letI := lxStr (M := M) (fun _ => False); M↓[LX] ⊧* paLX := by
  let _ : Structure LX M := lxStr (fun _ => False)
  have _ : Structure.Eq LX M := lxStr_eq _
  refine Semantics.modelsSet_iff.mpr ?_
  rintro σ (hσ | hσ | hσ)
  · exact Theory.models M (𝗘𝗤 LX) hσ
  · obtain ⟨τ, hτ, rfl⟩ := hσ
    refine Semiformula.models_lMap.mpr ?_
    rw [lxStr_lMap]
    exact Semantics.modelsSet_iff.mp hM (Set.mem_union_left _ hτ)
  · obtain ⟨φ, -, rfl⟩ := hσ
    have hax : M↓[ℒₒᵣ] ⊧ Semiformula.univCl (succInd (eraseX φ)) :=
      Semantics.modelsSet_iff.mp hM
        (Set.mem_union_right _ (mem_InductionScheme_of_mem trivial))
    rw [models_iff_proposition] at hax ⊢
    intro g
    have hg := hax g
    simp only [Semiformula.Evalf] at hg ⊢
    rw [eval_succInd_iff] at hg ⊢
    simp only [eval_eraseX] at hg
    have h0 : Semiterm.val (s := s) ![] g ((0 : ℕ) : Semiterm ℒₒᵣ ℕ 0) =
        Semiterm.val (s := lxStr (M := M) (fun _ => False)) ![] g ((0 : ℕ) : Semiterm LX ℕ 0) := by
      rw [← lMap_zero_LX, val_lMap_toLX]
    have h1 : ∀ x : M, Semiterm.val (s := s) ![x] g (‘(#0 + 1)’ : Semiterm ℒₒᵣ ℕ 1) =
        Semiterm.val (s := lxStr (M := M) (fun _ => False)) ![x] g
          (‘(#0 + 1)’ : Semiterm LX ℕ 1) := by
      intro x
      rw [← lMap_succ_LX, val_lMap_toLX]
    simp only [h0, h1] at hg
    exact hg

/-- **Conservation.**  `PA[X]` proves no new `X`-free sentence. -/
theorem peano_of_paLX {σ : ArithmeticSentence} (h : paLX ⊢ Semiformula.lMap toLX σ) :
    𝗣𝗔 ⊢ σ := by
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro M _ sM _ hM
  let _ : Structure LX M := lxStr (fun _ => False)
  have _ : M↓[LX] ⊧* paLX := models_paLX_lxStrF hM
  have h2 : M↓[LX] ⊧ Semiformula.lMap toLX σ := consequence_iff'.mp (Theory.Proof.sound h) M
  have h3 := Semiformula.models_lMap.mp h2
  rwa [lxStr_lMap] at h3

end GoodsteinWu.Conservation
