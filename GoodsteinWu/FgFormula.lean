/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinWu.ApplyTI
import GoodsteinWu.Readoff

/-!
# The Σ₁ graph of `fastGrowing o` as a two-place arithmetic formula

The last piece of the route.  `fgFormula o` is `fgGraphDef` with the code of `o` plugged into its
first argument and the remaining two arguments put in the frozen statement's order `(y, n)`.
Being the `.val` of a `𝚺₁.Semisentence`, it is `𝚺₁` by construction.

Three facts are assembled here:

* `hierarchy_fgFormula` — `fgFormula o` is `𝚺₁`;
* `peano_fgFormula` — `𝗣𝗔 ⊢ ∀ n, ∃ y, fgFormula o`, from `ApplyTI.peano_fg` with the `isNF ⌜o⌝`
  guard discharged by `NotationBridge.isNF_modelCode`;
* `fgGraph_total` — the standard-model instance of the previous item, which together with
  `Readoff.fgGraph_sound` gives the frozen `↔` in both directions.  Note that no witness set is
  ever built by hand at `ℕ`: the `←` direction is the `ℕ`-instance of the `𝗣𝗔`-proof.
-/

open scoped FFL.FirstOrder.Bounding
open FFL.FirstOrder.Tarski

set_option autoImplicit false

namespace GoodsteinWu.FgFormula

open Classical
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding.HierarchySymbol
  OrdinalAnalysis.Compat OrdinalAnalysis.Compat.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalONote OrdinalAnalysis.Gentzen.NotationBridge
open GoodsteinWu.InternalFund GoodsteinWu.FastGrowingGraph GoodsteinWu.ProgTransfer

/-- `fgGraphDef` with `⌜code o⌝` substituted for the code argument and the value/index arguments
reordered to `(y, n)`. -/
noncomputable def fgSem (o : ONote) : 𝚺₁.Semisentence 2 :=
  fgGraphDef.rew (Rew.subst ![((code o : ℕ) : Semiterm ℒₒᵣ Empty 2), #1, #0])

/-- The Σ₁ graph of `fastGrowing o`, as a plain two-place arithmetic formula. -/
noncomputable def fgFormula (o : ONote) : Semisentence ℒₒᵣ 2 := (fgSem o).val

lemma hierarchy_fgFormula (o : ONote) :
    Bounding.Hierarchy ℬ[<, ℒₒᵣ] 𝚺 1 (fgFormula o) := (fgSem o).sigma_prop

lemma eval_fgFormula {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (o : ONote) (y n : V) :
    V ⊧/![y, n] (fgFormula o) ↔ fgGraph (modelCode (V := V) o) n y := by
  simp only [fgFormula, fgSem, Bounding.HierarchySymbol.Semiformula.val_rew,
    Semiformula.eval_substs]
  rw [show (Semiterm.val (L := ℒₒᵣ) ![y, n] (Empty.elim : Empty → V) ∘
      ![((code o : ℕ) : Semiterm ℒₒᵣ Empty 2), #1, #0]) =
      ![modelCode (V := V) o, n, y] from ?_]
  · exact fgGraph_defined.iff
  · funext i
    match i with
    | 0 => simp [modelCode]
    | 1 => rfl
    | 2 => rfl

/-! ### From `peano_fg` to the frozen shape -/

/-- The totality half of `ApplyTI.peano_fg`, with the `isNF ⌜o⌝` guard discharged: in every model
of `𝗣𝗔`, every `n` has a value. -/
theorem exists_fgGraph {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (o : ONote) (ho : o.NF) (n : M) : ∃ y, fgGraph (modelCode (V := M) o) n y := by
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (T := 𝗜𝚺₁) (U := 𝗣𝗔) inferInstance
  have hsat : M↓[ℒₒᵣ] ⊧ ApplyTI.arithFgClosed ⟨o, ho⟩ :=
    consequence_iff'.mp (Theory.Proof.sound (ApplyTI.peano_fg ⟨o, ho⟩)) M
  rw [models_iff] at hsat
  simp only [ApplyTI.arithFgClosed, Semiformula.eval_univCl] at hsat
  have h := (eval_arithFgAt (M := M) ![] (fun _ => (0 : M))
    ((nonoteCode ⟨o, ho⟩ : ℕ) : ArithmeticSemiterm ℕ 0)).mp (hsat (fun _ => (0 : M)))
  have hcode : Semiterm.val (L := ℒₒᵣ) ![] (fun _ => (0 : M))
      ((nonoteCode ⟨o, ho⟩ : ℕ) : ArithmeticSemiterm ℕ 0) = modelCode (V := M) o := by
    simp [nonoteCode, modelCode]
  rw [hcode] at h
  exact h (isNF_modelCode o ho) n

/-- **`𝗣𝗔` proves `∀ n, ∃ y, fgFormula o`.** -/
theorem peano_fgFormula (o : ONote) (ho : o.NF) :
    𝗣𝗔 ⊢ (∀¹ ∃¹ fgFormula o : Sentence ℒₒᵣ) := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗣𝗔 _
  intro M _ _
  rw [models_iff]
  simp only [Semiformula.eval_all, Semiformula.eval_ex]
  intro n
  obtain ⟨y, hy⟩ := exists_fgGraph (M := M) o ho n
  exact ⟨y, (eval_fgFormula (V := M) o y n).mpr hy⟩

/-- **`fgGraph` is total at the standard model, with the right value.**  The witness set is not
built here: it comes from the `𝗣𝗔`-proof read at `ℕ`, and `Readoff.fgGraph_sound` identifies its
value with `fastGrowing o n`. -/
theorem fgGraph_total (o : ONote) (ho : o.NF) (n : ℕ) :
    fgGraph (V := ℕ) (code o) n (ONote.fastGrowing o n) := by
  obtain ⟨y, hy⟩ := exists_fgGraph (M := ℕ) o ho n
  have hy' : fgGraph (V := ℕ) (code o) n y := by simpa [modelCode] using hy
  have hval : y = ONote.fastGrowing o n := Readoff.fgGraph_sound hy'
  rw [← hval]
  exact hy'

/-- The frozen `↔`, both directions. -/
theorem eval_fgFormula_nat (o : ONote) (ho : o.NF) (n y : ℕ) :
    ℕ ⊧/![y, n] (fgFormula o) ↔ y = ONote.fastGrowing o n := by
  rw [eval_fgFormula (V := ℕ)]
  constructor
  · intro h; exact Readoff.fgGraph_sound (by simpa [modelCode] using h)
  · intro h; subst h; simpa [modelCode] using fgGraph_total o ho n

end GoodsteinWu.FgFormula
