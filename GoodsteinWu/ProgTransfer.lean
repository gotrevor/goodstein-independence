/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinWu.Progressive
import OrdinalAnalysis.Gentzen.UpperBound

/-!
# Transporting progressiveness into `PA[X]`

`GoodsteinWu.Progressive.fgTotal_progressive` is a statement about models of `𝗜𝚺₁`.  Here it
becomes a *proof*, first of the arithmetic sentence `arithProgStatement` in `𝗜𝚺₁`, then — via
Wu's `paLX_of_peano_semantic` — of `progStatement`, the `PA[X]` sentence `Prog(≺, ψ)` with
`ψ := fgTotalCode` the `X`-free formula `isNF c → ∀ n, ∃ y, f_c(n) = y`.

That is precisely the hypothesis of `closedTI`, so it is what `gentzen_upper_bound` consumes.

The `simp` discipline here follows Wu (`InternalEpsMonoCode`): never let `simp` unfold the
concrete coded formulas (`precDef`, `fgGraphDef`), or it runs away in memory.  All the
evaluation work is done by the two small lemmas `eval_arithPrecAt` / `eval_arithFgAt`.
-/

open scoped FFL.FirstOrder.Bounding
open FFL.FirstOrder.Tarski

set_option autoImplicit false

namespace GoodsteinWu.ProgTransfer


open Classical
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding.HierarchySymbol
  OrdinalAnalysis.Compat OrdinalAnalysis.Compat.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen OrdinalAnalysis.Gentzen.CodedNotation
open OrdinalAnalysis.Gentzen.InternalONote GoodsteinWu.InternalFund
  GoodsteinWu.FastGrowingGraph GoodsteinWu.Progressive

/-- `ψ(c)`: `isNF c → ∀ n, ∃ y, f_c(n) = y`. -/
def fgTotalDef : ArithmeticSemisentence 1 :=
  “c. !nfDef c → ∀ n, ∃ y, !fgGraphDef c n y”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem eval_fgTotalDef (c : V) : fgTotalDef.Evalb ![c] ↔ fgTotal c := by
  simp [fgTotalDef, fgTotal, fgGraph_defined.iff]


noncomputable def fgTotalCode : Semiformula LX ℕ 1 := liftCode fgTotalDef

/-- The arithmetic side of `precCode`. -/
noncomputable def arithPrec : ArithmeticSemiformula ℕ 2 := Rewriting.emb precDef.val

noncomputable def arithFg : ArithmeticSemiformula ℕ 1 := Rewriting.emb fgTotalDef

noncomputable def arithFgAt {n : ℕ} (x : ArithmeticSemiterm ℕ n) :
    ArithmeticSemiformula ℕ n := Rew.subst ![x] ▹ arithFg

noncomputable def arithPrecAt {n : ℕ} (y x : ArithmeticSemiterm ℕ n) :
    ArithmeticSemiformula ℕ n := Rew.subst ![y, x] ▹ arithPrec

noncomputable def arithProgStatement : ArithmeticSentence :=
  (∀¹ (∼(∀¹ (∼(arithPrecAt (#0 : ArithmeticSemiterm ℕ 2) #1) ⋎ arithFgAt #0)) ⋎
    arithFgAt #0)).univCl

private lemma map_prog_body :
    Semiformula.lMap toLX
      (∀¹ (∼(∀¹ (∼(arithPrecAt (#0 : ArithmeticSemiterm ℕ 2) #1) ⋎ arithFgAt #0)) ⋎
        arithFgAt #0)) =
      progAt precCode fgTotalCode := by
  simp only [arithPrecAt, arithFgAt, arithPrec, arithFg, progAt, belowAt, formulaAt, precAt,
    precCode, fgTotalCode, liftCode, Semiformula.lMap_all, Semiformula.lMap_exs,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    LogicalConnective.HomClass.map_and, Semiformula.lMap_subst]
  have h₁ : (Semiterm.lMap toLX ∘ ![(#0 : Semiterm ℒₒᵣ ℕ 2), (#1 : Semiterm ℒₒᵣ ℕ 2)]) =
      ![(#0 : Semiterm LX ℕ 2), Rew.bShift (#0 : Semiterm LX ℕ 1)] := by
    funext x; match x with | 0 => rfl | 1 => rfl
  have h₂ : (Semiterm.lMap toLX ∘ ![(#0 : Semiterm ℒₒᵣ ℕ 2)]) =
      ![(#0 : Semiterm LX ℕ 2)] := by
    funext x; match x with | 0 => rfl
  have h₃ : (Semiterm.lMap toLX ∘ ![(#0 : Semiterm ℒₒᵣ ℕ 1)]) =
      ![(#0 : Semiterm LX ℕ 1)] := by
    funext x; match x with | 0 => rfl
  rw [h₁, h₂, h₃]

noncomputable def arithBelowAt {n : ℕ} (b : ArithmeticSemiterm ℕ n) :
    ArithmeticSemiformula ℕ n :=
  ∀¹ (∼(arithPrecAt (#0 : ArithmeticSemiterm ℕ (n+1)) (Rew.bShift b)) ⋎ arithFgAt #0)

noncomputable def arithProg : ArithmeticSemiformula ℕ 0 :=
  ∀¹ (∼(arithBelowAt (#0 : ArithmeticSemiterm ℕ 1)) ⋎ arithFgAt #0)

lemma eval_arithPrecAt {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {n : ℕ} (b : Fin n → M) (f : ℕ → M) (y x : ArithmeticSemiterm ℕ n) :
    Semiformula.Eval b f (arithPrecAt y x) ↔
      isNF (y.val b f) ∧ isNF (x.val b f) ∧ icmp (y.val b f) (x.val b f) = 0 := by
  simp only [arithPrecAt, arithPrec, Semiformula.eval_substs, Semiformula.eval_emb]
  rw [show (Semiterm.val b f ∘ ![y, x]) = ![y.val b f, x.val b f] by
    funext i; match i with | 0 => rfl | 1 => rfl]
  exact eval_precDef _ _

lemma eval_arithFgAt {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {n : ℕ} (b : Fin n → M) (f : ℕ → M) (x : ArithmeticSemiterm ℕ n) :
    Semiformula.Eval b f (arithFgAt x) ↔ fgTotal (x.val b f) := by
  simp only [arithFgAt, arithFg, Semiformula.eval_substs, Semiformula.eval_emb]
  rw [show (Semiterm.val b f ∘ ![x]) = ![x.val b f] by funext i; match i with | 0 => rfl]
  exact eval_fgTotalDef _

theorem arithmetic_prog : 𝗜𝚺₁ ⊢ arithProgStatement := by
  apply FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  rw [models_iff]
  simp only [arithProgStatement, Semiformula.eval_univCl, Semiformula.eval_all,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    eval_arithPrecAt, eval_arithFgAt, Semiterm.val_bvar,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  intro f c
  by_cases hb : ∀ d : M, isNF d → isNF c → icmp d c = 0 → fgTotal d
  · exact Or.inr (fgTotal_progressive c hb)
  · refine Or.inl fun hall => hb fun d h1 h2 h3 => ?_
    rcases hall d with h | h
    · exact absurd ⟨h1, h2, h3⟩ h
    · exact h


/-- `Prog(≺, ψ)` as a `PA[X]` sentence. -/
noncomputable def progStatement : Sentence LX := (progAt precCode fgTotalCode).univCl

theorem models_prog_iff_arithmetic {M : Type*} [Nonempty M] [sLX : Structure LX M] :
    M↓[LX] ⊧ progStatement ↔ (sLX.lMap toLX).toStruc ⊧ arithProgStatement := by
  letI : Structure ℒₒᵣ M := sLX.lMap toLX
  rw [models_iff, models_iff]
  simp only [progStatement, arithProgStatement, Semiformula.eval_univCl]
  rw [← map_prog_body]
  simp only [Semiformula.eval_lMap]

/-- **Totality of the fast-growing hierarchy is progressive, provably in `PA[X]`.** -/
theorem concrete_prog : paLX ⊢ progStatement :=
  paLX_of_peano_semantic (Entailment.WeakerThan.pbl arithmetic_prog)
    (fun _ _ _ => models_prog_iff_arithmetic)

end GoodsteinWu.ProgTransfer
