/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinWu.ProgTransfer
import GoodsteinWu.Conservation

/-!
# Feeding progressiveness to the Gentzen upper bound

Step 5 of the route.  `concrete_prog` gives `paLX ⊢ Prog(≺, ψ)`, and Wu's
`concrete_nonote_ti` gives `paLX ⊢ TI(ψ, ⌜b⌝)` for every notation `b`.  Picking `b` above `a`
(`exists_lt_nonoteTower`) and discharging the comparison with `concrete_nonote_prec` yields
`paLX ⊢ ψ(⌜a⌝)`, and conservation (`peano_of_paLX_semantic`) brings it back to `𝗣𝗔`:

    `peano_fg (a : NONote) : 𝗣𝗔 ⊢ arithFgClosed a`

i.e. `𝗣𝗔` proves `isNF ⌜a⌝ → ∀ n, ∃ y, fgGraph ⌜a⌝ n y` — the totality of `f_a`, up to the ℕ
read-off of `fgGraph`, which is step 6.
-/

open scoped FFL.FirstOrder.Bounding
open FFL.FirstOrder.Tarski

set_option autoImplicit false

namespace GoodsteinWu.ApplyTI


open Classical
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen OrdinalAnalysis.Gentzen.CodedNotation
open OrdinalAnalysis.Gentzen.UpperBound OrdinalAnalysis.Gentzen.Cofinality
open OrdinalAnalysis.Gentzen.NotationBridge
open OrdinalAnalysis.Gentzen.Order
open GoodsteinWu.ProgTransfer
open OrdinalAnalysis.Gentzen.OmegaTower (lMap_numeral)

variable {M : Type*} [Structure LX M]

lemma eval_precAt' {n : ℕ} (e : Fin n → M) (f : ℕ → M) (prec : Semiformula LX ℕ 2)
    (y x : Semiterm LX ℕ n) :
    Semiformula.Eval e f (precAt prec y x) ↔
      Semiformula.Eval ![y.val e f, x.val e f] f prec := by
  simp only [precAt, Semiformula.eval_substs]
  rw [show (Semiterm.val e f ∘ ![y, x]) = ![y.val e f, x.val e f] by
    funext i; match i with | 0 => rfl | 1 => rfl]

lemma eval_formulaAt' {n : ℕ} (e : Fin n → M) (f : ℕ → M) (φ : Semiformula LX ℕ 1)
    (x : Semiterm LX ℕ n) :
    Semiformula.Eval e f (formulaAt φ x) ↔ Semiformula.Eval ![x.val e f] f φ := by
  simp only [formulaAt, Semiformula.eval_substs]
  rw [show (Semiterm.val e f ∘ ![x]) = ![x.val e f] by funext i; match i with | 0 => rfl]

/-- `PA[X]` proves `ψ` at every standard notation code. -/
theorem concrete_fg (a : NONote) :
    paLX ⊢ (formulaAt fgTotalCode (notationTerm a)).univCl := by
  obtain ⟨n, han⟩ := exists_lt_nonoteTower a
  apply Theory.Proof.complete.{0, 0}
  rw [consequence_iff_eq']
  intro N _ sLX _ hM
  letI : N↓[LX] ⊧* paLX := hM
  have hTI : N↓[LX] ⊧ closedTI fgTotalCode (notationTerm (nonoteTower n)) :=
    consequence_iff_eq'.mp
      (Theory.Proof.sound (concrete_nonote_ti fgTotalCode (nonoteTower n))) N
  have hProg : N↓[LX] ⊧ progStatement :=
    consequence_iff_eq'.mp (Theory.Proof.sound concrete_prog) N
  have hPrec : N↓[LX] ⊧ closedPrec (notationTerm a) (notationTerm (nonoteTower n)) :=
    consequence_iff_eq'.mp (Theory.Proof.sound (concrete_nonote_prec han)) N
  rw [models_iff] at hTI hProg hPrec ⊢
  simp only [closedTI, tiUptoAt, progStatement, closedPrec, Semiformula.eval_univCl,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg] at hTI hProg hPrec ⊢
  intro f
  rcases hTI f with h | h
  · exact absurd (hProg f) h
  · rw [belowAt, Semiformula.eval_all] at h
    have hx := h ((notationTerm a).val ![] f)
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg] at hx
    rcases hx with hn | hy
    · refine absurd ?_ hn
      refine (eval_precAt' _ f precCode (#0 : Semiterm LX ℕ 1)
        (Rew.bShift (notationTerm (nonoteTower n)))).mpr ?_
      have hp := (eval_precAt' ![] f precCode (notationTerm a)
        (notationTerm (nonoteTower n))).mp (hPrec f)
      simpa using hp
    · refine (eval_formulaAt' ![] f fgTotalCode (notationTerm a)).mpr ?_
      have hq := (eval_formulaAt' _ f fgTotalCode (#0 : Semiterm LX ℕ 1)).mp hy
      simpa using hq

/-- The arithmetic sentence `ψ(⌜a⌝)`. -/
noncomputable def arithFgClosed (a : NONote) : ArithmeticSentence :=
  (arithFgAt ((nonoteCode a : ℕ) : ArithmeticSemiterm ℕ 0)).univCl

private lemma map_fg_body (a : NONote) :
    Semiformula.lMap toLX (arithFgAt ((nonoteCode a : ℕ) : ArithmeticSemiterm ℕ 0)) =
      formulaAt fgTotalCode (notationTerm a) := by
  simp only [arithFgAt, arithFg, formulaAt, fgTotalCode, liftCode, notationTerm,
    Semiformula.lMap_subst]
  rw [show (Semiterm.lMap toLX ∘ ![((nonoteCode a : ℕ) : ArithmeticSemiterm ℕ 0)]) =
      ![((nonoteCode a : ℕ) : Semiterm LX ℕ 0)] by
    funext i; match i with | 0 => exact lMap_numeral (nonoteCode a)]

/-- **`PA` proves `ψ(⌜a⌝)`** — the totality of `f_a` — for every normal notation `a`. -/
theorem peano_fg (a : NONote) : 𝗣𝗔 ⊢ arithFgClosed a := by
  apply Conservation.peano_of_paLX_semantic (concrete_fg a)
  intro N _ sLX h
  letI : Structure ℒₒᵣ N := sLX.lMap toLX
  rw [models_iff] at h ⊢
  simp only [arithFgClosed, Semiformula.eval_univCl] at h ⊢
  intro f
  have hf := h f
  rw [← map_fg_body] at hf
  exact Semiformula.eval_lMap.mp hf


end GoodsteinWu.ApplyTI
