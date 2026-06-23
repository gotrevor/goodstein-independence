/-
# `DescentSemantic.lean` — the E wall via first-order COMPLETENESS (lap-30 strategic redirect)

**The lap-30 finding.** The descent wall `Thm56.DescentE`
(`𝗣𝗔 ⊢ goodsteinSentence → Nonempty (Derivation2 paLX {TI prec})`) does **not** require hand-building a
`paLX` sequent-calculus derivation of `TI_≺(X)` (the literature-gated Route-B plan, see
`ON-LINE-REQUEST.md`). Foundation's **first-order completeness theorem** delivers the derivation from a
single *semantic* premise. `Derivation.completeness_of_encodable` (`Completeness/Completeness.lean`)
produces `(paLX : Schema LX) ⟹ [TI prec]` from:

> every model `M ⊧ paLX` satisfies `TI prec` (under every assignment).

So the **entire** E wall collapses to ONE semantic obligation, `paLX_models_TI_of_PA_provable`: *under
the hypothesis `𝗣𝗔 ⊢ goodsteinSentence`*, every model `M ⊧ paLX` satisfies `TI prec`. This is Rathjen
§3 carried out **inside the model `M`** — the free set predicate `X` is `M`'s own interpretation, and the
inequality-(6) induction is justified by `M ⊧ InductionScheme LX`. Three structural wins over the
sequent-calculus plan:

1. **Resolves the free-`X` obstruction** (lap-24 correction). The earlier `sigma1_pos_succ_induction`
   route worked in `V ⊧ 𝗜𝚺₁` (no `X`) and landed an X-free `𝗣𝗔 ⊢ PRWO`, which cannot refute the free-`X`
   `TI prec`. Here we work in models of `paLX`, where `X` is present throughout, and completeness does the
   syntactic lift for free.
2. **No literature gate.** No need to pin "the precise calculus-internal `Goodstein ⟹ paLX ⊢ TI_≺(X)`
   sequent shape" — the semantic argument is standard model theory.
3. **Reuses the lap-26 substrate.** The internal Goodstein arithmetic (`igoodstein`/`ibump`, bridged
   faithful to `Defs`) lives in `M`'s `ℒₒᵣ`-reduct; `DescentCore.ineq6_step` is the route-neutral kernel.

**Non-vacuity / anti-fraud.** `paLX_models_TI_of_PA_provable` is **conditionally** true (its conclusion
`M ⊧ TI prec` is exactly what fails in the Thm-5.6 countermodel; the hypothesis `𝗣𝗔 ⊢ goodsteinSentence`
is the real meta-premise we discharge — *not* assumed false). It genuinely needs Rathjen §3 to connect
"Goodstein terminates in `M`" with "`TI prec` holds in `M`". This file proves `Thm56.DescentE` **modulo
the disclosed `sorry`** in that lemma; it does **NOT** touch `Statement.lean`'s headline `sorry`, which
stays put until the semantic lemma is real and `#print axioms` is clean (`DIRECTION.md` anti-fraud rule).
-/
import GoodsteinPA.Thm56
import GoodsteinPA.DescentLift

namespace GoodsteinPA.DescentSemantic

open LO LO.FirstOrder
open GoodsteinPA GoodsteinPA.LangX GoodsteinPA.EmbeddingX

/-! ### `LX` is an encodable language

`completeness_of_encodable` needs `[LX.Encodable]`. `LX = Language.add ℒₒᵣ Xpred` has
`Func k = ℒₒᵣ.Func k ⊕ Empty` and `Rel k = ℒₒᵣ.Rel k ⊕ XRel k`; the only missing piece is
`Encodable (XRel k)` (`XRel` is the one-constructor `X : XRel 1`). -/

/-- `XRel k` is empty for `k ≠ 1` and the singleton `{X}` for `k = 1`; encode everything to `0`. -/
instance instEncodableXRel (k : ℕ) : Encodable (XRel k) where
  encode _ := 0
  decode n := match k, n with
    | 1, 0 => some XRel.X
    | _, _ => none
  encodek := by rintro ⟨⟩; rfl

instance instEncodableLXFunc (k : ℕ) : Encodable (LX.Func k) :=
  inferInstanceAs (Encodable (Language.Func ℒₒᵣ k ⊕ Empty))

instance instEncodableLXRel (k : ℕ) : Encodable (LX.Rel k) :=
  inferInstanceAs (Encodable (Language.Rel ℒₒᵣ k ⊕ XRel k))

noncomputable instance instEncodableLX : Language.Encodable LX :=
  ⟨fun _ => inferInstance, fun _ => inferInstance⟩

/-! ### The single semantic obligation (Rathjen §3, model-internal) -/

/-- **The E wall, reduced to one model-theoretic statement (DISCLOSED `sorry`).**

Under `𝗣𝗔 ⊢ goodsteinSentence`, *every* model `M ⊧ paLX` satisfies `TI prec`. Discharge plan
(Rathjen "Goodstein revisited" §3, carried out **inside `M`**):

1. **Import Goodstein into `M`.** From `h : 𝗣𝗔 ⊢ goodsteinSentence`, E-lift
   (`DescentLift.paLX_derivable2_lMap_of_PA_provable`) gives `paLX ⊢ lMap goodsteinSentence`; soundness
   then gives `M ⊧ lMap goodsteinSentence`, i.e. (via `Semiformula.eval_lMap`) the `ℒₒᵣ`-reduct of `M`
   models `goodsteinSentence` — every internal Goodstein run terminates in `M`.
2. **Suppose `M ⊭ TI prec`.** Then `M ⊧ Prog(X) ∧ ¬X a₀` for some `a₀ ∈ M`. By `M`'s LX least-number
   principle (an instance of `InductionScheme LX`, available since `M ⊧ paLX`), build the `X`-definable
   `≺`-descent `a₀ ≻ a₁ ≻ …` (`aₖ₊₁ =` `≺`-least `b ≺ aₖ` with `¬X b`, nonempty by `Prog`-contrapositive).
3. **Slow it down + run inequality (6).** Slow the descent (Rathjen 3.3/3.4/Thm 3.5) to `(βₖ)` with
   `C(βₖ) ≤ k+1`, run the special Goodstein sequence from `m₀ = T̂²(β₀)`. Inequality (6)
   (`DescentCore.ineq6_step`, iterated by `M`'s LX-induction over the X-definable predicate) gives
   `M ⊧ ∀k, mₖ ≥ T̂^{k+2}(βₖ) > 0` — the run never reaches `0` in `M`.
4. **Contradiction** with step 1 (`M ⊧ goodsteinSentence` says it does reach `0`). Hence `M ⊧ ∀a X a`,
   i.e. `M ⊧ TI prec`.

The free predicate `X` is present throughout (we are in a model of `paLX`, not `𝗜𝚺₁`), so the lap-24
free-`X` obstruction does not apply. The lap-26 internal-Goodstein substrate supplies the run; the
remaining genuine content is steps 2–3 carried out in `M`. -/
theorem paLX_models_TI_of_PA_provable (h : 𝗣𝗔 ⊢ ↑goodsteinSentence)
    {M : Type} [Nonempty M] [Structure LX M] (hM : M ⊧ₘ* (paLX : Theory LX)) (f : ℕ → M) :
    Semiformula.Evalfm M f (Boundedness.TI Thm56.prec) := by
  sorry

/-! ### `DescentE` via first-order completeness -/

/-- **`Thm56.DescentE`, proved via completeness (modulo the disclosed semantic `sorry`).** From
`𝗣𝗔 ⊢ goodsteinSentence`, `completeness_of_encodable` turns the single semantic premise
`paLX_models_TI_of_PA_provable` into the derivation `paLX ⟹ [TI prec]`, then `toDerivation2` packages it
as the `Derivation2 paLX {TI prec}` that `DescentE` requires. -/
theorem descentE : Thm56.DescentE := by
  intro h
  have d : (paLX : Theory LX).toSchema ⟹ ([Boundedness.TI Thm56.prec] : List (SyntacticFormula LX)) :=
    Derivation.completeness_of_encodable
      (fun M _ _ hM => ⟨_, by simp, fun f => paLX_models_TI_of_PA_provable h hM f⟩)
  exact ⟨by simpa using Derivation.toDerivation2 _ d⟩

/-- **The headline, modulo the one disclosed semantic `sorry`.** Combining `descentE` with the proved
reduction `Thm56.peano_not_proves_goodstein_of_descent` yields `𝗣𝗔 ⊬ goodsteinSentence`. This carries a
`sorryAx` (from `paLX_models_TI_of_PA_provable`) and is therefore **NOT** wired into `Statement.lean`'s
headline (anti-fraud). It exists so `#print axioms` audits the *full* chain: the only non-trust-base
axioms must be `sorryAx` + the F-φ `native_decide` artifact — no `PA_delta1Definable`, no custom axiom. -/
theorem peano_not_proves_goodstein_modulo_semantic : 𝗣𝗔 ⊬ ↑goodsteinSentence :=
  Thm56.peano_not_proves_goodstein_of_descent descentE

end GoodsteinPA.DescentSemantic
