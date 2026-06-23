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
import GoodsteinPA.ReductModel
import GoodsteinPA.DescentInternal

namespace GoodsteinPA.DescentSemantic

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
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

/-! ### Step 1 (PROVED): import Goodstein into the model

The easy front of the semantic obligation: under `𝗣𝗔 ⊢ goodsteinSentence`, the lifted Goodstein sentence
holds in every model `M ⊧ paLX`. Pure proof-translation + soundness, no Rathjen content. -/

open GoodsteinPA.DescentLift in
/-- **`M` models the lifted Goodstein sentence.** From `𝗣𝗔 ⊢ goodsteinSentence`, E-lift
(`paLX_derivable2_lMap_of_PA_provable`) gives `paLX ⊢ lMap Φ goodsteinSentence` (as an `LX`-sentence, via
`provable_def` + `Semiformula.lMap_emb`); soundness (`models_of_provable`) then transports it into any
model `M ⊧ paLX`. -/
theorem models_lMap_goodstein (h : 𝗣𝗔 ⊢ ↑goodsteinSentence)
    {M : Type} [Nonempty M] [Structure LX M] (hM : M ⊧ₘ* (paLX : Theory LX)) :
    M ⊧ₘ (Semiformula.lMap Φ goodsteinSentence : Sentence LX) := by
  obtain ⟨d⟩ := paLX_derivable2_lMap_of_PA_provable goodsteinSentence h
  refine models_of_provable hM ?_
  rw [provable_def, show (↑(Semiformula.lMap Φ goodsteinSentence) : SyntacticFormula LX)
        = Semiformula.lMap Φ (↑goodsteinSentence : SyntacticFormula ℒₒᵣ) from
      (Semiformula.lMap_emb goodsteinSentence).symm]
  exact provable_iff_derivable2.mpr ⟨d⟩

open GoodsteinPA.DescentLift in
/-- **The `ℒₒᵣ`-reduct of `M` models `goodsteinSentence`** (the directly-usable arithmetic form of
`models_lMap_goodstein`, via `Semiformula.models_lMap`): every internal Goodstein run terminates in `M`. -/
theorem reduct_models_goodstein (h : 𝗣𝗔 ⊢ ↑goodsteinSentence)
    {M : Type} [Nonempty M] [inst : Structure LX M] (hM : M ⊧ₘ* (paLX : Theory LX)) :
    (inst.lMap Φ).toStruc ⊧ goodsteinSentence :=
  Semiformula.models_lMap.mp (models_lMap_goodstein h hM)

/-! ### Step 2 (PROVED): unfold `TI prec` semantics in `M` to abstract transfinite induction

`Evalfm M f (TI prec)` is exactly transfinite induction for the pair `(Mlt f, MX)` — `Mlt` is `M`'s
interpretation of the X-free order `prec` (= `≺`), `MX` is `M`'s interpretation of the set variable `X`.
This strips the Foundation-DSL wrapper, leaving a transparent goal the Rathjen §3 argument acts on. -/

/-- `M`'s interpretation of the set variable `X` (the `Xsym` relation). -/
def MX {M : Type} [Structure LX M] (a : M) : Prop := Structure.rel (L := LX) Xsym ![a]

/-- `M`'s interpretation of the order `≺` (`= Thm56.prec`, X-free), at assignment `f`: `Mlt f y x` reads
`prec` with `#0 ↦ y`, `#1 ↦ x`. -/
def Mlt {M : Type} [Structure LX M] (f : ℕ → M) (y x : M) : Prop :=
  Semiformula.Eval (L := LX) ‹_› ![y, x] f Thm56.prec

/-- **`TI prec` in `M` = abstract transfinite induction for `(Mlt, MX)`.** `Evalfm M f (TI prec)` holds
iff: progressivity of `MX` along `Mlt` implies `MX` is total. Pure unfolding (`map_imply`/`eval_all`/
`eval_rel₁`). -/
theorem evalfm_TI_unfold {M : Type} [Nonempty M] [Structure LX M] (f : ℕ → M) :
    Semiformula.Evalfm M f (Boundedness.TI Thm56.prec)
      ↔ ((∀ x : M, (∀ y : M, Mlt f y x → MX y) → MX x) → ∀ x : M, MX x) := by
  unfold MX Mlt
  simp only [Boundedness.TI, Boundedness.Prog, Boundedness.hyp, Boundedness.Xat,
    LogicalConnective.HomClass.map_imply, Semiformula.eval_all, Semiformula.eval_rel₁,
    Semiterm.val_bvar, Matrix.cons_val_zero]
  rfl

/-! ### Tool for wall D — `LX`-induction inside a model of `paLX`

The descent bound `b k = T̂^{k+2}(βₖ)` is `X`-definable (`βₖ` is extracted from the `X`-descent), so the
non-termination induction (wall D) runs over an `LX`-formula, **not** an `ℒₒᵣ`-`𝚺₁` one — Foundation's
`Arithmetic.InductionScheme.succ_induction` (ℒₒᵣ-only) does not reach it. These two lemmas supply the
`X`-essential induction from `M ⊧ paLX ⊇ InductionScheme LX Set.univ`. Axiom-clean. -/

/-- `paLX = (lMap Φ 𝗣𝗔⁻ + InductionScheme LX univ) + {relExt Xsym}` (lap-32 3-summand), so a model of
`paLX` models `InductionScheme LX Set.univ`. -/
theorem models_inductionScheme_LX {M : Type} [Nonempty M] [Structure LX M]
    (hM : M ⊧ₘ* (paLX : Theory LX)) :
    M ⊧ₘ* (Arithmetic.InductionScheme LX Set.univ : Theory LX) :=
  ModelsTheory.of_ss hM (fun _ hψ => Or.inl (Or.inr hψ))

/-- **`LX`-succ-induction in a model of `paLX`** (the `X`-essential analog of
`Arithmetic.InductionScheme.succ_induction`, which is `ℒₒᵣ`-only). Any predicate `P` on `M` definable by
an `LX`-formula (`hP`) admits ordinary `0`/`+1` induction over `M`'s ring operations read off its
`LX`-reduct (`ReductModel.reductORing`). This is the induction wall D's `X`-definable descent bound runs
on. Proof: `M ⊧ InductionScheme LX univ` gives `M ⊧ univCl (succInd φ)`; unfold to `0`/`+1` induction over
`LX`-eval, matching `reductORing`'s ops via the `Structure.Zero/One/Add LX M` read-offs. -/
theorem lx_succ_induction {M : Type} [Nonempty M] [Structure LX M] [Structure.Eq LX M]
    (hM : M ⊧ₘ* (paLX : Theory LX)) {P : M → Prop}
    (hP : ∃ e : ℕ → M, ∃ φ : Semiformula LX ℕ 1, ∀ x, P x ↔ Semiformula.Evalm M ![x] e φ) :
    letI : ORingStructure M := ReductModel.reductORing
    P 0 → (∀ x, P x → P (x + 1)) → ∀ x, P x := by
  letI oM : ORingStructure M := ReductModel.reductORing
  haveI hSZ : Structure.Zero LX M :=
    ⟨by simp [Semiterm.Operator.val, Semiterm.Operator.Zero.term_eq]; rfl⟩
  haveI hSO : Structure.One LX M :=
    ⟨by simp [Semiterm.Operator.val, Semiterm.Operator.One.term_eq]; rfl⟩
  haveI hSA : Structure.Add LX M :=
    ⟨fun a b => by simp [Semiterm.Operator.val, Semiterm.Operator.Add.term_eq, Semiterm.val_func,
        Matrix.fun_eq_vec_two]; rfl⟩
  haveI hind : M ⊧ₘ* (Arithmetic.InductionScheme LX Set.univ : Theory LX) := models_inductionScheme_LX hM
  rcases hP with ⟨e, φ, hPφ⟩
  intro hzero hsucc
  have hsucc' : M ⊧ₘ (.univCl (Arithmetic.succInd φ) : Sentence LX) :=
    ModelsTheory.models (T := Arithmetic.InductionScheme LX Set.univ) M ⟨φ, trivial, rfl⟩
  have key : ∀ x, Semiformula.Evalm M ![x] e φ := by
    have h := hsucc'
    simp only [models_iff, Semiformula.eval_univCl, Arithmetic.succInd,
      LogicalConnective.HomClass.map_imply, Semiformula.eval_all, Semiformula.eval_substs,
      Matrix.constant_eq_singleton, Semiterm.val_operator₂, Semiterm.val_bvar,
      Matrix.cons_val_fin_one, Semiterm.val_operator₀, Structure.numeral_eq_numeral,
      ORingStructure.one_eq_one, Structure.Add.add, Function.const_apply, Matrix.cons_val_zero] at h
    refine h e ?_ ?_
    · exact (hPφ 0).mp hzero
    · intro x hx
      exact (hPφ (x + 1)).mp (hsucc x ((hPφ x).mpr hx))
  intro x
  exact (hPφ x).mpr (key x)

/-! ### Tools for wall C — `LX` order-induction and the least-number principle inside a model of `paLX`

Wall C builds the `Mlt`-descent from `no_min` as an `M`-internal/definable object. The recursion makes
canonical choices via `M`'s least-number principle over its *arithmetic* order `<` (the `reductORing`
read-off), applied to an `LX`-definable predicate. Foundation's `Arithmetic.leastNumber`/`orderInd` are
the `ℒₒᵣ`-only analogs; these port them to `LX`, deriving them (exactly as Foundation does) from the
succ-induction `lx_succ_induction` already in hand. Axiom-clean. -/

/-- The bounded-quantifier predicate `fun x ↦ ∀ y < x, P y` is `LX`-definable whenever `P` is: from an
`LX`-formula `φ` for `P`, `(φ ⇜ ![#0]).ballLT #0` defines it (over `M`'s arithmetic `<`, the
`reductORing` read-off). The lone closure step the order-induction needs. -/
theorem lxDef_ballLT {M : Type} [Nonempty M] [Structure LX M] {P : M → Prop}
    (hP : ∃ e : ℕ → M, ∃ φ : Semiformula LX ℕ 1, ∀ x, P x ↔ Semiformula.Evalm M ![x] e φ) :
    letI : ORingStructure M := ReductModel.reductORing
    ∃ e : ℕ → M, ∃ φ : Semiformula LX ℕ 1,
      ∀ x : M, (∀ y : M, y < x → P y) ↔ Semiformula.Evalm M ![x] e φ := by
  letI oM : ORingStructure M := ReductModel.reductORing
  haveI hSLT : Structure.LT LX M := ⟨fun a b => by
    simp only [Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq, Semiformula.eval_rel₂]
    rfl⟩
  rcases hP with ⟨e, φ, hφ⟩
  refine ⟨e, (φ ⇜ ![(#0 : Semiterm LX ℕ 2)]).ballLT (#0 : Semiterm LX ℕ 1), fun x => ?_⟩
  simp only [Semiformula.eval_ballLT, Semiterm.val_bvar, Matrix.cons_val_zero,
    Semiformula.eval_substs, Matrix.cons_val_fin_one, Matrix.constant_eq_singleton]
  exact forall_congr' fun y => imp_congr_right fun _ => hφ y

/-- **`LX` order-induction in a model of `paLX`** (the `X`-essential analog of
`Arithmetic.InductionOnHierarchy.order_induction`, which is `ℒₒᵣ`-only). For any `LX`-definable `P`,
`∀-below` progressivity yields totality. Derived from `lx_succ_induction` via the
`fun x ↦ ∀ y < x, P y` reduction (`lxDef_ballLT`), exactly as Foundation derives the `ℒₒᵣ` version. -/
theorem lx_order_induction {M : Type} [Nonempty M] [Structure LX M] [Structure.Eq LX M]
    (hM : M ⊧ₘ* (paLX : Theory LX)) {P : M → Prop}
    (hP : ∃ e : ℕ → M, ∃ φ : Semiformula LX ℕ 1, ∀ x, P x ↔ Semiformula.Evalm M ![x] e φ) :
    letI : ORingStructure M := ReductModel.reductORing
    (∀ x, (∀ y, y < x → P y) → P x) → ∀ x, P x := by
  letI oM : ORingStructure M := ReductModel.reductORing
  haveI hPA : M ⊧ₘ* (𝗣𝗔⁻ : Theory ℒₒᵣ) := models_of_subtheory (ReductModel.reduct_models_PA hM)
  intro ind
  suffices h : ∀ x : M, ∀ y : M, y < x → P y by
    intro x; exact h (x + 1) x (lt_add_one x)
  intro x
  refine lx_succ_induction hM (lxDef_ballLT hP) ?_ ?_ x
  · intro y hy; exact absurd hy (not_lt.mpr (by simp))
  · intro w IH y hy
    rcases (lt_succ_iff_le.mp hy).lt_or_eq with hlt | rfl
    · exact IH y hlt
    · exact ind y IH

/-- **`LX` least-number principle in a model of `paLX`** (the `X`-essential analog of
`Arithmetic.leastNumber`). Any nonempty `LX`-definable `P` has a `<`-least witness (`<` = `M`'s
arithmetic order, the `reductORing` read-off). This is the choice-free, `M`-internal selector wall C's
descent recursion uses to pick the canonical `Mlt`-smaller non-`MX` element. -/
theorem lx_least_number {M : Type} [Nonempty M] [Structure LX M] [Structure.Eq LX M]
    (hM : M ⊧ₘ* (paLX : Theory LX)) {P : M → Prop}
    (hP : ∃ e : ℕ → M, ∃ φ : Semiformula LX ℕ 1, ∀ x, P x ↔ Semiformula.Evalm M ![x] e φ) :
    letI : ORingStructure M := ReductModel.reductORing
    (∃ x, P x) → ∃ z, P z ∧ ∀ y, y < z → ¬ P y := by
  letI oM : ORingStructure M := ReductModel.reductORing
  rintro ⟨a, ha⟩
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ z, P z → ∃ y, y < z ∧ P y` (no `<`-least witness). Then `¬P` everywhere (order-induction),
  -- contradicting `ha`.
  have hNP : ∃ e : ℕ → M, ∃ φ : Semiformula LX ℕ 1, ∀ x, (¬ P x) ↔ Semiformula.Evalm M ![x] e φ := by
    rcases hP with ⟨e, φ, hφ⟩
    exact ⟨e, ∼φ, fun x => by
      rw [LogicalConnective.HomClass.map_neg]; exact not_congr (hφ x)⟩
  have hall : ∀ x, ¬ P x := lx_order_induction hM hNP (fun x IH hPx => by
    obtain ⟨y, hy, hPy⟩ := hcon x hPx
    exact IH y hy hPy)
  exact hall a ha

/-! ### Tool for wall D — `X`-essential non-termination of the dominated internal Goodstein run

The lap-29 `DescentArith.igoodstein_nonterminating_of_dominating` consumes an `ℒₒᵣ`-`𝚺₁` bound `b`. But
the Rathjen §3 dominating bound `b k = T̂^{k+2}(βₖ)` is extracted from the **`X`-descent** (wall C), hence
`X`-dependent — it is an `LX`-formula, *not* an `ℒₒᵣ`-`𝚺₁` function — so the inequality-(6) iteration must
run by `lx_succ_induction` (the `X`-essential succ-induction), not `sigma1_pos_succ_induction`. This is the
`LX` analog of the run side, which wall C feeds once it supplies `(b, m₀)`. Axiom-clean. -/

/-- **Wall-D substrate (`X`-essential).** Given an `LX`-definable bound predicate `P k := b k ≤
igoodstein m₀ k` (`hPdef`), the seed domination (`base`), the internalized inequality-(6) step (`step`),
and bound positivity (`hpos`), the internal Goodstein run from `m₀` never reaches `0` in `M`. The
iteration is `lx_succ_induction` over `P` (which mentions `X` through `b`), and positivity transfers
`0 < b k ≤ igoodstein m₀ k`. -/
theorem lx_nonterminating {M : Type} [Nonempty M] [Structure LX M] [Structure.Eq LX M]
    (hM : M ⊧ₘ* (paLX : Theory LX)) :
    letI : ORingStructure M := ReductModel.reductORing
    letI : M ⊧ₘ* (𝗜𝚺₁ : Theory ℒₒᵣ) := ReductModel.reduct_models_isigma1 hM
    ∀ {b : M → M} (m₀ : M),
      (∃ e : ℕ → M, ∃ φ : Semiformula LX ℕ 1,
        ∀ k, (b k ≤ InternalPow.igoodstein m₀ k) ↔ Semiformula.Evalm M ![k] e φ) →
      b 0 ≤ m₀ →
      (∀ k, b k ≤ InternalPow.igoodstein m₀ k →
        b (k + 1) ≤ InternalPow.igoodstein m₀ (k + 1)) →
      (∀ k, 0 < b k) →
      ∀ k, 0 < InternalPow.igoodstein m₀ k := by
  letI oM : ORingStructure M := ReductModel.reductORing
  haveI hI : M ⊧ₘ* (𝗜𝚺₁ : Theory ℒₒᵣ) := ReductModel.reduct_models_isigma1 hM
  intro b m₀ hPdef base step hpos
  have hineq : ∀ k, b k ≤ InternalPow.igoodstein m₀ k := by
    refine lx_succ_induction hM hPdef ?_ step
    simpa using base
  intro k
  exact lt_of_lt_of_le (hpos k) (hineq k)

/-! ### Step 3 — the genuine remaining obligation (Rathjen §3 in `M`), as ONE named `sorry` -/

/-- **The lone remaining wall: a non-`MX`-minimal seed yields a contradiction with Goodstein-in-`M`
(DISCLOSED `sorry`).** This is Rathjen "Goodstein revisited" §3 carried out *inside `M`*: given the
"no `Mlt`-minimal non-`MX` element" fact `no_min` (so `MX`'s complement is `Mlt`-progressive-downward) and
the Goodstein-termination fact `hgood`, derive `False`. Discharge plan:

1. **M-internal `Mlt`-descent.** From `no_min` + `ha₀`, build a *definable* descending sequence
   `G : M → M`, `G 0 = a₀`, `G(k+1) =` `Mlt`-least `y` with `Mlt y (G k) ∧ ¬MX y`, via `M`'s LX
   least-number principle (`hM ⊧ InductionScheme LX Set.univ`; `Arithmetic.succInd`/`leastNumber` are
   generic over `[LX.ORing]`). **Must be M-internal** (definable + M-recursion), *not* metatheoretic
   `choice`, so the run aligns with `M`'s internal termination statement (see `PENDING_WORK.md` ⚠).
2. **`M`'s `ℒₒᵣ`-reduct as `𝗜𝚺₁`.** `hM ⊧ paLX ⊇ lMap 𝗣𝗔` ⟹ reduct `⊧ 𝗣𝗔 ⊇ 𝗜𝚺₁`; install it as the
   substrate's `[ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁]`.
3. **Slow-down + inequality (6).** Slow `(G k)` ⟹ `(βₖ)` (`C(βₖ) ≤ k+1`); run the special Goodstein seq
   from `m₀ = T̂²(β₀)` (lap-26 `igoodstein` in the reduct); iterate `DescentCore.ineq6_step` by `M`'s
   LX-induction ⟹ `M ⊧ ∀k mₖ > 0`; contradict `hgood`.

The free predicate `X` (`MX`) is present throughout (a model of `paLX`, not `𝗜𝚺₁`) — the lap-24 free-`X`
obstruction does not apply. The lap-26 substrate supplies the run; this lemma is the genuine content. -/
theorem no_min_descent_absurd_of_goodstein {M : Type} [Nonempty M] [Structure LX M]
    [Structure.Eq LX M]
    (hgood : M ⊧ₘ (Semiformula.lMap GoodsteinPA.DescentLift.Φ goodsteinSentence : Sentence LX))
    (hM : M ⊧ₘ* (paLX : Theory LX)) {f : ℕ → M} {a₀ : M} (ha₀ : ¬ MX a₀)
    (no_min : ∀ x : M, ¬ MX x → ∃ y, Mlt f y x ∧ ¬ MX y) : False := by
  -- Install `M`'s `ℒₒᵣ`-reduct as a genuine model of `𝗜𝚺₁`. This is the payoff of the lap-33
  -- `[Structure.Eq LX M]` plumbing: the internal Goodstein substrate (`InternalPow.igoodstein`,
  -- `DescentArith.*`) runs over `[ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁]`.
  letI oM : ORingStructure M := ReductModel.reductORing
  haveI hI : M ⊧ₘ* (𝗜𝚺₁ : Theory ℒₒᵣ) := ReductModel.reduct_models_isigma1 hM
  -- ───────────────────────────────────────────────────────────────────────────────────────────
  -- WALL C+D (disclosed). The `X`-definable `Mlt`-descent extracted from `no_min`/`ha₀`, slowed
  -- down (Rathjen §3, so `C(βₖ) ≤ k+1`), seeds a special internal Goodstein run `igoodstein m₀`
  -- whose dominating `𝚺₁`-bound `b k = T̂^{k+2}(βₖ)` keeps it `> 0` forever. The run side is ALREADY
  -- axiom-clean (`DescentArith.igoodstein_nonterminating_of_dominating`: given `(base, step, hpos)`
  -- it yields `∀ k, 0 < igoodstein m₀ k`); the open content is the seed/bound construction from the
  -- descent + the internalized `ineq6_step` (`DescentCore.ineq6_step`, route-neutral kernel).
  have hCD : ∃ m₀ : M, ∀ k : M, 0 < InternalPow.igoodstein m₀ k := by
    sorry
  obtain ⟨m₀, hpos⟩ := hCD
  -- ───────────────────────────────────────────────────────────────────────────────────────────
  -- WALL B (disclosed). `hgood` says `M`'s `ℒₒᵣ`-reduct models `goodsteinSentence`
  -- (`= ∀⁰ codeOfREPred goodsteinTerminates`, the *opaque* r.e.-blob). Bridge the blob to the
  -- *transparent* internal run inside `M ⊧ 𝗜𝚺₁`: the `igoodstein`-run from `m₀` reaches `0`. This is
  -- the Σ₁-definitional agreement of `codeOfREPred goodsteinTerminates` with `∃ k, igoodstein · k = 0`
  -- (`reduct_models_goodstein` supplies the blob; the gap is the code↔run equivalence in `M`).
  have hB : ∃ k : M, InternalPow.igoodstein m₀ k = 0 := by
    sorry
  obtain ⟨k, hk⟩ := hB
  exact absurd hk (hpos k).ne'

/-! ### The single semantic obligation, assembled (Rathjen §3, model-internal) -/

/-- **The E wall, reduced to one model-theoretic statement.** Under `𝗣𝗔 ⊢ goodsteinSentence`, *every*
model `M ⊧ paLX` satisfies `TI prec`. Steps 1–2 (`models_lMap_goodstein`, `evalfm_TI_unfold`) and the
progressivity-contrapositive are PROVED here; the genuine remaining content is the single named
`sorry` `no_min_descent_absurd_of_goodstein` (Rathjen §3 in `M`). -/
theorem paLX_models_TI_of_PA_provable (h : 𝗣𝗔 ⊢ ↑goodsteinSentence)
    {M : Type} [Nonempty M] [Structure LX M] [Structure.Eq LX M]
    (hM : M ⊧ₘ* (paLX : Theory LX)) (f : ℕ → M) :
    Semiformula.Evalfm M f (Boundedness.TI Thm56.prec) := by
  -- Step 1 (PROVED): the lifted Goodstein sentence holds in `M`.
  have hgood : M ⊧ₘ (Semiformula.lMap GoodsteinPA.DescentLift.Φ goodsteinSentence : Sentence LX) :=
    models_lMap_goodstein h hM
  -- Step 2 (PROVED): reduce to abstract transfinite induction for `(Mlt f, MX)`.
  rw [evalfm_TI_unfold]
  intro hProg
  -- Suppose `MX` is not total: `¬MX a₀` for some `a₀`.
  by_contra hcon
  rw [not_forall] at hcon
  obtain ⟨a₀, ha₀⟩ := hcon
  -- PROVED (progressivity-contrapositive): the non-`MX` set has no `Mlt`-minimal element.
  have no_min : ∀ x : M, ¬ MX x → ∃ y, Mlt f y x ∧ ¬ MX y := fun x hx => by
    by_contra hc
    rw [not_exists] at hc
    exact hx (hProg x (fun y hy => by by_contra hny; exact hc y ⟨hy, hny⟩))
  -- Step 3 (the lone remaining obligation): the descent + Goodstein run contradiction.
  exact no_min_descent_absurd_of_goodstein hgood hM ha₀ no_min

/-! ### `DescentE` via first-order completeness -/

/-- **`Thm56.DescentE`, proved via completeness (modulo the disclosed semantic `sorry`).** From
`𝗣𝗔 ⊢ goodsteinSentence`, `completeness_of_encodable` turns the single semantic premise
`paLX_models_TI_of_PA_provable` into the derivation `paLX ⟹ [TI prec]`, then `toDerivation2` packages it
as the `Derivation2 paLX {TI prec}` that `DescentE` requires. -/
theorem descentE : Thm56.DescentE := by
  intro h
  -- The closed-sentence form of `TI prec` (it is free-variable-free: `Thm56.freeVariables_TI`).
  let tiSent : Sentence LX := (Boundedness.TI Thm56.prec).toEmpty Thm56.freeVariables_TI
  -- Semantic premise, now with genuine equality available in each model (via `𝗘𝗤 ⪯ paLX`):
  -- `consequence_iff_eq` lets us WLOG-assume `[Structure.Eq LX M]` (every model is elementarily
  -- equivalent to its `QuotEq`-quotient, and `𝗘𝗤 ⪯ paLX` preserves `paLX` under that quotient).
  have hsem : (GoodsteinPA.EmbeddingX.paLX : Theory LX) ⊨ tiSent := by
    rw [show ((GoodsteinPA.EmbeddingX.paLX : Theory LX) ⊨ tiSent)
          = ((GoodsteinPA.EmbeddingX.paLX : Theory LX) ⊨[Struc.{0,0} LX] tiSent) from rfl,
        consequence_iff_eq]
    intro M _ _ _ hM
    rw [models_iff]
    exact (Semiformula.eval_toEmpty Thm56.freeVariables_TI).mp
      (paLX_models_TI_of_PA_provable h hM (fun _ => Classical.arbitrary M))
  -- Completeness (`complete : T ⊨ φ → T ⊢ φ`): the semantic premise lifts to syntactic provability.
  have hprov : (GoodsteinPA.EmbeddingX.paLX : Theory LX) ⊢ tiSent := complete hsem
  -- Repackage `paLX ⊢ tiSent` as a `Schema`-`Derivation2`, then rewrite `↑tiSent = TI prec`.
  have h2 : (GoodsteinPA.EmbeddingX.paLX : Schema LX) ⊢!₂! (↑tiSent : SyntacticFormula LX) :=
    provable_iff_derivable2.mp (provable_def.mp hprov)
  rwa [show (↑tiSent : SyntacticFormula LX) = Boundedness.TI Thm56.prec
        from Semiformula.emb_toEmpty (Boundedness.TI Thm56.prec) Thm56.freeVariables_TI] at h2

/-- **The headline, modulo the one disclosed semantic `sorry`.** Combining `descentE` with the proved
reduction `Thm56.peano_not_proves_goodstein_of_descent` yields `𝗣𝗔 ⊬ goodsteinSentence`. This carries a
`sorryAx` (from `paLX_models_TI_of_PA_provable`) and is therefore **NOT** wired into `Statement.lean`'s
headline (anti-fraud). It exists so `#print axioms` audits the *full* chain: the only non-trust-base
axioms must be `sorryAx` + the F-φ `native_decide` artifact — no `PA_delta1Definable`, no custom axiom. -/
theorem peano_not_proves_goodstein_modulo_semantic : 𝗣𝗔 ⊬ ↑goodsteinSentence :=
  Thm56.peano_not_proves_goodstein_of_descent descentE

end GoodsteinPA.DescentSemantic
