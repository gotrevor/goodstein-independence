/-
# `DescentLift.lean` — E-lift bricks: `lMap` commutes with the induction-axiom builders

The descent wall **E** (`Thm56.DescentE`) factors (see `DESCENT-PLAN.md`) into **E-core** (the §3
"slowing-down" reasoning inside PA, `𝗣𝗔 ⊢ goodstein → 𝗣𝗔 ⊢ PRWO(ε₀)`) and **E-lift** (the
proof-translation `ℒₒᵣ ↪ LX` that turns a PA-derivation into a `Derivation2 paLX`-object). The
language-map half of E-lift bottoms out at: **`Semiformula.lMap (ORing.embedding LX)` commutes with
Foundation's `succInd`** (the induction-axiom builder), so that

    `Theory.lMap (ORing.embedding LX) (InductionScheme ℒₒᵣ univ) ⊆ InductionScheme LX univ`,

and hence `(𝗣𝗔 : Schema ℒₒᵣ).lMap (ORing.embedding LX) ⊆ (paLX : Schema LX)` — the schema inclusion
that lets `Derivation.lMap` carry a PA-derivation into the `paLX` calculus.

The genuine friction here is that the `“…”` arithmetic DSL desugars `0` / `#0 + 1` into
`Rew.subst _ (Rew.emb op.term)`, and there is **no ready-made `Semiterm.lMap_operator` lemma**; the
ORing embedding fixes the ring/successor function symbols (`Language.ORing.embedding`), so these
operator terms are `lMap`-invariant, but that has to be proved symbol-by-symbol. `lMap_zero_const`,
`lMap_one_const`, `lMap_succT` are those leaves; `lMap_succInd` assembles them.

These are pure Foundation-syntax facts (ZERO Goodstein content), reusable for the whole E-lift, and
`#print axioms`-clean. See `DESCENT-PLAN.md §2` for how they slot into the X-free lift lemma.
-/
import GoodsteinPA.EmbeddingX

namespace GoodsteinPA.DescentLift

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open GoodsteinPA GoodsteinPA.LangX

/-- The order-ring language embedding `ℒₒᵣ ↪ LX` along which a PA-derivation is translated. -/
abbrev Φ : ℒₒᵣ →ᵥ LX := Language.ORing.embedding LX

/-- `lMap Φ` fixes the constant `0`-term: `Φ` maps `Zero.zero ↦ Zero.zero`, and the term `op(0)` is
`func Zero.zero ![]` (`Operator.Zero.term_eq`), whose only data is the fixed symbol. -/
theorem lMap_zero_const {ξ n} :
    Semiterm.lMap Φ (Semiterm.Operator.Zero.zero.const : Semiterm ℒₒᵣ ξ n)
      = (Semiterm.Operator.Zero.zero.const : Semiterm LX ξ n) := by
  simp only [Semiterm.Operator.const, Semiterm.Operator.operator, Semiterm.Operator.Zero.term_eq,
    Rew.func, Semiterm.lMap_func]
  exact congrArg (Semiterm.func Language.Zero.zero) (funext fun i => i.elim0)

/-- `lMap Φ` fixes the constant `1`-term (same argument as `lMap_zero_const`, symbol `One.one`). -/
theorem lMap_one_const {ξ n} :
    Semiterm.lMap Φ (Semiterm.Operator.One.one.const : Semiterm ℒₒᵣ ξ n)
      = (Semiterm.Operator.One.one.const : Semiterm LX ξ n) := by
  simp only [Semiterm.Operator.const, Semiterm.Operator.operator, Semiterm.Operator.One.term_eq,
    Rew.func, Semiterm.lMap_func]
  exact congrArg (Semiterm.func Language.One.one) (funext fun i => i.elim0)

set_option maxHeartbeats 1600000 in
/-- `lMap Φ` fixes the successor term `#0 + 1` (depth-1): `Add.add` is fixed by `Φ`, the first
argument `#0` is a bvar (fixed), and the second is the `1`-const (`lMap_one_const`). This is the
successor term `succInd`'s step uses. -/
theorem lMap_succT {ξ} :
    Semiterm.lMap Φ (‘(#0 + 1)’ : Semiterm ℒₒᵣ ξ 1) = (‘(#0 + 1)’ : Semiterm LX ξ 1) := by
  simp only [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Semiterm.lMap_func, Rew.emb_bvar, Rew.subst_bvar]
  refine congrArg (Semiterm.func Language.Add.add) (funext fun i => ?_)
  refine i.cases ?_ (fun j => ?_)
  · simp
  · refine j.cases ?_ (fun k => k.elim0)
    simp only [Matrix.cons_val_one, Fin.succ_zero_eq_one]
    exact lMap_one_const

set_option maxHeartbeats 1600000 in
/-- **`lMap Φ` commutes with `succInd`.** `Semiformula.lMap Φ (succInd φ) = succInd (lMap Φ φ)`.
`succInd φ = “!φ 0 → (∀x, !φ x → !φ (x+1)) → ∀x !φ x”` translates termwise; the connectives/quantifiers
commute with `lMap` by the `@[simp]` `lMap_*` lemmas, and the two substituted terms `0` and `#0+1`
are `lMap`-fixed (`lMap_zero_const` / `lMap_succT`). This is the workhorse for the induction-scheme
inclusion `lMap (InductionScheme ℒₒᵣ univ) ⊆ InductionScheme LX univ`. -/
theorem lMap_succInd (φ : Semiformula ℒₒᵣ ℕ 1) :
    Semiformula.lMap Φ (succInd φ) = succInd (Semiformula.lMap Φ φ) := by
  unfold succInd
  simp [Semiformula.lMap_subst]
  refine ⟨?_, ?_⟩
  · exact congrArg (fun t => (Semiformula.lMap Φ φ)/[t]) lMap_zero_const
  · exact congrArg (fun t => (Semiformula.lMap Φ φ)/[t]) lMap_succT

/-! ## `lMap` commutes with `univCl`, and the induction-scheme inclusion -/

/-- `fvSup` is preserved by `lMap` (it is a function of the free-variable set, which `lMap` fixes by
`freeVariables_lMap`). Needed so the `allClosure` count in `univCl'` matches across the translation. -/
theorem fvSup_lMap (ψ : SyntacticFormula ℒₒᵣ) : (Semiformula.lMap Φ ψ).fvSup = ψ.fvSup := by
  unfold Semiformula.fvSup; rw [Semiformula.freeVariables_lMap]

/-- `lMap` commutes with `Rew.fixitr 0 k` (the "fix all `< k` free variables" rewriting). `fixitr 0 k`
is `k`-fold `Rew.fix` (`fixitr_succ`), and `lMap` commutes with each `Rew.fix` (`lMap_fix`). -/
theorem lMap_fixitr (k : ℕ) (ψ : SyntacticSemiformula ℒₒᵣ 0) :
    Semiformula.lMap Φ (Rew.fixitr 0 k ▹ ψ) = Rew.fixitr 0 k ▹ (Semiformula.lMap Φ ψ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Rew.fixitr_succ, TransitiveRewriting.comp_app, Semiformula.lMap_fix, ih,
      Rew.fixitr_succ, TransitiveRewriting.comp_app]

/-- `lMap` commutes with the syntactic universal closure `univCl'` (`∀⁰*` over `fixitr`-fixed
variables): the closure count `fvSup` is `lMap`-invariant and `lMap` passes through both `∀⁰*`
(`lMap_allClosure`) and `fixitr` (`lMap_fixitr`). -/
theorem lMap_univCl' (ψ : SyntacticFormula ℒₒᵣ) :
    Semiformula.lMap Φ ψ.univCl' = (Semiformula.lMap Φ ψ).univCl' := by
  unfold Semiformula.univCl'
  rw [Semiformula.lMap_allClosure, fvSup_lMap, lMap_fixitr]

/-- `lMap` commutes with the sentence-level universal closure `univCl`. Via injectivity of the
`Sentence ↪ SyntacticFormula` coercion (`coe_inj`): both sides coerce to `(lMap Φ ψ).univCl'`
(`coe_univCl_eq_univCl'` + `lMap_emb` + `lMap_univCl'`). -/
theorem lMap_univCl (χ : SyntacticFormula ℒₒᵣ) :
    Semiformula.lMap Φ (Semiformula.univCl χ) = Semiformula.univCl (Semiformula.lMap Φ χ) := by
  apply (Semiformula.coe_inj _ _).mp
  rw [Semiformula.coe_univCl_eq_univCl', ← Semiformula.lMap_emb,
    Semiformula.coe_univCl_eq_univCl', lMap_univCl']

/-- **The induction-scheme inclusion.** `lMap (ORing.embedding LX)` carries every full
`ℒₒᵣ`-induction axiom to a full `LX`-induction axiom: an instance `univCl (succInd φ)` maps to
`univCl (succInd (lMap Φ φ))` (`lMap_univCl` + `lMap_succInd`), which is the `LX`-instance for the
formula `lMap Φ φ` (the universe predicate accepts it). This is the binding step that lets a
PA-derivation's induction axioms land inside `paLX`. -/
theorem lMap_inductionScheme_subset :
    Theory.lMap Φ (InductionScheme ℒₒᵣ Set.univ) ⊆ InductionScheme LX Set.univ := by
  rintro σ' ⟨σ, hσ, rfl⟩
  obtain ⟨φ, -, rfl⟩ := hσ
  rw [lMap_univCl, lMap_succInd]
  exact ⟨Semiformula.lMap Φ φ, trivial, rfl⟩

/-! ## The X-free E-lift: a PA-derivation translates into a `paLX`-derivation -/

/-- `Theory.lMap Φ 𝗣𝗔 ⊆ paLX`: `𝗣𝗔 = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ univ`; its `𝗣𝗔⁻`-image is `paLX`'s
first summand verbatim, and its induction-scheme image lands in `InductionScheme LX univ` (`paLX`'s
second summand) by `lMap_inductionScheme_subset`. -/
theorem lMap_PA_subset : Theory.lMap Φ 𝗣𝗔 ⊆ (GoodsteinPA.EmbeddingX.paLX : Theory LX) := by
  show Theory.lMap Φ (𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ) ⊆ _
  rw [Theory.add_def, Theory.lMap, Set.image_union]
  exact Set.union_subset (fun _ hx => Or.inl (Or.inl hx))
    (fun _ hx => Or.inl (Or.inr (lMap_inductionScheme_subset hx)))

/-! ## `𝗘𝗤 ⪯ paLX` — the equality axioms hold in `paLX` (Task A2, lap-32)

The completeness route needs `[Structure.Eq LX M]` for the substrate's real `=`; supplying it via
`consequence_iff_eq`/`EQ.provOf` needs `𝗘𝗤 ⪯ paLX`. The ℒₒᵣ-part of `𝗘𝗤(LX)` is the `lMap Φ`-image of
`𝗘𝗤(ℒₒᵣ) ⊆ 𝗣𝗔⁻ ⊆`-image-of-`paLX`; the lone non-ℒₒᵣ axiom `relExt Xsym` is the third summand of `paLX`.
So `𝗘𝗤(LX) ⊆ paLX` as a set, hence `𝗘𝗤 ⪯ paLX` by `WeakerThan.ofSubset`. -/

/-- `Φ` (`ORing.embedding`) sends an `ℒₒᵣ` relation symbol to its `Sum.inl` injection in `LX`. -/
lemma phi_rel {k} (r : (ℒₒᵣ : Language).Rel k) : Φ.rel r = Sum.inl r := by cases r <;> rfl

/-- `Φ` sends an `ℒₒᵣ` function symbol to its `Sum.inl` injection in `LX`. -/
lemma phi_func {k} (f : (ℒₒᵣ : Language).Func k) : Φ.func f = Sum.inl f := by cases f <;> rfl

/-- `LX`'s `=`-symbol is `Sum.inl` of `ℒₒᵣ`'s (the `Language.Eq LX` instance). -/
lemma lx_eq : (Language.Eq.eq : LX.Rel 2) = Sum.inl Language.Eq.eq := rfl

/-- `lMap Φ (Eq.refl) = Eq.refl` (over `LX`). -/
lemma lMap_eq_refl : Semiformula.lMap Φ (Theory.Eq.refl ℒₒᵣ) = (Theory.Eq.refl LX) := by
  simp [Theory.Eq.refl, Semiformula.Operator.eq_def, phi_rel, lx_eq]

/-- `lMap Φ (Eq.symm) = Eq.symm` (over `LX`). -/
lemma lMap_eq_symm : Semiformula.lMap Φ (Theory.Eq.symm ℒₒᵣ) = (Theory.Eq.symm LX) := by
  simp [Theory.Eq.symm, Semiformula.Operator.eq_def, phi_rel, lx_eq]

/-- `lMap Φ (Eq.trans) = Eq.trans` (over `LX`). -/
lemma lMap_eq_trans : Semiformula.lMap Φ (Theory.Eq.trans ℒₒᵣ) = (Theory.Eq.trans LX) := by
  simp [Theory.Eq.trans, Semiformula.Operator.eq_def, phi_rel, lx_eq]

set_option maxHeartbeats 4000000 in
/-- `lMap Φ (Eq.relExt r) = Eq.relExt (Φ.rel r)` — the equality-extensionality axiom translates to the
extensionality axiom for the image relation symbol. -/
lemma lMap_relExt {k} (r : (ℒₒᵣ : Language).Rel k) :
    Semiformula.lMap Φ (Theory.Eq.relExt r) = Theory.Eq.relExt (Φ.rel r) := by
  cases r <;>
    simp [Theory.Eq.relExt, Semiformula.Operator.eq_def, Semiformula.lMap_rel, Semiterm.lMap_bvar,
      Matrix.conj, Matrix.vecTail, Function.comp, lx_eq, phi_rel, Matrix.fun_eq_vec_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

set_option maxHeartbeats 4000000 in
/-- `lMap Φ (Eq.funcExt f) = Eq.funcExt (Φ.func f)`. -/
lemma lMap_funcExt {k} (f : (ℒₒᵣ : Language).Func k) :
    Semiformula.lMap Φ (Theory.Eq.funcExt f) = Theory.Eq.funcExt (Φ.func f) := by
  cases f <;>
    simp [Theory.Eq.funcExt, Semiformula.Operator.eq_def, Semiformula.lMap_rel, Semiterm.lMap_func,
      Semiterm.lMap_bvar, Matrix.conj, Matrix.vecTail, Function.comp, lx_eq, phi_rel, phi_func,
      Matrix.fun_eq_vec_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- **`𝗘𝗤(LX) ⊆ paLX`.** Each `𝗘𝗤(LX)` axiom is either the `lMap Φ`-image of an `𝗘𝗤(ℒₒᵣ) ⊆ 𝗣𝗔⁻`
axiom (refl/symm/trans/funcExt/relExt over ℒₒᵣ symbols — `paLX`'s first summand) or `relExt Xsym`
(`paLX`'s third summand). -/
theorem eqLX_subset_paLX : (𝗘𝗤 : Theory LX) ⊆ (GoodsteinPA.EmbeddingX.paLX : Theory LX) := by
  have hbase : ∀ σ : Sentence ℒₒᵣ, σ ∈ (𝗘𝗤 : Theory ℒₒᵣ) →
      Semiformula.lMap Φ σ ∈ (GoodsteinPA.EmbeddingX.paLX : Theory LX) := by
    intro σ hσ
    exact Or.inl (Or.inl ⟨σ, PeanoMinus.equal σ hσ, rfl⟩)
  intro σ hσ
  cases hσ with
  | refl => exact (lMap_eq_refl ▸ hbase _ Theory.eqAxiom.refl)
  | symm => exact (lMap_eq_symm ▸ hbase _ Theory.eqAxiom.symm)
  | trans => exact (lMap_eq_trans ▸ hbase _ Theory.eqAxiom.trans)
  | funcExt f =>
    cases f with
    | inl f₀ =>
      have := hbase _ (Theory.eqAxiom.funcExt f₀)
      rwa [lMap_funcExt, phi_func] at this
    | inr e => exact e.elim
  | relExt r =>
    cases r with
    | inl r₀ =>
      have := hbase _ (Theory.eqAxiom.relExt r₀)
      rwa [lMap_relExt, phi_rel] at this
    | inr xr =>
      cases xr
      exact Or.inr rfl

/-- **`𝗘𝗤 ⪯ paLX`** — the instance the completeness route's `consequence_iff_eq`/`EQ.provOf` needs. -/
instance eqAxiom_weakerThan_paLX : (𝗘𝗤 : Theory LX) ⪯ (GoodsteinPA.EmbeddingX.paLX : Theory LX) :=
  Entailment.WeakerThan.ofSubset eqLX_subset_paLX

/-- The schema coercion commutes with `lMap`: `(T : Schema).lMap Φ = (Theory.lMap Φ T : Schema)`
(both are `lMap`/`emb` images; they agree by `lMap_emb`). -/
theorem coe_schema_lMap (T : Theory ℒₒᵣ) :
    Schema.lMap Φ (T : Schema ℒₒᵣ) = ((Theory.lMap Φ T : Theory LX) : Schema LX) := by
  unfold Schema.lMap Theory.toSchema Theory.lMap
  rw [Set.image_image, Set.image_image]
  exact Set.image_congr (fun σ _ => Semiformula.lMap_emb σ)

/-- The schema-level form of `lMap_PA_subset`. -/
theorem schema_lMap_PA_subset :
    Schema.lMap Φ (𝗣𝗔 : Schema ℒₒᵣ) ⊆ ((GoodsteinPA.EmbeddingX.paLX : Theory LX) : Schema LX) := by
  rw [coe_schema_lMap]; exact (Theory.coe_subset_coe).mpr lMap_PA_subset

/-- **The X-free E-lift.** A `𝗣𝗔`-proof of any `ℒₒᵣ`-sentence `σ` translates into a `Derivation2`
of its `LX`-image in the `paLX` calculus: take the Tait derivation (`provable_def`), `lMap` it
(`Derivation.lMap`), weaken the schema along `schema_lMap_PA_subset`, and repackage as a `Derivation2`
(`provable_iff_derivable2`). This is the proof-translation half of E-lift; the descent wall **E**
remains because `TI prec` mentions the set variable `X` and is *not* such an `lMap`-image (see
`DESCENT-PLAN.md §1`) — the X-induction instance is the missing E-core content. -/
theorem paLX_derivable2_lMap_of_PA_provable (σ : Sentence ℒₒᵣ) (h : 𝗣𝗔 ⊢ σ) :
    Nonempty (Derivation2 ((GoodsteinPA.EmbeddingX.paLX : Theory LX) : Schema LX)
      {Semiformula.lMap Φ (↑σ : SyntacticFormula ℒₒᵣ)}) := by
  have h1 : (𝗣𝗔 : Schema ℒₒᵣ) ⊢ (↑σ : SyntacticFormula ℒₒᵣ) := provable_def.mp h
  have d := h1.get
  have h3 : Schema.lMap Φ (𝗣𝗔 : Schema ℒₒᵣ) ⊢ Semiformula.lMap Φ (↑σ : SyntacticFormula ℒₒᵣ) :=
    ⟨Derivation.cast (Derivation.lMap Φ d) (by simp)⟩
  have h4 : ((GoodsteinPA.EmbeddingX.paLX : Theory LX) : Schema LX)
      ⊢ Semiformula.lMap Φ (↑σ : SyntacticFormula ℒₒᵣ) :=
    (Entailment.Axiomatized.weakerThanOfSubset schema_lMap_PA_subset).pbl h3
  exact provable_iff_derivable2.mp h4

end GoodsteinPA.DescentLift
