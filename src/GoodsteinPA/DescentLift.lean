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

end GoodsteinPA.DescentLift
