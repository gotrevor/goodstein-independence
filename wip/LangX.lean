/-
# `wip/LangX.lean` — the language `ℒₒᵣ + X` for the Buchholz Boundedness route (lap-12 pivot)

VERIFY-(a), concretely: define the extended language `ℒₒᵣ` + one unary "set variable" predicate `X`
(Buchholz §5's `L₀(X)`), give it the `ORing` instance (so the full arithmetic API transfers), and confirm
numerals + an `X`-atom formula typecheck. This is the first lego of the pivot (`ANALYSIS-2026-06-22-lap12-
buchholz-pivot.md`): the whole chain (PA, embedding M4, cut-elim M5, Boundedness) lives over this language.
-/
import Foundation.FirstOrder.Arithmetic.Basic.Model
import Foundation.FirstOrder.Basic.Operator

namespace GoodsteinPA.LangX

open LO LO.FirstOrder

/-- The one-unary-relation language carrying Buchholz's set variable `X`. -/
inductive XRel : ℕ → Type
  | X : XRel 1

/-- The language `{X}` (one unary predicate, no functions). -/
def Xpred : Language where
  Func := fun _ => Empty
  Rel := XRel

/-- The extended language `ℒₒᵣ + X` of Buchholz §5. -/
abbrev LX : Language := Language.add ℒₒᵣ Xpred

/-- `ℒₒᵣ`'s ring/order symbols transfer to `LX` via the left injection, giving `LX` its `ORing`
structure — so the whole `Foundation` arithmetic API (numerals, `Structure ℕ`, …) is available. -/
instance : Language.ORing LX where
  eq := Sum.inl (Language.Eq.eq)
  lt := Sum.inl (Language.LT.lt)
  zero := Sum.inl (Language.Zero.zero)
  one := Sum.inl (Language.One.one)
  add := Sum.inl (Language.Add.add)
  mul := Sum.inl (Language.Mul.mul)

/-- The set-variable predicate symbol `X` as a relation of `LX`. -/
def Xsym : LX.Rel 1 := Sum.inr XRel.X

/-- `X t` as an `LX`-formula (for a term `t`). -/
def Xatom {ξ n} (t : Semiterm LX ξ n) : Semiformula LX ξ n :=
  Semiformula.rel Xsym ![t]

-- Probes: numerals exist over `LX`, and an `X`-atom on the numeral `3` typechecks.
noncomputable example : Semiterm.Const LX := Semiterm.Operator.numeral LX 3
noncomputable example : Semiformula LX ℕ 0 := Xatom ((Semiterm.Operator.numeral LX 3).const)

/-- The `ORing` embedding `ℒₒᵣ →ᵥ LX` (Foundation's `Language.ORing.embedding`), the hook for
re-instantiating M4/M5 (currently hardwired to `ℒₒᵣ`) over `LX`. -/
noncomputable example : ℒₒᵣ →ᵥ LX := Language.ORing.embedding LX

end GoodsteinPA.LangX
