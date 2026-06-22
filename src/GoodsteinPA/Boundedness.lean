/-
# `wip/Prog.lean` — the `Prog_≺(X)` / `TI_≺(X)` formulas over `LX` (lap-13, Boundedness scaffolding)

The transfinite-induction formula scaffolding the Boundedness theorem (Buchholz Thm 5.4) inverts.
The order `≺` is given by a depth-2 `LX`-formula `prec` (`#0 ≺ #1`); for the headline `prec` is the
ℒₒᵣ-definable CNF-ε₀ order. `X t` is the set-variable atom `Xat t`.

  `Prog_≺(X) := ∀x ((∀y (y ≺ x → X y)) → X x)`
  `TI_≺(X)   := Prog_≺(X) → ∀x X x`

The point of this file (for now) is to pin the de-Bruijn shapes so the Boundedness induction's
inversion cases line up; the proof of Boundedness itself is the next target.
-/
import GoodsteinPA.ZinftyGen
import GoodsteinPA.LangX

namespace GoodsteinPA.Boundedness

open LO LO.FirstOrder
open GoodsteinPA.ZinftyGen GoodsteinPA.LangX

/-- The set-variable atom `X t`. -/
def Xat {n} (t : Semiterm LX ℕ n) : Semiformula LX ℕ n := Semiformula.rel Xsym ![t]

variable (prec : Semiformula LX ℕ 2)

/-- `∀y (y ≺ x → X y)` as a depth-1 formula (free `x = #0`). At depth 2, `prec` reads `#0 ≺ #1`
with `#0 = y`, `#1 = x`. -/
def hyp : Semiformula LX ℕ 1 := ∀⁰ (prec 🡒 Xat (#0))

/-- `Prog_≺(X) := ∀x ((∀y (y ≺ x → X y)) → X x)`. -/
def Prog : Semiformula LX ℕ 0 := ∀⁰ (hyp prec 🡒 Xat (#0))

/-- `TI_≺(X) := Prog_≺(X) → ∀x X x`. -/
def TI : Semiformula LX ℕ 0 := Prog prec 🡒 ∀⁰ (Xat (#0))

-- Probes: the formulas typecheck and their negations have the expected `∃`/`∀` shape for inversion.
example : Form LX := Prog prec
example : Form LX := TI prec
example : ∼(Prog prec) = ∃⁰ ∼(hyp prec 🡒 Xat (#0)) := by simp [Prog]
example : ∼(TI prec) = (Prog prec) ⋏ ∼(∀⁰ (Xat (#0))) := by simp [TI, Semiformula.imp_eq]

end GoodsteinPA.Boundedness
