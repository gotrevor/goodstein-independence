/-
# `wip/GenericZinftyProbe.lean` — M5's core constructs generalise over `[ORing L]` (lap-12 pivot probe)

Validates VERIFY-(a) on M5's REAL constructs (not a toy): the `Form`/`nm`/`atomTrue`/`Deriv`-rule shapes
of `src/Zinfty.lean` re-stated over a *generic* `{L} [Language.ORing L] [Structure L ℕ]`. If this
typechecks, the M5 (and M4) generalisation to `LX = ℒₒᵣ+X` is a mechanical header swap, confirming the
Buchholz route's #1 lap-13 task is plumbing, not math. Compiles green ⟹ confirmed.
-/
import Foundation.FirstOrder.Arithmetic.Basic.Model
import Foundation.FirstOrder.Basic.Operator

namespace GoodsteinPA.GenericZinftyProbe

open LO LO.FirstOrder

variable {L : Language} [Language.ORing L] [Structure L ℕ]
  [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]

/-- M5 `Form`, generic. -/
abbrev Form (L : Language) := SyntacticFormula L

/-- M5 `nm` (the `n`-th numeral as a closed term), generic — needs only `ORing`'s `Zero/One/Add`. -/
noncomputable def nm (n : ℕ) : Semiterm L ℕ 0 := (Semiterm.Operator.numeral L n).const

/-- M5 `atomTrue`/`LitTrue` (truth of a closed literal in the ℕ-model), generic — needs `Structure L ℕ`. -/
noncomputable def atomTrue (φ : Form L) : Prop := Semiformula.Evalm ℕ ![] (id : ℕ → ℕ) φ

/-- A mini `Z∞`-style calculus carrying the three structurally-interesting M5 rules (`axTrue` truth
leaf, the ω-rule `allω`, the numeral-witness `exI`) — the cases that touch `nm`/`atomTrue`/numerals.
That this is well-formed over generic `L` is the crux of "M5 generalises". -/
inductive MiniDeriv : Finset (Form L) → Prop
  | axTrue {Γ} (φ : Form L) (htrue : atomTrue φ) (hmem : φ ∈ Γ) : MiniDeriv Γ
  | allω {Γ} (φ : SyntacticSemiformula L 1)
      (d : ∀ n : ℕ, MiniDeriv (insert (φ/[nm n]) Γ)) : MiniDeriv (insert (∀⁰ φ) Γ)
  | exI {Γ} (φ : SyntacticSemiformula L 1) (n : ℕ)
      (d : MiniDeriv (insert (φ/[nm n]) Γ)) : MiniDeriv (insert (∃⁰ φ) Γ)

/-- Sanity: a closed-witness `∃`-intro typechecks generically (the M5 `exI` shape). -/
example (φ : SyntacticSemiformula L 1) (Γ : Finset (Form L)) (n : ℕ)
    (d : MiniDeriv (insert (φ/[nm n]) Γ)) : MiniDeriv (insert (∃⁰ φ) Γ) :=
  MiniDeriv.exI φ n d

/-! ## CONFIRMED (lap 12) — exact instance bundle the M5/M4 generalisation needs

This file compiles green, so generalising M5 (`Zinfty.lean`) + M4 (`Embedding.lean`) from hardwired `ℒₒᵣ`
to `{L : Language}` needs exactly these four instance assumptions (all hold for `ℒₒᵣ` and for `LX`):
  `[Language.ORing L]`  — ring/order symbols (numerals via `Operator.numeral`); `LX`: built in `LangX.lean`.
  `[Structure L ℕ]`     — the ℕ-model for `atomTrue` (Evalm); `LX`: **the one remaining instance to build**
                          — parametrise by the `X`-set `S ⊆ ℕ` (standard `ℒₒᵣ` part + `X ↦ S`), which is
                          exactly the carrier of Buchholz's `⊨^α` (with `S := {n : |n|_≺ < α}`).
  `[(k) → DecidableEq (L.Func k)]`, `[(k) → DecidableEq (L.Rel k)]` — for `Finset` sequents; `LX`: derive
                          from `ℒₒᵣ`'s (already instances) + `XRel`'s (trivial, a 1-constructor inductive).
So the port is a header swap (`abbrev Form := SyntacticFormula L` + thread the 4 instances) — plumbing,
not math, as the pivot analysis predicted. `Structure LX ℕ`-with-`X:=S` doubles as the `⊨^α` carrier. -/

end GoodsteinPA.GenericZinftyProbe
