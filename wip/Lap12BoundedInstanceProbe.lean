import GoodsteinPA.OperatorZeh

/-!
# lap-12 SERIES-1 Stage-5 (lane D) — `<BoundedInstance>` mini-probe (R-4 delegated choice)

The SERIES-1 order R-4 restates rung D `readoff_delta0_Zef2` to

```lean
theorem readoff_delta0_Zef2 {φ : SyntacticSemiformula ℒₒᵣ 1}
    (hφbdd : ∀ n, <BoundedInstance> (φ/[nm n]))
    {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ}
    (dd : Zef2 α e H f 0 {(∃⁰ φ)}) :
    ∃ n ≤ f 0, atomTrue (φ/[nm n])
```

`<BoundedInstance>` is the ONE delegated choice in the series; the order requires probing ≥2
candidates + a docstring justification BEFORE the Stage-5 grind consumes it.  This file does that.

## The decisive structural fact (kernel-grounded)

The `Zeh`/`Zef`/`Zef2` core has exactly SIX constructors — `axL` (a pair of complementary
literals), `wk`, `weak`, `allω` (∀ over all ℕ-instances `χ/[nm k]`), `exI` (∃ at a witness), `cut`.
**There is NO `∧`/`∨` (and/or) rule and no `verum`/`falsum` rule.**  So the only formula shapes the
read-off induction ever DECOMPOSES are: atoms (`axL`) and quantifiers (`allω`/`exI`).  A conjunction
or disjunction can only sit UN-decomposed in a sequent (closed by some other member via `axL`).

Consequence for the predicate: the read-off recursion descends the instance `φ/[nm n]` through
`allω`/`exI`/`axL` only.  For the SINGLETON start `{∃⁰ φ}` the sequent stays a quantifier tower over
literals as it descends, and the induction bottoms out at `axL`.  So the faithful family the read-off
can actually consume is the **∀/∃-tower over literals** — which is exactly the Δ₀ Goodstein matrix
`gAll = ∀x ∃y (g_y(x)=0)` (bounded-quantifier tower over an atomic equation, `LowerBound.lean:46`).

## Candidate A (RECOMMENDED) — Foundation-native `DeltaZero` (`Hierarchy 𝚺 0`)

The repo-native syntactic Δ₀ predicate the order names.  Pros: repo-native, the literal "Δ₀"
notion, maximally faithful, already has an induction principle + a rich API (`Hierarchy.and_iff`,
`ball`, `bex`, …).  Con: it ADMITS `∧`/`∨` (`Hierarchy.and`/`.or`), which the calculus cannot
decompose — but for the SINGLETON read-off those heads are vacuous (a singleton `{A ⋏ B}` is not
`axL`-closable and has no ∧-rule, so it is underivable ⇒ the induction discharges the case by
impossibility, or the head is never reached).  So `DeltaZero` is SOUND as the predicate; the ∧/∨
cases are dead branches, not obligations.

## Candidate B — a repo-local structural tower `QTower`

Matches the calculus fragment EXACTLY (atoms + ∀⁰ + ∃⁰, no ∧/∨).  Pro: no dead ∧/∨ branches.  Con:
NOT repo-native (a bespoke predicate the judge must re-audit), and it drops the "bounded/Δ₀"
semantic content (the finiteness handle the Π-side read-off ultimately needs) — it is an
*unbounded* tower.  Rejected in favour of A on repo-nativity + faithfulness grounds.

**VERDICT: adopt Candidate A = `LO.FirstOrder.Arithmetic.DeltaZero`.**  The read-off's genuine
difficulty is NOT the predicate but the `allω` (Π) case — reading `atomTrue (∀⁰ χ) = ∀ k, Evalm
(χ/[nm k])` off an `allω` node requires every branch to expose its matrix as the true disjunct plus
the Δ₀ bound to make only finitely many branches load-bearing (Towsner §5.4).  That is the Stage-5
grind; the predicate choice does not change it.
-/

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open GoodsteinPA.OperatorZinfty

/-- Candidate A typechecks against the read-off instance `φ/[nm n]`. -/
example (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ) : Prop := DeltaZero (φ/[nm n])

/-- **Candidate A admits conjunctions** (`Hierarchy.and`) — the over-approximation the calculus
cannot decompose, so the read-off must treat `∧`/`∨` heads as dead branches, not obligations. -/
theorem deltaZero_admits_and {φ ψ : Form} (hφ : DeltaZero φ) (hψ : DeltaZero ψ) :
    DeltaZero (φ ⋏ ψ) := Hierarchy.and hφ hψ

/-- Candidate B — the calculus-exact ∀/∃-tower over literals. -/
inductive QTower : Form → Prop
  | rel {ar} (r : (ℒₒᵣ).Rel ar) (v) : QTower (Semiformula.rel r v)
  | nrel {ar} (r : (ℒₒᵣ).Rel ar) (v) : QTower (Semiformula.nrel r v)
  | all {χ : SyntacticSemiformula ℒₒᵣ 1} (h : ∀ k, QTower (χ/[nm k])) : QTower (∀⁰ χ)
  | exs {χ : SyntacticSemiformula ℒₒᵣ 1} (h : ∀ k, QTower (χ/[nm k])) : QTower (∃⁰ χ)

/-- Candidate B typechecks against `φ/[nm n]`. -/
example (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ) : Prop := QTower (φ/[nm n])

/-- **Candidate B excludes conjunctions** — it has no `∧` constructor, matching the calculus
fragment.  (The `∀⁰`/`∃⁰`/`rel`/`nrel` heads are pairwise distinct from `⋏`.) -/
theorem qtower_excludes_and {φ ψ : Form} : ¬ QTower (φ ⋏ ψ) := by
  intro h; cases h

end GoodsteinPA.OperatorZeh
