# E — JUDGE route-review input for the lap-171 gate (Ren, 2026-07-01)

> **Judge/host session (Ren), NOT a grind lap.** This is *input* to the lap-171 verdict, not the verdict
> itself (the verdict is written by the gate lap to `ROUTE-ESCALATION-2026-06-28.md` and handed to the
> operator). Grounded in: a 4-reader review of the repo (strategic history · crux-2 depth · code reality ·
> math-done-vs-engineering) + direct reading of `DIRECTION.md`, `ROUTE-ESCALATION`, `E-ROUTE-OPTIONS`,
> the lap-168/169 handoffs, and a **machine-grounded probe of escape hypothesis (α)** against the live
> substitution API. Self-contained; pasteable to Codex / the operator.

## TL;DR — recommendation for the gate

1. **Verdict leans `PIVOT-B`** (~70%). Escape (α) is **DEAD** (below, 95%), escape (β) reduces to
   "adopt the ω-rule," and the M2 induction leaf on Route A is blocked by a *principled expressiveness
   gap*, not an engineering oversight. Lap 170 should confirm (β) is dead-or-equals-meta, then write it.
2. **The real completion probability is ~30–40% by the best route, not single digits** — the naive
   7-node product (~7–8%) is the wrong model (correlation, not independence; see §2). No route clears ~50%.
3. **`PIVOT-B` must name its target.** "B" is overloaded (§4): the **Towsner operator lane** Codex built
   (still has a cut-elim wall) vs the **Wainer growth-rate route** (Castéran Coq blueprint, no cut-elim).
   The induction-leaf finding this session **rebalances toward Towsner** more than the escalation assumed.

## 1. Escape (α) is DEAD — machine-grounded (95%)

The lap-168 "induction leaf is bounded, every rule is present" optimism was overturned at lap 169: the
step premise `Γ, φ(b) → φ(b+1)` (free eigenvariable `b`) is **not closable by internal Z's nine rules**
— Z's only ∀-left `zAxAll` instantiates at a **numeral** only (`zAxAllSuccWff`, `InternalZ.lean:1576`),
and there is no ∨-/→-left rule for `∼φ(b) ^⋎ φ(b+1)`.

Lap-170's escape (α) asked: is there an **admissible free-variable ∀-left** / a substitution lemma that
lifts a numeral-instance derivation family to a free-variable one? **Answer: no.** The only derivation-level
substitution lemma is

    ZDerivation_zsubst {a t} (ht : IsSemiterm ℒₒᵣ 0 t) :
      ∀ d, ZDerivation d → maxEigen d < a → ZDerivation (zsubst d a t)   -- Zsubst.lean:3674

which substitutes a **free variable `^&a` ↦ a closed term `t`** — the *forward/binding* direction. Escape (α)
needs the *reverse* (numeral-family ↦ free-var generalization). No lemma of that shape exists anywhere in
`Zsubst.lean` / `FvSubst.lean` / `InternalZ.lean`; the `fvSubst_*` family all commute or bind, none
generalize. This is exactly the **finitary-`zInd` vs ω-rule design fork**: an ω-logic calculus derives the
induction axiom from numeral instances (matching `zAxAll`) + the ω-rule; the finitary eigenvariable `zInd`
needs a free-var ∀-left that ω-logic deliberately omits (it would perturb the numeral-only subformula
property the calculus is built on). **Not a proof-engineering oversight — a calculus-expressiveness gap.**

## 2. The completion odds — why "7%" is wrong AND "65%/node" is wrong

**Not 7%.** The naive `0.8 × 0.65⁵ × 0.75 ≈ 7%` multiplies risks that are (a) **correlated** (nodes 2/3/5
share one calculus; 7/8 are *adapters into an already-proven theorem*, `lowerBound_hardy_selfcontained`,
`LowerBound.lean:362`, 0 sorries), and (b) **already-spent discovery risk** — both of Towsner's glosses
(§19.6 commuting ω-bound, §17.1 ∀-case) are *resolved*, and §17.1's fix is **compiled**. So the residual is
*correlated formalization-engineering on one calculus*, not seven independent discoveries.

**Not 65%/node either.** Two marks-down: (i) there are **two** coupled hard bets — the cut-elim engine AND
the PA-induction embedding (this leaf) — not one; (ii) the realized-difficulty prior is damning — the
structurally-identical wall has been ground ~110 laps, fired **both** pre-registered abort triggers, hit
**≥4 documented false summits**, and confidence has declined monotonically **70% (lap 61) → 55–70% (lap
147) → 30–40% (now)**. The forward-looking per-node confidences inherit that optimism; the *ledger* (proven
/ sorry / axiom-clean) is trustworthy, the *estimates* are not (code reader confirms: the 6 middle marker
Props are empty inductives; node 5, the global embedding over a real PA proof, is **un-started** — the
per-node numbers score "are the rules provable," not "does the global induction run").

**Model:** one-to-two coupled architectural bets on the operator-`Z∞` calculus, each ~coin-flip, everything
else conditional-high ⇒ **~25–40% for the best route**, governed by correlation, not multiplication.

## 3. The unavoidable core (the reframe)

There is **no route that dodges the work.** Every route to `PA ⊬ Goodstein` must *build* ε₀-proof-theoretic
strength in Lean (≈ Bryce–Goré-scale, ~6–7k lines, **never done in Lean**, absent from mathlib). The routes
differ only in the *packaging* of that one monument:

| Route | Packaging of the ε₀ wall | Precedent | Est. |
|---|---|---|---|
| **A — current** (Rathjen → Gödel II) | IΣ₁-**internalized** cut-elim over coded derivations | **un-precedented in any prover** | 30–40%, falling |
| **A′ — Towsner** (the Codex `PathBProbe`/`Zekd` lane) | **meta** cut-elim (Thm 19.9) + lower bound **already banked** | meta cut-elim precedented; still a cut-elim wall | ~25–35% |
| **B — Wainer growth-rate** (Castéran) | **Wainer domination** — *no cut-elim*; Goodstein-len = Hardy `H_{ε₀}` | full **Coq blueprint** to port | ~50% / "~65% net easier" |

A picked the only un-precedented wrapper. The pivot's value is **base-rate** (get to a precedented
packaging), not a clean probability gap. **Do not let anyone call the target "the easy route"** — the
monument is unavoidable; the pivot buys *precedent*, not *escape*.

## 4. The strategic fork the gate should actually decide: which "B"

`PIVOT-B` is used for two different routes and the docs conflate them:
- **Towsner A′** (what Codex has been *building*): keeps a cut-elim wall (node 6), BUT its lower-bound half
  is banked, its scaffold is genuinely clean/sorry-free, AND — the new datapoint this session — it handles
  induction **the right way**: the meta calculus already proves `inductionLeaf_runningIndex_witnessBound`
  (`OperatorZinfty.lean:1033`, the ω-rule premise at index `max k n` pays the witness budget) where
  `inductionLeaf_fixedIndex_witnessBound_impossible` (`:1025`) shows the finitary index fails. **This is the
  exact wall Route A just died on** — so A′ is *further ahead on the induction bet than the escalation
  credited*, not just "equal-or-harder cut-elim."
- **Wainer B** (the escalation's stated `PIVOT-B`, `no Gödel II / no bridge`): the only route that deletes
  cut-elim entirely; its hard piece (Wainer's classification of PA-provably-total functions) has a complete,
  axiom-free **Coq blueprint** (Castéran `hydra-battles`) to port, plus the Caicedo length formula. Genuinely
  un-started in Lean; ~Bryce–Goré-scale.

**Honest read:** this is a real, balanced call, not obvious. Wainer has the better base rate (port-not-invent)
but zero progress; Towsner-A′ has a banked lower bound + the right induction machinery but keeps a
(precedented) cut-elim wall + an un-started global embedding (node 5). **This is the decision the operator
should make at the gate** — recommend the verdict lap present *both* B's explicitly rather than pivoting
reflexively to whichever lane happens to be open.

## 5. Recommendation to the gate lap (lap 171)

1. **Write `PIVOT-B`** unless lap 170 finds escape (β) closes *without* becoming the ω-rule. (β) =
   "translate the induction axiom's *use-in-proof* rather than the closed leaf in isolation" — but the
   principled realization of that IS the ω-rule/cut-tower, i.e. the meta route. So (β) succeeding ≈ conceding
   the pivot. Confirm, then write it.
2. **Present the A′-vs-Wainer choice to the operator** with §4's framing. Do not equate "pivot" with "switch
   to the open Codex lane."
3. **Bank the lap-169 shell + this session's (α)-dead finding** as the machine-grounded reason — the leaf
   reduces to exactly `PAInductionStepObligation`, which is unclosable in the finitary calculus.

## 6. Verified in Lean this session (host, branch `plan`, no treadmill running)
- Baseline `wip/M2Probe.lean` typechecks clean (`lake env lean`, exit 0).
- Escape (α) verdict grounded against the live substitution API (`ZDerivation_zsubst` direction, §1).
- (Any lemma added this session is noted in the commit; the reduction of the leaf to the isolated step
  obligation is the target.)
