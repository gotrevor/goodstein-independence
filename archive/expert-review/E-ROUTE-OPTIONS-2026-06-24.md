# E — Route options for "PA ⊬ Goodstein": don't-lose-track ledger (judge, 2026-06-24, ~lap 81)

> **VALIDATE, don't trust.** Source-grounded judge pass over the in-repo `papers/` PDFs (8 read in full,
> 11 more being summarized; each PDF now has a same-basename `.md`). Trigger: the operator's intuition that
> "just before the A/B test a literature search melted the wall — maybe take another look." It did **not**
> melt, but it **relocated**, and the relocation exposed a route the expedition **never costed**. Operator
> constraint (binding): **keep every option tracked** — this file is that ledger. Secondary, *lightly*
> weighed: which byproducts the **Foundation** repo (FormalizedFormalLogic) would appreciate.

## TL;DR
- There are **three** routes to `PA ⊬ Goodstein`. The current one (Rathjen Cor 3.7) is the only one that
  forces **IΣ₁ internalization** — which is the *entire* current pain (`RedSound`, the C0.5 Foundation→Z
  bridge, `PA_delta1Definable`, the parked genuine-reduct redesign).
- The **growth-rate / Wainer route is META-only** — it deletes that whole layer. The ε₀-strength content
  doesn't vanish (it moves into Wainer's classification of PA-provably-total functions), but it moves to a
  setting where **no coded-derivation arithmetization is needed**. Plausibly materially cheaper (~65%).
- **Judge recommendation: STAY internalized for now** — it is further along, has route-agnostic momentum
  (front 2), and yields the more **Foundation-shaped** byproducts. Apply the **Buchholz unblock** (below)
  to restart crux-2. Keep growth-rate as a **fully-documented, costed fallback** with an explicit pivot
  trigger (a *second* crux-2 false-summit).

## The three routes

| Route | Source(s) | Mechanism | Internalized cut-elim (crux-2)? | Net |
|---|---|---|---|---|
| **A. Proof-theoretic (CURRENT)** | Rathjen 2014 Cor 3.7; Buchholz [6]; Freund | PA-internal `Con(PA)` via reduction on **coded** derivations → Gödel II | **YES = crux-2** | the wall we're on |
| **A′. Towsner (Route B)** | Towsner | direct cut-free lower bound (Thm 17.1) instead of Con(PA) | **YES** (his Thm 19.9 cut-elim) + PA↔PA⁺ bridge (Remark 10.3 gap) | **equal-or-harder**; stay on A |
| **B. Growth-rate (META)** | Cichoń 1983; Caicedo; Sladek 2007 | Goodstein-length = Hardy `H_{ε₀}` (exact closed form) → **Wainer**: PA-provably-total ⟹ dominated by `H_{α<ε₀}` → too fast | **NO** | the never-costed lead |
| **C. Model-theoretic** | Kirby–Paris 1982 (original) | nonstandard models + indicators + Ketonen–Solovay | NO | avoids crux-2 but trades for an **equally-absent, arguably-harder** model-theory tower; not recommended |

## Why B is genuinely different (the key insight)
Route A's signature pain exists **only because Cor 3.7 routes through PA-*internal* `Con(PA)`**, which forces
internalizing the Gentzen reduction in IΣ₁ over coded derivations (`RedSound`, the C0.5 bridge, Δ₁-definability).
**`PA ⊬ γ` is itself a meta-statement; Wainer's bound is a meta-theorem.** Route B does **meta-level**
cut-elimination (over ordinary Lean types — *precedented*: Bryce–Goré's Coq Con(PA), ~6–7k lines) to get the
Hardy bound on PA's provably-total functions, then an **elementary** growth comparison (Caicedo's exact
`𝒢(n) = f_{α₁}(…f_{α_k}(3)…) − 2`). **No coded-derivation arithmetization anywhere** — `RedSound`, the bridge,
`PA_delta1Definable`, and Gödel II all *vanish*.

Under the **axiom-free directive**, both A and B must *build* ε₀-strength (Wainer ≈ Gentzen in fast-growing
clothing; neither is free, neither is in mathlib). The trade is: **A = "originate IΣ₁-internalized cut-elim
from scratch"** (currently parked) **vs B = "precedented meta cut-elim + an elementary length formula."**

## Costing (rough; lap rate ≈ 1.5/hr)
| | sunk so far | remaining (axiom-free) | finishability |
|---|---|---|---|
| **A (current)** | crux-1 ✅; Z/ordinal apparatus; front-2 in flight | genuine-reduct redesign + C0.5 bridge (~1k lines) + `PA_delta1Definable` + headline wire | ~80–160 laps, ~40–50% |
| **B (growth-rate)** | reuses existing Goodstein/ε₀ termination work | meta cut-elim of PA_∞ (Bryce–Goré-scale) + Hardy/`H_α` + **Wainer classification** (never in Lean) + Caicedo length formula | comparable scale, **better-factored**; ~50% but lower IΣ₁-friction |

> **B substrate status (Castéran `hydra-battles`, read 2026-06-24).** The Hardy `H_α` + Wainer `F_α`
> hierarchies, ε₀ CNF ordinals, fundamental sequences `{α}(n)`, and the KS81 domination/monotonicity lemmas
> are **fully formalized, constructive, and axiom-free in Coq** — an excellent *blueprint*, but **not
> importable to Lean** and **absent from mathlib**, so B pays a from-scratch (bounded, non-research) Lean
> port of the substrate. The genuinely-new/hard pieces B still owes: **(i)** the Goodstein-length ↔ Hardy
> formula (Castéran has only Hydra battle-length, not Goodstein; `F_α ≈ H_{ω^α}` is left as an exercise),
> and **(ii)** the load-bearing **Wainer *upper* bound** (PA-provably-total ⟹ `H_{<ε₀}`-dominated) = the
> real ε₀-strength wall, meta but Bryce–Goré-scale. Net: B = bounded substrate port + elementary length
> formula + one big meta theorem; the IΣ₁-arithmetization layer (A's pain) stays deleted. See
> `papers/casteran-hydra-battles-in-coq.md`.

## Ecosystem / Foundation lens (lightly weighed, per operator)
- **A's byproducts are Foundation-shaped — the strongest single argument for A.** `PA_delta1Definable` is
  *literally an `axiom` in Foundation today* (`Incompleteness/Examples.lean:17`); discharging it (= front 2,
  in flight now) **removes an axiom from Foundation** — a concrete, mergeable contribution **independent of
  whether the headline ever lands.** A PA-internal Gentzen `Con(PA)` / `PRWO(ε₀)→Con(PA)` would be a Lean
  first and squarely Foundation's domain (it has Gödel II, not Gentzen).
- **B's byproducts are mathlib-shaped**: the fast-growing/Hardy hierarchy + Wainer's classification are
  general proof-theory/ordinals — valuable, but to *mathlib*, not Foundation specifically.
- **Net tilt:** the reusability lens favors **A** (and especially *finishing front 2* regardless of route).

## Route-agnostic unblock — apply NOW (Buchholz, read in full)
The parked genuine-reduct decision is **over-thought**. Buchholz proves **validity (Thm 3.4)** and
**ordinal-descent (Lemma 4.1)** as **two SEPARATE parallel inductions over the same reduct `d↦d[n]`** — so
"ordinal-faithful but not derivation-valid" is a **missing parallel invariant, not a contradiction**. His
**Def 3.2** is a bounded primitive-recursive structural recursion (5 cases; the only search is Lemma 3.1's
least redex pair); **Thm 3.4(b)** *is* the validity (`RedSound`) invariant; the **§7 axiomatic skeleton**
maps `D₁`=validity/RedSound, `D₃`=descent directly onto the IΣ₁ targets. **Port Def 3.2 verbatim and carry
Thm 3.4(b)/§7-`D₁` as the RedSound invariant — do NOT try to recover validity post-hoc from the
ordinal-faithful reduct.** This unblocks crux-2 with no route change. (Details: `papers/buchholz-on-gentzens-first-consistency-proof.md`.)

## Judge recommendation
1. **Stay on Route A.** Further along, route-agnostic momentum, Foundation-shaped byproducts.
2. **Finish front 2 (`PA_delta1Definable`) first** — near-term AND independently valuable (removes a
   Foundation axiom even if the headline stalls).
3. **Restart crux-2 via the Buchholz unblock** (parallel inductions; port Def 3.2; Thm 3.4(b) = RedSound).
4. **Keep Route B alive as costed insurance.** Pivot trigger: *if the genuine-reduct redesign hits a second
   false summit*, switch to meta/growth-rate (Castéran's Coq Hydra has reusable ε₀/Hardy machinery — see
   `papers/casteran-hydra-battles-in-coq.md`).

## Parallelization decision (operator, 2026-06-24) — split the two fronts
The two headline blockers are **independent** (lap-81 HANDOFF) and **file-disjoint** (front 2 writes only
`PADelta1.lean`; crux-2 writes `InternalZ.lean`/`Zsubst.lean`/`FvSubst.lean`; no import coupling). So:
- **Accept `PA_delta1Definable` as the Foundation `axiom` it already is** on the main line — a *tracked,
  actively-discharged* rest-point, NOT a permanent one. This is **consistent with the anti-cop-out
  directive**: the forbidden cop-out is axiomatizing the *ε₀-strength core* (crux-2 / the ordinal analysis);
  `PA_delta1Definable` is a mundane recursion-theoretic fact (PA's induction scheme is Δ₁), it's Foundation's
  own axiom, it's disclosed, and a dedicated box is discharging it — so it **drops at merge** and the
  destination (fully axiom-free) is unchanged. Operator has used this split on other Foundation axioms before.
- **Main box → crux-2** (Buchholz-unblocked); **parallel worktree box → `inductionSchemeUnivDelta1`**
  (`PADelta1.lean:681`). ~2× on the combined timeline, clean merge.

## Validation / how this could be wrong
- B's "materially cheaper" rests on Wainer's classification being more mathlib-tractable than IΣ₁
  internalization. **Wainer has never been formalized in Lean** — it's a Bryce–Goré-scale build; "cheaper"
  could fail to hold. (~65% it's net easier.)
- If a future operator wants the **PA-internal `Con(PA)`** artifact for its own sake (it's the more famous
  byproduct), A wins regardless of B's tractability.
- The Foundation tilt is *lightly* weighed by directive; do not let it override a large tractability gap if
  one emerges.
- `papers/agboola-termite-and-tower-goodstein.pdf` is **mislabeled** — it is Sladek (2007), not Agboola
  (flagged in its summary; rename if provenance matters).

## Pointers
- Route summaries: `papers/{rathjen-2014,cichon-1983,kirby-paris-1982,towsner,caicedo,freund-unprovability,agboola(=Sladek),buchholz-on-gentzens}*.md`.
- Prior judge findings: `E-EQ5-ROUTE-FINDING-2026-06-23.md` (Bryce–Goré feasibility), `E-CRUX2-DECOMPOSITION-2026-06-24.md` (leaf punch-list), `JUDGE-HANDOFF.md` (baton).
