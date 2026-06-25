# E — Crux-2 milestone roadmap: the 80–160 behemoth as 4 bounded steps (judge, 2026-06-24)

> Project-management cut of crux-2 (complements `E-CRUX2-DECOMPOSITION-2026-06-24.md`, which is the
> *leaf-math* cut). Each milestone ≤ 40 laps, with a **measurable "done-when"** so progress is observable,
> not asserted. Front-2 (`PA_delta1Definable`) is **already discharged** (Foundation re-pin `e6e1ad1`,
> verified: real 1385-line `InductionSchemeDelta1.lean` instance, no sorry/axiom) — crux-2 is the SOLE
> remaining blocker. State at write time: lap 83, src sorries 3 (all crux-2/headline), descent banked,
> wall = validity + dispatch.

## The four milestones
| # | Milestone | Delivers / clears | Laps | Conf | Parallel? |
|---|---|---|---|---|---|
| **M1** | Genuine reduct `red` + `RedSound` (the nut) | `red` (Buchholz §6 Thm 6.6 / Def 3.2, 5-case primrec) + `RedSound` *proven* via parallel-induction (Thm 6.2 invariant + banked `zKValidFDef`); `RedSound`+descent re-pointed off dead `iR2` | **25–40** | 55% | no |
| **M2** | C0.5 Foundation→Z bridge | `foundation_bot_to_Z_empty : 𝗣𝗔.DerivationOf d ⊥ → ∃ z, ZDerivesEmpty z` (M-internal). Bryce–Goré `Peano.v` blueprint B1–B3: PA axioms→Z atomic; cut→`K^r`, ∀→`I_∀`, **PA-induction→native `Ind` (cheap)**; compose | **15–30** | 65% | **YES (2nd box)** |
| **M3** | Descent assembly → `PA ⊢ (PRWO(ε₀)→Con(PA))` | wire M1+M2+banked ε₀-descent → `gentzen_descent_of_inconsistent` → no-infinite-primrec-descent ⊥ → `ZDerivesEmpty→False` → Con(PA). Clears `DescentSemantic:582`. Leaves: C4 (`isNF`/≠0 of `iord` on ⊥-derivs), C5 (descent as Σ₁ graph; least ⊥-proof via bridge) | **15–30** | 60% | no |
| **M4** | Headline wire-up + axiom-clean cert | discharge `goodstein_implies_consistency` (`Reduction.lean:68`) = crux-1 (γ→PRWO, done) ∘ M3; discharge `peano_not_proves_goodstein` (`Statement.lean:22`) via Gödel II | **5–15** | 70% | no |

## Sequencing
```
M1 ─┐
    ├─► M3 ─► M4
M2 ─┘
```
M1 and M2 are **independent + file-disjoint** (M1 = `InternalZ.lean`/reduct; M2 = a new bridge module + the
Foundation calculus), so **M2 runs in a second box in parallel** (the play that just won front-2 — except
M2 won't get gifted, so actually spin it; `lean-create-worktree` + a scoped treadmill).

- **Parallel (M1‖M2):** ~max(40,30) + 25 + 12 ≈ **75 laps**
- **Serial (one box):** ~40 + 30 + 30 + 15 ≈ **115 laps**
- **+ research tail on M1:** up to ~150

Decomposing **tightens** the prior 80–160 to ~**75–150**; the parallel path is the floor.

## Measurable checkpoints (watch for drift, don't trust "progress")
- **M1 alive:** `red` exists as a 5-case function AND validity is proved *in the same induction* as descent
  (Buchholz parallel-induction). ❌ if a lap is still polishing `iR2` or recovering validity post-hoc.
- **M2 alive:** the PA-induction → Z-`Ind` case lands (the cheap part B–G paid for and we skip).
- **M3 alive:** `DescentSemantic:582` clears.
- **M4 (finish tape):** `#print axioms peano_not_proves_goodstein = [propext, Classical.choice, Quot.sound]`
  (PA_delta1Definable already gifted ⟹ no extra axiom).

## Overrun trigger (the one with real research risk)
**M1 is the only milestone that can blow past 40.** If M1 passes ~40 laps without `RedSound` materializing as
a proven theorem, **stop grinding and reweigh the Route-B / growth-rate pivot** (`E-ROUTE-OPTIONS-2026-06-24.md`)
— that's the pre-agreed decision point, not a vibe. M2/M3/M4 are bounded engineering; M1 is the wall.
