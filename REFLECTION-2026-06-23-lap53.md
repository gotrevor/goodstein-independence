# Reflection — 2026-06-23 (lap 53, DEEP) — route re-validated from source; the honest endpoint named

> Altitude pass on the stronger model. I re-derived the route decision from first principles
> (not from the summaries), re-checked the kernel, read the actual `Hauptsatz` source, and
> stress-tested whether the 8-lap crux-1 grind is fixation. Verdict: **direction KEEP**, with two
> honest re-classifications the grind laps couldn't make from inside the trees. This file is the
> lap's primary deliverable; the STATUS/ledger refresh and PENDING_WORK section implement it.

## Kernel re-verified this lap (real `#print axioms`, build green 1313 jobs)
| theorem | axioms | reading |
|---|---|---|
| `peano_not_proves_goodstein` (headline) | `propext, sorryAx, choice, Quot.sound` | honest `sorry`, **0 math axioms**, anti-fraud intact |
| `goodsteinSentence_faithful` | `propext, choice, Quot.sound` | faithfulness anchor CLEAN |
| `not_proves_of_implies_consistency` / `peano_not_proves_consistency` | `propext, choice, Quot.sound, PA_delta1Definable` | Gödel-II hook carries `PA_delta1Definable` |
| `goodstein_implies_consistency` (the one open girder) | `propext, sorryAx, choice, Quot.sound, PA_delta1Definable` | disclosed `sorry`; **already carries `PA_delta1Definable` through its type** |
| `Thm56.peano_not_proves_TI` (banked monument) | `propext, choice, Quot.sound, native_decide.ax_1_5` | clean; OFF the headline path |

Faithfulness at altitude: traced `Statement.peano_not_proves_goodstein` → `goodsteinSentence :=
“∀ m, ∃ N, !igoodsteinDef 0 m N”` → `goodsteinSentence_faithful` → audited `goodsteinSeq` (`Defs.lean`,
standard Goodstein: `base k = k+2`, hereditary bump, −1). **No transcription drift. The headline means
Kirby–Paris.**

## Finding 1 — the lap-46 route pivot is CORRECT (independently re-derived). Direction KEEP.
The whole current direction rests on lap-45's claim that the free-X route is *structurally* blocked. I
re-derived it from the mathematics, not the summary, and it holds:

- **Goodstein implies PRWO(ε₀), not free-X-TI.** Rathjen Cor 2.7: over PA, Goodstein-terminates ⟺
  PRWO(ε₀) (no *primitive recursive* descending ε₀-sequence). The §3 slow-down (Lemma 3.2 Grzegorczyk
  domination) is **primrec-only** — a free/oracle-X descent is not dominated by any `f_l`, so
  `Goodstein → TI_≺(X)` for a free X genuinely fails (machine-checked `Grz.not_dominated_of_diag_le`).
  This is not "hard," it is the *wrong implication direction*. The pivot away from `peano_not_proves_TI`
  (Thm 5.6, free-X, axiom-clean) was the right call: that monument is a real, banked, publishable result
  (Gentzen 1943 sharpness, `PA ⊬ TI(ε₀)`), but it cannot chain to the headline. **Do not resurrect it as
  the back-end; do not delete it.**
- Therefore Route A (Rathjen Cor 3.7: `γ → PRWO(ε₀) → Con(PA)`, then Gödel II) is the correct, standard,
  textbook route. No course change on the route.

## Finding 2 — name the honest endpoint: the headline best-case is NOT the strict trust base.
Kernel-confirmed this lap: `goodstein_implies_consistency` *already* carries `PA_delta1Definable` through
its type (`↑𝗣𝗔.consistent` forces the `𝗣𝗔.Δ₁` instance, which Foundation supplies as a disclosed
`axiom`). So **the best-case discharged headline on Route A is**

    [propext, Classical.choice, Quot.sound, PA_delta1Definable]

— **not** the strict `[propext, choice, Quot.sound]` that `DIRECTION.md` anti-fraud rule #1 names. This
is *inherent* to using Foundation's Gödel II and cannot be routed around on Route A. It is not a defect
to hide; it is the honest endpoint of the standard route. `PA_delta1Definable` (Δ₁-definability of PA's
axiom set) is a true theorem held as an upstream Foundation `axiom` — the math content of THIS repo does
not include it. **Operator/review reconciliation needed (flagged, not resolved):** either (a) accept
`PA_delta1Definable` as a single disclosed upstream axiom on the headline, or (b) burn it down upstream
(a separate Foundation-side formalization of the induction-scheme arithmetization). My recommendation:
**(a)** — it is a clean, narrow, named, true upstream fact; demanding (b) makes this repo hostage to a
Foundation TODO that is orthogonal to the Goodstein mathematics.

## Finding 3 — the two cruxes have ASYMMETRIC feasibility; classify them honestly.
- **Crux 1 (`γ → PRWO(ε₀)`, Rathjen §3): TRACTABLE — 🟡, the resolvable doubt.** ℕ-template done
  (`Grzegorczyk.lean`, sorry-free), internal Thm 3.5 done (lap 47), Lemma 3.6 done. Internalizing Cor 3.4
  is ~80% built (`BlkRec`/`IIter`/`iF`/`ipsum`/`InternalGrz`, all axiom-clean). Lap-50's key insight —
  the headline composes crux 1 at the *single* primrec instance `gentzenDescentφ`, so Lemma 3.2 gives a
  **STANDARD** Grzegorczyk level, no internal Ackermann — is sound and makes the remaining `ig` assembly
  finitely far (a few laps: `ig` + port `g_NF/g_lt/g_desc/g_C_bound/g_exp` + wire `StdCor34.salpha` +
  resolve the wseq seam + the `icmp`↔`natCode` seam).
- **Crux 2 (`PRWO(ε₀) → Con(PA)`, Gentzen Thm 2.8(i)): GENERATIONAL — 🟠, settled as a cited axiom.**
  Needs the ordinal assignment `ord` + reduction `R` on **arithmetized** PA-derivations, with eq (5)
  `ord(R d) ≺ ord d`, all **inside PA**. I confirmed at the source there is **no shortcut**: Foundation's
  `Hauptsatz.main : ⊢ᵀ Γ → {d // IsCutFree d}` is a *meta-level Lean function* on the `Derivation`
  inductive, NOT a primrec function arithmetized in PA; no arithmetized ordinal analysis exists in
  Foundation or mathlib. The banked Thm-5.6 machinery (`embedC`, cut-elim, boundedness) is *also*
  meta-level/infinitary — it **cannot** be reused for the internal `ord` (JUDGE watch-item #4 is right).
  Building ord/R/eq-5 inside PA is a multi-year formalization in its own right (harder than the ~15-lap
  Thm-5.6 monument, because it must be internal, not meta). The named 🟠 reason: *no arithmetized
  ordinal-analysis of PA exists upstream; eq (5) is Gentzen 1936 (textbook, proven) but unformalized,
  and formalizing it is a research project.* The `wip/GentzenCon.lean` scaffold already isolates it to
  the single `ord_R_descends` axiom and proves the meta-level descent + all three SEAM type-checks — the
  honest crux-2 floor is reached.

**Consequence — the realistic, valuable endpoint of this campaign:** *crux-1 fully built (γ→PRWO
axiom-clean) + crux-2 reduced to the single cited Gentzen fact eq (5) + `PA_delta1Definable` upstream.*
i.e. **"Kirby–Paris formalized end-to-end, modulo Gentzen's reduction-procedure ordinal-descent (eq 5,
cited) and PA's Δ₁-definability (upstream)."** That is a strong, honest, publishable endpoint, and it is
within reach. It is NOT "perpetual motion" and it is NOT a fully axiom-free headline — say so plainly.

## Finding 4 — mild fixation signal, but the immediate target is right (hardest-first, properly applied).
Laps 45–52 (8 laps) grinded crux-1 internal-Grzegorczyk substrate almost exclusively; crux-2 got one lap
(50). One crux-1 lap (49's `icorAlpha`/`iVbigMul` generic-V tower) was explicitly "off-path effort,
banked" — a real over-build. **But** the correct application of *hardest-first* here is subtle: crux-2's
feasibility is already SETTLED (generational → cited eq-5; no doubt left to resolve until someone commits
the multi-year arithmetization). The doubt that is *resolvable this campaign* is crux-1's internalization
— *can* §3 be done inside PA at standard level, cleanly, axiom-free? Driving crux-1 to its `goodstein_
implies_prwo` assembly **is** the hardest-first move among resolvable doubts, and landing it de-risks half
the headline with a concrete, checkable win. So: **KEEP driving crux-1 to assembly.** The lap-52 NEXT
(`ig` + port the g-properties + wire StdCor34) is the right call.

## The call
- **KEEP:** Route A; driving crux-1 `goodstein_implies_prwo` to a clean axiom-free assembly; the
  `wip/GentzenCon.lean` scaffold + SEAM guards; the banked Thm-5.6 monument (do not touch).
- **STOP:** open-ended crux-1 substrate that isn't on the `ig → StdCor34.salpha → InternalThm35 →
  nonterminating_internal → goodstein_implies_prwo` critical path. Every crux-1 brick must answer "does
  this bring the `goodstein_implies_prwo` *body* closer?" (the lap-49 generic-V tower failed that test).
  Do NOT invest further laps in crux-2 beyond the existing scaffold until crux-1 lands — crux-2 is
  cited-generational; chip it only opportunistically.
- **HIGHEST-VALUE NEXT TARGET:** finish crux-1's `goodstein_implies_prwo` — assemble `ig` (internal
  Grzegorczyk `g`, meta-recursion on level over `iF`/`ipsum`/`iblockIdx`), port `g_NF/g_lt/g_desc/
  g_C_bound/g_exp` into the `StdCor34.igt` interface, wire `BlkRec.blk/off` + `igt` through
  `StdCor34.salpha_*` → `InternalThm35.bbeta` → `DescentArith.nonterminating_internal`, then discharge
  the wseq seam (prefix-invariance, `blk_prefix_congr` done) and re-`#print axioms` after the
  `icmp`↔`natCode` seam. Land `γ→PRWO` axiom-clean — that is the campaign's next real milestone.
- **HYGIENE (low priority):** the off-path free-X `DescentSemantic` `sorry` (`:582`) still sits in
  `src/`; it is banked/off-path and a `wip/` candidate. Not urgent, but `src/` should eventually reflect
  only the live route.

## What a sharp outside expert would still ask (open architectural questions, recorded not resolved)
1. **Is there a direct `PA ⊬ PRWO(ε₀)` via boundedness that avoids BOTH Gödel II and the Gentzen
   arithmetization?** The Thm-5.6 boundedness machine produces a *free-X* counterexample; PRWO(ε₀) is a
   Π₂ arithmetic sentence (no free X), so it doesn't directly apply. Likely no — but worth one focused
   think before committing years to crux-2.
2. **Can `PA_delta1Definable` be discharged here cheaply** by formalizing the induction-scheme
   arithmetization and contributing upstream? Probably project-scale, but it's the only non-Gentzen
   residual and might be more tractable than it looks.
