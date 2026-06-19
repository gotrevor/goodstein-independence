# Expedition plan — Goodstein independence over PA

Formalize **Kirby–Paris (1982)**: `𝐏𝐀 ⊬ γ`, where `γ` ≈ "∀ m, the Goodstein sequence from m
reaches 0," expressed as a first-order sentence of arithmetic.

## TL;DR verdict
**Not overnight, and not a solo autonomous-treadmill job.** Termination built in one lap because
*every* lemma was already in mathlib — the lap only had to assemble. Independence is the
opposite: its load-bearing theorem (the **ordinal analysis of PA**) exists in **no** Lean
library and must be *originated*. A lap assembles; it cannot originate a major body of proof
theory in a night, and if pushed it will either spin or emit a vacuous/axiom-smuggling "proof."
This is a research milestone, executed in phases, with a human architect.

## Library landscape (scouted 2026-06-18)

| Piece | Status | Where |
|---|---|---|
| Goodstein terminates (positive thm) | ✅ done, axiom-clean | `~/src/lean-formalizations` `Logic/Goodstein` |
| ε₀ + ordinal arithmetic / well-foundedness | ✅ in mathlib | `SetTheory/Ordinal/Veblen`, `…/Basic` |
| First-order logic, PA via `ISigma` schemata, models | ✅ | `FormalizedFormalLogic/Foundation` (mathlib @ v4.29.0) |
| Arithmetization / Σ₁ sequence-coding (to *encode* Goodstein) | ✅ | FFL `arithmetization` (`ISigmaOne/Zero`) |
| Gödel I, cut-elim (Hauptsatz), Gödel–Gentzen translation | ✅ | `Foundation` |
| Gödel II (`PA ⊬ Con(PA)`), D1/D2/D3, `Con[·]` | ✅ (confirm toolchain — see 0.1) | FFL `Incompleteness` (Arith/Second.lean) |
| **Ordinal analysis of PA: `TI(ε₀) ⊢ Con(PA)`** | ❌ **missing everywhere** | — |
| **`Goodstein ⟹ TI(ε₀)`** | ❌ **missing everywhere** | — |
| Fast-growing / Hardy hierarchy `H_α` (α<ε₀) + PA-provably-total characterization | ❌ missing (mathlib "fastGrowing" hit = ordinal *Notation*, red herring) | — |

## The math: two routes to the same wall

**Route A — Gentzen / ordinal analysis (standard).**
`Goodstein ⟹ TI(ε₀)` (the descent in Goodstein's proof *is* a transfinite-induction-to-ε₀
instance) `⟹ Con(PA)` (Gentzen: `TI(ε₀) ⊢ Con(PA)`). Then Gödel II (`PA ⊬ Con(PA)`) gives
`PA ⊬ Goodstein`. Reuses the existing Gödel II directly. The cost is `TI(ε₀) ⊢ Con(PA)`:
an infinitary calculus `PA_∞` (ω-rule), ordinal assignment `< ε₀` to derivations, and
cut-elimination bounded by ε₀. **This is the missing girder.** (Foundation's Hauptsatz is the
*finitary* FO cut-elim — necessary background, not the ε₀-bounded arithmetic version.)

**Route B — Hardy/fast-growing domination (Kirby–Paris combinatorial).**
The Goodstein length `G(n)` grows like `H_{ε₀}`. Every PA-provably-total function is dominated by
some `H_α`, α<ε₀. `H_{ε₀}` outgrows all of them ⟹ `G` is not PA-provably-total ⟹ `PA ⊬` "G is
total" = γ. Cost: build the `H_α` hierarchy + the (deep) characterization of PA's
provably-total functions. The characterization itself needs ordinal analysis, so Route B doesn't
dodge the girder — but it offers crisp, checkable *milestones* (e.g. "G dominates Ackermann",
"G dominates F₃") that Route A lacks.

**Recommendation:** Route A as the spine (reuses Gödel II + our termination work), with Route B's
growth lemmas as morale-building, independently-valuable side milestones.

## Phases

### Phase 0 — Statement & scaffolding  (bounded; the near-term piece)
0.1 **Build resolution.** New Lean project, v4.29.x, depending on `Foundation` (transitively
   mathlib). Confirm where Gödel II currently lives and on which toolchain (Foundation v4.29.0
   vs the standalone `Incompleteness` v4.16.0-rc2) and pin accordingly. Get it compiling on a
   **networked host** — ⚠️ the isolated lean-yolo box CANNOT fetch FFL (egress allowlist =
   anthropic only); see Execution model.
0.2 **Encode `γ`.** Define the Goodstein step relation as a Δ₀/Σ₁ formula over ℒₒᵣ using FFL's
   sequence-coding; `γ` := the Π₂ sentence "∀ m ∃ N, sequence from m is 0 at step N."
0.3 **Faithfulness bridge (anti-vacuity certificate).** Prove `(ℕ ⊨ γ) ↔ goodstein_terminates`
   — tie the *syntactic* sentence's standard-model truth to our mathlib theorem. This is the
   analog of the termination repo's `native_decide` anchors: it makes a wrong encoding
   impossible to pass off as right. **The whole value of Phase 0 lives here** — a `sorry`'d
   `𝐏𝐀 ⊬ γ` against an unfaithful `γ` is worthless.
0.4 **State the target:** `theorem pa_not_proves_goodstein : 𝐏𝐀 ⊬ γ := by sorry`.
   Deliverable: a faithful, formally-stated open conjecture (citable; the shape `formal-conjectures` collects).

### Phase 1 — Gödel II hook
Surface `Con(𝐏𝐀)` and `𝐏𝐀 ⊬ Con(𝐏𝐀)` from FFL in usable form; prove the meta-reduction
"`𝐏𝐀 ⊢ γ → 𝐏𝐀 ⊢ Con(𝐏𝐀)`" *as a target* so the whole theorem collapses to one implication
(`γ ⟹ Con(PA)` inside PA). After this, only Phase 2–3 remain.

### Phase 2 — The ordinal-analysis girder  (flagship core; months)
Formalize `TI(ε₀) ⊢ Con(𝐏𝐀)`: infinitary `PA_∞`, ordinal assignment `< ε₀`, ε₀-bounded
cut-elimination. Human-architected; likely a standalone mathlib-scale contribution. **Not
autonomous-treadmill work** — this is originating substrate, not assembling it.

### Phase 3 — `Goodstein ⟹ TI(ε₀)`
The reduction inside PA. **Big reuse:** our `Engine.lean` already maps Goodstein states to
ordinals `< ε₀` and concludes by well-foundedness — that is the *model-side* of TI(ε₀). Phase 3
re-expresses that descent syntactically. The termination work is the seed, not waste.

### Phase 4 — Assemble
`γ ⟹ TI(ε₀) ⟹ Con(𝐏𝐀)`, then Gödel II ⟹ `𝐏𝐀 ⊬ γ`. Discharge the Phase 0 `sorry`.
`#print axioms` must stay clean.

## Execution model (important, differs from the termination treadmill)
- The lean-yolo box is **network-isolated**; it cannot `lake`-fetch `Foundation`/mathlib from
  GitHub. So this expedition is **not** drop-in treadmill-able. Options: (a) a **networked host**
  dev loop (Claude Code on the host, no box) for Phases 0–1; (b) **vendor** FFL + a prebuilt
  mathlib cache into a box image to treadmill bounded sub-lemmas later.
- Phases 0–1 are bounded → feasible with focused host sessions (and *parts* could be scoped for a
  vendored-box treadmill once it builds). Phase 2 is research, human-led. Phases 3–4 reuse +
  assemble.

## Calibration note (learned the hard way, 2026-06-18)
**No lap-count or wall-clock prediction here.** My termination estimate was a ~10× overshoot and
I then misread a cumulative log to fake a "hit." So: Phase 0 is "bounded, days-to-weeks, the
faithful encoding + bridge is the real work"; Phase 2 is "the months-to-year frontier piece."
Numbers get attached only *after* a phase lands, against authoritative timestamps.

## Open questions to resolve first (Phase 0.1)
1. Gödel II current home + toolchain: is `PA ⊬ Con(PA)` in `Foundation` @ v4.29.0, or only in the
   older `Incompleteness` @ v4.16.0-rc2? (Decides the project toolchain + whether one project can
   hold both the ε₀ work and Gödel II.)
2. Does FFL's PA (`𝐏𝐀` / `ISigma` schemata) match the standard PA Kirby–Paris uses, and is its
   `Con` the one Gödel II is proven about?
3. Cleanest sequence-coding API in `arithmetization` for the Π₂ encoding of `γ`.
