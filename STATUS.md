# STATUS — goodstein-independence (branch `wainer-lower`) 📊

**Wainer's classification of PA's provably total functions — both halves, sorry-free and
axiom-clean: the upper half on trunk, the lower half here via KT. Wu's Gentzen upper bound.** ·
**Build**: 🟢 green (`lake build GoodsteinWu`, 1371 jobs; full `lake build`, 1548) ·
**Updated**: lap 10 · 2026-09-29 · `d8ed830`

## Where it stands

**COMPLETE.**  All six steps of the route are proved, `GoodsteinWu/` holds **no `sorry`**, and
`#print axioms GoodsteinWu.wainer_classification` is `[propext, Classical.choice, Quot.sound]` —
the trust base, with **zero mathematical axioms**.  `scripts/AxiomCheckWu.lean` pins that with
`#guard_msgs` (silent + exit 0 = clean), and two anti-vacuity anchors in `WainerLower.lean` pin the
produced formula to low values of the hierarchy (`fgFormula 0` = successor, `fgFormula 1` =
doubling).

Steps 1–5 were: conservation of `PA[X]` over `PA`,
the internal fundamental-sequence function `ifd` with its descent and normal-form closure, the Σ₁
graph `fgGraph` of `fastGrowing` on Wu's ordinal codes, progressiveness of `fgTotal` in every model
of `IΣ₁` and then as a `PA[X]`-proof, and the application of `gentzen_upper_bound` yielding
`ApplyTI.peano_fg : 𝗣𝗔 ⊢ isNF ⌜a⌝ → ∀ n, ∃ y, fgGraph ⌜a⌝ n y` for every normal notation `a`.

Step 6, the **ℕ read-off**, closed on lap 10 (`GoodsteinWu/Readoff.lean`): a witness set for
`fgGraph (code o) n y` at the standard model forces `y = ONote.fastGrowing o n`.  It is the one
place well-foundedness is used, and only *externally* — Lean's recursion on `o : ONote` with the
order `ONote.fastGrowing` itself recurses on.  `GoodsteinWu/FgFormula.lean` then assembles the
frozen statement.

## What's happened (newest first)

* **2026-09-29 (lap 10)** — **HEADLINE PROVED.** Review pass confirmed the direction (no repetition,
  no crux-neglect across laps 1–9), then closed step 6: `Readoff.fgStepIn_sound` (the ℕ read-off,
  by Lean-level well-founded recursion on `o : ONote`, no `NF` hypothesis needed) and
  `FgFormula` (the Σ₁ two-place formula, `peano_fgFormula` via completeness, the frozen `↔`).
  `GoodsteinWu.wainer_classification` is sorry-free and axiom-clean. Added
  `scripts/AxiomCheckWu.lean`, two anti-vacuity anchors, `STATUS.md`, `DIRECTION.md`.
* **2026-09-29 (lap 9)** — `ApplyTI.peano_fg`: `gentzen_upper_bound` at `fgTotalCode` and a tower
  notation above `a`, discharged with `concrete_nonote_prec` and brought back to `𝗣𝗔` by
  `Conservation.peano_of_paLX_semantic`. Step 5 closed.
* **2026-09-29 (lap 8)** — `ProgTransfer.concrete_prog : paLX ⊢ progStatement`. Step 4b closed.
* **2026-09-29 (lap 7)** — `Progressive.fgTotal_progressive` (all three cases, incl. the `𝚺₁`
  succ-induction `fgIter`). Step 4 internal half closed.
* **2026-09-29 (lap 6)** — `FastGrowingGraph.fgGraph` + `fgGraphDef`; witnesses are HFS *sets*, so
  `fgWit_union` merges them. Step 3 closed.
* **2026-09-29 (lap 5)** — `InternalFund.isNF_ifdVal`; the `InternalFund` layer owes nothing further.
* **2026-09-29 (lap 4)** — `InternalFund.icmp_ifdVal_lt` — the internal descent `c[n] ≺ c`.
* **2026-09-28 (lap 3)** — `FundBridge.ifd_modelCode`: `ifd` computes mathlib's
  `ONote.fundamentalSequence` on standard codes (validates the transcription).
* **2026-09-28 (lap 2)** — `InternalFund.ifd` arithmetizing `fundamentalSequence` in every `IΣ₁`
  model, `𝚺₁`-defined by a course-of-values table.
* **2026-09-28 (lap 1)** — `Conservation.peano_of_paLX` — the one route ingredient Wu's package
  lacks. Sorry-free, axiom-clean.
* **2026-09-28 (lap 0)** — Branch cut from `v4.34`; `OrdinalAnalysis` port pinned; non-module
  library `GoodsteinWu` created carrying the two frozen statements.

## Outstanding

### Short-term

None. The branch's objective is met.

### Long-term (nothing required; opportunities only)

* `GoodsteinWu` is out of `defaultTargets` (it was carrying the `sorry`); moving it in is now
  possible but needs a lakefile edit, which the brief forbids on this branch.
* The CI axiom-clean gate is commented out in `.github/workflows/ci.yml`; re-enabling it, and adding
  `lake build GoodsteinWu && lake env lean scripts/AxiomCheckWu.lean`, is a trunk-side decision.

### To completion

Done.

## Axiom ledger

| headline theorem | paper claim | `#print axioms` shows | verdict |
| --- | --- | --- | --- |
| `GoodsteinWu.wainer_classification` | unconditional (Wainer) | `propext, Classical.choice, Quot.sound` | ✅ trust base only |
| `GoodsteinWu.fastGrowing_provably_total` | unconditional (Wainer, lower half) | `propext, Classical.choice, Quot.sound` | ✅ trust base only |
| `GoodsteinWu.Readoff.fgGraph_sound` | step 6 | `propext, Classical.choice, Quot.sound` | ✅ trust base only |
| `GoodsteinPA.Wainer.pa_provable_pi2_eventually_witnessed_below_fastGrowing` | unconditional (upper half) | `propext, Classical.choice, Quot.sound` | ✅ trust base only |
| `GoodsteinWu.ApplyTI.peano_fg` | step 5 | `propext, Classical.choice, Quot.sound` | ✅ trust base only |
| `GoodsteinWu.ProgTransfer.concrete_prog` | step 4b | `propext, Classical.choice, Quot.sound` | ✅ trust base only |
| `GoodsteinWu.Conservation.peano_of_paLX` | step 1 | `propext, Classical.choice, Quot.sound` | ✅ trust base only |
| `OrdinalAnalysis.Gentzen.UpperBound.gentzen_upper_bound` | required input (Wu) | `propext, Classical.choice, Quot.sound` | ✅ trust base only |

Math-axiom count (🟢+🟡+🟠): **0**. No 🔴 anywhere. No `sorryAx`. Audit surface:
`scripts/AxiomCheckWu.lean` (this branch) and `scripts/AxiomCheck.lean` (trunk headlines).

## Pointers

`WAINER-LOWER.md` (brief) · `DIRECTION.md` (binding directive) ·
newest `HANDOFF-2026-09-29-*.md` · `PENDING_WORK.md` (live plan)
