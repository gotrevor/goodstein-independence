# STATUS — goodstein-independence (branch `wainer-lower`) 📊

**Wainer's classification of PA's provably total functions: upper half already proved on trunk,
lower half being proved here via KT. Wu's Gentzen upper bound.** ·
**Build**: 🟢 green (`lake build GoodsteinWu`, 1369 jobs) · **Updated**: lap 10 · 2026-09-29 · `91c3c91`

## Where it stands

Steps 1–5 of the six-step route are **complete and sorry-free**: conservation of `PA[X]` over `PA`,
the internal fundamental-sequence function `ifd` with its descent and normal-form closure, the Σ₁
graph `fgGraph` of `fastGrowing` on Wu's ordinal codes, progressiveness of `fgTotal` in every model
of `IΣ₁` and then as a `PA[X]`-proof, and the application of `gentzen_upper_bound` yielding
`ApplyTI.peano_fg : 𝗣𝗔 ⊢ isNF ⌜a⌝ → ∀ n, ∃ y, fgGraph ⌜a⌝ n y` for every normal notation `a`.

**One `sorry` remains in the whole library** — the frozen headline
`GoodsteinWu.fastGrowing_provably_total` (`GoodsteinWu/WainerLower.lean:33`). It is step 6, the
**ℕ read-off**: that a witness set for `fgGraph (code o) n y` at the standard model forces
`y = ONote.fastGrowing o n`. Every other declaration in `GoodsteinWu/` is
`[propext, Classical.choice, Quot.sound]`-clean; there are **zero math axioms** anywhere on the
route, and none are planned.

## What's happened (newest first)

* **2026-09-29 (lap 10, review)** — Course-correction pass: direction confirmed, no repetition and
  no crux-neglect across laps 1–9 (each closed a distinct step on the critical path). STATUS.md and
  DIRECTION.md created; the remaining work is exactly step 6 and it *is* the crux.
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

### Short-term (mirror PENDING_WORK top)

1. **Step 6, the ℕ read-off — the crux.** `GoodsteinWu/Readoff.lean`:
   `fgStepIn_sound`, by well-founded recursion on `o : ONote` (`fsVal o n < o`, no NF needed),
   with an inner `ℕ`-induction along the iteration sequence in the successor clause.
2. **Assemble the headline.** `φ := Rew.subst ![⌜code o⌝, #1, #0] ▹ fgGraphDef.val`; its
   `Hierarchy 𝚺 1`; the `↔` (forward = step 6, backward free from `peano_fg` at ℕ + step 6); and
   `𝗣𝗔 ⊢ ∀⁰ ∃⁰ φ` from `peano_fg` by completeness plus `isNF_modelCode`.

### Long-term

Nothing after step 6: `wainer_classification` is already assembled from the two halves and needs no
further input.

### To completion

Step 6 plus the assembly. One to three laps.

## Axiom ledger

| headline theorem | paper claim | `#print axioms` shows | verdict |
| --- | --- | --- | --- |
| `GoodsteinWu.fastGrowing_provably_total` | unconditional (Wainer, lower half) | `propext, sorryAx, Classical.choice, Quot.sound` | one open `sorry` = step 6; **0 math axioms** |
| `GoodsteinWu.wainer_classification` | unconditional (Wainer) | `propext, sorryAx, Classical.choice, Quot.sound` | inherits only the above `sorry`; **0 math axioms** |
| `GoodsteinPA.Wainer.pa_provable_pi2_eventually_witnessed_below_fastGrowing` | unconditional (upper half) | `propext, Classical.choice, Quot.sound` | ✅ trust base only |
| `GoodsteinWu.ApplyTI.peano_fg` | step 5 | `propext, Classical.choice, Quot.sound` | ✅ trust base only |
| `GoodsteinWu.ProgTransfer.concrete_prog` | step 4b | `propext, Classical.choice, Quot.sound` | ✅ trust base only |
| `GoodsteinWu.Conservation.peano_of_paLX` | step 1 | `propext, Classical.choice, Quot.sound` | ✅ trust base only |
| `OrdinalAnalysis.Gentzen.UpperBound.gentzen_upper_bound` | required input (Wu) | `propext, Classical.choice, Quot.sound` | ✅ trust base only |

Math-axiom count (🟢+🟡+🟠): **0**. No 🔴 anywhere. `sorryAx` on the two headlines is the single
open obligation, not a cited axiom.

## Pointers

`WAINER-LOWER.md` (brief) · `DIRECTION.md` (binding directive) ·
newest `HANDOFF-2026-09-29-*.md` · `PENDING_WORK.md` (live plan)
