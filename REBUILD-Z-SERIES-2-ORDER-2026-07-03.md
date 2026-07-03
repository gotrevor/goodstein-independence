# REBUILD-Z — SERIES-2 ORDER: statements + amendment probes (architect, 2026-07-03) 🔒

> **Binding.** Issued with `E-2026-07-03-JUDGE-series1-validation.md` (Series-1 PASS, qualified).
> This is a **small, judged statement/probe series** — NOT a batched grind. Its whole purpose is
> to produce the kernel evidence for the two reserved amendment rulings (top-rank-cut trilemma;
> Ax2 vs restatement for rungs D+E), plus to clear the Series-1 Stage-1 debt. Expected 2–4 laps.
> The safety invariant is unchanged: statements below are given verbatim where ratified;
> everything probe-shaped is **wip-only**; self-ratification VOID. **No grind on the top-rank
> cut or `readoffD_trapped` in this series — they are reserved for the post-ruling grind series.**

Maintain `REBUILD-Z-SERIES-2-LEDGER.md` (append-only, one block per stage, same discipline —
and per the Series-1 ruling §5.2: **hygiene claims must be diff-verified**, never asserted from
memory). Gate every stage with the **bare `lake build`** (1341-job full gate; `lake build
GoodsteinPA` is known-insufficient for Route-B edits).

## Stage A — Series-1 Stage-1 debt (src, pre-ratified, mechanical)

- **(A-1) Create `src/GoodsteinPA/WainerLadder.lean`** (imports `OperatorZef2` + the translation
  apparatus per ruling §4 L-E direction; wire into the blueprint lib root + `mk_all`).
- **(A-2) Move + restate `wainer_splice_Zef2`** there, VERBATIM per the Series-1 order R-5 block:

  ```lean
  theorem wainer_splice_Zef2 :
      (𝗣𝗔 ⊢ ↑goodsteinSentence) →
        ∃ o : ONote, o.NF ∧
          EventuallyLE GoodsteinPA.Dom.goodsteinLength (fun n => fastGrowing o n)
  ```

  Body `sorry`; docstring: rung W, consumes E/R/D + the Hardy Lemma-19 brackets. DELETE the old
  parametric form from `OperatorZef2.lean` (it is the lap-8-ruling VOIDed-as-trivial L-W shape).
- **(A-3) DELETE `embedding_Zef2`** from `OperatorZef2.lean` (the lap-8 ruling §4 VOIDed
  placeholder — R-6 debt). Docstring TODO in `WainerLadder.lean` naming rung E's statement lap.
- **(A-4) Blueprint**: `thm:zeh_rank_zero` → `\lean{rankToZero_Zef2}` (drop `\notready` — it is
  proven modulo the pass; keep it OFF `\leanok` until the pass lands); `thm:wainer_splice` →
  `\lean{wainer_splice_Zef2}`; `blueprint_audit` must pass; reconciler rerun.
- **(A-5) Trash the stale `wip/Lap13ReadoffDeltaProbe.lean`** (name-clash with promoted `sound0`)
  or fix its imports; wip-only, either is fine.

## Stage B — rung-E statement lap (the Ax2-adequacy probe; wip-first, then ONE src statement)

The lap-8 ruling's mandated pre-probe, now doubly motivated (it gates rung E AND lane D's
route A). **Wip-only until the judge rules**:

- **(B-1) `wip/Ax2AdequacyProbe.lean`**: clone the `Zef2` inductive as `Zef2T` = `Zef2` + the
  E–W (Ax2) true-literal rule (`trueRel`/`trueNrel` mirroring `Zekd`, `OperatorZinfty.lean:51/53`).
  Kernel-answer, in order:
  (i) does `toZef` extend to `Zef2T` (the two read-off templates: Zef read-off
  `OperatorZeh.lean:1801`ff, Zekd read-off `:377`ff) — or characterize the exact breakage;
  (ii) do pins 1–2 re-prove over `Zef2T` (the new constructors add cases to the
  `cutReduceAllAuxRunning` induction — measure the delta against the proven Series-1 templates);
  (iii) the lap-195 sharpening check: confirm the Lemma-31-style read-off over `Zef2T` (top-`∃`
  extraction at slot `f`, matrix truth via `sound0`, NO `allω` descent) closes the
  `readoffD_trapped` shape — a miniature suffices (rank 0, one trapped `allω` node).
- **(B-2) Rung-E statement draft** (text only, in the probe file docstring — NOT src): the
  W3-ratified K-hypothesis shape re-based onto `Zef2` (or `Zef2T` per (B-1)), source hypothesis
  `hpa : 𝗣𝗔 ⊢ ↑goodsteinSentence`, `Γ_G` bound to the CONCRETE goodstein translation, homed in
  `WainerLadder.lean`. The judge ratifies the text before it touches src.

## Stage C — lane-D Option-B feasibility (wip-only)

- **(C-1)** Kernel-check whether the splice consumer closes with the **achievable** bound: does
  `wainer_splice_Zef2` (A-2 form) go through if rung D concludes `∃ n ≤ ewIter f α 0` instead of
  `∃ n ≤ f 0`? (The lap-195 handoff notes the splice already speaks `ewIter … α 0`.) If YES,
  draft the R-4′ restatement text (docstring, wip) — it may dodge (Ax2) for the headline path
  entirely, with `readoffD_trapped_of_mono` covering the goodstein-shaped fragment.
- **(C-2)** Confirm the goodstein matrix's bounded-∀ step clauses satisfy the
  `readoffD_trapped_of_mono` guard condition (`atomTrue (χ/[nm 0]) → atomTrue (∀⁰ χ)`) on the
  CONCRETE translation — a `native_decide`-free kernel example, wip.

## Stage D — top-rank-cut trilemma probes (wip-only)

- **(D-1) Absorbing-norm existence**: is there a norm `N` on ONote with (i) finite fibers
  (T-Z7(i)'s requirement) and (ii) `N(α+γ) ≤ max (N α) (N γ) + O(1)`? Probe candidates (e.g.
  CNF-depth × max-coefficient hybrids) and kernel-check the two properties on small cases; if a
  candidate survives, check the node gate `N(α+γ) ≤ g(f 0)` closes from `N α ≤ g 0`, `N γ ≤ f 0`
  WITHOUT `hg_base`. A refutation ("finite fibers force additivity-like growth") is equally
  valuable — state it as a concrete failing family, kernel-checked.
- **(D-2) Shift-relativization cost assessment**: define `rel1' f n = fun m => f (n + m)` (the
  E–W-literal `f[n]`) beside `rel1` in wip; kernel-check it preserves `hg_base` AND the
  `2m+1` floor AND Monotone/infl; then measure the blast radius — which Series-1-ratified
  statements mention `rel1` (the pins' `fam` hypotheses do), and does the `allω` constructor
  bind `rel1` or take the slot as data? Deliverable: a precise, kernel-grounded amendment cost
  (what re-proves mechanically vs what needs new mathematics).

## Gates (every stage)

Bare `lake build` 🟢 (1341) · headline quadruple UNDRIFTED · `lean-sorry src/` delta = exactly
{−2 stale voided sorries (A-2/A-3), +1 restated `wainer_splice_Zef2`} = **17** expected end-state ·
NO new `axiom` in src · NO `native_decide` in new files · wip freeze references untouched ·
`blueprint_audit` passes · ledger per stage. **Series end: STOP for the judge** — the two
amendment rulings follow from B/C/D evidence, then the post-ruling grind series (Series 3) gets
its order.

## FORBIDDEN

Grinding `passAux` top-rank cut or `readoffD_trapped` **in src** (reserved for the post-ruling
grind series — but wip-probe advances on both are SANCTIONED, ladder P4 below). Adding (Ax2) to
the src `Zef2` (probe clones only). Any `rel1` change in src. Statement text beyond the blocks
above (rung-E draft stays in wip until ratified). Self-ratification (VOID). Un-diff-verified
ledger claims. Route-A / `Zf`-era sorries (`Crux2Blueprint` ×12, `DescentSemantic`,
`OperatorZeh:1925` old pin 3) stay FROZEN per the operator route decision — they are superseded
surfaces, not open theorems; laps spent there are not productive work.

## PRODUCTIVITY LADDER (operator directive 2026-07-03: 10 productive hours; walk DOWN on blocks)

Work the highest rung that offers in-scope work; a wall (recorded escalation/probe) on one rung
is the license to move down, not to idle. Every lap must bank something kernel-checked.

- **P1** — Stage A (mechanical debt). Always available; do it first.
- **P2** — Stages B, C, D (the probe evidence — the high-value core). Lanes are independent:
  blocked in B ⇒ move to C or D, and vice versa.
- **P3** — Probe DEEPENING (after B–D's first passes): (i) B-1(iii) at increasing fidelity —
  grow the Lemma-31-style read-off miniature over `Zef2T` toward the full `readoffD_trapped`
  shape; (ii) D-2 extended — actually RE-PROVE pins 1–2 over `rel1'` in the wip clone (measure
  the amendment cost by construction, not estimation); (iii) D-1 candidate-family sweeps;
  (iv) C-1 → a full feasibility proof draft of the splice against the `ewIter f α 0` bound.
- **P4** — every-open-theorem fallback (wip-only where gated): advance the TOP-RANK CUT inside
  the wip amendment clones (does the cut case close over `rel1'`? over an absorbing-norm
  candidate? — each answer directly feeds the reserved ruling) and `readoffD_trapped` via the
  `Zef2T` (Ax2) mechanism. Never src, never self-ratified — these are ruling inputs, and they ARE
  productive work.
- **P5** — lap-TAIL only (never a whole lap): ledger/docstring/blueprint hygiene.

## STOP RULE (do not burn tokens idling)

"Productive" = a rung of the ladder offers work whose result the series-end judge will consume
(a statement executed, a probe answered, a cost measured, an escalation sharpened). When NO rung
does — every stage landed-or-escalated, probes answered to ruling grade, fallbacks exhausted —
**self-stop green** (`done --green`; the host verifies the full gate) with the ledger's final
block naming what was exhausted. Do NOT pad laps with hygiene, re-verification theater, or
Route-A archaeology. An early honest stop is a good outcome; an idle lap is not.

## Fire shape (operator)

One fire, `--max-laps 8 --max-duration 10h --review-every 3 --allow-stop` (statement/probe laps
are cheap and historically run true to estimate; the ladder fills 10h only if the evidence is
flowing). Even the all-refutation branch hands the judge everything needed to rule both
amendments.
