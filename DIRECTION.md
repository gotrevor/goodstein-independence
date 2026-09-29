# DIRECTION — branch `wainer-lower`

## CURRENT DIRECTIVE  (lap 10, 2026-09-29; altitude laps are the only writers; OUTRANKS the HANDOFF)

**OBJECTIVE MET — branch complete; STOP taken.**  `GoodsteinWu.fastGrowing_provably_total` and
`GoodsteinWu.wainer_classification` are proved, sorry-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`, zero mathematical axioms).  `GoodsteinWu/` holds no
`sorry`; `lake build GoodsteinWu` is green (1371 jobs) and the full `lake build` is green (1548).

**Mandated next move.**  *None on this branch.*  Any further work here must be requested
explicitly; do not invent side quests.  If resumed, the only legitimate items are the two
non-mathematical ones listed under "Long-term" in `STATUS.md` (moving `GoodsteinWu` into
`defaultTargets`, re-enabling the CI axiom gate), **both of which need permission** because they
touch the lakefile / CI, which this brief forbids.

**Forbidden drift.**
* Do **not** change either frozen statement.
* Do **not** add an `axiom`, edit `OrdinalAnalysis`, `lake update`, or push.
* Do **not** "improve" the finished proofs by relocating or re-deriving them.

**Why.**  The objective was scoped to exactly one target (`sorry-free:GoodsteinWu/WainerLower.lean`)
and it is met and audited (`scripts/AxiomCheckWu.lean`, silent + exit 0).  The two anti-vacuity
anchors in `WainerLower.lean` pin the produced formula to `fastGrowing 0 = succ` and
`fastGrowing 1 = 2·n`, so the statement is not hollow.

### Directive history
* lap 10 (2026-09-29) — set: finish step 6 (the ℕ read-off of `fgGraph`) and assemble the frozen
  headline; steps 1–5 are closed and axiom-clean.
* lap 10 (2026-09-29, same lap, after the work) — **MET**: step 6 closed, headline proved
  axiom-clean, audit added, STOP taken. No further mandated work on this branch.

---

## Standing charter

**Destination.**  `GoodsteinWu.wainer_classification`: the PA-provably total functions are exactly
those eventually dominated by `ONote.fastGrowing o` for some `o < ε₀`.  The upper half is proved on
the trunk (`GoodsteinPA.Wainer.pa_provable_pi2_eventually_witnessed_below_fastGrowing`); this branch
owes only the lower half.

**Route.**  Six steps, fixed at lap 2 and unchanged since; see `PENDING_WORK.md` for the live list
and `WAINER-LOWER.md` for the brief.  The required external input is
`OrdinalAnalysis.Gentzen.UpperBound.gentzen_upper_bound` (Wu), used as a black box.

**Route-level abort conditions** (a FIRED trigger means write `ROUTE-ESCALATION-<date>.md`, not
"direction kept"):

* **T-1** — `gentzen_upper_bound`'s statement turns out not to give transfinite induction for an
  arbitrary `LX`-formula up to every notation below ε₀.  *Not fired* (read and applied at lap 9).
* **T-2** — conservation of `PA[X]` over `PA` fails for `X`-free sentences.  *Not fired* (proved,
  lap 1).
* **T-3** — `fgGraph` is not Σ₁, or its witness sets do not merge, forcing a reindexing calculus
  inside PA.  *Not fired* (`fgGraphDef` is `mkSigma`; `fgWit_union`, lap 6).
* **T-4** — the ℕ read-off needs well-foundedness *inside* PA (not just at ℕ).  *Not fired, and now
  settled*: `Readoff.fgStepIn_sound` is external, by Lean's recursion on `o : ONote`; no internal
  well-foundedness principle was needed anywhere.

**Invariants.** Frozen statements unchanged; zero `axiom`s; no edits to `OrdinalAnalysis`; no
`lake update`; no push; commit every green build; a handoff each lap.
