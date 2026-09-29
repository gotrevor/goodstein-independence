# DIRECTION — branch `wainer-lower`

## CURRENT DIRECTIVE  (lap 10, 2026-09-29; altitude laps are the only writers; OUTRANKS the HANDOFF)

**Objective (the only one).**  Discharge the single remaining `sorry`, the frozen
`GoodsteinWu.fastGrowing_provably_total` in `GoodsteinWu/WainerLower.lean`.  Everything the route
needs upstream of it is proved and axiom-clean.

**Mandated next move.**  Step 6 of `PENDING_WORK.md`, in a new file `GoodsteinWu/Readoff.lean`:

1. `fgStepIn_sound : fgWit (V := ℕ) w → ∀ o : ONote, ∀ n y : ℕ,
   fgStepIn (V := ℕ) w (NotationBridge.code o) n y → y = ONote.fastGrowing o n`
   — well-founded recursion on `o` with the `<` that mathlib's `fastGrowing` itself recurses on
   (`fsVal o n < o` holds for *every* `o`, so **no `NF` hypothesis is needed**), `FundBridge.ifd_modelCode`
   to turn each `fgJust` clause into the matching `fundamentalSequence` clause, and an inner
   ordinary `ℕ`-induction along the iteration sequence `u` in the successor clause.
2. Assemble the headline: `φ := Rew.subst ![⌜code o⌝, #1, #0] ▹ fgGraphDef.val`, its
   `Hierarchy 𝚺 1`, the `↔` (→ is 1; ← is free: `ApplyTI.peano_fg` + soundness at ℕ hands back the
   witness, so nothing is built by hand at ℕ), and `𝗣𝗔 ⊢ ∀⁰ ∃⁰ φ` from `peano_fg` by completeness
   plus `NotationBridge.isNF_modelCode` to kill the `isNF ⌜a⌝` guard.

Decompose into named `sorry` leaves in `src` (`GoodsteinWu/`) on the first lap that touches it;
raising the `sorry` count while the leaves shrink is progress.

**Forbidden drift.**
* Do **not** change either frozen statement (`fastGrowing_provably_total`, `wainer_classification`).
* Do **not** add an `axiom`; the route has **zero** math axioms and must keep zero.
* Do **not** build an explicit `fgGraph` witness at ℕ — the `←` half of the frozen `↔` comes for
  free from `peano_fg`; hand-building one is wasted work.
* Do **not** reopen steps 1–5, edit `OrdinalAnalysis`, `lake update`, or push.
* Do **not** park an active-crux `sorry` in `wip/`.

**Why.**  Nine laps closed steps 1–5, each on the critical path, with no repetition and no leaf
drift; step 6 is now the whole remaining obligation, so there is no scaffolding left to hide behind.
It is also the *easiest*-looking of the six and still the crux by definition, because it is the only
thing between a green build and the finished theorem.

### Directive history
* lap 10 (2026-09-29) — set: finish step 6 (the ℕ read-off of `fgGraph`) and assemble the frozen
  headline; steps 1–5 are closed and axiom-clean.

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
* **T-4** — the ℕ read-off needs well-foundedness *inside* PA (not just at ℕ).  *Not fired*: the
  read-off is external, by recursion on `o : ONote` in Lean.  If step 6 ever demands an internal
  well-foundedness principle, T-4 has fired.

**Invariants.** Frozen statements unchanged; zero `axiom`s; no edits to `OrdinalAnalysis`; no
`lake update`; no push; commit every green build; a handoff each lap.
