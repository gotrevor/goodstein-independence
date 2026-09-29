# HANDOFF 2026-09-29 — WAINER-LOWER **COMPLETE** (laps 1–10)

Branch `wainer-lower`.  Working tree clean.
`lake build GoodsteinWu` 🟢 green (1371 jobs) · full `lake build` 🟢 green (1548 jobs).

## Result

Both frozen statements in `GoodsteinWu/WainerLower.lean` are **proved, sorry-free, axiom-clean**:

```
#print axioms GoodsteinWu.fastGrowing_provably_total  -- [propext, Classical.choice, Quot.sound]
#print axioms GoodsteinWu.wainer_classification       -- [propext, Classical.choice, Quot.sound]
```

Zero mathematical axioms anywhere on the route.  `grep -rn sorry GoodsteinWu/` is empty.
Audit surface: `scripts/AxiomCheckWu.lean` — `#guard_msgs`-pinned, silent + exit 0 when clean:

```
lake build GoodsteinWu && lake env lean scripts/AxiomCheckWu.lean
```

`GoodsteinWu.wainer_classification` is the full classification: PA's provably total functions are
exactly those eventually dominated by `ONote.fastGrowing o` for some `o < ε₀` — upper half from the
trunk (`GoodsteinPA.Wainer.pa_provable_pi2_eventually_witnessed_below_fastGrowing`), lower half from
this branch, both axiom-clean.

## What lap 10 added

`GoodsteinWu/Readoff.lean` (step 6, the crux) — the ℕ read-off.
`fgStepIn_sound : fgWit (V := ℕ) w → fgStepIn w (code o) n y → y = ONote.fastGrowing o n`.

The one thing the plan got wrong, and it made the proof *shorter*: **no `NF` hypothesis and no
internal `icmp`/`isNF` reasoning is needed here at all.**  The plan expected the descent to come
from `icmp_ifdVal_lt` + `isNF_ifdVal` (laps 4–5, which are `isNF`-gated).  In fact the recursion is
Lean's own, on `o : ONote` with `InvImage.wf ONote.repr Ordinal.lt_wf` — the very order
`ONote.fastGrowing` recurses on — and `fsVal o n < o` falls straight out of mathlib's
`fundamentalSequence_has_prop` for *every* `o`: `o.repr = succ (fsVal o 0).repr` in the successor
case, `(h.2.1 n).2.1` in the limit case.  So laps 4–5 are load-bearing for step 4 (progressiveness
*inside* PA, where `precCode` carries `isNF`) and not for step 6.  `FundBridge.ifd_modelCode`
converts each `fgJust` clause into the matching `fundamentalSequence` clause; the successor clause
closes with an ordinary ℕ-induction giving `znth u j = (fastGrowing (fsVal o 0))^[j] n`.

`GoodsteinWu/FgFormula.lean` — the assembly.

* `fgSem o := fgGraphDef.rew (Rew.subst ![⌜code o⌝, #1, #0])` and `fgFormula o := (fgSem o).val`.
  Substituting at the `𝚺₁.Semisentence` level rather than on the raw formula means Σ₁-ness is
  `(fgSem o).sigma_prop` — no hand-rolled `Hierarchy` proof.
* `exists_fgGraph` — in an arbitrary model of `𝗣𝗔`, `ApplyTI.peano_fg` plus
  `NotationBridge.isNF_modelCode` (to kill the `isNF ⌜o⌝` guard) gives `∀ n, ∃ y, fgGraph ⌜o⌝ n y`.
  Needs `have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (T := 𝗜𝚺₁) (U := 𝗣𝗔) inferInstance`.
* `peano_fgFormula` — `FirstOrder.Arithmetic.complete.{0} 𝗣𝗔` on that.
* `eval_fgFormula_nat` — the frozen `↔`.  The `←` direction builds **no** witness set at ℕ: it is
  the ℕ-instance of the `𝗣𝗔`-proof, with `Readoff.fgGraph_sound` naming its value.

Anti-vacuity anchors in `WainerLower.lean`: `fgFormula 0` reads as successor, `fgFormula 1` as
doubling, both through `eval_fgFormula_nat` and mathlib's `fastGrowing_zero`/`fastGrowing_one`.

Docs: `STATUS.md` and `DIRECTION.md` created on the lap-10 review pass; `PENDING_WORK.md` closed out.

## Idiom notes worth keeping

* The `∀⁰`/`∃⁰` prefixes are g-i's (`GoodsteinPA/ToFoundation/Compat.lean`); files that do not import
  `GoodsteinPA` must write upstream's `∀¹`/`∃¹` — same constants, so the frozen statement's
  `∀⁰ ∃⁰ φ` and a lemma's `∀¹ ∃¹ φ` are literally the same term.
* `Bounding.HierarchySymbol.Semiformula.val_rew` must be written out in full: bare
  `Semiformula.val_rew` is ambiguous once `FFL.FirstOrder.Bounding.HierarchySymbol` is opened.
* `rcases ho : o.fundamentalSequence with ...` rewrites the *goal*, not just hypotheses — the branch
  goal is already in terms of the constructor, so the follow-up is `rfl`, not `exact ho`.
* `rw [ONote.fastGrowing_limit o hf]` leaves an unreduced beta-redex; use `simp only [...]` when the
  next rewrite has to see through it.
* `modelCode (V := ℕ) o` is `((code o : ℕ) : ℕ)`; `simpa [modelCode]` (i.e. `Nat.cast_id`) is what
  bridges it to `code o`.

## Anything left?

Nothing mathematical.  Two housekeeping items, both **blocked by this brief** and therefore left
alone (see `STATUS.md` → Outstanding → Long-term):

1. `GoodsteinWu` is still out of `defaultTargets` (it was excluded while it carried the `sorry`).
   Moving it in needs a lakefile edit, which the brief forbids.
2. The CI axiom-clean gate in `.github/workflows/ci.yml` is commented out.  Re-enabling it and
   adding `lake build GoodsteinWu && lake env lean scripts/AxiomCheckWu.lean` is a trunk decision.
