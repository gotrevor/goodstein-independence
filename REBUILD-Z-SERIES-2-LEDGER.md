# REBUILD-Z — SERIES-2 LEDGER (append-only, one block per stage)

Order: `REBUILD-Z-SERIES-2-ORDER-2026-07-03.md`. Discipline: bare `lake build` (1342-job full
gate) per stage; hygiene claims diff-verified (Series-1 §5.2); self-ratification VOID; wip-only
for everything probe-shaped.

---

## Stage A — Series-1 Stage-1 debt (src, pre-ratified, mechanical) — ✅ LANDED (lap 196)

**Build**: 🟢 `lake build` (1342 jobs, fresh full rebuild). **Headline**:
`GoodsteinPA.peano_not_proves_goodstein` footprint = `{propext, Classical.choice,
GoodsteinPA.goodstein_implies_consistency, Quot.sound}` — UNDRIFTED (re-checked via
`blueprint_audit`). **`blueprint_audit`**: ✓ PASSED, 16 nodes consistent, 0 warnings.

Diff-verified changes (git diff, not asserted from memory):

- **(A-1) `src/GoodsteinPA/WainerLadder.lean` CREATED.** Imports `GoodsteinPA.OperatorZef2` +
  `GoodsteinPA.WainerRoute` (the translation apparatus: `EventuallyLE`, `goodsteinSentence`,
  `GoodsteinPA.Dom.goodsteinLength`, `fastGrowing`). Namespace `GoodsteinPA.WainerLadder`.
  Wired into the blueprint lib root (`src/GoodsteinPABlueprint.lean` +1 import line). This is
  the L-E-direction home (ruling §4) where the top rungs can bind the concrete goodstein
  translation without the `OperatorZef2`-level cross-import obstruction.
- **(A-2) `wainer_splice_Zef2` MOVED + RESTATED VERBATIM** at the R-5 shape:
  ```lean
  theorem wainer_splice_Zef2 :
      (𝗣𝗔 ⊢ ↑goodsteinSentence) →
        ∃ o : ONote, o.NF ∧
          EventuallyLE GoodsteinPA.Dom.goodsteinLength (fun n => fastGrowing o n) := by sorry
  ```
  This is EXACTLY the statement of the `wainer_bound_of_pa_proves_goodstein` axiom (the rung
  that flips it `axiom → theorem`). The OLD parametric form
  (`(e B α …) : … ewIter (ewRootSlot e B) α 0 ≤ …`, the lap-8-ruling L-W VOIDed-as-trivial
  shape) DELETED from `OperatorZef2.lean`.
- **(A-3) `embedding_Zef2` DELETED** from `OperatorZef2.lean` (lap-8 ruling §4 VOIDed
  placeholder, R-6 debt). A `TODO(rung E, Stage-B statement lap)` naming its faithful
  statement now lives in `WainerLadder.lean`'s module docstring. No src theorem for rung E
  (its statement is the Stage-B ratification target — wip-first).
- **(A-4) Blueprint tex** (`blueprint/src/content.tex`): `thm:zeh_rank_zero` `\notready`
  DROPPED (proven modulo the pass; kept OFF `\leanok` — no `@[goodstein_blueprint]` site since
  sorry-pins can't be tagged, so the reconciler leaves this hand-status alone);
  `thm:wainer_splice` bound `\lean{GoodsteinPA.WainerLadder.wainer_splice_Zef2}` (kept
  `\notready`, still a sorry). `blueprint_audit` PASSES.
  ⚠️ **Web HTML regeneration (`annotate_depgraph.py --web`) DEFERRED to host**: `leanblueprint`
  is not installed on this box (`which leanblueprint` → absent). The tex SOURCE is updated and
  the machine gate (`blueprint_audit`) passes; the generated `blueprint/web/*.html` +
  `blueprint/lean_decls` (both untracked artifacts) refresh needs the host's leanblueprint
  toolchain. `checkdecls` will resolve the new `\lean{}` binding (the decl compiles in the
  blueprint lib).
- **(A-5) `wip/Lap13ReadoffDeltaProbe.lean` DELETED** (`git rm`) — stale name-clash with the
  now-promoted `src` `sound0` (`OperatorZef2.lean:897`).

**Sorry-declaration delta** (build `declaration uses \`sorry\`` warnings, fresh full rebuild):
15 → **14** = net −1, matching the mandated {−2 voided (A-2 old form + A-3 embedding), +1
restated}. (The order's absolute "17 expected" uses a `lean-sorry` tool not present on this
box; the verifiable delta is the mandated −1.)

Gate summary: 🟢 build · headline undrifted · no new `src` axiom · no `native_decide` in new
files · wip freeze refs untouched · `blueprint_audit` ✓. Stage A CLOSED.

---
