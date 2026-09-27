# Port the ε₀ arc onto FFL `main` (treadmill direction)

**Objective.** Make the ε₀ arc (stages 1-3: general Wainer bound, PA ⊬ Hydra, PA ⊬ Paris–Harrington)
build green on this branch, `epsilon0`, which starts from FFL `main` (`4eb213c`).  The arc was written
on the pre-refactor fork layout (tag **`pre-ffl-rebase`** = `5990fc6` on `gotrevor/goodstein-independence`,
based on `92b77ee`).  FFL then refactored heavily, so this is a PORT, not a replay: the mathematics
and the headline statements stay; module paths, namespaces and imports change.

Commit every green checkpoint with `git-safe`.  Do not push and do not open PRs.  Keep a short dated
log at the bottom of this file; it is the lap-to-lap handoff.

## What is already staged (uncompiled)

The arc's added files were copied in with `src/` stripped:
- Lean: `GoodsteinPA/{WainerGeneral,HydraComputable,HydraEscape,HydraIndependence,HydraLowerBound}.lean`,
  `GoodsteinPA/PH/**`, `PAComparator/**`, `scripts/comparator-probe`, `.github/workflows/comparator.yml`.
- Docs/notes (reference only, no edits needed): `archive/eps0/` (roadmap, freeze, PH spec + plan,
  Buchholz text `archive/eps0/papers/ph-buchholz-bewth98.txt`, agent mail).
- Changes the arc made to files that FFL also has are saved as diffs, NOT applied:
  `archive/eps0/fork-side/{lakefile.toml,lake-manifest.json,scripts_AxiomCheck.lean,src_GoodsteinPA.lean,src_GoodsteinPA_ONoteComp.lean}.diff`.
  Re-apply their *intent* onto FFL's versions by hand.
- The old tree is always readable: `git show pre-ffl-rebase:src/GoodsteinPA/<File>.lean`, and FFL's
  refactor history is `git log 92b77ee..4eb213c` (the ~25 SnO₂WMaN PRs say what moved where).

## Frozen headlines (same statements, same namespaces)

These must end up proved, with statements unchanged up to the new import paths:
- `GoodsteinPA.Wainer.pa_provable_pi2_eventually_witnessed_below_fastGrowing` (`WainerGeneral.lean`)
- `GoodsteinPA.Hydra.pa_not_proves_hydra`, `GoodsteinPA.Hydra.exists_sigma1_battle_def`
- `GoodsteinPA.PH.pa_not_proves_ph`, `GoodsteinPA.PH.exists_sigma1_ph_def`, `GoodsteinPA.PH.ph_true`

Compare each against `git show pre-ffl-rebase:<old path>` before declaring done.  If an FFL rename
forces a change in a *statement* (e.g. a definition moved namespace), keep the meaning identical and
note it in the log.

## Porting notes

- **Layout.** No `src/`; the lib root is `GoodsteinPA.lean` at the repo root.  FFL uses the Lean
  **module system**: files start with `module`, use `public import`, and `@[expose] public section`.
  Follow the style of neighbouring FFL files.
- **Moved modules** (old → find the new home with `git grep` on FFL): `ONoteComp` →
  `GoodsteinPA/ToMathlib/ONote/Computability.lean`; `Hardy`, `Domination`, `Computability`,
  `WainerBound`, `Bridge` → under `GoodsteinPA/ToMathlib/…`, `Zef2TC/…`, `Encoding.lean`.
  `GoodsteinPA.Statement` still exists.  Grep for the declaration names the arc uses; do not guess.
- **The `ONoteComp` change** (`primrec_cmpStep`, `primrec_Cnat`) must be added to FFL's
  `ToMathlib/ONote/Computability.lean`: additive, keep `computable_cmpStep`.
- **Foundation** moved from `2040d2f` to `b47cf44` (#835 renamed the clashing `Matrix.map` /
  `forall_iff` / `exists_iff` to `vec*`).  Fix the call sites.
- **LeanGallery**: add the `[[require]]` + the manifest entry from the saved diff (rev `a834bba…`),
  **by hand-editing `lakefile.toml` and `lake-manifest.json`**.  Its package is already present in
  `.lake/packages/`.  Never run `lake update`: it drags the gallery's newer mathlib in.
- **`PAComparator` lib**: add the `[[lean_lib]]` stanza from the saved diff.  FFL has no `srcDir =
  "src"`, so the override is probably unnecessary; check.  It stays out of `defaultTargets`.
- `scripts/AxiomCheck.lean`: add the arc's `#print axioms` pins to FFL's version.

## Hard rules

- Do not change `GoodsteinPA/Statement.lean` or any existing FFL headline.  Prefer additive edits
  to FFL files; if you must expose or generalize an FFL lemma, keep the old name working.
- No new `axiom`.  `native_decide` is acceptable where the arc already used it.
- No network in the box: all packages are already under `.lake/packages`.
- Work-in-progress files stay out of `GoodsteinPA.lean` until they compile; check a single file with
  `lake env lean <file>`.

## Done when

1. `lake build` is green with every arc module imported from `GoodsteinPA.lean`.
2. `lake env lean scripts/AxiomCheck.lean` shows the arc headlines on the standard three axioms
   (plus whatever the pinned footprints were at `pre-ffl-rebase`).
3. `lake build PAComparator` builds (Challenge files carry `sorry` by design).
Then log it and stop.

## Log

### 2026-09-27 — stage 1 (Wainer general) ported green

- `ToMathlib/ONote/Computability.lean`: additive `primrec_cmpStep` / `primrec_Cnat`
  (`computable_cmpStep` kept as a corollary).
- `GoodsteinPA/WainerGeneral.lean` ported to the module system (`public import
  GoodsteinPA.Zef2TC.Wainer` + `GoodsteinPA.ToMathlib.Hardy.Majorization`) and imported from
  `GoodsteinPA.lean`.  Statement-level renames only, all forced by Foundation `b47cf44`:
  `SyntacticSemiformula ℒₒᵣ n` → `Semiformula ℒₒᵣ ℕ n`, `SyntacticFormula ℒₒᵣ` →
  `Semiformula ℒₒᵣ ℕ 0`, `SyntacticSemiterm` → `Semiterm ℒₒᵣ ℕ`, `Embedding.asg` → `asg`,
  `HardyMajorization.{Scirc_dom_pad,master_conversion}` → `ONote.…` (bare, via `open ONote`),
  `WainerRoute.EventuallyLE`/`GoodsteinPA.Dom` → `Goodstein.EventuallyLE`/`Goodstein.Dom`.
  The frozen headline `pa_provable_pi2_eventually_witnessed_below_fastGrowing` is unchanged
  modulo those; `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
- Next: stage 2 (Hydra) — needs the LeanGallery `[[require]]` + manifest entry by hand.
