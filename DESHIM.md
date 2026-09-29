# DESHIM: remove the Foundation compat shim, spell everything the upstream way

Treadmill brief, branch `ffl-deshim` (on top of `ffl-v434`, the v4.34 port).  The box never
pushes.  Leave this file in place; the host strips process notes before any PR.

## Why

`GoodsteinPA/ToFoundation/Compat.lean` restores Foundation's *old* spellings on top of the current
API: notations (`∀⁰ ∃⁰ ∀⁰* ∃⁰*`, `⊧ₘ ⊧ₘ*`, `Γ-[n]`, `𝚺₀ 𝚷₀ 𝚫₀ 𝚺₁ 𝚷₁ 𝚫₁`), aliases (`gVal`,
`gValm`, `gEval`, `gEvalm`, `Arithmetic.Hierarchy`, `Arithmetic.DeltaZero`, `Derivation2`), and
re-proved `@[simp]` lemmas upstream dropped (`val_const`, `val_operator₀/₁/₂`, `eval_rel₀/₁/₂`,
`eval_nrel₀/₁/₂`).  All of it is declared into Foundation's own `FFL.*` namespaces or as global
notation, so anything importing GoodsteinPA inherits it, and it collides with other FFL libraries.
This repo is now hosted at FFL next to Foundation and AlphaCentauri; its code should read the way
theirs does.

## Objective

1. `scripts/deshim-check.sh` prints `deshim-check: OK` (red today).
2. `lake build` green.
3. `scripts/statement-check.sh` prints `statement-check: OK`, unchanged baseline.

Then commit, create `DESHIM-GREEN.md` with the last lines of all three runs, commit it, `box done`.

## How

- Rewrite every call site to the upstream spelling the shim abbreviates: `∀⁰` → `∀¹`, `∃⁰` → `∃¹`,
  `∀⁰*` → `∀¹*`, `∃⁰*` → `∃¹*`; `V ⊧ₘ* T` → `V↓[ℒₒᵣ] ⊧* T`; `gEval s e ε φ` → the instance form
  (`letI := s; Semiformula.Eval e ε φ` or `@Semiformula.Eval … s …`), and so on.  Read each shim
  entry's body in `Compat.lean`: **it is the replacement.**  Check Foundation for the current name
  before inventing one (`grep -rn` under `.lake/packages/Foundation/Foundation`).
- The removed simp lemmas: prefer upstream's general lemma (`Semiterm.val_operator`,
  `Semiformula.eval_rel`, …) plus `Matrix.empty_eq` / `Matrix.fun_eq_vec_one` / `…_two` at the call
  site.  If one is used so widely that inlining is silly, keep it as a `private` or file-local
  lemma in **our own namespace** (`GoodsteinPA.…`), never under `FFL.*`.
- Then delete `Compat.lean` and its imports.  Work file by file; commit green checkpoints.
- Mechanical sed is fine for the notation swaps, but macOS `sed` / plain `perl` mangle multibyte
  characters: use `perl -CSD -Mutf8 -pi -e` or Python with explicit UTF-8.

## The statement gate

`scripts/statement-check.sh` fingerprints every GoodsteinPA declaration's type (and definition
value) with the Compat constants delta-expanded, against `scripts/statement-snapshot.txt`.  A pure
spelling change keeps every line identical; a changed statement shows up as a diff line.

- If a line changes, the fix is almost always to match the shim body more literally (argument
  order, `letI` vs explicit `@`, a `fun` wrapper).  Make the new spelling elaborate to the same term.
- **Never run `--update`** and never edit `statement-snapshot.txt`.  If a line cannot be matched
  after an honest try, stop on it: record the declaration, the old and new pretty-printed types,
  and why in `DESHIM-STUCK.md`, and `box stuck`.

## Rules

- **Frozen:** `scripts/statement-check.sh`, `scripts/StatementSnapshot.lean`,
  `scripts/statement-snapshot.txt`, `scripts/deshim-check.sh`, `lakefile.toml`, `lake-manifest.json`.
- Never add an `axiom` or `sorry`.  No network.
- Proof bodies may change freely; statements may not (see the gate).
