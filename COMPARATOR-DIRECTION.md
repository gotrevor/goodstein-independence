# DIRECTION: build the first Comparator harness for goodstein-independence

**You are working in a git worktree** on branch `gotrevor/comparator`
(`~/src/goodstein-independence/worktrees/gotrevor/comparator`). Everything below happens
here. This doc is scaffolding: **do NOT `git add` this file** to the PR branch.

## Goal

Stand up a single `leanprover/comparator` entry, `Comparator/Goodstein/`, that certifies the
proved headline `GoodsteinPA.peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence` plus its
anti-vacuity anchor `GoodsteinPA.goodsteinSentence_faithful`. This is the beachhead proving the
Foundation dependency works end-to-end under comparator. **Only this one entry** — do not start
the later Hydra / Paris-Harrington entries.

Commit green on this branch. **Do NOT push and do NOT open a PR** — the box has no GitHub egress,
and Trevor pushes to the fork + reviews before it goes to FFL. Finish by writing a short
`HANDOFF-comparator-DONE.md` (untracked is fine) with the final state.

## The key finding (why this was thought hard, and why it isn't)

Comparator does **not** hardcode a Mathlib-only environment. It builds `Challenge.lean` against
**this repo's own `lakefile.toml`** (which already `require`s Foundation). So a Challenge that does
`import Mathlib` + imports Foundation modules builds and compares fine. "Mathlib-only" is a
**trust-minimization convention, not a tool constraint**. The trust base here honestly grows
Mathlib → Mathlib + Foundation (a one-line decision; Flypitch's CH-independence sits on
`1000.yaml` on exactly this basis).

## How comparator actually checks (the mental model that drives the design)

For each name in `theorem_names`, comparator (see `~/src/clone/comparator/README.md` "Internals"
step 4) compares the challenge's and the solution's declaration at `ConstantVal` level (name,
universe params, **type**), then **walks the transitive constant closure of that type — and of the
*values* of every `def` in it — demanding a byte-identical `ConstantInfo` for every constant.**

Crucial consequence: **shared Foundation/Mathlib constants match automatically** (both the challenge
and the solution import the *same* Foundation at the *same* rev via the *same* lakefile, so
`LO.FirstOrder.Arithmetic.subDef`, `PR.Blueprint`, `Rew.subst`, `𝗣𝗔`, `⊬`, `Models`, … are literally
the same declarations in both environments). **The only constants you must re-declare
byte-identically in the Challenge are the ones this repo OWNS** that appear in the closure.

### ⛔ Do NOT use comparator "definition holes" here (confirmed gameable)

A def-hole checks only name/type/universe/safety, not the body — so a hole on `igoodsteinDef` would
let a solution substitute *any* Σ₁ formula. The tempting shortcut ("the bridge
`goodsteinSentence_faithful` certifies fidelity, so leave `igoodsteinDef` a hole") is **wrong**: the
bridge's RHS (`∀ m, ∃ N, goodsteinSeq m N = 0`) is a *proved theorem*, so the iff collapses to just
`ℕ ⊧ₘ goodsteinSentence`, satisfiable by any ℕ-true PA-unprovable ∀∃-sentence. ⇒ **Full
byte-identical re-declaration of the whole closure. No `definition_names` field in config.json.**
The bridge is still worth including as the second `theorem_name` (an ℕ-truth / anti-vacuity anchor
tying the syntactic sentence to the small auditable `goodsteinSeq`), just not as a shortcut.

## The exact re-declaration set (empirically traced; verify with the probe)

The closure of the two theorems' statements bottoms out at these **repo-owned** constants. Copy each
one **VERBATIM** from the worktree's own `src/GoodsteinPA/*.lean` (that is the source of truth — do
not re-type from memory). Copy **only these `def`s** — NOT the `instance`s, `@[simp] lemma`s, or
`construction`s next to them (those are not in the *statement* closure). Keep the `_root_.` prefixes
and `noncomputable` modifiers exactly.

**Mathlib-native trio (small, the human-readable audit core) — `namespace GoodsteinPA`:**
| constant | file:line |
|---|---|
| `GoodsteinPA.base` | `src/GoodsteinPA/Defs.lean:25` |
| `GoodsteinPA.bump` (well-founded; copy the full `termination_by`/`decreasing_by`) | `src/GoodsteinPA/Defs.lean:30` |
| `GoodsteinPA.goodsteinSeq` | `src/GoodsteinPA/Defs.lean:46` |

**Foundation-DSL syntactic objects (the arithmetization specialization):**
| constant | file:line | namespace context |
|---|---|---|
| `GoodsteinPA.InternalPow.pow.blueprint` | `InternalPow.lean:31` | `namespace GoodsteinPA.InternalPow` |
| `LO.FirstOrder.Arithmetic.ipowDef` | `InternalPow.lean:53` | `def _root_.LO.FirstOrder.Arithmetic.ipowDef` |
| `LO.FirstOrder.Arithmetic.ilogDef` | `InternalLog.lean:116` | `def _root_.LO...ilogDef` (`.mkSigma`, refs `!ipowDef`) |
| `LO.FirstOrder.Arithmetic.bumpNextDef` | `InternalBump.lean:31` | refs `!ilogDef !ipowDef !znthDef !divDef !remDef` |
| `GoodsteinPA.InternalBump.bumpTable.blueprint` | `InternalBump.lean:47` | refs `!mkSeq₁Def !bumpNextDef !seqConsDef` |
| `LO.FirstOrder.Arithmetic.ibumpTableDef` | `InternalBump.lean:74` | `bumpTable.blueprint.resultDef.rew …` |
| `LO.FirstOrder.Arithmetic.ibumpDef` | `InternalBump.lean:85` | `.mkSigma`, refs `!ibumpTableDef !znthDef` |
| `GoodsteinPA.InternalPow.goodstein.blueprint` | `InternalGoodstein.lean:24` | ⚠️ **namespace is `GoodsteinPA.InternalPow`** (that file opens it), refs `!ibumpDef !subDef` |
| `LO.FirstOrder.Arithmetic.igoodsteinDef` | `InternalGoodstein.lean:47` | `goodstein.blueprint.resultDef.rew …` |
| `GoodsteinPA.goodsteinSentence` | `Encoding.lean:83` | `namespace GoodsteinPA` (`noncomputable def`) |

All the `!…Def` splices that are NOT in this list (`znthDef`, `divDef`, `remDef`, `subDef`,
`seqConsDef`, `mkSeq₁Def`) are **Foundation** — do not re-declare them; they resolve to the shared
Foundation constants. (The `!ipowDef`/`!ilogDef`/etc. splices resolve to *your re-declared* copies
because they share the fully-qualified name.)

**Notation, not constants:** `goodsteinSentence_faithful`'s type uses the Compat notation `⊧ₘ`.
Notation creates no constant, so copy the two `notation` lines from `src/GoodsteinPA/Compat.lean:33`
and `:37` into the Challenge verbatim (`⊧ₘ*` and `⊧ₘ`). Do NOT `import GoodsteinPA.Compat` (that
would pull repo code into the challenge). The `“…”` first-order-formula notation, `!fooDef` splice
notation, `.mkSigma`, `𝚺₁.Semisentence`, `PR.Blueprint`, `Rew.subst`, `#0` de Bruijn — all
Foundation-native, available once you import the Foundation modules + `open LO LO.FirstOrder
LO.FirstOrder.Arithmetic`.

## Files to create

### `Comparator/Goodstein/config.json`
```json
{
  "challenge_module": "Comparator.Goodstein.Challenge",
  "solution_module": "Comparator.Goodstein.Solution",
  "theorem_names": [
    "GoodsteinPA.peano_not_proves_goodstein",
    "GoodsteinPA.goodsteinSentence_faithful"
  ],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": true
}
```
No `definition_names` field (see the def-hole ban above).

### `Comparator/Goodstein/Solution.lean`
Imports the development, declares **nothing** (the "strong pattern"):
```lean
import GoodsteinPA.Statement   -- peano_not_proves_goodstein
import GoodsteinPA.Bridge       -- goodsteinSentence_faithful
```
Plus a docstring explaining why there is nothing to write here (mirror
`~/src/tao-collatz/Comparator/TaoCollatz/Solution.lean` and `~/src/lean-gallery/Comparator/Goodstein/Solution.lean`).

### `Comparator/Goodstein/Challenge.lean`
- `import Mathlib`
- Foundation imports (start with these three, matching `Encoding.lean` + `InternalPow.lean`; add
  more if the build reports a missing constant/notation):
  `import Foundation.FirstOrder.Incompleteness.Second`,
  `import Foundation.FirstOrder.Arithmetic.R0.Representation`,
  `import Foundation.FirstOrder.Arithmetic.HFS`
- `set_option warningAsError false` (the statements below are `sorry` by design; the lib builds
  warnings-as-errors — see tao-collatz's Challenge for the same load-bearing line). Consider also
  `set_option autoImplicit false` to match if you enable it in the lakefile.
- `open LO LO.FirstOrder LO.FirstOrder.Arithmetic` (+ the two Compat `notation` lines).
- The full re-declaration set above, each under its exact namespace / `_root_.` name.
- The two theorems stated with `sorry`:
  ```lean
  namespace GoodsteinPA
  theorem peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence := sorry
  theorem goodsteinSentence_faithful :
      (ℕ ⊧ₘ goodsteinSentence) ↔ ∀ m, ∃ N, goodsteinSeq m N = 0 := sorry
  end GoodsteinPA
  ```
- This file is the human audit surface: give the DEFINITIONS real docstrings pointing at Goodstein
  1944 / Kirby–Paris, and explain the trust base includes Foundation.

### lakefile wiring
Add a `Comparator` lean_lib. ⚠️ this repo sets package `srcDir = "src"`, but the harness lives at
repo root under `Comparator/` (matching tao-collatz / lean-gallery layout). So the Comparator lib
needs its own `srcDir = "."`:
```toml
# comparator harness — NOT in defaultTargets (challenge carries `sorry` by design; the main libs
# build warnings-as-errors). Build explicitly: `lake build Comparator`. Real gate: CI.
[[lean_lib]]
name = "Comparator"
srcDir = "."
globs = ["Comparator.+"]
```
Verify `lake build Comparator.Goodstein.Challenge` and `lake build Comparator.Goodstein.Solution`
both resolve the module path. If per-lib `srcDir = "."` misbehaves with the glob, fall back to
putting the files under `src/Comparator/Goodstein/` and dropping the `srcDir` override (the package
srcDir then applies) — module path stays `Comparator.Goodstein.*` either way.

### `.github/workflows/comparator.yml`
Mirror `~/src/lean-gallery/.github/workflows/comparator.yml` verbatim, adjusting only
`LEAN4EXPORT_TAG` if this repo's `lean-toolchain` differs (check it; lean-gallery pins `v4.31.0`).
Keep `enable_nanoda: true` (config) — the second independent kernel is the one real trust gain and
is easy to lose by accident.

## The local pre-flight probe — FIX IT FIRST (it has a real bug for this repo)

There is no `scripts/comparator-probe` in this repo yet. Copy `~/src/lean-gallery/scripts/comparator-probe`
into `scripts/comparator-probe` and **fix its `keep` filter**, which is the crux for g-i:

- The lean-gallery probe keeps constants by **name prefix** (`"Goodstein"`, `"LeanGallery"`, …).
  That is WRONG here because this repo deliberately declares its syntactic objects under
  **Foundation's namespace** (`LO.FirstOrder.Arithmetic.ipowDef`, `…ilogDef`, `…ibumpDef`,
  `…igoodsteinDef`, `…bumpNextDef`, `…ibumpTableDef`). No name prefix — not even "derive prefix from
  theorem_names" (which yields `GoodsteinPA`) — catches those, so the probe would silently skip them
  and report a false green.
- **Fix: keep by DEFINING MODULE, not by name.** A constant is repo-owned iff its module starts with
  `GoodsteinPA` (solution env) or `Comparator` (challenge env, where the re-declarations live). Both
  environments *import* the probed module, so `env.getModuleFor? n` returns a real module for every
  probed constant (the current-file-elaboration `none` case does not arise — the probe does
  `import {module}` then `#eval`). Rewrite `keep` to be env-aware, e.g.:
  ```lean
  def keepMod (env : Environment) (n : Name) : Bool :=
    match env.getModuleFor? n with
    | some m => let s := m.toString; s.startsWith "GoodsteinPA" || s.startsWith "Comparator"
    | none   => false
  ```
  and thread `env` through the seed filter and `constClosure`'s `more` filter (both currently call
  `keep`). Everything else in the probe (the structural `render` with `pp.all`, the diff, the
  MISSING-THEOREM guard) stays.
- ⚠️ Note this is a strictly better fix than the KB todo `comparator-probe-stale-oleans.md`
  suggested ("derive prefixes from theorem_names"); record that when you write findings. Do NOT edit
  the shared `~/src/lean-gallery/scripts/comparator-probe` or the skill-repo copy from here — just
  fix this repo's local copy and note the finding for the host session.

## The loop

1. Write the four files + lakefile wiring + fixed probe.
2. `lake build Comparator.Goodstein.Challenge` and `…Solution` until both are green. Build failures
   in the Challenge usually mean a missing re-declaration (add the named constant) or a missing
   Foundation import (add the module).
3. `scripts/comparator-probe Goodstein` until it prints **`✅ Goodstein: statement closure
   identical`**. A DIFFERS report tells you exactly which constant mismatches — fix its
   re-declaration to be byte-identical (watch for a stray `noncomputable`, a different argument
   order in `Rew.subst ![#0,#2,#1]`, or copying a lemma/instance instead of the def).
4. Sanity: `lean-axiom-gate` (or `scripts/AxiomCheck.lean` via CI) on the main lib is unaffected —
   don't regress it.
5. Commit green on `gotrevor/comparator` (`git-safe` doors; bare `git` works in-box). **No push, no
   PR.** Write `HANDOFF-comparator-DONE.md` summarizing: files added, probe result, any Foundation
   modules you had to add, and anything for Trevor to check before he pushes to the fork.

## Completion criteria
- [ ] `lake build Comparator.Goodstein.Challenge` + `…Solution` green.
- [ ] `scripts/comparator-probe Goodstein` → `✅ statement closure identical (2 theorem(s))`.
- [ ] `.github/workflows/comparator.yml` present, adapted, `enable_nanoda: true`.
- [ ] Committed on `gotrevor/comparator`; `COMPARATOR-DIRECTION.md` NOT committed.
- [ ] `HANDOFF-comparator-DONE.md` written.

## Reference harnesses (read-only, on the `~/src` mount)
- `~/src/tao-collatz/Comparator/TaoCollatz/{config.json,Solution.lean,Challenge.lean}` + its `lakefile.toml`.
- `~/src/lean-gallery/Comparator/Goodstein/{...}` + `lakefile.toml` + `.github/workflows/comparator.yml` + `scripts/comparator-probe`.
- `~/src/clone/comparator/README.md` — the tool's config schema, build model, def-hole semantics.
