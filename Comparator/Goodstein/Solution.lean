/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import GoodsteinPA.Statement   -- GoodsteinPA.peano_not_proves_goodstein
import GoodsteinPA.Bridge      -- GoodsteinPA.goodsteinSentence_faithful

/-!
# Kirby–Paris independence of Goodstein's theorem — comparator SOLUTION

Discharges the two `sorry`s in `Challenge.lean` by bringing the real development into scope. This
file declares **nothing** — and that is not a shortcut, it is the point (the "strong pattern",
mirroring `~/src/tao-collatz/Comparator/TaoCollatz/Solution.lean` and
`~/src/lean-gallery/Comparator/Goodstein/Solution.lean`).

## Why there is nothing to write here

`Challenge.lean` re-derives every repo-owned constant that appears in the two headline
statements — the audited Mathlib-native trio (`GoodsteinPA.base`, `GoodsteinPA.bump`,
`GoodsteinPA.goodsteinSeq`) *and* the Foundation-DSL arithmetization objects
(`…ipowDef`, `…ilogDef`, `…bumpNextDef`, `…ibumpTableDef`, `…ibumpDef`, `…igoodsteinDef`, the
three `PR.Blueprint`s, and `GoodsteinPA.goodsteinSentence`) — **under their own fully-qualified
names**, from `Mathlib` + `Foundation` alone, importing nothing from this repo. Importing the real
`Statement`/`Bridge` here therefore populates this environment with constants of exactly those
names, and comparator's job becomes to check that the two are *the same declarations*:

* `compareAt` compares the challenge's and the solution's `peano_not_proves_goodstein` /
  `goodsteinSentence_faithful` at the level of `ConstantVal` (name, universe params, **type**), then
  walks the transitive constant closure of that type — and of the *values* of every `def` in it —
  demanding a **byte-identical `ConstantInfo`** for every constant it reaches;
* `checkAxioms` then walks this development's proofs and rejects any axiom outside the whitelist
  `{propext, Quot.sound, Classical.choice}`;
* the Lean kernel — and, because `enable_nanoda: true`, the independent `nanoda` kernel — replay the
  whole thing.

The alternative — a challenge under a fresh namespace, whose copies this file would have to bridge
to the development's — is strictly worse. `bump` is defined by **well-founded recursion**, which
Lean marks **irreducible**: two copies would not be interchangeable by `rfl`, so the bridge could
not be a one-liner. Using the development's real names deletes all that glue and upgrades the
certificate from "a faithful copy of the theorems holds" to "**this development's theorems** hold".

## Trust base

This entry honestly rests on **Mathlib + Foundation** (`FormalizedFormalLogic/Foundation`, pinned by
rev in `lakefile.toml`), not Mathlib alone: `Challenge.lean` imports Foundation to reuse its
first-order logic, `𝗣𝗔`, Σ₁ arithmetization and Gödel II. That is a deliberate, one-line widening of
the trust base (the same basis on which Flypitch's CH-independence sits in comparator's `1000.yaml`).
Foundation is a shared dependency of *both* environments at the *same* rev, so its constants
(`𝗣𝗔`, `⊬`, `Rew.subst`, `PR.Blueprint`, …) match automatically.

If anyone edits the development's `bump`, `base`, `goodsteinSeq`, the arithmetization `…Def`s, or
either headline's statement, comparator fails here — which is exactly the tripwire we want.

This file is *not* part of the audit surface. `Challenge.lean` is.
-/
