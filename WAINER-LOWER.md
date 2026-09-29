# WAINER-LOWER: the lower half of Wainer's classification, via Wu's Gentzen upper bound

Treadmill brief, branch `wainer-lower` of `gotrevor/goodstein-independence` (cut from `v4.34`,
the trunk).  The box never pushes.

## The goal

g-i already proves the **upper half** of Wainer's classification of PA's provably total functions
(`GoodsteinPA.Wainer.pa_provable_pi2_eventually_witnessed_below_fastGrowing`,
`GoodsteinPA/WainerGeneral.lean`): every PA-provable Π₂ sentence `∀x ∃y φ` (φ Σ₁) has witnesses
eventually bounded by some `fastGrowing o`, `o < ε₀`.

This branch proves the **lower half**: every `fastGrowing o` with `o` in normal form (so `o < ε₀`)
is PA-provably total.  Together they are the full classification: the PA-provably total functions
are exactly those eventually dominated by the fast-growing hierarchy below ε₀.

The frozen statement is `GoodsteinWu.fastGrowing_provably_total` in `GoodsteinWu/WainerLower.lean`,
and `GoodsteinWu.wainer_classification` packages both halves.  **Do not change either statement.**

## Where the key input comes from

`OrdinalAnalysis` (KT. Wu's repo, our v4.34 port, required at a pinned SHA) proves Gentzen's upper
bound, `OrdinalAnalysis.Gentzen.UpperBound.gentzen_upper_bound`:

```lean
theorem gentzen_upper_bound (φ : Semiformula LX ℕ 1) (a : ONote) (ha : ONote.NF a) :
    paLX ⊢ closedTI φ (notationTerm ⟨a, ha⟩)
```

i.e. PA, in the language `LX = ℒₒᵣ + X`, proves transfinite induction along Wu's coded ordering
`≺` (`precCode`, `Gentzen/CodedNotation.lean`) up to every notation, for every formula.  Use it as a
black box; never edit `OrdinalAnalysis`.

## Suggested route (the lap may choose another)

1. **Arithmetize the hierarchy on Wu's codes.**  A Σ₁ formula `F(c, n, y)` over `ℒₒᵣ` whose
   ℕ-reading is `y = fastGrowing o n` when `c = nonoteCode o` (Wu's coding,
   `Gentzen/NotationBridge.lean`), via computation sequences of the fundamental-sequence recursion
   (mathlib `ONote.fundamentalSequence`, `ONote.fastGrowing`, `Mathlib/SetTheory/Ordinal/Notation.lean`).
   Wu's `Gentzen/InternalONote.lean` already has the internal comparator `icmp`, `isNF`, `iadd`,
   `ocOadd`; g-i's `wip/InternalONote.lean` shares that coding.
2. **PA proves the recursion equations** for `F` (zero, successor, limit cases), in IΣ₁ style.
3. **Totality is progressive.**  Take `ψ(c) := ∀n ∃y F(c, n, y)` (substituted for `X` with Wu's
   `SubstX.substX`).  Show PA ⊢ `Prog(≺, ψ)`: if every `d ≺ c` is total then `c` is (the successor
   case iterates `F(d, ·)`; the limit case uses `F(c[n], n)`).
4. **Apply `gentzen_upper_bound`** with `φ := ψ` at `a := o`, get `paLX ⊢ ∀c ≺ o. ψ(c)` plus `ψ(o)`.
5. **Conservation**: `paLX ⊢ lMap σ → 𝗣𝗔 ⊢ σ` for `X`-free σ.  Not in Wu.  Semantic proof: any
   model of PA expands to a model of `paLX` with `X := ∅`, then completeness.  Wu's
   `paLX_of_peano` (`CodedNotation.lean:147`) is the other direction.
6. **Read off** the frozen statement: `φ(y, n) := F(⌜o⌝, n, y)`, its Σ₁-ness, its ℕ-reading.

Decompose into named `sorry` leaves early; a lap that turns one fat `sorry` into five named ones
has made progress.

## Layout (why a separate library)

g-i's files use the Lean `module` system and Wu's do not, and a module cannot import a non-module
file.  So the bridge lives in the **non-module** library `GoodsteinWu` (`GoodsteinWu/*.lean`), which
may import both `GoodsteinPA.*` and `OrdinalAnalysis.*`.  Do not convert either side.

`GoodsteinWu` is not in `defaultTargets` while it carries `sorry`: build it with
`lake build GoodsteinWu`.

## Done

`GoodsteinWu/WainerLower.lean` is sorry-free and `lake build GoodsteinWu` is green, with
`#print axioms GoodsteinWu.wainer_classification` showing only
`[propext, Classical.choice, Quot.sound]`.  Log it in the handoff, commit, `box done`.

## Rules

- **Frozen:** the two statements above, and everything under `GoodsteinPA/` that `scripts/AxiomCheck.lean`
  pins.  Add new files under `GoodsteinWu/`; touch `GoodsteinPA/` only to add a helper lemma.
- Never add an `axiom`; never edit the lakefile or manifest; no network (`lake update`, `cache get`).
- `native_decide`, deprecations, heartbeat bumps are fine.
- New files carry the standard header:
  `Copyright (c) 2026 Trevor Morris. All rights reserved.` /
  `Released under Apache 2.0 license as described in the file LICENSE.` / `Authors: Trevor Morris`.
- Commit green checkpoints as you go.
