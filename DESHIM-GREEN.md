# DESHIM-GREEN

Branch `ffl-deshim`, commit `4324001` — `GoodsteinPA/ToFoundation/Compat.lean` is gone and every call site spells Foundation's current API.

## `lake build`

```
Build completed successfully (1396 jobs).
```

## `scripts/deshim-check.sh`

```
deshim-check: OK
```

## `scripts/statement-check.sh`

```
statement-check: OK (1557 decls)
```

## What changed

Pure spelling, no statement changes (the fingerprint gate is unchanged against the frozen
`scripts/statement-snapshot.txt`, 1557 declarations):

| shim spelling | upstream spelling |
| --- | --- |
| `∀⁰ φ`, `∃⁰ φ`, `∀⁰* φ` | `∀¹ φ`, `∃¹ φ`, `∀¹* φ` |
| `V ⊧ₘ* T` | `V↓[ℒₒᵣ] ⊧* T` |
| `M ⊧ₘ σ` | `M↓[ℒₒᵣ] ⊧ σ` |
| `Semiterm.gValm ℕ e ε t` | `Semiterm.val (M := ℕ) e ε t` |
| `Semiterm.gVal s e ε t` | `Semiterm.val (s := s) e ε t` |
| `Semiformula.gEvalm ℕ e ε φ` | `Semiformula.Eval (M := ℕ) e ε φ` |
| `Semiformula.gEval s e ε φ` | `Semiformula.Eval (s := s) e ε φ` |
| `𝚺₁`, `𝚺₀`, `Γ-[n]`, `𝚺-[1]` | `𝚺ᴬ₁`, `𝚺ᴬ₀`, `Γᴬ-[n]`, `𝚺ᴬ-[1]` |
| `Arithmetic.Hierarchy Γ s φ` | `ℬ[<, ℒₒᵣ].Hierarchy Γ s φ` |
| `Arithmetic.Hierarchy.rew/and_iff/…` | `Bounding.Hierarchy.rew/and_iff/…` |
| `Arithmetic.DeltaZero φ` | `ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ` |
| `Derivation2 T Γ` | `LK2.Derivation T Γ` |

`𝗜𝚺₁` / `𝗜𝚺₀` keep their own (unrelated) spelling.

The `@[simp]` lemmas the shim re-proved (`val_const`, `val_operator₀/₁/₂`,
`eval_rel₀/₁/₂`, `eval_nrel₀/₁/₂`) turned out not to be load-bearing: after the notation
port, the only explicit reference was `Semiterm.val_operator₀` in one `simp only` set in
`GoodsteinPA/Encoding.lean`, replaced there by upstream's general `Semiterm.val_operator`
plus `Matrix.empty_eq`.  Nothing was kept in our namespace, so the shim's declarations are
gone outright rather than relocated.

Files that previously reached Foundation only through `Compat` (`Internal.lean`,
`ToFoundation/Numeral.lean`, `ToFoundation/FvSubst.lean`) now import
`Foundation.FirstOrder.Arithmetic.HFS` directly.

No `axiom` or `sorry` was added.

## Follow-on: the axiom gate is live again

`scripts/AxiomCheck.lean` — described in `Statement.lean` as "the enforced point of truth" — had
been silently dead: it still imported `GoodsteinPA.Reduction` / `.Bridge` / `.Domination`, modules
that no longer exist, and CI's axiom step was commented out.  Re-pointed to the current names
(`GoodsteinPA.Zinfty.consistency_PA` for the consistency corollary, `Goodstein.Dom.goodstein_terminates`
for the ℕ-level companion) and re-enabled in `.github/workflows/ci.yml`, alongside the two new gates:

```
$ lake env lean scripts/AxiomCheck.lean
$ echo $?
0
```

Silent + exit 0 means all four `#guard_msgs`-pinned audits hold, so the de-shim introduced no
`sorryAx` and no axiom drift:

- `GoodsteinPA.peano_not_proves_goodstein`
- `GoodsteinPA.Zinfty.consistency_PA`
- `Goodstein.Dom.goodstein_terminates`
- `GoodsteinPA.goodsteinSentence_faithful`

each on exactly `[propext, Classical.choice, Quot.sound]`.  `lake shake GoodsteinPA --keep-public`
reports no unused imports after the import rewiring.

## Scope note for the host

This run's objective was the **bounded** DESHIM brief only (remove the compat shim; all three
gates green).  It is met.  The 69 `sorry`s elsewhere in `GoodsteinPA/` are pre-existing,
unrelated proof debt and were deliberately untouched — the shim port changed no statement, as
the fingerprint gate confirms.  If this run is relaunched, it should be with
`--done-when 'deshim'`-style scoping rather than repo-wide sorry-freeness.

## Follow-on 2: repo-wide axiom sweep, and the `native_decide` it found

`AxiomCheck.lean` pins four *designated* theorems.  That is a spot check: a `sorry` or a
`native_decide` anywhere else in `GoodsteinPA/` is invisible to it unless the summit happens to
reach that declaration.  `scripts/AxiomSweep.lean` (new) closes the hole — it walks **every**
declaration in every `GoodsteinPA*` module, calls `Lean.collectAxioms`, and throws unless each
dependency is in `{propext, Classical.choice, Quot.sound}`.

Its first run was **not** clean: 9 declarations in `GoodsteinPA/ToMathlib/ONote/Computability.lean`
carried an `ofReduceBool` from one `native_decide` in `ONote.cmpStep_spec`'s `m = 0` base case
(`cmpStep_spec` itself plus `computable_Cnat`, `computable_enc`, `computable_Nfb`, `computable_nfTB`,
`computable_nfStep`, `computable_nthNF`, `computable_countNF`, `rePred_ltPull_natCode`).

The `native_decide` was unnecessary.  The goal there is `1 = ordCode ((decodeONote 0).cmp (decodeONote 0))`;
plain `decide` gets stuck because `decodeONote` is defined by well-founded recursion, so its `0` case
does not reduce under whnf.  Rewriting with the equation lemma first makes it
`1 = ordCode (zero.cmp zero)`, closed by `simp [decodeONote, ONote.cmp, ordCode]`.

After that one-line fix:

```
$ lake env lean scripts/AxiomSweep.lean
$ echo $?
0
```

Then strengthened: the first version filtered out `isInternalDetail` names, which silently skipped
**2006** declarations (`private` lemmas, compiler auxiliaries, `example`s) — an overstated claim.  It
now takes the closure over *every* declaration with no name filter at all, **3564** of them, and the
union is still exactly `[propext, Classical.choice, Quot.sound]`.  Nothing can hide behind a name.

It also asserts the two anti-vacuity anchor modules are still in the import graph.  The anchors
(`goodsteinLength 3 = 5`, `bump 2 4 = 27` — the classic `2² ↦ 3³`, …) deliberately use
`native_decide` and are written as anonymous `example`s precisely so no named declaration can depend
on them; they guard against definitional drift on every build without entering the trusted base.
Nothing previously noticed if they were dropped.

Both halves were confirmed by negative test, not just by passing:

```
$ # inject `theorem sweep_canary : 1 = 1 := by sorry` into Goodstein/Defs.lean
$ lake env lean scripts/AxiomSweep.lean
error: AxiomSweep: 1 disallowed axiom dependency/ies among 3564 GoodsteinPA declarations:
  Goodstein.sweep_canary  depends on  sorryAx

$ # drop the Anchors import from GoodsteinPA.lean
$ lake env lean scripts/AxiomSweep.lean
error: AxiomSweep: anti-vacuity anchor module
  GoodsteinPA.ToMathlib.Goodstein.Domination.Anchors is missing from the import graph
```

Both canaries reverted.  Added to CI.

The three audit scripts now have complementary, non-overlapping jobs:

| script | claim |
| --- | --- |
| `AxiomCheck.lean` | the four headline *statements* are clean (narrow, human-readable, pinned) |
| `AxiomSweep.lean` | *nothing anywhere* in `GoodsteinPA/` is dirty (broad, unconditional) |
| `statement-check.sh` | no declaration's statement drifted from the frozen baseline |

