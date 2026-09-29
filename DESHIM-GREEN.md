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
