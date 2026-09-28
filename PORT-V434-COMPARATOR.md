# PORT-V434-COMPARATOR — Phase 2 green (PAComparator on v4.34.0)

Branch `v4.34`, local only (never pushed).  Phase 2 of `PORT-V434.md`: the `PAComparator` lib is
ported to current Foundation syntax, both builds are green, `AxiomCheck` is silent, and every
comparator-pinned statement is **expression-identical** between the challenge and the development.

## Green evidence

`lake build` (default targets, the whole development):

```
Build completed successfully (1548 jobs).
```

`lake build PAComparator` (the four challenge/solution pairs):

```
Build completed successfully (1505 jobs).
```

`lake env lean scripts/AxiomCheck.lean` → no output, exit `0` (every pinned statement and expected
axiom list byte-identical to the v4.31 tree).

## What Phase 2 changed

The `*/Challenge.lean` files are the comparator's trusted statements, so they stay **self-contained**
— no `GoodsteinPA/ToFoundation/Compat.lean`, no shim — and are written in upstream's own current
spelling:

* `∀⁰ ∃⁰ φ` → `∀¹ ∃¹ φ` (the superscript now numbers the order);
* `Arithmetic.Hierarchy 𝚺 1 φ` → `Bounding.Hierarchy ℬ[<, ℒₒᵣ] 𝚺 1 φ`;
* `FFL.FirstOrder.Arithmetic.HierarchySymbol` → `FFL.FirstOrder.Bounding.HierarchySymbol`,
  `𝚺₁.Semisentence` → `𝚺ᴬ₁.Semisentence`, plus `open scoped FFL.FirstOrder.Arithmetic
  FFL.FirstOrder.Bounding` (both notation families became `scoped`).

Because the Challenge files may not use the shim, the **development's** four pinned Σ₁ hypotheses
were restated with the same upstream spelling (`Bounding.Hierarchy ℬ[<, ℒₒᵣ] 𝚺 1 φ`, the very term
`Compat`'s `Arithmetic.Hierarchy` abbreviates) in `GoodsteinPA/PH/Main.lean`,
`GoodsteinPA/HydraEscape.lean` and `GoodsteinPA/WainerGeneral.lean`.  That is `Compat.lean`'s own
rule: statements hang off upstream directly.  No statement changed meaning and `AxiomCheck` is
unchanged.

Two **pre-existing** drifts (not toolchain churn) surfaced and were fixed on the comparator side:

* the development had moved `base`/`bump`/`goodsteinSeq` into `namespace Goodstein` and typed
  `goodsteinSentence : ArithmeticSentence`; `Support/Defs.lean` and `Challenge.lean` still said
  `namespace GoodsteinPA` / `Sentence ℒₒᵣ`;
* the development had consolidated the four `Internal*.lean` files into one
  `GoodsteinPA/Internal.lean`, which changes how Lean deduplicates the auto-generated
  `…_proof_N` auxiliaries of `.mkSigma` / `PR.Blueprint`.  The four support modules are now one
  `PAComparator/Goodstein/Support/Internal.lean` in `module` mode, declarations in the
  development's order — see churn pattern 29 in `PORT-V434.md`.

## Statement-identity harness

`scratchpad/cmp/` holds the check that drove all of the above.  For each side (challenge imports vs
development imports) it `#check`s / `#print`s under `pp.explicit`, `pp.notation false`,
`pp.fullNames` and `diff`s:

| harness | covers | result |
| --- | --- | --- |
| `chal.lean` / `dev.lean` | all 7 comparator-pinned theorem **types** | identical |
| `defs-chal.lean` / `defs-dev.lean` | `Goodstein.{base,bump,goodsteinSeq}`, `goodsteinSentence`, `pow.blueprint`, `ipowDef`, `ilogDef`, `bumpNextDef`, `ibumpTableDef`, `ibumpDef`, `igoodsteinDef` — bodies **and** `_proof_N` names | identical |
| `ph-*.lean` | `RelLarge`, `Homog`, `PH`, `PHx` | identical |
| `hy-*.lean` | `Hydra`, `ord`, `canonStep`, `battle`, `ofCode` | identical |

The 7 pinned names (from the `config.json`s):
`GoodsteinPA.peano_not_proves_goodstein`, `GoodsteinPA.goodsteinSentence_faithful`,
`GoodsteinPA.Hydra.pa_not_proves_hydra`, `GoodsteinPA.PH.pa_not_proves_ph`,
`GoodsteinPA.PH.exists_sigma1_ph_def`, `GoodsteinPA.PH.ph_true`,
`GoodsteinPA.Wainer.pa_provable_pi2_eventually_witnessed_below_fastGrowing`.

No `axiom` was added, no `lake update` / `lake exe cache get` was run, nothing was pushed.
