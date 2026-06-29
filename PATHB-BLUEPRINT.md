# Path B Blueprint: Open Capstones

Generated from `@[goodstein_blueprint ...]` attributes in Lean declarations.

| # | Declaration | Stage theorem | Category | Laps | Confidence | Uses |
|---:|---|---|---:|---:|---:|---|
| 1 | `GoodsteinPA.PathBProbe.pathB_goodsteinSentenceShape_capstone` | `GoodsteinPA.PathBProbe.pathB_goodsteinSentenceShape_stage` | debt | 1-2 | 80% | none |
| 2 | `GoodsteinPA.PathBProbe.pathB_peanoMinusAxiomLeaves_capstone` | `GoodsteinPA.PathBProbe.pathB_peanoMinusAxiomLeaves_stage` | debt | 2-4 | 70% | GoodsteinPA.PathBProbe.pathB_goodsteinSentenceShape_stage |
| 3 | `GoodsteinPA.PathBProbe.pathB_inductionAxiomShell_capstone` | `GoodsteinPA.PathBProbe.pathB_inductionAxiomShell_stage` | debt | 5-10 | 60% | GoodsteinPA.PathBProbe.pathB_peanoMinusAxiomLeaves_stage |
| 4 | `GoodsteinPA.PathBProbe.pathB_closedWitnessBudgets_capstone` | `GoodsteinPA.PathBProbe.pathB_closedWitnessBudgets_stage` | debt | 2-5 | 75% | GoodsteinPA.PathBProbe.pathB_inductionAxiomShell_stage |
| 5 | `GoodsteinPA.PathBProbe.pathB_someKStructuralEmbedding_capstone` | `GoodsteinPA.PathBProbe.pathB_someKStructuralEmbedding_stage` | debt | 6-12 | 55% | GoodsteinPA.PathBProbe.pathB_closedWitnessBudgets_stage |
| 6 | `GoodsteinPA.PathBProbe.pathB_operatorCutElimination_capstone` | `GoodsteinPA.PathBProbe.pathB_operatorCutElimination_stage` | debt | 8-16 | 50% | GoodsteinPA.PathBProbe.pathB_someKStructuralEmbedding_stage |
| 7 | `GoodsteinPA.PathBProbe.pathB_subformulaProjection_capstone` | `GoodsteinPA.PathBProbe.pathB_subformulaProjection_stage` | debt | 4-8 | 55% | GoodsteinPA.PathBProbe.pathB_operatorCutElimination_stage |
| 8 | `GoodsteinPA.PathBProbe.pathB_goodsteinFragmentExtraction_capstone` | `GoodsteinPA.PathBProbe.pathB_goodsteinFragmentExtraction_stage` | debt | 2-5 | 65% | GoodsteinPA.PathBProbe.pathB_subformulaProjection_stage |
| 9 | `GoodsteinPA.PathBProbe.pathB_terminalRouteBridge_capstone` | `GoodsteinPA.PathBProbe.pathB_terminalRouteBridge_stage` | debt | 1-3 | 80% | GoodsteinPA.PathBProbe.pathB_goodsteinFragmentExtraction_stage |

## Outline

### 1. `GoodsteinPA.PathBProbe.pathB_goodsteinSentenceShape_capstone`

- Stage theorem: `GoodsteinPA.PathBProbe.pathB_goodsteinSentenceShape_stage`
- Kind: `capstone_axiom`
- Category claim: `debt`
- Estimate: 1-2 laps, 80% confidence
- Summary: Normalize a PA proof of the encoded Goodstein sentence to the closed sequent shape consumed by the bounded embedding.
- Literature / evidence:
  - Kirby-Paris 1982, Goodstein sentence as the PA target
  - GoodsteinPA.Encoding / GoodsteinPA.Bridge: local faithful encoding and standard-model bridge

### 2. `GoodsteinPA.PathBProbe.pathB_peanoMinusAxiomLeaves_capstone`

- Stage theorem: `GoodsteinPA.PathBProbe.pathB_peanoMinusAxiomLeaves_stage`
- Kind: `capstone_axiom`
- Category claim: `debt`
- Estimate: 2-4 laps, 70% confidence
- Summary: Discharge the finite PA-minus and equality axiom leaves in the witness-bounded operator calculus.
- Literature / evidence:
  - Foundation PeanoMinus.Basic: finite PA-minus and equality axiom base
  - Towsner, Goodstein's Theorem, epsilon_0, and Unprovability, Section 16: embedding PA axioms into Z_infty
  - Buchholz lecture notes, Section 5 axioms; local X-free/value-congruent axiom leaves

### 3. `GoodsteinPA.PathBProbe.pathB_inductionAxiomShell_capstone`

- Stage theorem: `GoodsteinPA.PathBProbe.pathB_inductionAxiomShell_stage`
- Kind: `capstone_axiom`
- Category claim: `debt`
- Estimate: 5-10 laps, 60% confidence
- Summary: Simulate the PA induction-axiom shell without losing the finite witness budget.
- Literature / evidence:
  - Towsner Sections 16 and 18: PA induction through the infinitary calculus
  - Buchholz Theorem 5.5 / local metaInduction_cong pattern for induction axioms
  - Foundation Arithmetic.Schemata: succInd and InductionScheme

### 4. `GoodsteinPA.PathBProbe.pathB_closedWitnessBudgets_capstone`

- Stage theorem: `GoodsteinPA.PathBProbe.pathB_closedWitnessBudgets_stage`
- Kind: `capstone_axiom`
- Category claim: `debt`
- Estimate: 2-5 laps, 75% confidence
- Summary: Extract finite K budgets for every Foundation existential and closed-witness step.
- Literature / evidence:
  - Towsner Section 15: witness-bounded derivations
  - Towsner Section 19.6: forall/existential cut interaction and witness bound
  - GoodsteinPA.OperatorZinfty.embedding_closedTermExI_someK_probe and ZekdSomeK.lift

### 5. `GoodsteinPA.PathBProbe.pathB_someKStructuralEmbedding_capstone`

- Stage theorem: `GoodsteinPA.PathBProbe.pathB_someKStructuralEmbedding_stage`
- Kind: `capstone_axiom`
- Category claim: `debt`
- Estimate: 6-12 laps, 55% confidence
- Summary: Embed the whole PA proof into the someK witness-bounded operator calculus.
- Literature / evidence:
  - Towsner Theorems 16.1/16.5/16.7: embedding PA proofs into Z_infty
  - GoodsteinPA.OperatorZinfty: ZekdSomeK structural combinators

### 6. `GoodsteinPA.PathBProbe.pathB_operatorCutElimination_capstone`

- Stage theorem: `GoodsteinPA.PathBProbe.pathB_operatorCutElimination_stage`
- Kind: `capstone_axiom`
- Category claim: `debt`
- Estimate: 8-16 laps, 50% confidence
- Summary: Run bounded operator cut-elimination while preserving a finite witness budget after ordinal lift.
- Literature / evidence:
  - Towsner Section 19, especially Theorems 19.5, 19.6, 19.7, 19.9: cut elimination
  - GoodsteinPA.OperatorZinfty: control-ordinal witness-bounded operator calculus

### 7. `GoodsteinPA.PathBProbe.pathB_subformulaProjection_capstone`

- Stage theorem: `GoodsteinPA.PathBProbe.pathB_subformulaProjection_stage`
- Kind: `capstone_axiom`
- Category claim: `debt`
- Estimate: 4-8 laps, 55% confidence
- Summary: Project the cut-free operator derivation to the subformula fragment consumed by the lower-bound theorem.
- Literature / evidence:
  - Towsner Section 17.1: lower bound for witness-bounded cut-free derivations
  - GoodsteinPA.LowerBound: LowerBoundHardy.B and allInv/mono_k terminal calculus

### 8. `GoodsteinPA.PathBProbe.pathB_goodsteinFragmentExtraction_capstone`

- Stage theorem: `GoodsteinPA.PathBProbe.pathB_goodsteinFragmentExtraction_stage`
- Kind: `capstone_axiom`
- Category claim: `debt`
- Estimate: 2-5 laps, 65% confidence
- Summary: Identify the projected derivation with the concrete Goodstein-fragment terminal object.
- Literature / evidence:
  - Towsner Section 17.1: Goodstein fragment forall x exists y g_y(x)=0
  - GoodsteinPA.LowerBound.lowerBound_hardy_selfcontained: concrete Hardy/Goodstein lower bound

### 9. `GoodsteinPA.PathBProbe.pathB_terminalRouteBridge_capstone`

- Stage theorem: `GoodsteinPA.PathBProbe.pathB_terminalRouteBridge_stage`
- Kind: `capstone_axiom`
- Category claim: `debt`
- Estimate: 1-3 laps, 80% confidence
- Summary: Assemble the staged capstones into the terminal RouteBCapstone consumed by the lower-bound contradiction.
- Literature / evidence:
  - Towsner Section 20: assembly of unprovability from bounded embedding, cut elimination, and lower bound
  - Kirby-Paris 1982: PA unprovability of Goodstein's theorem
  - GoodsteinPA.PathBProbe.no_routeBCapstone: terminal contradiction from the promoted lower bound

## Audit

Run the stage theorem through `#print axioms` to see the actual kernel-level open assumptions.
