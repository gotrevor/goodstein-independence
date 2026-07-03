# Codex M2 Probe Review - 2026-06-28

## What I Changed

I added a focused Lean probe:

- `wip/M2Probe.lean`

The probe imports `GoodsteinPA.Crux2Blueprint` and isolates the exact interface needed for M2:

- the Foundation inconsistency witness shape,
- the Z empty-sequent target shape,
- the missing one-sided-to-two-sided simulation boundary,
- the extra regularity/freshness/antecedent invariants required by `ZDerivesEmptyR`.

Verification run:

```bash
lake env lean wip/M2Probe.lean
```

Result: `wip/M2Probe.lean` typechecks with no warnings and no `sorry`. The open bridge is represented as
the proposition `M2Bridge`, not as an unproved theorem body.

I also flagged the two stale in-repo bridge stubs/comments:

- `src/GoodsteinPA/Crux2Blueprint.lean`, around the live `foundation_bot_to_Z_empty` stub.
- `src/GoodsteinPA/InternalZ.lean`, around the older C0.5 planning block.

## Main Finding

The current M2 route should be corrected before more work is invested in individual PA axiom cases.

Foundation consistency exposes a proof of bottom as:

```lean
(𝗣𝗔 : Theory ℒₒᵣ).Proof d (⌜(⊥ : Sentence ℒₒᵣ)⌝ : V)
```

By definitional unfolding, this is:

```lean
(𝗣𝗔 : Theory ℒₒᵣ).DerivationOf d ({⌜⊥⌝} : V)
```

That means the root sequent is the singleton `{⌜⊥⌝}`.

The existing M2 stub in `src/GoodsteinPA/Crux2Blueprint.lean` starts from:

```lean
theorem foundation_bot_to_Z_empty
    {d : V}
    (hd : (𝗣𝗔 : Theory ℒₒᵣ).Derivation d)
    (h0 : fstIdx d = ∅) :
    ∃ z : V, ZDerivesEmptyR z := sorry
```

This does not match the witness produced by `¬ Consistent PA`. The bridge needs to start from `Proof d ⌜⊥⌝`, or from `DerivationOf d {⌜⊥⌝}`, not from a Foundation derivation whose `fstIdx` is empty.

## Probe Shape

The probe introduces the corrected input shape:

```lean
abbrev FoundationProofOfBot (d : V) : Prop :=
  (𝗣𝗔 : Theory ℒₒᵣ).Proof d (foundationBotCode : V)
```

and the corresponding Z empty sequent:

```lean
noncomputable abbrev zEmptySequent : V := mkSeqt (∅ : V) (^⊥ : V)
```

It then records the direct target as a proposition:

```lean
def M2Bridge : Prop :=
  ∀ {d : V}, FoundationProofOfBot (V := V) d → ∃ z : V, ZDerivesEmptyR z
```

This is the interface I would use as the M2 gate.

The probe also proves the exact consistency-witness equivalence:

```lean
lemma not_paConsistent_iff_exists_foundationProofOfBot :
    ¬(𝗣𝗔 : Theory ℒₒᵣ).Consistent V ↔
      ∃ d : V, FoundationProofOfBot (V := V) d
```

and the route assembly:

```lean
theorem paConsistent_of_prwo_and_bridge
    (hprwo : InternalPRWO V) (hbridge : M2Bridge (V := V)) :
    (𝗣𝗔 : Theory ℒₒᵣ).Consistent V
```

So there is no remaining top-level wiring ambiguity: if the corrected M2 bridge exists, the current
PRWO/Z endgame is enough to derive the model-internal PA consistency statement.

## Second Finding

A bare derivation simulation is not enough for the live contradiction path, but the split is now precise.

The natural relational simulation has this shape:

```lean
def FoundationToZSimulation (toZ : V → V → Prop) : Prop :=
  ∀ {d s q : V},
    (𝗣𝗔 : Theory ℒₒᵣ).DerivationOf d s → toZ s q →
      ∃ z : V, ZDerivation z ∧ fstIdx z = q
```

For the bottom singleton, the probe proves this is enough to produce bare `ZDerivesEmpty`, provided the
relation maps `{⌜⊥⌝}` to `mkSeqt ∅ ^⊥`:

```lean
theorem foundationProofBot_to_Z_derivesEmpty_of_sim
    {toZ : V → V → Prop} [FoundationToZSequent (V := V) toZ]
    (hsim : FoundationToZSimulation (V := V) toZ)
    {d : V} (hd : FoundationProofOfBot (V := V) d) :
    ∃ z : V, ZDerivesEmpty z
```

But the live route needs `ZDerivesEmptyR`, which also requires:

- `ZRegular z`,
- `ZFresh z`,
- `ZSeqAnt z`.

Those invariants are not automatic from `ZDerivation z ∧ fstIdx z = mkSeqt ∅ ^⊥`. The probe now factors
the two exact options.

Option A: prove a regularization theorem:

```lean
def ZEmptyRegularization : Prop :=
  ∀ {z : V}, ZDerivesEmpty z → ∃ zR : V, ZDerivesEmptyR zR
```

Then the plain simulation suffices:

```lean
theorem foundationProofBot_to_Z_empty_of_sim_and_regularization
    (hsim : FoundationToZSimulation (V := V) toZ)
    (hreg : ZEmptyRegularization (V := V))
    {d : V} (hd : FoundationProofOfBot (V := V) d) :
    ∃ z : V, ZDerivesEmptyR z
```

and instantiates the bridge/endgame:

```lean
theorem M2Bridge_of_sim_and_regularization
    (hsim : FoundationToZSimulation (V := V) toZ)
    (hreg : ZEmptyRegularization (V := V)) :
    M2Bridge (V := V)

theorem paConsistent_of_prwo_sim_and_regularization
    (hprwo : InternalPRWO V)
    (hsim : FoundationToZSimulation (V := V) toZ)
    (hreg : ZEmptyRegularization (V := V)) :
    (𝗣𝗔 : Theory ℒₒᵣ).Consistent V
```

Option B: strengthen the simulation target:

```lean
def FoundationToZSimulationR (toZ : V → V → Prop) : Prop :=
  ∀ {d s q : V}, (𝗣𝗔 : Theory ℒₒᵣ).DerivationOf d s → toZ s q →
    ∃ z : V, ZDerivation z ∧ fstIdx z = q ∧ ZRegular z ∧ ZFresh z ∧ ZSeqAnt z
```

Then the bridge target follows directly.

The probe also proves the corresponding bridge/endgame wrappers:

```lean
theorem M2Bridge_of_simR
    (hsim : FoundationToZSimulationR (V := V) toZ) :
    M2Bridge (V := V)

theorem paConsistent_of_prwo_simR
    (hprwo : InternalPRWO V)
    (hsim : FoundationToZSimulationR (V := V) toZ) :
    (𝗣𝗔 : Theory ℒₒᵣ).Consistent V
```

So M2 needs either:

- a strengthened simulation that constructs regular/fresh/antecedent-disciplined Z proofs directly, or
- a later normalization theorem from `ZDerivesEmpty` to `ZDerivesEmptyR`.

## Why The Cheap Cases Are Misleading

The easy PA arithmetic axioms are not representative of the actual hard part.

Foundation proof codes use the Tait/sequent derivation constructors, including:

- structural rules such as weakening, shift, and cut,
- quantifier rules,
- theory axiom leaves through `axm s p` with `p ∈ T.Δ₁Class`.

For PA, the induction axioms enter through the theory-membership side, not as native Z induction nodes. The Z calculus has `zInd`, but using it for Foundation PA induction requires decoding the Foundation PA axiom membership and proving it corresponds to a Z-provable induction sequent. That is the real transfer problem.

Bryce-Goré is useful as a conceptual sanity check, but its `Peano.v` source is an explicit Hilbert-style inductive PA and its target shares syntax with the source. It does not remove the need to translate Foundation's one-sided Tait proof codes and `Δ₁Class` theory axiom leaves.

## Induction Leaf Sizing

I added a compiler-checked split between the standard syntactic induction axiom case and the actual
internal axm-leaf case.

The standard quoted case is small:

```lean
def StandardPAInductionAxiomCode (p : V) : Prop :=
  ∃ φ : Semiformula ℒₒᵣ ℕ 1,
    p = (⌜(.univCl (succInd φ) : Sentence ℒₒᵣ)⌝ : V)

lemma standardPAInductionAxiomCode_mem_paDelta1Class {p : V}
    (hp : StandardPAInductionAxiomCode (V := V) p) :
    p ∈ (𝗣𝗔 : Theory ℒₒᵣ).Δ₁Class
```

The probe also checks the expected syntactic decomposition:

```lean
lemma pa_mem_iff_peanoMinus_or_induction {σ : Sentence ℒₒᵣ} :
    σ ∈ (𝗣𝗔 : Theory ℒₒᵣ) ↔
      σ ∈ (𝗣𝗔⁻ : Theory ℒₒᵣ) ∨ σ ∈ InductionScheme ℒₒᵣ Set.univ

lemma inductionScheme_mem_iff_succInd {σ : Sentence ℒₒᵣ} :
    σ ∈ InductionScheme ℒₒᵣ Set.univ ↔
      ∃ φ : Semiformula ℒₒᵣ ℕ 1, σ = .univCl (succInd φ)
```

But that is not enough for M2. The actual Foundation `axm` case receives an arbitrary model code
`p : V`, not necessarily an externally standard quote. For universal induction, Foundation's real
recognizer is the code predicate `InductionUnivR p` from `InductionSchemeDelta1.lean`.

The probe now names the hard obligation directly:

```lean
def PAInductionAxmCode (p : V) : Prop :=
  InductionUnivR p

def PAInductionAxmCoreData (p : V) : Prop :=
  ∃ m ≤ p, ∃ b ≤ p,
    p = qqAlls b m ∧ IsUFormula ℒₒᵣ b ∧ shift ℒₒᵣ b = b ∧ bv ℒₒᵣ b = m
    ∧ ∃ K ≤ subst ℒₒᵣ (fvarVec m) b,
        IsSemiformula ℒₒᵣ 1 K ∧ subst ℒₒᵣ (fvarVec m) b = indBodyVal K

lemma PAInductionAxmCode_iff_coreData {p : V} :
    PAInductionAxmCode (V := V) p ↔ PAInductionAxmCoreData (V := V) p
```

The arbitrary PA axm-code branch now also splits cleanly:

```lean
def PAPeanoMinusAxmCode (p : V) : Prop :=
  p ∈ (𝗣𝗔⁻ : Theory ℒₒᵣ).Δ₁Class

lemma paDelta1Class_iff_peanoMinus_or_inductionAxmCode {p : V} :
    p ∈ (𝗣𝗔 : Theory ℒₒᵣ).Δ₁Class ↔
      PAPeanoMinusAxmCode (V := V) p ∨ PAInductionAxmCode (V := V) p
```

and the full PA axm leaf is reduced to finite `PA⁻` leaves plus the universal-induction branch:

```lean
def PAPeanoMinusLeafSimulation (toZ : V → V → Prop) : Prop :=
  ∀ {s p q : V}, p ∈ s → PAPeanoMinusAxmCode (V := V) p → toZ s q →
    ∃ z : V, ZDerivation z ∧ fstIdx z = q

def PAAxmLeafSimulation (toZ : V → V → Prop) : Prop :=
  ∀ {s p q : V}, p ∈ s → p ∈ (𝗣𝗔 : Theory ℒₒᵣ).Δ₁Class → toZ s q →
    ∃ z : V, ZDerivation z ∧ fstIdx z = q

def PAInductionLeafSimulation (toZ : V → V → Prop) : Prop :=
  ∀ {s p q : V}, p ∈ s → PAInductionAxmCode (V := V) p → toZ s q →
    ∃ z : V, ZDerivation z ∧ fstIdx z = q

theorem PAAxmLeafSimulation_of_peanoMinus_and_induction
    (hpm : PAPeanoMinusLeafSimulation (V := V) toZ)
    (hind : PAInductionLeafSimulation (V := V) toZ) :
    PAAxmLeafSimulation (V := V) toZ
```

This is the honest sizing point. Proving the standard `succInd φ` code is a PA axiom is bounded. Proving
the Z simulation for arbitrary `p` satisfying `InductionUnivR p` is the hard part.

Net read for Path A: the plumbing is cleaner, but not rosier. The compiler now confirms the hard branch
is exactly isolated, and it is the branch that carries closure/body/core-code data rather than a ready
typed formula. That makes the decision sharper, not easier.

## Native Z-Ind Test

I took the next decisive step and checked the native `zInd` handoff directly.

The probe proves the constructor wrapper:

```lean
lemma zDerivation_zInd_intro_probe {s at' p d0 d1 : V}
    (hd0 : ZDerivation d0) (hd1 : ZDerivation d1)
    (hwff : zIndWff (zInd s at' p d0 d1)) :
    ZDerivation (zInd s at' p d0 d1)
```

and the crucial conclusion-shape fact:

```lean
lemma zIndWff_conclusion_is_instance {s at' p d0 d1 : V}
    (hwff : zIndWff (zInd s at' p d0 d1)) :
    seqSucc s = substs1 ℒₒᵣ (π₂ at') p
```

So native `zInd` concludes an instance `F(t)`. It does not by itself derive the closed PA induction
axiom code `∀* (succInd F)`. It also requires two premise derivations:

```lean
def NativeZIndInstanceDerivation (q K : V) : Prop :=
  ∃ at' d0 d1 : V,
    ZDerivation d0 ∧ ZDerivation d1 ∧ zIndWff (zInd q at' K d0 d1)
```

The remaining hard object is therefore the shell around native induction:

```lean
def PAInductionAxiomShellSimulation (toZ : V → V → Prop) : Prop :=
  ∀ {s p q m b K : V},
    p ∈ s →
    p = qqAlls b m →
    IsUFormula ℒₒᵣ b →
    shift ℒₒᵣ b = b →
    bv ℒₒᵣ b = m →
    IsSemiformula ℒₒᵣ 1 K →
    subst ℒₒᵣ (fvarVec m) b = indBodyVal K →
    toZ s q →
    ∃ z : V, ZDerivation z ∧ fstIdx z = q
```

The probe proves this is exactly enough for the hard PA branch:

```lean
theorem PAInductionLeafSimulation_of_shell
    (hshell : PAInductionAxiomShellSimulation (V := V) toZ) :
    PAInductionLeafSimulation (V := V) toZ

theorem PAAxmLeafSimulation_of_peanoMinus_and_shell
    (hpm : PAPeanoMinusLeafSimulation (V := V) toZ)
    (hshell : PAInductionAxiomShellSimulation (V := V) toZ) :
    PAAxmLeafSimulation (V := V) toZ
```

This is the decision point. The old comfort claim "PA induction maps directly to native `zInd`" is false
at the leaf level. Native `zInd` is one ingredient inside the shell; it is not the shell.

## Recommendation

Treat M2 viability as a hypothesis to test, not as the standing conclusion. The findings remove the
main reason M2 looked cheap: Foundation PA induction is not handed over directly to native `zInd`; it
arrives as a `Δ₁Class` theory-axiom leaf that still has to be decoded and translated.

Continue only under a strict gate, with hard stop at lap 171:

1. Replace or wrap the current stub with the exact Foundation witness shape:

   ```lean
   theorem foundation_proof_bot_to_Z_empty
       {d : V}
       (hd : (𝗣𝗔 : Theory ℒₒᵣ).Proof d (foundationBotCode : V)) :
       ∃ z : V, ZDerivesEmptyR z := ...
   ```

2. Define a concrete `FoundationToZSequent` relation, rather than treating formula translation as implicit.

3. Prove the singleton-bottom relation:

   ```lean
   toZ ({foundationBotCode} : V) (mkSeqt ∅ ^⊥)
   ```

4. Prove one genuinely structural Foundation rule case, preferably `cutRule` or `allIntro`.

5. Prove one PA induction axiom leaf case through Foundation's `axm s p` / `p ∈ 𝗣𝗔.Δ₁Class` interface.

If item 2 or item 5 expands into a large new formalization, that is `PIVOT-B`. Do not narrow the probe
again to dodge that wall. If both land as bounded lemmas, then M2 becomes viable again; until then the
read is pivot-leaning.

## Concrete Next Edits

I would make the next Lean edits in this order:

1. Add the corrected theorem statement next to `foundation_bot_to_Z_empty`, while keeping the old stub temporarily if other files depend on it.

2. Define the concrete sequent relation. My best guess is that it should focus one one-sided formula into the Z succedent and place the remaining formulas into the Z antecedent under the needed polarity/dual operation.

3. Decide whether the simulation target is:

   ```lean
   ∃ z, ZDerivation z ∧ fstIdx z = q
   ```

   plus a separate regularization theorem, or directly:

   ```lean
   ∃ z, ZDerivation z ∧ fstIdx z = q ∧ ZRegular z ∧ ZFresh z ∧ ZSeqAnt z
   ```

4. Only after that, spend effort on PA axiom leaves. The first meaningful axiom case should be an induction axiom, not a Peano-minus arithmetic axiom.

## Verdict

M2 remains a useful probe, not a favored route. The current evidence tilts toward pivot unless the
concrete one-sided-to-two-sided relation and the PA induction `Δ₁Class` leaf both stay bounded. The next
work should size those two items honestly, and stop at lap 171 if either one turns into a new
formalization.

## Follow-up Checked Work

Update: `wip/M2Probe.lean` now discharges the first structural checkpoints from the recommendation above.
New checked pieces:

```lean
@[simp] lemma foundationBotCode_eq_zFalsum

def FoundationToZFocus
def FoundationToZMemFocus

lemma FoundationToZFocus.singleton_bot
lemma FoundationToZMemFocus.singleton_bot

lemma paDerivationOf_cutRule_of_premises

theorem FoundationToZMemFocus.cutPremiseTranslations

theorem foundationCutRule_simulation_of_expansion
theorem foundationCutRule_simulationR_of_expansionR
```

Read: the Foundation bottom code is definitionally the Z falsum code, two concrete focus relations now
instantiate the endpoint interface, and the Foundation `cutRule` case is reduced to explicit translation
threading plus a Z cut combiner.  The strengthened cut adapter carries `ZRegular`, `ZFresh`, and `ZSeqAnt`
through the obligation instead of hiding those invariants in the recursion.

The membership-focus relation is intentionally not the final faithful one-sided-to-two-sided translation:
it chooses an existing one-sided formula as the Z succedent and ignores the rest.  Its value is that cut
premise threading is now checked:

```lean
toZ s q → ∃ qPos qNeg,
  toZ (insert p s) qPos ∧ toZ (insert (neg ℒₒᵣ p) s) qNeg
```

The remaining cut work is therefore concrete: replace this probe relation with the faithful antecedent
translation and prove the actual Z cut combiner.  The remaining axiom work is unchanged: the PA induction
leaf still has to pass through the `axm s p` / `p ∈ 𝗣𝗔.Δ₁Class` interface.
