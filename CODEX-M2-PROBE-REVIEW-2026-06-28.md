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

Option B: strengthen the simulation target:

```lean
def FoundationToZSimulationR (toZ : V → V → Prop) : Prop :=
  ∀ {d s q : V}, (𝗣𝗔 : Theory ℒₒᵣ).DerivationOf d s → toZ s q →
    ∃ z : V, ZDerivation z ∧ fstIdx z = q ∧ ZRegular z ∧ ZFresh z ∧ ZSeqAnt z
```

Then the bridge target follows directly.

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

## Recommendation

Continue M2 only under a stricter 5-lap gate:

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

If item 2 or item 5 expands into a large new formalization, I would pivot away from M2. If those two land cleanly, M2 remains viable.

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

M2 is still the right probe, but the route should be narrowed. The current stub is not aligned with Foundation's consistency API, and the decisive work is not the simple arithmetic axiom cases. The decisive work is the concrete one-sided-to-two-sided simulation plus either regularization or invariant-preserving construction, with the PA induction axiom leaf as the hard axiom case.
