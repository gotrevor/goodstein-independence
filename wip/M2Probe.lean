/-
# M2Probe — corrected Foundation→Z bridge surface

This is a feasibility spike for the Route-A M2 probe.  It deliberately lives in `wip/`
and is not imported by `GoodsteinPA.lean`.

The point is to pin the exact API seam before grinding cases:

* Foundation's `Con(PA)` API produces a proof of the singleton formula sequent
  `{⌜⊥⌝}`, via `Theory.Proof d ⌜⊥⌝`.
* The Z engine consumes `ZDerivesEmptyR`, i.e. a `Z` derivation of the two-sided
  sequent `∅ → ⊥`, plus regularity/freshness/antecedent invariants.

Those are not definitionally the same shape.  The bridge must translate a
one-sided Foundation/Tait sequent into the two-sided Buchholz-Z sequent discipline.
-/
import GoodsteinPA.Crux2Blueprint

namespace GoodsteinPA.InternalZ

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalONote

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- The exact formula-code Foundation uses in `Theory.Consistent`. -/
noncomputable abbrev foundationBotCode : V := (⌜(⊥ : Sentence ℒₒᵣ)⌝ : V)

/-- The direct witness shape obtained from `¬ (𝗣𝗔).Consistent V`. -/
abbrev FoundationProofOfBot (d : V) : Prop :=
  (𝗣𝗔 : Theory ℒₒᵣ).Proof d (foundationBotCode : V)

/-- Unfolding checkpoint: Foundation proof of `⊥` is a derivation of the singleton sequent `{⌜⊥⌝}`. -/
example {d : V} :
    FoundationProofOfBot d ↔
      (𝗣𝗔 : Theory ℒₒᵣ).DerivationOf d ({(foundationBotCode : V)} : V) :=
  Iff.rfl

/-- The end sequent carried by a Foundation proof of bottom. -/
lemma fstIdx_of_foundationProofOfBot {d : V} (hd : FoundationProofOfBot (V := V) d) :
    fstIdx d = ({(foundationBotCode : V)} : V) :=
  hd.1

/-- The derivation component carried by a Foundation proof of bottom. -/
lemma derivation_of_foundationProofOfBot {d : V} (hd : FoundationProofOfBot (V := V) d) :
    (𝗣𝗔 : Theory ℒₒᵣ).Derivation d :=
  hd.2

/--
Foundation's consistency predicate negated is exactly the existence of the singleton-bottom proof
shape used by the corrected M2 target.
-/
lemma not_paConsistent_iff_exists_foundationProofOfBot :
    ¬(𝗣𝗔 : Theory ℒₒᵣ).Consistent V ↔
      ∃ d : V, FoundationProofOfBot (V := V) d := by
  simp [FoundationProofOfBot, foundationBotCode, Theory.Consistent, Theory.Provable]

/-- The actual Z-empty sequent consumed by `ZDerivesEmpty`. -/
noncomputable abbrev zEmptySequent : V := mkSeqt (∅ : V) (^⊥ : V)

@[simp] lemma seqAnt_zEmptySequent : seqAnt (zEmptySequent : V) = (∅ : V) := by
  simp [zEmptySequent]

@[simp] lemma seqSucc_zEmptySequent : seqSucc (zEmptySequent : V) = (^⊥ : V) := by
  simp [zEmptySequent]

/-- Packaging checkpoint: a Z derivation whose end-sequent is `∅ → ⊥` is a `ZDerivesEmpty`. -/
lemma zDerivesEmpty_of_fstIdx_zEmpty {z : V}
    (hz : ZDerivation z) (hfst : fstIdx z = (zEmptySequent : V)) :
    ZDerivesEmpty z := by
  exact ⟨hz, by rw [hfst]; simp, by rw [hfst]; simp⟩

/--
The corrected M2 bridge as a reusable proposition.  This is the obligation that should replace or wrap
the stale `foundation_bot_to_Z_empty` signature in `Crux2Blueprint.lean`.
-/
def M2Bridge : Prop :=
  ∀ {d : V}, FoundationProofOfBot (V := V) d → ∃ z : V, ZDerivesEmptyR z

/-- The downstream Z contradiction principle needed by the consistency route. -/
def NoZEmpty : Prop :=
  ∀ z : V, ZDerivesEmptyR z → False

/-- Negated Foundation consistency feeds the corrected M2 bridge directly. -/
theorem not_paConsistent_to_Z_empty_of_bridge
    (hbridge : M2Bridge (V := V))
    (hnc : ¬(𝗣𝗔 : Theory ℒₒᵣ).Consistent V) :
    ∃ z : V, ZDerivesEmptyR z := by
  obtain ⟨d, hd⟩ := not_paConsistent_iff_exists_foundationProofOfBot (V := V) |>.mp hnc
  exact hbridge hd

/-- If the Z empty derivations are contradictory, the corrected M2 bridge proves PA consistency. -/
theorem paConsistent_of_noZEmpty_and_bridge
    (hbridge : M2Bridge (V := V)) (hno : NoZEmpty (V := V)) :
    (𝗣𝗔 : Theory ℒₒᵣ).Consistent V := by
  intro hprov
  obtain ⟨d, hd⟩ := hprov
  obtain ⟨z, hz⟩ := hbridge hd
  exact hno z hz

/--
Route assembly checkpoint: once M2 is proved in the corrected shape, the existing PRWO/Z endgame
axiom is enough to derive model-internal PA consistency.
-/
theorem paConsistent_of_prwo_and_bridge
    (hprwo : InternalPRWO V) (hbridge : M2Bridge (V := V)) :
    (𝗣𝗔 : Theory ℒₒᵣ).Consistent V :=
  paConsistent_of_noZEmpty_and_bridge (V := V) hbridge
    (fun _ hz => false_of_ZDerivesEmpty hprwo hz)

/--
Route-A M2 invariant candidate.

Use a relation rather than a function: translating a one-sided Foundation/Tait sequent to Z requires
choosing a focused succedent and moving the remaining formulas to the antecedent with the appropriate
polarity.  The singleton-bottom case must realize `zEmptySequent`.
-/
class FoundationToZSequent (toZ : V → V → Prop) : Prop where
  singleton_bot :
    toZ ({(foundationBotCode : V)} : V) (zEmptySequent : V)

/--
Bridge decomposed through a sequent relation.  This is the shape to make concrete in the next probe:
first prove the rule-by-rule simulation at arbitrary related sequents, then specialize to the
singleton-bottom witness above.
-/
def FoundationToZSimulation (toZ : V → V → Prop) : Prop :=
  ∀ {d s q : V}, (𝗣𝗔 : Theory ℒₒᵣ).DerivationOf d s → toZ s q →
    ∃ z : V, ZDerivation z ∧ fstIdx z = q

/--
A regularization theorem would let the bridge first target bare `ZDerivesEmpty`, then normalize to the
stronger invariant package consumed by the existing descent engine.
-/
def ZEmptyRegularization : Prop :=
  ∀ {z : V}, ZDerivesEmpty z → ∃ zR : V, ZDerivesEmptyR zR

/--
A plain relational simulation reaches the bare Z empty-sequent target.  The extra `R` invariants are
separate work, captured by either `ZEmptyRegularization` or `FoundationToZSimulationR` below.
-/
theorem foundationProofBot_to_Z_derivesEmpty_of_sim
    {toZ : V → V → Prop} [FoundationToZSequent (V := V) toZ]
    (hsim : FoundationToZSimulation (V := V) toZ)
    {d : V} (hd : FoundationProofOfBot (V := V) d) :
    ∃ z : V, ZDerivesEmpty z := by
  obtain ⟨z, hz, hfst⟩ := hsim hd FoundationToZSequent.singleton_bot
  exact ⟨z, zDerivesEmpty_of_fstIdx_zEmpty hz hfst⟩

/-- If a plain simulation and an empty-derivation regularizer exist, the corrected M2 target follows. -/
theorem foundationProofBot_to_Z_empty_of_sim_and_regularization
    {toZ : V → V → Prop} [FoundationToZSequent (V := V) toZ]
    (hsim : FoundationToZSimulation (V := V) toZ)
    (hreg : ZEmptyRegularization (V := V))
    {d : V} (hd : FoundationProofOfBot (V := V) d) :
    ∃ z : V, ZDerivesEmptyR z := by
  obtain ⟨z, hz, hfst⟩ := hsim hd FoundationToZSequent.singleton_bot
  exact hreg (zDerivesEmpty_of_fstIdx_zEmpty hz hfst)

/--
Alternative strengthened simulation target: build the invariants during the Foundation→Z translation.
This avoids a separate regularization theorem.
-/
def FoundationToZSimulationR (toZ : V → V → Prop) : Prop :=
  ∀ {d s q : V}, (𝗣𝗔 : Theory ℒₒᵣ).DerivationOf d s → toZ s q →
    ∃ z : V, ZDerivation z ∧ fstIdx z = q ∧ ZRegular z ∧ ZFresh z ∧ ZSeqAnt z

/-- A strengthened regular simulation also discharges the corrected M2 target directly. -/
theorem foundationProofBot_to_Z_empty_of_simR
    {toZ : V → V → Prop} [FoundationToZSequent (V := V) toZ]
    (hsim : FoundationToZSimulationR (V := V) toZ)
    {d : V} (hd : FoundationProofOfBot (V := V) d) :
    ∃ z : V, ZDerivesEmptyR z := by
  obtain ⟨z, hz, hfst, hregular, hfresh, hseqAnt⟩ :=
    hsim hd FoundationToZSequent.singleton_bot
  exact ⟨z, zDerivesEmpty_of_fstIdx_zEmpty hz hfst, hregular, hfresh, hseqAnt⟩

end GoodsteinPA.InternalZ
