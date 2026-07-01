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

/-- Foundation's quoted bottom formula is the same internal formula code Z uses for `⊥`. -/
@[simp] lemma foundationBotCode_eq_zFalsum : (foundationBotCode : V) = (^⊥ : V) := by
  rfl

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

/-- A first concrete one-sided-to-two-sided translation: focus a singleton Foundation sequent. -/
noncomputable abbrev foundationFocusSequent (p : V) : V := mkSeqt (∅ : V) p

@[simp] lemma seqAnt_foundationFocusSequent (p : V) :
    seqAnt (foundationFocusSequent p : V) = (∅ : V) := by
  simp [foundationFocusSequent]

@[simp] lemma seqSucc_foundationFocusSequent (p : V) :
    seqSucc (foundationFocusSequent p : V) = p := by
  simp [foundationFocusSequent]

/--
Concrete singleton-focus relation for the M2 probe.

This is intentionally small: it proves the bottom input is not mysterious (`{⌜⊥⌝}` maps to `∅→⊥`),
while making clear that the full bridge still needs a broader relation for non-singleton rule premises.
-/
def FoundationToZFocus (s q : V) : Prop :=
  ∃ p : V, s = ({p} : V) ∧ q = foundationFocusSequent p

/--
A slightly broader concrete focus relation: pick a formula already present in the one-sided Foundation
sequent and use it as the Z succedent.

This still does not move the remaining one-sided formulas into the Z antecedent; it is a deliberately small
probe relation for testing endpoint and structural-premise plumbing.
-/
def FoundationToZMemFocus (s q : V) : Prop :=
  ∃ p : V, p ∈ s ∧ q = foundationFocusSequent p

/-- The corrected Foundation bottom sequent maps to the Z empty sequent under singleton focus. -/
lemma FoundationToZFocus.singleton_bot :
    FoundationToZFocus (V := V) ({(foundationBotCode : V)} : V) (zEmptySequent : V) := by
  refine ⟨foundationBotCode, rfl, ?_⟩
  simp [foundationFocusSequent, zEmptySequent]

/-- The corrected Foundation bottom sequent also maps to the Z empty sequent under membership focus. -/
lemma FoundationToZMemFocus.singleton_bot :
    FoundationToZMemFocus (V := V) ({(foundationBotCode : V)} : V) (zEmptySequent : V) := by
  refine ⟨foundationBotCode, by simp, ?_⟩
  simp [foundationFocusSequent, zEmptySequent]

/-- Packaging checkpoint: a Z derivation whose end-sequent is `∅ → ⊥` is a `ZDerivesEmpty`. -/
lemma zDerivesEmpty_of_fstIdx_zEmpty {z : V}
    (hz : ZDerivation z) (hfst : fstIdx z = (zEmptySequent : V)) :
    ZDerivesEmpty z := by
  exact ⟨hz, by rw [hfst]; simp, by rw [hfst]; simp⟩

/-- A Z derivation of the focused `⌜⊥⌝` singleton is already a bare Z empty derivation. -/
lemma zDerivesEmpty_of_fstIdx_foundationFocusBot {z : V}
    (hz : ZDerivation z) (hfst : fstIdx z = foundationFocusSequent (foundationBotCode : V)) :
    ZDerivesEmpty z := by
  apply zDerivesEmpty_of_fstIdx_zEmpty hz
  rw [hfst]
  simp [foundationFocusSequent, zEmptySequent]

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

/-! ## PA axiom leaf sizing

The bridge's `axm` case receives an arbitrary model code `p : V` with `p ∈ 𝗣𝗔.Δ₁Class`.
For standard quoted sentences, Foundation gives simp lemmas back to syntactic membership.  For the
actual internal induction case, the recognizer is the substantial `InductionUnivR` code predicate from
`InductionSchemeDelta1.lean`, not merely a meta-level `∃ φ`.
-/

/-- A Foundation theory-axiom leaf for PA. -/
def PAAxmLeaf (s p : V) : Prop :=
  p ∈ s ∧ p ∈ (𝗣𝗔 : Theory ℒₒᵣ).Δ₁Class

/-- The internal recognizer side of a PA induction axiom leaf. -/
def PAInductionAxmCode (p : V) : Prop :=
  InductionUnivR p

/-- Expanded data carried by Foundation's universal-induction recognizer. -/
def PAInductionAxmCoreData (p : V) : Prop :=
  ∃ m ≤ p, ∃ b ≤ p,
    p = qqAlls b m ∧ IsUFormula ℒₒᵣ b ∧ shift ℒₒᵣ b = b ∧ bv ℒₒᵣ b = m
    ∧ ∃ K ≤ subst ℒₒᵣ (fvarVec m) b,
        IsSemiformula ℒₒᵣ 1 K ∧ subst ℒₒᵣ (fvarVec m) b = indBodyVal K

/-- `InductionUnivR` is already the expanded closure/substitution/core-code package. -/
lemma PAInductionAxmCode_iff_coreData {p : V} :
    PAInductionAxmCode (V := V) p ↔ PAInductionAxmCoreData (V := V) p := by
  rfl

/-- The Peano-minus side of a PA theory-axiom leaf. -/
def PAPeanoMinusAxmCode (p : V) : Prop :=
  p ∈ (𝗣𝗔⁻ : Theory ℒₒᵣ).Δ₁Class

/-- The smaller, standard-only induction axiom shape. This is not enough for an arbitrary axm leaf. -/
def StandardPAInductionAxiomCode (p : V) : Prop :=
  ∃ φ : Semiformula ℒₒᵣ ℕ 1, p = (⌜(.univCl (succInd φ) : Sentence ℒₒᵣ)⌝ : V)

/-- Standard quoted PA theory membership reduces to syntactic membership. -/
lemma paDelta1Class_quote_iff {σ : Sentence ℒₒᵣ} :
    (⌜σ⌝ : V) ∈ (𝗣𝗔 : Theory ℒₒᵣ).Δ₁Class ↔ σ ∈ (𝗣𝗔 : Theory ℒₒᵣ) := by
  simp

/-- PA syntactic membership splits into `PA⁻` and universal induction. -/
lemma pa_mem_iff_peanoMinus_or_induction {σ : Sentence ℒₒᵣ} :
    σ ∈ (𝗣𝗔 : Theory ℒₒᵣ) ↔
      σ ∈ (𝗣𝗔⁻ : Theory ℒₒᵣ) ∨ σ ∈ InductionScheme ℒₒᵣ Set.univ := by
  simp [Peano, Theory.add_def]

/-- Universal induction-scheme membership is exactly the `succInd` axiom shape. -/
lemma inductionScheme_mem_iff_succInd {σ : Sentence ℒₒᵣ} :
    σ ∈ InductionScheme ℒₒᵣ Set.univ ↔
      ∃ φ : Semiformula ℒₒᵣ ℕ 1, σ = .univCl (succInd φ) := by
  constructor
  · rintro ⟨φ, _, rfl⟩
    exact ⟨φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨φ, trivial, rfl⟩

/-- Every standard quoted induction axiom is recognized as a PA theory axiom code. -/
lemma standard_succInd_mem_paDelta1Class (φ : Semiformula ℒₒᵣ ℕ 1) :
    (⌜(.univCl (succInd φ) : Sentence ℒₒᵣ)⌝ : V) ∈
      (𝗣𝗔 : Theory ℒₒᵣ).Δ₁Class := by
  rw [paDelta1Class_quote_iff, pa_mem_iff_peanoMinus_or_induction]
  exact Or.inr (mem_InductionScheme_of_mem (C := Set.univ) trivial)

/-- Standard induction axiom codes imply PA theory-code membership. -/
lemma standardPAInductionAxiomCode_mem_paDelta1Class {p : V}
    (hp : StandardPAInductionAxiomCode (V := V) p) :
    p ∈ (𝗣𝗔 : Theory ℒₒᵣ).Δ₁Class := by
  rcases hp with ⟨φ, rfl⟩
  exact standard_succInd_mem_paDelta1Class (V := V) φ

/--
Arbitrary PA axm-code membership splits into the finite `PA⁻` recognizer or the universal induction
recognizer.  This is the real axm-leaf case split for M2; the induction branch is still internal
`InductionUnivR p`, not an external standard quote.
-/
lemma paDelta1Class_iff_peanoMinus_or_inductionAxmCode {p : V} :
    p ∈ (𝗣𝗔 : Theory ℒₒᵣ).Δ₁Class ↔
      PAPeanoMinusAxmCode (V := V) p ∨ PAInductionAxmCode (V := V) p := by
  unfold PAPeanoMinusAxmCode PAInductionAxmCode Theory.Δ₁Class
  change
    (V ⊧/![p] (PeanoMinus.delta1.ch ⋎ chUniv).val) ↔
      (V ⊧/![p] PeanoMinus.delta1.ch.val) ∨ InductionUnivR p
  simp only [HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq, InductionUnivR.defined.iff]
  simp

/-- Standard quoted induction axioms give standard PA axm leaves when inserted into a root sequent. -/
lemma standard_succInd_paAxmLeaf {s : V} (φ : Semiformula ℒₒᵣ ℕ 1)
    (hp : (⌜(.univCl (succInd φ) : Sentence ℒₒᵣ)⌝ : V) ∈ s) :
    PAAxmLeaf (V := V) s (⌜(.univCl (succInd φ) : Sentence ℒₒᵣ)⌝ : V) :=
  ⟨hp, standard_succInd_mem_paDelta1Class (V := V) φ⟩

/--
The actual hard induction leaf obligation: simulate a Foundation `axm s p` where `p` satisfies the
internal universal-induction recognizer, not just where `p` is externally a standard quoted axiom.
-/
def PAInductionLeafSimulation (toZ : V → V → Prop) : Prop :=
  ∀ {s p q : V}, p ∈ s → PAInductionAxmCode (V := V) p → toZ s q →
    ∃ z : V, ZDerivation z ∧ fstIdx z = q

/-- The finite `PA⁻` side of the PA axm-leaf simulation. -/
def PAPeanoMinusLeafSimulation (toZ : V → V → Prop) : Prop :=
  ∀ {s p q : V}, p ∈ s → PAPeanoMinusAxmCode (V := V) p → toZ s q →
    ∃ z : V, ZDerivation z ∧ fstIdx z = q

/-- The whole PA axm-leaf simulation obligation. -/
def PAAxmLeafSimulation (toZ : V → V → Prop) : Prop :=
  ∀ {s p q : V}, p ∈ s → p ∈ (𝗣𝗔 : Theory ℒₒᵣ).Δ₁Class → toZ s q →
    ∃ z : V, ZDerivation z ∧ fstIdx z = q

/--
The PA axm leaf splits cleanly: the only non-finite branch is `InductionUnivR`. This is a useful
Path-A checkpoint because it prevents the bridge from hiding the induction work inside `PA.Δ₁Class`.
-/
theorem PAAxmLeafSimulation_of_peanoMinus_and_induction
    {toZ : V → V → Prop}
    (hpm : PAPeanoMinusLeafSimulation (V := V) toZ)
    (hind : PAInductionLeafSimulation (V := V) toZ) :
    PAAxmLeafSimulation (V := V) toZ := by
  intro s p q hp hPA htoZ
  rcases (paDelta1Class_iff_peanoMinus_or_inductionAxmCode (V := V) (p := p)).mp hPA with hpmc | hindc
  · exact hpm hp hpmc htoZ
  · exact hind hp hindc htoZ

/-! ## Native Z-Ind sizing

The Foundation PA induction leaf is a closed induction-axiom code.  A native Z `Ind` node is different:
it is an inference rule needing base and step premise derivations, and its conclusion is an instance
`F(t)`.  The implication/universal shell of the PA axiom still has to be built around it.
-/

/-- Constructor wrapper: a native Z `Ind` rule is available only after both premise derivations exist. -/
lemma zDerivation_zInd_intro_probe {s at' p d0 d1 : V}
    (hd0 : ZDerivation d0) (hd1 : ZDerivation d1)
    (hwff : zIndWff (zInd s at' p d0 d1)) :
    ZDerivation (zInd s at' p d0 d1) := by
  exact zDerivation_iff.mpr
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, at', p, d0, d1, rfl, hd0, hd1, hwff⟩))))

/-- A native Z `Ind` node concludes an instance `F(t)`, not the closed PA induction axiom. -/
lemma zIndWff_conclusion_is_instance {s at' p d0 d1 : V}
    (hwff : zIndWff (zInd s at' p d0 d1)) :
    seqSucc s = substs1 ℒₒᵣ (π₂ at') p := by
  simpa [zIndWff, zIndTerm, zIndP] using hwff.2.2.1

/--
The smallest direct native-Ind target still requires synthesizing two premises.  This is strictly below
the full PA induction axiom shell, because it derives `F(t)` at `q`, not the closed axiom code `p`.
-/
def NativeZIndInstanceDerivation (q K : V) : Prop :=
  ∃ at' d0 d1 : V,
    ZDerivation d0 ∧ ZDerivation d1 ∧ zIndWff (zInd q at' K d0 d1)

/-- Native Z-Ind premise synthesis gives a Z derivation of the instance sequent. -/
theorem zDerivation_of_nativeZIndInstance {q K : V}
    (h : NativeZIndInstanceDerivation (V := V) q K) :
    ∃ z : V, ZDerivation z ∧ fstIdx z = q := by
  rcases h with ⟨at', d0, d1, hd0, hd1, hwff⟩
  exact ⟨zInd q at' K d0 d1, zDerivation_zInd_intro_probe hd0 hd1 hwff, by simp⟩

/-! ### M2 verdict probe (lap 168): the native-Ind step carries the `ZDerivesEmptyR` invariants

The `FoundationToZSimulationR` target needs `ZRegular ∧ ZFresh ∧ ZSeqAnt`, not just a bare
`ZDerivation`.  The probe question for the lap-171 gate is whether those invariants EXPLODE on the
native `zInd` node.  They do not: `zReg_zInd`/`zFresh_zInd`/`zSeqAnt_zInd` show each is
`max (one bounded eigen/seq side-flag) (max (premise invariant) (premise invariant))`, so the
invariants compose from the two premise invariants plus THREE bounded flags
(`ltFlag (maxEigen d1) (π₁ at')` — the eigenvariable-freshness side-condition,
`freshFlag (π₁ at') ⊥ (seqAnt q)`, and `seqAntSeqFlag q`).  This is exactly the standard
eigenvariable side-condition of an induction rule — bounded, not a new formalization.  Verdict signal:
**M2-PLAUSIBLE for the native-Ind piece of the induction shell.** -/
theorem zDerivation_of_nativeZIndInstance_R {q at' K d0 d1 : V}
    (hd0 : ZDerivation d0) (hd1 : ZDerivation d1)
    (hwff : zIndWff (zInd q at' K d0 d1))
    (hreg0 : ZRegular d0) (hreg1 : ZRegular d1)
    (hfresh0 : ZFresh d0) (hfresh1 : ZFresh d1)
    (hseqant0 : ZSeqAnt d0) (hseqant1 : ZSeqAnt d1)
    (heig : ltFlag (maxEigen d1) (π₁ at') = 0)
    (hfr : freshFlag (π₁ at') (^⊥ : V) (seqAnt q) = 0)
    (hsa : seqAntSeqFlag q = 0) :
    ∃ z : V, ZDerivation z ∧ fstIdx z = q ∧ ZRegular z ∧ ZFresh z ∧ ZSeqAnt z := by
  have hr0 : zReg d0 = 0 := hreg0
  have hr1 : zReg d1 = 0 := hreg1
  have hf0 : zFresh d0 = 0 := hfresh0
  have hf1 : zFresh d1 = 0 := hfresh1
  have hs0 : zSeqAnt d0 = 0 := hseqant0
  have hs1 : zSeqAnt d1 = 0 := hseqant1
  refine ⟨zInd q at' K d0 d1, zDerivation_zInd_intro_probe hd0 hd1 hwff, by simp, ?_, ?_, ?_⟩
  · show zReg (zInd q at' K d0 d1) = 0
    rw [zReg_zInd, heig, hr0, hr1]; simp
  · show zFresh (zInd q at' K d0 d1) = 0
    rw [zFresh_zInd, hfr, hf0, hf1]; simp
  · show zSeqAnt (zInd q at' K d0 d1) = 0
    rw [zSeqAnt_zInd, hsa, hs0, hs1]; simp

/--
The missing shell around native `zInd`: from an internal induction-axiom code `p = ∀* b` with recovered
core `K`, build a Z derivation of the translated sequent for the closed axiom, not merely an instance
`K(t)`.
-/
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

/--
If the shell simulation exists, the hard induction leaf follows.  This theorem is intentionally one-way:
it exposes that `InductionUnivR` supplies closure/core data, while Z still needs the shell construction.
-/
theorem PAInductionLeafSimulation_of_shell
    {toZ : V → V → Prop}
    (hshell : PAInductionAxiomShellSimulation (V := V) toZ) :
    PAInductionLeafSimulation (V := V) toZ := by
  intro s p q hp hind htoZ
  rcases (PAInductionAxmCode_iff_coreData (V := V) (p := p)).mp hind with
    ⟨m, _hmle, b, _hble, hp_eq, hb, hshift, hbv, K, _hKle, hK, hsubst⟩
  exact hshell hp hp_eq hb hshift hbv hK hsubst htoZ

/-- Full PA axm-leaf simulation reduced to finite `PA⁻` leaves plus the induction-axiom shell. -/
theorem PAAxmLeafSimulation_of_peanoMinus_and_shell
    {toZ : V → V → Prop}
    (hpm : PAPeanoMinusLeafSimulation (V := V) toZ)
    (hshell : PAInductionAxiomShellSimulation (V := V) toZ) :
    PAAxmLeafSimulation (V := V) toZ :=
  PAAxmLeafSimulation_of_peanoMinus_and_induction (V := V) hpm
    (PAInductionLeafSimulation_of_shell (V := V) hshell)

/--
Route-A M2 invariant candidate.

Use a relation rather than a function: translating a one-sided Foundation/Tait sequent to Z requires
choosing a focused succedent and moving the remaining formulas to the antecedent with the appropriate
polarity.  The singleton-bottom case must realize `zEmptySequent`.
-/
class FoundationToZSequent (toZ : V → V → Prop) : Prop where
  singleton_bot :
    toZ ({(foundationBotCode : V)} : V) (zEmptySequent : V)

/-- Singleton focus is a concrete instance of the bridge relation interface. -/
instance FoundationToZFocus.instFoundationToZSequent :
    FoundationToZSequent (FoundationToZFocus (V := V)) where
  singleton_bot := FoundationToZFocus.singleton_bot (V := V)

/-- Membership focus is another concrete instance of the bridge relation interface. -/
instance FoundationToZMemFocus.instFoundationToZSequent :
    FoundationToZSequent (FoundationToZMemFocus (V := V)) where
  singleton_bot := FoundationToZMemFocus.singleton_bot (V := V)

/-- Foundation's PA cut constructor, restated at the exact `DerivationOf` shape used by M2. -/
lemma paDerivationOf_cutRule_of_premises {s p d₁ d₂ : V}
    (hd₁ : (𝗣𝗔 : Theory ℒₒᵣ).DerivationOf d₁ (insert p s))
    (hd₂ : (𝗣𝗔 : Theory ℒₒᵣ).DerivationOf d₂ (insert (neg ℒₒᵣ p) s)) :
    (𝗣𝗔 : Theory ℒₒᵣ).DerivationOf (cutRule s p d₁ d₂) s := by
  exact ⟨by simp, Theory.Derivation.cutRule hd₁ hd₂⟩

/--
Bridge decomposed through a sequent relation.  This is the shape to make concrete in the next probe:
first prove the rule-by-rule simulation at arbitrary related sequents, then specialize to the
singleton-bottom witness above.
-/
def FoundationToZSimulation (toZ : V → V → Prop) : Prop :=
  ∀ {d s q : V}, (𝗣𝗔 : Theory ℒₒᵣ).DerivationOf d s → toZ s q →
    ∃ z : V, ZDerivation z ∧ fstIdx z = q

/-- The concrete singleton-focus simulation obligation for the current bounded M2 probe. -/
abbrev FoundationToZFocusSimulation : Prop :=
  FoundationToZSimulation (V := V) (FoundationToZFocus (V := V))

/--
Bare Z-side cut combiner needed by the Foundation `cutRule` case.

The relation expansion chooses translated sequents for both Foundation premises; this combiner is the
calculus-side step that turns derivations of those translated premises into a derivation of the translated
parent sequent.
-/
def ZCutCombiner (qPos qNeg q : V) : Prop :=
  ∀ {zPos zNeg : V},
    ZDerivation zPos → fstIdx zPos = qPos →
    ZDerivation zNeg → fstIdx zNeg = qNeg →
    ∃ z : V, ZDerivation z ∧ fstIdx z = q

/-- Translation-only part of the Foundation cut case: related parent sequents have related cut premises. -/
def FoundationCutPremiseTranslations (toZ : V → V → Prop) : Prop :=
  ∀ {s p q : V}, toZ s q →
    ∃ qPos qNeg : V, toZ (insert p s) qPos ∧ toZ (insert (neg ℒₒᵣ p) s) qNeg

/-- Z cut combiners for every premise pair chosen by a translation relation. -/
def FoundationCutCombiners (toZ : V → V → Prop) : Prop :=
  ∀ {s p q qPos qNeg : V},
    toZ s q → toZ (insert p s) qPos → toZ (insert (neg ℒₒᵣ p) s) qNeg →
      ZCutCombiner (V := V) qPos qNeg q

/-- Translation-side premise expansion required for simulating Foundation `cutRule`. -/
def FoundationCutPremiseExpansion (toZ : V → V → Prop) : Prop :=
  ∀ {s p q : V}, toZ s q →
    ∃ qPos qNeg : V,
      toZ (insert p s) qPos ∧ toZ (insert (neg ℒₒᵣ p) s) qNeg ∧
        ZCutCombiner (V := V) qPos qNeg q

/-- Separate translation threading plus Z combiners give the bundled cut expansion obligation. -/
theorem FoundationCutPremiseExpansion_of_translations_and_combiners
    {toZ : V → V → Prop}
    (htrans : FoundationCutPremiseTranslations (V := V) toZ)
    (hcomb : FoundationCutCombiners (V := V) toZ) :
    FoundationCutPremiseExpansion (V := V) toZ := by
  intro s p q htoZ
  rcases htrans htoZ with ⟨qPos, qNeg, htoZPos, htoZNeg⟩
  exact ⟨qPos, qNeg, htoZPos, htoZNeg, hcomb htoZ htoZPos htoZNeg⟩

/--
Membership focus threads through both Foundation cut premises: if the parent sequent contains the focused
formula, then inserting the cut formula or its negation preserves that focused formula.
-/
theorem FoundationToZMemFocus.cutPremiseTranslations :
    FoundationCutPremiseTranslations (V := V) (FoundationToZMemFocus (V := V)) := by
  intro s p q htoZ
  rcases htoZ with ⟨focus, hfocus, rfl⟩
  exact ⟨foundationFocusSequent focus, foundationFocusSequent focus,
    ⟨focus, by simp [hfocus], rfl⟩,
    ⟨focus, by simp [hfocus], rfl⟩⟩

/--
One structural Foundation rule reduced to two local obligations: premise translation expansion and a Z cut
combiner.  This is the checked cut-case adapter for the plain simulation target.
-/
theorem foundationCutRule_simulation_of_expansion
    {toZ : V → V → Prop}
    (hexpand : FoundationCutPremiseExpansion (V := V) toZ)
    {s p q d₁ d₂ : V}
    (hd₁ : (𝗣𝗔 : Theory ℒₒᵣ).DerivationOf d₁ (insert p s))
    (hd₂ : (𝗣𝗔 : Theory ℒₒᵣ).DerivationOf d₂ (insert (neg ℒₒᵣ p) s))
    (htoZ : toZ s q)
    (hIHPos : ∀ {qPos : V}, toZ (insert p s) qPos →
      ∃ zPos : V, ZDerivation zPos ∧ fstIdx zPos = qPos)
    (hIHNeg : ∀ {qNeg : V}, toZ (insert (neg ℒₒᵣ p) s) qNeg →
      ∃ zNeg : V, ZDerivation zNeg ∧ fstIdx zNeg = qNeg) :
    ∃ z : V, ZDerivation z ∧ fstIdx z = q := by
  have _hparent : (𝗣𝗔 : Theory ℒₒᵣ).DerivationOf (cutRule s p d₁ d₂) s :=
    paDerivationOf_cutRule_of_premises (V := V) hd₁ hd₂
  rcases hexpand htoZ with ⟨qPos, qNeg, htoZPos, htoZNeg, hcut⟩
  rcases hIHPos htoZPos with ⟨zPos, hzPos, hfstPos⟩
  rcases hIHNeg htoZNeg with ⟨zNeg, hzNeg, hfstNeg⟩
  exact hcut hzPos hfstPos hzNeg hfstNeg

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

/-- Focus-specialized version of the bare empty-sequent target. -/
theorem foundationProofBot_to_Z_derivesEmpty_of_focus_sim
    (hsim : FoundationToZFocusSimulation (V := V))
    {d : V} (hd : FoundationProofOfBot (V := V) d) :
    ∃ z : V, ZDerivesEmpty z :=
  foundationProofBot_to_Z_derivesEmpty_of_sim
    (V := V) (toZ := FoundationToZFocus (V := V)) hsim hd

/-- If a plain simulation and an empty-derivation regularizer exist, the corrected M2 target follows. -/
theorem foundationProofBot_to_Z_empty_of_sim_and_regularization
    {toZ : V → V → Prop} [FoundationToZSequent (V := V) toZ]
    (hsim : FoundationToZSimulation (V := V) toZ)
    (hreg : ZEmptyRegularization (V := V))
    {d : V} (hd : FoundationProofOfBot (V := V) d) :
    ∃ z : V, ZDerivesEmptyR z := by
  obtain ⟨z, hz, hfst⟩ := hsim hd FoundationToZSequent.singleton_bot
  exact hreg (zDerivesEmpty_of_fstIdx_zEmpty hz hfst)

/-- Focus-specialized plain simulation plus regularization discharges the corrected M2 target. -/
theorem foundationProofBot_to_Z_empty_of_focus_sim_and_regularization
    (hsim : FoundationToZFocusSimulation (V := V))
    (hreg : ZEmptyRegularization (V := V))
    {d : V} (hd : FoundationProofOfBot (V := V) d) :
    ∃ z : V, ZDerivesEmptyR z :=
  foundationProofBot_to_Z_empty_of_sim_and_regularization
    (V := V) (toZ := FoundationToZFocus (V := V)) hsim hreg hd

/-- Plain simulation plus regularization is exactly enough to instantiate the corrected M2 bridge. -/
theorem M2Bridge_of_sim_and_regularization
    {toZ : V → V → Prop} [FoundationToZSequent (V := V) toZ]
    (hsim : FoundationToZSimulation (V := V) toZ)
    (hreg : ZEmptyRegularization (V := V)) :
    M2Bridge (V := V) :=
  fun hd => foundationProofBot_to_Z_empty_of_sim_and_regularization
    (V := V) hsim hreg hd

/-- Concrete focus route to the corrected M2 bridge. -/
theorem M2Bridge_of_focus_sim_and_regularization
    (hsim : FoundationToZFocusSimulation (V := V))
    (hreg : ZEmptyRegularization (V := V)) :
    M2Bridge (V := V) :=
  M2Bridge_of_sim_and_regularization
    (V := V) (toZ := FoundationToZFocus (V := V)) hsim hreg

/-- End-to-end route if M2 is proved as plain simulation plus regularization. -/
theorem paConsistent_of_prwo_sim_and_regularization
    {toZ : V → V → Prop} [FoundationToZSequent (V := V) toZ]
    (hprwo : InternalPRWO V)
    (hsim : FoundationToZSimulation (V := V) toZ)
    (hreg : ZEmptyRegularization (V := V)) :
    (𝗣𝗔 : Theory ℒₒᵣ).Consistent V :=
  paConsistent_of_prwo_and_bridge (V := V) hprwo
    (M2Bridge_of_sim_and_regularization (V := V) hsim hreg)

/-- End-to-end focus route when regularization is supplied separately. -/
theorem paConsistent_of_prwo_focus_sim_and_regularization
    (hprwo : InternalPRWO V)
    (hsim : FoundationToZFocusSimulation (V := V))
    (hreg : ZEmptyRegularization (V := V)) :
    (𝗣𝗔 : Theory ℒₒᵣ).Consistent V :=
  paConsistent_of_prwo_and_bridge (V := V) hprwo
    (M2Bridge_of_focus_sim_and_regularization (V := V) hsim hreg)

/--
Alternative strengthened simulation target: build the invariants during the Foundation→Z translation.
This avoids a separate regularization theorem.
-/
def FoundationToZSimulationR (toZ : V → V → Prop) : Prop :=
  ∀ {d s q : V}, (𝗣𝗔 : Theory ℒₒᵣ).DerivationOf d s → toZ s q →
    ∃ z : V, ZDerivation z ∧ fstIdx z = q ∧ ZRegular z ∧ ZFresh z ∧ ZSeqAnt z

/-- The concrete invariant-preserving singleton-focus simulation obligation. -/
abbrev FoundationToZFocusSimulationR : Prop :=
  FoundationToZSimulationR (V := V) (FoundationToZFocus (V := V))

/-- Invariant-preserving Z-side cut combiner needed by the strengthened simulation target. -/
def ZCutCombinerR (qPos qNeg q : V) : Prop :=
  ∀ {zPos zNeg : V},
    ZDerivation zPos → fstIdx zPos = qPos → ZRegular zPos → ZFresh zPos → ZSeqAnt zPos →
    ZDerivation zNeg → fstIdx zNeg = qNeg → ZRegular zNeg → ZFresh zNeg → ZSeqAnt zNeg →
    ∃ z : V, ZDerivation z ∧ fstIdx z = q ∧ ZRegular z ∧ ZFresh z ∧ ZSeqAnt z

/-- Translation-side premise expansion required for invariant-preserving Foundation `cutRule` simulation. -/
def FoundationCutPremiseExpansionR (toZ : V → V → Prop) : Prop :=
  ∀ {s p q : V}, toZ s q →
    ∃ qPos qNeg : V,
      toZ (insert p s) qPos ∧ toZ (insert (neg ℒₒᵣ p) s) qNeg ∧
        ZCutCombinerR (V := V) qPos qNeg q

/-- Invariant-preserving Z cut combiners for every premise pair chosen by a translation relation. -/
def FoundationCutCombinersR (toZ : V → V → Prop) : Prop :=
  ∀ {s p q qPos qNeg : V},
    toZ s q → toZ (insert p s) qPos → toZ (insert (neg ℒₒᵣ p) s) qNeg →
      ZCutCombinerR (V := V) qPos qNeg q

/-- Translation threading plus invariant-preserving Z combiners give the bundled strengthened expansion. -/
theorem FoundationCutPremiseExpansionR_of_translations_and_combinersR
    {toZ : V → V → Prop}
    (htrans : FoundationCutPremiseTranslations (V := V) toZ)
    (hcomb : FoundationCutCombinersR (V := V) toZ) :
    FoundationCutPremiseExpansionR (V := V) toZ := by
  intro s p q htoZ
  rcases htrans htoZ with ⟨qPos, qNeg, htoZPos, htoZNeg⟩
  exact ⟨qPos, qNeg, htoZPos, htoZNeg, hcomb htoZ htoZPos htoZNeg⟩

/--
The invariant-preserving structural cut adapter.  The remaining work is now isolated in the concrete
translation expansion and Z cut combiner, not hidden inside the Foundation recursion.
-/
theorem foundationCutRule_simulationR_of_expansionR
    {toZ : V → V → Prop}
    (hexpand : FoundationCutPremiseExpansionR (V := V) toZ)
    {s p q d₁ d₂ : V}
    (hd₁ : (𝗣𝗔 : Theory ℒₒᵣ).DerivationOf d₁ (insert p s))
    (hd₂ : (𝗣𝗔 : Theory ℒₒᵣ).DerivationOf d₂ (insert (neg ℒₒᵣ p) s))
    (htoZ : toZ s q)
    (hIHPos : ∀ {qPos : V}, toZ (insert p s) qPos →
      ∃ zPos : V, ZDerivation zPos ∧ fstIdx zPos = qPos ∧
        ZRegular zPos ∧ ZFresh zPos ∧ ZSeqAnt zPos)
    (hIHNeg : ∀ {qNeg : V}, toZ (insert (neg ℒₒᵣ p) s) qNeg →
      ∃ zNeg : V, ZDerivation zNeg ∧ fstIdx zNeg = qNeg ∧
        ZRegular zNeg ∧ ZFresh zNeg ∧ ZSeqAnt zNeg) :
    ∃ z : V, ZDerivation z ∧ fstIdx z = q ∧ ZRegular z ∧ ZFresh z ∧ ZSeqAnt z := by
  have _hparent : (𝗣𝗔 : Theory ℒₒᵣ).DerivationOf (cutRule s p d₁ d₂) s :=
    paDerivationOf_cutRule_of_premises (V := V) hd₁ hd₂
  rcases hexpand htoZ with ⟨qPos, qNeg, htoZPos, htoZNeg, hcut⟩
  rcases hIHPos htoZPos with ⟨zPos, hzPos, hfstPos, hregPos, hfreshPos, hseqAntPos⟩
  rcases hIHNeg htoZNeg with ⟨zNeg, hzNeg, hfstNeg, hregNeg, hfreshNeg, hseqAntNeg⟩
  exact hcut hzPos hfstPos hregPos hfreshPos hseqAntPos
    hzNeg hfstNeg hregNeg hfreshNeg hseqAntNeg

/-- A strengthened regular simulation also discharges the corrected M2 target directly. -/
theorem foundationProofBot_to_Z_empty_of_simR
    {toZ : V → V → Prop} [FoundationToZSequent (V := V) toZ]
    (hsim : FoundationToZSimulationR (V := V) toZ)
    {d : V} (hd : FoundationProofOfBot (V := V) d) :
    ∃ z : V, ZDerivesEmptyR z := by
  obtain ⟨z, hz, hfst, hregular, hfresh, hseqAnt⟩ :=
    hsim hd FoundationToZSequent.singleton_bot
  exact ⟨z, zDerivesEmpty_of_fstIdx_zEmpty hz hfst, hregular, hfresh, hseqAnt⟩

/-- Focus-specialized invariant-preserving simulation discharges the corrected M2 target. -/
theorem foundationProofBot_to_Z_empty_of_focus_simR
    (hsim : FoundationToZFocusSimulationR (V := V))
    {d : V} (hd : FoundationProofOfBot (V := V) d) :
    ∃ z : V, ZDerivesEmptyR z :=
  foundationProofBot_to_Z_empty_of_simR
    (V := V) (toZ := FoundationToZFocus (V := V)) hsim hd

/-- Invariant-preserving simulation is exactly enough to instantiate the corrected M2 bridge. -/
theorem M2Bridge_of_simR
    {toZ : V → V → Prop} [FoundationToZSequent (V := V) toZ]
    (hsim : FoundationToZSimulationR (V := V) toZ) :
    M2Bridge (V := V) :=
  fun hd => foundationProofBot_to_Z_empty_of_simR (V := V) hsim hd

/-- Concrete focus route to M2 when the simulation carries the Z invariants directly. -/
theorem M2Bridge_of_focus_simR
    (hsim : FoundationToZFocusSimulationR (V := V)) :
    M2Bridge (V := V) :=
  M2Bridge_of_simR
    (V := V) (toZ := FoundationToZFocus (V := V)) hsim

/-- End-to-end route if M2 is proved as an invariant-preserving simulation. -/
theorem paConsistent_of_prwo_simR
    {toZ : V → V → Prop} [FoundationToZSequent (V := V) toZ]
    (hprwo : InternalPRWO V)
    (hsim : FoundationToZSimulationR (V := V) toZ) :
    (𝗣𝗔 : Theory ℒₒᵣ).Consistent V :=
  paConsistent_of_prwo_and_bridge (V := V) hprwo
    (M2Bridge_of_simR (V := V) hsim)

/-- End-to-end focus route when regularity/freshness/antecedent invariants are built by simulation. -/
theorem paConsistent_of_prwo_focus_simR
    (hprwo : InternalPRWO V)
    (hsim : FoundationToZFocusSimulationR (V := V)) :
    (𝗣𝗔 : Theory ℒₒᵣ).Consistent V :=
  paConsistent_of_prwo_and_bridge (V := V) hprwo
    (M2Bridge_of_focus_simR (V := V) hsim)

end GoodsteinPA.InternalZ
