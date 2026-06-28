import GoodsteinPA.LowerBound
import GoodsteinPA.Encoding

/-!
# Path B probe: witness-bounded terminal target

This file deliberately uses the current Pivot-B meaning from
`ROUTE-ESCALATION-2026-06-28.md`: the growth-rate / Towsner lower-bound route.

The old `wip/Bounding.lean` assembly is not revived here, because it is explicitly
false as stated: it routes through the unbounded `Z∞` calculus and loses Towsner's
witness bound.  The live terminal target for B is the witness-bounded calculus
`LowerBoundHardy.B`.
-/

namespace GoodsteinPA.PathBProbe

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open GoodsteinPA.LowerBoundHardy

/-- A cut-free, witness-bounded derivation of the Goodstein fragment at ordinal `α`
and witness budget `k`.  This is the terminal object that Path B must extract from
a PA proof after bounded embedding and bounded cut-elimination. -/
def CutFreeGoodsteinBounded (α : ONote) (k : ℕ) : Prop :=
  B α k ({GForm.gAll} : Seq)

/-- The promoted lower-bound theorem directly rules out the B terminal object for
every normal-form ordinal notation and every witness budget. -/
theorem no_cutFreeGoodsteinBounded {α : ONote} (hα : α.NF) (k : ℕ) :
    ¬ CutFreeGoodsteinBounded α k := by
  simpa [CutFreeGoodsteinBounded] using lowerBound_hardy_selfcontained (α := α) hα k

/-- The current B capstone, isolated from the upstream embedding work. -/
def RouteBCapstone : Prop :=
  ∃ α : ONote, α.NF ∧ ∃ k : ℕ, CutFreeGoodsteinBounded α k

/-- The lower-bound half of B is already decisive once a bounded cut-free derivation
has been produced. -/
theorem no_routeBCapstone : ¬ RouteBCapstone := by
  rintro ⟨α, hα, k, hB⟩
  exact no_cutFreeGoodsteinBounded hα k hB

/-- The real next B bridge: a PA proof of Goodstein must yield the witness-bounded
cut-free terminal object above, not merely an unbounded `Z∞` derivation. -/
def RouteBBridgeFromPAProof : Prop :=
  (𝗣𝗔 ⊢ ↑goodsteinSentence) → RouteBCapstone

/--
Named B obligations.  These are not global Lean axioms; they are an explicit assumption
package so the route can be reviewed by named missing theorem rather than hidden inside the
single bridge above.

The hardest field is `boundedInductionAxiomLeaf`: porting the PA-induction axiom discharge to
the witness-bounded calculus without losing the `exI` witness bound.
-/
structure RouteBNamedObligations where
  boundedUniversalAxiomLeaves : Prop
  boundedInductionAxiomLeaf : Prop
  boundedStructuralEmbedding : Prop
  boundedCutElimination : Prop
  subformulaBridgeToLowerBound : Prop
  h_boundedUniversalAxiomLeaves : boundedUniversalAxiomLeaves
  h_boundedInductionAxiomLeaf : boundedInductionAxiomLeaf
  h_boundedStructuralEmbedding : boundedStructuralEmbedding
  h_boundedCutElimination : boundedCutElimination
  h_subformulaBridgeToLowerBound : subformulaBridgeToLowerBound
  bridgeFromNamed :
    boundedUniversalAxiomLeaves →
    boundedInductionAxiomLeaf →
    boundedStructuralEmbedding →
    boundedCutElimination →
    subformulaBridgeToLowerBound →
    RouteBBridgeFromPAProof

/-- Collapse the named B obligations to the single bridge consumed by the terminal assembly. -/
def RouteBNamedObligations.bridge (h : RouteBNamedObligations) : RouteBBridgeFromPAProof :=
  h.bridgeFromNamed
    h.h_boundedUniversalAxiomLeaves
    h.h_boundedInductionAxiomLeaf
    h.h_boundedStructuralEmbedding
    h.h_boundedCutElimination
    h.h_subformulaBridgeToLowerBound

/-- Once the bounded bridge exists, the headline independence result follows from
the already-promoted lower-bound theorem. -/
theorem peano_not_proves_goodstein_of_routeBBridge
    (hbridge : RouteBBridgeFromPAProof) : 𝗣𝗔 ⊬ ↑goodsteinSentence := by
  intro hpa
  exact no_routeBCapstone (hbridge hpa)

/-- The same assembly, but with the missing B work exposed as named obligations. -/
theorem peano_not_proves_goodstein_of_routeBNamedObligations
    (h : RouteBNamedObligations) : 𝗣𝗔 ⊬ ↑goodsteinSentence :=
  peano_not_proves_goodstein_of_routeBBridge h.bridge

end GoodsteinPA.PathBProbe
