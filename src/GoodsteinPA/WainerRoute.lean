/-
# Wainer/Cichon/Caicedo growth-rate route

This module is the new route spine after the 2026-07-01 route decision.  The old
active route tried to derive `Con(PA)` from Goodstein inside PA and then use Godel II.
That forced an IΣ₁-internalized cut-elimination bridge.  The lap-171 M2 probe found
the decisive obstruction: the PA-induction leaf wants a free-variable forall-left /
implication-left step that the finitary internal-Z calculus does not have.

The growth route instead proves non-provability from rates of growth:

  PA proves Goodstein
    -> the Goodstein length function is PA-provably total
    -> Wainer: every PA-provably-total recursive function is eventually bounded by
       some fast-growing `f_o`, `o < epsilon_0`
    -> Cichon/Caicedo: Goodstein length is not eventually bounded by any fixed
       `f_o`, `o < epsilon_0`
    -> contradiction.

The existing repo already proves the main concrete growth asset:
`GoodsteinPA.Dom.goodsteinLength_dominates_fastGrowing`.  This module now upgrades
that asset to the exact no-fixed-bound theorem needed by the route.  The remaining
named axiom is the Wainer PA-provably-total classification bridge.
-/
import GoodsteinPA.Statement
import GoodsteinPA.Domination
import GoodsteinPA.BlueprintAttr

namespace GoodsteinPA.WainerRoute

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open ONote GoodsteinPA.FastGrowing

/-- Eventual pointwise domination.  `EventuallyLE f g` means that, from some threshold
onward, `f n <= g n`. -/
def EventuallyLE (f g : ℕ -> ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n -> f n ≤ g n

/-- Eventual domination with a fixed additive slack on the right. -/
def EventuallyLEWithSlack (f g : ℕ -> ℕ) (c : ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n -> f n ≤ g n + c

/-- The already-machine-checked Cichon/Caicedo lower-bound direction in the shape the
Wainer route needs first: every fixed fast-growing level below `epsilon_0` is eventually
bounded by Goodstein length, up to the repo's documented additive slack `2`. -/
theorem goodsteinLength_eventually_dominates_fixed_fastGrowing (o : ONote) (ho : o.NF) :
    EventuallyLEWithSlack (fun n => fastGrowing o n) GoodsteinPA.Dom.goodsteinLength 2 :=
  GoodsteinPA.Dom.goodsteinLength_dominates_fastGrowing ho

/-- Iterating a strictly inflationary map adds at least the iteration count.

This is the elementary arithmetic engine behind the successor-level separation
`f_o(n) + 2 < f_{o+1}(n)` for large `n`. -/
theorem add_le_iterate_of_lt {g : ℕ -> ℕ}
    (hstep : ∀ y, 1 ≤ y -> y + 1 ≤ g y)
    (hpos : ∀ y, 1 ≤ y -> 1 ≤ g y) :
    ∀ (j : ℕ) {y : ℕ}, 1 ≤ y -> y + j ≤ g^[j] y := by
  intro j
  induction j with
  | zero =>
      intro y hy
      simp
  | succ j ih =>
      intro y hy
      rw [Function.iterate_succ_apply]
      have h1 : 1 ≤ g y := hpos y hy
      have hstepy : y + 1 ≤ g y := hstep y hy
      have hih := ih (y := g y) h1
      omega

/-- The strict successor gap in the fast-growing hierarchy.

For `m >= 4`, the notation-successor level has already iterated `f_o` long enough to
swallow the additive `+2` slack from the Goodstein lower bound:
`f_o(m) + 2 < f_{osucc o}(m)`. -/
theorem fastGrowing_fixed_add_two_lt_successor {o : ONote} (ho : o.NF) {m : ℕ}
    (hm : 4 ≤ m) :
    fastGrowing o m + 2 < fastGrowing (osucc o) m := by
  have hfs : fastGrowing (osucc o) m = (fastGrowing o)^[m] m := by
    rw [fastGrowing_succ (osucc o) (fundamentalSequence_osucc ho)]
  have hstep : ∀ y, 1 ≤ y -> y + 1 ≤ fastGrowing o y := fun y hy => lt_fastGrowing o hy
  have hpos : ∀ y, 1 ≤ y -> 1 ≤ fastGrowing o y :=
    fun y hy => le_trans hy (le_fastGrowing o y)
  have hsplit : (fastGrowing o)^[m] m = (fastGrowing o)^[m - 1] (fastGrowing o m) := by
    obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [hn]
    simp [Function.iterate_succ_apply]
  have hiter :
      fastGrowing o m + (m - 1) ≤ (fastGrowing o)^[m - 1] (fastGrowing o m) :=
    add_le_iterate_of_lt hstep hpos (m - 1) (hpos m (by omega))
  rw [hfs, hsplit]
  omega

/-- Cichon/Caicedo in the exact no-fixed-bound form needed by Wainer.

The repo's existing lower bound gives `f_{osucc o}(m) <= goodsteinLength m + 2`
eventually.  The successor-gap lemma above gives `f_o(m) + 2 < f_{osucc o}(m)` for
`m >= 4`.  Together they imply `f_o(m) < goodsteinLength m` eventually, so no fixed
`f_o` can eventually bound the Goodstein length function from above. -/
theorem goodsteinLength_eventually_strictly_dominates_fixed_fastGrowing (o : ONote)
    (ho : o.NF) :
    ∃ N, ∀ m, N ≤ m -> fastGrowing o m < GoodsteinPA.Dom.goodsteinLength m := by
  obtain ⟨N, hN⟩ :=
    GoodsteinPA.Dom.goodsteinLength_dominates_fastGrowing (osucc_NF ho)
  refine ⟨max N 4, fun m hm => ?_⟩
  have hmN : N ≤ m := le_trans (le_max_left _ _) hm
  have hm4 : 4 ≤ m := le_trans (le_max_right _ _) hm
  have hdom := hN m hmN
  have hgap := fastGrowing_fixed_add_two_lt_successor ho hm4
  omega

/-- **Wainer classification, specialized to this route.**

If PA proves the Goodstein sentence, then the Goodstein length function is PA-provably
total; Wainer's classification of PA-provably-total recursive functions then bounds it
eventually by one fixed fast-growing function `f_o`, `o < epsilon_0`.

This is the new proof-theory debt replacing the internalized Gentzen bridge. -/
axiom wainer_bound_of_pa_proves_goodstein :
    (𝗣𝗔 ⊢ ↑goodsteinSentence) ->
      ∃ o : ONote, o.NF ∧ EventuallyLE GoodsteinPA.Dom.goodsteinLength (fun n => fastGrowing o n)

/-- **Cichon/Caicedo exact no-fixed-bound theorem.**

This is now proved from existing machine-checked growth assets plus the successor-gap
lemma above.  It is the exact growth-route contradiction against Wainer's fixed
`f_o` upper bound. -/
theorem cichon_caicedo_not_eventually_bounded_by_fixed_fastGrowing :
    ∀ o : ONote, o.NF ->
      ¬ EventuallyLE GoodsteinPA.Dom.goodsteinLength (fun n => fastGrowing o n) := by
  intro o ho hbound
  obtain ⟨N, hN⟩ := hbound
  obtain ⟨M, hM⟩ :=
    goodsteinLength_eventually_strictly_dominates_fixed_fastGrowing o ho
  let n := max N M
  have hupper : GoodsteinPA.Dom.goodsteinLength n ≤ fastGrowing o n :=
    hN n (le_max_left _ _)
  have hlower : fastGrowing o n < GoodsteinPA.Dom.goodsteinLength n :=
    hM n (le_max_right _ _)
  omega

/-- **Kirby--Paris via Wainer/Cichon/Caicedo.**

This is the new route theorem: if PA proved Goodstein, Wainer would put the Goodstein
length function below some fixed `f_o`; Cichon/Caicedo says no fixed `f_o` can bound it.
The only route-specific axiom left is the specialized Wainer classification above. -/
theorem peano_not_proves_goodstein_growth : 𝗣𝗔 ⊬ ↑goodsteinSentence := by
  intro hpa
  obtain ⟨o, ho, hbound⟩ := wainer_bound_of_pa_proves_goodstein hpa
  exact cichon_caicedo_not_eventually_bounded_by_fixed_fastGrowing o ho hbound

/- Blueprint ledger: THE remaining route-B debt — the specialized Wainer
classification, held as the sole axiom. The whole Zᵉ operator-calculus substrate
(the rebuild) exists to discharge this. Estimate re-based 2026-07-02 from the
WAINER-LADDER decomposition (rungs P/R/D/E/W, sum ≈ 20–40 laps; a planning
claim, not a kernel fact; category `debt` is machine-audited by
`lake exe blueprint_audit`). The rungs get their own ledger rows at the lap-8
port; until then this row carries the sum. -/
attribute [goodstein_blueprint 14 debt "wainer_axiom" "20-40" 65 wainer_bound_of_pa_proves_goodstein
  []
  ["WAINER-LADDER-2026-07-02.md: rungs P 4-7@70 + R 1@90 + D 2-3@80 + E 8-20@65 + W 2-4@75; supersedes the MASTERPLAN 30-60@60 monolith estimate",
   "Buchholz-Wainer 1987: the classification is proved by omega-logic + cut-elimination — the someK/Zeh substrate"]
  "The specialized Wainer classification axiom; discharged by the wainer ladder over the Z^e operator calculus (embed -> pass -> rank-0 -> Delta_0 read-off -> splice)."]
  wainer_bound_of_pa_proves_goodstein

/- Blueprint ledger: the route-B headline (PA ⊬ Goodstein via growth rates).
Proved in Lean modulo the Wainer axiom above (3-line assembly over Cichon/Caicedo),
so it inherits `debt` until that axiom lands; the estimate is the final
packaging/assembly step (masterplan W6). -/
attribute [goodstein_blueprint 15 debt "routeB_headline" "1-2" 90 peano_not_proves_goodstein_growth
  []
  ["MASTERPLAN-2026-07-01-ZERO-AXIOMS.md W6 (assembly, corollaries, full independence): 1-2 laps, 90%",
   "Proof body is done mod the axiom: intro hpa; obtain from wainer_bound; exact cichon_caicedo"]
  "Route-B independence headline: PA ⊬ Goodstein from Wainer's fixed-f_o bound vs Cichon/Caicedo no-fixed-bound. Assembly done; debt inherited from the Wainer axiom."]
  peano_not_proves_goodstein_growth

end GoodsteinPA.WainerRoute
