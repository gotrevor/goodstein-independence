import GoodsteinPA.WainerLadder

/-!
# SERIES-2 Stage C-1 probe — lane-D Option-B splice feasibility

**Question (`REBUILD-Z-SERIES-2-ORDER-2026-07-03.md` Stage C-1).**  Lane D's read-off residue
(`readoffD_trapped`) is GATED: the ratified rung-D bound `∃ n ≤ f 0` is not reachable by the
structural `allω` descent without E–W's (Ax2); what IS achievable is the weaker
`∃ n ≤ ewIter f α 0` (lap-195).  Does the splice consumer (`wainer_splice_Zef2`) still close if
rung D concludes at the achievable bound — i.e. can the headline path DODGE (Ax2) entirely?

**ANSWER: YES, and the cost is exactly ONE tower level — structurally FREE.**  Kernel facts:

1. `optionB_tower_step` (**`rfl`**): the Option-B exit bound at the rank-0 pair
   `(collapseIter d α, ewIterTower f d α)` — namely `ewIter (ewIterTower f d α) (collapseIter d α)`
   — IS the `(d+1)`-level tower `ewIterTower f (d+1) α`, **by definition**.  So an Option-B
   rung D does not change the FUNCTIONAL SHAPE of the splice's final bound at all: whatever
   Hardy-bracket domination argument converts `ewIterTower f d α 0` into the
   `hardy`/`fastGrowing` vocabulary converts `ewIterTower f (d+1) α 0` by the same lemma at
   `d+1`.  (`d` is fixed per PA proof either way.)

2. `optionB_splice_exit`: the full generic composition.  ⚠️ Axiom footprint
   `[propext, sorryAx, Classical.choice, Quot.sound]` — the `sorryAx` is INHERITED from
   `rankToZeroAux` (rung R consumes `passAux`, whose top-rank cut is the escalated trilemma
   crux); the composition logic ADDED here introduces no sorry.  `optionB_tower_step` and
   `ewIterTower_mono_infl` are axiom-clean `[propext, Classical.choice, Quot.sound]`.  From ANY Option-B-shaped
   read-off (hypothesis `readoffB`: every rank-0 `Zef2` derivation of `{∃⁰ φ}` yields a witness
   `≤ ewIter f' α' 0` at ITS OWN ordinal/slot) and a rank-`d` derivation, `rankToZeroAux`
   composes to the exit `∃ n ≤ ewIterTower f (d+1) α 0`.  The `Zef2Prov` ordinal slack
   (`α' ≤ collapseIter d α`) is absorbed by gated ordinal-monotonicity (`ewIter_le_of_lt`), the
   gate coming from the `Zef2Prov` norm bound itself — NO new hypotheses beyond the EwLow
   triple `rankToZeroAux` already threads.

**R-4′ restatement draft (ruling input, NOT ratified — text only).**  Rung D (Option B):
  `readoff_delta0_Zef2' : Zef2 α e H f 0 Γ → (Δ₀/goal-shape hypotheses as in R-4) →
     ∃ n ≤ ewIter f α 0, atomTrue (φ/[nm n])`
i.e. R-4 with the exit bound `f 0` replaced by `ewIter f α 0`.  The trapped-contraction residue
then closes structurally: at an `allω` node the branch bound `rel1 f n`-growth is ≤ the
`ewIter f α`-budget (the branch ordinals sit below `α`), which is exactly what the lap-195
narrowing could not fit under `f 0`.  Consequence for the splice: `wainer_splice_Zef2` consumes
the SAME tower shape one level higher (fact 1), so the Series-3 conversion obligation
(dominate `m ↦ ewIterTower (ewRootSlot e m) D α 0` by a fixed `fastGrowing o`) is UNCHANGED in
kind.  With `readoffD_trapped_of_mono` covering the monotone-matrix fragment, (Ax2) would be
needed by NEITHER the read-off NOR the splice on the headline path — it remains solely a
rung-E calculus-faithfulness question (Stage B).

**Residual honest caveat (for the ruling):** this probe verifies the CONSUMER side (composition
+ bound shape).  The PRODUCER side — that the Option-B statement `readoff_delta0_Zef2'` itself
closes structurally at the `allω` trapped case — is Series-3 grind work (sanctioned only
post-ruling); its feasibility evidence is lap-195's diagnosis that the trap is exactly a
`f 0`-vs-`rel1`-growth budget mismatch, which the `ewIter f α` budget by construction covers.

wip-only ruling input (SERIES-2 order Stage C / ladder P2).  `src` untouched.
-/

namespace GoodsteinPA.OptionBSpliceProbe

open LO LO.FirstOrder ONote
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-- **Fact 1 — the Option-B exit bound is the `(d+1)`-tower, BY DEFINITION.**  The bound an
Option-B rung D reads off the rank-0 pair produced by `d` passes is literally
`ewIterTower f (d+1) α` — the same functional shape the ratified splice already consumes,
one level up.  `rfl`. -/
theorem optionB_tower_step (f : ℕ → ℕ) (d : ℕ) (α : ONote) :
    ewIter (ewIterTower f d α) (collapseIter d α) = ewIterTower f (d + 1) α := rfl

/-- The slot tower preserves `Monotone` and inflationarity (levelwise, from
`ewIter_monotone`/`ewIter_infl`). -/
theorem ewIterTower_mono_infl {f : ℕ → ℕ} (hm : Monotone f) (hi : ∀ x, x ≤ f x) :
    ∀ (d : ℕ) (α : ONote),
      Monotone (ewIterTower f d α) ∧ ∀ x, x ≤ ewIterTower f d α x
  | 0, _ => ⟨hm, hi⟩
  | (d + 1), α => by
      obtain ⟨hm', hi'⟩ := ewIterTower_mono_infl hm hi d α
      exact ⟨ewIter_monotone hm' hi' _, ewIter_infl hi' _⟩

/-- **Fact 2 — the generic Option-B splice composition** (sorry-free HERE; inherits rung R's
disclosed `sorryAx` through `rankToZeroAux`/`passAux` — see the file docstring).  Given an
Option-B-shaped read-off (`readoffB`, the R-4′ draft form: any rank-0 derivation of `{∃⁰ φ}`
yields a witness bounded by `ewIter f' α' 0` at its own ordinal/slot), a rank-`d` derivation
composes through `rankToZeroAux` to the exit witness bounded by the `(d+1)`-tower.  The
`Zef2Prov` ordinal slack is absorbed by gated ordinal-monotonicity; no hypotheses beyond the
EwLow triple already threaded by rung R. -/
theorem optionB_splice_exit {e : ONote} (heNF : e.NF)
    {φ : SyntacticSemiformula ℒₒᵣ 1}
    (readoffB : ∀ {α' : ONote} {H : ONote → Prop} {f' : ℕ → ℕ},
        Zef2 α' e H f' 0 {(∃⁰ φ)} →
        ∃ n ≤ ewIter f' α' 0, atomTrue (φ/[nm n]))
    {α : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {d : ℕ}
    (D : Zef2 α e H f d {(∃⁰ φ)})
    (hmono : Monotone f) (hinfl : ∀ x, x ≤ f x) (hlow : ∀ m, 2 * m + 1 ≤ f m)
    (hαNF : α.NF) (hαH : Cl H α) :
    ∃ n ≤ ewIterTower f (d + 1) α 0, atomTrue (φ/[nm n]) := by
  obtain ⟨α', hle, hNF', _hH', hgate, D'⟩ :=
    rankToZeroAux e heNF d D hmono hinfl hlow hαNF hαH
  obtain ⟨hm', hi'⟩ := ewIterTower_mono_infl hmono hinfl d α
  obtain ⟨n, hn, htrue⟩ := readoffB D'
  refine ⟨n, ?_, htrue⟩
  rw [← optionB_tower_step]
  rcases lt_or_eq_of_le (le_def.mp hle) with hlt | heq
  · have hlift : ewIter (ewIterTower f d α) α' 0
        ≤ ewIter (ewIterTower f d α) (collapseIter d α) 0 :=
      ewIter_le_of_lt hi' (lt_def.mpr hlt) (le_trans hgate (hm' (Nat.zero_le _)))
    exact le_trans hn hlift
  · have hα'eq : α' = collapseIter d α := by
      haveI := hNF'
      haveI := collapseIter_NF hαNF d
      exact repr_inj.mp heq
    exact hα'eq ▸ hn

end GoodsteinPA.OptionBSpliceProbe
