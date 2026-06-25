/-
# Crux-2 blueprint — the genuine reduct ⟹ the Gentzen contradiction, as sorried leaves

**Blueprint (judge, 2026-06-24).** Decomposes the single open girder `Reduction.goodstein_implies_consistency`
into precise, named, sorried leaves M1a–M3, so the crux-2 contradiction `¬Con(𝗣𝗔) → False` follows
**by construction** — the assembly is wired here, not "at the end." Increasing the sorry count is the
*point*: one fat `sorry` split into small precise ones is progress, not regress.

Grounded in the existing `InternalZ` API (verified against HEAD): `ZDerivation`, `ZDerivesEmpty`, `iord`,
`icmp`, `iR2`, `RedSound`, `iord_iR2_iterate_descends`, `inference_critical_pair`. The genuine reduct
`red` (Buchholz §6 `red` / Def 3.2) *replaces* the ordinal-faithful-but-invalid `iR2`; everything the
box banked for `iR2` (the one-step ordinal descent) re-states over `red` and the descent then becomes
**unconditional** once `redSound` (M1b) is proven.

⚠️ SEED — not yet compiled by the judge (can't host-build against the live box). The grind's first task
is to make this file elaborate (fix any signature drift against HEAD), then discharge the leaves
M1a → M1b → M2 → M3. Deliberately NOT imported by `GoodsteinPA.lean`, so it cannot affect the default
`lake build GoodsteinPA`. Literature + lap budgets: `E-CRUX2-ROADMAP-2026-06-24.md`.
-/
import GoodsteinPA.InternalZ
import GoodsteinPA.Reduction

namespace GoodsteinPA.InternalZ

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol ISigma1 PeanoMinus
open LO.FirstOrder.Arithmetic.Bootstrapping
open GoodsteinPA.InternalONote

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-! ## M1a — the genuine validity-faithful reduct `red` + construction correctness
Buchholz §6 `red` / Def 3.2: a 5-case primrec dispatch on the tag; the critical/`K`-case builds the
auxiliaries `d{0},d{1}` per 3.2(5.1) from the redex `inference_critical_pair` (L3.1) and the rank bound
`inference_critical_pair_rank` (T3.4(a)) — both already in `InternalZ`. -/

/- **M1a — DONE.** The genuine reduct `red` (5-case tag dispatch; critical `K`-case = `iRcritG`, the
genuine recombination on correct reduced endsequents) is now defined + `𝚺₁`-definable in `InternalZ`,
with per-rule recursion equations (`red_zAtom`/`red_zIall`/`red_zIneg`/`red_zInd`/`red_zAxAll`/`red_zAxNeg`/
`red_zK`). The placeholder def is removed — `red` is `InternalZ.red`. -/

/-- **M1a — DONE.** `red` preserves the end-sequent on the chain-reduct rules (`Ind`, `K`), which are the
only reducible rules a ⊥-derivation visits — `InternalZ.fstIdx_red_of_tag_Ind_or_K`. -/
theorem fstIdx_red {d : V} (hd : ZDerivation d) (htag : zTag d = 3 ∨ zTag d = 4) :
    fstIdx (red d) = fstIdx d := fstIdx_red_of_tag_Ind_or_K hd htag

/-! ## M1b — `RedSound` for `red`: validity as the parallel-induction invariant
Buchholz Thm 3.4(b) / Thm 6.2: principal sequent ⊆ Γ, cut-rank `< m`. Proved as a SEPARATE simultaneous
induction over the same `red` (not recovered post-hoc from the ordinal side) — threading the banked
`zKValidFDef` (faithful validity). This is the cut-elimination core; everything downstream is plumbing. -/

/-- **M1b — THE nut.** The `red`-reduct of a contradiction derivation is again a genuine `ZDerivation`.
(Re-pointed `RedSound`, off the dead `iR2`.) -/
theorem redSound : ∀ d : V, ZDerivesEmpty d → ZDerivation (red d) := sorry

/-- **M1b (descent re-point, one step).** The banked ordinal descent, restated over `red`
(`iR2` analogue: `iord_descent_iR2_of_ZDerivesEmpty`). -/
theorem iord_descent_red {d : V} (hd : ZDerivesEmpty d) : icmp (iord (red d)) (iord d) = 0 := sorry

/-! ## Connectives — PROVEN from the leaves (this is the "no wiring step" demonstration)
With `redSound` in hand, `ZDerivesEmpty` is closed under the whole `red`-orbit and the ε₀-descent is
**unconditional** — mirrors `ZDerivesEmpty_iterate` / `iord_iR2_iterate_descends`, minus the `RedSound`
hypothesis. Bodies left `sorry` here only because this file is uncompiled; they are pure plumbing copies. -/

/-- **`red` preserves `ZDerivesEmpty`** (mirror of `ZDerivesEmpty_iR2`, now UNCONDITIONAL): a
contradiction derivation reduces to one — `redSound` gives `ZDerivation (red d)` and `fstIdx_red`
transfers the empty antecedent + `⊥` succedent. -/
theorem ZDerivesEmpty_red {d : V} (h : ZDerivesEmpty d) : ZDerivesEmpty (red d) := by
  have hfst : fstIdx (red d) = fstIdx d := fstIdx_red h.1 (zTag_Ind_or_K_of_ZDerivesEmpty h)
  exact ⟨redSound d h, by rw [hfst]; exact h.2.1, by rw [hfst]; exact h.2.2⟩

/-- `ZDerivesEmpty` is closed under the `red`-orbit (no hypothesis — `redSound` discharges it). -/
theorem ZDerivesEmpty_red_iterate {z : V} (hz : ZDerivesEmpty z) :
    ∀ n : ℕ, ZDerivesEmpty (red^[n] z)
  | 0 => by simpa using hz
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact ZDerivesEmpty_red (ZDerivesEmpty_red_iterate hz n)

/-- **The infinite ε₀-descent of crux-2, UNCONDITIONAL.** `n ↦ iord (red^[n] z)` strictly `≺`-descends.
An infinite primitive-recursive ε₀-descent — exactly what `PRWO(ε₀)` forbids. -/
theorem iord_red_iterate_descends {z : V} (hz : ZDerivesEmpty z) (n : ℕ) :
    icmp (iord (red^[n+1] z)) (iord (red^[n] z)) = 0 := by
  rw [Function.iterate_succ_apply']
  exact iord_descent_red (ZDerivesEmpty_red_iterate hz n)

/-! ## M2 — the C0.5 Foundation→Z bridge
`Z ⊇ 𝗣𝗔` on closed sequents, M-internal (Bryce–Goré `Peano.v` blueprint, B1–B3; the PA-induction axiom
maps directly to Z's native `Ind`, skipping their biggest sub-tower). Populates `ZDerivesEmpty` from a
Foundation ⊥-proof. -/

/-- **M2.** A model-internal `𝗣𝗔`-derivation of the (coded) empty/`⊥` sequent yields a `Z`-derivation
of the empty sequent. ⚠️ **Signature to pin against Foundation's coded-provability API:** the confirmed
primitive `Theory.DerivationOf (d s : V) := fstIdx d = s ∧ T.Derivation d` takes a *coded sequent*
`s : V` (here `∅`/the `⊥`-sequent), NOT a `Sentence ℒₒᵣ` (the in-repo doc was loose); the exact
`𝗣𝗔`-internal theory term `T` is the box's to fix (it is what `¬ 𝗣𝗔.Consistent M` unfolds to internally,
cf. `Reduction.peano_not_proves_consistency`). -/
theorem foundation_bot_to_Z_empty {d : V} (hd : (𝗣𝗔 : Theory ℒₒᵣ).Derivation d) (h0 : fstIdx d = ∅) :
    ∃ z : V, ZDerivesEmpty z := sorry

/-! ## M3 — assemble the Gentzen contradiction
An inconsistency gives a `ZDerivesEmpty` (M2) whose `red`-orbit is an infinite ε₀-descent (M1b ⟹
`iord_red_iterate_descends`), which `PRWO(ε₀)`/well-foundedness forbids. This is the payload that
discharges the deep axiom `GentzenCon.gentzen_descent_of_inconsistent`; the existing `Reduction.lean`
+ `GentzenCon` scaffolding carries it the rest of the way to `goodstein_implies_consistency` and the
headline — no new top-level wiring. -/

/-- **M3.** From a `ZDerivesEmpty` witness, the unconditional ε₀-descent contradicts well-foundedness of
the internal ordinal order — the Gentzen `False`. (Internalize `n ↦ iord (red^[n] z)` as the `Σ₁` graph
`gentzenDescentφ`; the descent is `iord_red_iterate_descends`.) -/
theorem false_of_ZDerivesEmpty {z : V} (hz : ZDerivesEmpty z) : False := sorry

end GoodsteinPA.InternalZ
