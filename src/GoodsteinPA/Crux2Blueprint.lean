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

/-! ### `redSound` decomposed: structural induction skeleton + two precise validity residuals

`redSound` is the genuine cut-elimination soundness. We prove the GENERAL form
`redSoundGen : ∀ d, ZDerivation d → ZDerivation (red d)` by `zDerivation_induction`; the seven `ZPhi`
disjuncts split as:

* **atom / Ax∀ / Ax¬** (`red = d`): rebuilt directly from the disjunct via `zDerivation_iff.mpr`.
* **I∀ / I¬** (`red = d₀`, the premise): the immediate sub-derivation, from the IH.
* **Ind** (`red = zK s (irk p) (iIndReductSeq d₀ d₁ 1)`): a chain whose premises are the Ind premises
  (`znth_iIndReductSeq_ZDerivation`); a genuine `ZDerivation` once the produced chain is valid — the
  residual `zKValid_iIndReduct_of_zInd` (Buchholz Thm 3.4, Ind case).
* **K** (`red = iRK …`, the 5.1/5.2.1/5.2.2 dispatch): the genuine recombination is a `ZDerivation`
  given every premise reduct `red dᵢ` is — the residual `ZDerivation_red_zK` (Buchholz Thm 3.4, K case;
  the heart of cut-elimination).

This splits the single fat `redSound` `sorry` into exactly the two deep Buchholz-3.4 validity facts. -/

/-- **Residual (Ind case of Buchholz Thm 3.4).** The Ind-reduct chain `zK s (irk p) (iIndReductSeq d₀ d₁ 1)`
of a valid `Ind` inference is FAITHFULLY valid (`zKValidF`, no criticality). The chain's `Seq` structure
and per-premise derivability are free (`znth_iIndReductSeq_ZDerivation`); this is the validity-threading
obligation. (Stated at `zKValidF` not `zKValid`: the reduct chain need not be critical.) -/
theorem zKValidF_iIndReduct_of_zInd {s at' p d0 d1 : V}
    (hZ : ZDerivation (zInd s at' p d0 d1)) :
    zKValidF s (irk p) (iIndReductSeq d0 d1 1) := sorry

/-- **Residual (K case of Buchholz Thm 3.4 — the cut-elimination core).** The genuine reduct `red` of a
valid chain `zK s r ds` is again a `ZDerivation`, given that the reduct of every premise is. The
dispatch (`iRK`: 5.1 critical / 5.2.1 splice / 5.2.2 replace) is already wired into `red`
(`red_zK`/`red_zK_crit`); this lemma supplies the validity-preservation across the dispatch. -/
theorem ZDerivation_red_zK {s r ds : V}
    (hZ : ZDerivation (zK s r ds))
    (hred : ∀ i < lh ds, ZDerivation (red (znth ds i))) :
    ZDerivation (red (zK s r ds)) := sorry

/-- **`redSound`, general form.** The `red`-reduct of ANY genuine `ZDerivation` is again a `ZDerivation`
(full cut-elimination soundness). Structural induction over `ZDerivation`; the two deep cases delegate to
`zKValid_iIndReduct_of_zInd` (Ind) and `ZDerivation_red_zK` (K). -/
theorem redSoundGen : ∀ d : V, ZDerivation d → ZDerivation (red d) := by
  apply zDerivation_induction (P := fun d : V => ZDerivation (red d))
  · definability
  · intro C hC d hphi
    rcases hphi with ⟨s, rfl, hin⟩ | ⟨s, a, p, d0, rfl, hd0, hsucc, hwff⟩ |
      ⟨s, p, d0, rfl, hd0, hsucc, hwff⟩ |
      ⟨s, at', p, d0, d1, rfl, hd0, hd1, hwff⟩ | ⟨s, r, ds, rfl, hds, hmem, hvalid⟩ |
      ⟨s, p, k, rfl, hp, hin⟩ | ⟨s, p, rfl, hp, hin⟩
    · -- zAtom: red = identity
      rw [red_zAtom]; exact zDerivation_iff.mpr (Or.inl ⟨s, rfl, hin⟩)
    · -- zIall: red = d0 (the premise)
      rw [red_zIall]; exact (hC d0 hd0).1
    · -- zIneg: red = d0
      rw [red_zIneg]; exact (hC d0 hd0).1
    · -- zInd: red = chain reduct; residual supplies validity
      have hZ : ZDerivation (zInd s at' p d0 d1) := zDerivation_iff.mpr
        (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨s, at', p, d0, d1, rfl, (hC d0 hd0).1, (hC d1 hd1).1, hwff⟩))))
      rw [red_zInd, iRInd_zInd, zDerivation_iff]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨s, irk p, iIndReductSeq d0 d1 1, rfl, iIndReductSeq_seq d0 d1 1,
          fun i hi => znth_iIndReductSeq_ZDerivation (hC d0 hd0).1 (hC d1 hd1).1 i hi,
          zKValidF_iIndReduct_of_zInd hZ⟩))))
    · -- zK: the dispatch; residual supplies validity-preservation
      exact ZDerivation_red_zK
        (zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨s, r, ds, rfl, hds, fun i hi => (hC (znth ds i) (hmem i hi)).1, hvalid⟩))))))
        (fun i hi => (hC (znth ds i) (hmem i hi)).2)
    · -- zAxAll: red = identity
      rw [red_zAxAll]; exact zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨s, p, k, rfl, hp, hin⟩))))))
    · -- zAxNeg: red = identity
      rw [red_zAxNeg]; exact zDerivation_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨s, p, rfl, hp, hin⟩))))))

/-- **M1b — THE nut.** The `red`-reduct of a contradiction derivation is again a genuine `ZDerivation`.
(Re-pointed `RedSound`, off the dead `iR2`.) Now a direct corollary of the general `redSoundGen`. -/
theorem redSound : ∀ d : V, ZDerivesEmpty d → ZDerivation (red d) :=
  fun d h => redSoundGen d h.1

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
