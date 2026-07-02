import GoodsteinPA.OperatorZef2

/-!
# lap-11 SERIES-1 Stage-3 CUT TOP-RANK PROBE — the `hg_base` floor seam

`passAux` (the cut-elimination pass over `Zef2`) is at 5/6 cases; the remaining sub-`sorry` is the
TOP-RANK cut (`χ.complexity = c`).  The designed discharge (per the SERIES-1 order + lap-189 handoff)
is: IH-reduce both premises to rank `c`, then apply the principal ∀/∃ reduction
`stepAllω_Zf2` / `stepAllω_Zf2_bnd`.  That reduction's signature carries a **growth-floor**
hypothesis on the ∀-side slot `g`:

    hg_base : ∀ k, g 0 + k ≤ g k

used (via `base_add_le_comp` → `ewN_add_le_comp`) to close every rebuilt node's gate
`ewN (α + γ) ≤ (g ∘ f) 0 = g (f 0)` from the two additive input gates `ewN α ≤ g 0`, `ewN γ ≤ f 0`.

**The seam.**  The pass threads only `Monotone f ∧ (∀x,x≤f x) ∧ (∀m, 2m+1 ≤ f m)` — chosen at
lap 189 precisely because these three are `rel1`-STABLE (the node gate `ewN_collapse_le` needs only
`2m+1`, and `rel1_low` preserves it).  At a top-rank cut the ∀-side reduced slot is `ewIter s βφ`
where `s` is the pass slot AT THAT NODE — and inside an `allω` branch `s` is a `rel1`-relativized
slot, which has a `max`-PLATEAU.  This file kernel-checks that the pass's invariant does **NOT**
entail `hg_base`, and isolates exactly where the seam bites.

The upshot for the grind: the base floor `g 0 + k ≤ g k` is a *relative-to-`g 0`* lower bound, and
`g 0` JUMPS under `rel1` (`(rel1 t n) 0 = t n`, the plateau top), so — unlike the absolute lower
bound `2m+1 ≤ g m` — it is not `rel1`-stable.  See `basefloor_not_rel1_stable` below.

**Ruling-grade guarantee (judge check, lap-194).**  The refuting slot `gRel = rel1 tBase 3`
SATISFIES the pass's full threaded kit — `gRel_mono` (Monotone), `gRel_infl` (`∀x, x ≤ gRel x`),
`gRel_low` (`∀m, 2m+1 ≤ gRel m`) are all kernel-proven below — so it is exactly a slot the pass can
produce at a `rel1`-relativized `allω` branch.  A floor-failure from a non-pass-producible `s` would
refute nothing; `basefloor_not_rel1_stable` bundles the four facts (mono ∧ infl ∧ 2m+1 ∧ ¬hg_base)
into a single kernel-checked witness, so the refutation is ruling-grade, not a shape artifact.
-/

namespace GoodsteinPA.OperatorZeh

open ONote

/-- The base slot `t m = 2m+1`: monotone, inflationary, meets its own `2m+1` floor, AND satisfies
the growth floor `t 0 + k ≤ t k` (it is strictly monotone). -/
def tBase : ℕ → ℕ := fun m => 2 * m + 1

theorem tBase_mono : Monotone tBase := fun _ _ h => by simp only [tBase]; omega
theorem tBase_infl : ∀ x, x ≤ tBase x := fun x => by simp only [tBase]; omega
theorem tBase_low : ∀ m, 2 * m + 1 ≤ tBase m := fun m => by simp only [tBase]; omega
theorem tBase_floor : ∀ k, tBase 0 + k ≤ tBase k := fun k => by simp only [tBase]; omega

/-- The relativized slot `g = rel1 tBase 3` — exactly the shape a slot takes inside an `allω`
branch (`rel1 (currentSlot) n`).  It STILL satisfies all three threaded invariants… -/
def gRel : ℕ → ℕ := rel1 tBase 3

theorem gRel_mono : Monotone gRel := rel1_monotone tBase_mono 3
theorem gRel_infl : ∀ x, x ≤ gRel x := rel1_infl tBase_infl 3
theorem gRel_low : ∀ m, 2 * m + 1 ≤ gRel m := rel1_low tBase_mono tBase_low 3

/-- …but it **VIOLATES** the growth floor `g 0 + k ≤ g k`: at `k = 1`, `g 0 = tBase 3 = 7`,
`g 1 = tBase (max 3 1) = tBase 3 = 7`, so `g 0 + 1 = 8 ≤ 7` is false.  The `max`-plateau eats the
increment.  **Kernel-verified** the pass's invariant does not entail `hg_base`. -/
theorem gRel_floor_fails : ¬ (∀ k, gRel 0 + k ≤ gRel k) := by
  intro h
  have := h 1
  simp only [gRel, rel1, tBase] at this
  omega

/-- **The seam, stated as a stability failure.**  There is a slot `g` with the pass's full invariant
(`Monotone ∧ inflationary ∧ 2m+1-floored`) for which the growth floor `hg_base` fails — so no lemma
can derive `hg_base` from the threaded invariant alone.  The `stepAllω_Zf2` discharge of the
top-rank cut therefore cannot fire at a `rel1`-relativized slot as the pass currently threads it. -/
theorem basefloor_not_rel1_stable :
    ∃ g : ℕ → ℕ, Monotone g ∧ (∀ x, x ≤ g x) ∧ (∀ m, 2 * m + 1 ≤ g m) ∧
      ¬ (∀ k, g 0 + k ≤ g k) :=
  ⟨gRel, gRel_mono, gRel_infl, gRel_low, gRel_floor_fails⟩

/-- **`ewIter s 1 = s ∘ s`.**  At ordinal `1` the ball filter `{δ | δ < 1}` is the singleton `{0}`,
so the `max'` collapses to the lone `δ=0` term `ewIter s 0 (ewIter s 0 k) = s (s k)`.  This is the
smallest PRINCIPAL-capable ordinal (an `allω` at `1` has all branches at `0`). -/
theorem ewIter_one (s : ℕ → ℕ) (k : ℕ) : ewIter s 1 k = s (s k) := by
  have h0α : (0 : ONote) < 1 := oadd_pos 0 1 0
  have hα : (1 : ONote) ≠ 0 := h0α.ne'
  apply le_antisymm
  · conv_lhs => rw [ewIter_unfold s 1 k]
    rw [ewStep]
    simp only [dif_neg hα]
    apply Finset.max'_le
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨δ, hδmem, rfl⟩
    have hδlt : (δ : ONote) < 1 := (Finset.mem_filter.mp δ.2).2.1
    have hδ0 : (δ : ONote) = 0 := by
      by_contra hne
      have hpos : (0 : ONote) < (δ : ONote) := by
        rcases hd : (δ : ONote) with _ | ⟨e, n, a⟩
        · exact absurd hd hne
        · exact hd ▸ oadd_pos e n a
      have hr : (δ : ONote).repr < 1 := by simpa [repr_one] using lt_def.mp hδlt
      have hr0 : (δ : ONote).repr = 0 := Order.lt_one_iff.mp hr
      have hposr : 0 < (δ : ONote).repr := by simpa [repr_zero] using lt_def.mp hpos
      rw [hr0] at hposr
      exact absurd hposr (lt_irrefl 0)
    rw [hδ0]
    simp [ewIter_zero]
  · have hlow := ewIter_lower (f := s) (β := 0) (α := 1) (m := k) h0α (Nat.zero_le _)
    simpa [ewIter_zero] using hlow

/-- **The floor fails at the PRINCIPAL ordinal `β = 1` too.**  With the flat slot `gRel`
(`gRel 0 = gRel 1 = 7`), `ewIter gRel 1 = gRel ∘ gRel` is flat on `{0,1}`
(`ewIter gRel 1 0 = gRel (gRel 0) = gRel 7 = 15 = ewIter gRel 1 1`), so
`ewIter gRel 1 0 + 1 ≤ ewIter gRel 1 1` is `16 ≤ 15` — false.  **This kills escape lane (A)**: the
`βφ ≠ 0` base floor does NOT hold in general — the ball at `β=1` is the singleton `{0}`, so there is
no ball-growth to restore the increment, and `gRel ∘ gRel` inherits the plateau. -/
theorem ewIter_one_floor_fails : ¬ (∀ k, ewIter gRel 1 0 + k ≤ ewIter gRel 1 k) := by
  intro h
  have h1 := h 1
  rw [ewIter_one, ewIter_one] at h1
  simp only [gRel, rel1, tBase] at h1
  omega

/-!
## Reading of the probe — the wall is REAL (both escape lanes measured)

`basefloor_not_rel1_stable` lands at `β = 0` (`g = ewIter s 0 = s`, the relativized slot itself).
`ewIter_one_floor_fails` lands at the **principal-reachable** `β = 1` (an `allω` at `1` has all
branches at `0`).  Together they settle the `hg_base` question BOTH ways:

  (A) **Principality split — REFUTED.**  The hope was that at a *principal* ∀ (`βφ ≠ 0`) the ball
      radius `K_k = s (ewN βφ + k)` grows with `k`, admitting larger `δ`-terms that restore the
      per-step increment even where `s` plateaus.  `ewIter_one_floor_fails` KILLS this: at `βφ = 1`
      the ball `{δ | δ < 1}` is the singleton `{0}` — NO ball-growth — so `ewIter s 1 = s ∘ s`
      inherits `s`'s plateau verbatim and the floor fails (`16 ≤ 15`).  `βφ = 1` is exactly a
      principal top-rank ∀ (branches at `0`), so the split does not save the discharge.

  (B) **Reduction re-gate via the `2m+1` floor + a tight family-ordinal bound (PROOF-only, the live
      lane).**  The fresh-node gate `ewN (α₁ + γ') ≤ g (f' 0)` need NOT go through `hg_base`.  The
      reduced ∀-side slot `g = ewIter s βφ` inherits the `rel1`-stable floor `2m+1 ≤ g m` (for
      `βφ = 0`, `g = s`; for `βφ ≠ 0`, `g m ≥ s(s m) ≥ 2m+1`), so `g (f' 0) ≥ 2·(f' 0) + 1`.  Then
      `ewN(α₁+γ') ≤ ewN α₁ + ewN γ'`, `ewN γ' ≤ f' 0` (the ∃-node gate), and `f' 0 ≥ s 0`, so the
      gate closes AS LONG AS the ∀-side family ordinal has the TIGHT norm bound `ewN α₁ ≤ s 0 + 1`
      (giving `ewN α₁ + f' 0 ≤ (s0+1) + f'0 ≤ 2 f'0 + 1 ≤ g(f'0)`).  This replaces the whole
      `hg_base` machinery and needs NO statement change — but requires (i) a floor-based re-proof of
      `cutReduceAllAuxRunning`'s gate discharge, and (ii) `passAux` to EXPOSE `ewN α₁ ≤ s 0 + 1` on
      its output witness.  ⚠️ **Open sub-problem for (ii):** the tight bound `ewN(witness) ≤ f 0 + 1`
      is inductive through `axL`/`wk`/`weak`/`exI`/`allω`/`cut`-sub-rank (all produce a
      `collapse α` witness with `ewN = ewN α + 1 ≤ f 0 + 1` via the node gate `ewN α ≤ f 0`, and
      `wk`/`weak` pass the SAME slot through) — but the top-rank `cut` OUTPUT has
      `ewN ~ ewN α₁ + ewN γ₁ ~ 2(f 0)+2`, breaking `≤ f 0 + 1`.  So the tight bound must be relaxed
      for cut outputs, OR the ∀-premise of a principal cut must be shown to reduce to a
      collapse-shaped (tight-norm) witness because its `∀χ'`-introducing spine is `allω`-headed.
      This is the decisive remaining design question for the top-rank cut.

  (C) **Invariant amendment (judge-gated fallback).**  If (B)(ii) cannot be closed, strengthen the
      pass invariant / restate the reduction — a STATEMENT change, FORBIDDEN to self-ratify under the
      SERIES-1 order; escalate to the ledger.

**Status.**  Lap-189's assumed discharge (IH-reduce → `stepAllω_Zf2`, needing `hg_base`) is
kernel-refuted as incompatible with the `rel1`-stable invariant (this file).  Lane (B) is a viable
PROOF-only route pending its sub-problem (ii); pursue it before escalating.  Recorded to
`REBUILD-Z-SERIES-1-LEDGER.md` and `PENDING_WORK.md`.
-/

end GoodsteinPA.OperatorZeh
#print axioms GoodsteinPA.OperatorZeh.ewIter_one_floor_fails
#print axioms GoodsteinPA.OperatorZeh.basefloor_not_rel1_stable
