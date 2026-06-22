# Hdom assembly — ready-to-compile draft (append after the chain + B calculus, in ONE wip unit)

Once `wip/Domination.lean` (chain, `namespace GoodsteinPA.Dom`) compiles, MERGE it with
`wip/LowerBoundHardy.lean` (the `B` calculus + `lowerBound_hardy`) into one file so both are visible
(wip can't import wip). Then append the following. Uses `G n = goodsteinLength n` via
`sInf_zeroSet_eq_goodsteinLength` (port from `wip/GoodsteinLength.lean` — note the chain already
includes `goodsteinLength`/`goodstein_terminates`, so just add the `sInf` bridge).

```lean
open GoodsteinPA.FastGrowing

/-- Iterating a strictly-inflationary map adds ≥ the iteration count. -/
theorem add_le_iterate_of_lt {g : ℕ → ℕ}
    (hstep : ∀ y, 1 ≤ y → y + 1 ≤ g y) (hpos : ∀ y, 1 ≤ y → 1 ≤ g y) :
    ∀ (j : ℕ) {y : ℕ}, 1 ≤ y → y + j ≤ g^[j] y := by
  intro j
  induction j with
  | zero => intro y hy; simp
  | succ j ih =>
    intro y hy
    rw [Function.iterate_succ_apply]
    have h1 : 1 ≤ g y := hpos y hy
    have hstepy : y + 1 ≤ g y := hstep y hy
    have := ih (y := g y) h1
    omega

/-- **Hdom, strict.** For NF α, Goodstein length eventually strictly exceeds `hardy α`. -/
theorem hardy_lt_goodsteinLength {α : ONote} (hα : α.NF) :
    ∃ N, ∀ m, N ≤ m → hardy α m < goodsteinLength m := by
  -- dominate at osucc α to get the +2 slack swallowed by the fastGrowing/hardy gap
  obtain ⟨N, hN⟩ := goodsteinLength_dominates_fastGrowing (osucc_NF hα)
  refine ⟨max N 4, fun m hm => ?_⟩
  have hm4 : 4 ≤ m := le_trans (le_max_right _ _) hm
  have hmN : N ≤ m := le_trans (le_max_left _ _) hm
  -- fastGrowing (osucc α) m = (fastGrowing α)^[m] m
  have hfs : fastGrowing (osucc α) m = (fastGrowing α)^[m] m := by
    rw [ONote.fastGrowing_succ (osucc α) (fundamentalSequence_osucc hα)]
  -- (fastGrowing α)^[m] m = (fastGrowing α)^[m-1] (fastGrowing α m) ≥ fastGrowing α m + (m-1)
  have hstep : ∀ y, 1 ≤ y → y + 1 ≤ fastGrowing α y := fun y hy => lt_fastGrowing α hy
  have hpos : ∀ y, 1 ≤ y → 1 ≤ fastGrowing α y := fun y hy => le_trans hy (le_fastGrowing α y)
  have hiter : fastGrowing α m + (m - 1) ≤ (fastGrowing α)^[m - 1] (fastGrowing α m) :=
    add_le_iterate_of_lt hstep hpos (m - 1) (hpos m (by omega))
  have hsplit : (fastGrowing α)^[m] m = (fastGrowing α)^[m-1] (fastGrowing α m) := by
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m-1, by omega⟩   -- VERIFIED standalone
    simp [Function.iterate_succ_apply]
  have hHF : hardy α m ≤ fastGrowing α m := hardy_le_fastGrowing α m (by omega)
  -- combine: hardy α m + 3 ≤ fastGrowing α m + (m-1) ≤ (fastGrowing α)^[m] m = fastGrowing(osucc α) m
  --          ≤ goodsteinLength m + 2  ⟹ hardy α m < goodsteinLength m
  have hdom := hN m hmN          -- fastGrowing (osucc α) m ≤ goodsteinLength m + 2
  rw [hfs, hsplit] at hdom
  omega  -- from hHF, hiter (m-1 ≥ 3), hdom
```

Caveats to fix at compile:
- `ONote.fastGrowing_succ` exact form: in `wip/FastGrowing.lean` it was used as `rw [fastGrowing_succ o e]`
  turning `fastGrowing o n` ⟿ `(fastGrowing a)^[n] n`. Adjust `hfs` accordingly (may need to apply at `m`).
- `hsplit`: `g^[m] m = g^[m-1] (g m)`. `Function.iterate_succ_apply : g^[n+1] x = g^[n] (g x)`. With
  `m = (m-1)+1`: `g^[m] m = g^[(m-1)+1] m = g^[m-1] (g m)`. So `rw [show m=(m-1)+1.., iterate_succ_apply]`
  on the OUTER m only (the argument m must stay). Use `conv` to target the exponent. The `sorry` is
  purely this rewrite bookkeeping.
- Final `omega`: needs `hHF : hardy α m ≤ fastGrowing α m`, `hiter : fastGrowing α m + (m-1) ≤ T`,
  `hsplit/hfs` so `hdom : T ≤ goodsteinLength m + 2`, and `m-1 ≥ 3` (from m≥4). Then
  `hardy α m ≤ fastGrowing α m`, and `fastGrowing α m + 3 ≤ fastGrowing α m + (m-1) ≤ T ≤ gL m + 2`,
  so `hardy α m + 3 ≤ gL m + 2`, i.e. `hardy α m < gL m`. ✓ (treat T, fastGrowing α m, hardy α m, gL m as omega vars)

/-- **Hdom in the `Hdom` shape `lowerBound_hardy` consumes.** -/
theorem Hdom_of_NF {α : ONote} (hα : α.NF) (k : ℕ) :
    ∃ x, hardy α (max k x) < G x := by
  obtain ⟨N, hN⟩ := hardy_lt_goodsteinLength hα
  refine ⟨max N k, ?_⟩
  have hxk : k ≤ max N k := le_max_right _ _
  have hxN : N ≤ max N k := le_max_left _ _
  rw [max_eq_right hxk]                              -- max k (max N k) = max N k since k ≤ max N k
  rw [show G (max N k) = goodsteinLength (max N k) from sInf_zeroSet_eq_goodsteinLength _]
  exact hN _ hxN

-- Then: `lowerBound_hardy (Hdom_of_NF hα k) : ¬ B α k {gAll}` — fully self-contained Thm 17.1.
```

This makes `lowerBound_hardy` self-contained (no `Hdom` hypothesis) for any NF α. The only `sorry`
above is the `hsplit` iterate-rewrite, which is pure bookkeeping — close at compile.
