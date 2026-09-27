# PH treadmill direction (stage 3: PA ⊬ Paris–Harrington)

**Objective:** make `src/GoodsteinPA/PH/Main.lean` sorry-free.  Its two statements,
`pa_not_proves_ph` and `exists_sigma1_ph_def`, are RATIFIED and frozen.  Never change them,
and never touch `src/GoodsteinPA/Statement.lean` (mathlib PR #41337 links it).  Same for
`PH/Statement.lean`, except that you may add known-answer `example`s.

Branch `eps0/ph`.  Commit every green checkpoint with `git-safe`.  Do not push, and do not
open PRs.  Keep a short dated log at the bottom of this file, which is the lap-to-lap handoff.

## Hard rules
- No new `axiom`.  `native_decide` is acceptable (the repo already uses it in `ONoteComp`).
- Do not `lake update` anything.  LeanGallery is pinned by hand at `47b095d`, and an update
  drags in mathlib v4.33.1.
- The main lib builds with warnings as errors, so work-in-progress files stay OUT of
  `GoodsteinPA.lean` until they are sorry-free.  Check them with `lake env lean <file>`.
- Once `Main.lean` is sorry-free:
  - import it (and `PH/Computable.lean` etc.) from `src/GoodsteinPA.lean`;
  - add `#print axioms` pins for both theorems to `scripts/AxiomCheck.lean` (see the hydra pins);
  - run `lake build`.
- Add the anchor `example : ¬ PH 1 0 0 0 := by decide` to `PH/Statement.lean` (degenerate case
  `PH e 0 k N ↔ e ≤ N`).

## Part A: `exists_sigma1_ph_def` (routine; do this first)
`src/GoodsteinPA/PH/Computable.lean` is a work-in-progress sketch and **does not compile yet**.
Rewrite freely.  The design:

- Masks.  Put `B := N + 1`.  A subset of `Icc 1 N` is a mask `h < 2^B` with bit 0 clear.
  - Set of a mask: `bitsB B n := (range B).filter (n.testBit ·)`.
  - Mask of a set: `code s := ∑ i ∈ s, 2^i`.
  - Mathlib (`Mathlib/Combinatorics/Colex.lean`, namespace **`Finset.Nat`**) has
    `toFinset_bitIndices_sum_two_pow` and `sum_toFinset_bitIndices_two_pow`.
  - Mathlib (`Data/Nat/BitIndices.lean`) has `Nat.mem_bitIndices : i ∈ n.bitIndices ↔ n.testBit i`.
  - From these: `testBit (code s) j ↔ j ∈ s`.
  - Init has `Nat.lt_pow_two_of_testBit`, `Nat.testBit_eq_false_of_lt`, `Nat.eq_of_testBit_eq`,
    and `Nat.testBit_eq_decide_div_mod_eq : testBit x i = decide (x / 2^i % 2 = 1)`.
  - Popcount: `pop B n := ((List.range B).filter (n.testBit ·)).length`, which equals
    `(bitsB B n).card`.
- Colourings.  One number `C < r^(2^B)`; the colour of mask `t` is `C / r^t % r`.
  - `pack` / `digit_pack` / `pack_lt` in the sketch already compile.
  - For PHbits → PH, pack the list
    `(List.range (2^B)).map fun t => if hs : bitsB B t ∈ (Icc 1 N).powersetCard e then c ⟨_, hs⟩ else 0`.
- The bounded form:
  ```
  PHbits e r k N :=
    (r = 0 ∧ e ≤ N) ∨
    (0 < r ∧ ∀ C < r^2^B, ∃ h < 2^B, h.testBit 0 = false ∧ k ≤ pop B h ∧
       (∀ a < B, h.testBit a → (∀ b < a, h.testBit b = false) → a ≤ pop B h) ∧
       ∃ i < r, ∀ t < 2^B, (∀ j < B, t.testBit j → h.testBit j) → pop B t = e → C / r^t % r = i)
  ```
- Prove `PHbits e r k N ↔ PH e r k N`.
  - `r = 0`: `PH e 0 k N ↔ e ≤ N`.
    - If `N < e` the domain is empty (`Finset.powersetCard_eq_empty`) and `Homog` needs a
      `Fin 0`, so PH fails.
    - If `e ≤ N`, `Finset.exists_subset_card_eq` gives a domain element, so no colouring exists
      and PH holds vacuously.
  - PH → PHbits.  Colour a set by its digit `c s := C / r^(code s) % r`, and take `h := code H`.
  - PHbits → PH.  Take `H := bitsB B h` and use the packed `C`.
- `PrimrecRel` of `PHbits` (or of `PHx`), built with:
  - Mathlib: `PrimrecRel.forall_lt` / `exists_lt` (the bound is the first argument, the
    parameter tuple the second), `PrimrecRel.comp`, `PrimrecPred.and/or/not/of_eq`,
    `Primrec.nat_div/nat_mod/eq/nat_le/nat_lt`, `Primrec.list_length/list_range`,
    `PrimrecPred.listFilter`, `Primrec.ite`;
  - the repo: `GoodsteinPA.primrec_natPow`.
  - Express `testBit` through `/ 2^j % 2 = 1`.
- Existence: copy `exists_sigma1_battle_def` in `src/GoodsteinPA/HydraComputable.lean`.
  - Use `phC x N := if PHbits' x N then 0 else 1`, wrapped as a `List.Vector ℕ 2 → Part ℕ` with
    `Nat.Partrec'.of_part`, then `Arithmetic.codeOfPartrec'`.
  - `PHx` unpacks `x = ⟪e, ⟪r, k⟫⟫` with `Nat.unpair`.

## Part B: `pa_not_proves_ph` (the hard part)

**UPDATE 2026-09-26 (Ren): Part B is being done separately on branch `eps0/ph-lb`
(skeleton `src/GoodsteinPA/PH/LB/*.lean`, parallel provers).  Do NOT start Part B here.  When Part A is
complete (Computable.lean green, `exists_sigma1_ph_def` proved in Main.lean, anchors added), record it
in the Log, commit, and stop the treadmill with `box done` / self-stop.**
- `PH/Independence.lean` already proves `pa_not_proves_ph_of_escape`.  What remains is proving
  `Escapes`.
- Follow `STAGE3-PH-PLAN.md`, steps 1–7.
  - Source: `papers/ph-buchholz-bewth98.pdf` (pp. 46–49, PDF pages 47–50); a text dump sits
    beside it at `papers/ph-buchholz-bewth98.txt` in the main checkout.
  - Use the repo's `hardy`: Mathlib fundamental sequences, and `hardy_limit` has no `+1`.
  - Reuse the stage-2 machinery:
    - `HydraLowerBound.lean`: the P2 descent argument by well-founded induction on `repr`;
    - `HydraEscape.lean`: the P3 composition via `fastGrowing_le_hardy_omega_pow`,
      `hardy_add_comp` and `hardy_le_of_lt`.
- Decompose freely into named sorried lemmas in new files under `src/GoodsteinPA/PH/`.  Raising
  the sorry count by splitting is progress.  Record the lemma map in this file.

## Log
- 2026-09-26: direction written (Ren, attended session).  Part A sketch in `PH/Computable.lean`
  (not compiling).  Target: `PH/Main.lean`.
- 2026-09-27 (lap 1, autonomous): **Part A COMPLETE.**  `src/GoodsteinPA/PH/Computable.lean`
  rewritten and green; `exists_sigma1_PHx_def` is kernel-clean `[propext, choice, Quot.sound]`
  and wired into `PH/Main.lean`'s `exists_sigma1_ph_def`.  Lemma map:
  `bits`/`code`/`lt_two_pow_iff`/`bits_subset_Icc` (mask ↔ subset of `Icc 1 N`),
  `bit1`/`popL`/`popL_eq_card` (arithmetic bit tests), `pack`/`digit_pack`/`pack_lt` (colouring
  packing), `Colour`/`SubMask`/`HomogBits`/`RelLargeBits`/`PHbits`, `ph_zero`, **`PHbits_iff`**
  (`PHbits ↔ PH`), then `forall_ltb`/`exists_ltb`/`bAll`/`bEx`/`prImp` (parameterised bounded
  quantifiers — mathlib's `PrimrecRel.forall_lt` hardwires `β = ℕ`, these generalise it),
  `primrecRel_bit1`, `primrec_popL`, `primrecRel_SubMask`, `primrecRel_homogBody`,
  `primrecPred_homogBits`, `primrecRel_relLargeBits`, `primrecRel_witness`,
  **`primrecPred_PHbits`**, `PHbitsx`, `primrecRel_PHbitsx`, `phC`, `primrec_phC`, `phVec`,
  `partrec_phVec`, `exists_sigma1_PHx_def`.  `PH/Independence.lean` + `PH/Computable.lean` are
  now in `GoodsteinPA.lean`.  Anchor `¬ PH 1 0 0 0` added to `PH/Statement.lean`.
  Mathlib-name notes (pinned v4.31 mathlib): the colex bit lemmas are
  `Finset.toFinset_bitIndices_sum_two_pow` / `Finset.sum_toFinset_bitIndices_two_pow`
  (**no** `Nat` namespace, and `Nat.equivBitIndices` does not exist); `Finset.range_succ` is
  `Finset.range_add_one`; `Colex`/`Primrec` do not transitively import `norm_num`/`ring`.
  **Next: Part B (`Escapes`).**
