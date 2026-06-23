# Pending work — open obligations & attack paths

## ⭐⭐⭐ Lap 52 — crux-1 bricks 1 + 2-core BUILT (green, axiom-clean, wip)
Discharged the two `wip/StdCor34` interface obligations' substrate (lap-51 designated NEXT):

- **Brick 1 DONE — `wip/BlkRec.lean`** (axiom-clean): the definable block bookkeeping `blk`/`off` as a
  single internal `𝚺₁` primitive recursion (`boStep` state machine: advance offset within a block,
  roll to next block when `off+1 ≥ W(blk)`) over an **abstract width sequence code `wseq`** (read by
  `znth wseq (blk j)`) — sidesteps internal `findGreatest`. Proves exactly the `StdCor34.salpha`
  bookkeeping hyps: `blk_succ_dich` (= `hblk_dich`), `off_succ_of_blk_eq` (within-block off-advance,
  behind `higt_within`), `blk_add_off_le` (= `hnm`) ⟹ `blk_le` (for `hβC`). Independent of β.

- **Brick 2 CORE DONE — `wip/IIter.lean`** (axiom-clean): the reusable internal-iterate primitive
  `iIter fDef f hf x c = f^[c] x` for a **fixed** `𝚺₁`-function `f` (graph `fDef`) at an **internal**
  count `c : V`, as a `PR.Construction` with both recurrence laws + `𝚺₁`-definability of `(x,c) ↦ f^[c]x`
  + `iIter_natCast` (standard `k` ⟹ meta-iterate `f^[k]`). This is the engine `iF (l+1) n = (iF l)^[n] n`
  needs (internal iteration at standard meta-level l ⟹ NO internal Ackermann).

**Brick 2 — `iF` + `ipsum` substrate DONE (`wip/IIter.lean`, axiom-clean); REMAINING = block-decomp + `ig`:**
- ✅ `iF : ℕ → (V → V)` built by meta-recursion (Subtype bundle `iFwith` carries function+Def+proof):
  `iF_zero`/`iF_succ`/`iF_defined` + `iF_natCast` (standard agreement `iF l ↑k = ↑(Grz.F l k)`).
- ✅ `ipsum f n i = Σ_{t=1}^i f^[t] n` (`Grz.psum` internalized): `ipsum_zero`/`ipsum_succ`/`ipsum_defined`
  + monotonicity. Generic over the fixed `𝚺₁`-fn `f`, so it serves every `iF l`.
- ✅ `wsumc` + `wsumc_blk_le` (`wip/BlkRec.lean`, codex review lap 52): the elapsed-WIDTH invariant
  `wsumc (blk j) ≤ j` that `salpha_C_le`'s `hβC` actually needs — `blk_le` (block count) alone was an
  OVERCLAIM. `wsumc_blk_add_off : wsumc(blk j) + off j = j` (exact, under positive widths).
- ⚠️ **wseq SEAM (codex lap 52):** `BlkRec.blk/off` read the width from a finite sequence CODE `wseq`
  (`znth wseq b`); the IIter substrate (`ipsum`) reads it from a definable width FUNCTION. For crux-1
  integration these must meet. Two routes: (a) build a concrete definable global width `W t = iC(β(t+1))`
  and thread its Def (couples `BlkRec` to β); (b) **prefix-invariance** — prove `blk wseq j` depends only
  on `znth wseq b` for `b ≤ blk j` (≤ j), so a *long-enough prefix code* of the true widths gives the
  correct `blk/off`. Route (b) keeps `BlkRec` abstract; add `blk_prefix_congr`/`off_prefix_congr` next.
- ⏭ NEXT: `iblockIdx`/`iblockOff` over `iF l` (level sets of `ipsum (iF l) n`). Mirror `Grz.blockIdx`/
  `blockOff` but AVOID internal `findGreatest` — use the `BlkRec.boStep` state-machine idiom (a width
  recurrence whose width at block `i` is `iIter (iFDef l) (iF l) (iF_defined l) n (i+1)`), giving
  `psum_blockIdx_le`/`blockOff_lt_width`/`psum_add_blockOff` internally. Needs `ipsum` monotonicity +
  a `≤ n` cap (blocks `< n`). Then `iF l`/`ipsum`/block-decomp standard-agreement lemmas as needed.
1. `ig : ℕ → V → V → V` meta-recursion: `ig 0 = ig0` (built), `ig (l+1) n m = iblk (l+1) (n - iblockIdx…)
   (ig l (iF l^[…] n) (iblockOff…))` for `m < iF (l+1) n` else 0 (mirror `Grz.g`). Port `g_NF`/`g_lt`/
   `g_desc`/`g_C_bound`/`g_exp` ⟹ the `StdCor34` `igt` interface (`higtNF`/`higt0`/`higt_within`/`higtC`/
   `higt_exp`). Then `igt n m := ig l₀ n m` for the Lemma-3.2 standard level `l₀`.
Then wire `BlkRec.blk/off` + `igt` into `StdCor34.salpha_*` → `InternalThm35.bbeta` → `DescentArith.
nonterminating_internal` (Lemma 3.6) ⟹ `goodstein_implies_prwo` body (crux 1).
⚠️ Then verify the DEFERRED DEEPER SEAM (`icmp`-code ↔ `natCode`-order) before claiming crux 1.

## ⭐⭐⭐ Lap 51 — SEAM CHECKS (operator-directed): crux-1↔crux-2 chain VERIFIED at statement level
Added 3 machine-checked guards to `wip/GentzenCon.lean` (compile iff the seams hold; green modulo the
2 disclosed crux sorries):
- **Seam 1 (ONE shared PRWO):** crux 1 *outputs* `𝗣𝗔 ⊢ prwoInstance gentzenDescentφ`, crux 2 *consumes*
  the same — the composition `gentzen_prwo_implies_consistency (goodstein_implies_prwo gentzenDescentφ ·)`
  type-checks ⟹ both reference the **identical** `prwoInstance` def (same `precφ` ε₀-order). ✓
- **Seam 2 (Con is Foundation's `Con[𝗣𝗔]`):** `example (hγ) : False := peano_not_proves_consistency
  (goodstein_implies_consistency_via_gentzen hγ)` type-checks ⟹ the assembly's `↑𝗣𝗔.consistent` is
  **definitionally** the object Gödel II (`consistent_unprovable 𝗣𝗔`) forbids — not a lookalike. ✓
- **Seam 3 (end-to-end = the girder):** `not_proves_of_implies_consistency
  goodstein_implies_consistency_via_gentzen : 𝗣𝗔 ⊬ ↑goodsteinSentence` — same type as `Reduction.lean`'s
  `goodstein_implies_consistency` girder; the assembly drops in once both crux sorries are real. ✓

**⚠️ ONE DEEPER SEAM STILL DEFERRED (verify when crux-1's BODY is wired):** the above guard seam 1 only
checks the prwoInstance *def* is shared between the two crux STATEMENTS. The crux-1 *proof*
(StdCor34 slow-down → `goodstein_implies_prwo`) works on `InternalONote` codes ordered by `icmp`/`isNF`;
but `prwoInstance`/`precφ` order the descent by `natCode` (`precφ_spec : ℕ⊧![m,n] precφ ↔ natCode m <
natCode n`). So wiring crux-1's body needs the bridge **`icmp a b = 0 ↔ natCode-order`** (and
`isNF`-code ↔ valid CNF notation) — i.e. that the StdCor34 descent β (icmp-code form) IS the descent
`prwoInstance gentzenDescentφ` quantifies over. This is the F-φ-flavoured code↔order seam; check it the
moment `goodstein_implies_prwo`'s sorry starts getting filled (ANTI-FRAUD: re-`#print axioms` the route).

## ⭐⭐⭐ Lap 51 — standard-level Cor 3.4 global assembly BUILT (green); crux-1 reduced to 2 concrete bricks
Followed the lap-50 designated next action. Two deliverables, both green:
- **`isNF_iadd_clean` + `isNF_icorAlpha`** (`src/InternalCor34.lean`, axiom-clean, in the build) — the
  missing NF sibling of `icmp_iadd_clean`/`iC_iadd_clean`. Completes the `icorAlpha` brick set: the
  slowed term `ω^(l+1)·β + g` now has ALL FOUR Cor-3.4 properties (within/boundary/C-bound/NF).
- **`wip/StdCor34.lean`** (type-checks at 400k heartbeats, off the build target) — the internal
  **global** Cor-3.4 assembly: `salpha_isNF` / `salpha_desc` / `salpha_C_le` prove that the slowed
  sequence `α j = ω^(l+1)·β_{blk j} + igt(blk j)(off j)` has `isNF` + global `icmp`-descent +
  `iC(α j) ≤ K·(j+1)` — **exactly the input `InternalThm35.bbeta` (Thm 3.5) consumes** — by composing
  the `icorAlpha_*` bricks. This is NEW non-vacuous content (the ℕ-template `Grz.corAlpha_*` only has
  the per-step lemmas; the global ∀j descent is vacuous in ℕ but real inside `V ⊧ 𝗜𝚺₁`).
  GOTCHA banked: `iadd`/`icorAlpha` are semireducible → `isDefEq` whnf-loops on variable-level args
  even on identical terms; `attribute [local irreducible] iadd icorAlpha` makes defeq structural.
  And `habove`'s 3rd arg feeds `β (blk a)`, so boundary leads `β(blk(j+1))`/`β(blk j)` need `a=j+1`/`a=j`
  (NOT `blk j+1`), keeping `salpha(j+1)` un-`hb`-rewritten.

**Crux 1 now reduces to discharging the `wip/StdCor34` interface hypotheses (2 concrete bricks):**
1. **Block bookkeeping `blk`/`off`** = internal `iwsum`/`iwidx`/`iwoff` (partial sums + `findGreatest`
   over the width fn `t ↦ iC(β(t+1))`), giving the dichotomy `blk(j+1) ∈ {blk j, blk j+1}`, the offset
   relations, and `blk j + off j ≤ j`. MECHANICAL `𝚺₁` recursion (mirror `Grz.wsum`/`widx`/`woff` +
   the PR.Construction idiom in `InternalCor34.iAboveTable`). Self-contained, axiom-clean-achievable.
2. **The `ig`-tail recursion `igt n m`** = internal Grzegorczyk `g` (`Grz.g`) at STANDARD level: NF /
   `≠0` / within-block descent / `iC ≤ Kg·(n+m+1)` / `iAbove(ocExp(igt n m)) (ω^(l+1)·…)`. Bottoms at
   `ig0`/`iblk` (built); the deep part is the meta-l recursion over the F-block decomposition, needing
   internal `iF_l` (standard l ⟹ fixed primrec, IΣ₁-total — NO internal Ackermann).
Then wire `salpha` → `bbeta` → `DescentArith.nonterminating_internal` (Lemma 3.6) → contradicts γ =
`goodstein_implies_prwo` (crux 1). **THE remaining hard wall stays crux-2 eq (5)** `ord(R d) ≺ ord d`.

## ⭐⭐⭐⭐ Lap 50 KEY INSIGHT — crux 1 for the HEADLINE needs only STANDARD level (internal-Ackermann wall is OFF-path)
Re-derived + paper-validated (Rathjen `scratchpad/rathjen.txt:401`, Lemma 3.2). Memory
`crux1-headline-needs-only-standard-level`. **This re-frames the project's hardest crux.**

- `goodstein_implies_consistency = crux2 ∘ crux1` uses crux 1 at the **single instance**
  `seq = gentzenDescentφ` (= graph of `n↦ord(Rⁿd₀)`), NOT for all primrec descents (PRWO is a schema).
- `H(n,d)=ord(R^[n]d)` is a **concrete** primrec function ⟹ Lemma 3.2 gives a **STANDARD** Grzegorczyk
  level `n₀` (PA-provable bound, independent of the internal arg `d₀`). `f_{n₀}` is then a fixed primrec
  fn, IΣ₁-total, evaluable at internal `d₀`. **No internal Ackermann.** The laps-45→49 internal-`l`
  conclusion was correct only for FULL PRWO (∀ internal-index descent) — the headline never needs that.
- ⟹ **crux 1 downgraded from generational to tractable engineering.** Build STANDARD-level internal
  Cor 3.4 (abstract over a descent with a STANDARD-l domination hyp `∃ l:ℕ, ∀n, C(β(n+1))≤f_l n`):
  * Reuse the ABANDONED standard lead `InternalCor34.ibigMul (k:ℕ)` + `ig0`/`iblk` (the lap-49 generic-V
    `iVbigMul`/`icorAlpha` tower was unneeded effort for the headline — keep banked, not on the path).
  * Blueprint = sorry-free ℕ-template `Grzegorczyk.lean` (`corAlpha`/`corAlpha_C_bound`/`_within`/`_boundary`,
    `g`/`g_desc`/`g_C_bound`, `F`).
  * Downstream DONE: internal Thm 3.5 (`InternalThm35.bbeta_*`), Lemma 3.6 (`DescentArith.nonterminating_internal`).
  * Discharge the standard-l domination for the gentzen descent via Lemma 3.2 once `ord`/`R` exist.
- **THE remaining hard wall is now crux 2's eq (5)** `ord(R d) ≺ ord d` (Gentzen reduction, Buchholz [6];
  Foundation Hauptsatz is meta-level only ⟹ from-scratch arithmetization). Crux 1 is no longer the bottleneck.
- ⚠️ NOT yet built/verified — validate the standard-level internal Cor 3.4 type-checks + `#print axioms`
  clean before relabeling crux 1 done.

**NEXT-LAP first action:** start `wip/StdCor34.lean` (or extend `InternalCor34`) — the standard-level
abstract Cor 3.4 over `ibigMul`, mirroring `Grz.corAlpha_*`. Then wire to `InternalThm35` + Lemma 3.6.

## ⭐⭐⭐ Lap 50 (2026-06-23) — REVIEW + crux-2 PRWO formulation BUILT & faithfulness-certified
Fresh-mind review. **Direction KEEP** (Route A = Rathjen Cor 3.7). Crux-1 step-3 (internal `ig`
f-recursion → internal Grzegorczyk `F`, Ackermann-level) is **blocked on infra Foundation lacks** —
so this lap advanced the *unblocked* **crux 2** (Gentzen `PRWO→Con`), per the lap-49 handoff.

**Foundation map (Explore, lap 50):** NO universal evaluator / Kleene-T predicate (`code`/
`codeOfPartrec'`/`codeOfREPred` all encode a *meta* function into a *fixed* formula). ⟹ **PRWO must be
a per-formula schema**, which is exactly what the proof needs (crux 1 proves all instances; crux 2 uses
the one for `n↦ord(Rⁿd₀)`). `Con(𝗣𝗔)` = `Theory.consistent : 𝚷₁.Sentence`; Gödel II =
`consistent_unprovable [T.Δ₁][𝗜𝚺₁⪯T][Consistent T]`; arithmetized derivations =
`Theory.Derivation : V→Prop` (`Bootstrapping/Syntax/Proof/Basic.lean:459`); Hauptsatz is **meta-level
only** (not arithmetized — no shortcut for eq 5). See memory `crux2-prwo-schema-no-universal-evaluator`.

**DONE this lap (`wip/GentzenCon.lean`, type-checks, 2 disclosed crux sorries):**
- `prwoInstance seq := “¬∀ n y z, (!seq y n ∧ !seq z (n+1)) → !precφ z y”` — reuses `SeamDefinability.precφ`
  (the ε₀-ordering ℒₒᵣ-formula); no `isNF` needed (`natCode : ℕ ≃ NONote` bijects onto all CNF).
- **`prwoInstance_faithful` PROVED** (`ℕ⊧prwoInstance seq ↔ ¬∀n y z, seq[y,n]→seq[z,n+1]→natCode z<natCode y`;
  axioms = trust base + 1 🟢 F-φ native_decide) — the formulation is **kernel-certified faithful**.
- `gentzenDescent_descends`/`derivesEmpty_iterate` PROVED (the `n↦ord(Rⁿd)` descent from `ord_R_descends`).
- assembly `goodstein_implies_consistency_via_gentzen` = `crux2 ∘ crux1` type-checks = the `Reduction.lean`
  girder interface (validates the architecture).

**NEXT — crux-2 deep cores (hardest-first), all in `wip/GentzenCon.lean`:**
1. **`ord_R_descends` (eq 5)** — THE Gentzen reduction ordinal-descent. Ground in Buchholz [6]
   (`papers/buchholz-on-gentzens-first-consistency-proof.pdf` + `siders-…pdf`). Hardest.
2. **`ord`/`R` as arithmetized primrec functions** over `Theory.Derivation` + `R_preserves_empty` +
   `gentzenDescentφ` (the ℒₒᵣ graph of `n↦ord(Rⁿd₀)`, `d₀`=least ⊥-proof).
3. **`gentzen_prwo_implies_consistency` (crux 2)** — assemble: `¬Con ⟹` derivation `d₀` of ⊥ ⟹ the
   `gentzenDescent` is an infinite ≺-descent ⟹ contradicts `prwoInstance gentzenDescentφ`. Needs the
   reasoning INSIDE 𝗣𝗔 (the `prwoInstance` must be applied to the internal `d₀`).
4. (crux 1, separate girder) **`goodstein_implies_prwo`** — Rathjen §3 internal Cor 3.4 (blocked, see below).

## ⭐⭐⭐ Lap 49 (2026-06-23) — generic-route Cor 3.4 lead bricks + crux-2 grounded
Confirmed **M1 (`goodsteinTerminates_re`) and Phase-1 reduction (`not_proves_of_implies_consistency`)
are already complete & axiom-clean** — the operator's named M1 target was done by a prior lap; the only
open obligation is the deep Phase-2 girder `Reduction.goodstein_implies_consistency` (crux 1+2 below).

**CRUX 2 grounded this lap (Rathjen 2014 Thm 2.8, read pp. 8–11) → `CRUX2-GENTZEN-2026-06-23.md`.** The
Phase-2 Gentzen girder `PRWO(ε₀)→Con(PA)` decomposed lemma-by-lemma over Foundation's ARITHMETIZED
`Theory.Derivation : V → Prop` (located): `prwoSentence` (the hinge — formulate PRWO, highest confab risk),
primrec `ord`/`R` on coded derivations, `ord(R D) ≺ ord D` (Gentzen reduction, the deep core), assemble
via primrec descent `n ↦ ord(R^[n] d)` vs PRWO. Independent of crux 1; NOT blocked on Ackermann. Next-lap
candidate if crux-1's Ackermann-`F` infra stays blocked. Keep crux-2 scaffold sorries in `wip/`.

**Done this lap (`InternalCor34.lean`, axiom-clean, green 1311):** the generic Cor 3.4 lead at a
*non-standard* level `l : V` (the meta-`ibigMul (k:ℕ)` was only the standard-level special case).
- `oadd1iter_eq_succ` / `iAbove_ibigMul_finCode` — cast the `MinExpGe` threshold iterate to finite-code
  form (standard level).
- **`iVbigMul β l = (ω·)^l β`** — V-indexed `ω^l·β` as a genuine `𝚺₁` primitive recursion (`PR.Construction`,
  mirror of `iAboveTable`), with `isNF_iVbigMul`/`icmp_iVbigMul`/`iC_iVbigMul_le` by `sigma1_succ_induction`.
- **`iAbove_finCode_iVbigMul`** — V-indexed MinExpGe: `ω^(l+2)·β` clean above finite code `l+1`.
  (Motive-definability needed an EXPLICIT `Definable.comp₂` term — aesop blows up on the `iAbove` rule;
  see memory `definability-aesop-depth-blowup`.) Plus `iVbigMul_ne_zero`, `isNF_finCode`, `iadd_one_finCode`,
  `iAbove_zero_iVbigMul`.

**DONE — steps 1 & 2 of the prior plan (this lap, all green/axiom-clean):**
1. ✅ **Generic clean-append on `iVbigMul`** — `iAbove_code_iVbigMul`, `iAbove_ocExp_iVbigMul_fin/_inf`
   discharge `iAbove (ocExp g) (iVbigMul β (l+1))` for finite or infinite-top-exponent `g < ω^(l+1)`.
2. ✅ **`icorAlpha` assembly** — `icorAlpha β g l := iadd (iVbigMul β (l+1)) g` with the three portable
   Cor-3.4 properties: `icorAlpha_within` (`icmp_iadd_clean_within`), `icorAlpha_boundary`
   (`icmp_iadd_clean_boundary`+`icmp_iVbigMul`), `icorAlpha_C_le` (`iC_iadd_clean`+`iC_iVbigMul_le`).
   Validated end-to-end at level 0 with concrete `ig0` (`icorAlpha_ig0_within`). NB: `iVbigMul` is now
   `irreducible` (its `construction.result` never reduces on a variable level → whnf blow-up); the full
   4-hyp `icmp_iadd_clean` also blows up on unification — use the `_within`/`_boundary` wrappers.

**NEXT — two genuinely deep, isolated remaining pieces (crux 1 step 3):**
3a. **The internal `ig` f-recursion over level `l:V`** — `ig (l+1) n m = iblk (l+1) (…) (ig l (f^[blk] n)
   (off))` bottoms out at the internal Grzegorczyk `F` (Ackermann-level, NOT IΣ₁-total ⟹ needs the FULL-PA
   reduct `reduct_models_PA`, a different layer than this `V ⊧ 𝗜𝚺₁` file). Abstract-`ig` interface (provide
   `isNF`, `ocExp(ig) = code j ∨ 0` with `j ≤ l`, `ig ≠ 0`, `iC(ig) ≤ K(n+m+1)`, within/boundary descent as
   hyps — exactly what `icorAlpha_*` consume) defers the F-construction; discharge `f` separately.
3b. **The X-definable block bookkeeping** (`corBlk`/`corOff` over the raw descent's C-widths `corW β t =
   iC(β(t+1))`) — assembles the global slow sequence `α : V → V`. **KEY FINDING this lap: this is NOT cleanly
   IΣ₁** — `W = corW β` is X-definable (β lives in the LX descent layer, `DescentConstruction`), so `iwsum`/
   `iwidx`/`iwoff` must be built X-definably THERE (mirror `Grz.wsum`/`widx`/`woff`, lines 159-217), not in
   this generic-`V` file. The resulting α feeds `InternalThm35.bbeta` (Thm 3.5, DONE) → `nonterminating_of_xDescent`.

## ⭐⭐⭐ Lap 47 (2026-06-23) — internal Thm 3.5 COMPLETE; the two §3/Gentzen cruxes are next
Discharged lap-46 item 4's remaining input: **ω-tower cofinality** `iwtower_cofinal : ∀ c, ∃ s, icmp c
(iwtower s) = 0` (`InternalThm35`, axiom-clean), proved with NO NF hypothesis (`icmp_ocOadd_lt_exp` reads
only the leading exponent, so `sigma1_order_induction` at `ocExp c < c` decides the whole code; witness
`s` = the iterated-exponent depth). ⟹ `bbeta_desc_exists` gives the full Thm 3.5 descending sequence
**unconditionally** (no `hbdry`). **Internal Thm 3.5 is now hypothesis-free and route-independent.**

**The two open deep cruxes (hardest-first), both multi-lap — the live work:**
1. **Internal Cor 3.4** (THE harder). Produce the slow internal descent `α : V → V` (`iC(αₙ)≤K(n+1)`,
   `isNF`, `icmp`-descent) from a raw primrec ε₀-descent. Internal level `l:V` ⟹ Ackermann ⟹ needs the PA
   substrate. **Recommended first attack (lap-45 path #2): parameterize over an abstract internal `f`**
   (recursion eqns + Lemma-3.2 domination as hypotheses); build `ig`/`icorAlpha`/descent+bound relative to
   it; discharge `f`'s existence separately. Blueprint = `Grzegorczyk.lean` ℕ-template. The standard-`l`
   `InternalCor34` (`ig0`/`iblk`/`ibigMul`) is reusable bricks (special case), NOT the generic route.
2. **Gentzen Thm 2.8(i) `PRWO(ε₀)→Con(𝗣𝗔)`** + formulate **`PRWO(ε₀)` as a `Sentence ℒₒᵣ`**. Primrec `ord`
   + reduction `R`, `ord(R D)<ord D`, over Foundation `Derivation`. THE deep ordinal-analysis girder.

**Decision for next lap:** start crux 1 via the abstract-`f` parameterization (path #2) — it lets the
genuine `g`-padding math land green now without first building internal Ackermann. See `Reduction.lean`
docstring + STATUS "Where it stands" for the full chain.

**Crux-1 PROGRESS (lap 47, `InternalCor34.lean`, axiom-clean):** Cor 3.4's slowed term
`αⱼ = ω^(l+1)·βₙ + g(l,n,m)` needs a GENERAL clean append (`g` is a genuine ordinal `< ω^(l+1)`, not the
finite tail the `betaTail` lemmas handle). Built the internal analog of `Grz.AllExpAbove`/`C_add_clean`:
- `iadd_clean_step` — the `gt`-branch recursion of `iadd` under the clean head condition.
- `iAbove e0 a` (Σ₁-flag predicate via a parameterized course-of-values table, + `iAbove_zero`/`iAbove_ocOadd`
  recursion) — "every leading exponent down `a`'s spine `≻ e0`" (internal `MinExpGe`).
- **`icmp_iadd_clean_within`** — two clean appends onto the SAME head compare by their tails:
  `icmp (iadd a b₁)(iadd a b₂) = icmp b₁ b₂` (= internal `corAlpha_within`, the `g`-descent through the
  fixed lead). Plus `ocExp_iadd_clean` (head exponent preserved).
**Crux-1 NEXT (hardest-first):**
1. **`icmp_iadd_clean_boundary`** — `icmp a₁ a₂ = 0 → icmp (iadd a₁ b₁)(iadd a₂ b₂) = 0` (head drops; =
   internal `corAlpha_boundary`). Needs the shared-prefix recursion; cleanest with `isNF a₁/a₂` + the
   `icmp = 1 ⟹ equal-code` fact (so equal exponents are literal, enabling `icmp_ocOadd_same_head`). For
   Cor 3.4 use `icmp_ibigMul` gives `icmp a₁ a₂ = icmp β' β`. A unified `icmp (iadd a₁ b₁)(iadd a₂ b₂) =
   thenV (icmp a₁ a₂)(icmp b₁ b₂)` would subsume within+boundary.
2. **`iC_iadd_clean`** — `iC (iadd a b) ≤ max (iC a)(iC b)` under `iAbove (ocExp b) a` (= internal
   `C_add_clean`, the slowness C-split). Also `iAbove`-preservation lemmas for `ibigMul`/`iomul` (the head
   `ω^(l+1)·βₙ` satisfies `iAbove (ocExp g) ·` since `g < ω^(l+1)`) = internal `MinExpGe_bigMul`/`AllExpAbove_bigMul`.
3. Then the abstract-`ig` interface (recursion eqns + descent + `iC ≤ K(n+m+1)` + `ig < ω^(l+1)` as hyps),
   `icorAlpha`, and the internal `ig` recursion on level `l:V` (the f-recursion; the genuinely deep last step).

## ⭐⭐⭐ Lap 46 (2026-06-23) — ROUTE RESOLVED: PRWO(ε₀)→Con(PA)+Gödel II (Rathjen Thm 2.8)
Operator-directed Route A. Lap-45's fork is **settled** (memory `route-resolved-prwo-gentzen`):
- **Headline path** = Rathjen Cor 3.7: `𝗣𝗔⊢γ →(§3, primrec) 𝗣𝗔⊢PRWO(ε₀) →(Gentzen Thm 2.8(i)) 𝗣𝗔⊢Con(PA)`,
  then Gödel II. This IS `Reduction.goodstein_implies_consistency` (now decomposed in its docstring).
- **The free-X β-wall (`DescentSemantic:582`) is the WRONG target**: §3 is primrec-only; an oracle X
  descent isn't dominated (machine-checked `not_dominated_of_diag_le`). But a **PRWO** descent is
  *internally* primrec ⟹ Lemma 3.2 applies internally ⟹ unblocked. `peano_not_proves_TI` (free-X)
  does NOT chain (free-X-TI ⊢ PRWO, wrong direction) — banked asset, off-path.
- **DONE this lap (axiom-clean):** `InternalThm35.bbtail_isNF/_C_le/_desc` — the model-internal Thm 3.5
  block-tail (`r ≥ K`): from a slow internal descent α produce βᵣ = ω·α_{(r-K)/K}+(K-(r-K)%K) with
  strict ≺-descent and the TIGHT `iC(βᵣ) ≤ r+1`, via internal division. Route-independent.
- **Open cruxes (hardest-first), both deep / multi-lap:**
  1. **Internal Cor 3.4** — Grzegorczyk hierarchy `f:V→V→V` over `V ⊧ 𝗣𝗔` (internal level `l:V`,
     Ackermann, not IΣ₁-total ⟹ needs the PA substrate `reduct_models_PA`). Produces the slow α that
     `bbtail_*` consumes. lap-45 path #2 (parameterize over abstract f) recommended first.
  2. **Gentzen Thm 2.8(i) `PRWO(ε₀)→Con(PA)`** — primrec `ord` + reduction `R`, `ord(R D)<ord D`,
     arithmetized in PA over Foundation's `Derivation`. The deep ordinal-analysis girder.
  3. **Formulate `PRWO(ε₀)` as a `Sentence ℒₒᵣ`** (∀ primrec-code descent → finite); gates both 1,2.
  4. Thm 3.5 **prefix + full β — DONE (modulo one cofinality input)**. `bbeta K s α` (`InternalThm35`)
     is the complete Thm 3.5 sequence indexed from `0`: ω-tower prefix for `r<K` (SIMPLIFIED to single
     towers `βⱼ = ω_{s+K−1−j}` — valid since `C` is the max coeff, not term count, so `C=1≤j+1`),
     block-tail `bbtail` for `r≥K`. Axiom-clean: `bbeta_isNF`, `bbeta_C_le : iC(βᵣ)≤r+1` (all r),
     `bbeta_desc` (prefix→prefix / seam / block→block). **Remaining = ONE disclosed hypothesis**
     `hbdry : icmp (bbtail K α K) (iwtower s) = 0` (i.e. `β_K ≺ ωₛ`): ω-tower **cofinality** in ε₀
     — `∀ NF code c, ∃ s, c ≺ iwtower s`, with a concrete `s = σ(α₀,K)`. Next lap: prove cofinality.
     Supporting: `iwtower` (ω-tower on codes), `icmp_iwtower_succ`, `icmp_ocOadd_lt_exp`.
- Foundation `PA_delta1Definable` axiom rides Gödel II (separate residual; lap-6 noted upstream burndown).


## ⭐⭐ Lap 45 (2026-06-23) — VALIDATED PIVOT: §3-on-X is BLOCKED; route is now Trevor's call
**Read `E-ARCHITECTURE-REVIEW-2026-06-23.md` §H + `HANDOFF.md`.** Independently re-derived in-box AND
confirmed against the external review. The lap-27→44 plan (run Rathjen §3 slow-down on the X-definable
descent → free-X `TI_≺(X)`) is **structurally blocked, not merely hard**:
- `peano_not_proves_TI` is genuinely **free-X** (checklist #1: `Xsym` free, `prec` concrete) — the
  *strong* back-end; a §3 reduction to primrec-PRWO cannot reach it.
- The §3 domination `∃ l, ∀ n, C(β(n+1)) ≤ F_l n` is **FALSE for an X-definable descent** — now
  MACHINE-CHECKED (`Grz.not_dominated_of_diag_le`/`F_diag_not_dominated`, commit `279050d`): the
  Grzegorczyk hierarchy's diagonal escapes every fixed level, so domination is primrec-only.
- Root cause of the misalignment: a non-standard / X-definable descent needs an **internal** (V-level,
  Ackermann) Grzegorczyk level — NOT a fixed meta-l — and `f_l` for `l:V` is NOT IΣ₁-provably total.
  So the lap-40→44 meta-iterate `ibigMul` / meta-recursion `ig` design cannot produce the needed β.

**THE FORK (Trevor decides — do NOT pick unilaterally; lap-12 forbade Route A's axiom on the headline):**
1. **Route A** (Rathjen's actual proof): primrec §3 → primrec-PRWO → Con(PA) → Gödel II.
   `Grzegorczyk.lean` already fits (primrec). Cost: disclosed `PA_delta1Definable` (still an `axiom` in
   the pin) + the unbuilt `TI(ε₀)⊢Con(PA)` girder (`Reduction.lean:52`; PA∞ cut-elim — distinct from
   Buchholz §5). Attack paths: (a) check if a Foundation pin-bump discharges `PA_delta1Definable`
   upstream (lap-6 noted a session was on it); (b) build the Gentzen ordinal-analysis girder.
2. **Route B via Kirby–Paris 1982** (model-theoretic indicators): keep free-X; replace §3-on-X with
   the KP indicator argument inside `M ⊧ paLX` (the wall `no_min_descent_absurd_of_goodstein` is already
   model-internal — natural continuation). Avoids the axiom. Read `papers/kirby-paris-1982-…pdf`.
   Attack paths: (a) formalize indicators / the Σ₁-definable "gap" function; (b) the
   Paris–Harrington-style density argument adapted to Goodstein.
3. **§3-on-X: DEAD** — `InternalCor34` meta-l grind must NOT resume.

**Survives regardless:** `peano_not_proves_TI` (axiom-clean), `Grzegorczyk.lean` (primrec §3, Lemma 3.3
complete + the obstruction lemma), `InternalONote` code arithmetic, `InternalCor34.ig0` + general
`ocOadd` descent lemmas (substrate-agnostic leaves).

### SHARPENED (lap 45, end) — the crux is localized to Cor 3.4; Thm 3.5 + Lemma 3.6 are done/tractable
Grounded the Route-A back-end against Rathjen pp.13–14 (Lemma 3.6, Cor 3.7, Thm 2.8). Precise map:
- **Lemma 3.6** (the special-Goodstein run never terminates, given `C(βₙ) ≤ n+1`) = repo's **DONE**
  `DescentArith.nonterminating_internal` / `DescentSlowdown.slowdown_run_facts` (axiom-clean).
- **Thm 3.5** (slow `α` → `β`, `C(βᵣ) ≤ r+1`) is **level-agnostic, no Ackermann, IΣ₁-tractable**: finite
  tails + `r = K(n+1)+i` *division* indexing. Internal C-bound `iC_betaTail_le` LANDED (lap 45); descent
  = `icmp_betaTail_within/_boundary`, NF = `isNF_iadd_finite` (built). Remaining: the `β:V→V` assembly
  (internal division reindex + the `j<K` ω-tower prefix) — mechanical, route-agnostic.
- **Cor 3.4** (raw descent → slow `α`, the Grzegorczyk `g`-padding) = **THE deep crux, common to both
  routes.** Needs the Grzegorczyk level `l`; for ANY *quantified/generic* descent (Route A's ∀-primrec
  PRWO, or Route B's oracle X-descent) `l` is **internal (`l:V`)** ⟹ `f_l` is Ackermann ⟹ **NOT
  IΣ₁-provably-total** ⟹ needs a **PA substrate** (`V ⊧ₘ* 𝗣𝗔`), not the IΣ₁ `PR.Construction` toolkit.
  CORRECTION to the lap-45 mid-note: the meta-`l` `InternalCor34` design (`ig0`, `iblk`, `ibigMul`) is
  NOT outright dead — it is the **standard-`l`** special case (correct when the descent's level is a
  fixed standard natural), and `ig0` + the general `ocOadd` lemmas are reused by the internal-`l` version.
  But the *generic* slow-down needs internal `l`.

**3 attack paths for the Cor 3.4 crux (internal-`l` `g`-padding):**
1. **Build internal Ackermann/Grzegorczyk `f : V→V→V` over `V ⊧ 𝗣𝗔`** (Σ₁-graph + PA-totality by
   induction on the level), then `ig`/`icorAlpha` by PA-induction on `l:V`. Most direct, heaviest.
2. **Parameterize over an abstract internal `f`** (take `f`'s recursion eqns + Lemma-3.2 domination as
   hypotheses / a structure supplied by `M ⊧ 𝗣𝗔`), build `ig`/`icorAlpha`/descent+bound relative to it,
   and discharge `f`'s existence separately (disclosed). Lets the genuine `g`-math land green now; most
   tractable. ⟸ RECOMMENDED first.
3. **Restructure `g` to avoid `f_l`**: define blocks by the descent's *actual* widths (incremental V
   recursion) and prove the linear `C`-bound directly. Risk: the linear bound may genuinely need the
   Grzegorczyk recursion (Rathjen's `g` is built that way precisely for the linear bound) — may be false.

**Route decision still open** (Trevor): (A) Rathjen Con(PA)+Gödel II [carries `PA_delta1Definable`; reuses
Cor 3.4 + Buchholz §5 for Thm 2.8] vs (B′) Kirby–Paris model-theoretic indicators [axiom-clean back-end;
fresh technique]. Cor 3.4 (internal-`l`) is needed by (A); (B′) replaces §3 entirely with indicators.


## ⭐ Reflection — 2026-06-23 (lap 44, DEEP) — the wall `sorry` is framed on a DEAD path; rewire it FIRST

Full synthesis in `REFLECTION-2026-06-23-lap44.md`. Two findings:

- **(A) `DescentSemantic.no_min_descent_absurd_of_goodstein` (`:574`) routes through the DEAD 𝚺₁ path.**
  The literal `sorry` lives inside `hCD`, which uses `hbound` (`∃ m₀ b, 𝚺₁-Function₁ b ∧ …`) +
  `DescentArith.nonterminating_internal`. But the bound `b` is built from the **X-definable** descent, so
  it is genuinely **X-dependent** ⟹ no 𝚺₁ `b` exists in a general model ⟹ the `hbound` 𝚺₁ shape is
  **UNACHIEVABLE / FALSE**, not just hard. **Action (next lap, do first):** rewire `hCD` to the in-file
  **`nonterminating_of_xDescent`** (lap 41, X-essential `lx_succ_induction`). It needs `β : M → M` with
  `∀k isNF (β k)`, `∀k iCanon (k+1) (β k)`, `∀k icmp (β(k+1)) (β k)=0`, and the LX-definable run comparison
  `hPdef`. The residual `sorry` then becomes the HONEST "produce `β`" obligation. The 𝚺₁ engine
  (`nonterminating_internal`/`hbound_of_slowdown`/`nonterminating_of_slowdown` in `DescentSlowdown`) is
  sorry-free + axiom-clean — KEEP as a banked asset (charter: never delete completed proofs), just stop
  routing the live wall through it.

- **(B) `Grzegorczyk.lean` collapses Rathjen's length `|·|` (Lemma 3.3(2)/Cor 3.4) onto C.** Self-consistent
  on paper (`C ≤ |·|`; the absolute `C(βᵣ)≤r+1` is Thm 3.5, built in `DescentCore.C_betaTail_le` via
  `C_omega_mul_le`) but UNVERIFIED until the ℕ Cor 3.4 assembly (item 1 below) typechecks. If the C-bound
  won't close, define `len : ONote → ℕ` (the symbol-count `|·|`), prove `C ≤ len`, redo Lemma 3.3(2) on
  `len`, and bound `C` via `C ≤ len` at the end.

**Status of the run/consumer side (all DONE):** `nonterminating_of_xDescent`, `slowdown_run_facts`,
`ineq6_step_internal`, `DescentCore` Thm 3.5 reindex + `lemma36_nonterminating`, the unconditional descent
`descentR`/`descent_iterate_seq_total`. The ONLY remaining content = produce the M-internal `β`.

## ⭐ Lap 43 — **Rathjen Lemma 3.3 COMPLETE in the ℕ-template** (`Grzegorczyk.lean`, 6 axiom-clean commits, green 1309)

The genuine combinatorial heart of the slow-down wall (Lemma 3.3, the Grzegorczyk `g`) is now fully
machine-checked in the self-contained ℕ-template `src/GoodsteinPA/Grzegorczyk.lean`:
- `F` (the hierarchy `F 0 n=n+1`, `F (l+1) n=(F l)^[n] n`); `g0` base case.
- `blk k c x = ω^k·c+x` + Rathjen's two ordinal descent cases (`repr_blk_within`, `repr_blk_boundary`).
- Block decomposition `blockIdx`/`blockOff` (via `Nat.findGreatest`) + full correctness specs
  (`psum_blockIdx_le`, `blockIdx_lt`, `lt_psum_blockIdx_succ`, `blockOff_lt_width`, `blockIdx_eq`).
- **`g`** recursion (`g (l+1) n m = blk (l+1) (n-i) (g l (F_l^i n) j)` for `m<F(l+1)n`, else 0).
- Invariants `g_lt` (`repr (g l n m) < ω^(l+1)`), `g_NF`.
- **`g_desc`** (Lemma 3.3(1) DESCENT — the hard property; within/boundary/exhausted case split).
- **`g_C_bound`** (Lemma 3.3(2) BOUND `C(g l n m) ≤ K_l·(n+m+1)`).

**REMAINING toward `hbound` (hardest-first):**
1. **(ℕ-template Cor 3.4 assembly)** — from a descending `β:ℕ→ONote` + a **domination** `∃ l, ∀ n, |β_{n+1}| ≤ F l n`,
   build `αⱼ = ω^ω·βₙ + g l n m` (`j = Σ_{t≤n}|βₜ| + m`, `m<|β_{n+1}|`): descent (within-block via `g_desc`,
   across-block via `βₙ ≻ β_{n+1}` + `ω^ω` absorbing `g<ω^ω`), slowness `C(αⱼ)≤K(j+1)` (via `g_C_bound`).
   Needs a `|·|`-length/`C` measure on `ONote` for the block widths + block-finding on the β side
   (mirror of `blockIdx`). NOTE: the domination hypothesis is where "β primitive recursive" bites
   (Lemma 3.2 = `exists_lt_ack_of_nat_primrec`, + `ack ≤ F l` relation); state Cor 3.4 abstractly over
   the domination so the M-internal version supplies its own.
2. **(Thm 3.5 reindex)** — feed the slow α into the EXISTING `DescentCore` template
   (`C_betaTail_le`, `repr_betaTail_within/_boundary`) ⟹ β' with `C(β'ᵣ)≤r+1` ⟹ `lemma36_nonterminating`.
3. **(M-internalization)** — port the whole ℕ-template chain onto `InternalONote` M-codes; the M-internal
   subtlety is whether the domination holds for the X-dependent descent's block-length function.

## ⭐ Lap 42 (REVIEW) — `IterPrefix_lxDef` DISCHARGED; the descent EXISTS unconditionally; **the real crux is now the Rathjen §3 SLOW-DOWN**

**Done lap 42 (1 commit, axiom-clean, green 1308):** `IterPrefix_lxDef` + `minClause_lxDef`
(`DescentConstruction.lean`) — the lap-41 "lone wall" (`hPdef`). The membership-form trick
(`isDescent_iff_mem`: X-atom on a *bound* variable) that `DescentConstruction.descent_seq_exists`
already used for the `Mlt`-descent applies verbatim to the **`descentR`** route. So `IterPrefix`'s four
clauses (`skel`/`descentMlt`/`minClause`/`xclause`) are each binary-`LX`-definable; the only new one is
`minClause` (the `descentR` minimality `∀ z<x', ¬(Mlt f z x ∧ ¬MX z)` via Foundation `ballLT`). Result:
**`descent_iterate_seq_total : ∀ k:M, IterPrefix hM f a₀ k` is UNCONDITIONAL** — the canonical
`Mlt`-descent prefix exists at every length, no hypotheses. (Lap 41 over-rated this as "genuine
multi-lap infra"; it was one membership-form clause.)

**⚠️ FRESH-MIND COURSE-CORRECTION — the prior `hbound` decomposition under-specified the SLOWNESS.**
The lap-41 plan (piece 1) claimed the extracted descent `α` comes "with `iC(α k) ≤ K(k+1)` (Rathjen
`|αₖ|≤K(k+1)`)". **That is NOT automatic.** `descentR` picks the `<`-least `¬MX` code `≺ αₖ`; its
coefficient `C` is uncontrolled. Rathjen gets the bound only via **Corollary 3.4** (read `papers/
rathjen-2014…pdf` p.11–12): pad an arbitrary descent into a *slow* one (`|αᵢ|≤K(i+1)`) using the
Grzegorczyk function `g` from **Lemma 3.3** (`g(n,m)>g(n,m+1)` for `m<f(n)`, `|g(n,m)|≤K(n+m+1)`).
**Only then** does **Theorem 3.5**'s reindex `β_{K(n+1)+i}=ω·αₙ+(K-i)` give `C(βᵣ)≤r+1`. The lap-41
`InternalONote` toolkit (`iC_iomul`/`iC_iadd_finite`/`icmp_betaTail_*`) is the **Thm-3.5** code
arithmetic; **Cor 3.4 (the `g`/Grzegorczyk padding) is NOT started and is the genuine remaining wall.**

**Also flag (stale code):** `no_min_descent_absurd_of_goodstein`'s `hbound` `sorry`
(`DescentSemantic.lean:569`) still demands a `𝚺₁-Function₁ b`. That is UNACHIEVABLE — `b` is
`X`-dependent (derived from `no_min`/`MX`). The correct route is lap-41's `nonterminating_of_xDescent`
(the `lx_nonterminating`/`X`-essential path). When β is built, **refactor `hCD` to go through
`nonterminating_of_xDescent`**, deleting the dead `𝚺₁` `hbound`+`DescentArith.nonterminating_internal`.

**REMAINING for `hbound`, hardest-first (revised lap 42):**
1. **(HARD CRUX — Rathjen Cor 3.4 slow-down)** — internalize the `g`/Lemma 3.3 Grzegorczyk padding on
   `M`-codes: from an `icmp`-descent of ε₀-codes, produce a SLOW `icmp`-descent with `iC(αᵢ)≤K(i+1)`.
   Lemma 3.2 = mathlib `exists_lt_ack_of_nat_primrec` (ack ≈ Grzegorczyk fₙ). **This is multi-lap.**
   Decompose: (a) ℕ-template `g : ℕ²→ONote` + descent/bound lemmas (Aristotle-eligible, self-contained);
   (b) internalize as `M`-code recursion.
2. ✅ **(DONE lap 42) Extract `α : M → M`** — `descent_alpha_exists` (`DescentConstruction.lean`):
   `α 0=a₀`, `∀k ¬MX(α k)`, `∀k descentR f (α k)(α(k+1))`. Coherence via `IterPrefix_agree` (prefix
   agreement by X-free `sigma1_succ_induction` + `descentR_functional`). Axiom-clean. ⟹ `Mlt`-descent +
   each `¬MX` (`descentR_descends`). NOTE: `α` is NOT yet known slow — that's piece 1 (Cor 3.4).
3. **(plumbing) Decode `Mlt`→`icmp`** on codes (the route-b seam): `Mlt f y x` (`=prec`, X-free) ⟺
   `icmp y x = 0` on the ε₀-code reading; `isNF (α k)`. Needs the `prec`↔`icmp` bridge in `M`.
4. **(ARITH, toolkit ready) Thm 3.5 reindex** `α(slow) → β`, `βᵣ=ω·αₙ+(K-i)` — `iCanon(r+1)`
   (`iC_iomul`+`iC_iadd_finite`), `icmp`-descent (within+boundary), `isNF` (`isNF_iadd_finite`).
5. **`hPdef'` + close** — LX-def of `ievalNat(k+1)(βₖ)≤igoodstein m₀ k` (`lxDef_of_reduct` on the 𝚺₁
   `ievalNat`/`igoodstein` graphs + β's LX-formula); `nonterminating_of_xDescent` ⟹ `hCD` ⟹ `hbound`.
   ANTI-FRAUD: re-`#print axioms` headline (must stay `sorryAx` until the WHOLE chain is real) + girder.

## ⭐ Lap 41 — slow-down toolkit + run engine COMPLETE; `hbound` reduced to "build the X-definable β"

The lone wall is still `hbound` (`DescentSemantic.lean`, now ~line 460). Lap 41 closed the ENTIRE
code-level + run-level half (8 axiom-clean commits, green 1308):
- ✅ `icmp_iomul`, `icmp_betaTail_boundary`, `isNF_iomul`, `isNF_iadd_finite` (`InternalONote.lean`) —
  the slow-down's order/NF lemmas. Toolkit now complete: `iadd`/`iomul`, `iC_iomul`/`iC_iadd_finite`
  (⟹ `C(βₖ)≤k+1`), within+boundary descent, NF preservation, `ineq6_step_internal` (the (6) step).
- ✅ `DescentSlowdown.lean` (NEW): `slowdown_run_facts` (X-agnostic base/step/hpos core),
  `hbound_of_slowdown` (𝚺₁ path), `nonterminating_of_slowdown`.
- ✅ `DescentSemantic.nonterminating_of_xDescent` — **the reduction**: given `β:M→M` with the 3 arith
  facts (NF/iCanon(k+1)/icmp-descent) AND `hPdef` (LX-definability of `T̂^{k+2}(βₖ)≤mₖ`), the run from
  `T̂²(β₀)` never terminates. Via `slowdown_run_facts` + `lx_nonterminating` (X-essential). ⚠ The
  descent is X-DEPENDENT so the run MUST go through `lx_nonterminating`, NOT the 𝚺₁ path.
- ✅ `DescentSemantic.descentR` — the LX-definable functional descent-step relation to iterate:
  `descentR_exists` (=descent_step), `descentR_descends`, `descentR_lxDef`.

**REMAINING for `hbound` — three pieces, hardest-first:**
1. **(HARD CORE) M-internal X-definable iteration `α : M → M`** — `α 0 = a₀`, `α (k+1) = descentR-image`,
   for `k : M`. Build via an **LX recursion theorem**: `lx_succ_induction` over the LX-formula
   `Pk := ∃ s, Seq s ∧ lh s = k+1 ∧ znth s 0 = a₀ ∧ ∀ i<k, descentR (znth s i)(znth s (i+1)) ∧ ∀ i≤k ¬MX(znth s i)`
   (Seq/znth/lh are reduct-𝚺₁ → bridge via `lxDef_of_reduct`; `descentR` clause via `descentR_lxDef`).
   Then `α k := znth (the s) k` extracted via uniqueness. PREREQ: `descentR_functional` (uniqueness —
   needs reduct `<`-trichotomy; M⊧PA⁻ via `ReductModel.reduct_models_PA`, port `lt_trichotomy`).
   Gives `α`: `Mlt`-descending, each `¬MX`, with `icmp (α(k+1))(α k)=0` (decode `Mlt`=`prec`→`icmp` on
   codes — the route-(b) seam) + `isNF (α k)` + a coeff bound `iC(α k) ≤ K(k+1)` (Rathjen `|αₖ|≤K(k+1)`).
2. **(ARITH) Rathjen reindexing `α → β`** — `βᵣ = ω·αₙ + (K−i)`, `r = K(n+1)+i`, `i<K` (block n via
   `r/K`, offset `r%K`). Gives `iCanon(r+1) βᵣ` (`iC_iomul`+`iC_iadd_finite`, ℕ-template
   `DescentCore.C_betaTail_le`), `icmp`-descent (within `icmp_betaTail_within` + boundary
   `icmp_betaTail_boundary`), `isNF` (`isNF_iadd_finite`). Pure code arithmetic, 𝚺₁-definable in r.
3. **`hPdef`** — `T̂^{k+2}(βₖ)≤mₖ` is LX-definable: `lxDef_of_reduct` on the 𝚺₁ `ievalNat`/`igoodstein`
   graphs + the LX-formula for `β` (from 1+2). Then `nonterminating_of_xDescent` ⟹ `hCD` ⟹ close `hbound`.
   ANTI-FRAUD: re-`#print axioms peano_not_proves_TI` (must stay clean) AND `peano_not_proves_goodstein`
   (must stay `sorryAx` until the WHOLE chain is real) after any edit near the girder/headline.

## ⭐ Lap 40 — internal ordinal arithmetic for the slow-down STARTED (2 axiom-clean commits)

Read Rathjen 2014 §3 ("Slowing down", Thm 2.6 proof + Def 3.1) on disk — confirmed the slow-down
(arbitrary ε₀-descent → sequence feeding the **special** Goodstein `igoodstein`) is irreducible and
fundamentally needs `ω·α` multiplication + CNF addition on codes. Built the two foundational internal
ops in `InternalONote.lean` (both `#print axioms`-clean, build green 1307):
- ✅ **`iadd`** (`47c267b`) — internal CNF ordinal addition `a+b` on codes, CofV table indexed by the
  first summand (param = b), 3-way leading-exponent `icmp` branch. Lemmas `iadd_zero_left`,
  `iadd_ocOadd`.
- ✅ **`iomul`** (`1af80bc`) — internal ω-multiplication `ω·c`, exponent bump `e↦1+e = iadd (ocOadd 0
  1 0) e`, recurse tail. Lemmas `iomul_zero`, `iomul_ocOadd`.

**KEY SIMPLIFICATION (lap 40):** `ineq6_step_internal` (the `step`) keeps `ievalNat βₖ` SYMBOLIC —
it only needs `isNF`, `iCanon`, `icmp`-descent of the codes, NOT computed `ievalNat` values. So the
messy `ievalNat_iadd`/`ievalNat_iomul` laws are NOT needed for the assembly. Only `isNF` + `iC`(canon)
+ `icmp`-descent of the `βₖ = ω·αₖ + (K-i)` codes are required.

**DONE this lap (7 commits, all axiom-clean, green 1307):**
- ✅ `iadd` (CNF addition), `iomul` (ω·α).
- ✅ `iC_one_add`, `iC_iomul` (`iC(ω·c) ≤ iC c + 1`), `iC_iadd_finite` (`iC(ω·c + m) ≤ max(iC(ω·c)) m`)
  → the full `C(βₖ) ≤ k+1` canonicity bound (Rathjen Thm 3.5).
- ✅ `icmp_self`, `icmp_betaTail_within` (within-block descent `ω·α+p ≺ ω·α+(p+1)`).
- ✅ `icmp_one_add` (`1+·` preserves the comparison) + helpers — the boundary crux.

**NEXT (hardest-first) toward `hbound`:**
1. **`icmp_iomul`** (`icmp (iomul a)(iomul b) = icmp a b`, ω-mult order-preserving) — structural
   induction via `icmp_one_add` (head) + IH (tail). NF hyps needed.
2. **boundary descent** `icmp (ω·αNext + s)(ω·α + t) = 0` from `icmp αNext α = 0` — via icmp_iomul
   (decision happens in the iomul part, before the appended finite tails).
3. **`isNF_iomul`, `isNF_iadd_finite`** — isNF preservation. Needed for step's isNF hyps.
4. **βₖ assembly** from the M-internal descent (seam) — 𝚺₁-def in k, `iCanon (k+1) βₖ` (iC bounds, HAVE),
   icmp-descent (within + boundary), isNF; `b k = ievalNat (k+1) βₖ`; `step` = `ineq6_step_internal`
   (HAVE); base/hpos; assemble `hbound`. Plus the SEAM rewire (route b) for the descent input.
Aristotle: idle. Candidate open lemma = `icmp_iomul` (self-contained given icmp_one_add). Spec before submit.

## ⭐ Lap 39 — internal arithmetic for `hbound`'s `step` COMPLETE (3 axiom-clean commits)

The lone wall is still `hbound` (`DescentSemantic.lean:416`). Pieces 1–2 of the decomposition are DONE
this lap (all `#print axioms`-clean, build green 1307):
- ✅ **`InternalONote.evalNat_succ_base`** `ievalNat (b+1) c = ibump (b+1) (ievalNat b c)` (isNF/iCanon),
  digit-direct strong induction (helpers `ilog_eq_of_bounds`, `ievalNat_tail_lt`, div/mod peel). `53d1b00`.
- ✅ **`InternalPow.ibump_mono`/`ibump_strictMono`** — ported the Aristotle ℕ blueprint (UUID 7c8bb0e8)
  into clean IΣ₁ (combined UB+strict-mono induction, no nlinarith). `c7675f0`.
- ✅ **`InternalONote.ineq6_step_internal`** — the internalized Rathjen ineq (6), = `hbound`'s `step`:
  `ievalNat (k+2) bk1 ≤ ibump (k+2) m - 1` from `bk1 ≺ bk` + `ievalNat (k+1) bk ≤ m`. Chains
  `evalNat_succ_base` + `ibump_mono` + `ievalNat_lt_of_icmp_eq_zero`. `5f9df55`.

**Remaining to assemble `hbound`** (`∃ m₀ b, 𝚺₁-Function₁ b ∧ b 0 ≤ igoodstein m₀ 0 ∧ step ∧ ∀k 0<b k`):
With `βₖ` the slowed descent, `b k = ievalNat (k+1) βₖ`, `m₀ = ievalNat 1 β₀`: `step` = `ineq6_step_internal`
(HAVE); `base` = refl; `hpos` = `ievalNat_pos` (need `βₖ ≠ 0`). The two HARD remaining pieces:
3. **Seam/F re-wire (route b)** — make `Mlt`/`precφ`/`MX` (in `paLX_models_TI_of_PA_provable`) decode to
   `icmp`/codes, so the `no_min` descent becomes a `≺`-descent of ε₀-codes. RISKY (touches the proven
   `peano_not_proves_TI` girder) — re-`#print axioms peano_not_proves_TI` after EVERY edit (must stay clean).
   FIRST investigate: `DescentLift`/`DescentSemantic` defs of `Mlt`/`MX`/`prec`; `Thm56.prec`/`precφ`;
   `SeamDefinability`. Decide whether a standalone "slow-down of an abstract code-descent" lemma can be
   built BEFORE the seam (so piece 4 proceeds in parallel).
4. **βₖ slow-down (Rathjen Thm 3.5)** + assemble — from the code-descent build `βₖ` with `iC βₖ ≤ k+1`
   (so `iCanon (k+1) βₖ`), still `≺`-descending; `𝚺₁`-definable in k; feed `DescentArith.nonterminating_internal`.

Aristotle: idle (next genuinely-open lemma = the slow-down or the seam; spec one before submitting).

## ⭐ Lap 38 — INTERNAL-ONOTE SUBSTRATE COMPLETE (read `HANDOFF-2026-06-23-lap38.md`)

`InternalONote.lean` now has the full ε₀-notation arithmetic inside `IΣ₁`, all axiom-clean: codes,
`iC`, `ievalNat`, `iCanon`, **`icmp`** (CNF comparison), **`isNF`** (well-formedness), and the **crux
`ievalNat_lt_of_icmp_eq_zero`** (order-reflection, Rathjen 2.3(iii), digit-direct). Remaining road to
`hbound` (`DescentSemantic.lean:392`), hardest-first:
1. internal `evalNat_succ_base` (`ievalNat (b+1) c = ibump (b+1) (ievalNat b c)`) — extract the tail
   bound `ievalNat_tail_lt` from order-reflection's `TB` first; needs `ilog` peel facts.
2. internal `ineq6_step` (port `DescentCore.ineq6_step` onto codes, uses 1 + order-reflection).
3. seam/F re-wire to transparent `natCodeT` (route (b); re-`#print axioms` girder after each change).
4. `βₖ` slow-down (Rathjen Thm 3.5) + assemble `hbound`.
Aristotle `ibump_mono` COMPLETE in `scratchpad/ibump_x/` (ℕ form), not yet ported to V.

## ⭐ Reflection — 2026-06-23 (lap 36, deep): NEW DIRECTION — refactor the sentence transparent. Read FIRST.

Full synthesis: `REFLECTION-2026-06-23-lap36.md`. Headline state (real `#print axioms`): girder
(`Thm56.peano_not_proves_TI`) **clean**; headline honest `sorry`; the chain `…_modulo_semantic` carries
exactly **one** `sorryAx` from `no_min_descent_absurd_of_goodstein`, which is `hCD` (wall C+D, `:410`) +
`hB` (wall B, `:419`).

**The finding — wall B is self-inflicted.** Every lap since 24 treated `goodsteinSentence = ∀⁰ codeOfREPred
goodsteinTerminates` (Foundation's opaque `Classical.epsilon` r.e. blob) as a FIXED target and tried to
*bridge to it* inside nonstandard `M` (wall B; the open `ON-LINE-REQUEST`; the "`PA_delta1Definable`-
flavoured gap"). But `goodsteinSentence` is **not** locked, and `Encoding.lean`'s docstring (lines 35–39)
**explicitly sanctions** refactoring it to a transparent form gated on the bridge spec.

**STOP**: bridging the opaque code; reasoning about `Classical.epsilon` Kleene codes on nonstandard inputs;
treating `goodsteinSentence` as immutable. The `ON-LINE-REQUEST.md` wall-B question is **superseded** — do
not wait on it.

**KEEP**: the lap-30 model-internal completeness architecture; the route-neutral ONote kernel
(`DescentCore`); route 1 (ordinal analysis — monument done; route 2 is no shortcut); `#print axioms` audits.

**✅ Transparent-sentence refactor — DONE lap 36 (wall B dissolved):**
1. ✅ `goodsteinSentence := “∀ m, ∃ N, !igoodsteinDef 0 m N”` (`Encoding.lean`, imports `InternalGoodstein`).
   `InternalPow.igoodstein` IS `InternalGoodstein.igoodstein` (one function, namespace `GoodsteinPA.InternalPow`).
2. ✅ `Bridge.goodsteinSentence_faithful` re-proved axiom-clean — identical locked RHS — eval via
   `InternalPow.igoodstein_defined.iff` + `InternalPow.igoodstein_nat` + `eq_comm`. `models_lMap_goodstein`
   compiled unchanged (form-independent, confirmed).
3. ✅ `hB` (`DescentSemantic.lean:419`) closed: `Semiformula.models_lMap.mp hgood` → `simp only
   [ReductModel.reduct_eq_standardModel]` → coerce `.toStruc ⊧` to `Evalbm (s := @standardModel M oM)`
   (defeq, `models_iff` rfl) → same eval `simp only` set → `hev m₀`. `ON-LINE-REQUEST` archived.
   Real `#print axioms`: `goodsteinSentence_faithful` clean; chain's lone `sorryAx` = `hCD` only.
   GOTCHA banked: to eval a `lMap Φ`-lifted ℒₒᵣ sentence in `M`'s reduct, `models_lMap.mp` gives
   `(inst.lMap Φ).toStruc ⊧ σ`; `simp only [reduct_eq_standardModel]` (NOT `rw` — dependent `reductORing`
   motive) rewrites the reduct to `standardModel oM`, then `have h : Evalbm (s := @standardModel M oM) … := this`
   coerces by defeq (`rw [models_iff]` does NOT fire on the `.toStruc ⊧` form).

**`hCD` NARROWED lap 36 — run side baked in; the lone open obligation is `hbound`.** `hCD`
(`DescentSemantic.lean:409`) now closes via `DescentArith.nonterminating_internal` + the run's
`𝚺₁`-definability (both proved), so the **only** remaining `sorry` is:
```
hbound : ∃ (m₀ : M) (b : M → M), (𝚺₁-Function₁ b) ∧
  b 0 ≤ igoodstein m₀ 0 ∧
  (∀ k, b k ≤ igoodstein m₀ k → b (k+1) ≤ igoodstein m₀ (k+1)) ∧   -- internalized ineq6_step
  (∀ k, 0 < b k)
```
This is the Rathjen §3 slow-down, internalized in `M`'s `𝗜𝚺₁`-reduct. Decomposition for the next laps
(the deep infra; DescentCore has all of it at ONote/ℕ level, the gap is making it `𝚺₁`-definable in `M`):
1. **Internal ordinal-notation codes + `C` (slow-down measure) in `M`.** Need CNF-coded ordinals as
   `M`-elements with `C(β) ≤ k` (`DescentCore.C`/`Canon_iff_C_le`) as a `𝚺₁` predicate on `M`.
2. **Internal `T̂_ω` evaluation** `ievalNat : M → M → M` (base, ordinal-code → value), `𝚺₁`-definable,
   matching `DescentCore.evalNat` on standard inputs (the InternalPow `ipow`/`ilog` substrate feeds this).
3. **Internal `βₖ` slow-down** from the descent `descent_seq_exists` (extract a coherent `a : M → M` or
   reuse the coded `W`; build `βₖ` with `C(βₖ) ≤ k+1` per `DescentCore.C_betaTail_le`), then
   `b k = ievalNat (k+2)^[k+2] (βₖ)`. `𝚺₁`-definable.
4. **Internalized `ineq6_step`** (`step`): the `Δ₀` numeral form of `DescentCore.ineq6_step` (Lemma 3.6,
   ineq (6)) — proved in `M` by its `𝗜𝚺₁` arithmetic. `base`/`hpos` fall out of the `βₖ` positivity.
This is multi-lap infrastructure (internalizing ONote arithmetic into a nonstandard `M`); attack hardest-
first = piece 2 (`ievalNat`) + piece 4 (`ineq6_step` internal), since pieces 1/3 are codings on top.

**LAP-37 progress (numeric bricks + Aristotle dispatch).** Landed `InternalLog.ilog_mono` (`2≤b`,
`0<n≤n'` ⟹ `ilog b n ≤ ilog b n'`, green). Identified that pieces 2/4 both bottom out on **`ibump`/
`evalNat` monotonicity** — the digit-direct "next hard chip" (lap-29 NB1), which is genuinely interdependent
(the per-digit bound and monotonicity are mutually recursive — `ibump b r < (b+1)^(ibump b e)` needs
`ibump b (ilog b r) < ibump b e`, i.e. mono, while mono's `e<e'` case needs that bound). Architected the
self-contained statement and **submitted `ibump_mono` to Aristotle** (UUID `7c8bb0e8-23cc-4118-9bab-70b37a2debbc`,
`scratchpad/ibump_mono.lean`): goal `2≤b → n≤n' → ibump b n ≤ ibump b n'` over ℕ with the true `ibump`/`ipow`/
`ilog` laws as axioms (algebra identical to the V-model, so a clean proof PORTS to `InternalBump`).
NEXT-LAP: poll `aristotle list`; on COMPLETE, verify + port to `src/GoodsteinPA/InternalBump.lean` as
`ibump_mono` (then strict-mono `ibump_strictMono` follows). This is the numeric core that internal `evalNat`
order-reflection (piece 2) and internal `ineq6_step` (piece 4) both consume.

**Also landed lap 37 (green): `DescentCore.evalNat_succ_base`** — `Canon b o → o.NF → 2≤b →
evalNat (b+1) o = bump (b+1) (evalNat b o)` (via `canon_round_trip` + `evalNat_toONote`). THE bridge:
raising the evalNat base by one is exactly the numeric `bump`. So `evalNat (k+2) βₖ = bump (k+2) (evalNat
(k+1) βₖ) = ibump (k+2) (b k)` — meaning the *internal* `ibump` substrate realizes `evalNat`'s base-bump
inside `M` directly (no separate internal ONote-evaluation needed for the base-change). This is the precise
restatement that `ineq6_step`'s `bump (k+2) m = evalNat (k+2) (toONote (k+2) m)` step should be rebuilt on
internally: internal `ineq6_step` = `ibump (k+2) (b k) - 1`-domination + internal evalNat ORDER-REFLECTION
(the still-open piece needing internal ONote codes for the `βₖ₊₁ ≺ βₖ` comparison).

**Refined decomposition of `hbound` after lap 37** (what internal ONote codes are STILL needed for):
- ✅ Base-change (evaluation) side: `evalNat (b+1) o = ibump (b+1) (evalNat b o)` — internalizes via the
  existing `ibump` substrate (`evalNat_succ_base` is the ℕ-shadow; internal version is `ibump`-direct).
- ❌ Order-reflection side: `βₖ₊₁ ≺ βₖ ⟹ evalNat (k+2) βₖ₊₁ < evalNat (k+2) βₖ` — STILL needs internal
  ONote codes + internal `evalNat` as a function of the code (`evalNat_lt_iff`/`evalNat_lt_of_lt`
  internalized). This is the irreducible internal-ONote requirement: the descent comparison.
- ❌ `βₖ` construction (the slow-down Thm 3.5 / Cor 3.4) from the M-internal descent (`descent_seq_exists`):
  needs internal ONote codes + internal `C` + the `C(βₖ) ≤ k+1` bound, all `LX`/`𝚺₁`-definable in `M`.
So the genuine remaining internal-ONote build is the CODE representation + `evalNat` (as code-fn) + `C` +
order-reflection. The base-change/run side is now substrate-direct. NEXT cold-start subproject:
`wip/InternalONote.lean` — code CNF terms as nested HFS pairs (`0 ↦ 0`, `oadd e n r ↦ ⟪⟪ec,n⟫,rc⟫`),
`isONoteCode` predicate (Fixpoint/Δ₁), `iC`/`ievalNat` via course-of-values table (à la `ibumpTable`),
internal `evalNat_lt_iff`. Multi-lap.

**⭐ STRATEGIC FINDING lap 37 (read `ANALYSIS-2026-06-23-lap37-order-reflection-opacity.md`).**
Grounded the order-reflection wall in Rathjen 2014 §3 (paper on disk). The descent is `Mlt f y x =
M ⊧ precφ(y,x)` with `precφ = codeOfREPred₂(natCode a < natCode b)` — the **opaque r.e. blob**, the
SAME opacity that was wall B; `natCode = (Denumerable.eqv NONote).symm` is arbitrary. Rathjen's βₖ
construction (Cor 3.4 / Thm 3.5) manipulates the **CNF** of descent elements, so the descent must be
decodable to CNF in `M`. **Route decision = (b): transparent HFS-CNF coding.** Build internal ONote
codes (a code IS its CNF), define `natCodeT : ℕ ≃ NONote` + transparent `precT`, re-wire seam + F
(`epsilon0_le_orderType_ltPull` holds for ANY `e : ℕ ≃ NONote`, so the order-type half transfers;
F-φ computability is easier for transparent CNF compare). Multi-lap girder refactor of the (axiom-
clean) order argument — re-validate `peano_not_proves_TI` with `#print axioms` at every step.

**✅ FOUNDATION STARTED lap 37 (green, sorry-free, `src/GoodsteinPA/InternalONote.lean`).** Internal
ONote CNF codes as nested HFS pairs: `ocOadd ec n rc := ⟪⟪ec,n⟫,rc⟫+1` (0 ↦ 0), decode projections
`ocExp`/`ocCoeff`/`ocTail` with round-trip simp lemmas, and the **subterm-bound lemmas** `ocExp_lt`/
`ocCoeff_lt`/`ocTail_lt` (+ `_of_pos` forms) — the course-of-values strict-decrease facts the next
recursions need.

**✅ `iC` (internal `C` max-coefficient) LANDED lap 37 (green, sorry-free, `InternalONote.lean`).**
Built `iC : V → V` via the same course-of-values table reduction as `ibump` (`iCTable n = ⟨iC 0,…,iC
n⟩`, `iCNext` reads the two sub-results at `ocExp`/`ocTail` out of the table). Proved `𝚺₁`-definable
(`iC_defined`), `iC_zero`, and the **recursion `iC_ocOadd : iC (ocOadd ec n rc) = max (max (iC ec) n)
(iC rc)`** (Rathjen's `C_oadd`). The CofV-table pattern now proven to work on the new codes.

**✅ `ievalNat` + `iCanon` LANDED lap 37 (green, sorry-free, `InternalONote.lean`).**
- `ievalNat : V → V → V` (Rathjen `T̂^b_ω` on codes) via the binary CofV table (parameter = base `b`),
  `𝚺₁`-definable, with `ievalNat_zero` + recursion `ievalNat_ocOadd : ievalNat b (ocOadd ec n rc) =
  n * ipow (b+1) (ievalNat b ec) + ievalNat b rc` (mirrors `Domination.evalNat_oadd`).
- `iCanon b c := iC c ≤ b` (internal `Canon`, FREE from `iC` via `Canon_iff_C_le`), with `iCanon_zero`,
  recursion `iCanon_ocOadd : iCanon b (ocOadd ec n rc) ↔ n ≤ b ∧ iCanon b ec ∧ iCanon b rc`, and the
  `Γ-Relation` definability instance.

**NEXT — the deep piece: internal order-reflection.** Two routes to the order the descent consumes:
1. `icmp : V → V → V` — 3-valued CNF lexicographic comparison via a BINARY CofV table indexed by the
   pair `⟪o,p⟫` (sub-calls `icmp(ocExp o, ocExp p)`/`icmp(ocTail o, ocTail p)` sit at `⟪e1,e2⟫`/
   `⟪r1,r2⟫` `< ⟪o,p⟫` by `pair_lt_pair`). Then `icmp` ≡ ievalNat-order on `iCanon` codes.
2. Direct internal `evalNat_lt_iff`: `iCanon b o → iCanon b p → isNF o → isNF p → (ievalNat b o <
   ievalNat b p ↔ o ≺ p)`. Structural induction using ievalNat arithmetic + the "tail value < leading
   power" NF bound (`ievalNat b rc < ipow (b+1) (ievalNat b ec)`). This is the SAME difficulty family
   as `ibump_mono` (on Aristotle, UUID `7c8bb0e8`) — harvest that proof's digit-direct technique first.
Also needed: internal `isNF` predicate (exponents strictly decreasing — needs `icmp`), and the internal
`evalNat_succ_base` (`ievalNat (b+1) c = ibump (b+1) (ievalNat b c)` for `iCanon b c ∧ isNF c`, by
structural induction + `ibump_pos`, given the NF leading-power bound). Then seam/F re-wire to `natCodeT`
(route b, `ANALYSIS-2026-06-23-lap37-order-reflection-opacity.md`) and the slow-down `βₖ`.

---

## 🎯 LAP-34 (2026-06-23) — wall-C/D model-internal induction TOOLKIT landed. Read FIRST.

**Done this lap (green 1304 jobs, all `[propext, choice, Quot.sound]`, in `DescentSemantic.lean`):** the
`X`-essential induction toolkit `no_min_descent_absurd_of_goodstein`'s `hCD` (wall C+D) needs, all derived
from lap-33's `lx_succ_induction`:
- `lxDef_ballLT` — `fun x ↦ ∀ y<x, P y` is `LX`-definable when `P` is (installs `Structure.LT LX M` off
  `reductORing`; formula `(φ ⇜ ![#0]).ballLT #0`). The closure step order-induction needs.
- `lx_order_induction` — `<`-below progressivity ⟹ totality for `LX`-definable `P` over `M`'s reduct
  arithmetic `<`. Mirrors Foundation's `InductionOnHierarchy.order_induction`.
- `lx_least_number` — every nonempty `LX`-definable `P` has a `<`-least witness. **The choice-free,
  M-internal selector wall C's `Mlt`-descent recursion picks the canonical `Mlt`-smaller ¬MX element
  with** (resolves the ⚠ "must be definable, not metatheoretic `choice`" subtlety).
- `lx_nonterminating` — **wall-D run side, `X`-essential form.** Given an `LX`-definable bound predicate
  `P k := b k ≤ igoodstein m₀ k`, seed domination `b 0 ≤ m₀`, the internalized ineq-(6) `step`, and
  `0 < b k`, the run never reaches `0`. Iteration is `lx_succ_induction` (NOT the lap-29
  `igoodstein_nonterminating_of_dominating`, which wants an `ℒₒᵣ`-`𝚺₁` bound — but the Rathjen §3 bound
  `b k = T̂^{k+2}(βₖ)` is `X`-dependent, so that ℒₒᵣ tool is the wrong one; this is the corrected substrate).

**Wall-C SCAFFOLD landed in `wip/DescentConstruction.lean`** (typechecks, ONE disclosed `sorry`, off the
build so `src/` stays sorry-free): the `Seq`-coded `M`-internal descent.
- `IsDescent f a₀ W` — `W` codes a finite `Mlt`-descending sequence through `¬MX` from `a₀`.
- `descent_base` / `descent_extend` — **PROVEN** (real content): length-1 base + the canonical one-step
  `seqCons` extension via `descent_step` (incl. all the `znth`-preservation/`¬MX`/descent clauses; the
  generic-`M` order arithmetic uses Foundation `PeanoMinus` lemmas, NOT `omega`/`ring`).
- `descent_seq_exists` — `∀ k, ∃ W, IsDescent W ∧ lh W = k+1`, by `lx_succ_induction` (base/step wired).
  **The lone `sorry`** = `hDdef`, the `LX`-definability of `D(k) := ∃ W, IsDescent f a₀ W ∧ lh W = k+1`
  (a `Seq`-existential `LX`-formula with `Mlt`/`¬MX` atoms on `znth`-terms). NEXT-LAP TASK: build that
  formula. **LAP-35 progress — `isDescent_iff_mem` (PROVEN, wip):** reformulated `IsDescent` into
  **membership form** (over the reduct, when `0 < lh W`): `Seq W ∧ ⟪0,a₀⟫∈W ∧ (∀ i x x', ⟪i,x⟫∈W →
  ⟪i+1,x'⟫∈W → Mlt f x' x) ∧ (∀ i x, ⟪i,x⟫∈W → ¬MX x)`. **Key win:** the `X`-atom now sits on a *bound
  variable* `x`, not a `znth`-function-term — `hDdef` no longer needs `znth`-graph-into-`X` plumbing.
  **NEXT (hDdef, decomposed):** `D(k) ↔ ∃ W, A(W,k) ∧ B(W) ∧ C(W)` with
    - `A(W,k) := Seq W ∧ ⟪0,a₀⟫∈W ∧ lh W = k+1` — pure `ℒₒᵣ`-on-reduct (NO prec/X); `Semisentence` from
      Foundation `Defined.df` (`seq_defined`/`lh_defined`/membership+pairing DSL); bridge via a *binary*
      `lxDef2_of_reduct` (generalize `lxDef_of_reduct` to `![W,k]` + `a₀` as a free-var in `e`).
    - `B(W) := ∀ i x x', ⟪i,x⟫∈W → ⟪i+1,x'⟫∈W → Mlt f x' x` — `∈`-guards + `prec` atom (X-free, fvar-free)
      under bounded `∀∀∀`; build directly in `LX`.
    - `C(W) := ∀ i x, ⟪i,x⟫∈W → ¬MX x` — `∈`-guard + `Xsym`-atom under bounded `∀∀`; build directly.
    Combine via binary `lxDef2_and`, then `∃`-close `W` (`lxDef_exists`, Foundation `eval_ex`). Needed
    combinators (verifiable generalizations of the unary ones in `DescentSemantic`): `lxDef2_and`,
    `lxDef2_of_reduct`, `lxDef_exists`. Then `descent_seq_exists` is sorry-free → promote to `src/`.

**NEXT (wall C — after `hDdef`), hardest-first:**
1. **Build the `X`-descent `a : M → M`** from `no_min`/`ha₀`: `a 0 = a₀`, `a (k+1) =` `lx_least_number`
   applied to the `LX`-predicate `Q y := Mlt f y (a k) ∧ ¬MX y` (nonempty by `no_min`). This needs
   **M-internal recursion** so `a` is `LX`-definable as a function of `k` (Foundation `PR.Construction`,
   the way `igoodstein` was built — but the step is `X`-dependent, so it's an `LX`-recursion, not
   `ℒₒᵣ`-`𝚺₁`; check whether `PR.Construction` admits `LX`-formula steps or needs a bespoke
   sequence-coding (HFS `Seq`) argument). The `Mlt`-strict-descent + `¬MX`-along-`a` are then immediate.
2. **Slow-down `βₖ`** (Rathjen 3.3/3.4/Thm 3.5): from the `Mlt`-descent `(a k)` build `(βₖ)` with
   `C(βₖ) ≤ k+1`, as an `LX`-definable function. The ONote/`C` machinery is in `DescentCore`/`Domination`
   (route-neutral) — port the value facts to internal-`M`.
3. **Define `b k = T̂^{k+2}(βₖ)`, `m₀ = T̂²(β₀)`; prove `(hPdef, base, step, hpos)`** and feed
   `lx_nonterminating` ⟹ `hCD`. `step` is the internalized `DescentCore.ineq6_step`.

Wall B (the opaque `codeOfREPred` ↔ `igoodstein` bridge) is unchanged + literature-gated
(`ON-LINE-REQUEST.md`); independent of wall C/D.

## 🎯 LAP-31 (2026-06-23) — reduct→𝗜𝚺₁ bridge DONE + architecture correction (equality). Read FIRST.

**Verified this lap (green 1303 jobs, axiom-clean `[propext, choice, Quot.sound]`):**
`src/GoodsteinPA/ReductModel.lean` (NEW). The lap-30 plan to run Rathjen §3 inside `M` via the lap-26
`igoodstein` substrate needs `M`'s `ℒₒᵣ`-reduct presented as `[ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁]`. This
brick does it:
- `reductORing : ORingStructure M` — read off `M`'s `LX`-interpretation of the ring/order symbols.
- `reduct_eq_standardModel : inst.lMap Φ = @standardModel M reductORing` — via `standardModel_unique`
  (template: Foundation `FirstOrder/Arithmetic/TA/Nonstandard.lean`).
- `reduct_models_PA` / `reduct_models_isigma1` — `M ⊧ paLX ⟹ reduct ⊧ 𝗣𝗔 ⟹ ⊧ 𝗜𝚺₁`
  (via `lMap_PA_subset` + `modelsTheory_onTheory₁` + `models_of_subtheory` on `𝗜𝚺₁ ⪯ 𝗣𝗔`).

**⚠ ARCHITECTURE CORRECTION (the lap-30 plan understated this).** Two genuine subtleties for the
completeness route, BOTH must be handled before the substrate can run inside `M`:

1. **Equality (FULLY SCOPED lap 31 — see `ANALYSIS-2026-06-23-lap31-equality-architecture.md`).** The
   Tait `Derivation` calculus has NO equality rules (verified `Calculus.lean:20`), so
   `completeness_of_encodable` (used by `descentE`) gives models where `=` is an arbitrary relation,
   NOT real equality. The substrate needs real `=`. **Honest precondition = `[Structure.Eq LX M]`**
   (proved sufficient in `ReductModel`). To SUPPLY it, restrict to `[Structure.Eq]`-models via
   `EQ.provOf` (`Completeness/Corollaries.lean`) — which needs **`𝗘𝗤 ⪯ paLX`**. The EXACT gap = ONE
   axiom: **X-congruence `Theory.Eq.relExt Xsym` = `∀x y, x=y → X(x) → X(y)`** (the ℒₒᵣ-part of
   `𝗘𝗤(LX)` is `lMap Φ 𝗘𝗤(ℒₒᵣ)`, already in `lMap Φ 𝗣𝗔⁻ ⊆ paLX`; `𝗘𝗤 ⪯ paLX` `infer_instance`
   FAILS only for X-cong — verified). **NEXT-LAP TASK A**, two parts:
   - **A1 (the crux, deep-but-bounded):** augment `paLX` with X-congruence and re-validate
     `peano_not_proves_TI` — `hax_paLX` needs a NEW branch discharging X-congruence into the
     `PXFc`/`XFreeAx` `Z∞` carrier (it is NOT X-free, so `provable_true_x` doesn't apply; it's not an
     induction instance either). ONE simple true low-complexity axiom → a small bounded-ordinal `PXFc`
     derivation in `EmbeddingBound`/`EmbeddingX`. The `α`/cut-rank bound of `peano_not_proves_TI` is
     otherwise unchanged. This is the real new work; START it next lap.
   - **A2 (plumbing):** `EQ.provOf` + `completeness_of_encodable : T ⊨ φ → T ⊢ φ` + `Semiformula.toEmpty`
     of `TI prec` (`emb_toEmpty` un-coerces) + `provable_def`/`provable_iff_derivable2` → `Derivation2`.
     Fiddly/bounded. Blast radius: `paLX` is woven through 6 files — augmenting its def risks a red
     build; consider a separate `paLX'` (but `peano_not_proves_TI'` still re-runs the embedding, A1).

2. **Opaque headline blob ↔ transparent substrate (THE arithmetization wall).** `hgood` gives
   `reduct ⊧ goodsteinSentence`, and `goodsteinSentence = ∀⁰ (codeOfREPred goodsteinTerminates)` is an
   OPAQUE Foundation r.e.-code (`Encoding.lean`), NOT `∃N, igoodstein m N = 0`. They agree on ℕ
   (`InternalBridge`), but in a nonstandard `M` you need them **IΣ₁-provably equivalent** to use the
   descent contradiction. This is the #4 arithmetization wall (landscape doc). **NEXT-LAP TASK B**
   (deep): either (i) prove `IΣ₁ ⊢ codeOfREPred goodsteinTerminates m ↔ ∃N, igoodstein m N = 0`
   (needs the register-machine ↔ igoodstein computation internalized — very deep), or (ii) reconsider
   making `goodsteinSentence` a transparent igoodstein-Σ₁ form whose ℕ-faithfulness is `InternalBridge`
   (touches the audit surface `Encoding.lean`; Bridge.lean RHS is LOCKED so re-prove faithfulness with
   SAME RHS — `InternalBridge.igoodstein_nat` already supplies it). (ii) is architecturally cleaner but
   needs an anti-fraud review; do NOT do it silently.

**Remaining decomposition of `no_min_descent_absurd_of_goodstein` (the lone wall), hardest-first:**
- (A) reduct→𝗜𝚺₁ — ✅ DONE (this lap, modulo wiring `[Structure.Eq]` via Task A).
- (B) opaque↔transparent (Task B above) — deep, unstarted.
- (C) M-internal `Mlt`-descent from `no_min` via `M`'s LX least-number principle — deep, unstarted.
- (D) slow-down `βₖ`-definable + internal `ineq6` iteration (`DescentCore.ineq6_step` is the kernel) —
  deep; substrate (`igoodstein_nonterminating_of_dominating`) ready to consume `(b, step, hpos)`.

## 🎯 LAP-30 (2026-06-23) — STRATEGIC REDIRECT: the E wall = ONE semantic lemma via completeness. Read FIRST.

**The whole headline now reduces to a single model-theoretic statement.** Fresh-mind review found the
lap-27 plan ("Route B = hand-build the `paLX` sequent derivation of `TI_≺(X)`", literature-gated) is not
the cleanest path. Foundation's **first-order completeness** (`Derivation.completeness_of_encodable`,
general FO, on disk) produces `paLX ⟹ [TI prec]` from the semantic premise "every `M ⊧ paLX` models
`TI prec`". So `Thm56.DescentE` is now **PROVED** (`src/GoodsteinPA/DescentSemantic.lean`, NEW, green 1302
jobs) modulo ONE disclosed `sorry`:

```
paLX_models_TI_of_PA_provable (h : 𝗣𝗔 ⊢ ↑goodsteinSentence)
    {M} [Nonempty M] [Structure LX M] (hM : M ⊧ₘ* paLX) (f : ℕ → M) : Evalfm M f (TI prec)
```

`#print axioms descentE` = `#print axioms peano_not_proves_goodstein_modulo_semantic` =
`[propext, sorryAx, choice, Quot.sound, ONoteComp…native_decide.ax_1_5]` — **NO `PA_delta1Definable`, NO
custom axiom**. Discharge the one `sorry` ⟹ the headline is axiom-clean. (Built `LX.Encodable`: 4 small
instances, only `Encodable (XRel k)` was missing.) `Statement.lean` headline `sorry` UNTOUCHED (anti-fraud).

**Why it's correct (vs the superseded sequent plan):** (i) **resolves the free-`X` obstruction** — work in
models of `paLX` (where `X` is `M`'s relation), not `V ⊧ 𝗜𝚺₁`; completeness lifts to a derivation for free;
(ii) **no literature gate** — standard model theory, `ON-LINE-REQUEST.md` question is moot; (iii) **reuses
the lap-26 substrate** — `igoodstein`/`ibump` run in `M`'s `ℒₒᵣ`-reduct, `DescentCore.ineq6_step` is the
kernel. Full map in **`DESCENT-PLAN.md §5`**.

**PROGRESS (lap 30, all green + axiom-clean in `DescentSemantic.lean`):**
- **✅ Step 1 — `M ⊧ lMap goodsteinSentence`.** `models_lMap_goodstein` (E-lift + `provable_def` +
  `Semiformula.lMap_emb` + `models_of_provable` soundness) and `reduct_models_goodstein` (via
  `Semiformula.models_lMap`: `M`'s `ℒₒᵣ`-reduct ⊧ `goodsteinSentence`). Axiom-clean.
- **✅ Step 2 — unfold `TI prec` semantics in `M`.** `evalfm_TI_unfold` : `Evalfm M f (TI prec) ↔
  ((∀x, (∀y, Mlt f y x → MX y) → MX x) → ∀x, MX x)` — **abstract transfinite induction** for `(Mlt, MX)`,
  where `MX a := Structure.rel Xsym ![a]` (M's X) and `Mlt f y x := Eval M ![y,x] f Thm56.prec` (M's ≺).
  Pure `map_imply`/`eval_all`/`eval_rel₁` unfolding + `rfl`. The main lemma now `rw`s this and `intro`s
  progressivity; the lone `sorry` sits on the crisp goal `∀ x, MX x`.

**NEXT — the deep core (`DescentSemantic.lean:144`), hardest-first:** goal `∀ x : M, MX x` given
`hProg : ∀ x, (∀ y, Mlt f y x → MX y) → MX x` and Goodstein-in-`M`. Suppose `¬MX a₀`. Sub-obligations:
1. **M-internal `Mlt`-descent.** `Prog`-contrapositive: `∀x, ¬MX x → ∃y, Mlt y x ∧ ¬MX y`. Build the
   descending sequence **as an M-INTERNAL/definable object** (NOT metatheoretic `choice` — see ⚠ below):
   `G : M → M` by M-recursion, `G(k+1) = ≺`-least `y` with `Mlt y (G k) ∧ ¬MX y`, via `M`'s LX
   least-number principle. NEED: LNP for LX-formulas from `M ⊧ InductionScheme LX` (search Foundation for
   a semantic `leastNumber`/order-induction over models of induction, or derive it).
2. **`M`'s `ℒₒᵣ`-reduct as an `ORingStructure`/`𝗜𝚺₁` model.** `hM ⊧ paLX ⊇ lMap 𝗣𝗔` ⟹ reduct ⊧ `𝗣𝗔` ⊇
   `𝗜𝚺₁`. Bridge the reduct `inst.lMap Φ : Structure ℒₒᵣ M` into the substrate's `[ORingStructure M]
   [M ⊧ₘ* 𝗜𝚺₁]` (instance juggling: the substrate's `igoodstein` uses the ambient `ORingStructure`).
3. **Slow-down + inequality (6) in `M`.** Slow `(G k)` ⟹ `(βₖ)` (`C(βₖ) ≤ k+1`, Rathjen §3); run special
   Goodstein from `m₀ = T̂²(β₀)` (lap-26 `igoodstein` in the reduct); iterate `ineq6_step` by `M`'s
   induction ⟹ `M ⊧ ∀k mₖ > 0`; contradict Goodstein-in-`M`.

**⚠ THE key subtlety (M-internal vs external descent):** the descent must be **M-internal/definable**, not
built by Lean-level `choice` over real ℕ. An external `g : ℕ → M` makes inequality (6) hold only for
*standard* `k`, but `M ⊧ goodstein` gives termination at an `M`-natural `N` that may be *nonstandard* — the
external bound never reaches it. Building `G` M-internally (definable + M-recursion) makes the run align
with `M`'s internal termination statement. This is the crux of why the deep core is genuine work.

**Banked/superseded (true + green, keep in `src/`):** `DescentInternal.igoodstein_nonterminating_of_dominating`
and the `DescentArith`/`sigma1_pos_succ_induction` scaffold are the X-free `V ⊧ 𝗜𝚺₁` framing — their
arithmetic content transfers to step 3, but re-targeted to `M ⊧ paLX`. The internal-bump bricks
(`ibump_pos`, `le_ibump`, `ibump_gt`, + a still-needed `ibump_mono`) are reusable in `M`'s reduct.

## 🎯 LAP-29 (2026-06-23) — `InternalBridge` FINISHED: substrate faithfulness machine-checked. Read FIRST.

**Done this lap (green, 1300 jobs, axiom-clean `[propext, choice, Quot.sound]`):** the lap-28 parked
`ibump_nat`/`igoodstein_nat` bridges are now **theorems** in `src/GoodsteinPA/InternalBridge.lean`. The
internal `𝚺₁`-definable Goodstein substrate (`ibump`/`igoodstein` over a model `V`) is proven to compute
the **audited** `Defs.bump`/`Defs.goodsteinSeq` on the standard model `ℕ` — the anti-fraud faithfulness
link Route B relies on (the internal run is the genuine Goodstein process, not a look-alike).

**The Foundation-ℕ operation diamond is SOLVED** (the lap-28 blocker). Foundation declares `noncomputable
scoped` `Div`/`Mod`/`Sub` instances over any `PeanoMinus` model `V` (built from `Classical.choose!`),
which over `V=ℕ` are **distinct instances** from `Nat.instDiv`/`instMod`/`instSub` (NOT defeq for
`/`,`%`,`−`; only `+`,`*` and `OfNat 0/1` coincide — there is NO `instAdd_foundation`/`instMul_foundation`).
Three bridge lemmas convert them:
- `fdiv_nat`/`fmod_nat`/`fsub_nat` — must state the LHS with the **explicit Foundation instance**
  `@HDiv.hDiv ℕ ℕ ℕ (@instHDiv ℕ (@LO.FirstOrder.Arithmetic.instDiv_foundation ℕ _ _)) x d` (a bare `_`
  resolves to `Nat.instDiv`, the global winner — confirmed via pp.all probe). Proofs: `div_eq_of`
  (foundation) + Nat facts; `sub_spec_of_ge`/`sub_spec_of_le` (foundation) + `omega` (omega treats the
  foundation sub as an atom and the `+` as Nat's).
- **Gotcha:** `igoodstein_succ`'s `ibump (k+2) …` uses the generic `instOfNatAtLeastTwo` numeral (V was
  generic), NOT `instOfNatNat`, so `rw [ibump_nat (k+2) …]` won't match a freshly-written `k+2`; first
  `rw [fsub_nat]` to Natify the `−1`, then `show … (k+2) … = …` to re-cast the numeral (defeq), then
  the rewrite matches. (Saved to memory.)

Route-neutral / on the Route-B path (the substrate doubles as `LX`-formula builders). The ONE wall is
unchanged: **E-core(b) Route-B** (the integrated paLX descent), partially literature-gated (see
`ON-LINE-REQUEST.md` — the precise calculus-internal `Goodstein ⟹ paLX ⊢ TI_≺(X)` shape).

**Also landed lap 29 (`src/GoodsteinPA/DescentInternal.lean`, green, axiom-clean):** wired the bridged
internal run into the (6)-scaffold. `igoodstein_sigma1 (m₀) : 𝚺₁-Function₁ (igoodstein m₀)` (partial
application of `igoodstein_definable` via `DefinableFunction₂.comp`), and
`igoodstein_nonterminating_of_dominating` = `nonterminating_internal` specialized to `m := igoodstein
m₀`. **This makes the RUN side of E-core(b) axiom-clean and pins the precise remaining obligation: a
`𝚺₁`-bound `b k = T̂^{k+2}(βₖ)` with `(base, step, hpos)`.** `step` is the internalized `ineq6_step`
(numeral-Δ₀ form of `DescentCore.ineq6_step`); `b`/`βₖ` is the slow-down side, fed in Route B by the
`X`-definable descent from `¬TI prec`.

**Internal-arithmetic bricks STARTED (lap 29, green, axiom-clean) toward the internal `ineq6_step`:**
- `InternalPow.ipow_le_ipow_left` / `ipow_lt_ipow_left` — `ipow` (strict) monotone in the base.
- `InternalLog.ilog_pos` — `1 ≤ ilog b n` for `b ≤ n`.
- `InternalBump.ibump_pos` — the general positive-argument recursion (`ibump_succ` for arbitrary `0<n`).
- `InternalBump.le_ibump` — `n ≤ ibump b n` (Δ₀-numeral analogue of `Domination.le_bump`), via `𝚺₁`
  order-induction (`ISigma1.sigma1_order_induction`) peeling through `ibump_pos`.
- `InternalBump.ibump_gt` — `b ≤ n → n+1 ≤ ibump b n` (analogue of `Domination.bump_gt`), digit-direct.
- **NB1:** the ℕ proof of `bump_mono` goes *via ordinals* (`toOrdinal` StrictMono), NOT internalizable
  (`DESCENT-PLAN §3b`: avoid internal ONote) — internal `ibump_mono` needs a fresh **digit-direct** proof
  (genuinely subtle: comparing hereditary reps of `a ≤ a'`). This is the next hard chip.
- **NB2 (reusable):** `omega` and `ring` do **NOT** work over a generic model `V` (only `ℕ`/`Int`);
  `ring` is also not imported in the `Internal*` files. Use manual ordered-semiring lemmas
  (`add_le_add`, `mul_le_mul`, `add_right_comm`, `lt_iff_succ_le`, `pos_iff_one_le`, `le_iff_lt_succ`).

**NEXT (hardest-first, offline-tractable pieces):**
1. **Internal `ineq6_step`** (the `step` hyp): the genuine non-vacuous Π₁ kernel as a `Δ₀`-numeral fact
   inside `V` — base-`b` digit form (Rathjen 2.2(ii)), NOT internalized ONote (`DESCENT-PLAN §3b`).
   Build on `ibump` (bridged) + `le_ibump` + internal `ibump`-monotonicity (digit-direct) + internal
   `ibump_gt` (`b ≤ n → n+1 ≤ ibump b n`). Deep, multi-lap; the irreducible content.
2. **The `b`/`βₖ` side**: requires the descending input. In Route B this is `X`-definable from `¬TI
   prec` — literature-gated on the exact paLX shape (`ON-LINE-REQUEST.md`).
3. **Route-B paLX glue**: from `¬TI prec` (free-`X`) extract the descent via the LX least-number scheme;
   contradict the lifted `goodsteinSentence` via `igoodstein_nonterminating_of_dominating`. Skeleton-
   decompose into named `wip/` obligations once the paLX shape is pinned.

## 🎯 LAP-28 (2026-06-23) — F-φ DISCHARGED (in build). ONE wall left: E-core(b) Route-B. Read FIRST.

**Done this lap:** F-φ ported + wired (`src/GoodsteinPA/ONoteComp.lean`); `peano_not_proves_TI` is now
fully axiom-clean (mod trust base + 1 🟢 `native_decide`). The project has **exactly one wall: `DescentE`**
(`Thm56.lean:133`) — the integrated paLX Route-B construction (`𝗣𝗔 ⊢ goodstein → paLX ⊢ TI prec`).

**Attempted + parked (off-critical-path):** the route-neutral faithfulness bricks `ibump_nat`/
`igoodstein_nat` in `InternalBridge.lean` (PENDING-26 NEXT). The math is straightforward strong
induction matching `ibump_succ`/`Defs.bump`, BUT it hit a **Foundation-ℕ operation diamond**: Foundation's
`/`,`%` on a model `V` are `noncomputable scoped instance`s built from `Classical.choose!`
(`IOpen/Basic.lean:86,260`), so over `V=ℕ` they are **NOT defeq** to `Nat.div`/`Nat.mod` (instances
`instDiv_foundation`/`instMod_foundation` ≠ `Nat.instDiv`/`Nat.instMod`). `ipow_nat`/`ilog_nat` work
because `ipow`/`ilog` are hand-built (bridged by their own induction); but `ibump_succ` exposes raw V-`/`,`%`.
- **The fix (next lap):** build two bridge lemmas `Vdiv_nat`/`Vmod_nat` (Foundation `/`,`%` over ℕ = Nat's)
  via `LO.FirstOrder.Arithmetic.div_eq_of` (`hb : b*c ≤ a`, `ha : a < b*(c+1)` ⟹ `a/b = c`) + `rem_graph`
  / `div_add_mod` (`IOpen/Basic.lean:106,267,275`), feeding Nat facts (`Nat.mul_div_le`,
  `Nat.lt_div_add_one_mul_self`) through `le_def`. CAUTION: the scoped Foundation `Div`/`Mod` lose to
  Nat's global instance in plain `a / b` notation — must state the bridges with explicit
  `@HDiv.hDiv ℕ ℕ ℕ <foundation-inst>`. Then `ibump_nat` closes (the `*`,`+` ARE defeq; only `/`,`%` need it).
- This is **route-neutral** (faithfulness link to audited `Defs`), NOT the headline crux. Do it only as
  warm-up / when E-core stalls.

## 🎯 LAP-27 (2026-06-23) — DEEP REFLECTION: F-φ SOLVED on Aristotle; back-end DECIDED = Route B. Read FIRST.

Full synthesis in **`REFLECTION-2026-06-23.md`**. Two changes the grind laps inherit:

**(1) F-φ is solved — PORT IN PROGRESS (`wip/aristotle-fphi/`).** Aristotle proved
`rePred_ltPull_natCode` (verified faithful: verbatim our statement + our `natCode`). **Port started lap
27** (`ONoteComp.v431-port-wip.lean`): reuses our `Epsilon0Complete` scaffolding, 4 proofs fixed, the
`native_decide +revert` >10min hang resolved. **~12 proofs still break on v4.28→v4.31 drift** — full
error analysis + fix recipe + compile-time strategy (low-heartbeat diagnostic; full build is >10min) in
**`wip/aristotle-fphi/PORT-STATUS.md`**. The disclosed `axiom` stays in `SeamDefinability.lean` (TRUE +
PROVEN, honest 🟡) until the port is green. **Mechanical multi-lap port — NOT the crux.** When green:
wire into the lib + SeamDefinability, confirm `#print axioms peano_not_proves_TI =
[propext, choice, Quot.sound]` (+ ≤2 🟢 `native_decide`). If it stays painful (see PORT-STATUS),
deprioritize vs E-core (the actual crux).

**(2) Back-end DECIDED: Route B. STOP the internal-V induction-toward-headline.** The lap 25–26
`DescentArith.ineq6_internal` (`sigma1_pos_succ_induction`) lands X-free `𝗣𝗔 ⊢ PRWO(ε₀)` = **Route A's**
antecedent; it **cannot** feed the built `peano_not_proves_TI` (free-`X` obstruction — exactly the
lap-24 correction; `𝗣𝗔 ⊢ PRWO`/primrec can't refute the X-definable counterexample to `TI prec`, and
E-lift can't make the free `X`). Route A also carries `PA_delta1Definable` (🟡), which anti-fraud
forbids on the headline. **So:**
- **KEEP** the lap-26 arithmetic substrate (`InternalPow/Digits/Log/Bump/Goodstein` + `InternalBridge`)
  — it encodes Goodstein arithmetic as definable formulas, needed by Route B too (~70% transfers).
  **Finish `InternalBridge`** (`ibump_nat`, `igoodstein_nat`) — faithfulness link to `Defs`, route-neutral.
- **STOP** extending `DescentArith.ineq6_internal` toward the headline. It's a true lemma (stays in
  `src/`, green), but it's Route-A-flavored and off the clean-headline path.
- **START** E-core(b) the **Route-B way:** inside a paLX derivation, set up the X-definable descent from
  `¬TI prec` (LX least-number scheme), define the Goodstein run from it via the lap-26 substrate (now as
  `LX`-formula builders), and run inequality (6) as an **`InductionScheme LX`** step (NOT
  `sigma1_pos_succ_induction`), contradicting the lifted X-free `goodsteinSentence` at the X-definable
  seed `m₀ = T̂²(β₀)`. This is the integrated paLX construction the lap-24 correction named — the last wall.

**Fallback endpoint (if E-core(b) Route-B proves intractable after sustained effort):** state E-core as
ONE narrow cited axiom (`DescentE`) on top of the built monument + F — a legitimate, valuable artifact,
and strictly better than Route A's `PA_delta1Definable` + unbuilt `PRWO ⟹ Con(PA)`.

## 🎯 LAP-26 (2026-06-23) — E-core(b) "THE WALL" CRACKED: internal `bump`/`goodsteinSeq` BUILT. Read FIRST.

The lap-25 gating prereq ("make `bump`/`goodsteinSeq` `𝚺₁`-definable inside `V`") is **DONE + axiom-clean**.
Five new files (`InternalPow`/`InternalDigits`/`InternalLog`/`InternalBump`/`InternalGoodstein`) build the
internal Goodstein substrate via Foundation's `PR.Construction` (base-2-only `Exponential` forced a hand-built
`ipow`). Highlights: `ilog_defined : 𝚺₁-Function₂`, `ibump` (table reduction of the course-of-values bump) with
the **proven peel recursion `ibump_succ` = `Defs.bump`**, and `igoodstein` = the concrete `m : V → V` for
`DescentArith.ineq6_internal`. Faithfulness bridge started (`InternalBridge`: `ipow_nat`, `ilog_nat`). Full
details + resolved gotchas (aesop-can't-do-ibumpTable → explicit `comp` terms; LE diamond on ℕ → `le_def`) in
**`HANDOFF-2026-06-23-lap26.md`**. Build green 1280 jobs; headline `sorry` intact.

**NEXT (hardest-first):** (1) finish `InternalBridge` (`ibump_nat` by `Nat.strong_induction_on`,
`igoodstein_nat`) — anti-fraud link to audited `Defs`. (2) **THE math content:** internal `ineq6_step`
(Rathjen Lemma 3.6 slow-down) — build `b k = T̂^{k+2}∘βₖ` as `𝚺₁`-fn, prove base + step, plug `m=igoodstein`
into `DescentArith.ineq6_internal`. (3) back-end (Route A/B, deferred). (4) F-φ on Aristotle.

## 🎯 LAP-24 (2026-06-23) — E-core kernel landed + back-end correction. Read FIRST.

**Two walls left: E-core + F-φ** (D' discharged lap 22; E-lift X-free half done lap 23). Build green
1271 jobs; headline `sorry` intact. F-φ on Aristotle (`aris_onotecmp`, running). See refreshed
`STATUS.md` + `DESCENT-PLAN.md §3a` (Σ₁-completeness reframe) + `DESCENT-PLAN.md §1 CORRECTION`.

**✅ Landed this lap (`src/GoodsteinPA/DescentCore.lean`, axiom-clean):** `Dom.ineq6_step` — the
non-vacuous Π₁ kernel of Rathjen Lemma 3.6 (one special Goodstein step from `m ≥ T̂^{k+2}_ω(βₖ)` lands
`≥ T̂^{k+3}_ω(β_{k+1})`), + `lemma36_ineq6`/`lemma36_nonterminating` (the `∀k` iteration — **semantic
shadow only**, vacuous hypotheses since ε₀ is well-founded; the real content is the arithmetization).
Weakened `Domination.canon_repr` `2≤b → 1≤b` (base-2 `T̂²_ω` needs `evalNat 1`).

**⚠️ Back-end correction (lap 24).** The DESCENT-PLAN's "`PRWO ⟹ TI prec` = one X-instance" understated
the Route-B bridge: Rathjen's `PRWO(ε₀)` is the **primrec** well-ordering statement (Thm 2.8), and a
counterexample to the free-X `TI prec` yields an **X-definable** (not primrec) descent, so primrec-`PRWO`
can't refute `TI prec` directly. The honest Route-B bridge = carry out Rathjen §3 **inside paLX** with the
free-X descent (LX least-number scheme + inequality (6), contradicting the lifted X-free Goodstein at the
X-definable seed). **De-risking:** `Goodstein ⟹ PRWO(ε₀)` (Rathjen §3) is **shared by both back-ends**
(Route A `PRWO ⟹ Con(PA)` + Gödel II, costs `PA_delta1Definable`; Route B the integrated paLX construction,
axiom-clean). **Focus E-core on the shared §3; defer the back-end choice.** Lit request filed
(`ON-LINE-REQUEST.md` lap 24) to pin the cheaper back-end.

**✅ Landed lap 25 (`DescentCore.lean`, axiom-clean):** Rathjen's tower `ωₙ` (`omegaStack`: `ω₀=1`,
`ωₙ₊₁=ω^{ωₙ}`) + `omegaStack_NF`, `C_omegaStack : C(ωₙ)=1`, `repr_omegaStack_succ`,
`repr_omegaStack_strictMono` (the Thm 3.5 head-term scaffold). **✅ Also landed lap 25 (`DescentCore.lean`, axiom-clean):** the C-arithmetic for the tail terms —
`one_add_oadd` (`1 + oadd e' n' a'` evaluation), `C_one_add_le : C(1+e) ≤ C(e)+1`, and the headline
`C_omega_mul_le : C(ω·α) ≤ C(α)+1` (= Rathjen's "multiplying by ω bumps coeffs by ≤1"; `omegaO := oadd 1 1 0`,
induction on the `ONote.mul` recursion). **✅ Also landed lap 25 (`DescentCore.lean`, axiom-clean):** the Thm 3.5 tail-term `C`-bound, complete —
`C_ofNat`, `one_add_ne_zero`, `NoFin`/`noFin_omega_mul` (ω·α has no finite part), `C_add_ofNat_le`
(`C(a+finite) ≤ max(C a, finite)` for `NoFin` NF `a`; mirrors `add_nfBelow` with cmp-gt), `NF_omegaO`,
and the headline **`C_betaTail_le : C(ω·αₙ + (K-i)) ≤ K(n+1)+i+1`** (= `C(βᵣ)≤r+1` for the tail block,
given `C(αₙ)≤K(n+1)`, `i<K`). **✅ Tail-block DESCENT done lap 25 (`DescentCore.lean`, axiom-clean):** `repr_omegaO` (repr ω=ω),
`repr_betaTail_within` (larger finite tail → larger value), `repr_betaTail_boundary`
(`ω·αₙ₊₁+K < ω·αₙ` from `αₙ₊₁≺αₙ`; ω absorbs the finite K). **Both halves of Thm 3.5's TAIL block —
`C(βᵣ)≤r+1` and `βᵣ₊₁<βᵣ` — are now machine-checked.** This is the asymptotic (non-vacuous) content.

**ARITHMETIZATION MAP VERIFIED lap 25 (see `DESCENT-PLAN.md §3b`):** the inequality-(6) PA-induction is
feasibility-confirmed — `sigma_one_completeness` (Σ₁ free) and `sigma1_pos_succ_induction` (the internal
`𝗜𝚺₁` induction; `succ` = internal `ineq6_step`) both exist with verified signatures; `P(k):=mₖ≥T̂^{k+2}(βₖ)`
is Δ₀ hence a `𝚺₁-Predicate`, so the induction applies directly. **The one gating prerequisite = make
`bump`/`goodsteinSeq`/`T̂`/`βₖ` `𝚺₁`-definable *inside* `V`** (the `PA_delta1Definable`-flavoured gap, here
only for the concrete primrec `bump` the repo already has `computable_bump` for). 

**✅ Arithmetization SCAFFOLD machine-checked lap 25 (`src/GoodsteinPA/DescentArith.lean`, axiom-clean,
now in the lib build).** `ineq6_internal` : inside `[V ⊧ₘ* 𝗜𝚺₁]`, given `𝚺₁`-functions `m,b`, base
`b 0 ≤ m 0`, and the internal step, `sigma1_pos_succ_induction` yields `∀k, b k ≤ m k` — the `definability`
tactic discharges the `𝚺₁`-predicate automatically. `nonterminating_internal` adds `0<b k ⟹ 0<m k`
(the PA-internal Lemma 3.6). **The inequality-(6) induction now assembles in Lean**; the deep layer is
isolated behind the two `𝚺₁`-function hyps + the step. Also: wired `DescentLift`/`DescentCore`/`DescentArith`
into `src/GoodsteinPA.lean` (build 1271→1274 jobs).

**Next bricks (priority):** (1) **THE WALL — internalized definability:** supply the concrete `𝚺₁`-function
`m` = internalized `goodsteinSeq`/`bump` (build on Foundation `𝗜𝚺₁` `log`/`exp`/`bexp` in
`Arithmetic/Exponential/`; `bump` is base-b digit manipulation) + `b` = `T̂^{k+2}∘β`, and prove the
internal `ineq6_step` (`Δ₀` numeral form of `DescentCore.ineq6_step`), then plug into `ineq6_internal`.
Multi-lap. (2) Optional completeness: the Thm 3.5 HEAD block (`βⱼ=Σω_{s-i}`,
`j<K`) — a finite boundary detail, vacuous on its own; `headBeta s t := oadd (omegaStack (s-1)) 1
(headBeta (s-1) t)`, `C=1` from `C_omegaStack`, descent by `repr_add`. Low value vs (1).

**Next concrete bricks (route-independent §3):** (1) the slow-down constructions Rathjen Lemma 3.3 / Cor
3.4 / Thm 3.5 — the explicit padding function `g : ℕ² → ω^ω` and the bounded-coefficient sequence `βⱼ`,
with their *step* properties (descending-at-a-step, `C(βᵣ)≤r+1`) as non-vacuous finite ℕ/ONote facts
(Lemma 3.2 = mathlib `exists_lt_ack_of_nat_primrec`). (2) Then the arithmetization: inequality (6)'s `∀k`
as a genuine PA-induction (the dominant wall; Σ₁ glue is free via `sigma_one_completeness`).
**Landed lap 24:** `Dom.C : ONote → ℕ` (Rathjen's max-coefficient) + `Canon_iff_C_le` (`Canon b o ↔ C o ≤ b`).

### Arithmetization API — GROUNDED (lap 24 scoping of the dominant wall)

Scoped Foundation's machinery for the inequality-(6) PA-induction (E-core's irreducible core). Findings:
- **Σ₁ glue is free:** `LO.FirstOrder.Arithmetic.sigma_one_completeness {σ : Sentence ℒₒᵣ}
  (hσ : Hierarchy 𝚺 1 σ) : ℕ ⊧ₘ σ → T ⊢ σ` (for `[𝗥₀ ⪯ T]`, so `𝗣𝗔`) — every TRUE Σ₁ sentence is
  PA-provable (`R0/Basic.lean:146`). This is the engine `precφ`/F-φ already rides (`codeOfREPred₂` →
  `sigma_one_completeness_iff`). All Δ₀/Σ₁ *computations* (specific Goodstein/`T̂`/βₖ values) are free.
- **The inductive core is the genuine work.** `∀k (mₖ ≥ T̂^{k+2}(βₖ))` is Π₁ (∀ of Δ₀) — NOT free. It
  needs a PA-induction. Foundation's idiom = the **internalized-model approach**
  (`Arithmetic/Induction.lean`: `sigma1_pos_succ_induction`, `bounded_all_sigma1_order_induction`, …):
  work inside an arbitrary `V ⊧ 𝗜𝚺₁` with `𝚺₁`-definable predicates/functions, do internal induction,
  and the framework yields the `𝗜𝚺₁`/`𝗣𝗔` proof.
- **KEY SIMPLIFICATION — arithmetize over base-b NUMERALS, not internalized ONote.** Rathjen's whole
  framework is numeral-based: `T̂^b_ω(α)`/`S^b_c` are base-conversions on numerals, and the order
  comparison is base-b *digit* comparison (Lemma 2.2(ii)), which is **Δ₀** (PA-provable directly). The
  ordinal/ONote/`repr`/ε₀ detour is only the *semantic* (ZFC-side) proof convenience (e.g. `ineq6_step`
  via `evalNat_lt_iff`/`canon_repr`); the **PA-side proof of inequality (6) uses Δ₀ numeral comparison**
  and avoids internalizing ONote into `V`. This is the big de-risk vs re-implementing ONote in HFS.
- **Prerequisite chain:** (i) the Goodstein function `goodsteinSeq` is already arithmetized
  (`Encoding.lean`/`goodsteinSentence`); (ii) the slow-down sequence `βₖ` + `T̂^{k+2}` as `𝚺₁`/primrec
  numeral functions (define from the Lean fns via `codeOfREPred`, or hand-build in `IΣ₁`); (iii) the
  arithmetized `ineq6_step` (Δ₀ numeral comparison); (iv) internal induction (`sigma1_pos_succ_induction`)
  to land `𝗣𝗔 ⊢ ∀k ψ(k)`; (v) the back-end (Route A/B, deferred). **(ii)–(iv) are the multi-lap wall.**

---

## 🎯 LAP-23 (2026-06-23) — E decomposition GROUNDED + first E-lift bricks LANDED.

Read **`DESCENT-PLAN.md`** (new, this lap): the full E wall mapped from Rathjen 2014 §2–3 to repo defs,
with the exact Foundation E-lift bricks (`Derivation.lMap`, `provable_iff_derivable2`,
`Derivation.toDerivation2`) verified present, and the **X-essential subtlety** spelled out (`TI prec`
mentions the set variable `X`, so it is NOT the `lMap` of any `ℒₒᵣ` sentence — E genuinely needs the
X-induction instance, not just proof-translation).

**✅ X-FREE E-LIFT COMPLETE (axiom-clean, `src/GoodsteinPA/DescentLift.lean`, `#print axioms =
[propext, Classical.choice, Quot.sound]`).** The full proof-translation half of E-lift is machine-
checked: **`paLX_derivable2_lMap_of_PA_provable : 𝗣𝗔 ⊢ σ → Nonempty (Derivation2 paLX {lMap Φ ↑σ})`**.
The chain, all landed:
- `lMap_{zero,one}_const`, `lMap_succT`, **`lMap_succInd`** — `lMap` commutes with the induction-axiom
  builder (the operator-`lMap` leaves, proved symbol-by-symbol since there is **no
  `Semiterm.lMap_operator` lemma**; also **`fin_cases` is NOT available** in this build — use
  `Fin.cases`/`.elim0`).
- `fvSup_lMap`, `lMap_fixitr`, `lMap_univCl'`, **`lMap_univCl`** — `lMap` commutes with universal closure.
- **`lMap_inductionScheme_subset`** : `lMap (InductionScheme ℒₒᵣ univ) ⊆ InductionScheme LX univ`.
- `lMap_PA_subset`, `coe_schema_lMap`, `schema_lMap_PA_subset` — `(𝗣𝗔:Schema).lMap Φ ⊆ (paLX:Schema)`.
- The lift: `provable_def` → `Derivation.lMap` → schema-weaken → `provable_iff_derivable2`.

**E-core brick landed** (`src/GoodsteinPA/DescentCore.lean`, axiom-clean): `evalNat_lt_iff` /
`evalNat_le_iff` / `evalNat_lt_of_lt` — Rathjen Lemma 2.3(iii), `evalNat` (= `T̂^b_ω`) order-reflects
on the `Canon`/`NF` domain (immediate from the already-present `Domination.canon_repr` round-trip +
`toOrdinal` strict monotonicity, also added `toOrdinal_lt_iff`/`le_iff`). **Note:** `Domination.lean`
is far more developed than the lap-22 map implied — it already has `Canon`/`Good`/`canon_repr`/
`canon_round_trip` (the full T̂/T round-trip) plus the entire `goodsteinLength ~ fastGrowingε₀` growth
analysis. Grep it before building any semantic ONote/Goodstein lemma.

**Next (E-core — the real remaining content):** the **X-essential** step `𝗣𝗔 ⊢ goodstein → Derivation2
paLX {TI prec}`. `TI prec` mentions the set variable `X` so it is NOT an `lMap`-image (the lift above
does NOT produce it directly). Path: (a) `𝗣𝗔 ⊢ goodsteinSentence → 𝗣𝗔 ⊢ ⌜PRWO(ε₀)⌝` (Rathjen §3
slowing-down, formalized inside PA — the dominant wall; first bricks: `C : ONote → ℕ` + `evalNat`
order-monotonicity, Aristotle-eligible), then (b) the X-induction instance `PRWO ⟹ TI prec` in `paLX`
(one least-number/induction instance for the `X`-formula — the lift's schema inclusion already gives
`paLX` those axioms). See `DESCENT-PLAN.md §1, §3`.

## 🎯 LAP-22 (2026-06-23) — D' DISCHARGED + E (DescentE) MAPPED FROM RATHJEN. Read FIRST.

**D' is closed.** `Thm56.embed_TI_bounded` is now machine-checked (the embedded ordinal `< ε₀`); the
entire `EmbeddingBound.lean` chain is axiom-clean. `#print axioms peano_not_proves_TI` = `[propext,
choice, Quot.sound, rePred_ltPull_natCode]` — `sorryAx` GONE. **Walls left: F-φ (Aristotle) + E.**

### E = `DescentE` decomposition (grounded in Rathjen-2014 "Goodstein revisited" §2-3, read lap 22)

`DescentE := 𝗣𝗔 ⊢ ↑goodsteinSentence → Nonempty (Derivation2 paLX {TI prec})`. The math (Rathjen):
Goodstein's theorem is **PA-equivalent to PRWO(ε₀)** (no descending prim-rec sequences of ordinals `<ε₀`,
= transfinite induction), and `𝗣𝗔 ⊬ PRWO(ε₀)` by Gentzen+Gödel-II. The two halves:

1. **The SEMANTIC descent is ALREADY in the repo** (`Domination.lean`, axiom-clean):
   - `toOrdinal b n` = Rathjen's `T^b_ω(m)` (base-`b` rep → CNF ordinal); `repr_toONote` ties it to `ONote`.
   - `seqOrd m k := toOrdinal (k+2) (goodsteinSeq m k)`; **`seqOrd_step` = Rathjen eq. (4)** — the ordinal
     strictly DECREASES along a Goodstein sequence (`goodsteinSeq m k ≠ 0 → seqOrd m (k+1) < seqOrd m k`).
   - `goodstein_terminates` (the (ii)⟹(i) direction, semantic) is fully proven.
   This is the **backbone**; E does NOT need to redo it.

2. **The SYNTACTIC gap (E's real content):** realize "Goodstein ⟹ TI(≺)" as a `Derivation2 paLX`
   proof-object, i.e. lift the semantic descent to a Z-proof of `TI prec`. Sub-lemmas (attack order):
   - **E-lift:** a finitary `𝗣𝗔`(ℒₒᵣ)-proof of an arithmetic `TI`/`PRWO(ε₀)` statement maps to a
     `Derivation2 paLX` of `TI prec` (proof-translation along `ℒₒᵣ ↪ LX`; `paLX ⊇ lMap 𝗣𝗔⁻ + induction`;
     match the arithmetic well-ordering formula to Buchholz's `TI prec = Prog prec 🡒 ∀⁰ Xat #0`, the
     set-variable `X` = the induction predicate). Mechanical-ish but needs the ℒₒᵣ `TI(ε₀)` formula DEFINED.
   - **E-core (the deep part):** `𝗣𝗔 ⊢ Goodstein ⟹ 𝗣𝗔 ⊢ TI(ε₀)` (Rathjen Cor 2.7 (i)⟹(ii), the
     reversal). Needs §3 "slowing down" (Lemma 3.2 Grzegorczyk bound, Lemma 3.3/Cor 3.4: convert arbitrary
     descending prim-rec sequences to SLOW ones `|αᵢ| ≤ K·(i+1)`, since PA only expresses prim-rec sequences).
   - **ALT (Route A escape hatch):** `Reduction.goodstein_implies_consistency : 𝗣𝗔 ⊢ γ → 𝗣𝗔 ⊢ Con(𝗣𝗔)`
     (Rathjen Thm 2.8: PRA ⊢ PRWO(ε₀)→Con(PA)) then Gödel II. Reintroduces `PA_delta1Definable` (🟡).
   - **First concrete prerequisite to formalize next lap:** the ℒₒᵣ-arithmetic statement of `PRWO(ε₀)` /
     `TI(ε₀)` + Rathjen Lemma 2.3 (the `T^b_ω`/`T̂^ω_b` order-iso, mostly in `toOrdinal_mono_and_bound`).
   - Scaffold (sorried statements) belongs in `wip/Descent.lean` (keeps `src/` sorry-free for the gate).

### Earlier notes below ⤵


## ✅ LAP-19 (2026-06-22) — F ORDER-TYPE WALL CLOSED (axiom-clean). Read FIRST.

The order-type half of **F** is **DONE + `#print axioms`-clean** in `src/GoodsteinPA/Epsilon0Complete.lean`
(build green, 1268 jobs). This was the campaign's dominant risk (laps 12-19: "the real F girder mathlib
LACKS"). Landed, in dependency order:
1. `exists_NF_repr_eq : ∀ o<ε₀, ∃ x:ONote, x.NF ∧ x.repr=o` — ε₀-completeness of CNF notations (CNF
   recursion via `WellFoundedLT.induction`; key step `log_omega0_lt_self` = no ω^· fixed point below ε₀).
2. `repr_lt_epsilon0` (NF ⟹ repr<ε₀, induction on ONote) + `range_NONote_repr` (= `Iio ε₀`).
3. `rk_ltPull_eq_repr` (= seam-advice `note_rank_eq_repr`) + `epsilon0_le_orderType_ltPull (e : ℕ≃NONote)`
   — `ε₀ ≤ orderType (ltPull e)`. Proved by naming `orderType`/`rk` itself as some `repr (e n₀)` via
   surjectivity ⟹ NO Iio-sup identity, NO universe bump (all `Ordinal.{0}`; the `NONote ≃o Iio ε₀` route
   would land in `Ordinal.{1}` ≠ project's `orderType`).
4. `encodeONote`/`decodeONote` (computable `Encodable ONote`; ONote only derives DecidableEq) + `Infinite`/
   `Denumerable NONote` ⟹ `natCode : ℕ ≃ NONote` + `epsilon0_le_orderType_natCode` (concrete `Seam.ge`).

**F now reduces to ONE Foundation-side wire-up** (Worker B): the X-free `ℒₒᵣ` formula `φ : Semiformula ℒₒᵣ ℕ 2`
(via `codeOfREPred₂` from `codeOfPartrec'`) defining **`natCode`'s order** (`ltPull natCode`), then instantiate
`GoodsteinPA.EpsilonOrder.Seam` with `φ`, `hφ`, and `ge := epsilon0_le_orderType_natCode`. The definability
half (`hprec`/`hprecXPos`) is already discharged (lap 18, `EpsilonOrder.lean`). **Binding constraint:** `φ` must
define the SAME order `natCode` induces (`repr(natCode a) < repr(natCode b)` — express arithmetically via the
computable `ONote.cmp` on codes, since `<` itself routes through noncomputable `repr`).

### Remaining open obligations (priority for lap 20+)
- **C₂ glue `hax_paLX`** X-induction case (`EmbeddingX.lean:705`) — closes **Thm 5.6 (`PA ⊬ TI(ε₀)`)**
  axiom-clean modulo E+F. Recipe inlined at the sorry (steps 1-7); all four helper lemmas proven
  (`metaInduction_cong`, `subst_value_subst`, `succInd_nnf`, `PXFc_allClosure`). Friction = Foundation-DSL
  Rew-pushing through `succInd`/`univCl`/`fixitr` (steps 3-5). ALL-OR-NOTHING (can't partial-commit the sorry);
  extract step-4 `rew_succInd : g ▹ succInd ψ = succInd (g.q ▹ ψ)` as a standalone helper first.
- **F-definability `φ`** (Worker B, Foundation-side) — see above. Independent of C₂ glue and E.
- **E**: Goodstein⟹TI_≺(natCode order) in PA — the other unstarted wall. Per seam-advice Reviewer-2 §3:
  commit to `natCode`'s CNF order for BOTH F and E; E uses `Domination.toONote` as a descent MAP into it
  (E's order need not have type ε₀, only a PA-provable strictly-decreasing descent). Needs papers/ reading.

---

## Reflection — 2026-06-22 (lap 18, deep-reflection) — the F seam, grounded vs an outside attack plan

**Context.** Evaluated an external (GPT-5.5) attack plan for **F** (the arithmetization seam,
`‖≺‖=ε₀` + discharge `hprec`/`hprecXPos`) against the real repo + mathlib. The plan is largely
sound (it read the code: its `EpsilonOrder.hprec` reproduces `Boundedness.lean:699-702` exactly), but
it under-scopes the hard part and omits the E-coupling. Verified facts + corrected attack below.

**Direction call: KEEP the Buchholz Boundedness route; it is working.** As of lap 17 the *entire
machine from D back is machine-checked and `#print axioms`-clean*: Boundedness (Thm 5.4) + corollary B,
C₁ `PXFc.cutElim`→cr0, D `orderType_le_of_TIprovable`, C₂-structural `embedC_LX_gen`, M4 `embedC`,
M5 `cutElim`. The honest realistic endpoint: **headline reduced to two well-scoped girders — E
(Goodstein⟹TI) and F (arithmetization seam) — atop a fully-built, axiom-clean infinitary
proof-theory core.** That is a valuable, net-new-in-Lean endpoint even if F lands as one narrow
cited fact + built remainder. Remaining open obligations, in priority order:
1. **C₂ glue** `hax_paLX` induction case (`EmbeddingX.lean:705`) — pure integration, recipe inlined
   at the sorry (lap-17 HANDOFF #3). ~1 lap. Closes **Thm 5.6 (`PA ⊬ TI(ε₀)`)** axiom-clean modulo E+F.
2. **F-girder: ε₀-completeness of CNF notations** — the real wall (below). Mathlib-only ⟹ Aristotle-eligible.
3. **E**: Goodstein ⟹ TI_≺(X) — and it *constrains which ≺ F may use* (coupling, below).

### F attack — corrected (what the outside plan got right / wrong, verified)
- ✅ **Seam structure** (abstract `hprec`/`hprecXPos` into a record so F proceeds in parallel) — good.
  FIX 1: `orderType lt = ε₀` is stronger than needed; the contradiction only needs **`ε₀ ≤ orderType lt`**
  (D gives `‖≺‖ ≤ 2^β`, `β<ε₀`). The `≤ε₀`/embedding obligation is then free to drop.
  FIX 2: carry the **X-free ℒₒᵣ defining formula** `φ` (set `prec := φ.lMap (ORing.embedding LX)`), so
  `hprecXPos : XPos (∼prec)` is *automatic* (X-free ⟹ XPos, `XPositive.lean:18`), not a separate field.
- ✅ **`hprec` reduces to definability** — `hprec_of_lMap_defined`. `TruthSem.models_lMap`
  (`TruthSem.lean:120`, closed case) + the `levelSet lt γ={n|rk<γ}` interpretation (`TruthSem.lean:51`)
  already exist; after unfolding `hyp prec=∀⁰(prec🡒Xat #0)` every `prec` occurrence is a *closed*
  instance, so the closed `models_lMap` suffices (no need to generalize it to arity-2). **TRACTABLE —
  do this FIRST among F bricks. Foundation-side.**
- ✅ **`codeOfREPred₂` via `codeOfPartrec'`** — verified real: `Foundation/.../R0/Representation.lean:233`
  `codeOfPartrec' {k} : (Vector ℕ k →. ℕ)→Semisentence ℒₒᵣ (k+1)`; `:245 codeOfREPred`+`:250` spec is the
  unary template. Binary version constructible. (Our `lt` is computable — NONote `cmp` is decidable.)
- 🔴 **THE under-scope — `note_rank_eq_repr : rank(·<·) o = repr o` is NOT a mathlib wire-up.** It is
  **equivalent to completeness of the notation system up to ε₀** (every ordinal `<ε₀` is some `repr`),
  and **mathlib does NOT have that.** `Mathlib/SetTheory/Ordinal/Notation.lean` (1298 lines) proves only
  that `repr` is order-preserving + injective on `NF` (an *embedding* `NONote↪ε₀`: `lt_def:111`,
  `repr_inj:319`) — no surjectivity/`ofOrdinal`/order-type lemma. The embedding gives `rank o ≤ repr o`
  and `orderType ≤ ε₀` cheaply; the `=`/`≥` direction is the missing girder. **And the FIX-1 relaxation
  does NOT save you**: `ε₀ ≤ orderType lt` still needs the represented set to fill `[0,ε₀)` (cof ε₀ = ω,
  so a cofinal ω-chain has order type ω, not ε₀). ⟹ **formalize `∀ o<ε₀, ∃ x:ONote, x.NF ∧ x.repr=o`
  (CNF existence up to ε₀). ~1–3 laps. Pure mathlib ordinal arith, ZERO Foundation dep ⟹ the one piece
  of this project genuinely well-suited to ARISTOTLE** (contra the lap-17 blanket "poor fit").
  - The outside plan's "Domination.lean has `towerO/repr_towerO/exists_repr_lt_omegaTower`" is **wrong**
    — those names don't exist. Repo has `toONote`/`repr_toONote`/`toONote_NF` (base-b Goodstein coding,
    sparse) + tower material in `Hardy.lean` (`tower i`, `fastGrowingε₀`, A4 `fastGrowing_lt_fastGrowingε₀`).
- ✅ **Don't reuse `toOrdinal 2 n`/`seqONote`** — correct, and worse than "sparse": `toOrdinal b ·` is
  strictly monotone, so the pullback has `rk lt n = n` and `orderType = ⨆ succ n = ω`, NOT ε₀. F needs a
  **bijective ℕ↔NONote** coding (order type of the *whole* system), not a monotone enumeration.

### F's real blind spot — E pins the order (co-design E and F)
The `≺` whose order type F proves `=ε₀` MUST be the **same** `≺` for which PA proves `TI_≺(X)` from
Goodstein in E. Pick an arbitrary clean NONote-coding for a tidy order-type proof → you then owe E
(*PA ⊢ Goodstein → PA ⊢ TI along that coding*). The repo's natural Goodstein descent (`Domination.seqONote`,
`repr_seqONote`, `seqONote_lt`) is tailored to E but has order type ω (wrong for F). **Crux = one order
simultaneously (a) honestly ε₀ in order type [F], (b) X-free-definable [F2/F3], (c) PA-provably-TI-from-
Goodstein [E].** Co-design, or make `EpsilonOrder` expose the E-hook (standard CNF order on ℕ-codes +
Goodstein-descent-embeds-into-it).

### Corrected F work order
1. ✅ **DONE (lap 18, `src/GoodsteinPA/EpsilonOrder.lean`, all axiom-clean).** The whole **definability
   half** of F is built: `eval_lMap_structLX`, `hprec_of_eval`, `hprec_of_lMap_defined` (discharge the
   exact Boundedness `hprec` for ANY `lMap`-definable `lt`); `xpos_lMap` + `hprecXPos_lMap` (⟹ `hprecXPos`
   automatic); and the **`Seam` structure** (`GoodsteinPA.EpsilonOrder.Seam`) bundling `lt`/`φ`/`hφ`/`ge`
   with methods `Seam.prec`/`hprec`/`hprecXPos`. **Only `Seam.ge : ε₀ ≤ orderType lt` is left undischarged.**
2. **`codeOfREPred₂` + spec (Foundation-side)** — NEXT tractable brick. NOTE `Semisentence ℒₒᵣ 2 =
   Semiformula ℒₒᵣ Empty 2` ⟹ need `Empty→ℕ` embedding (`Rew.emptyMap`/`Semiformula.emb`) to feed
   `Seam.φ : Semiformula ℒₒᵣ ℕ 2` / `hφ`. (Or add a `Semisentence`-flavoured `hprec_of_lMap_defined`.)
3. **ε₀-completeness `∀ o<ε₀, ∃ x:ONote, NF x ∧ repr x = o`** = `Seam.ge` (the real girder; mathlib-only;
   Aristotle-eligible). mathlib `Ordinal.lt_epsilon_zero : o<ε₀ ↔ ∃ n, o<(ω^·)^[n] 0` is the tower hook.
4. Bijective ℕ↔NONote coding + transfer order type (build `Seam.lt` + its `ge`).
5. Instantiate `Seam` (combine 2+3+4). The definability fields are already discharged by step 1.
6. Reconcile with E (same `lt`) before claiming the seam closes the headline.

---

## ⏭️ LAP-16 (2026-06-22) — C₂ structural port LANDED; the `exs` wall = a calculus retrofit. Read FIRST.

**Landed (green, committed):** `src/GoodsteinPA/EmbeddingX.lean` — `embedC_LX_gen` (9/10 `Derivation2`
cases, `axm`-abstracted) + `provable_true_x` (X-free ω-completeness, `XFreeAx`-safe) + `XFreeForm`.

**THE finding (corrects the lap-15 "mechanical" claim):** the `exs` case is NOT mechanical. Collapsing
a closed witness to a numeral needs a **value-congruent EM**; for an X-atom body that requires Buchholz's
**value-congruent X-pair axiom** `{Xs,¬Xt}` (`sᴺ=tᴺ`, `AX(Z∞)`, lecture notes p.27), which our same-atom
`Deriv.axL` does NOT provide. **Read `ANALYSIS-2026-06-22-lap16-exs-axLv.md`** — full obligation map +
retrofit recon (5/8 ZinftyGen sites mechanical; `atomCutAux` = Buchholz Remark p.27 = the one hard spot;
`removeFalseLit_x` X-free-restriction keeps `XFreeAx` safe; Boundedness case 1.2 = p.29).

### LANDED (lap 16): the `axLv` retrofit — green across all 3 files, 1 disclosed `sorry` left
`Deriv.axLv` (value-congruent literal axiom, Buchholz `AX(Z∞)` p.27) threaded through ZinftyGen
(incl. `atomCutAux` Remark p.27 + 3-case `removeFalseLitAux`), Boundedness (case 1.2 p.29), and
XFreeCutElim (7/8 `_x` sites). Remaining `sorry`: `PXFc.atomCutAux`'s value-cong **X-atom-cut** case
(`XFreeCutElim.lean:1048`) — C₁/D carry it temporarily.

### NEXT (lap 17): `nrel_value_subst` clears it; then `exs`; then `embedC_LX`
1. **`PXFc.nrel_value_subst`** — `Δ` cut-free `XFreeAx`, `nrel r v ∈ Δ`, `|v|=|w|` ⟹
   `PXFc d.o 0 (insert (nrel r w) (Δ.erase (nrel r v)))`. Mirror `removeFalseLitAux_x` with frame
   `Γ.erase Lit → insert Lit' (Γ.erase Lit)`; leaves close via `PXFc.axLv`/X-free `axTrue`; matched
   `axLv` leaf: extract via `congrArg (∼·)` not raw dependent `injection`. Then transport `hNC` in
   `atomCut_x` Case `hrel`.
   - **fallback** if the dependent leaf cases swamp: isolate as a disclosed `axiom` (NOT on headline)
     to let `cutElim` go clean-modulo-that, OR keep the current `sorry` and move to `exs`/`embedC_LX`
     (which don't depend on `nrel_value_subst`) to make orthogonal progress.
2. ~~`exs`~~ ✅ DONE lap 16 — `embedC_LX_gen` is sorry-free + axiom-clean (`provable_em_cong_gen_x`
   via `axLv` + `PXFc.exI_closed`).
3. **`embedC_LX`** = `embedC_LX_gen` at `↑paLX` + `hax` (X-free `provable_true_x`, X-ind `metaInduction`).
   Independent of `nrel_value_subst` (only the cutElim end of D needs that).

### C₂-axm discharge (after structural is sorry-free) — `paLX` + `hax`
`paLX := Theory.lMap (ORing.embedding LX) 𝗣𝗔⁻ + InductionScheme LX Set.univ`. X-free axioms via
`provable_true_x`; X-induction via `metaInduction` glue. (`InductionScheme L` IS generic over ORing `L`.)

---

## ⏭️ LAP-15 (2026-06-22) — review validated lap-14 design; EXECUTE C₁ then C₂. Read this FIRST.

**Direction CONFIRMED sound** (fresh-mind review). Lap 14 finished the crux (Boundedness Thm 5.4 +
corollary B, axiom-clean). The remaining work to **Thm 5.6 (`PA ⊬ TI(ε₀)`)** is C₁+C₂ (connective
tissue), then E (Goodstein⟹TI bridge) + F (arithmetization seam). **Key validated fact (lap 15):** the
cr=0 design is feasible — `atomCut` on an X-atom, applied to `XFreeAx` inputs, preserves `XFreeAx`, because
(i) our `Provable.axL` is the *same-atom* EM axiom `{Xs,¬Xs}` so X-atomic cuts close by **set idempotence**
(the `axL` branch of `atomCutAux`, no truth), and (ii) the truth-surgery branch (`removeFalseLitAux`) fires
only on an `axTrue` leaf *equal to the cut atom* = an X-`axTrue` leaf, which `XFreeAx` forbids ⟹ **vacuous**.
So `removeFalseLitAux` is only ever invoked on X-FREE cut atoms (emitting X-free `axTrue`, fine).

### ✅ C₁ — XFreeAx-preserving cutElim → cr=0 — **DONE lap 15, axiom-clean** (`src/GoodsteinPA/XFreeCutElim.lean`).
Full `PXFc` port: builders + inversions-at-cr≤c + cut reductions + truth layer + `cutElim` + the Thm-5.6
tail `orderType_le_of_TIprovable` (`PXFc α c {TI} ⟹ ‖≺‖ ≤ 2^(ω_c^α)`). **C₂ is now the only connective
gap to Thm 5.6.** (Original C₁ plan kept below for reference.)

### C₂ — `embedC` over LX. **CRUX DONE lap 15; structural port is THE NEXT TARGET (lap 16).**
Done lap 15 (`src/GoodsteinPA/XFreeCutElim.lean`, axiom-clean): `provable_em_x` (LX excluded middle →
`PXFc`, `XFreeAx`-automatic) + **`metaInduction`** (the X-induction embedding via a cut-tower on `ψ(i)`,
`XFreeAx`-preserving — the faithfulness-critical case). **Remaining = the STRUCTURAL `embedC` port:**
mirror `src/Embedding.lean:525–660` (induct on `Derivation2 (𝗣𝗔(LX):Schema) Γ`, emit `PXFc`), swapping
`ZinftyF`/`ℒₒᵣ` → `ZinftyGen`/`LX`. `axm`: PA⁻(LX) via `provable_true_x` (port `provable_true`, X-free
`axTrue`); X-induction via `metaInduction` (+ Foundation-DSL to build `step` from `ψ` + strip
`univCl`/`🡒`). `exs`: port `exI_closed`. **First resolve: what is `Z ⊢ TI(X)` in Lean?** (the target
schema is entangled with F — check Foundation's `PeanoMinus`/`InductionScheme` genericity over `ORing`).
See HANDOFF §"NEXT (lap 16)" for the full breakdown.

### C₁ original plan (reference; superseded by the DONE above):
Introduce in `Boundedness.lean` (or a new `src/GoodsteinPA/XFreeCutElim.lean`) the cut-rank-carrying carrier
`PXFc α c Γ := ∃ d : Deriv Γ, d.o ≤ α ∧ d.cr ≤ c ∧ XFreeAx d` (generalises lap-14's `PXF` = `PXFc α 0`).
Port, each tracking `XFreeAx` (the `Deriv` constructors used are exactly axL / X-free-axTrue / verumR / weak
/ andI / orI / allω / exI / cut — none add an X-`axTrue` except the vacuous `removeFalseLit` branch above):
1. **Smart builders** `PXFc.{mono,weakening,axL,axTrue(Xfree),verumR,andI,orI,exI,allω,cut,contr}` —
   mirror `ZinftyGen.Provable.*` (lines 179–265) but carry the third `XFreeAx` component. Most are trivial
   (`XFreeAx` of a built node = conjunction/∀ of the parts' `XFreeAx`, by the `def XFreeAx` clauses).
2. **`removeFalseLitAux` / `removeFalsumAux`** preserve `XFreeAx`: port `ZinftyGen` 1087/1334 threading the
   property. KEY: `removeFalseLitAux` is stated for a FALSE literal `signedLit b₀ r₀ v₀`; on the X-route it
   is only ever called with `r₀` X-FREE (from the vacuous-branch argument), so its emitted `axTrue` leaves
   are X-free ⟹ `XFreeAx`. State it with an added hyp `Sum.isLeft r₀ = true` (X-free cut atom) to make this
   explicit, OR thread `XFreeAx d` and show the X-axTrue case can't arise.
3. **`atomCutAux` / `atomCut`** (ZinftyGen 1191/1320) preserve `XFreeAx`: the `axTrue`/`heq` branch needs the
   leaf = cut atom; for X-free cut atoms it's an X-free leaf (fine); the cut atom is X-free anyway on the
   route. To be safe handle generic atoms: if the cut atom is an X-atom, the `axTrue`/heq branch is vacuous
   by `XFreeAx`, and the `axL` branch + structural cases are truth-free.
4. **`cutReduceConj/Disj/AllAux/All`** (ZinftyGen 796/826/862/1017) preserve `XFreeAx`: they compose the
   `XFreeAx`-preserving inversions (lap-14 `andInv_xfree`/`orInv_xfree`/`allInv_xfree` — already built! but
   at cr=0; **generalise them to cr ≤ c** since inversions don't change cut rank) + builders + `cut`.
5. **`cutElimPrincipal` / `cutElimStepAux` / `cutElimStep` / `cutElim`** (1422/1479/1529/1537): structural
   port; `cutElim : PXFc α c Γ → PXFc (omegaTower c α) 0 Γ`. This is the deliverable feeding corollary B.
**Aristotle target:** a self-contained "`removeFalseLitAux` preserves `XFreeAx` for X-free `r₀`" or a
`PXFc` builder lemma (inline the `Deriv`/`XFreeAx`/`o`/`cr` defs). Bounded + mechanical.

### C₂ — `embedC` over generic LX (parallel/after C₁). Plan in lap-14 HANDOFF §C₂ (CRITICAL: X-induction
axioms via the meta-induction tower of `cut`s on `φ(i)` + `provable_em` base/step — NOT `provable_true`,
which would lone-X-`axTrue`. `𝗣𝗔⁻` X-free axioms can still go via `provable_true`. Port the lap-10 worked
meta-induction). Produces the `XFreeAx` derivation of `{TI}` that C₁ then reduces to cr=0.

## ⏭️ LAP-13 (2026-06-22) — Buchholz route EXECUTING; read this FIRST

**Read `ANALYSIS-2026-06-22-lap13-boundedness-design.md`** (full Buchholz §5 pp.26–31 read + the design).
Lap 13 built ALL the Boundedness prerequisites — green, axiom-clean, in `src/`:
- `LangX.lean` — `structLX (S:ℕ→Prop) : Structure LX ℕ` (the `⊨^S` carrier) + DecidableEq instances +
  `eval_Xatom`. **The `⊨^α` carrier.**
- `ZinftyGen.lean` — **M5 cut-elim generalised over `{L}[ORing L][Structure L ℕ][DecEq…]`**,
  `Provable.cutElim` axiom-clean. Reused wholesale (no cut-elim re-proof on the X-route).
- `TruthSem.lean` — `rk`/`orderType`/`levelSet`/`models (⊨^γ)`/`Sat` + **`models_lMap` (X-free
  invariance)** + `orderType_le_of_forall`.
- `XPositive.lean` — `XPos` + **`models_mono` (⊨^γ monotone in γ on X-positive formulas)** (Buchholz
  cases 2/3/4) + `val_structLX_eq` + `eval_mono`.
- `wip/BoundednessProbe.lean` — `Xatom_axiom`: the Buchholz X-atom axiom `{Xs,¬Xt}` (sᴺ=tᴺ) is
  derivable in generic Z∞ at `(LX,structLX S)` for ANY S. (Validation probe; stays in wip.)

**THE crux still open = Boundedness Thm 5.4 (the 8-case induction) + its formula scaffolding.** Next:
1. **Construct `Prog_≺(X)` / `TI_≺(X)` as `LX`-formulas.** Parametrise by `prec : Semiformula LX ℕ 2`
   (the order, with its ℕ-interpretation = the wellfounded `lt`; for the app `prec` is ℒₒᵣ-definable OT
   order). `Prog := ∀x(∀y(y≺x → Xy) → Xx)`, `¬Prog ≃ ∃x(∀y≺x Xy ∧ ¬Xx)`. Use Foundation DSL/`∀⁰`/`∃⁰`
   + `Xatom`. Pin the inversion shape (`exI`/`allω`/`orI` on `¬Prog`) the induction needs.
2. **Boundedness (Thm 5.4):** induction on the cut-free `Provable β 0` `Deriv` over `LX` (cases =
   our constructors axL/axTrue/verumR/weak/andI/orI/allω/exI/cut ↔ Buchholz's 8). Ingredients ALL
   built: Ax→`Xatom_axiom` (X-pair) / `models_lMap` (TRUE₀); ⋀/⋁/Rep→IH + `models_mono`; ¬Prog `exI`
   inversion = case 2; `cut` on X-atom = case 8. Conclude `Sat lt (α+2^β) Γ`. THE new theorem.
3. **Corollary** `‖≺‖ ≤ 2^β` via `orderType_le_of_forall` (invert TI → ⊢^β_1 ¬Prog,Xn → 5.4 → ⊨^{2^β}Xn
   → rk n < 2^β ∀n).
4. **M4 `embedC` over LX** (mechanical `{L}` generalisation like M5; PA(X) axioms true in structLX S
   for any S since first-order induction holds for any fixed predicate) + assemble **Thm 5.6**
   (`Z⊢TI(X) ⟹ ‖≺‖<ε₀`).
5. **Goodstein⟹TI_≺(X)** bridge (VERIFY-(b)) + arithmetization seam (OT↔ε₀, `‖≺‖=ε₀`) ⟹ headline.

**Banked off-path (do NOT resume):** witness-bounded `wip/` calculi (Towsner/operator-H). The ℒₒᵣ-only
`src/Zinfty.lean`/`src/Embedding.lean` stay for now (existing users); the live chain uses the LX versions.

## ⏭️ LAP-12 PIVOT (2026-06-22) — superseded by lap-13 above (kept for the Buchholz-route rationale)

**Read `ANALYSIS-2026-06-22-lap12-buchholz-pivot.md`.** The lap-11 "build the witness-bounded `Zᵏ`" plan
below is **retired**: lap 12 proved its §19.6 cut-elim needs the Buchholz operator `H` (ADDENDUM 7 in
`ANALYSIS-…-cutelim-k-threading.md`) — a multi-lap wall — while Buchholz §5's **witness-FREE** route reuses
the done-and-axiom-clean **M4 `embedC`** + **M5 `cutElim`** and needs only a **Boundedness** theorem. The
lap-11 "embedC is the wrong object" verdict was a conflation of order-type-boundedness (valid, Buchholz
Thm 5.4) with witness-boundedness (walled, Towsner). **`embedC` is the RIGHT object** (Buchholz Thm 5.5).

**New critical path (Buchholz §5 — `Z ⊢ TI_≺(X) ⟹ ‖≺‖ < ε₀`, then Goodstein⟹TI(ε₀)):**
- **0. VERIFY-FIRST (do before deep work):** (a) M5/M4 take the set variable `X` (extend `ℒₒᵣ`→`ℒₒᵣ∪{X}`
  or add `X` as a fixed relation symbol; `embedC.axm`/`provable_true` only need the `X`-free PA axioms);
  (b) the Goodstein⟹TI_≺(X) bridge is provable in PA via the Phase-0 CNF-ε₀ encoding. Neither is a known
  wall; confirm before sinking laps.
- **1.** Truth semantics `⊨^α Γ` (`X := {n : |n|_≺<α}`), `Prog_≺`, ≺-norm `|n|_≺`, order type `‖≺‖`,
  X-positivity — light self-contained defs.
- **2.** **Boundedness (Thm 5.4)** — `Z∞ ⊢^β_1 ¬Prog_≺(X),¬Xs₁,…,¬Xsₖ,Γ & |sᵢ|_≺≤α ⟹ ⊨^{α+2^β} Γ`
  (Γ X-positive), by induction on the cut-free `Provable β 0`-derivation (8 cases, Buchholz p.29).
  Corollary: `Z∞ ⊢^β_1 TI_≺(X) ⟹ ‖≺‖ ≤ 2^β`. THE new theorem; no Hardy, no witness bound.
- **3.** Goodstein ⟹ TI_≺(X) for the ε₀-order (bridge; Kirby–Paris/Cichoń; reuse Phase-0 encoding).
- **4.** Assembly: PA⊢Goodstein ⟹ (M4) ⟹ (M5 cut-free `β<ε₀`) ⟹ (Boundedness) `‖≺‖≤2^β<ε₀`, but the
  ε₀-order has `‖≺‖=ε₀` ⟹ `False` ⟹ discharge headline, `#print axioms` clean.

**Banked off-path (do NOT resume on this route):** the witness-bounded `wip/` calculi. Lap-12 PROVED the
norm-budget half of Towsner §19.6 (`cutReduceAllAux` in `wip/OperatorZinfty.lean`, axiom-clean, via the
norm-carrying `ZekdProv` wrapper — see ADDENDUM 6); the witness-budget half needs operator `H` (ADDENDUM
7). Kept as reference IF the Buchholz route ever stalls. M6 (Hardy) is off-path too.

---

## ⏭️ LAP-11 FINAL STATE (2026-06-22) — SUPERSEDED by the lap-12 pivot above (kept for history)

**M4 — the embedding `embedC` — is COMPLETE, axiom-clean, promoted to `src/GoodsteinPA/Embedding.lean`,
in the default build.** `embedC : Derivation2 (𝗣𝗔:Schema) Γ → ∃ c, ∀ e, ∃ α, Provable α c (Γ.image
(asg e ▹))`. The two hard cases fell to two reusable lemmas: `Provable.exI_closed` (closed-witness
∃-intro, from value-congruent EM `provable_em_cong_gen` + cut) for `exs`; `provable_true`
(ω-completeness) for `axm`. See HANDOFF lap-11.

**⚠️ COURSE CORRECTION (lap 11, grounded in Towsner §13–17) — read
`ANALYSIS-2026-06-22-witness-bound-gap.md`.** The headline needs the **witness-bounded calculus
`Zᵏ`**, NOT a bound on M5's `Provable`. M5 tracks cut-rank `c` but drops Towsner's I∃ witness bound
`k` (`value(t) ≤ h_α(k)`) — and without it the lower bound (Thm 17.1) does not bite (`provable_true`
gives a cut-free `< ε₀` derivation of `{↑gs}`; bounded quantifiers cost `allω`=`ω`, `exI` costs `+1`
regardless of witness value). So `embedC` = the *unbounded* embedding (Towsner Thm 14.2), reusable but
not the headline object; the lap-11 `wip/Bounding.lean` bridge `cutfree_lt_eps0_absurd` is FALSE as
stated. The lap-9 "bound directly on unbounded `Deriv`" reframe is retracted.

**Corrected critical path (= lap-5 plan steps 1–4, now confirmed):**
1. **`Zᵏ`** = M5 `Deriv` + `(α,k)` witness bound on `exI`. Revive banked `wip/` Zekd/OperatorZinfty
   (lap-8 worked §19.2–19.5 + control axis). Carrier: `ZekdProv` wrapper `∃ α'≤α, α'.NF ∧ Zᵏ …`.
2. **Bounded embedding (Towsner Thm 16.1/16.5/16.7)** into `Zᵏ`. `axm`: 16.1 (universal axioms, via
   `provable_true` on the bounded matrix) + 16.5 (induction, bounded meta-induction ordinal
   `ω·4#2^{rk}#2`, via `provable_em` + `Provable.exI_closed`). Structural: port `embedC` cases.
3. **`(α,k)`-cut-elim (Thm 19.9)** — `wip/` Zekd §19 grind (`ANALYSIS-…-cutelim-k-threading.md`).
4. **Subformula bridge to `B`** (M6) + Σ₁-arithmetization seam (M7a: `codeOfREPred` ↔ `atomTrue`,
   anchor `codeOfREPred_spec`) + ONote↔Ordinal<ε₀ seam ⟹ contradiction with
   `lowerBound_hardy_selfcontained`.

**BANKED reusable (src/Embedding.lean, axiom-clean):** `provable_true`, `provable_em`,
`provable_em_cong_gen`, `Provable.exI_closed`, `embedC` structural cases. Do NOT discard.
**Aristotle candidates:** a `Zᵏ` mono/inversion lemma; the ONote↔Ordinal<ε₀ bridge; a `norm_add_le`/
NF ordinal fact from the §19 bookkeeping.

---

## ⏭️ LAP-10 FINAL STATE (2026-06-22) — superseded by lap-11 above; kept for context

**Headline result: the M5 `axTrue` truth-layer surgery is DONE (axiom-clean) and the assignment-
carrying embedding `embedC` is 8/10.** Full status in `HANDOFF.md`. The TWO remaining `embedC` cases
(`axm`, `exs`) both reduce to ONE shared deep lemma — build it next:

**`provable_subst_congr` (closed-term substitution congruence — THE next chip).** For closed terms
`s s'` of equal ℕ-value and any `ψ : SyntacticSemiformula ℒₒᵣ 1`: the sequent `{∼(ψ/[s]), ψ/[s']}` is
Z∞-derivable (`∃ a, Provable a 0 {...}`). Proof = induction on `ψ.complexity` (the `provable_em`
template), tracking the two terms:
- **atomic** `ψ = rel/nrel R v` (v mentions `#0`): `ψ/[s]` and `ψ/[s']` have EQUAL truth (`Evalm`
  depends on a term only via its value — `Semiterm.val_substs` (Semantics.lean:123) + `eval_substs`
  (l.391)). So `∼(ψ/[s])` and `ψ/[s']` can't both be false ⟹ one is a true literal ⟹ `Provable.axTrue`.
  (Needs the value-equality `hval` and that `(ψ/[s]).LitTrue ↔ (ψ/[s']).LitTrue`.)
- **and/or/all/exs**: recurse structurally, exactly mirroring `provable_em`'s compound cases (the ∀/∃
  cases use the `nm`-family + `exI`/`allω`, with the substituted term threaded through `/[·]`).
Then derive:
- **`Provable.exI_closed (s closed, value m)`: `Provable α c (insert (ψ/[s]) Γ) → ∃ β, Provable β c
  (insert (∃⁰ψ) Γ)`** — cut `provable_subst_congr s (nm m)` (weakened into Γ) against the hypothesis to
  swap `ψ/[s] ⤳ ψ/[nm m]`, then `Provable.exI ψ m`. Finishes `embedC.exs` (the `rew_subst_term` setup
  is already in place — see `wip/Embedding.lean`).
- **`embedC.axm`**: `𝗣𝗔⁻` instances → strip `∀` (`allω`), decompose connectives, bottom at `axTrue`;
  `univCl(succInd ψ)` → the worked meta-induction below, with `nm n+1 = nm(n+1)` via the same congruence.

API notes: term value = `Semiterm.valm ℕ ![] id s`; numeral value `valm ℕ … (nm m) = m` (find/derive
`val_numeral`); `nm`/`signedLit`/`LitTrue` live in `src/GoodsteinPA/Zinfty.lean` now.

---

## ⏭️ LAP-10 PROGRESS (earlier in lap)

**Done lap 10 (all committed, green):**
- `rew_subst_nm` PROVED ⟹ `provable_rew`/`ZProvable.rew` fully axiom-clean (`[propext, choice,
  Quot.sound]`). The M4 renaming enabler is DONE.
- `embed` `shift` + `all` PROVED ⟹ **8/10 cases** (only `axm`, `exs` remain). `all` is the ω-rule
  case: `provable_rew` substitutes the freed var by each `nm n` (undoing the `shift` on `Γ` via
  `rewrite_comp_shift_eq_id`), then `Provable.allω`.

**Remaining M4 cases — both deep:**

### `axm` (THE crux — Z∞-derive each PA axiom). `φ ∈ (𝗣𝗔:Schema)` = `↑σ`, `σ ∈ 𝗣𝗔⁻ ∪ InductionScheme`.
`axm` does NOT need the assignment reformulation (φ=↑σ is CLOSED). By `ZProvable.weakening` (`{↑σ} ⊆ Γ`
since `↑σ ∈ Γ`) reduces to `ZProvable {↑σ}` per axiom.
- **(a) `σ ∈ 𝗣𝗔⁻` (PeanoMinus, finite):** each a true closed ∀-sentence (semiring/order axioms). Z∞-
  derivable at finite ordinal. Bounded grind (enumerate Foundation's `PeanoMinus` axiom set).
- **(b) `σ = univCl(succInd ψ)` — induction via ω-rule. FULL PAPER PROOF WORKED OUT (lap 10):**
  `succInd ψ = ψ(0) → (∀x, ψ(x)→ψ(x+1)) → ∀x, ψ(x)`. After stripping `univCl` (iterated `allω` over the
  free-var numeral assignments) and two `orI` (Tait `A→B ≡ ∼A⋎B`), reduce to the sequent
  `S := {∼ψ(0), ∼(∀x,ψ(x)→ψ(x+1)), ∀x,ψ(x)}`. Introduce `∀x,ψ(x)` by `allω`: ∀n need `{∼ψ(0), ∼∀step, ψ(n)}`.
  **Meta-induction on n** (the heart — ω-rule absorbs PA-induction):
  - n=0: `{∼ψ(0), …, ψ(0)}` has `ψ(0)` and `∼ψ(0)` ⟹ `provable_em`. ✓
  - n→n+1: want `{∼ψ0, ∼∀step, ψ(n+1)}`. **`cut` on `ψ(n)`** (cut rank = `complexity ψ + 1`, uniform):
    - left `{∼ψ0, ∼∀step, ψ(n)}` = IH `D_n`. ✓
    - right `{∼ψ0, ∼∀step, ψ(n+1), ∼ψ(n)}`: `∼∀step = ∃y∼step(y)`; `exI` witness `n` reduces to
      `{∼ψ0, ∼step(n), ψ(n+1), ∼ψ(n)}` where `∼step(n) = ψ(n) ⋏ ∼ψ(n+1)`; `andI` splits into
      `{ψ(n),…,∼ψ(n)}` (em ✓) and `{∼ψ(n+1),…,ψ(n+1)}` (em ✓).
  Cut rank uniform `complexity ψ + 1`; ordinal O(n) per instance ⟹ `allω` gives ~ω. **Uses ONLY M5's
  existing constructors** (`provable_em`/`cut`/`exI`/`andI`/`allω`/`orI`) — no new smart constructors.
  Lean friction = Foundation-syntax wrangling: unfold `↑(univCl(succInd ψ))` `“…”`-DSL into the nested
  `⋎/∼/∀/∃` structure + the numeral substitutions `step(n)`, `ψ(x+1)`. Mechanical but intricate; multi-step.

### `exs` (needs the assignment reformulation). Open witness term `t` ⟹ naive statement can't close it.
Reformulate `embed : ∀ e:ℕ→ℕ, ZProvable (Γ.image (ρe ▹))`, `ρe := Rew.rewrite (nm∘e)`. ALSO needs a Z∞
closed-term→numeral collapse (`ρe▹t = nm m` is arithmetic, built from PeanoMinus eqns ⟹ intertwined with
`axm`(a)). Restructure re-proves the 8 done cases (mechanical, ρe distributes) — do AFTER `axm`.

---

## 🧭 LAP-9 DEEP-REFLECTION COURSE-CORRECTION (2026-06-22)
Full synthesis: `REFLECTION-2026-06-22.md`. STATUS refreshed. **The priority order below (A/B/…) is
SUPERSEDED.** New order, hardest-first = **unavoidable-first**:

1. **M4 — embedding `𝗣𝗔 ⊢ φ ⟹ Z_∞ ⊢^{α}_c {φ}` = THE next target.** The *universal bottleneck*:
   needed on Route A, two-phase Route B, AND the abandoned Zekd route — there is no headline path that
   skips it. **LAP-9 FEASIBILITY PROBE (done this lap) — the machinery EXISTS; here is the mapped path:**
   - **Foundation's finitary calculus** (`.lake/.../Foundation/FirstOrder/Basic/Calculus.lean`):
     `Derivation 𝓢 : Sequent L → Type` (List sequents), constructors
     `axm (φ∈𝓢) | axL | verum | or | and | all (φ.free :: Γ⁺) | exs t | wk | cut` — maps almost 1-1
     onto M5's `ZinftyF.Deriv`. A **Finset** variant `Derivation2` exists (`Calculus2.lean:13`, same
     constructors) + `provable_iff_derivable2 : 𝓢 ⊢ φ ↔ 𝓢 ⊢!₂! φ` (`Calculus2.lean:94`) — matches M5's
     Finset substrate (use it to skip the List→Finset bridge).
   - **The lap-6 "derivation-substitution" deep case is ALREADY PROVIDED:**
     `Derivation.rewrite : 𝓢 ⟹ Γ → ∀ (f:ℕ→SyntacticTerm L), 𝓢 ⟹ Γ.map (Rew.rewrite f ▹ ·)`
     (`Calculus.lean:255`). So the **finitary `all` (`φ.free :: Γ⁺`) → M5 ω-rule `allω`** conversion is:
     for each numeral `n`, `rewrite` the free var by `n` to get `𝓢 ⟹ φ/[n] :: Γ`, embed each, assemble
     via `Provable.allω` (`src/Zinfty.lean:183`). **No missing machinery.**
   - **The `axm` case** splits cleanly because `𝗣𝗔 = 𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ`
     (`Foundation/FirstOrder/Arithmetic/Schemata.lean:52`): (a) `φ ∈ 𝗣𝗔⁻` (PeanoMinus, **finite**) —
     each a true ∀-sentence, Z∞-derivable at a finite ordinal (bounded grind); (b) `φ = univCl(succInd ψ)`
     (`mem_InductionScheme_of_mem`, Schemata.lean:85) — derive in Z∞ **via the ω-rule** (`ψ(n)` for each
     `n` by `n`-fold step, then `allω`), ordinal ~`ω·k`. **This is the one genuine deep case** (Buchholz
     §5.5 / Towsner §16) — but it's standard textbook content and `Provable.allω` is already built.
   - **LAP-9 DID THIS: `wip/Embedding.lean` COMPILES** (`lake env lean wip/Embedding.lean`).
     `embed : Derivation2 (𝗣𝗔:Schema) Γ → ∃ α c, Provable α c Γ` over the SAME `Finset (SyntacticFormula
     ℒₒᵣ)` substrate (no language translation). **6/10 cases DONE** (verum/and/or/wk/cut/closed).
     **`provable_em` FULLY PROVED + axiom-clean** (`[propext,choice,Quot.sound]`): the Z∞ excluded-middle
     `∀ φ Γ, φ∈Γ → ∼φ∈Γ → ∃ a, Provable a 0 Γ`, incl. the ∀/∃ numeral ω-family. Promotable to `src/`.
   - **4 disclosed `sorry`s remain = the genuine deep content, ALL needing free-var/subst machinery
     for M5's `Deriv` (interdependent). Build the shared enabler FIRST:**
     - **(0, enabler) M5 renaming/subst lemma** = analogue of Foundation `Derivation.rewrite`
       (`Calculus.lean:255`): `Provable α c Γ → Provable α c (Γ.image (Rew…▹·))`, induction on `Deriv`
       (8 cases; `allω` case = the care point). Unlocks `shift`/`all`/`exs` together.
     - **`shift`** — corollary of the enabler. **`all`** — free var `&0` → each numeral via enabler →
       `allω`. **`exs`** — witness term → numeral value → `exI`. **`axm`** (deepest) — PeanoMinus finite +
       `univCl(succInd ψ)` via ω-rule. Buchholz §5.5.
2. **M7a — transparent arithmetization** = parallel/fallback (shovel-ready, faithfulness-gated):
   `gAllReal = ∀x∃y[g_y(x)=0]` + `𝗣𝗔 ⊢ goodsteinSentence ↔ gAllReal`, gated by `Bridge.lean`.
3. **Bounding bridge (small, downstream):** prove on M5's **real cut-free `Deriv`** directly
   (`allInv` ∀ away, read `exI` numeral off, witness `≤ hardy(toONote α)N`), combine with M6's
   `hardy_lt_goodsteinLength` (`src/LowerBound.lean:258`). **Reuse M6's ℕ-domination fact, NOT the
   abstract `B` transport** — the `B` lower bound is the template, banked. Ordinal seam = one `toONote`
   (check mathlib `ONote.repr` surjectivity onto `[0,ε₀)`).

**DO NOT RESUME** the witness-bounded cut-elim thread: `cutReduceAllAux`, `Zekd`, any 4th index
calculus. Proven off-critical-path (lap-8 findings: single-index Hardy inequality is FALSE; landscape
memory: the Hardy `k` index was never needed for cut-elim). `wip/{BoundedZinfty,SplitZinfty,
OperatorZinfty}.lean` = reference only. Everything below this block (the lap-7/8 A/B/Zekd plans) is
**historical context**, not the live plan.

---

## 🗺️ OPEN-OBLIGATION INVENTORY (lap-7 end) — full list + 3 attack paths each
### ⚠️ SUPERSEDED by the lap-9 block above — kept for history/attack-path detail only.
The headline `Statement.peano_not_proves_goodstein` is the only `src/` sorry (the designated open
target; anti-fraud — do NOT fill until the chain genuinely closes axiom-clean). It is reached via the
connecting spine. Open spine pieces, with attack paths:

## 🧭 LAP-8 STRATEGIC PIVOT (ON-LINE-FINDINGS 2026-06-22) — TWO-PHASE architecture is the headline path
The findings doc (`archive/findings/…omega-rule-commuting-bound.md`) **proves the §19.6 commuting bound
cannot close in any single-numeric-`k`/`(k,d)`/`(k,d,e)` system** (the Hardy inequality is FALSE; Towsner
hand-waves it). The lap-8 `Zekd cutReduceAllAux` commuting cases hit exactly this wall (norm-boundary
strictness). **Resolution (literature-standard, Buchholz §5 / Schwichtenberg–Wainer Ch.4): NEVER thread
the witness index through cut-elim. Two phases:**
  1. **Cut-elimination on the WITNESS-INDEX-FREE calculus** — pure ordinal + cut-rank. **This is M5,
     `src/Zinfty.lean`, ALREADY DONE + axiom-clean** (`Deriv.Provable.cutElim`). Commuting cases there are
     one-liners (`α#βₙ < α#β`) — no `k`/`d`/`e` to thread.
  2. **Hardy-bound the CUT-FREE result** — on a cut-free derivation there is NO `+α` growth, so the
     `max{k,n}`-vs-`+α` clash cannot arise. **This is M6, `lowerBound_hardy_selfcontained`, ALREADY DONE**
     (applied at `c=0`).
**The remaining work is the BRIDGE connecting them** (was "step 4 subformula bridge", now the critical
path): a cut-free `Z∞ ⊢^{α}_0 {gAll}` (from M4-embed + M5-cutElim) ⟹ a witness-bounded `B`-derivation
(subformula property: cut-free `{gAll}` uses only `GForm` subformulas; + a Hardy **bounding lemma** reading
off `∃`-witnesses ≤ `H_α(N)` on the cut-free structure) ⟹ contradicts `lowerBound_hardy_selfcontained`.
**Next lap: build this bridge.** The `Zekd`/`SplitZinfty` witness-bounded-cut-elim effort is a banked
alternative (NOT on the critical path anymore); its inversions/§19.5/`mono_e`/structural-`cutReduceAllAux`
cases stand for reference. Faithfulness corrections from the findings (carry into write-ups): Lemma 16.10
is `α<β ∧ τα<k ⟹ h_α(k)<h_β(k)` (strict); cut-elim base is `ω^α` (Towsner)/`3^α` (Buchholz), not `2^α`;
`h_{β#ω}(k)=h_β(2k)` is NOT a Towsner lemma (heuristic only); the operator `H[X]` is Buchholz-1992, not
the on-disk notes (which are pure-ordinal for PA).

---

**LAP-8 UPDATE — (A)/(B) substantially advanced.** Hardy-infra layer BANKED (axiom-clean, `src/`):
`hardy_add_comp`/`hardy_add_collapse` (control collapse) + `hardy_comp_lt_goodsteinLength` (lower-bound
nested-index domination). Control-ordinal operator calculus `Zekd α e k d c Γ` built in
`wip/OperatorZinfty.lean`, sorry-free through §19.5, with the NEW `mono_e` control axis. Design validated
(ADDENDUM 5): single control ordinal `e` closes the ADDENDUM-4 witness-index obstruction (no set-valued
`H` needed). **ONE remaining girder for step-1 cut-elim: §19.6 `cutReduceAll` on `Zekd`.**
  - **[LAP-8 NEXT] Port `Zinfty.lean:785 cutReduceAllAux` to `Zekd`.** Invert ∀-side → `fam`; induct on
    ∃-side; principal `exI` cuts `fam(witness)`; commuting cases reapply at `osucc(α+γ)`
    (`add_osucc_descent` banked), `d ↦ d + norm α` (norm-budget), `e` raised at the top cut via `mono_e`.
    **FIRST**: NF-ify the `Zekd` leaf rules (`trueRel`/`trueNrel` need `hαNF`) — leaf cases need
    `norm(α+γ) ≤ norm α + norm γ` (`norm_add_le`, NF-essential). ADDENDUM 5 has the subtlety + 3 fixes
    (option (b)/NF-ify-leaves cleanest). Budget arithmetic: issue leaf at the node's own `γ` then `weak`
    up to `osucc(α+γ)` (avoids the `osucc` `+1`-vs-strict-`<` boundary).

**(A) §19.6 `cutReduceAll` — the critical-path crux** (calculus + Hardy infra now in place — see LAP-8).
  1. **Control-ordinal operator calculus (RECOMMENDED).** Replace `Zkd`'s `(k,d)` with an index
     `(e, k, d)` where `e : ONote` is a *control ordinal* and the ω-premise / witness bound use
     `hardy e (n + k) + …` (a `hardy`-closed index). Cut-elim raises `e` to dominate cut-formula bounds;
     the principal cut's witness `w ≤ hardy γ (max k n + d) ≤ hardy e (n + k + d)` (γ<e, hardy mono in
     both args) stays controlled. Lower bound survives via **general Hardy additivity** `hardy α (hardy e m)
     ~ hardy (e (#)+ α) m` (e+α<ε₀ ⟹ G dominates). Port §19.2–19.5 from `SplitZinfty` (`max k ·` ⤳
     `hardy e ·`). **Lap-7 de-risk:** the cut-elim *control* side needs NO new lemma — the witness
     control `hardy γ (idx) ≤ hardy e (idx)` (γ<e) is the **existing** `hardy_le_of_lt` (`src/Hardy.lean`,
     `+ hardy_monotone` for the argument). Only the *lower-bound* side needs general Hardy additivity (B).
  2. **Buchholz set-valued operator `H`** (Buchholz §9 / 1992) — fully general; heavier. Fallback if the
     single control-ordinal `e` can't express some closure. `ON-LINE-REQUEST` filed for the PA spec.
  3. **Restrict the calculus to the `GForm` fragment** (the headline only needs cut-elim for derivations
     of `{gAll}` and its subformulas). The ∃-side may then have bounded structure making the witness
     index controllable without a full operator. Investigate whether the subformula property pre-bounds it.

**(B) General Hardy additivity** `hardy (e (#)+ α) m = hardy α (hardy e m)` (infra for A.1; generalizes
  the proved finite-tail `hardy_add_ofNat`).
  1. Induct on α through the fundamental-sequence structure (successor + limit), using the banked
     `fundamentalSequence`/`Reaches`/`hardy_le_of_reaches` machinery in `src/Hardy.lean`.
  2. Prove only the *inequality* `hardy α (hardy e m) ≤ hardy (e + α) m` (ordinary `+`) — weaker but may
     suffice for domination; likely easier than the exact `#`-additive identity.
  3. Aristotle target: self-contained ONote/Hardy statement (feed once A.1's exact form is pinned).

**(C) §19.7 `cutElimStep` + §19.9 `cutElim`** (depend on A). Ordinal `ω^α` (`norm_omegaPow` banked);
  iterate. Paths: port `src/Zinfty.lean` structure / the `SplitZinfty` helpers / existential-index.

**(D) Subformula bridge** (cut-free operator-derivation of `{gAll}` ⟹ `B`-derivation ⟹ lower bound).
  Paths: structural subformula-closure induction / `GForm ↪ ℒₒᵣ` identification / reuse M6 as-is.

**(E) M4 embedding `PA ⊢ φ ⟹ (calculus) ⊢ φ`** — INDEPENDENT of A (parallel thread). Recon done lap 6.
  Paths: induct on Foundation `Derivation` (axm = Lemma 16.1 + Cor 16.6 induction instances; `all`→ω-rule
  via derivation-substitution; `exs`→witness bound) / list→finset bridge / scope `axm` first.

**(F) M7a language gap** `𝗣𝗔 ⊢ goodsteinSentence ↔ gAllReal` — INDEPENDENT (parallel thread). Paths:
  arithmetize `goodsteinSeq` as a real Π₂ `ℒₒᵣ` formula (Foundation Σ₁ tools) / gate by `Bridge.lean` /
  prove one direction first.

**Lap-7 acted on (A): conceptual crux resolved, 4 lemmas proved, `(k,d)` calculus through §19.5 built,
the two §19.6 obstructions precisely characterized (norm-budget CLOSED, witness-index ⟹ needs operator).**

---

## ✅ LAP-7 — cut-elim `k`/`τ` crux RESOLVED (offline read of Towsner §15–§20). See `ANALYSIS-2026-06-22-cutelim-k-threading.md`.
The lap-6 "norm grows under addition ⟹ cut-elim might break `norm<k`" worry was a **misframing**.
Resolved facts (the design for ALL of §19): (a) `k` is **not** fixed — it grows (§19.5 `k↦2k`; §19.6
`k↦h_{β#ω}(k)`; §19.7 `k↦h_{ω^α}(k)`). (b) `lowerBound_hardy_selfcontained` is already `∀k` ⟹ growth
harmless. (c) every `ONote` is `<ε₀` by construction ⟹ ε₀ side-condition **free**. ⟹ **state the whole
cut-elim chain existentially in `k`**: `CutFree α Γ := ∃k, Zk α k 0 Γ`; endgame
`(∃k c, Zk α k c Γ) → α.NF → ∃ α' k', α'.NF ∧ Zk α' k' 0 Γ`, then subformula-bridge + lower bound.
Route decision recorded in `STATUS.md`: **STAY ROUTE B**. `ON-LINE-REQUEST` closed.

### Refined §19.6 plan (`cutReduceAll` for `Zk`) — the next girder, now unblocked
Port `src/Zinfty.lean:785 cutReduceAllAux` (the lap-3 ∀/∃ reduction over the unbounded `(α,c)`
calculus, fully proved) to `Zk`, adding the `(k,NF,norm)` bookkeeping:
- **Structure (unchanged from lap 3):** invert the ∀-side once (`allInv` → numeral family
  `fam : ∀n, Zk α k c (insert (φ/[nm n]) Γ)`), then **induct on the ∃-side `Zk γ k c Δ`** with
  `(∃∼φ)∈Δ`; principal `exI` case = cut `fam n` at the witness numeral; commuting cases re-apply the
  rule over `Δ.erase(∃∼φ) ∪ Γ`. `Zk` is `Prop`-valued, so induct directly (no height fn `o d`); the
  running ordinal is the constructor bound `γ` itself (sub-bounds `<γ` come from the descent premises).
- **Bound:** ordinal `α + γ` (`ONote.+`, `add_lt_add_left_NF`/`le_add_left_NF` banked); slack via
  `osucc` at cuts (`lt_osucc`, `osucc_NF` banked).
- **`k`-growth (the new content vs lap 3):** the conclusion's `k` is **`h_{β#ω}(k)`** (a Hardy value),
  NOT the input `k` — Towsner §19.6 exactly. ⚠️ **LAP-7 FINDING — the `allω`-commuting case is a REAL
  obstruction, not mechanical.** Reconstructing the ω-rule after adding `α` to the bound needs
  `norm(α+βₙ) < max K n`, but `norm(α+βₙ) ~ norm α + n` exceeds `max K n ~ n` for large `n`, for ANY
  fixed `K` (norm is not `<`-monotone, so `βₙ<β` doesn't bound `norm βₙ`; natural sum + `τα<k` don't
  save it). Towsner's "follows from IH" glosses this. **The numeric `(α,k)` form may genuinely need
  either (1) Buchholz operator-controlled derivations, (2) a generalized `Zk.allω` with a controlled
  premise-index `f n` (re-verify M6 lower bound survives — tension: cut-elim wants `f` to GROW to fit
  `+α`, the lower bound wants witnesses `≤ h(f n) < G(n)` BOUNDED), or (3) re-derived Towsner 16.8–16.10
  Hardy inequalities (likely insufficient per the `+α` analysis).** Full derivation +
  attack options in `ANALYSIS-2026-06-22-cutelim-k-threading.md` ADDENDUM. `ON-LINE-REQUEST` re-filed.
  ⚠️ **LAP-7 UPDATE — option (2) (global numeric index swap) is ELIMINATED.** Tried `max k n → k + n`:
  it fixes §19.6-commuting (`(k+n)+norm α = (k+norm α)+n`) but **breaks `allInv`**, whose principal case
  relies on `max`'s idempotence (`max(max k n₀)n₀ = max k n₀`); under `+` the lingering-duplicate subcase
  produces index `k + 2n₀` (slope 2), forcing the lower bound to need `hardy α (2n) < G n` — a
  *multiplicative* rescaling the additivity lemma does NOT give. So **no single numeric `idx(k,n)` serves
  both** `allInv` (wants idempotence) and §19.6-commuting (wants additive shift). Full analysis:
  `ANALYSIS-…-cutelim-k-threading.md` **ADDENDUM 2**. The `k+n` experiment was reverted (wip stays
  sorry-free). **REVISED RECOMMENDATION = option (1): function/operator-valued `allω` index** (Buchholz
  operator-controlled derivations specialized to PA): each `allω` carries a controlled index *function*
  `g : ℕ → ℕ` (`g n ≤ n + const`), rules compose `g`s (idempotently for `allInv`, post-composing `+norm α`
  for cut-elim). Keeps slope 1, so the proved domination lemmas (`hardy_add_ofNat`,
  `hardy_shift_lt_goodsteinLength`) still apply. Larger refactor of `wip/BoundedZinfty.lean` + `B`/lower
  bound, but it's the only design closing BOTH obstructions. Start fresh-headed; don't half-break wip.
  Lap-7 investigation confirmed M6 domination is STRONG (`hardy_lt_goodsteinLength {α NF} : ∃ N, ∀ m ≥ N,
  hardy α m < G m` — beats `hardy α` at *every* large `m`), so the controlled-`g` lower bound is viable.
  **This is now the hardest-first crux of step 1 — the principal `exI` case is clean; the commuting
  `allω` bounding is the live frontier.** Use `hardy` (`src/Hardy.lean`; `Reaches`/`fundamentalSequence`/
  `hardy_le_of_reaches`/`hardy_monotone` already banked).
- **`norm` ingredient (lap 7): BOTH PROVED + banked, axiom-clean** in `wip/BoundedZinfty.lean`:
  `norm_addAux_le` (head-merge bound) and `norm_add_le {α γ NF} : norm(α+γ) ≤ norm α + norm γ` (the
  `τ(α#β)≤τα+τβ` budget fact). NF is essential — the NF-free version is machine-checked FALSE; the
  eq-merge case is discharged by additive-principality **absorption** (`a + γ = γ` when `repr a <
  ω^(repr e) ≤ repr γ`, via `Ordinal.add_of_omega0_opow_le`). `wip/BoundedZinfty.lean` is **sorry-free**.

---

State after lap 6 (2026-06-22). Build green (`lake build GoodsteinPA`, 1257 jobs). Phase 0 + Phase 1
clean; **M5 (cut-elim) and M6 (Hardy lower bound) both DONE**. Headline stays a literal `sorry`
(anti-fraud). See `PHASE2-DECOMPOSITION.md` for the girder ladder; `ANALYSIS-…-bounding-resolution.md`
§"M4 scoping" for the 5-step connecting spine.

## ✅ LAP-6 — M6 DONE (lower bound self-contained); TOP PRIORITY now = step 1, the `Zᵏ` calculus
`src/GoodsteinPA/LowerBound.lean` (`lowerBound_hardy_selfcontained`) is the full Towsner Thm 17.1 with
no hypotheses beyond `α.NF`, axiom-clean modulo the 🟢 `native_decide` Goodstein base-cases. M5 + M6
are now both complete but **disconnected** (M5 = unbounded `(α,c)` over real `ℒₒᵣ`; M6 = bounded
`(α,k)` over the `GForm` fragment). The connecting spine (hardest-first):

### Step 1 — `Zᵏ`: witness-bounded ω-calculus over real `SyntacticFormula ℒₒᵣ` (Towsner §15)
**DEFINED + §19.2–19.5 DONE** (`wip/BoundedZinfty.lean`, lap 6, all axiom-clean). Chosen design:
**ONote-indexed, B-style (bound-as-parameter, no `⨆`-suprema)** over real `ℒₒᵣ` formulas, with both
`(α,k)` side conditions the lower bound needs (lap-4 finding — cannot be dropped): truth-atom rules
`trueRel`/`trueNrel` (`norm α < k`) + `∃`-witness bound (`exI` carries `n ≤ hardy α k`). Plus a
height-preserving `wk`, a β<α `weak` (raises ordinals in principal inversion cases), `∧`/`∨`/`cut`.
Built: `mono_k`, `mono_c`, `wk`/`weakening`; the **full inversion suite** `orInv`/`andInvL`/`andInvR`/
`allInv` (reshuffle helpers `invPush`/`invPull`/`invPush2`/`inv1Push`/… kept standalone so
`DecidableEq Form` doesn't blow the heartbeat limit inside the big inductions); the **§19.5** ∧/∨
cut-reductions `cutReduceConj`/`cutReduceDisj` (`lt_osucc` + caller-supplied NF upper bound `δ`, result
at `osucc δ` — no natural sum needed).

**NEXT — §19.6 ∀/∃ cut-reduction `cutReduceAllAux`** (the hard, non-invertible one; the witness-bound
survival crux). Port `src/Zinfty.lean`'s measure-style version to parameter-style:
- **Bound framing:** the family `fam : ∀ n, Zk α k c (insert (φ/[nm n]) Γ)`; induct on the ∃-side
  `d : Zk γ k c Δ` with running conclusion bound **`α + γ`** (`ONote.add`; `add_nf` instance gives NF,
  `repr_add` + `Ordinal.add_lt_add_left` give strict monotonicity in `γ` for the premise-`<` conditions).
- **Principal `exI` case** (∃-side introduces `∃⁰∼φ` at witness `n`): cut `fam n` (∀-instance) against
  the ∃-premise on `φ/[nm n]` (complexity `< c`). This is the witness cut.
- The non-principal cases mirror the inversions (reuse the union-reshuffle pattern; src frames the
  running sequent as `Δ.erase (∃⁰∼φ) ∪ Γ`).

**Then `cutElimStep` (§19.7, `c+1→c`, bound `ω^α = oadd α 1 0`) + `cutElim` (§19.9).**

⚠️ **KEY FINDING (lap 6) — the `norm<k` budget does NOT survive ordinal addition; it grows.** `norm`
is `max` over CNF coefficients (`Hardy.lean:637`), and addition MERGES coefficients when leading
exponents coincide: machine-checked `norm ω = 1` but `norm (ω+ω) = norm (ω·2) = 2`. So the naive
"`norm(α+γ) ≤ max`" is **false**; the true bound is additive (`norm(α+γ) ≤ norm α + norm γ`, to verify).
Consequences for the cut-elim design:
- **§19.7 `ω^α` blow-up is SAFE:** `norm (oadd α 1 0) = max (norm α) 1` (machine-checked, `norm_omegaPow`),
  coefficient stays `1` — a pure ω-tower never bumps `norm` beyond `max(norm α, 1)`. So iterating the
  rank-reduction keeps the budget (for `k ≥ 2`).
- **§19.6 within-rank addition is where `norm` grows.** The ω-rule combines premises by *supremum*
  (bound-as-parameter, no sum), NOT addition — so it doesn't bump `norm`. Only the §19.6 cut-combination
  (∀-family `α` + ∃-side `γ`) is an addition, and cut-elim performs finitely many such reductions (cut
  rank `c` finite), so `norm` grows by a *bounded* amount ⇒ choosing `k` large enough at embedding (M4)
  absorbs it. **The precise bookkeeping (how Towsner threads `τ`/`k` through §19; the exact growth bound)
  needs the paper — see `ON-LINE-REQUEST.md`.** Do NOT claim cut-elim closed until this is pinned down.
- Helpers banked this lap: `lt_osucc`, `add_lt_add_left_NF`, `le_add_left_NF`, `norm_omegaPow`. Still
  need (build with §19.6): `norm (α+γ) ≤ norm α + norm γ`, `norm (osucc δ) ≤ norm δ + 1`.
(`Ordinal.nadd`/`♯` absent in mathlib v4.31.0; ordinary `+`/`osucc` with slack, as `src/Zinfty.lean` did
— note natural sum would NOT help here, it merges coefficients the same way.)

### Step 2 — M4 embedding `PA ⊢ φ ⟹ Zᵏ ⊢^{α,k}_c φ`  (UNBLOCKED — independent of the §19.6 τ/k question)
α<ε₀, finite c (Towsner §16/§18). **Reconnaissance done (lap 6).** Foundation's proof object is
`Derivation (𝓢 : Schema L) : Sequent L → Type` in `Foundation/FirstOrder/Basic/Calculus.lean:20`
(`Sequent L = List (SyntacticFormula L)`, one-sided/Tait). Constructors + their `Zᵏ` image (the
embedding inducts on this `Derivation`):
- `axm : φ ∈ 𝓢` — **the PA-axiom case, the crux.** `Zᵏ` must derive each PA axiom at a bounded `(α,k)`:
  Lemma 16.1 (true Δ₀/atomic axioms via the `trueRel`/`trueNrel` rules, low bound) + Cor 16.6 (the
  **induction-scheme** instances at bound `ω·4 # 2rk(φ) # 8` — the real work; `∀`-closure via the
  ω-rule). This is the bulk of M4.
- `axL r v`→`Zk.axL`; `verum`→`Zk.verumR`; `or`→`Zk.orI`; `and`→`Zk.andI`; `wk`→`Zk.wk`;
  `cut`→`Zk.cut` (finitely many cut formulas of bounded complexity ⇒ finite cut rank `c`).
- `all` (eigenvariable `φ.free`) → **`Zk.allω`** (finitary ∀ becomes the ω-rule: derive `φ/[nm n]` for
  every `n`). 2nd deep case: needs **derivation-substitution** — specialize the single eigenvariable
  premise (`φ.free :: Γ⁺`, fresh free var) to each numeral `n` (Foundation `Rew`/free-var substitution
  on a whole `Derivation`). The uniform eigenvariable proof instantiates to all `ℕ`-many ω-rule premises.
- `exs t` (witness *term* `t`) → **`Zk.exI`** with numeral `⟦t⟧ℕ`, needing the **witness bound**
  `⟦t⟧ℕ ≤ hardy α k` (Towsner picks `k` large enough — where the bound is established).
Two wrinkles: (a) Foundation sequents are **`List`**, `Zᵏ` uses **`Finset`** — need a list→finset bridge.
(b) Confirm how `𝗣𝗔 ⊢ ↑goodsteinSentence` (the headline's `LO.Entailment`) connects to `Derivation
𝗣𝗔-schema` (the `OneSided` instance at `Calculus.lean:31` is `Derivation`). The structural map is
clean — the depth is all in `axm`. Foundation-heavy; not Aristotle-friendly.

### Step 3 — cut-elim with `k`
Redo `src/Zinfty.lean` §19 tracking the witness bound. The inversions/reductions *strategy* ports; the
new content is threading `h_{ω^α}(k)` through §19.6 (∀/∃ reduction) and confirming `ω^α < ε₀` keeps the
final cut-free bound `< ε₀` (so domination still bites). No deep math doubt (literature-standard,
host-verified) — formalization labor.

### Step 4 — subformula bridge (the clean small connector)
A cut-free `Zᵏ`-derivation of `{gAll}` contains only subformulas of `gAll` closed under numeral
substitution = exactly `{gAll, gEx n, atom m n}` = the `GForm` fragment, so it **is** a `B`-derivation
⇒ `lowerBound_hardy_selfcontained` refutes it. Needs: a subformula-closure lemma for the ω-calculus
(structural induction over `Deriv`, ω-rule = closure under numeral substitution) + the `GForm ↪ ℒₒᵣ`
encoding identification. Reuses M6 as-is.

### M7a — the language gap (the other hard girder; Towsner Remark 10.3)
`goodsteinSentence = ∀⁰ (codeOfREPred goodsteinTerminates)` is an **opaque Σ₁ blob**, NOT the
transparent `∀x∃y g_y(x)=0` that step 4 needs. Build a transparent Π₂ `gAllReal` (arithmetize
`goodsteinSeq` as a real `ℒₒᵣ` formula — Foundation's Σ₁/representability tools) and prove
`𝗣𝗔 ⊢ goodsteinSentence ↔ gAllReal`, gated by `Bridge.lean`'s spec so faithfulness can't regress.
Then the subformula bridge runs on `gAllReal`.

## ✅ LAP-5 — O0 done + the I∀ frontier RESOLVED; TOP PRIORITY is now O0′ (port `Hdom`)
The witness-bounded calculus `B` is now built over `ONote` with the **concrete** Hardy hierarchy
(`src/GoodsteinPA/Hardy.lean`, ported from Track-1). `wip/LowerBoundHardy.lean` proves, axiom-clean:
the ∃-fragment lower bound (`lowerBound_existential_hardy`, zero abstract hyps), `k`-monotonicity,
**∀-inversion** (`B.allInv`), and the **full Thm 17.1 modulo domination** (`lowerBound_hardy`). The
lap-4 "accumulating existentials" wall is resolved by inverting `gAll` away rather than carrying it
(see `ANALYSIS-2026-06-22-bounding-resolution.md`).

### O0′ (TOP) — discharge `Hdom : ∃ x, hardy α (max k x) < G x`
`G = goodsteinLength`; Goodstein defs (`bump`/`base`/`goodsteinSeq`) are **byte-identical** to Track-1.
Port `~/src/lean-formalizations Logic/Goodstein/{Length,Domination,DominationOmega,TowerDomination,
GrowthStatement,DominationCorollary,GoodsteinLike,DominationBaseCases}.lean` →
`goodsteinLength_dominates_fastGrowing {o}(ho:o.NF) : ∃ N, ∀ m≥N, fastGrowing o m ≤ goodsteinLength m+2`.
Chain `hardy α m ≤ fastGrowing α m` (`hardy_le_fastGrowing`) + identify `G = goodsteinLength`. **Bridge
the `+2` to strict `<`** (the one genuinely-open bit; fastGrowing's gap over hardy swallows +2 for
large m — good Aristotle target). Then `lowerBound_hardy` becomes a self-contained Thm 17.1. NB the
port carries documented `native_decide` finite-base-case axioms.

<details><summary>Superseded lap-4 O0 (re-architect on the witness-bounded calculus) — DONE</summary>

## ⚠️ TOP PRIORITY (lap 4) — O0: re-architect on the witness-bounded calculus
**Finding (machine-checked, axiom-clean, `wip/WitnessBound.lean`):** the completed M5 cut-elimination
in `src/Zinfty.lean` is for a calculus with an **unbounded `∃`-witness** and **no numeric index `k`**.
That calculus cannot reach the headline — `unbounded_proves_goodstein` derives the Goodstein sentence
cut-free at ordinal 2, so Towsner's lower bound (17.1) is FALSE for it. The headline needs the
**witness-bounded, Hardy-indexed `(α,k)` calculus** (Towsner §15), where `∃` carries `v ≤ h α k`,
`True` carries `τ α < k`, and `∀`'s premises use `max k n`. See `STATUS.md` lap-4 finding.

Attack paths (hardest-first; the crux is now the lower bound + the `k`-tracking cut-elim):
1. **Finish the lower bound (M6 / Thm 17.1).** `wip/WitnessBound.lean` has the calculus `B` and the
   `∀`-free fragment proved (`lowerBound_existential`). The remaining frontier is the `gAll`/`I∀`
   case with *accumulating* existentials — Towsner's stated invariant looks insufficient there
   (see `ON-LINE-REQUEST.md`). Either crack the refined invariant (likely a single-ordinal
   `H`-controlled measure, Buchholz style) or get it from the literature, then discharge the abstract
   Hardy hypotheses `Hmono`/`Hdom`/`HG` from a real `h_α`/`τ`/`G` (mathlib `ONote.fastGrowing`?).
2. **Retrofit `k` into cut-elimination.** Redo `src/Zinfty.lean`'s inversions/reductions tracking the
   numeric bound `k` (the *strategy* ports; only the bookkeeping changes). Needed so the cut-free
   output of M5 still carries the `(α,k)` bound that 17.1 refutes.
3. **Decide architecture:** Towsner two-index `(α,k)` vs. Buchholz single-ordinal `H`-controlled
   derivations. The latter may formalize more cleanly (one well-founded measure, standard boundedness
   theorem). Resolve via `ON-LINE-REQUEST.md` before sinking the cut-elim redo.

Plus the **PA↔PA⁺ language gap**: our headline is real-`ℒₒᵣ` PA with an opaque Σ₁ `goodsteinSentence`,
not Towsner's extended-language `∀x∃y g_y(x)=0`; the arithmetization bridge Towsner skips (Remark
10.3) is a separate deep girder (M7-adjacent). Route A (via `Con(PA)`, O1) stays entirely in real PA
and sidesteps this — re-evaluate Route A vs Route B in light of the language gap.
</details>

## Open obligations (toward a clean headline)

### O1 — `Reduction.goodstein_implies_consistency` (Route A girder) — `sorry`
`𝗣𝗔 ⊢ γ → 𝗣𝗔 ⊢ Con(𝗣𝗔)`. The deep ordinal-analysis content via Con(PA).
Attack paths:
1. **Gentzen `TI(ε₀) ⊢ Con(𝗣𝗔)` + `γ ⟹ TI(ε₀)`** — the classic route; needs `PA_∞`
   cut-elimination (same `Z_∞` machinery as Route B) plus the Con(PA) lower bound. Reuses
   Foundation's Gödel II downstream. (Buchholz `on-gentzens-first-consistency-proof`.)
2. **Drop Route A entirely for Route B** (recommended) — Towsner shows `𝗣𝗔 ⊬ γ` directly without
   Con(PA); then `goodstein_implies_consistency` becomes unnecessary (leave it as a documented,
   never-used alternative). The headline is discharged via O2's chain instead.
3. Partial: keep the lemma but prove the *easier* converse direction / a weaker reflection
   principle first as warmup, to exercise Foundation's provability API (`⊢`, `Con`, D1–D3).

### O2 — the Phase-2 girder (Route B, Towsner) — milestones M3…M7 in `PHASE2-DECOMPOSITION.md`

**✅ M3 (Z_∞ calculus) + M5 (cut-elimination) COMPLETE & axiom-clean** in
`src/GoodsteinPA/Zinfty.lean` (promoted from `wip/`, 0 sorries, `#print axioms` = trust base only,
2026-06-22 lap 3). The whole Towsner §19 is machine-checked: inversions 19.2–19.4, cut reductions
19.5 (`cutReduceConj/Disj`) + 19.6 (`cutReduceAll`), atomic/⊥ cuts (`atomCut`/`removeFalsum`, **no
truth layer needed** — set sequents dissolve them), `cutElimStep` (19.7), `cutElim` (19.9). Key
findings: `Ordinal.nadd` ABSENT in mathlib v4.31.0 → ordinary `+` with `+1` slack (bounded below
`ω^(·+1)` by additive principality); the Hardy `k` index was NOT needed for cut-elim (pure Schütte
`(α,c)` suffices — it's a §17 device); `exI` restricted to numeral witnesses.

**NEXT (hardest-first): M4 — the embedding `PA⁺ ↪ Z_∞`** (Towsner §16 Thm 16.7 / §18 Thm 18.1). A
`PA⁺` proof of `φ` yields `∃ α<ε₀, ∃ k c, Z_∞ ⊢^{α}_c φ`, finite `c` (finitely many induction
instances ⇒ finitely many finite-rank cuts — the hinge of the whole argument). Sub-targets:
M4.1 (Lemma 16.1, true universal sentences derivable at finite bound), M4.2 (Lemma 16.5/Cor 16.6,
induction axioms at bound `ω·4 # 2rk(φ) # 8`), M4.3 (Thm 16.7, induct over a Hilbert-style proof;
reuse Foundation's finitary `Derivation`, map `∀`→ω-rule). M6 (Hardy lower bound, §17) is
**independent and parallelizable** (M6.1–M6.3 overlap Track 1 `Logic/FastGrowing`; M6.4 = Thm 17.1
is new and likely DOES need the Hardy `k` threaded through a cut-free `Provable₀`).

<details><summary>Superseded lap-2 status (M5 was one open leaf `cutElimStep`)</summary>
Done and **machine-checked** (`lake env lean wip/ZinftyF.lean`, only `cutElimStep` sorry):
- The `Z_∞` calculus `inductive Deriv` over `SyntacticFormula ℒₒᵣ`, **Finset sequents** (set-based,
  per Towsner ⇒ contraction is FREE, no `contr` rule), ω-rule `allω`, ordinal bound `o`, `ℕ∞`
  cut rank `cr`. The `ℕ∞/⊤` blocker is **gone**: `complexity : Form → ℕ` is finite.
- Full predicate-level inference API: `axL/verumR/andI/orI/exI/allω/cut/mono/weakening/cast`,
  contraction free.
- **All three inversion lemmas PROVED** (the syntactic content of cut-elimination):
  `orInvAux`/`Provable.orInv` (§19.2 ∨), `andInvAux`/`Provable.andInvL`/`.andInvR` (§19.3 ∧),
  `allInvAux`/`Provable.allInv` (§19.4 ω/∀). Each by structural induction on `Deriv`, all 8 cases,
  preserving ordinal bound and cut rank.
- `cutElim` (Thm 19.9) reduced to the single open leaf `cutElimStep` (Thm 19.7).

**NEXT (hardest-first): the cut-REDUCTION lemma (Towsner §19.5–19.7), the ordinal-arithmetic
heart of `cutElimStep`.** With all inversions in hand, the reduction lemma is: a top-level cut on a
formula of complexity `= c` between two `Provable _ c` derivations can be replaced by a cut-free-at-
rank-`c` derivation with the ordinal bounds *added* (not `max+1`). The principal-formula reduction
uses the inversions to push the cut to the immediate subformulas (∨/∧ → smaller-complexity cut;
ω/∀ → instantiate at the ∃-witness numeral). Then `cutElimStep` does the transfinite induction over
the derivation eliminating all rank-`c` cuts, raising `α ↦ ω^α`. Likely needs a numeric/Hardy `k`
parameter re-added to `Provable` (Towsner threads `h_{ω^α}(k)` through 19.6/19.7) — assess whether
the `(α,c)` indexing suffices first.

Attack paths:
1. **Continue the `wip/Zinfty.lean` prototype** (E2 encoding — *compiles*). Next: (a) connect
   `AForm` to a faithful arithmetic formula with a real free-variable/substitution layer (replace
   the `ℕ → AForm` family with a single body + numeral substitution), so `rk` is genuinely
   finite; (b) state M3.3 bound-monotonicity lemmas; (c) state M4 embedding + M5 cut-elimination
   theorems as disclosed `sorry`s. Bank each as it typechecks; promote to `src/` when green.
2. **Develop M6 (Hardy domination) via Track 1.** `~/src/lean-formalizations` `Logic/FastGrowing`
   is building `h_α`, monotonicity, and Goodstein-length domination on mathlib's
   `ONote.fastGrowing`. Reuse those for M6.1–M6.3; only M6.4 (Thm 17.1, the cut-free lower bound)
   is new here. (Does NOT block M3–M5 — parallelizable.)
3. **Tackle cut-elimination (M5) on the prototype first**, before the embedding — it is the
   self-contained heart (Towsner §19). **STATUS: M5 is now structured down to ONE leaf.**
   `wip/Zinfty.lean` has `Provable.cutElim` (Thm 19.9, full elimination) *proved* by induction on
   cut rank, reducing entirely to the single open lemma **`Provable.cutElimStep`** (Thm 19.7, one
   level). So the next concrete target is exactly `cutElimStep` = §19 inversions 19.2–19.4 +
   reductions 19.5–19.6 + the principal-`Cut`-on-rank-`c` case. Proving it makes the whole
   cut-elimination machine-checked (mod the embedding M4 and lower bound M6.4). NOTE: `cutElimStep`
   likely needs the numeric/Hardy `k` bound that `Provable` currently elides — re-add a `k : ℕ`
   index to `Provable`/`Deriv.o` first (it threads the `h_{ω^α}(k)` bound through 19.6/19.7).
   *(Resolved lap 3: the `k` index turned out NOT to be needed for cut-elimination.)*
</details>

### O2′ — M4 DESIGN DECISION (scouted lap 3, execute lap 4) ⭐
The embedding needs Z_∞ to derive PA's **true defining axioms** (e.g. `n+(m+1)=(n+m)+1`), which the
current calculus CANNOT: `axL` is the clash-based identity (`rel r v ∧ nrel r v ∈ Γ`) and `verumR`
is only `⊤`. Towsner's "True" rule is a **truth-based atomic axiom**. So M4 requires extending the
calculus. Concrete plan:
1. **Atomic truth predicate** — reuse Foundation `Semiformula.Evalm ℕ` (the `standardModel`
   instance for `ℒₒᵣ` over `ℕ`; `=`/`<` decidable). For embedding-substituted formulas (free vars
   replaced by numerals) truth is assignment-independent. **VALIDATED (lap 3)** — this typechecks
   (imports `Foundation.FirstOrder.Arithmetic.Basic.Model`):
   ```
   noncomputable def atomTrue (φ : SyntacticFormula ℒₒᵣ) : Prop :=
     Semiformula.Evalm ℕ (fun _ => 0) (fun _ => 0) φ
   ```
   (`Foundation/.../Semantics/Semantics.lean:241`, `Arithmetic/Basic/Model.lean:25`.)
2. **Add `trueAtom` constructor** to `Deriv`: `(φ : Form) → (φ atomic) → Evalm ℕ … φ → φ ∈ Γ →
   Deriv Γ`, with `o = 0`, `cr = 0`. ⚠️ **This touches the completed cut-elimination**: every
   induction (`orInvAux`, `allInvAux`, `andInvAux`, `cutReduceAllAux`, `atomCutAux`,
   `removeFalsumAux`, `cutElimStepAux`) gains one new leaf case — mostly trivial (like `verumR`),
   EXCEPT `atomCutAux`: a `trueAtom` on the cut atom `rel r v` means `rel r v` is true ⇒ `nrel r v`
   is false ⇒ must remove it from the other premise. So `atomCut` needs a **truth-based false-atomic
   removal** (the genuine §19.2 content, now unavoidable, but only for atomics — decidable ℕ
   arithmetic). Do this extension on a `wip/` copy first; re-green; re-promote.
3. **ε₀** is `ε_ 0` in `Mathlib.SetTheory.Ordinal.Veblen` (first fixed point of `ω^·`); `omegaTower
   c α < ε₀` for `α < ε₀` is the closure fact M5.4/M7 need (ε₀ closed under `ω^·`).
4. Then M4.1 (Lemma 16.1) → M4.2 (Cor 16.6) → M4.3 (Thm 16.7), inducting over a `Peano`-proof
   (`𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ`), reusing Foundation's finitary `Derivation`.

**Caveat on the clean state:** cut-elimination is currently truth-free and axiom-clean precisely
because of clash-`axL`. Adding `trueAtom` re-introduces a (decidable, atomic-only) truth layer.
This is the standard Schütte setup and is correct; just do it carefully so the §19 proofs stay green.

### O3 — `PA_delta1Definable : 𝗣𝗔.Δ₁` (Foundation axiom) — only on Route A
Needed to *state* Gödel II for `𝗣𝗔`; Foundation axiomatizes it (TODO in
`Incompleteness/Examples.lean`). Route B avoids it. Attack paths:
1. **Avoid** — go Route B (O1 path 2); the axiom never enters the headline profile.
2. Discharge it: construct the Δ₁-definition of PA's axiom set (PA⁻ + induction scheme) in
   Foundation's `Theory.Δ₁` framework and prove `isDelta1`. Deep arithmetization; multi-lap.
3. Upstream: check whether a newer Foundation rev proves it (the TODO may get filled upstream);
   file an `ON-LINE-REQUEST.md` to check the latest Foundation `Incompleteness/Examples.lean`.

**UPDATE (lap 6, cross-session news):** a separate session (`~/src/Foundation-delta1-burndown`,
branch `feat/induction-scheme-delta1`) is **actively discharging** both `PA_delta1Definable` and
`ISigma1_delta1Definable` (proving them in `InductionSchemeDelta1.lean`; reduced `PA.Δ₁` to 3 isolated
obligations, build green, ~1–2 laps to PA-complete per that session). So path 3 is in progress
**upstream** — do NOT duplicate it here. When it lands and our Foundation pin bumps to include it,
Route A's `not_proves_of_implies_consistency` becomes axiom-clean (no `PA_delta1Definable`). This is a
**fallback de-risk only**: our headline stays on **Route B** (Towsner direct, avoids `Con(PA)` and this
axiom). `goodstein_implies_consistency` (the `TI(ε₀)⊢Con(PA)`-inside-PA girder of Route A) remains
deeply blocked regardless, so the Δ₁ news doesn't make Route A the preferred path.

## Done — lap 4 (2026-06-22)
- **Witness-bound architectural finding** (machine-checked, axiom-clean, `wip/WitnessBound.lean`):
  the `src/Zinfty.lean` `(α,c)` cut-elimination is OFF the headline path (its unbounded `∃` makes the
  lower bound false). Built the corrected witness-bounded calculus `B`; proved the existential-fragment
  lower bound (`lowerBound_existential[_real]`) grounded against the real `G`; decomposed the full
  Thm 17.1 to the single `bounding` frontier (`True`/`W`/`I∃` cases machine-verified via `sat_mono_ord`,
  `I∀` case the literature-gated frontier; `lowerBound` contradiction-extraction real). Goodstein-side
  grounded: `G`, `goodstein_zero_succ`/`_mono`, `atomTrue_iff_G_le`. Filed `ON-LINE-REQUEST.md` for the
  rigorous `bounding` invariant + architecture (Towsner `(α,k)` vs Buchholz `H`-controlled).
- Next deep brick (architecture-independent, but gated on the notation/architecture decision):
  the **Hardy / fast-growing hierarchy + τ-controlled monotonicity** to discharge `Hmono`/`Hmono_n`,
  and **Goodstein domination** (Towsner §5–§9) to discharge `Hdom`. mathlib `ONote.fastGrowing`
  exists but has NO growth lemmas (deliberately minimal).
  - **STARTED** (`wip/FastGrowing.lean`, axiom-clean): `fastGrowing_id_le` — `n ≤ fastGrowing o n`
    (the inflationary half, which IS separable from ordinal-monotonicity: successor case via
    iterating a `≥id` map, limit case via the smaller-ordinal IH).
  - **Confirmed entangled:** *numeric* monotonicity (`Hmono_n` analogue) of `fastGrowing` — its
    limit case `fastGrowing (f m) m ≤ fastGrowing (f m') m` needs *ordinal* monotonicity at fixed `n`,
    which is the τ-subtle one (false for small `n` without the coefficient control — Towsner §8). So
    `Hmono`/`Hmono_n` for the real hierarchy genuinely need the τ machinery; not a quick brick.

## Done — lap 1
- M1: `Encoding.goodsteinTerminates_re` proved (`Computability.lean`: `primrec_natLog`,
  `primrec_bump`, `primrec_goodsteinSeq`). Phase 0 axiom-clean.
- M2: `Reduction.lean` — Gödel II hook + meta-reduction (axiom-clean mod `PA_delta1Definable`).
- Phase 2: `PHASE2-DECOMPOSITION.md` (Towsner-grounded ladder) + `wip/Zinfty.lean` (E2 encoding
  prototype — compiles: ω-rule inductive, ordinal/cut-rank measures, bound-domination lemma,
  `Provable.mono`/`.weakening`, and the **proved predicate-level inference API** `Provable.orI`,
  `.exI`, `.allI` — the ω-rule with the supremum ordinal bound, machine-checked against the
  `Deriv` measures via `Classical.choice`).

## ⭐ KEY FINDING (2026-06-22, end of lap) — build `Z_∞` ON Foundation's Tait calculus
Foundation **already has a finitary Tait one-sided FO sequent calculus**:
`FirstOrder/Basic/Calculus.lean` — `inductive Derivation (𝓢 : Schema L) : Sequent L → Type`
with constructors `axL, verum, or, and, all, exs, wk, cut` and a `height` measure, over the *real*
`SyntacticFormula ℒₒᵣ` (which already carries free variables, substitution, negation, rank).
Plus `FirstOrder/Hauptsatz.lean` (finitary cut-elimination). **There is NO infinitary calculus /
ω-rule / `PA_∞`** (confirmed by grep — only finitary Tait + Hauptsatz).

**Consequence — revise M3.1:** do NOT continue the standalone `wip/Zinfty.lean` `AForm`. Instead
define `Z_∞` as a new inductive **over Foundation's `SyntacticFormula ℒₒᵣ`/`Sequent`**, replacing
the finitary `all` (eigenvariable, one premise, `ℕ` height) with the **ω-rule** (`all` taking an
`ℕ`-indexed family `n ↦ φ[x ↦ numeral n]`, `Ordinal` height). This:
- **kills the `AForm` substitution-layer prerequisite** — Foundation's formula substitution +
  `rk` are reused, so `rk φ` is already finite and `cut`/`cutElimStep` become directly stateable;
- **shrinks M4 (embedding):** a PA proof already yields a Foundation *finitary* `Derivation`
  (via Hauptsatz machinery); M4 becomes "finitary `Derivation` ↪ `Z_∞`" (map each rule across,
  ∀→ω-rule) instead of re-deriving from `True`/`Lemma 16.1` by hand;
- **makes M7 natural:** everything is over real `ℒₒᵣ` formulas, so connecting to our
  `goodsteinSentence` is a formula-level statement, not a re-encoding.
The `wip/Zinfty.lean` prototype keeps its value as the *proof that the ordinal/ω-rule measures
work* (the encoding-feasibility result) — port its `o`/`cr`/`allI`/`cutElim` skeleton onto
Foundation's `Derivation`-shaped inductive. **This is the recommended first action next lap**
(read `FirstOrder/Basic/Calculus.lean` + `Hauptsatz.lean` first).

## Design note — `Provable.cut` + the `ℕ∞` cut-rank (next lap, read before refactoring)
`cr : Deriv Γ → ℕ∞` (cut rank can be `⊤` for pathological infinite families). A predicate-level
`Provable.cut` is the one rule still missing: from `Provable α c (φ ::ₘ Γ)` and
`Provable β c (φ.neg ::ₘ Γ)` it should give `Provable (max α β + 1) c' (Γ)` where
`c' ≥ rk φ + 1`. But `rk φ : ℕ∞` may be `⊤`, so you can't pick a finite `c' : ℕ` in general —
`Provable`'s `c : ℕ`. **Fix:** when `AForm` gets the real free-variable + numeral-substitution
layer (the M3.1 refinement), `rk φ` becomes provably finite (`rk φ ≠ ⊤`) for genuine formulas, so
`Provable.cut` and the Hardy-bounded `cutElimStep` both become stateable with finite `c`. So the
substitution-layer refactor is a prerequisite for *both* `cut` and `cutElimStep` — do it first.

## Gotcha noted (for the corpus)
For `Ordinal`, `add_le_add_right h c` elaborates to `c + a ≤ c + b` (adds on the *left*) — use
`add_le_add h le_rfl` to get `a + 1 ≤ b + 1` from `a ≤ b`. `gcongr` on `⨆`-bounds spawns a
`BddAbove (Set.range …)` side-goal (discharge with `Ordinal.bddAbove_range`).

## lap 48 — internal Cor 3.4 bricks landed; MinExpGe assembly remaining (2026-06-23)
DONE (axiom-clean, green): `icmp_iadd_clean`/`_boundary` (within+boundary unified), `iC_iadd_clean`
(C-split = Grz.C_add_clean), `iAbove_iomul` (MinExpGe step: `iAbove e0 a → iAbove (1+e0)(ω·a)`),
`iAbove_zero_iomul` (MinExpGe base: `iAbove 0 (ω·a)`). Plus general `icmp_swap` antisymmetry infra
in InternalONote.

REMAINING for the `iAbove (ocExp g) (ibigMul (l+1) β)` clean-condition (3 attack paths):
1. **Meta-iterate (recommended).** By `induction k:ℕ`: `iAbove (oadd1iter k 0) (ibigMul (k+1) β)`
   from base `iAbove_zero_iomul` + step `iAbove_iomul` (needs `isNF_ibigMul` for the NF arg, exists).
   `oadd1iter k = (iadd (ocOadd 0 1 0))^[k]`. Then identify `oadd1iter k 0 = ocOadd 0 k 0` (finite k)
   via `iadd_one_zero`/`iadd_one_fin`, and weaken the threshold `ofin l → ocExp g` (g < ω^(l+1) ⟹
   ocExp g ⪯ ofin l).
2. **Threshold weakening** is the one piece needing care: `iAbove (ofin l) a → (ocExp g ⪯ ofin l) →
   iAbove (ocExp g) a`. Since g's exps are FINITE codes (ig0/iblk have finite ocExp), the spine-vs-
   threshold comparisons are all finite (cmpV on coeffs) OR infinite-head-vs-finite
   (`icmp_infHead_finHead`) — provable WITHOUT general `icmp` transitivity. State as
   `icmp_spine_finThresh_mono : icmp s (ofin (l+1)) = 2 → j ≤ l → icmp s (ofin j) = 2` by cases on s.
3. Alternatively prove general `icmp_trans` (≺ transitive) once — heavier but unblocks everything.

Then assemble `icorAlpha` (mirror `Grz.corAlpha`): C-bound (`iC_iadd_clean`+`iC_ibigMul_le`+`iC` of g),
within (`icmp_iadd_clean` with `icmp a a`=1 via the same-lead), boundary (`icmp_iadd_clean_boundary`
+ `icmp_ibigMul` lifting β-descent). Feeds `DescentSemantic.nonterminating_of_xDescent`.
