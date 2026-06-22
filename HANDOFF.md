# HANDOFF — 2026-06-22 (lap 15)

> **Branch** `plan` · build **green** (`lake build GoodsteinPA`, 1265 jobs) · headline
> `peano_not_proves_goodstein` = honest `sorry` (anti-fraud guard intact, untouched).
> **Lap 15 (review + grind) CLOSED C₁ AND D, axiom-clean.** The `XFreeAx`-preserving cut-elimination
> (`src/GoodsteinPA/XFreeCutElim.lean`, 1290 lines) is COMPLETE, and the Thm-5.6 *tail*
> `Z∞ ⊢ TI (any cut rank, XFreeAx) ⟹ ‖≺‖ ≤ 2^(ω_c^α)` is assembled and `[propext,choice,Quot.sound]`.
> **The ONLY remaining gap to Thm 5.6 (= `PA ⊬ TI(ε₀)`) is C₂ (`embedC` over LX).** Then E + F.

## Lap-15 review finding (validated the lap-14 design — see STATUS "What's happened")
The lap-14 cr=0 design was feared obstructed (X-atomic cuts seemingly un-eliminable while preserving
`XFreeAx`). **Resolved by reading `atomCutAux`:** our `Provable.axL` is the *same-atom* EM axiom
`{Xs,¬Xs}`, so X-atomic cuts close by **set idempotence** (no truth), and the truth-surgery branch
(`removeFalseLit`) is **vacuous under `XFreeAx`** (it needs an X-`axTrue` leaf). So C₁ is feasible as
written — confirmed by completing it.

## ✅ Lap-15 deliverable: C₁ + D (`src/GoodsteinPA/XFreeCutElim.lean`, axiom-clean)
The whole §19 cut-elimination, ported to a cut-rank-carrying `XFreeAx`-tracking twin
`PXFc α c Γ := ∃ d : Deriv Γ, d.o ≤ α ∧ d.cr ≤ c ∧ XFreeAx d` (generalises lap-14 `PXF = PXFc · 0`):
- **Builders** `PXFc.{mono,weakening,cast,axL,axTrue,verumR,andI,orI,exI,allω,cut,contr}` + bridges
  `PXF.toPXFc`/`PXFc.toPXF`.
- **Inversions at cut rank ≤ c** (real `cut` case now, not the lap-14 vacuous one): `orInvAux_x`,
  `andInvAux_x` (+`PXFc.andInvL/R`), `allInvAux_x` (+`PXFc.{orInv,allInv}`).
- **Cut reductions** `PXFc.{cutReduceConj,cutReduceDisj,cutReduceAllAux,cutReduceAll}` (§19.5/19.6).
- **Truth layer** `PXFc.{removeFalseLitAux,removeFalsumAux,removeFalsum,atomCutAux,atomCut}`. Key:
  `removeFalseLitAux` carries `Sum.isLeft r₀ = true` (X-free removed atom ⟹ X-free `axTrue` leaves);
  `atomCutAux`'s truth branch extracts that via **`xfree_transport`** (an `axTrue` leaf equal to the cut
  atom is X-free, so the cut atom is X-free; at an X-atom cut the branch is vacuous).
- **Assembly** `PXFc.{cutElimPrincipal,cutElimStepAux,cutElimStep,cutElim}` (§19.7/19.9):
  `cutElim : PXFc α c Γ → PXFc (omegaTower c α) 0 Γ`. **C₁.**
- **D** `orderType_le_of_TIprovable` = `PXFc.cutElim ∘ orderType_le_of_TIderiv` (corollary B):
  `PXFc α c {TI prec} ⟹ ‖≺‖ ≤ 2^(ω_c^α)` (given the legit seam hyps `hprec`/`hprecXPos`). **Thm 5.6 tail.**

## 🎯 Critical path to the headline (★ = real walls)
| Step | What | Status |
|---|---|---|
| **A** Boundedness Thm 5.4 | crux | ✅ DONE lap 14, axiom-clean |
| **B** Corollary `‖≺‖≤2^β` | invert TI + Boundedness | ✅ DONE lap 14, axiom-clean |
| **C₁** `XFreeAx` cutElim → cr=0 | the big §19 port | ✅ **DONE lap 15, axiom-clean** |
| **D** Thm 5.6 tail | C₁ ∘ B | ✅ **DONE lap 15** (`orderType_le_of_TIprovable`) |
| **C₂** `embedC` over `LX` | the one remaining connective gap | not started — **NEXT** |
| **E** Goodstein⟹TI_≺(X) bridge | Kirby–Paris; reuse Phase-0 CNF-ε₀ | not started |
| **F ★** Arithmetization seam | ℒₒᵣ-def ε₀ order, `‖≺‖=ε₀`, discharge `hprec`/`hprecXPos` | not started — 2nd hard wall |
| **G** Final assembly | chain + `#print axioms` clean | not started |

## NEXT (lap 16): C₂ — `embedC` over generic `LX`, producing `PXFc α c {TI prec}`
Port `src/Embedding.lean`'s `embedC` (over `ℒₒᵣ`, calculus `ZinftyF`) to the generic `ZinftyGen`
calculus over `LX`, tracking `XFreeAx` (so the output is a `PXFc`). The structural cases are mechanical
(`{L}`-generalise like M5/`ZinftyGen`). **CRITICAL faithfulness (lap-14 finding, still in force):**
- **`𝗣𝗔⁻` X-free axioms** → `provable_true` (ω-completeness, `axTrue` on X-free atoms — `XFreeAx`-safe).
- **X-induction scheme `Ind_φ` (φ an X-formula)** → MUST go via the **meta-induction tower of `cut`s on
  `φ(i)` + `provable_em` base/step** (Buchholz Thm 5.5), NOT `provable_true` (would `axTrue` a lone
  X-atom ⟹ break `XFreeAx`). `provable_em` for X-atoms already uses `Deriv.axL` (the X-pair, no truth).
  The lap-10 HANDOFF/PENDING has the worked meta-induction; port THAT for the X-case.
- `provable_em_cong_gen` (`exs`/`exI_closed`) `axTrue`s on `ψ/[s]`: safe iff `ψ` X-free — check the TI
  embedding never value-congruences an X-atom (likely fine: `prec` X-free, witnesses ℒₒᵣ terms).
Deliverable: `embedC_LX : (Z ⊢ TI(X)) → ∃ c, ∀ e, ∃ α, PXFc α c ({TI prec}.image (asg e ▹))` (or the
closed form). Then **D fires** ⟹ Thm 5.6 ⟹ `PA ⊬ TI(ε₀)` modulo F.

## Notes
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`, headline `sorry`.
- **Aristotle:** idle (jobs all IDLE). Good C₂ target: a self-contained `provable_em`-over-LX X-atom
  case, or the meta-induction `cut`-tower lemma (inline defs). No open `ON-LINE-REQUEST.md`.
- **Banked off-path (do NOT resume):** witness-bounded `wip/` calculi; `Zᵏ`/M6.
- Build: `lake build GoodsteinPA` (1265). See `STATUS.md` for the full overview + axiom ledger.
