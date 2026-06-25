# Lap 92 — DIRECTION DECISION: Path X (finish the finitary arithmetization) is favored

After the lap-92 reflection + correction, deeper analysis tips the Path X vs Path C decision toward
**Path X** (stay finitary; complete the eigenvariable-regularity tracking). Reasoning + the concrete,
de-risked plan.

## Why Path X over Path C (the ω-rule pivot)

1. **The ω-rule precedents are META-level, not arithmetized.** `Zinfty.lean` (the repo's axiom-clean
   ω-rule engine) and Bryce–Goré's Coq `PA_omega.v` both represent the ω-rule's infinitely-many premises
   as a **native function** (`∀ c_term, …` / a Lean `ℕ → Deriv`). That is free at the meta level. The
   **arithmetized** ω-rule (premises as a `Σ₁` recursive notation over codes `d : V`, Buchholz §6 `Z*`)
   is a genuinely different, **un-precedented, hard** object — and it is *exactly* the part the repo
   deliberately avoided by choosing the finitary system. So Path C's "follow the proven design" is partly
   illusory: the proven designs don't de-risk the arithmetized ω-rule.

2. **Path X completes invested infrastructure with standard bookkeeping.** The 7.3k-line `InternalZ` +
   the proven `zsubst` stack + the axiom-clean `iord` descent engine all stay. The remaining gap is the
   classical eigenvariable-regularity condition — standard proof theory, now shown tractable below.

3. **O2 is already done** (banked this lap: `ZDerivation_zsubst_zIall_premise` /
   `_zInd_premise1`). The reformulated `ZDerivation_zsubst` needs the bound only at eigenvariable nodes;
   the zK case transfers cleanly via the *positive* `iperm_tp_zsubst`/`isChainInf_zsubst` (criticality —
   the only delicate conjunct — is no longer in the live `zKValidF`). The Zsubst.lean:649 docstring
   ("needs `a ∉ FV(s)`") is **stale** (it described the old `zKValid`).

## The key insight that makes O1 tractable AND maintainable: `maxEigen` is `zsubst`-invariant

`zsubst d a t` (closed `t`) **preserves every eigenvariable index** — `zsubst_zIall` keeps the binder
`e`, `zsubst_zInd` keeps `π₁ at'` (verified). Therefore a freshness invariant phrased in terms of
**eigenvariable indices** (not derivation codes) is **stable under reduction**: the code-bound `d ≤ a`
is NOT preserved by `red`, but `maxEigen(premise) < eigenvar` IS (eigenvariables don't move, and chains
/ critical reducts add no new eigenvariables).

## The concrete de-risked plan (multi-lap, each step low-risk)

1. **Define `maxEigen d`** = the largest eigenvariable index in derivation `d`, by the **exact `idg`
   template** (`InternalZ.lean`: `maxEigenNext d s` reads premise results via `znth s (zIallPrem d)` etc.,
   combined with `zIallEig`/`zIndEig`; build the table via `PR.Construction`; `maxEigen d := znth (table) d`).
   `𝚺₁`-definable by the same mechanical proof as `idgNext_defined`.
2. **Prove `maxEigen_zsubst : maxEigen (zsubst d a t) = maxEigen d`** for closed `t` (eigenvariables
   preserved). This is the substitution-stability lemma — the crux that makes maintenance-through-`red` work.
3. **Reformulate `ZDerivation_zsubst`** to take freshness `maxEigen d < a` instead of `d ≤ a`: the proof
   body is unchanged except the two `e ≠ a` derivations now come from `e ≤ maxEigen d < a` (zIall/zInd) and
   the IH threading carries `maxEigen premise ≤ maxEigen d < a`.
4. **O1 — strengthen `zIallWff`/`zIndWff`** with `maxEigen d0 < eigenvar` (eigenvariable fresh above its
   premise). Discharge in M2 (the Foundation→Z embedding picks fresh eigenvariables this way). Prove `red`
   maintains it (steps 1–2 give stability; chains/critical reducts add no eigenvariables).
5. **Route B's reducts then discharge unconditionally** (the banked corollaries, with `hle` supplied by
   the strengthened Wff). `tpReduce` conclusion-tracking proceeds (lap-91 keystone).

## Fallback
If step 4's `red`-maintenance hits an unforeseen wall, **Path C** (the ω-rule, `wip/InternalZomega.lean`)
remains the escape hatch — but only then, given its un-precedented arithmetization cost. Do NOT pivot to
C pre-emptively.

## NEXT lap
Step 1: define `maxEigen` (copy the `idg`/`idgNext`/`idgTable` block, swap the combine function). Then
step 2 (`maxEigen_zsubst`). These are the two foundation lemmas; 3–5 follow.
