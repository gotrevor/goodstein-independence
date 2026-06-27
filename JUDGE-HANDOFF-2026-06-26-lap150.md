# JUDGE HANDOFF — goodstein-independence (fresh judge baton, 2026-06-26, ~lap 150)

> **You are the OUTSIDE JUDGE of `~/src/goodstein-independence`, not a worker.** An autonomous treadmill
> box (+ a parallel "Codex" reviewer) grind the proof. Your job: read the **source**, catch
> **architecture/seam** errors they can't see from inside, calibrate **honestly** (confidence %, "how this
> could be wrong"), and relay validatable findings to Trevor, who pastes them to the box. **Faithfulness >
> fluency** — route load-bearing claims to the paper/compiler, never a summary. **Validate, don't obey** the
> box's self-description (its handoffs run optimistic — "self-healing"/"turnkey"/"plumbing" labels have
> repeatedly proven false). Converge, credit the workers, add the value they can't.
> This supersedes the stale lap-65 `JUDGE-HANDOFF.md` (which still describes a finished A/B experiment).

## The goal (unchanged)
Prove `Statement.peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence` (Kirby–Paris 1982), **axiom-free or
abandon** — NO Gentzen-as-axiom cop-out on the headline. Route A (Rathjen Cor 3.7): inside 𝗣𝗔,
`γ → PRWO(ε₀) → Con(𝗣𝗔)` → Gödel II.

## Where the proof stands (VERIFY against HEAD — `lean-status g-i`)
- **Headline = `[propext, sorryAx, Classical.choice, Quot.sound]`** — 0 custom math axioms, lone `sorryAx` =
  crux-2. (Re-`#print axioms` it every altitude lap; the host audits this.)
- **DONE + axiom-clean:** M1 (encoding/`goodsteinTerminates_re`), crux-1 (`γ→PRWO`, lap 57), front-2
  (`PA_delta1Definable`, lap 89), the Gödel-II hook. **Existence-form pivot DONE** (lap 132→144): the live
  `false_of_ZDerivesEmpty` path is entirely **off the false `red` engine** — witnessed by genuine reducts
  (`iRKcCrit`, `iIndReductSeqG`), not `red`. The kernel-FALSE `red`-soundness lemmas {`zKValidF_iIndReduct_of_zInd`:80,
  `ZDerivation_red_zK_crit`:1108, `redSoundGen`:1471, …} are **off-path/dead** — do NOT attack them as stated.
- **Real sorry count ≈ src 14 / wip 7** (use `lean-sorry`, NOT `grep sorry` — it 4x-overcounts).

## THE crux you're judging — the "code-recursion crux"
The only deep live leaves are the **general `Γ→⊥` cut-reduction by structural induction on derivation CODE**
(Buchholz Thm 2.1 / §14.253-254): `descent_step_K_noncrit_repMajor_K` (tag-4) + `…_axMajor` (tag-5/6), plus
`exists_sigma1_descending_step` (gDef). As of lap 150 the box framed it as **`genReduct_botSucc` by Σ₁
structural induction**, proved tag-3, and isolated the crux to the **tag-4 §14.254 splice**.

**Read these two judge notes first — they ARE the current verdict (with a correction worth understanding):**
- `E-2026-06-26-JUDGE-code-recursion-crux.md` — the harsh judgment. **Key corrected finding:**
  - Architecture is faithful + IΣ₁-sound: *one-step reduct construction* must be **structural** (and the
    engine EXISTS: `zDerivation_induction`, InternalZ:5670, Δ₁ + Σ₁ motive flavors); *whole-orbit
    termination* is legitimately **ordinal/PRWO** (already wired). Do NOT conflate them. Do NOT use
    `iord`-recursion for the construction (Gödel-barred); do NOT use `redLeast`/μ-min (refuted lap-139).
  - Prereqs **built & sorry-free**: L3.1 `inference_critical_pair` (InternalZ:507), T3.4
    `inference_critical_pair_rank` (:576).
  - **Residual risk = MOTIVE STRENGTH + the SPLICE**, not a missing engine: (a) the `genReduct_botSucc`
    motive must stay **Σ₁** (watch the unbounded-∀ gotcha; the `∀ i ≤ j0, ∀ B, inAnt B …` threading must be
    bounded) and its IH must reach the §14.254 cut-partner codes `dj{0}`/`dj{1}` (the recursion is on a
    premise `dj`, so the IH is available — this de-risks it); (b) §14.254 is a **splice** case and this box
    has a documented splice-bug history — re-read `ANALYSIS-…-lap87-splice-order-sensitivity.md` and
    `…-lap94-splice-dispatch-unfaithful.md`, they're the test cases; (c) **gDef** still owes an explicit Σ₁
    *graph* — `∃ d'` from the induction is NOT the graph; build the constructive single-step reduct.
- `E-2026-06-26-JUDGE-codex-review.md` — the dashboards (M1b-term live path vs full headline), the §5.2
  spike-not-mandate, the dead-sorry cleanup, the gDef/iIter distinction.

## Source on disk (ground claims here, don't reconstruct)
- `scratchpad/buchholz-gentzen.txt`: §14.253 (Principal, lines 369-479), **§14.254 (the splice, 480-535)**,
  Cor 2.1 (537-541), Thm 3.4 rank bound (685-745), Thm 4.2 ordinal descent (749-815).
- `papers/buchholz-on-gentzens-first-consistency-proof.{pdf,md}` (the crux-2 source), Rathjen, Kirby-Paris.
- Bryce–Goré Coq `Con(PA)` (arXiv:2603.00487) in `scratchpad/Gentzen-bg/` — the **feasibility** precedent
  (it's been done meta-level; the IΣ₁-internalization is the un-precedented twist).

## Confidence (honest, decomposed)
- **Reachable in principle (Route A):** ~70% (Bryce–Goré precedent). **This campaign lands it axiom-clean:**
  ~55-60%. These are DIFFERENT numbers — don't quote one as the other. Codex and I converge ~60-70% on the
  code-recursion decomposition specifically.
- **The swing factors:** the tag-4 §14.254 splice (lands clean → nudge up; re-trips the lap87/94 bug → the
  predicted ≥1-false-attempt detour), and downstream **M2** (Foundation→Z bridge, ~0% built, the largest
  remaining unknown, crux-entangled). M2 is bracketed OUT of the M1b-term dashboard — don't let "only the
  crux is left" read as "almost done."
- **Convergence caveat:** Codex and I read the same repo docs, so our agreement isn't independent — a shared
  blind spot (esp. M2's unverified "plumbing" label) wouldn't show up in it.

## Tooling + catch-up recipe (every session)
```
lean-status g-i            # HEAD, branch, REAL sorry counts, newest HANDOFF title, treadmill lap
lean-status g-i --peek     # + what the box is doing THIS SECOND (its transcript, parsed; not a tail)
lean-status g-i --peek -c 5  # last 5 box events, to see the recent arc
cd ~/src/goodstein-independence
git log --oneline -15
grep -rn sorry src/GoodsteinPA/Statement.lean   # the audit surface
ls -t HANDOFF-*.md | head -1                     # newest box baton → read it + STATUS.md + PENDING_WORK.md
```

## Judge cautions (learned this session)
- **Don't make a confident ABSENCE claim from a narrow grep.** I twice said "X doesn't exist" (the sorry
  count; the recursion engine) and was wrong both times — grep the concept several ways, say "I find no X
  under these names," and route to the artifact. Concede cleanly when corrected; the sharpened finding beats
  saving face.
- **Trevor has no stake here** — report numbers straight, don't project hope/excitement onto him.
- **Faithfulness anchors (do NOT edit):** `Defs.lean` (`goodsteinSeq`/`bump`/`base`), `Bridge.lean` RHS,
  `Encoding.lean` `goodsteinTerminates`, `Statement.lean` headline. The whole point is that the headline
  means Kirby–Paris.

— Start with `lean-status g-i --peek`, then the two `E-*.md` notes, then the newest box `HANDOFF`. Ask:
"is the tag-4 §14.254 splice motive Σ₁, and does its IH reach the cut-partner codes?" — that's the live seam.
