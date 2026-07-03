# E — Judge: the "code-recursion crux" (leaves 2934/3002), source-grounded + harsh (Ren, 2026-06-26, ~lap 149)

> **VALIDATE, don't trust.** Grounded in `scratchpad/buchholz-gentzen.txt` §14.251-254 + Thm 2.1/3.4/4.2
> (read in full) and the Lean at HEAD lap-149. Operator asked for a harsh judgment of whether the general
> `Γ→⊥` cut-reduction (the two deepest live leaves) rests on a structural measure (IΣ₁-OK) or smuggles the
> ordinal (Gödel-barred). Verdict below with confidence + "how this could be wrong."

## TL;DR — faithful architecture, prereqs genuinely built, but the recursion ENGINE is missing
1. **Architecture is faithful + IΣ₁-sound IN PRINCIPLE.** Buchholz factors exactly as the box claims, and
   the two recursions must NOT be conflated (per Codex, correctly):
   - **one-step reduct CONSTRUCTION** (`d ↦ d[0]`, Thm 2.1, §14.25): proved "by induction on the build-up
     of d" = **structural** recursion into sub-derivations. THIS is leaves 2934/3002. Structural ⟹ IΣ₁-OK.
   - **whole-orbit TERMINATION** (Cor 2.1 + Thm 4.2 `o(d[n])<o(d)` + ε₀-wellfoundedness): **ordinal/PRWO**,
     legitimately, and already wired (`false_of_ZDerivesEmpty` + `InternalPRWO`). The ordinal lives ONLY
     here. So "not iord-recursion for the construction" is the right call and is faithful.
2. **The old decomposition worry is DEAD — credit the box.** L3.1 (`inference_critical_pair`, InternalZ:507)
   and T3.4 (`inference_critical_pair_rank`, :576, the rank bound `rk(A(d))<r`) are **built and sorry-free**.
   The "C3b can't even be stated truthfully" gap (E-CRUX2-DECOMPOSITION §3) is closed. These were the real
   prerequisites and they exist.
3. **THE GAP (harsh): there is NO finitary well-founded measure to FOUND the "strong induction on code."**
   `ZDerivation : V→Prop` is a **Σ₁ fixpoint over codes**, NOT a Lean inductive — so structural induction is
   NOT free; it requires a **numeric** measure (derivation height / code size) provably decreasing on
   premises, inducted via IΣ₁'s Σ₁/Π₁ induction. A grep of `InternalZ`/`Crux2Blueprint` for
   `zHeight`/`zSize`/`codeSize`/`WellFounded`/`strongRecOn`/height-decreases-on-premise finds **nothing**.
   Until that measure exists, "strong induction on derivation code" is a phrase, not a foundation.

## ⚠️ CORRECTION (Codex pushback, source-verified 2026-06-26) — the engine EXISTS; retract "no measure"
Codex flagged `zDerivation_induction`, and it's REAL: `InternalZ.lean:5670`, a structural induction over the
`ZDerivation` code-fixpoint, in BOTH a **Δ₁-motive** and a **Σ₁-motive** flavor (the `𝚺₁` variant is
purpose-built for exactly this), and `redSoundGen` was already built with it. So the code-induction principle
is NOT absent — my grep searched `height/size/WellFounded/strongRec` and missed the `*_induction` name (the
exact "absence may be a grep miss" hedge I flagged). **Point 3 above is RETRACTED**: the principle
encapsulates the well-foundedness; no separate `zHeight` measure is needed. My confident absence-claim
outran the evidence — credit Codex.

**The real (sharper) question is MOTIVE STRENGTH, verified facts:**
- The reduct is **still a bare `∃ d'`** everywhere (every `descent_step_*` concludes `∃ d', ZDerivesEmptyR d'
  ∧ icmp (iord d') … = 0`); there is **no `genReduct : V→V` definable function** yet. A bare-`∃` motive is Σ₁
  ⟹ use the **Σ₁-motive** `zDerivation_induction` variant (supported) — so it is NOT definability-blocked.
- The invariant ingredients are Σ₁-definable (`zFresh_defined`, `zSeqAnt_defined` : `𝚺₁-Function₁`), so they
  don't break the motive.
- **IH reach (the load-bearing seam) DE-RISKS, doesn't wall:** §14.254 reduces a *premise* `dj` first — a
  genuine sub-derivation, so the structural IH `P(dj)` IS exactly what `zDerivation_induction` provides,
  yielding `dj`'s reduct to splice. So the recursion is founded.
- **Residual definability risk:** the unbounded-∀ motive gotcha (`lean-definability-unbounded-forall-motive`)
  — the motive's same-end-sequent + threading clauses (`∀ i ≤ j0, ∀ B, inAnt B …`) must stay BOUNDED to keep
  it Σ₁. They look bounded; CONFIRM it when stating the motive.
- **gDef stays a DISTINCT obligation:** Σ₁-induction yields `∃ d'` (existence), NOT the explicit Σ₁ *graph*
  `exists_sigma1_descending_step` (:3125) needs. Bare-∃ is fine for the orbit contradiction but does not
  discharge gDef — the constructive single-step graph (Codex's earlier C4) is still owed separately.

## Why a heavier MOTIVE is the residual risk — §14.254 genuinely recurses
§14.253 (Principal case) is a one-level surgery (form three chain inferences from the existing premises) —
no recursion. But **§14.254** (lines 480-535) is where the recursion lives: when a remaining premise is
*unchanged* and its own reduction "is according to 14.253," you must **first reduce that sub-premise's
derivation `dj`**, then **SPLICE** `dj{0}`/`dj{1}` into the outer chain's premise sequence in place of the
conclusion (lines 486-535). That "reduce `dj` first" is the recursive call — on a premise (sub-derivation),
so the `zDerivation_induction` IH at `dj` founds it. The risk is whether the **motive** carries the splice
output (same-end-sequent + invariants + descent), NOT whether the recursion is well-founded.

## Two aggravating factors (why I go BELOW Codex's 60-70%)
- **§14.254 is the SPLICE case, and this box has a documented splice-bug history.**
  `ANALYSIS-2026-06-25-lap87-splice-order-sensitivity.md` and `…-lap94-splice-dispatch-unfaithful.md` are
  prior in-kernel refutations of exactly this "splice premises into the outer chain" machinery. The single
  hardest remaining sub-case is the one the box has historically gotten wrong. Expect ≥1 false attempt.
- **The Gödel-bar trap is one wrong reach away.** `iord` descends, so it's the *tempting* recursion measure
  — and it's forbidden (ε₀-recursion is not IΣ₁-available). The handoff's forbidden-list says "NOT
  iord-recursion," good — but knowing-what-not-to-use does not SUPPLY the finitary measure they need. The
  risk is a flail: can't use iord, no code-height built, so the induction has no engine.

## Recommendation — test MOTIVE STRENGTH first, don't reinvent the engine (Codex, endorsed)
1. **FIRST crux move = a skeleton `genReduct_botSucc` proof via the Σ₁-motive `zDerivation_induction`**, with
   the heavy constructor bodies left as named sub-`sorry`s. The motive bundles: same-end-sequent reduct +
   `ZRegular`/`ZFresh`/`ZSeqAnt` preservation + `iord`-descent + the §14.254 splice output. Do NOT build a
   new finitary measure — `zDerivation_induction` (InternalZ:5670) already IS the engine.
2. **At the skeleton stage, CONFIRM two things before grinding bodies:** (a) the motive stays Σ₁ — no
   unbounded ∀ leaks in (the `∀ i ≤ j0, ∀ B, inAnt B …` threading must be bounded); (b) the IH lands at the
   codes §14.254 actually consumes (the premise `dj` AND, after reducing it, the cut-partner pieces
   `dj{0}`/`dj{1}` you splice). If the IH does NOT reach a needed code, THAT is the real obstruction — surface
   it, don't paper over it.
3. **Then** state §14.254's splice as its own named lemma, order/dispatch pinned against the lap87/lap94
   findings (re-read those two ANALYSIS docs — the box's own prior refutations are the test cases).
4. T3.4/L3.1 are the rank-drop inputs (done). gDef (:3125) remains a SEPARATE obligation: the Σ₁-induction
   gives `∃ d'`, not the explicit graph gDef needs — build the constructive single-step reduct function for
   that, don't expect it to fall out of the existence proof.

## Confidence
**~60%** for a clean code-recursion decomposition from here (post-correction; was 55% under the wrong
"missing engine" premise; Codex: 60-70% — we now converge). The engine exists, prereqs are real, and the
§14.254 recursion is founded — this is NOT a feasibility wall and NOT a missing-scaffold. The residual risk
is concentrated in (a) the heavier **motive** staying Σ₁ + the IH reaching the splice codes, and (b) the
§14.254 splice faithfulness (historical bug-magnet, lap87/lap94). Both bounded. If the skeleton goes in with
a Σ₁ motive whose IH reaches the cut-partner codes, revise toward 70%.

## How this could be wrong
- **The measure may exist under a name I didn't grep** (e.g. folded into the `ZDerivation` fixpoint's own
  recursion, or an `idg`/code-length lemma I mis-skipped). If so, the central finding softens to "verify it
  founds §14.254's recursion." Worth the box confirming explicitly rather than assuming.
- **§14.254 might be dischargeable WITHOUT a general height recursion** if the ⊥-orbit's chain structure
  bounds the nesting depth (e.g. only one level of "reduce the sub-premise first" ever occurs on a `→⊥`
  endsequent). If the box can prove the nesting is depth-bounded, it sidesteps the general measure. I did
  not find such a bound, but it's the one route that dodges the scaffold — worth checking before building it.
- Convergence caveat: Codex and I agree on the architecture, but both read the same repo docs; the
  finitary-measure gap is the one thing the handoff's self-description omits, which is why I flag it loudest.

## Pointers
- Source: `scratchpad/buchholz-gentzen.txt` §14.253 (lines 369-479, Principal), §14.254 (480-535, splice),
  Cor 2.1 (537-541), Thm 4.2 ordinal descent (749-815).
- Built prereqs (sorry-free): `inference_critical_pair` (InternalZ:507), `inference_critical_pair_rank` (:576).
- Crux leaves: `descent_step_K_noncrit_repMajor_K` (Crux2Blueprint:2934), `…_axMajor` (:3002); gDef (:3125).
- Prior splice refutations (the §14.254 test cases): `ANALYSIS-…-lap87-splice-order-sensitivity.md`,
  `…-lap94-splice-dispatch-unfaithful.md`.
