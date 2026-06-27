# DIRECTION — GoodsteinPA (expedition charter)

Companion to `EXPEDITION-PLAN.md` (the math). This is the **operational charter** for an
autonomous treadmill campaign. Read both.

---

## ⚙️ CURRENT DIRECTIVE — altitude-lap-owned · binding on grind laps

> **WRITE-ACCESS: review & reflection (altitude) laps ONLY** (the operator may also set it). Grind
> laps READ this section and work strictly within it; they MUST NOT edit it. It **OUTRANKS** any
> `HANDOFF` "NEXT" pointer or in-flight campaign momentum — this is how an altitude lap's
> course-correction actually STICKS. The standing charter below changes rarely; THIS section turns
> over every few review laps. Keep it SHORT; detail lives in `PENDING_WORK.md` / `REFLECTION-*.md`.
> (Live milestone map = `E-CRUX2-ROADMAP-2026-06-24.md`; the phase list below is the standing charter.)

**Set: lap-155 (FRESH-MIND REVIEW). Supersedes lap-152. Direction KEPT (existence-form pivot off `red` +
code-recursion frame `genReduct_botSucc`). lap-152's mandate is DONE — `genReduct_chain_hasRedex` DROPPED
(lap 153), `genReduct_chain_noRedex` 6/8 branches PROVEN (lap 154). The whole termination crux is now the ONE
open leaf `axMajorClose` (tag-5/6 L-axiom cut-partner, `Crux2Blueprint:3418`). COURSE-CORRECTION: the lap-154
handoff frames this leaf's sub-case (b) as the lap-136 general-succedent reduction (the repo's hardest target);
this review judges that PESSIMISTIC + PREMATURE and mandates the cheaper SUCCEDENT-THREADING COLLAPSE first.
Re-verified axiom-clean (lap 155): headline `peano_not_proves_goodstein` = `[propext, sorryAx, choice,
Quot.sound]` (0 math axioms), `goodsteinSentence_faithful` + `peano_not_proves_consistency` clean — no drift.**

- **THE objective (only this):** close `axMajorClose` (`Crux2Blueprint:3418`) — the LAST open content of
  `genReduct_chain_noRedex` ⟹ of `genReduct_botSucc` ⟹ of the M1b-term termination crux `false_of_ZDerivesEmpty`.
- **MANDATED move — the SUCCEDENT-THREADING COLLAPSE, NOT the lap-136 general-succedent reduction.**
  Kernel-grounded this review: the tag-5 major `zAxAll s' p' k'` has `p'=⊥`, so the cut formula is `^∀⊥`; its
  active formula sits in the major's antecedent, and the chain's `hthread` gives **`^∀⊥ ∈ Γ` (sub-case a)** ∨
  **cut-partner `i'<jstar` concluding `^∀⊥` (sub-case b)** — exactly as `majorPrem_zAxAll_cutPartner` already
  splits, but now the (a) disjunct is LIVE at `Γ≠∅` (it dies only at `seqAnt s=∅`). Under `hnolow` (no redex
  below j0) a **direct R-intro `zIall` of `^∀⊥` below j0 is IMPOSSIBLE** — it would form an `isRedexPair` with
  jstar (VERIFIED: `isRedexPair` (`InternalZ:4820`) fires on `(zIall ^∀p, zAxAll ^∀p)`). So `^∀⊥` is never
  *created* below j0; it only threads from Γ. Decompose `axMajorClose` (raise the src sorry count = progress);
  full attack-tree in `PENDING_WORK.md` (lap-155 top). The teed-up first DROP = the 2 reusable ordinal lemmas
  `w < ω^w` + summand-≤-fold, which close sub-case (a) (fresh `zAxAll s ⊥ k'` derives `Γ→⊥`, õ-dropping).
- **Success metric:** a `src` sorry drops on this path. The ordinal-lemmas + sub-case (a) is the teed-up DROP;
  closing all of `axMajorClose` (the collapse total) drops the LAST `genReduct_chain_noRedex` leaf ⟹
  `genReduct_botSucc` PROVEN ⟹ outer `axMajor` + gDef collapse. NOT: building the lap-136 reduct before the
  collapse is tested; banking the ordinal lemmas without wiring them into sub-case (a).
- **FORBIDDEN:** building the lap-136 general-succedent / general-induction reduct (`⟨d0,d1[a:=0..k-1]⟩`,
  `k=⟦t⟧`) as the PRIMARY attack BEFORE the succedent-threading collapse is tested to exhaustion — it is most
  likely OBVIATED, and at worst returns as a NARROWED `Γ→^∀⊥` target (a `zInd` concluding a ∀-formula), never
  "arbitrary succedent C"; witnessing any descent branch with `red`; the construction by `iord`-recursion
  (PRWO/Gödel-barred — CODE induction via `zDerivation_sigma_induction` ONLY); `redLeast`/μ-min for gDef
  (refuted lap-139); the single-premise `seqUpdate`+combined-`iord` splice (`descent_step_K_splice`, refuted
  in-kernel lap 151); attacking `descent_step_K_noncrit_axMajor` :3507 or gDef :3630 STANDALONE (they are the
  Γ=∅ special case / constructive-reduct consumer of the master keys); the off-path dead `red`-soundness
  sorries {:82,:1257,:1367,:1563,:1653,:1765,:1868} AS STATED; M2 / M4 wiring.
- **Why:** the handoff's "(b) = lap-136" reading would commit grind laps to the repo's hardest target (the
  general induction reduct, kernel-refuted at face value lap-136) when the structural facts (`hnolow` forbids
  *creating* `^∀⊥`; the existing `chainAsucc_threaded_of_leaf`; the verified redex-pair check) most likely
  COLLAPSE tag-5/6 to the tractable sub-case (a). Test the collapse first — it is the lap-101/lap-132-style
  decisive spike. ALTITUDE CAUTION (still binding): M2 — the Foundation→Z bridge — is ~0% built and
  crux-entangled; "only the crux is left" must NOT read as "almost done."

### Directive history (newest first; append one line per altitude lap — never delete)
- **lap-155** (FRESH-MIND REVIEW): direction KEPT (existence-form pivot off `red` + `genReduct_botSucc` code-recursion). lap-152's mandate DONE — `genReduct_chain_hasRedex` DROPPED (lap 153) + `genReduct_chain_noRedex` 6/8 branches PROVEN (lap 154). Re-verified axiom-clean (headline `[propext,sorryAx,choice,Quot.sound]` 0 math axioms; faithful/consistency clean; statement no drift). The whole termination crux = the ONE open leaf `axMajorClose` (tag-5/6 L-axiom cut-partner, `Crux2Blueprint:3418`). **COURSE-CORRECTION:** the lap-154 handoff frames its sub-case (b) as the lap-136 general-succedent reduction (the repo's hardest target, kernel-refuted at face value); the review judges that PESSIMISTIC + PREMATURE. Kernel-grounded insight: cut formula is `^∀⊥` (`p=⊥`); under `hnolow` a direct R-intro `zIall` of `^∀⊥` below j0 is IMPOSSIBLE (would `isRedexPair` with jstar — VERIFIED `isRedexPair:4820` fires on `(zIall ^∀p, zAxAll ^∀p)`), so `^∀⊥` is never CREATED, only threaded from Γ. MANDATE = the SUCCEDENT-THREADING COLLAPSE (sub-case (a) `^∀⊥∈Γ` via 2 reusable ordinal lemmas `w<ω^w`+summand-≤-fold + generalize `majorPrem_*_cutPartner` off `seqAnt s=∅`; collapse sub-case (b): leaf→`chainAsucc_threaded_of_leaf`, R-intro→`hnolow`, zK→recurse, residual at most a `zInd` concluding `^∀⊥` — check it's even derivable). FORBIDDEN = building the lap-136 reduct BEFORE the collapse is tested to exhaustion; `red`; `iord`-recursion; `redLeast`; the refuted `seqUpdate` splice; axMajor/gDef standalone. ALTITUDE CAUTION = M2 (Foundation→Z bridge) ~0% built — "only the crux left" ≠ "almost done."
- **lap-152** (DEEP REFLECTION): direction KEPT (existence-form pivot off `red` + lap-150 code-recursion frame). lap-149's mandate DONE (tag-3 freshFlag DROPPED lap 149); laps 150-151 landed `genReduct_botSucc` (Σ₁ code-recursion), REFUTED the false `seqUpdate` splice in-kernel, PROVED the FLATTEN engine `descent_step_K_spliceHalves`, DROPPED false `descent_step_K_splice` via `GenReductCert` (replace|flatten). RE-VERIFIED axiom-clean (headline/faithful/consistency all `[propext,(sorryAx,)choice,Quot.sound]`, 0 math axioms, no drift). FINDING = trajectory is HEALTHY (lap-143's banking-not-wiring/witness-with-red worries RESOLVED; steady crux DROPS 144→151, in-kernel refutation discipline alive); crux now correctly isolated to `genReduct_botSucc`. KEY ARCHITECTURAL INSIGHT = the four open leaves reduce to TWO master keys: `genReduct_chain_hasRedex` :2989 + `genReduct_chain_noRedex` :3013 SUBSUME the outer `descent_step_K_noncrit_axMajor` :3226 (Γ=∅ special case) and feed gDef :3349 (constructive reduct) — do NOT attack axMajor/gDef standalone. MANDATE = DROP `genReduct_chain_hasRedex` via the zSeqAnt tag-4 `Seq (seqAnt s)` fold (`zSeqAntNext` :2003, exact shape of the proven lap-149/146 folds), THEN `genReduct_chain_noRedex`. FORBIDDEN = `red`; `iord`-recursion for construction; `redLeast` for gDef; the refuted `seqUpdate` single-splice; axMajor/gDef standalone; the fold as a goal. ALTITUDE CAUTION = M2 (Foundation→Z bridge) ~0% built + crux-entangled — "only the crux left" ≠ "almost done."
- **lap-149** (FRESH-MIND REVIEW): direction KEPT (existence-form pivot off `red`); lap-146's mandate is DONE (`descent_step_Ind` DROPPED lap 146; laps 147-148 advanced §5.2 noncritical, decomposed faithfully per Buchholz §14.254a/b). VERIFIED axiom-clean: `false_of_ZDerivesEmpty`/`ZDerivesEmptyR_descent_step`/`descent_step_K_noncrit_recurse` all `[propext, sorryAx, choice, Quot.sound]` — 0 math axioms; crux-2 = 4 disclosed `sorryAx` leaves {tag-3 freshFlag :2974, tag-4 K-recursion :2934, axMajor 5/6 :3002, gDef :3125}. FINDING = crux-neglect signal forming — recent laps closed surrounding machinery (Ind reducts, replace plumbing, dispatchers) while the genuine crux (general `Γ→⊥` cut-reduction by code-induction, leaves 2934+3002) stays untouched; tag-3 freshFlag is the LAST tractable leaf. MANDATE = DROP tag-3 freshFlag via the focused `zFreshNext` tag-3→freshFlag strengthening (mirror tag-1 I∀ :1671, exact shape of the proven lap-146 `zIndWff` ripple), THEN turn to the crux (general code-recursion + gDef) — NO more leaf-hunting. FORBIDDEN = `red` witnesses; `iord`-recursion for the general step; `redLeast` for gDef; jumping to the crux before freshFlag drops.
- **lap-146** (FRESH-MIND REVIEW): direction KEPT; lap-143's mandate is DONE (live path FULLY off `red`, lap-144; `ZDerivesEmptyR_descent_step` sorry-free). FINDING = the live termination path now has exactly THREE co-equal genuine sorries {`descent_step_Ind`, `descent_step_K_noncritical` §5.2, (A) `gDef`}, none generational. VERIFIED lap-145's `zIndWff` diagnosis is REAL not stale (step clause :1684 is membership `inAnt(F(a))`, base clause :1682 is an equation — genuine asymmetry) AND that the strengthening is REQUIRED for soundness (membership-only admits unsound Ind nodes) + more faithful to Buchholz; the ZSeqAnt + "no-cascade-docstring" reframes both CHECKED and refuted. MANDATE = DROP `descent_step_Ind` via the focused, definability-dominated `zIndWff` step-clause→shape ripple (`seqAnt(fstIdx prem1) = seqCons (seqAnt(fstIdx d)) (F(a))`); descent + `p=⊥` already banked. FORBIDDEN = `red` witnesses; the refuted reframes; jumping to §5.2/(A) before Ind drops.
- **lap-143** (DEEP REFLECTION): direction KEPT (existence-form pivot); FINDING = laps 141-142 regressed it — `descent_step_K_critical` re-witnesses with `red` (= the kernel-FALSE `redSoundGen`/:80/:1108 chain) and the genuine `ZDerivation_iRKcCrit_critical_all` (lap-142) is banked but UNWIRED. MANDATE = finish the pivot: derive `ZSeqAnt_iRKcCrit`, split `descent_step_K_critical` into ∀ (wire `iRKcCrit`, red-free) + ¬ (named `redexJ≤j0` sorry), then re-witness the Ind branch with `iIndReductSeqG`. FORBIDDEN = witnessing any descent branch with `red`. Retires lap-140's `descent_step_K_majorIdx`-by-major-tag mandate (abandoned lap-141).
- **lap-140** (altitude review): RETIRED lap-137's two stale mandates (orbit (B) DONE lap-138; `redLeast` μ-route REFUTED lap-139). Crux-2 termination collapses to ONE lemma `descent_step_K_majorIdx`; (A) folds in via concrete `redStep`. MANDATE = decompose it into per-tag {3,4,5/6} src sub-`sorry`s + assemble a banked sub-piece to a DROP (tag-5/6 explicit-pair soundness, or tag-3 `isChainInf_iIndReductSeqG`).
- **lap-137** (altitude review): existence-form spike DONE; TYPE-CORRECTED the PRWO seam (`InternalPRWO` hyp; `→ False` in bare 𝗜𝚺₁ was Gödel-barred). PRIMARY = `exists_sigma1_descent_of_step` (the 𝚺₁ ε₀-descent — neglected through laps 135-136); secondary = `descent_step_K_majorIdx`. [stale: see lap-140]
- **pre-lap-135** (operator + judge): focus to **M1b-term only**; existence-form spike FIRST; success = a `src/` sorry drops.

---

## The goal (not a fixture — the destination) 🦸

**Prove `Statement.peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence`** — Kirby–Paris (1982),
Peano Arithmetic does not prove Goodstein's theorem. That headline `sorry` is the *target*, not
a thing to preserve. The whole campaign exists to discharge it honestly.

## You (the box) own the full decomposition

This is **formalization of a known proof**, not origination. Gentzen's ordinal analysis is ~90
years old and in textbooks (Gentzen 1936, Schütte, Takeuti). Decomposing it into mathlib-shaped
Lean lemmas is exactly treadmill work. The phases (see `EXPEDITION-PLAN.md` for the math):

- **Phase 0 — encoding.** ✅ DONE - Milestone **M1** complete (`goodsteinTerminates_re` + `computable_bump` proven, 0 sorries; verified 2026-06-26).
- **Phase 1 — Gödel II hook.** Surface `Con(𝗣𝗔)` + `𝗣𝗔 ⊬ Con(𝗣𝗔)` from Foundation's *existing*
  Gödel II (`FirstOrder/Incompleteness/Second.lean`), and reduce the headline to the single
  implication `𝗣𝗔 ⊢ γ → 𝗣𝗔 ⊢ Con(𝗣𝗔)`. Assembly. Milestone **M2**.
- **Phase 2 — the girder.** `TI(ε₀) ⊢ Con(𝗣𝗔)`: infinitary `PA_∞` (ω-rule), ordinal assignment
  `< ε₀` to derivations, ε₀-bounded cut-elimination. The deep core. Decompose it; build on
  mathlib's ε₀ (`SetTheory/Ordinal/Veblen`, `ONote`) + Foundation's finitary Hauptsatz. Milestones **M3…**.
- **Phase 3 — `Goodstein ⟹ TI(ε₀)`.** Re-express, syntactically, the ordinal descent that the
  termination Engine (`lean-formalizations` `Logic/Goodstein`) already does model-side.
- **Phase 4 — assemble.** `γ ⟹ TI(ε₀) ⟹ Con(𝗣𝗔)`, then Gödel II ⟹ `𝗣𝗔 ⊬ γ`. Discharge the
  Statement `sorry`. `#print axioms` clean.

Decompose with **disclosed sub-`sorry`s** — a named lemma held at `sorry` is honest, checkable
progress. Bank green laps; chip the girder lemma by lemma.

## Literature — on disk + offline requests 📚

**On hand (read these FIRST):** `papers/` holds pre-downloaded proof-theory references (PDFs;
gitignored, but present on your disk via the bind-mount). `papers/SOURCES.md` is the catalog —
what each paper is and which phase it serves (Gentzen ordinal analysis, PA_∞ cut-elimination,
Kirby–Paris, Goodstein/Cichoń, fast-growing hierarchy). **Ground the girder in these, not in
memory** — infinitary proof theory is exactly where an LLM confabulates a plausible-but-wrong
argument. Quote the source; don't reconstruct it.

**For gaps:** you are network-isolated (no web, no GitHub). When you need a reference that isn't
in `papers/` — a specific lemma statement, the exact ε₀ cut-elimination bound, a notation
convention — **do not guess and do not stall.** Write an **`ON-LINE-REQUEST.md`** at the repo root
with precise questions; a host fulfiller researches it and commits `ON-LINE-FINDINGS-*.md` (and
may add a PDF to `papers/`) for you to read next lap. Getting the math right from the literature
beats inventing a decomposition.

## M1 — ✅ DONE (do NOT re-attack)

`Encoding.goodsteinTerminates_re : REPred goodsteinTerminates` is **PROVEN** (verified 2026-06-26:
0 sorries in `Encoding.lean` / `Computability.lean` / `Defs.lean`). It landed as built:
`computable_bump : Computable₂ bump` (`Computability.lean:131`) → `goodsteinTerminates_re`
(`Encoding.lean:60`). Effect realized: **Phase 0 is axiom-clean** - `goodsteinSentence_faithful`
(`Bridge.lean:34`) prints `[propext, Classical.choice, Quot.sound]`, no `sorryAx` (re-verified
in-kernel lap 132). Nothing here to do.

> Historical route (for reference): `Computable bump` (well-founded recursion on `Nat.log`) →
> `Computable₂ goodsteinSeq` → `ComputablePred (·=0)` → `ComputablePred.to_re` →
> `REPred.projection` (∃ N), per Foundation `Vorspiel/Computability`.

## ANTI-FRAUD guard (the one hard rule) 🚫

A `sorry`'d headline is honest; a **fake** one is the worst outcome. You may replace
`Statement.peano_not_proves_goodstein`'s `sorry` with a real proof **only if BOTH**:
1. `#print axioms peano_not_proves_goodstein` = `[propext, Classical.choice, Quot.sound]`
   (no `sorryAx`, no custom `axiom`), AND
2. it genuinely chains through built lemmas (no `native_decide` on the headline, no
   `axiom`-smuggling, no vacuous restatement).
If you cannot do both, **leave the `sorry`** and report the gap. The host audits
`#print axioms` on the headline every review lap. Inventing an axiom to "finish" = failure.

## LOCK — faithfulness anchors (do NOT edit) 🔒

Add lemmas freely, but never change these — they are the trust base that makes the headline mean
what it says:
- `Defs.lean` — audited `goodsteinSeq` / `bump` / `base`.
- `Bridge.lean`'s theorem **RHS** `∀ m, ∃ N, goodsteinSeq m N = 0`, and the proved bridge.
- `goodsteinTerminates`'s definition in `Encoding.lean`.

## Mode + execution

- **Expedition** (`--forever`): no self-stop; this is a long campaign measured in
  accumulated axiom-clean mathlib-shaped lemmas, not a single green.
- **Offline build prerequisite**: the box must `lake build GoodsteinPA` offline from the CoW'd
  Foundation v4.31 + mathlib oleans in `.lake/packages` + the box's v4.31.0 Linux toolchain.
  Never `lake update` / fetch. (If lap 1 can't build offline, that's the host's bug to fix —
  rebuild the box image / re-CoW — not yours to route around.)
