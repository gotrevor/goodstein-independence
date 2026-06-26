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

**Set: lap-146 (FRESH-MIND REVIEW). Supersedes lap-143. Direction KEPT (existence-form pivot, lap-132);
lap-143's mandated moves are DONE — the live `false_of_ZDerivesEmpty` path is now FULLY off `red`
(lap-144). The binding move advances to CLOSING the first genuine live-path sorry of the post-red era.**

- **THE objective (only this):** **M1b-term** = close the live `false_of_ZDerivesEmpty` termination path.
  The off-`red` STRUCTURAL goal is ACHIEVED: `ZDerivesEmptyR_descent_step` (`Crux2Blueprint:2270`) is
  sorry-free and dispatches Ind→`descent_step_Ind` (genuine `iIndReductSeqG`) / K→`descent_step_K_majorIdx`
  (critical off `red`, ¬-case CLOSED lap-144) — NO `red`, NO kernel-FALSE soundness on the live path. What
  remains are **three co-equal genuine live sorries**, none generational, none needing `red`:
  `descent_step_Ind` (:2262), `descent_step_K_noncritical` (:2139, Buchholz §5.2 atomic reduct),
  and (A) `exists_sigma1_descending_step` (:2327, the `gDef` Σ₁-Semisentence packaging).
- **MANDATED next move (hardest-first among teed-up work — DROP `descent_step_Ind`):**
  Strengthen the `zIndWff` STEP-premise clause (`InternalZ.lean:1684`) from MEMBERSHIP
  `inAnt (F(a)) (seqAnt(fstIdx prem1))` to SHAPE
  `seqAnt(fstIdx prem1) = seqCons (seqAnt(fstIdx d)) (F(a))` (faithful Buchholz Ind rule: step antecedent
  EXACTLY `Γ,F(a)`). This is **REQUIRED**, not convenient: the membership-only clause admits *unsound* Ind
  nodes (a lax `d1 ⊢ {⊥,X}→⊥` lets stray `X` leak past the rule, so the conclusion `Γ→F(t)` doesn't
  actually follow), and `ZSeqAnt` only flags sequence-wellformedness, not antecedent content — neither the
  ZSeqAnt nor the "no-cascade-docstring" reframe delivers the shape (both CHECKED + refuted lap-146). It is a
  **FOCUSED, definability-dominated ripple, NOT a 64-site cascade** (`zIndWff` is C-free, so `zphi_monotone`/
  `_strong_finite` are untouched): edit (a) `zIndWff` body :1684; (b) `zIndWffDef` σ+π :1704/1718 — use
  `seqConsDef` with `sas = seqAnt(fstIdx d)` already bound at :1700/1714 (or the available `seqAddAntDef`
  :6318); (c) `zIndWff_defined` simp set :1725 (+ `seqCons_defined.iff`); (d) the `zsubst`-preservation site
  `Zsubst.lean:3595/3604` (seqCons commutes with substitution); (e) assemble `descent_step_Ind` from the
  now-derivable shape. The DESCENT half (`iord_descent_iIndReductSeqG_one`) and the `p=⊥` collapse
  (`eq_falsum_of_substs1_falsum`) are ALREADY BANKED — the strengthening is the WHOLE remaining content.
  After it: on the ⊥-orbit `seqAnt(fstIdx d1) = {⊥}`, the telescope threads, soundness closes via
  `zDerivation_zK_intro` + `isChainInf_telescope`. (⚠️ if the build surfaces a LIVE constructor of a `zInd`
  ZDerivation beyond `zsubst`, discharge the new shape there too — but M4/embedding isn't wired, so expect
  only `zsubst`.) THEN: `descent_step_K_noncritical` (§5.2), THEN (A) `gDef`.
- **Success metric:** `descent_step_Ind`'s sorry DROPS — a live-path src sorry, the operator's bar. NOT:
  banking more support lemmas without dropping the sorry; relocating dead `red`-machinery for count-management.
- **FORBIDDEN:** witnessing any `ZDerivesEmptyR_descent_step` branch with `red`; attacking the now-off-path
  dead `red`-soundness sorries {`zKValidF_iIndReduct_of_zInd`:80, `ZDerivation_red_zK_crit`:1108, `_splice`
  :1257-ish, `_nonRep`:1367-ish, `redSoundGen`:1471-ish} AS STATED (relocate to `wip/` only as a DELIBERATE
  cleanup pass AFTER `descent_step_Ind` drops, never as count-management, never before); the
  ZSeqAnt/"no-cascade" reframes (CHECKED lap-146 — neither delivers the shape); jumping to
  `descent_step_K_noncritical`/(A) before `descent_step_Ind` drops (Ind is teed-up and validates the
  red-free pivot end-to-end — keep focus); the `redLeast`/μ-min route for (A) (refuted lap-139);
  `zReg`/`zFresh`/`zSeqAnt` folds as a *goal*; off-critical-path easy `sorry`s; M2 / M4 wiring.
- **Why:** lap-144 got the live path off `red`; lap-145 cracked `descent_step_Ind` down to a single
  well-understood obstruction with both prerequisites (descent + `p=⊥`) already banked. Closing it DROPS the
  FIRST genuine live-path sorry of the post-`red` era and confirms the existence-form + genuine-reduct pivot
  actually yields a sound, dropping proof — the thing the campaign has built toward for ~13 laps. The
  remaining {§5.2, (A) `gDef`} are then the last two genuine pieces, both decomposed and none generational.

### Directive history (newest first; append one line per altitude lap — never delete)
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
