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

**Set: pre-lap-135 (operator + judge).**

- **THE objective (only this):** **M1b-term** — resolve the `red`-engine **STALL / termination** of
  crux-2. Make a `red`-fixpoint on a ∅→⊥ orbit yield a contradiction, so the ordinal descent
  terminates and the fixpoint branch of `false_of_ZDerivesEmpty` (`Crux2Blueprint:1144`) closes.
- **Success metric:** a `src/` `sorry` actually **DROPS** on this path — NOT "lemmas banked" (src
  pinned at 11 for ~30 laps while lemmas accumulated; that ends here).
- **Mandated FIRST move:** run the **lap-132 existence-form reframe** as a cheap `wip/` spike BEFORE
  any more invariant-fold work — reframe the endgame from "`red` is a total Σ₁ function that descends
  every step" to the **existence / least-descending-reduct** form, where "fixpoint ⟹ cut-free" is
  definitional. If it holds it obviates the `majorIdx`/`firstBotPrem`/`zReg`/`zFresh`/`zSeqAnt`
  campaign and reuses the banked per-reduct soundness (laps 112–119). Settle it like the lap-101 spike.
- **FORBIDDEN until the spike is decided:** more `zReg`/`zFresh`/`zSeqAnt` folds; the engine swap as a
  goal; off-critical-path easy `sorry`s; M2 / M3 / M4. If you judge M1b-term blocked, record in
  `PENDING_WORK.md` why + one concrete attack — don't silently switch threads.
- **Why:** altitude laps 120 + 132 found the project circling — reduct-soundness / the swap got
  polished while the TERMINATION question (does cut-elim reach a contradiction, or stall?) sat open
  since lap 104, because each grind lap read the handoff, not the reflection. This layer is the fix.

### Directive history (newest first; append one line per altitude lap — never delete)
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

- **Phase 0 — encoding.** DONE except `goodsteinTerminates_re` (below). Milestone **M1**.
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

## M1 — the immediate residual

```
Encoding.goodsteinTerminates_re : REPred goodsteinTerminates
```
`goodsteinTerminates m := ∃ N, goodsteinSeq m N = 0` is r.e. (search `N`); the only non-trivial
input is **`Computable bump`** (`Defs.lean`, well-founded recursion on `Nat.log` — mathlib won't
auto-derive it). Route: `Computable bump` → `Computable₂ goodsteinSeq` → `ComputablePred (·=0)` →
`ComputablePred.to_re` → `REPred.projection` (∃ N). See Foundation `Vorspiel/Computability`. Pure
computability: zero faithfulness risk (typechecks or it doesn't). Closing M1 makes Phase 0
axiom-clean (`#print axioms goodsteinSentence_faithful` loses its `sorryAx`).

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
