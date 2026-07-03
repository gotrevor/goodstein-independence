# E — eq-(5) faithfulness + route/feasibility finding (judge, 2026-06-23, ~lap 61)

> **VALIDATE, don't trust.** Source-grounded judge pass (read Buchholz [6] §§1–5 in full + a literature
> survey). Three results: (1) the box's `o(d)` ordinal assignment is **faithful to Buchholz** ✅;
> (2) the **whole Gentzen Con(PA) core was machine-checked in Coq in Feb 2026** (Bryce–Goré) — feasibility
> is no longer in question; (3) one **architecture seam** (Foundation→Z bridge) is **missing from the
> C1–C5 plan** and is a ~1k-line-scale obligation, not a footnote. Each finding has a confidence %, a
> validation checklist, and a "how this could be wrong" so you can refute cleanly.

## Operator directive (binding) — NO axiom on the headline
Trevor 2026-06-23: this project builds **axiom-free** (trust base only: `propext, Classical.choice,
Quot.sound`) or is **abandoned**. Do **not** rest the headline on a cited `PRWO(ε₀)→Con(PA)` axiom.
You *may* state — and separately *prove* — `PRWO(ε₀)→Con(PA)` as its own headline result, but the
independence target may not depend on it as an axiom. (Also: `PA_delta1Definable`, the Foundation axiom
riding Gödel II, must end up **discharged** for true axiom-free — flag it; check whether the current
Foundation pin already proves it, else it's a sub-task.)

## Finding 1 — the `o(d)` assignment is FAITHFUL to Buchholz [6] §4 (confidence 90%)
Read Buchholz §4 against the lap-60 `idg`/`iõ`/`iord` design. Exact correspondence:

| Buchholz §4 | Box (`InternalZ`/`InternalTower`/`InternalNadd`) |
|---|---|
| `o(d) = ω_{dg(d)}(õ(d))`, `ω₀(α)=α`, `ω_{n+1}(α)=ω^{ω_n(α)}` | `iord d := iotower (idg d) (iõ d)` |
| `õ(I… d₀) = õ(d₀)+1` | `zIall/zIneg ↦ iõ(sub)+1` |
| `õ(Ind d₀ d₁) = ω^{õ(d₀)} # ω^{õ(d₁)+1}` | `zInd ↦ ω^{iõ d0} # ω^{iõ d1 +1}` |
| `õ(Kʳ d₀…d_l) = ω^{õ(d₀)} # … # ω^{õ(d_l)}` | `zK ↦ #-fold of ω^{iõ dⱼ}` |
| `dg(Ind…) = max{dg(d₀)−1, dg(d₁)−1, rk(F)}` | `zInd ↦ max(idg d0−1, idg d1−1, rk p)` |
| `dg(Kʳ…) = max{dg(dⱼ)−1, r}` | `zK ↦ max-fold(idg−1), r` |
| eq (5) = **Thm 4.2** `o(d[n]) < o(d)`, via **Lemma 4.1** (dg non-increasing, õ strictly drops, tower reindex `ω_{dg(d)−dg(d[n])}`) | F1–F4 (`inadd`) + `icmp_iotower_mono`/`_lt_succ_of_le` |

The order algebra already built (natural sums F1–F4 + ω-tower mono/cross-level) is **exactly** Lemma 4.1's
input. **No confabulation in the assignment — this is a clean transcription of Gentzen-via-Buchholz.**
- *Validation checklist:* (a) confirm `idg`/`iõ` dispatch matches the table for ALL five `zTag` cases incl.
  atomic (Buchholz §5); (b) confirm the tower is `ω_{dg}` height = `idg d`, base = `iõ d` (not swapped);
  (c) once C3 is stated, confirm it is literally `iord(iR d) ≺ iord d` via the `ω_{dg−dg}` reindex of Lemma 4.1,
  not a weaker per-step fact.
- *How this could be wrong:* I read §4's assignment but not every §5 atomic-derivation ordinal; if the atomic
  cases (`Ax⁰…Ax³`) get nonstandard ordinals, the table is incomplete. Also Buchholz footnote: the assignment
  "is essentially that of [KB81]" (Kirby–Paris) — a second source to cross-check the atomic cases against.

## Finding 2 — feasibility is SETTLED: the core was formalized in Coq, Feb 2026 (confidence 95% it exists)
**Bryce & Goré, arXiv:2603.00487, repo `aarondroidbryce/Gentzen`** — machine-checked **`Con(PA)`** via
ordinal assignment + cut-elimination, in Coq. This converts crux-2 from "uncharted, maybe-multi-year"
into "precedented, port-and-internalize." Size (cloned + `wc -l`): ~18k lines total, of which
**~4.5k = Castéran ε₀-ordinals (→ mathlib/`InternalONote`)**, **~4.2k = FOL substrate (→ Foundation/mathlib)**,
and **~6–7k = the new proof-theory core** (`cut_elim.v` 1206 + inversions ~2400 + `PA_omega.v` 713 +
**`Peano.v` PA↔PA_ω bridge 1215** + assembly).
- **Route caveat:** Bryce–Goré use the **infinitary PA_ω** route (Gödel's reformulation); the box uses
  Gentzen's **finitary Z** (Buchholz). **Keep Z** — it is the correct vehicle here: PRWO(ε₀) is about
  *primitive-recursive* descents, and only the finitary reduction `R` yields a *primrec* `n ↦ ord(Rⁿd₀)`
  descent that joins crux-1's Goodstein→PRWO slow-down. PA_ω cut-elim gives Con(PA) at meta-level but does
  **not** expose the primrec-PRWO hinge. (Their PA_ω inversion files ~1340 lines are route-specific and do
  NOT port to Z; the finitary Z reduction is plausibly leaner there.)
- **Use it as:** (i) feasibility proof, (ii) a blueprint specifically for the **bridge** (Finding 3) — read
  `theories/Logic/Peano.v` `PA_closed_PA_omega` for how they simulate every PA axiom/rule in the proof system.
- *How this could be wrong:* it's a self-described *draft* (JAR-intended, not yet peer-reviewed); the
  "~6–7k core" is `wc -l`, not a proof-content audit; and because it's PA_ω not Z, it bounds *feasibility*,
  not *our* line count.

## Finding 3 — MISSING SEAM: the Foundation→Z bridge (confidence 75% it's real & unplanned)
`gentzen_descent_of_inconsistent` is triggered by **`¬𝗣𝗔.Consistent M`** = M has a coded **Foundation**
derivation of ⊥. But `ord`/`R`/eq-(5) operate on **Buchholz-Z** derivations (`InternalZ`: `zK`=chain rule,
`zInd`=induction). **Nothing in C1–C5 turns a Foundation ⊥-proof into a Z ⊥-derivation.** Without it, C1–C5
build a machine with no input. Bryce–Goré's analogue (`Peano.v`, **1,215 lines**) shows this is a real
~1k-line milestone, not a footnote.
- **What's needed:** `Z ⊇ PA` on closed sequents — every Foundation/PA axiom is a Z-theorem and every
  Foundation inference rule is Z-admissible — so `Foundation-PA ⊢ ⊥  ⟹  Z ⊢ (→⊥)`. Then `derivesEmpty d`
  (the box's stand-in) is genuinely populated from `¬Con`. Must hold **M-internally** (Σ₁ / per-model), since
  the descent is on M-internal coded derivations.
- *Validation checklist:* (a) write the type of the bridge lemma now (`𝗣𝗔.DerivationOf d ⊥ → ∃ z, ZDerivesEmpty z`,
  M-internal) and add it as **milestone C0.5** before C1; (b) confirm `derivesEmpty`/`ZDerivation` is the
  *target* of that lemma and `𝗣𝗔.Consistent` its *source* — they are currently two unconnected objects;
  (c) check Foundation's actual calculus shape (`Foundation/FirstOrder/Basic/Calculus.lean`, the Tait/sequent
  system `Hauptsatz` cut-eliminates) to scope the simulation.
- *How this could be wrong:* if you intend `derivesEmpty` to be defined *natively in Z* and the only tie to
  Gödel II is a separate "Z-Con ↔ Foundation-Con" lemma, the bridge still exists — just relocated; it is not
  optional in any case because seam-2 (`gentzen_reduction_internalized`) ends at Foundation's `𝗣𝗔.consistent`.
  Lower confidence (75%) only because I haven't read `InternalZ.lean`'s intended `derivesEmpty` wiring — if
  you already have a C0.5 in mind, downgrade this to "confirm it's tracked."

## Net (judge recommendation)
- **Do not abandon, do not axiom.** Feasibility is established (Finding 2); the assignment is faithful
  (Finding 1). Honest finishability **~60%** (multi-month), up from ~35% before the literature pass — the
  revision is the Bryce–Goré existence proof, not optimism.
- **Keep Buchholz-Z.** Right vehicle for the primrec-PRWO architecture.
- **Add C0.5 (Foundation→Z bridge) to the milestone list** — it's the one real architecture gap, ~1k-line scale.
- **Track `PA_delta1Definable`** — must be discharged for true axiom-free; check the Foundation pin.
- Credit where due: the §4 transcription and the per-model reframe (semantic axiom + completeness) are both
  exactly right. Converge, don't re-litigate.
