# NEXT STEPS — Path C (lap 105: the `#`-natural-sum resolves the principal ∀/∃ ordinal tension)

> **⭐⭐ LAP-105 UPDATE (read FIRST).** Lap 104 deferred the cut node's ordinal as Gentzen's `ω`-tower,
> "multi-month". For the PRINCIPAL ∀/∃ step that deferral was unnecessary: the natural sum `inadd` (`#`)
> closes BOTH operator-control (strict self-domination, `lt_inadd_self_right`/`_left`) AND descent (strict
> monotonicity, `inadd_strict_mono`) at once — `zcOK_redAllExN` + `sord_redAllExN_lt` (`wip/PathCOmega.lean`,
> axiom-clean). The `ω`-tower is now isolated to **COMPOUND** cut formulas (∧/∨, rank-mixing). Remaining
> hardest-first: (1) general ∀-inversion `redInv∀` (re-principalize a non-ω-∀ left premise; `Zinfty.allInvAux`
> META template); (2) internal `iomegaTower` port (`Zinfty.omegaTower` → ε₀-codes via `iotower`) for the ∧/∨
> cases only. Then `red_iterate_descends` with `P = ZcOK ∧ derives ∅→⊥`, embedding (`hz`), arithmetization.

# NEXT STEPS — Path C (lap 104: endgame CORRECTED — datatype + inversion is `hinv`)

> **⭐⭐ LAP-104 CORRECTION (read FIRST — supersedes the lap-102/103 "complete `red` dispatch + `hdrop`"
> plan).** The lap-103 endgame `red_iterate_descends {P} (hinv) (hdrop) (hz)` is a TRUE conditional, but its
> `hinv` (orbit invariant `red`-closed) is **unsatisfiable for the naive dispatch-shaped `P`** — proven
> in-kernel this lap (`wip/PathCOmega.lean`: `naive_dispatch_P_not_red_closed`, `red_redAllEx_eq`,
> `sord_red_iterate_stalls_AllEx`, `zTag_ne_seven_of_ZDerivation`, all axiom-clean). The ∀/∃-cut reduct's
> new left premise `zsubst d0 a t` is a *substituted engine derivation* (tag ≤ 6, `zTag_zsubst`), never the
> stored-ω-∀ tag 7, so `red` is the identity on the reduct → the orbit STALLS after one step → no infinite
> descent. **The genuine `hinv` is the Hauptsatz**: `red` must RE-PRINCIPALIZE the reduct's premises via
> Schütte/Tait INVERSION (`redInv∀`/`redInv∧`/`redInv∨`), a recursion over the derivation that requires the
> genuine Path-C **derivation predicate (the datatype)**. **STOP adding `hdrop` cut-shape cases** (easy leaves
> on an unsatisfiable `hinv`). **START the datatype + inversion** (PRIORITY 1 below, rewritten). The lap-103
> bricks (ω-∀/ω-ind/cut/∃ nodes + `sord` Σ₁-def + per-step drops) stay valid and reusable.

## ▶ PRIORITY 1 (lap 104→) — the Path-C derivation predicate (`zcOK`) + inversion → `hinv`

Hardest-first ordering (each a `wip/` milestone; the datatype is the bottleneck — `hinv`, the embedding,
and arithmetization all need it):

1. **The datatype `zcOK : V → Prop`** — a small isolated Σ₁ `Deriv`-style predicate (NOT a new tag in the
   8000-line `InternalZ.zconstruction` Fixpoint — keep it isolated). Template: `InternalZ`'s
   `PR.Blueprint`/`Construction` Fixpoint pattern; rule set: `ZinftyF.Deriv` (the axiom-clean META ω-rule
   calculus in `src/Zinfty.lean`). Node shapes already coded (lap 102/103): ω-∀ (tag 7), ω-ind (8), cut (9),
   ∃ (10); ADD ∧/∨ intro + atom-axiom. Validity of a node = premises well-formed `zcOK` + conclusion-tracking
   + `∀ premise, sord(premise) ≺ sord(node)` (Buchholz operator-control; `sord` is Σ₁-def, lap 103).
2. **Inversion operators over `zcOK`.** `redInv∀ d t` / `redInv∧ d i` / `redInv∨ d`: from `zcOK d` deriving
   `Γ, A` (A = ∀x F / B∧C / B∨C) produce `zcOK` deriving the immediate subformula instance, stored ordinal
   `≼ sord d`. ∀-inv on the ω-∀-node itself = premise selection (banked `zAllOmega_cut_valid` /
   `zAllOmega_cut_descends`); the GENERAL case recurses through the derivation's last rule (the Schütte
   inversion lemmas, `Zinfty.lean` §19.2–19.4 are the META template — port the arithmetized version).
3. **`red` (Buchholz Def 3.2) calling inversion** + **`hinv`** (`red` preserves `zcOK`-of-∅→⊥: the reduct
   cut on `F(t)` has premises produced BY inversion, hence principal/`zcOK`) + **`hdrop`** (per-step stored-
   ordinal drop: bricks 1/3 for the principal selection + the inversion ordinal bounds). Then
   `red_iterate_descends` with the GENUINE `P` = `zcOK ∧ derives ∅→⊥`.
4. **Embedding (M2 analogue):** a Foundation/`ZDerivation` ⊥-proof yields a `zcOK` ⊥-derivation `z` (`hz`).
5. **Arithmetize** `red` (`sord`/`imax`/`zsubst`/projections/`zCutOmega` already Σ₁-def — compose) +
   `gentzenDescentφ` (Σ₁ graph of `n ↦ sord(red^[n] z)`) → discharge `gentzen_descent_of_inconsistent`
   (`wip/GentzenCon.lean`) from the V-internal descent + crux-1 PRWO. Then wire crux-1 ∘ crux-2 →
   `Reduction.goodstein_implies_consistency` → headline (ONLY when `#print axioms` clean — anti-fraud).

Build in `wip/` until step 5 lands; keep `InternalZ`/`Crux2Blueprint` (Path X) green in `src/` as fallback.

---

## (SUPERSEDED by lap 104 — lap-102/103 "complete the `red` dispatch" plan, kept for provenance)

> **⭐ LAP-102 UPDATE.** Probe 2 ran in `wip/InternalZomega.lean` (3 new axiom-clean lemmas).
> Verdict: the ω-rule (Path C) is the route, with a refinement — the chain/`redZKReady` motive is retired
> (proven by `Zinfty.lean`: full ω-cut-elim, no chain), BUT the ordinal layer must be **REPLACED, not
> reused**: `iotil_zK_iIndReduct_strictMono` proves the induction ω-node's premise ordinals strictly
> increase in depth, so its ordinal is a genuine LIMIT the computed `iord` (finite `#`-fold, no sup) cannot
> assign. Path C = **Buchholz operator-controlled derivations with STORED ordinals** (`ZinftyF.Deriv`/`o`
> shape, arithmetized). Path X (finitary `redZKReady`) is disfavoured AND likely broken (hereditary-Rep
> fails down a nested-chain spine — Cor 2.1 fires only at the ∅→⊥ top node). See
> `HANDOFF-2026-06-25-lap102.md` + the `wip/InternalZomega.lean` Probe-2 verdict.

## ▶ PRIORITY 1 (lap 102→) — the Path-C arithmetized stored-ordinal ω-derivation

**Foundations LANDED this lap (`wip/PathCOmega.lean`, all axiom-clean):**
- Brick 1 (full): `zAllOmega`/`zAllOmegaValidFull` (ω-∀-node + complete validity) +
  `zIall_realizes_zAllOmegaValidFull` (existing I∀ embedding realizes it, stored ord = its own `iord`).
- Brick 3 (kernel): `indOmegaStoredOrd` + `iord_iIndReduct_lt_storedBound` (the induction limit ordinal
  dominates every finite unfolding — the case the computed `iord` can't do).
- Brick 4 (skeleton): `stored_ord_iterate_descends` (the infinite descent from a per-step drop).
- **Endgame design fixed:** Path C uses Buchholz's single-step ordinal-DROPPING `red` (Def 3.2) + infinite
  ε₀-descent + PRWO(ε₀) — NOT Zinfty `cutElimStep` (raises the ordinal; meta-only). Bricks 1/3 ARE the
  per-node drops. This is the SAME descent shape as the finitary `Crux2Blueprint.iord_red_iterate_descends`,
  so the GentzenCon endgame (`gentzen_descent_of_inconsistent` ← `ord`/`R`/`ord_R_descends`) is the target.

**The remaining BUILD (deliberate, multi-lap) — the Σ₁ datatype + `red` + arithmetization:**
1. **Datatype.** The cleanest scope: the only genuinely-new node is the induction-as-ω-rule (the existing
   `zIall` already serves as the ω-∀-node — brick 1). Decide: (a) add ONE ω-node tag to the existing
   `InternalZ.zconstruction` Fixpoint (central, ripples through 8000 lines), vs (b) a fresh small Fixpoint
   for a Path-C derivation carrying stored ordinals as data. Lean toward (b) for isolation — a `Deriv`-style
   Σ₁ predicate `zcOK d` with node shapes {ω-∀, ω-ind, cut, axiom} each storing its ordinal, validity =
   premise codes + `∀-premise, sord(premise) ≺ sord(node)`. Template: `InternalZ`'s `PR.Blueprint`/
   `Construction` Fixpoint pattern; `ZinftyF.Deriv` for the rule set.
2. **`red` (Buchholz Def 3.2) on the datatype** — the single-step ordinal-dropping reduction. ∀-cut case =
   brick 1 (select witness, `zAllOmega_cut_descends`); induction case = brick 3 (unfold one step, ordinal
   drops by the limit bound). `sord` = the stored-ordinal projection.
3. **`ord_R_descends`** = assemble the per-node drops into `∀ d, ⊥-orbit d → icmp (sord (red d)) (sord d) =
   0`. Feeds `stored_ord_iterate_descends` (brick 4) → the infinite descent.
4. **Arithmetize `gentzenDescentφ`** (the Σ₁ graph `n ↦ sord (red^[n] d₀)`) + discharge the GentzenCon
   axiom `gentzen_descent_of_inconsistent` (`wip/GentzenCon.lean`) from the V-internal descent + crux-1
   PRWO. Then `gentzen_prwo_implies_consistency` (already proven modulo that axiom) closes crux-2.
5. **Wire** crux-1 ∘ crux-2 → `Reduction.goodstein_implies_consistency` → headline (only when `#print
   axioms` clean — anti-fraud).

Build in `wip/` until step 4 lands; keep `InternalZ`/`Crux2Blueprint` (Path X) green in `src/` as fallback.

---

## (SUPERSEDED by lap 102 — kept for provenance) lap-101 priorities

> Set by the lap-101 reflection. Supersedes the laps-95–100 "drive the `redZKReady` motive" plan as the
> default. Rationale: `REFLECTION-2026-06-25-lap101.md`. The destination (`𝗣𝗔 ⊬ Goodstein`, axiom-free) and
> the crux-2 target (`redSound`, internalized cut-elimination) are UNCHANGED. What changed is the sub-route
> call: the finitary-vs-ω-rule fork is reopened because lap-95's Path-X commitment skipped the de-risk
> spike lap-92 said to run first, and laps 95–100 relocated the wall rather than dissolving it.

## ▶ PRIORITY 1 — run the skipped de-risk spike (settles the fork)

**Target: `wip/InternalZomega.lean`** — a SELF-CONTAINED spike (NOT imported by `GoodsteinPA.lean`; cannot
affect the green gate). Goal: confirm in-kernel that the internal ω-rule cut-elimination is
substitution-free, so the finitary-vs-ω-rule decision is made on EVIDENCE.

Concretely (against the real `InternalZ` API):
1. **Define the internal ω-rule ∀-node** `zAllω s x h` — `s` the conclusion sequent `Γ→∀x F`, `h` a Σ₁
   CODE for the premise family. Premise-`n` := `zsubst h x (numeral n)` (reuse the axiom-clean `zsubst`;
   this is Buchholz §6 `Z*`: `h[n] = h₀(x/n)`). The validity predicate asserts `∀ n, ZDerivation
   (premise n) ∧ fstIdx (premise n) = seqSetSucc Γ F(n)` — i.e. the premise family is ASSUMED valid.
2. **Define the critical-cut reduct** on a cut `∀x F` (R-side `zAllω`) vs its L-side: the reduct SELECTS
   premise `t` (the cut term/witness) = `zsubst h x (numeral t)` = `premise t`. No NEW substitution in the
   reduction step (the `zsubst` lives in the premise-family DATA, where validity is given).
3. **State + try to prove the key lemma:** the reduct of a cut on `∀x F` is a `ZDerivation` whose
   conclusion is `tpReduce`-correct, with NO appeal to `ZDerivation_zsubst`/eigenvariable-substitution
   validity (contrast the finitary route, where O2 is the wall). Even getting this to ELABORATE (bodies
   sorried, signatures pinned against `InternalZ`) is the evidence: it shows IΣ₁ can express the ω-rule
   node + reduct.
4. **The sharp arithmetization-risk probe:** does cut-elimination recursion on `iord` work when the
   ∀-node's "size"/ordinal is a sup over the premise family? Check `iord (zAllω …)` is definable from the
   premise-family code (the repo's `iord`/ω-tower engine should supply `sup`/successor). If `iord` can't
   be assigned to the ω-node, that is the wall — and it justifies committing to Path X.

**Decision rule:** spike elaborates clean + reduct substitution-free + `iord` assignable → **PIVOT to
Path C** (rebuild the Z object theory on `zAllω`, retiring the finitary obligation list
motive/axNeg/Ind/5.1/5.2.1/ordinal-K at once; reuse the ordinal engine + `zsubst` + `Zinfty` template).
Spike walls on the Σ₁ arithmetization → **commit to Path X** with the evidence that finitary is the only
feasible internal route, and resume PRIORITY 2.

**Template to mirror:** `src/GoodsteinPA/Zinfty.lean` (the axiom-clean META ω-rule engine: `allω` rule +
the full Towsner §19 cut-elimination). The spike arithmetizes what `Zinfty` does at the meta level.

**STATUS (lap 101 — `wip/InternalZomega.lean`, 4 lemmas, all axiom-clean):**
- `zOmegaPrem_valid` — premise family uniformly valid, motive-free (freshness bound only).
- `zOmegaPrem_concl` — selected premise's conclusion computed, not threaded.
- `iord_zOmegaPrem` / `iord_zOmegaPrem_constant` — **Probe 1 RESOLVED**: premise-family ordinal is CONSTANT
  `= iord d0`, so the ω-node's `iord = iord d0 + 1` is finite — no sup-over-infinite-family primitive. The
  arithmetization-risk concern is retired.

- `iord_descent_zOmegaPrem` — the ω-rule ∀-cut reduction strictly descends (`iord d0 ≺ iord (zIall …)`),
  UNIFORMLY in the witness `t`; with `zOmegaPrem_valid` = the full per-step cut-elimination invariant
  (validity + descent) on the existing nodes.
- `zIall_realizes_omega` — capstone: a regular `zIall` realizes the full ω-node (premise family valid +
  conclusion-tracked + uniform ordinal), so the existing I∀ embedding is reused wholesale.

**NET CALL (honestly scoped): the evidence favours the Path-C pivot, with one decisive probe left.**
SETTLED in-kernel: the ω-rule ∀-NODE arithmetizes (premise validity motive-free, conclusion computed,
ordinal finite, node realizable from regular `zIall`, per-step ∀-cut descent) — the lap-92 "riskiest
assumption" is retired, all on the existing engine, axiom-clean. NOT yet settled: the actual crux-2 wall is
the **chain (`zK`) cut-elimination on the ⊥-orbit** (`ZDerivesEmpty` is Ind-or-chain; `redZKReady` is a
CHAIN obligation). The ∀-node is necessary infrastructure, not the chain itself. The lap-92 claim — that the
ω-rule's premise-selection ALSO dissolves the chain's conclusion-tracking motive — is plausible and
supported by the ∀-node result, but the chain is unprobed.

**NEXT = Probe 2: the ⊥-orbit Ind/chain ω-rule reduct (the node that actually walls).** Buchholz §6:
induction (`zInd`) becomes an ω-rule node (premises `F(0), F(1), …` from iterating the step); the chain's
repetition is absorbed into the ω-rule. Define the ω-rule reduct of an Ind/chain ⊥-orbit node and check it
avoids the `redZKReady` hereditary-Rep motive — the direct analogue of this lap's ∀-node result, on the
node that walls. This is the decisive test before a full commit. If it dissolves the motive (as the ∀-node
result predicts) → commit to the rebuild (`zAllω` tag 7 in the `zconstruction` Fixpoint, `ZPhi` disjunct =
ω-rule validity derivable via `zIall_realizes_omega`, `iord = iord d0 + 1`, Schütte/Tait recursion templated
by `Zinfty.lean`). If it walls → fall back to Path X (the finitary motive) with the evidence. ~2–3k-line
rebuild either way for the full pivot.

## ▶ PRIORITY 2 — Path X fallback (ONLY if the spike walls)

Resume the laps-95–100 plan, now informed: drive the `redZKReady` motive (`Crux2Blueprint.redSoundGen`
K-case `sorry`). First sub-lemma: `redZKReady_of_emptyAnt_botSucc` (∅→⊥ special case). The open core is
the hereditary Rep-reduction `fstIdx (red dᵢ) = fstIdx dᵢ` down the selected-premise spine — **but first
settle whether it even holds**, given ∅→⊥ chain premises have growing antecedents `{A₀..A_{i-1}}→Dᵢ` (so
Cor 2.1 does not directly reapply). If it does not hold as stated, the motive must track a different
invariant — which is itself evidence for the Path-C pivot. Then: axNeg ¬-cut, `zKValidF_iIndReduct_of_zInd`
(Ind), `ZDerivation_red_zK_crit` (5.1), `ZDerivation_red_zK_splice` (5.2.1), `iord_descent_red` (ordinal K).

## ▶ PRIORITY 3 — path-independent downstream (no-regret, either route)

These are needed regardless of finitary/ω-rule and can advance in parallel once the Z object theory is
stable. They consume the SHAPE of `ZDerivation`/`ZDerivesEmpty`/`iord`, so do them AFTER the fork is
settled (a Path-C pivot reshapes `ZDerivation`):
- **M2 `foundation_bot_to_Z_empty`** (`Crux2Blueprint`) — the Bryce–Goré `Peano.v` Foundation→Z bridge
  (the PA-induction axiom maps to Z's native `Ind`). ~1k-line milestone.
- **M3 `false_of_ZDerivesEmpty`** (`Crux2Blueprint`) — internalize the descent `n ↦ iord (red^[n] z)` as
  a Σ₁ graph + apply `PRWO(ε₀)` (from crux-1). Plumbing; structure is path-independent.
- **Wire** `Crux2Blueprint` M1b∘M2∘M3 → `Reduction.goodstein_implies_consistency` → headline (only when
  `#print axioms` is clean — anti-fraud).

## Faithfulness invariant (do NOT regress)
Headline stays a bare `sorry` until `#print axioms peano_not_proves_goodstein` is trust-base only. Never
introduce an `axiom` for the ordinal-analysis girder. Keep `goodsteinSentence_faithful` axiom-clean.
