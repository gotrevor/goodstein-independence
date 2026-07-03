# HANDOFF — 2026-06-22 (lap 6)

> **NEXT LAP FIRST ACTION:** read this + `STATUS.md` + `PENDING_WORK.md` (step 1).
> Build is **green** (`lake build GoodsteinPA`, 1257 jobs). `wip/BoundedZinfty.lean` compiles
> standalone (`lake env lean wip/BoundedZinfty.lean`). Headline still a literal `sorry` (anti-fraud).

## What landed this lap (8 commits, all verified green / axiom-clean)

1. **M6 lower-bound half DONE.** Promoted `wip/LowerBoundHardy.lean → src/GoodsteinPA/LowerBound.lean`
   (+ lib root). `lowerBound_hardy_selfcontained` = **full Towsner Thm 17.1, no hypotheses beyond
   `α.NF`** (`Hdom` discharged via the ported Goodstein-dominates-fastGrowing chain + the `+2`→strict
   iterate split). `#print axioms` = `[propext, choice, Quot.sound]` + 12 🟢 `native_decide` Goodstein
   base-case `ax_*` (acceptable indefinitely). `lowerBound_hardy`/`lowerBound_existential_hardy` clean.

2. **Step-1 keystone built: `wip/BoundedZinfty.lean`** — the **witness-bounded `Z_∞` calculus `Zᵏ`
   over real `SyntacticFormula ℒₒᵣ`** (ONote-indexed, B-style/no-suprema). It adds to the M5 calculus
   the two Towsner §15 side conditions the lower bound needs (lap-4 finding): truth-atom rules
   `trueRel`/`trueNrel` (`norm α < k`) + `∃`-witness bound (`exI` carries `n ≤ hardy α k`); plus a
   height-preserving `wk`, a β<α `weak`, and `∧`/`∨`/`cut`. **Everything below is axiom-clean:**
   - structural: `mono_k`, `mono_c`, `wk`/`weakening`;
   - **full inversion suite §19.2–19.4**: `orInv`, `andInvL`, `andInvR`, `allInv` (the ∀-inversion is
     the bound-critical one — it's what the subformula bridge to `B` will consume; it ports `B.allInv`
     + the principal/non-principal `all_inj` split, juggling `max(max k n)n₀ = max(max k n₀)n`);
   - **§19.5 ∧/∨ cut-reductions**: `cutReduceConj`, `cutReduceDisj` + `lt_osucc`. Both connectives
     invertible ⇒ no fresh induction; caller supplies an NF upper bound `δ` (with `norm δ < k`), result
     at `osucc δ`. No natural sum needed.
   - **Friction solved:** inline `simp; tauto` over `Finset Form` blows the heartbeat limit (formula
     `DecidableEq` is expensive). Fix: factor every reshuffle into a **standalone** helper
     (`invPush`/`invPull`/`invPush2`/`inv1Push`/`inv1Pull`/`inv1Push2`/`princOrSub`/`princAllSub`).

## The next girder — §19.6 ∀/∃ cut-reduction (the hardest cut-elim piece) → then `cutElimStep`/`cutElim`

`cutReduceAllAux` (port `src/Zinfty.lean:785`). The ∃ is **not invertible**, so: invert the ∀-side once
(`allInv` → numeral family), then **induct on the ∃-side derivation**, cutting at the witness numeral in
the principal `exI` case. Parameter-style design (worked out this lap, ready to execute):
- **Bound framing = `α + γ`** via `ONote.add`: `add_nf` instance gives NF; `repr_add` +
  `Ordinal.add_lt_add_left` give strict monotonicity in `γ` (the premise-`<` conditions as you descend).
- **Principal `exI`** (∃-side introduces `∃⁰∼φ` at witness `n`): cut `fam n` against the ∃-premise on
  `φ/[nm n]` (complexity `< c`). The witness cut.
- Non-principal cases mirror the inversions; src frames the running sequent as `Δ.erase (∃⁰∼φ) ∪ Γ`.

Then **`cutElimStep` (§19.7, `c+1→c`, bound `ω^α = oadd α 1 0`)** + **`cutElim` (§19.9)**.

⚠️ **KEY FINDING (lap 6) — the `norm<k` budget grows under ordinal addition.** Machine-checked:
`norm ω = 1` but `norm (ω+ω) = 2` (addition merges equal-exponent CNF coefficients). So my earlier
"`norm(α+γ) ≤ max`" was WRONG. The accurate picture:
- **§19.7 `ω^α` blow-up is SAFE** — `norm(ω^α) = max(norm α, 1)` (machine-checked `norm_omegaPow`),
  coefficient stays 1, so the ω-tower never bumps the budget (`k ≥ 2`).
- **§19.6 within-rank addition is where `norm` grows.** The ω-rule combines by *supremum* (no sum),
  only the §19.6 cut-combination (∀-family + ∃-side) adds — finitely many times — so the growth is
  bounded and a large `k` (chosen at embedding) plausibly absorbs it. **The precise bookkeeping needs
  Towsner §17–§19 — `ON-LINE-REQUEST.md` filed this lap.** Do NOT claim cut-elim closed until pinned.
- Banked helpers: `lt_osucc`, `add_lt_add_left_NF`, `le_add_left_NF`, `norm_omegaPow`. (Natural sum
  would NOT help — it merges coefficients identically.)

## Then the rest of the 5-step spine (see `ANALYSIS-2026-06-22-bounding-resolution.md` §"M4 scoping")
- **Step 2 — M4 embedding** `PA ⊢ φ ⟹ Zᵏ ⊢^{α,k}_c φ` (Foundation-heavy; reuse finitary `Derivation`,
  `∀`→ω-rule, finite induction instances ⟹ finite cut rank). The genuinely-doubtful girder.
- **Step 4 — subformula bridge**: a cut-free `Zᵏ`-derivation of `{gAll}` has only `GForm`-subformulas
  ⇒ it IS a `B`-derivation ⇒ contradicts `lowerBound_hardy_selfcontained` (M6, done). Consumes `allInv`.
- **M7a — language gap** (Towsner Remark 10.3): `goodsteinSentence = ∀⁰(codeOfREPred …)` is opaque Σ₁,
  not the transparent `∀x∃y g_y(x)=0` the bridge needs. Build a transparent `gAllReal` + `𝗣𝗔 ⊢
  goodsteinSentence ↔ gAllReal` (gated by `Bridge.lean`'s spec). The other hard girder besides M4.

## Notes
- **Cross-session (O3):** `~/src/Foundation-delta1-burndown` is discharging `PA_delta1Definable` upstream
  (Route-A fallback de-risk). Don't duplicate. We stay on Route B; it doesn't redirect us.
- **Aristotle:** reachable this lap, left idle — the remaining work (Zᵏ cut-elim, M4 embedding) is
  Foundation-heavy / not self-containable. A clean future target: the §19.6 witness-cut sub-lemma once
  the ONote-add framing is in place, or the `norm`-preservation lemmas.
- **Time-to-finish estimate** (asked this lap): ≈15–25 laps; dominant risk in M4 + M7a.
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`. Headline `sorry` intact.

## File map
- `src/GoodsteinPA/{Defs,Encoding,Bridge,Statement}.lean` — Phase 0 (headline `sorry`). LOCKED bits.
- `src/GoodsteinPA/{Computability,Reduction}.lean` — M1 (clean) + M2 (Gödel II hook).
- `src/GoodsteinPA/Zinfty.lean` — M5 cut-elim, unbounded `(α,c)` over real `ℒₒᵣ` (the strategy `Zᵏ` ports).
- `src/GoodsteinPA/{Hardy,Domination}.lean` — Hardy hierarchy + Goodstein domination (terminal assets).
- `src/GoodsteinPA/LowerBound.lean` — **M6, NEW lap 6**: self-contained Thm 17.1. Terminal asset.
- `wip/BoundedZinfty.lean` — **step-1 keystone, NEW lap 6**: `Zᵏ` + §19.2–19.5. Continue §19.6 here.
- `wip/{WitnessBound,GoodsteinLength,FastGrowing,Zinfty}.lean` — earlier scaffolding (history; keep).
