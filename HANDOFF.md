# HANDOFF — 2026-06-22 (lap 10)

> **Branch** `plan` · **HEAD** = latest (8 commits this lap) · build **green**
> (`lake build GoodsteinPA`, 1257 jobs) · headline `peano_not_proves_goodstein` = honest `sorry`
> (0 math axioms) · working tree clean.
> **Lap 10 closed the truth-layer gap: the M5 `axTrue` surgery is DONE — `Z∞` now has the
> atomic-truth axiom + a truth-layer cut-elimination, axiom-clean. M5 can now host the embedding.**
> Read `ANALYSIS-2026-06-22-truth-layer-gap.md` for context, then "NEXT LAP" below.

## 🎯 NEXT LAP — the assignment-carrying (all-closed) embedding
The surgery exposed that the *naive open* embedding is the wrong frame: `provable_rew` (renaming
invariance) is **false for `axTrue` with open literals** (`ω ▹` can flip a true-under-`id` literal to
false). The fix — needed for `exs` ANYWAY — is the **assignment-carrying embedding**, where every
sequent is CLOSED:

```
embed : Derivation2 (𝗣𝗔:Schema) Γ → ∀ e : ℕ → ℕ, ZProvable (Γ.image (ρ e ▹))
   where  ρ e := Rew.rewrite (fun x => nm (e x))   -- closes all free vars to numerals
```
Headline use: `↑goodsteinSentence` is closed, so `ρe ▹ ↑gs = ↑gs`; `embed d (fun _=>0)` gives
`ZProvable {↑gs}`. Under this form (all literals closed):
- **structural cases** (closed/verum/and/or/wk/cut): re-prove (mechanical, `ρe` distributes over
  connectives; the 8 done naive cases port).
- **`all`**: `allω` with the numeral-extended assignment `n :>ₙ e` — the freed var ↦ `nm n`, the
  shifted `Γ` ↦ `ρe`-image. (Like the lap-10 `all` proof but via the assignment, NOT `provable_rew`.)
- **`shift`**: re-index the assignment (`ρe ∘ shift = ρ(e∘succ)`) — no `provable_rew`.
- **`exs`**: `ρe ▹ t` is now CLOSED → collapse to its numeral value `nm m` (the `axTrue` closed-term
  evaluation) → `Provable.exI … m`.
- **`axm`**: closed PA axiom `↑σ` (assignment-immaterial). `σ ∈ 𝗣𝗔⁻ ∪ InductionScheme`:
  - `𝗣𝗔⁻` (finite): strip `∀` via `allω` → each closed instance is a true atomic → **`Provable.axTrue`**.
  - `univCl(succInd ψ)`: the worked meta-induction (PENDING_WORK lap-10) — `cut`/`exI`/`andI`/
    `provable_em`, with the `nm n+1 = nm(n+1)` step now closed by **`axTrue`** (`removeFalseLit`/atomic).
`provable_rew`/`ZProvable.rew`/naive `shift`+`all` (`wip/Embedding.lean`) are **superseded** by this
closed form (kept for reference; `provable_rew` now carries a disclosed `sorry` on its `axTrue` case).

## ✅ The M5 `axTrue` surgery (lap 10, COMPLETE, committed, axiom-clean)
`src/GoodsteinPA/Zinfty.lean`. Added the ω-logic atomic-truth leaf + truth-layer cut-elim:
- `signedLit b r v` (Bool-signed literal), `LitTrue` (ℕ-truth), `litTrue_neg`/`_or_neg`/`_flip`.
- **`Deriv.axTrue`** constructor (`o=cr=0`) + `Provable.axTrue` smart constructor.
- Threaded all 9 recursion sites (`o`, `cr`, `orInvAux`, `allInvAux`, `andInvAux`, `cutReduceAllAux`,
  `removeFalsumAux`, `cutElimStepAux`, `atomCutAux`).
- **`removeFalseLitAux`**: remove any FALSE closed literal from a cut-free derivation (truth layer).
- **`atomCutAux`**: splits on `litTrue_or_neg` of the cut atom (true ⟹ `removeFalseLitAux` the false
  `∼`-side off `hNC`; false ⟹ existing set-idempotence).
- `#print axioms Provable.cutElim = [propext, Classical.choice, Quot.sound]` — NO `sorryAx`, NO math
  axioms. M5 stays clean (`Classical.choice` already in the ledger). `LowerBound` untouched.

## ✅ Lap-10 results (all committed, green)
1. **`rew_subst_nm` PROVED** (`9531777`) → the M4 enabler `provable_rew` + `ZProvable.rew` are now
   **fully axiom-clean** (`[propext, choice, Quot.sound]`, 0 math axioms). `wip/Embedding.lean`.
2. **`embed` `shift` + `all` PROVED** (`6eb1f03`) → **8/10 cases** (only `axm`, `exs` remain).
   - `shift` = `ZProvable.rew Rew.shift`.
   - `all` = the **ω-rule case**: `provable_rew` substitutes the freed var by each `nm n` (which
     simultaneously undoes the `shift` on `Γ` via `Rew.rewrite_comp_shift_eq_id`), then `Provable.allω`.
3. **ANALYSIS — the truth-layer gap** (`624933e`): `ANALYSIS-2026-06-22-truth-layer-gap.md`. The
   finding (grounded in the code): every PA axiom embedding (`axm`) bottoms out at **true closed
   atomics** (`nm n + 0 = nm n`; and the successor bridge `nm n + 1 = nm(n+1)`). M5's `Deriv` is pure
   logic — only atomic leaf is `axL` (both polarities); its atomic cut-elimination is **deliberately
   truth-free** (header line 15, `atomCutAux` docstring). Adding a one-polarity `axTrue` breaks that.
   The sibling `LowerBound.B` calculus **already has `trueR`**, and the planned bounding bridge maps
   `Deriv` leaves to `B.trueR` — so the architecture already presupposes `axTrue` on `Deriv`.
4. **M5 `axTrue` surgery COMPLETE** (see below) — `Z∞` now hosts the embedding, axiom-clean.

## State of the spine (Route B, two-phase)
- **M1, M2, Phase 0/1** — done, clean. M1 (`Encoding.goodsteinTerminates_re` → `Computable bump`) is
  **already discharged** (`Computability.lean` sorry-free) — the operator's "discharge M1" is done.
- **M5 — ε₀ cut-elim + truth layer** (`src/Zinfty.lean`) — done, clean. The lap-10 `axTrue` surgery
  added the ω-logic atomic-truth leaf so M5 now hosts the embedding (was pure-logic before).
- **M6 — Hardy lower bound** (`src/LowerBound.lean`, `lowerBound_hardy_selfcontained`) — done, clean.
  Uses the **separate** abstract `B` calculus (which already has `trueR`); untouched by the surgery.
- **M4 — embedding** (`wip/Embedding.lean`) — enabler axiom-clean; 8/10; `axm`/`exs` blocked on the
  surgery. **`provable_em` still promotable to `src/Zinfty.lean`** (axiom-clean, lap-9).
- **Bounding bridge + assembly (M7b)** — downstream.

## Notes
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`. Headline `sorry` intact.
- **`WebFetch` dead; `WebSearch` works.** No open `ON-LINE-REQUEST.md`.
- **Aristotle:** idle is correct — the surgery is over M5's real `Deriv` internals (not cleanly
  self-containable). Feed only a genuinely-bounded isolated lemma if one arises.
- **Reference corpus** (`~/personal/claude/knowledge/core/projects/lean-journey/reference/`):
  `goodstein-independence-landscape.md`, the ONote/Hardy gotcha files. `grep -rl <keyword>` first.
## Lap-10 changes (8 commits)
- `src/GoodsteinPA/Zinfty.lean` — **`axTrue` truth-layer surgery** (the headline): `signedLit`/
  `LitTrue`/duality, `Deriv.axTrue` + `Provable.axTrue`, 9 sites threaded, `removeFalseLitAux` +
  `atomCutAux` truth split. Green, axiom-clean (`cutElim = [propext, choice, Quot.sound]`).
- `wip/Embedding.lean` — `rew_subst_nm` proved; `embed` naive `shift`+`all` proved (now SUPERSEDED by
  the assignment form); `provable_rew` carries a disclosed `sorry` on its `axTrue` case (the pivot).
- `ANALYSIS-2026-06-22-truth-layer-gap.md` — NEW (the finding + resolution; now executed).
- `wip/ZinftyTrue.lean` — created then **promoted into `src/` and removed** (content lives in Zinfty).
- `PENDING_WORK.md` — lap-10 block (worked `axm` paper proof + truth-layer gap). Update for the
  assignment-form pivot next.
- `STATUS.md` / `HANDOFF.md` — refreshed. Build green (1257), headline `sorry` intact.
