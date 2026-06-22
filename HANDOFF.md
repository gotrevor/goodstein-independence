# HANDOFF — 2026-06-22 (lap 11)

> **Branch** `plan` · **HEAD** `bb0488e` (+docs after) · 5 commits this lap · build **green**
> (`lake build GoodsteinPA`, 1258 jobs) · headline `peano_not_proves_goodstein` = honest `sorry`
> (0 math axioms) · working tree clean.
> **Lap 11 COMPLETED M4 — the embedding (the 8-lap universal bottleneck) — and promoted it to
> `src/`. The headline gap is now isolated to exactly TWO typed obligations (B1 + the bridge).**

## 🎉 M4 — the embedding `embedC` — COMPLETE & axiom-clean (`src/GoodsteinPA/Embedding.lean`)
`embedC : Derivation2 (𝗣𝗔:Schema) Γ → ∃ c, ∀ e:ℕ→ℕ, ∃ α, Provable α c (Γ.image (asg e ▹))`.
`#print axioms embedC = [propext, Classical.choice, Quot.sound]` (no sorryAx, no math axioms). In
the default build (added to `src/GoodsteinPA.lean` root import). The two non-structural cases:
- **`exs`** (∃-intro, open witness `t`): `Provable.exI_closed` collapses the closed term `asg e ▹ t`
  to its numeral value via the **value-congruent EM** `provable_em_cong_gen` (arity-general; atomic
  leaves close by `axTrue` on value-equal arg vectors, quantifiers via `allω`/`exI` with the
  `subst_q_cons_app` substitution-composition identity) + one `cut`, then numeral-`exI`.
- **`axm`** (PA axiom `↑σ`): **ω-completeness** `provable_true` — every closed formula TRUE in ℕ is
  `Z∞`-derivable cut-free (induction on complexity). Since `ℕ ⊧ₘ* 𝗣𝗔`, every axiom is true. The
  ω-rule subsumes the Buchholz §5.5 meta-induction ENTIRELY — no induction-scheme special-casing.

Reusable axiom-clean assets now in `src/Embedding.lean`: `provable_em`, `provable_em_cong_gen/_cong`,
`Provable.exI_closed`, `provable_true`. (Superseded naive `embed`/`provable_rew` dropped on
promotion; history in `wip/Embedding.lean`.)

## 🎯 NEXT LAP — the bounding bridge + B1 (`wip/Bounding.lean` — the assembly is scaffolded)
`peano_not_proves_goodstein_routeB` (in `wip/Bounding.lean`) is **PROVED modulo two disclosed
sorries** — it wires the whole Route-B chain (embedC → cutElim → `omegaTower_lt_epsilon0` →
bridge). The headline reduces to:

1. **B1 — `embed_lt_eps0`** (the easier, paper-independent one — START HERE): `embedC` but with the
   ordinal `α < ε₀`. This is a refinement of `embedC` that tracks the ordinal through the structural
   induction. **The one subtlety:** the `all` case introduces `allω` whose ordinal is `(⨆ₙ βₙ)+1`;
   need the `βₙ` UNIFORMLY bounded `< ε₀` (they are — the sub-derivation SHAPE is the same for every
   numeral `n`, only the assignment differs, and the ordinal depends only on shape). Likely cleanest:
   restructure `embedC` to return a *uniform* ordinal bound independent of the assignment `e`, OR a
   bound `β(d)` computed from the `Derivation2` structure with `β(d) < ε₀` provable separately. Also
   needs: `provable_em`'s and `provable_true`'s ordinals are `< ε₀` (they are — complexity-bounded
   `allω` towers, `< ω^ω`). **Attack:** strengthen the `embedC` statement to `∃ α, α < ε₀ ∧ Provable
   α c …` and re-run the induction, discharging each case's ordinal-`< ε₀` side goal (use
   `omega0_opow_lt_epsilon0`, sups of `<ε₀` families bounded via `Ordinal.iSup_lt`/principal-`ε₀`).

2. **The bridge — `cutfree_lt_eps0_absurd`** (B2–B5, the deep arithmetization core): no cut-free
   `Z∞` derivation of `{↑goodsteinSentence}` has ordinal `< ε₀`. ⚠️ **`↑gs` is TRUE so it DOES have
   a cut-free derivation (`provable_true`) — the contradiction is the ORDINAL `< ε₀`, not existence.**
   Sub-pieces (see PENDING_WORK):
   - **B2** cut-free ∀/∃ witness bound on the real `Deriv`: invert the outer `∀` (`Provable.allInv`,
     already in M5) per numeral `m`; bound the Σ₁ `∃N` witness by a Hardy `H_α(m)` (Towsner
     boundedness lemma — needs reading `papers/`).
   - **B3** arithmetization (M7a): the Σ₁ `codeOfREPred goodsteinTerminates` matrix ↔ the semantic
     `atomTrue m N` (`goodsteinSeq N m = 0`) used by M6. THE intractability-risk piece.
   - **B4** ordinal seam: mathlib `Ordinal < ε₀` ↔ `ONote` NF (mathlib `ONote`/`Ordinal.lt_epsilon`).
   - **B5** assembly vs `lowerBound_hardy_selfcontained` (M6, `hardy_lt_goodsteinLength`).

## State of the spine (Route B)
- **M1, M2, Phase 0/1** — done, clean.
- **M4 embedding** (`src/Embedding.lean`, `embedC`) — **DONE this lap, axiom-clean, in the build.**
- **M5 ε₀ cut-elim** (`src/Zinfty.lean`, `Provable.cutElim`, `omegaTower_lt_epsilon0`) — done, clean.
- **M6 Hardy lower bound** (`src/LowerBound.lean`, `lowerBound_hardy_selfcontained`) — done, clean.
- **M7 bridge + assembly** (`wip/Bounding.lean`) — assembly SCAFFOLDED (proved mod B1 + bridge).

## Notes
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`, headline `sorry` intact.
- **Aristotle:** the `em_cong` job submitted this lap was CANCELLED (solved locally). Feed a bounded
  open lemma when one arises (e.g. a self-contained B1 ordinal-sup-`<ε₀` fact, or a B4 ONote bridge).
- **`WebFetch` dead; `WebSearch` works.** No open `ON-LINE-REQUEST.md`. For B2/B3 ground in `papers/`
  (Towsner; `papers/SOURCES.md`) — request via `ON-LINE-REQUEST.md` if a specific bound is missing.
- **Build:** `lake build GoodsteinPA` (1258); test wip via `lake env lean wip/Bounding.lean`.
- **Reference corpus** (`~/personal/claude/knowledge/.../lean-journey/reference/`): `grep -rl` first.

## Lap-11 commits
- `861d490` embedC exs PROVED (value-congruent EM ⟹ closed-term ∃-intro), 9/10.
- `86ed9ec` embedC axm PROVED via ω-completeness → M4 COMPLETE 10/10.
- `ff49e3b` promote embedC to `src/GoodsteinPA/Embedding.lean` (in the verified build).
- `bb0488e` Route-B assembly scaffold (`wip/Bounding.lean`) — gap isolated to B1 + bridge.
