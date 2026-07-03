# HANDOFF — 2026-06-23 (lap 31, **reduct→𝗜𝚺₁ bridge + equality fully scoped + X-cong matrix proved**)

> **Branch** `plan` · HEAD = `3ba2727` · build **green** (`lake build GoodsteinPA`, **1304 jobs**) ·
> headline `GoodsteinPA.peano_not_proves_goodstein` = honest `sorry` (anti-fraud intact). **Tree clean.**

Durable overview = **`STATUS.md`**. Attack map + corrections = **`PENDING_WORK.md` lap-31 top** (read
FIRST) + **`ANALYSIS-2026-06-23-lap31-equality-architecture.md`**. Lone wall unchanged:
`DescentSemantic.no_min_descent_absurd_of_goodstein`.

## Lap-31 deliverables (3 new green, axiom-clean `[propext, choice, Quot.sound]`)
1. **`ReductModel.lean`** (`a8211c3`) — `M ⊧ paLX` ⟹ its `ℒₒᵣ`-reduct is `[ORingStructure M][M ⊧ₘ* 𝗜𝚺₁]`
   (the `igoodstein` substrate carrier), given `[Structure.Eq LX M]`. `reductORing`,
   `reduct_eq_standardModel` (via `standardModel_unique`), `reduct_models_PA`/`reduct_models_isigma1`.
2. **Equality architecture FULLY SCOPED** (`e601c48` + ANALYSIS doc). The Tait calculus has NO equality
   rules ⟹ completeness gives non-`Eq` models ⟹ substrate (needs real `=`) blocked unless `𝗘𝗤 ⪯ paLX`.
   EXACT gap = ONE axiom: **X-congruence `Eq.relExt Xsym`** (`𝗘𝗤(ℒₒᵣ)` already rides in `lMap Φ 𝗣𝗔⁻`).
3. **`XCongruence.lean`** (`3ba2727`) — the genuinely-new embedding obligation, per-numeral core PROVED:
   - `litTrue_eq_iff`: lifted `=`-atom at numerals is ℕ-true iff `m = n`.
   - `pxfc_xcMatrix`: cut-free `XFreeAx`-safe `PXFc` derivation of `[m≠n, ¬X(m), X(n)]` ∀`(m,n)`
     (`m=n` → `PXFc.axLv Xsym`; `m≠n` → `PXFc.axTrue`). The crux of Task A1.

## NEXT (resume here, hardest-first)
**TASK A1 — finish + wire the X-congruence discharge (continues `XCongruence.lean`):**
1. Assemble the full discharge from `pxfc_xcMatrix`: `↑(Eq.relExt Xsym) = ∀⁰* (↑σ)` (`emb_allClosure`
   `@[simp]`), `asgX e ▹ (↑sentence) = ↑sentence`, then `PXFc_allClosure` (strip the 2 `∀⁰*` vars,
   `v : Fin 2 → ℕ ↦ (m,n)`), giving `∃ c, ∀ e, ∃ α, PXFc α c (Γ.image (asgX e ▹ ·))` when
   `↑(Eq.relExt Xsym) ∈ Γ`. Need: `Rew.subst (nm∘v) ▹ (↑σ) = xcMatrix (v 0) (v 1)` (DSL bookkeeping —
   the `Matrix.conj` over `Fin 1` is a single conjunct; `🡒`/NNF unfolds to `nrel Eq ⋎ (nrel X ⋎ rel X)`).
2. Augment `paLX` to include `𝗘𝗤` (or just `Eq.relExt Xsym`); extend `hax_paLX` (`EmbeddingX.lean:744`)
   with the X-cong branch using step 1. Then `peano_not_proves_TI` re-validates (the `α`/cut bound is
   unchanged; only the `hax` axiom set grew by one). **6-file blast radius** — do in one green push.
**TASK A2 — completeness plumbing:** add `[Structure.Eq LX M]` to `paLX_models_TI_of_PA_provable`;
re-route `descentE` via `EQ.provOf` (now `𝗘𝗤 ⪯ paLX` holds) + `completeness_of_encodable` +
`Semiformula.toEmpty` of `TI prec` (`emb_toEmpty`) + `provable_iff_derivable2` → `Derivation2`.
**Then the deep walls (route-neutral):** B (opaque `codeOfREPred` ↔ `igoodstein`, IΣ₁-internal), C
(M-internal descent from `no_min` via LX least-number), D (slow-down `βₖ` + internal `ineq6`).

## LOCKED untouched (anti-fraud)
`Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`, headline `Statement.lean` `sorry`.

## src/ code sorries (3, unchanged)
`Statement.lean` (headline, locked), `Reduction.lean:50` (Route-A hook, off path),
`DescentSemantic.no_min_descent_absurd_of_goodstein` (**THE wall**, disclosed). New bricks sorry-free.

## Aristotle
Idle/correct. Task-A1 step 1 (the `subst ▹ ↑σ = xcMatrix` DSL equation) could be a self-contained
Aristotle lemma once isolated; not yet.
