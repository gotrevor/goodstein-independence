# SPIKE W3 — VERDICT

> Deciding experiment #1 of `MASTERPLAN-2026-07-01-ZERO-AXIOMS.md` §5 (W3). One bounded session.
> Deliverable: typed skeleton `wip/SpikeW3Embedding.lean` + this verdict. See `SPIKE-W3-STATEMENT.md`.

## Verdict: **PASS — conditional on ONE mandatory, banked-feasible amendment.**

The candidate master statement + all ten `Derivation2` rule-case lemmas **elaborate** (build green,
sorries disclosed), and the master theorem is assembled from them by a **real, non-`sorry`
induction**. The witness-budget discipline **survives the global embedding induction** — but the
candidate signature's quantifier placement (`∃ α e` and the `∃ K` of `ZekdSomeK`, both *inside*
`∀ env`) **cannot drive the ω-rule (`all`) case**. The fix is a quantifier/structure re-placement —
hoist the *base* control ordinal `e`, the family's uniform `< ε₀` bound, and the *base* witness
index `K` **out** of `∀ env` (structural), letting only the **running index** `max K n` depend on
the ω-branch. This is exactly the discipline the calculus was built for (banked at the leaf), so it
is a **designable amendment, not a wall**: **trigger T-W3 does NOT fire.**

## What was built (evidence)

`wip/SpikeW3Embedding.lean` — builds under the repo toolchain (`lake env lean wip/SpikeW3Embedding.lean`):

- `def BudgetedEmbeds Γ` — the candidate master body verbatim:
  `∃ c d₀ : ℕ, ∀ env, ∃ α e : ONote, α.NF ∧ e.NF ∧ ZekdSomeK α e d₀ c (Γ.image (asg env ▹ ·))`.
- **10 named `sorry`ed case lemmas**, one per `Derivation2` constructor (mirrors `embedC`'s split
  exactly): `closed, axm, verum, and, or, all, exs, wk, shift, cut`. Each stated with the SAME
  budget discipline (conclusion `BudgetedEmbeds`, IHs `BudgetedEmbeds`).
- **`theorem budgetedEmbedding`** — the candidate signature verbatim, body `show BudgetedEmbeds Γ`
  then a real `induction d with …` whose every arm is a single `exact` into the matching case lemma.
- Disclosed axioms (real `#print axioms`, in-file):

  ```
  'GoodsteinPA.SpikeW3.budgetedEmbedding' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
  ```

  → `sorryAx` + the 3 canonical only. **No new `axiom` declarations anywhere.** No LOCK file, no
  `DIRECTION.md`, no `Zekd`/`ZekdSomeK` redesign was touched.

That the assembly *elaborates* is the spike's positive result: the master statement is **coherent
under the global induction** — every case's IH shape matches its case lemma's hypothesis shape, so no
rule structurally rejects the budget at the type level.

## Per-case disposition (mechanical vs hard)

| Case | Verdict | Discharging machinery (all banked in `OperatorZinfty`) |
|---|---|---|
| `closed` | mechanical | `ZekdSomeK.axL` (atomic) / `embedding_valueCongruentEM_probe` (general EM) |
| `verum` | mechanical | `ZekdSomeK.verumR` |
| `and` | mechanical | `ZekdSomeK.andI` (+ `mono_c/mono_d` budget align; `mono_e` to unify the *two* sub-`e` — finite, trivial once `e` structural) |
| `or` | mechanical | `ZekdSomeK.orI` |
| `exs` | mechanical | `embedding_closedTermExI_someK_probe` (closed-term collapse; witness value absorbed into `∃ K`) |
| `wk` | mechanical | `ZekdSomeK.wk` + `Finset.image_subset_image` |
| `shift` | mechanical | assignment re-index `asg env ∘ shift = asg (env∘succ)` (as in `embedC`) |
| `cut` | mechanical | `ZekdSomeK.cut` (+ budget align; structural `c > φ.complexity`) |
| **`axm`** | **hard** | splits: finite `𝗣𝗔⁻`/eq axioms → `ofBoundedTruth` (**= masterplan W1**); induction schema → `inductionLeaf_cutTowerStepWithTerm_someK_probe` + `inductionLeaf_allOmegaFromStep_someK_probe` (**= masterplan W2**) |
| **`all`** | **hard** | `ZekdSomeK.allω` + the `EmbeddingBound` uniform-ω-family port; **forces the amendment (below)** |

8 mechanical, 2 hard. The two hard cases are precisely where the real engine work lives — and the
`axm` case being "hard" is itself informative: in the *unbounded* `embedC` it is FREE (`provable_true`,
ω-completeness), whereas the witness-bounded calculus must **pay** for every PA axiom, which is why
the masterplan reifies it as two separate phases (W1 `boundedAxiomLeaves`, W2 `boundedInduction`)
that *feed* W3 as leaves.

## The three probe-consistency checks (objective #3) — **all hold; none contradicted**

1. **`ex` ↔ `embedding_closedTermExI_someK_probe`.** The probe's signature is
   `ZekdSomeK βSrc e d c (insert (ψ/[s]) Γ) → ZekdSomeK αOut e d c (insert (∃⁰ ψ) Γ)` with `s`
   closed, all ordinals structural, and **`e` threaded unchanged** input→output. This is *exactly*
   the `exs` case obligation after `embedC`'s `rew_subst_term` rewrite (`asg env ▹ (φ/[t]) =
   ((asg env).q ▹ φ)/[asg env t]`, `asg env t` closed). **Consistent** — the probe *is* the obligation.
2. **axiom leaves ↔ `ofBoundedTruth`.** Signature yields `ZekdSomeK (ONote.ofNat (2*q)) e d c Γ`
   from a `ZekdBoundedTruth` package — ordinal `ofNat(2q)` **structural** (a function of the
   complexity `q` only, env-independent), `e`/`d`/`c` free/uniform. Matches the finite-axiom
   sub-case of `axm`. **Consistent.** (The lone existential sub-case `addEqOfLt` routes through the
   closed-term `exI` probes, same as check 1.)
3. **`axm`-induction ↔ `inductionLeaf_cutTowerStepWithTerm_someK_probe` + `…allOmegaFromStep_someK_probe`.**
   The step probe composes a single running-index cut-tower step in `ZekdSomeK` at **uniform `e,d,c`**;
   the packaging probe wraps the chain into `ZekdSomeK αAll e d c (insert (∀⁰ ψ) Δ)`. **Consistent** —
   and *corroborating*: `allOmegaFromStep_someK_probe`'s hypothesis is
   `∃ k, … ∧ (∀ n, norm (β n) < max k n + d) ∧ … Zekd (β n) e (max k n) d c …`, i.e. it **encodes the
   exact discipline the amendment names** — a *structural* base index `k` (∃ k, outside the branch
   quantifier), a family `β` uniformly `< αAll`, uniform `e`, and the branch entering only through the
   running index `max k n`. No probe signature is contradicted.

## THE finding — the ω-rule (`all`) forces the amendment

`embedC` closes its `all` case with the **unbounded** `Provable.allω`, which `⨆`-sups an arbitrary
premise family over full `Ordinal.{0}` and carries **no witness index and no control ordinal**
(`src/GoodsteinPA/Zinfty.lean:232`). The ω-rule is *free* there. The witness-bounded
`ZekdSomeK.allω` (`OperatorZinfty.lean:2147`) instead demands, over `ONote` (`< ε₀`):

```
(β : ℕ → ONote)  (∀ n, β n < α)  (α.NF)              -- one uniform-bounded ordinal family
{e : ONote}                                          -- one control ordinal, ALL branches
{K : ℕ}          (∀ n, … (max K n) …)                -- one base index; branch via RUNNING INDEX
```

Instantiating the `all`-case IH `BudgetedEmbeds (insert (free φ) (Γ.image shift))` at the shifted
assignment `n :>ₙ env` (as `embedC` does) gives, **per branch `n`**, an *opaque*
`∃ α_n e_n, ∃ K_n, Zekd α_n e_n K_n d c (insert (φ'/[nm n]) Δ)`. Feeding `ZekdSomeK.allω` then
requires:

- a single NF `α` with `∀ n, α_n < α` — **unavailable**: `α_n` are opaque per-branch (sub-derivations
  contain `∀`s, so `α_n > ω`, not finite; no uniform `< ε₀` bound extractable);
- a single `e` with `∀ n` at that `e` — **unavailable**: `e_n` opaque per-branch;
- a single base `K` with `∀ n, K_n ≤ max K n` — **unavailable**: the candidate's `∃ K` sits *inside*
  `∀ env`, giving `∀ branch. ∃ K_n` (independent `K_n`), whereas the rule needs the swapped
  `∃ K. ∀ branch` with `max K n`. `∀∃` does not yield `∃∀`.

This is the precise place a `>100`-lap wall could hide, and the spike surfaces it in one session.

**Why it is an amendment, not a wall (T-W3 does not fire).** The underlying mathematics *is* solved,
and banked at the leaf:

- **Control ordinal `e` stays uniform.** The ω-branch witnesses are paid by the **running index**
  (`hardy e (max K n + d) ≥ max K n + d ≥` witness), *not* by raising `e` — so a single structural
  `e` (even minimal) serves all branches in the embedding (`e` is raised only later, in W4
  cut-elimination). This is exactly `inductionLeaf_runningIndex_witnessBound` — "the exact wall
  Route A died on, already solved here at the leaf" (masterplan §1). `e` per-branch is **not needed**.
- **Ordinal family is uniformly `< ε₀`.** `EmbeddingBound` already proves the `< ε₀` half in the
  ordinal-only calculus: `PXFc.allω_omega` lands a *non-uniform finite* family at the fixed `ω+1`
  (finite branches sup to `ω`), nested `∀` is handled by `allClosure`, and `embedC_LX_bdd` is the
  *working* bounded-embedding master. This "uniform ω-family" discipline is what must be ported into
  the witness-bounded `ZekdSomeK` (the `all`-case work of W3).
- **Base index `K` is structural + running index absorbs the branch.** This is precisely the shape of
  `inductionLeaf_allOmegaFromStep_someK_probe`'s `∃ k … max k n …` hypothesis (check 3).

Because the fix is a **quantifier/structure placement that the FAIL criterion explicitly treats as
absorbing** ("a `K` *no quantifier placement* absorbs" ⇒ FAIL; here a placement *does* absorb it),
and the leaf machinery is banked, this is a **PASS with a mandatory amendment**, not a structural
impossibility. The Buchholz fully-operator-controlled fallback (`Zᵉ`) is **not needed**.

## Recommended amended master statement (the W3 exit target)

Mirror `EmbeddingBound.embedC_LX_bdd`'s discipline inside the witness-bounded calculus: make the
whole budget **structural** and let only the running index track the branch.

```lean
theorem budgetedEmbedding {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (d : Derivation2 (𝗣𝗔 : Schema ℒₒᵣ) Γ) :
    ∃ (c d₀ : ℕ) (α e : ONote), α.NF ∧ e.NF ∧
      ∀ env : ℕ → ℕ, ZekdSomeK α e d₀ c (Γ.image (fun φ => asg env ▹ φ))
--          ^^^^^^^ α, e hoisted OUTSIDE ∀env (structural); ZekdSomeK's ∃K (per env) carries the
--          running index. For the headline (Γ = {γ} closed) env is irrelevant, so nothing is lost.
```

Notes for the W3 grind:

- Hoisting `α`, `e` out of `∀ env` is **strictly correct for the headline** (`γ` is a closed
  sentence — `asg env ▹ γ = γ` for every `env`, so `∀ env` is vacuous there); it only tightens the
  *internal* IH so the ω-rule can consume it. The candidate discipline "`c`/`d₀` structural, `K` may
  depend on `env`" is **refined** to: `c`, `d₀`, `α`, `e` structural; and the *base* index `K`
  structural too, with only the **running-index increment** `max K n` depending on the ω-branch.
- The 8 mechanical cases carry over unchanged under the amendment; `and`/`cut` get *simpler* (the two
  sub-`e` now coincide — no `mono_e` unification).
- The `all` case is then: instantiate the (now structural-budget) IH per branch, assemble the
  running-index family, and apply `ZekdSomeK.allω` with the `EmbeddingBound` uniform-family bound.
  This is the isolated genuinely-new piece of W3 — the port of `PXFc.allω_omega` into `ZekdSomeK`.

## Bottom line for the masterplan

W3 is **un-blocked and well-posed**. Sequence for the ~6–13 lap phase: (1) re-state the master with
the structural-budget amendment above; (2) discharge the 8 mechanical cases against the banked
`ZekdSomeK` API; (3) the `all` case via the `EmbeddingBound` uniform-family port; (4) the `axm` case
is a thin dispatcher over the W1 (`ofBoundedTruth`) and W2 (induction cut-tower) capstones once those
land. No pre-registered abort trigger fires. The wall the spike was sent to find (the ω-rule's
control-ordinal / witness-index uniformity) is real, located, and already solved at the leaf — the
work is to lift that leaf solution to the global statement.
