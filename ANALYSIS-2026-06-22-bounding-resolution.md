# Resolution of the `bounding` / Thm 17.1 frontier — invert-then-bound (lap 5)

**Status:** architectural resolution found (lap 5, via WebSearch literature + a machine-checkable
analysis). Self-answers most of `ON-LINE-REQUEST.md` lap-4. The Arai PDF is still worth fetching for
the *exact* bound bookkeeping; the architecture below does not depend on it.

## The problem (lap-4 handoff's "accumulating existentials")

The full lower bound (Towsner Thm 17.1) was decomposed in `wip/WitnessBound.lean` to a single open
case: the `I∀` (ω-rule) case of `bounding`, where a cut-free derivation of `{gAll}` (`gAll =
∀x∃y g_y(x)=0`) re-applies the ω-rule, **accumulating** existentials `{gEx n*, gEx n', …, gAll}` in
a *set* sequent. The lap-4 attempt tried to carry an "every formula is out of reach" invariant
through the induction on the derivation, with `gAll` kept in the sequent.

**Why that invariant genuinely fails (now understood):** because the sequent is a *set* and the
`allI` rule keeps `gAll`, you can re-expand `gAll` at a **small, reachable** index `n'`, then `exI`
with the true witness `G n'` (which is `≤ hardy bound` since `n'` is small), introducing a **true**
atom `g_{G n'}(n')`. `trueR` then closes the *entire* sequent — including any out-of-reach
`gEx n*` that was riding along (a true atom anywhere closes the whole set sequent). So the naive
"all out of reach" invariant is **not preserved by `allI`**, and `{gAll}` would even be *derivable*.
This is the real content of the frontier — not a gloss, a genuine insufficiency of the direct
invariant.

## The resolution: ∀-inversion removes the universal, then the proven ∃-fragment bites

The standard proof-theoretic move (Schwichtenberg–Wainer *Proofs and Computations* Ch. 4 bounding
lemma; Arai, *Two remarks on proof theory of first-order arithmetic*, arXiv:2003.13207, the
Σ₁-witness derivability relation) is **invert, then bound** — and the inversion is what dissolves
the accumulation:

1. **∀-inversion for `B`.** `B α k Γ` with `gAll ∈ Γ` yields a derivation of the *instance* sequent
   with `gAll` **removed/replaced**: `B α' k' ({gEx n} ∪ (Γ \ {gAll}))` for each numeral `n`, at a
   bound `(α', k')` controlled by `(α,k)` (the `allI` premise already hands this over directly:
   `B (β n) (max k n) (insert (gEx n) Γ)` with `β n < α`; the other rules commute with the
   inversion). This is the exact analogue of `Zinfty.allInv` (already proved there for the `(α,c)`
   calculus), now with the `(α,k)` witness bookkeeping.

2. **Apply the proven gAll-free ∃-fragment.** After inversion at the dominating index `n*`, the
   sequent `{gEx n*} ∪ (Γ \ gAll)` contains **no** `gAll`, so
   `wip/LowerBoundHardy.lean : lowerBound_existential_hardy` (axiom-clean, over the real `hardy`/`G`)
   applies directly: out-of-reach ⟹ not derivable.

3. **Domination supplies "out of reach" at `n*`.** Need `∃ x, hardy α (max k x) < G x`
   (Towsner Thm 7.2 / 9.8 = Goodstein dominates every Hardy level). Then
   `hardy (β n*) (max k n*) ≤ hardy α (max k n*) < G n*` (Hmono = `hardy_le_of_lt`, β n* < α with
   budget; numeric monotonicity = `hardy_monotone`), so `gEx n*` is out of reach. Contradiction.

The disjunctive reading of the bounding lemma ("*some* formula of Γ is witnessed below `H_α(N)`",
not *every* existential simultaneously) is what `lowerBound_existential_hardy` already encodes in
contrapositive form. The universal is handled *outside* that lemma, by inversion — which is the
piece the lap-4 decomposition was missing.

## Concrete Lean plan (M6 full)

- [x] `lowerBound_existential_hardy` — gAll-free ∃-fragment, concrete Hardy/G, axiom-clean
      (`wip/LowerBoundHardy.lean`, lap 5).
- [ ] `B.allInv (n)` : `B α k Γ → gAll ∈ Γ → B α k (insert (gEx n) (Γ.erase gAll))` — ∀-inversion,
      by induction on the derivation (mirror `Zinfty.allInv`). Bound bookkeeping: aim height-
      preserving; if `k` cannot be held (the `allI` premise grows it to `max k n`), state it
      existentially `∃ α' k', … ∧ α' ≤ α ∧ k ≤ k'` and transfer the out-of-reach condition via
      `hardy_le_of_lt` + `hardy_monotone`.
- [ ] **Strictness bridge for `Hdom` (the one genuinely-open bit).** Track-1's domination is
      `goodsteinLength_dominates_fastGrowing (ho:α.NF) : ∃ N, ∀ m≥N, fastGrowing α m ≤ goodsteinLength m + 2`
      — i.e. `G m = goodsteinLength m ≥ fastGrowing α m − 2`. Combined with `hardy α m ≤ fastGrowing α m`
      this only gives `hardy α m ≤ G m + 2`, the WRONG direction for the strict `hardy α (max k x) < G x`
      that `Hdom` needs. Fix: apply domination at a **larger ordinal** `β > α` (e.g. `β = α+1` via
      `osucc`): then `G x ≥ fastGrowing β x − 2`, and the fastGrowing-over-hardy gap
      (`fastGrowing (α+1) x = (fastGrowing α)^[x] x ≫ hardy α x + 3` for `x ≥ 4`) yields
      `hardy α (max k x) = hardy α x < G x` for large `x ≥ max k`. Pick `x` past all thresholds.
      The `α=0` corner (`fastGrowing 0 = succ`, gap 1) uses `β = α+1 = 1` or just that `goodsteinLength`
      is super-linear. Bounded, self-contained → good Aristotle target once the chain is ported.
- [ ] `Hdom` : `∃ x, hardy α (max k x) < G x` — Goodstein dominates Hardy. Track-1
      (`~/src/lean-formalizations Logic/Goodstein/Domination*.lean`) has `goodsteinLength`-domination
      of `fastGrowing_*`; needs (a) `hardy ≤ fastGrowing`-style bridge or direct `hardy` domination,
      (b) relating `goodsteinLength` to our `G` (least-zero step). Largely a port.
- [x] `lowerBound_hardy` : assemble — invert at `n*` from `Hdom`, apply `lowerBound_existential_hardy`.
      DONE (lap 5, modulo `Hdom`).

## M4 scoping (lap 5) — how the fragment lower bound connects to the headline

`B` (`wip/LowerBoundHardy.lean`) is a **specialized Goodstein-fragment** calculus: its formulas are
only `atom`/`gEx`/`gAll`. Foundation's finitary calculus (`FirstOrder/Basic/Calculus.lean`:
`Derivation` with `axL`/`verum`/`or`/`and`/`all`/`exs`/`wk`/`cut`) is general over
`SyntacticFormula ℒₒᵣ`. So the headline chain is NOT "embed PA directly into `B`"; it is:

1. **General witness-bounded ω-calculus `Zᵏ`** — `src/Zinfty.lean`'s `Deriv` *plus* the Towsner §15
   `(α,k)` witness bound on `∃` (the bound `src/Zinfty.lean` currently drops — the lap-4 finding).
2. **M4 embed** `PA⁺ ⊢ φ ⟹ Zᵏ ⊢^{α,k}_c φ` (α<ε₀, finite c). Map Foundation `Derivation` rules
   across; finitary `∀`→ω-rule; finite induction instances ⟹ finite cut rank.
3. **Cut-elim with `k`** (redo `src/Zinfty.lean`'s §19 tracking the bound) ⟹ cut-free `Zᵏ ⊢^{α,k}_0 gAll`.
4. **Subformula restriction** (the bridge to `B`): a *cut-free* `Zᵏ`-derivation of `{gAll}` contains
   only subformulas of `gAll` = exactly `atom`/`gEx`/`gAll` (the `GForm` fragment), so it **is** a
   `B`-derivation. Hence `lowerBound_hardy` (+ `Hdom`) ⟹ no cut-free `Zᵏ ⊢^{α,k}_0 gAll`. Contradiction
   with steps 2–3. This subformula lemma is the clean, *small* connector — much easier than redoing
   17.1 in the general calculus.
5. **M7**: PA↔PA⁺ language bridge (opaque Σ₁ `goodsteinSentence` vs `∀x∃y g_y(x)=0`) + assemble.

So the load-bearing 17.1 content (`B` + `lowerBound_hardy`) is **done**; the remaining lower-bound
work is the general calculus plumbing (steps 1–4), where step 4 reuses the fragment result as-is.

## Literature anchors (WebSearch, lap 5)
- Schwichtenberg–Wainer, *Proofs and Computations*, Ch. 4 — bounding/boundedness lemma for `PA_∞`,
  Σ₁-witnesses dominated by `H_α`, `α < ε₀`.
- T. Arai, *Two remarks on proof theory of first-order arithmetic*, arXiv:2003.13207 — Thm 1.1 +
  a derivability relation bounding witnesses for provable Σ₁-formulas (the cleanest target).
- "Unprovability in Mathematics: A First Course on Ordinal Analysis", arXiv:2109.06258.
- Towsner, *Goodstein's Theorem, ε₀, and Unprovability* (on disk, `papers/`) — §17 is the target;
  the inversion step is implicit in his §19 inversions, applied to the §17 lower bound.
