# Route scope reality — "the ε₀ girder is the whole project" (2026-07-01)

> Written host-side (Ren) in answer to the operator's question: *"The ε₀ problem keeps coming up. Do we not
> have documentation on how to prove that? DIRECTION.md only scopes efforts worth a dozen laps. What's being
> missed?"* — paired with the operator's binding decision the same day: **full axiom-free discharge OR
> abandon; a named/citable/accepted axiom is a 100% non-starter.**

## TL;DR

Nothing is missing in **knowledge**. The math of the ε₀ girder is fully documented — both in the external
literature AND on this repo's own disk. What's been missing is **scope honesty in the one document the grind
laps actually obey** (`DIRECTION.md`), which repeatedly re-framed a multi-year, never-done-in-Lean research
monument as "decompose the textbook proof into a dozen mathlib-shaped laps." Every route pivot (A → A′ → B)
has quietly relocated that same monument and reset the estimate by hoping to *avoid* building it. The
operator's "axiom-free or abandon" decision removes the last hiding place: the girder can no longer be
internalized-away, cited-away, or deferred. **It is now, unambiguously, the entire remaining deliverable.**

## 1. We have abundant documentation on how to prove the ε₀ result

Both halves — the *math* and the *honest scope* — are already in `papers/` and the charter:

- **The math (complete recipes):**
  - `papers/buchholz-beweistheorie-lecture-notes.md` — a full, self-contained development from Tait
    cut-elimination up to the ordinal analysis of PA (`Z`) via the infinitary `Z^∞` (ω-rule), culminating in
    `PRA + QF-TI(ε₀) ⊢ Con(Z)` **and** the primitive-recursive characterization of PA's provably-recursive
    functions via a `red(h)` reduction. This *is* the girder, executed.
  - `papers/buchholz-on-gentzens-first-consistency-proof.md` — the ordinal assignment `õ(d) < ε₀` and the
    reduction `d ↦ d[n]`.
  - `papers/buchholz-wainer-1987-...md` (NEW 2026-07-01) — the growth-rate converse ("Bounding the provably
    computable functions"): PA ↪ ω-logic + cut-elimination ⟹ every PA-provably-total function is dominated
    by some `F_α`, `α<ε₀`. This is *exactly* `wainer_bound_of_pa_proves_goodstein`, with its proof.
  - Plus `siders-...`, `rathjen-2006-...`, `arai-...`, `freund-...`, `nested-multisets-...-isabelle`.
- **The honest scope (already written, but not where the box looks):** `EXPEDITION-PLAN.md`, day one —
  > "its load-bearing theorem (**the ordinal analysis of PA**) exists in **no** Lean library and must be
  > *originated*. A lap assembles; it **cannot originate** a major body of proof theory in a night … This is
  > a **research milestone**, executed in phases, **with a human architect**." And its landscape table marks
  > **"Ordinal analysis of PA: TI(ε₀) ⊢ Con(PA) — ❌ missing everywhere … the missing girder."**
  - `STATUS.md` is saturated with the true scale: "Bryce–Goré-scale," "a major multi-lap undertaking,"
    "~1k-line milestone = Bryce–Goré's `Peano.v`," etc.

So: **the answer to "do we not have documentation on how to prove ε₀?" is "we have a whole shelf of it."**
The gap was never knowledge.

## 2. What's being missed: the scope lives in the charter, but the box obeys `DIRECTION.md`

`DIRECTION.md` is, by its own header, the **tactical** layer — "grind laps READ this section and work
strictly within it," "keep it SHORT," turns over every few laps. And until today it contained a line that
**directly contradicted** the charter:

> *(old `DIRECTION.md`)* "This is **formalization of a known proof, not origination** … Decomposing it into
> mathlib-shaped Lean lemmas is **exactly treadmill work**."

That is the precise inversion of `EXPEDITION-PLAN.md`'s "must be *originated* … **not** a solo
autonomous-treadmill job." The document the box actually reads told it to treat the monument as routine
decomposition. **That is the miss** — not a missing paper, but a charter/tactical contradiction that trained
the box (and each review lap's estimate) to see "a dozen laps" where the charter saw "a human-architected
research milestone." (Fixed 2026-07-01 in the "honest scope warning" block + Phase 2.)

## 3. Why it kept producing false summits

Three reinforcing dynamics:

1. **The treadmill substrate rewards within-lap green.** A lap that chips a tractable sub-lemma and compiles
   looks like progress on the girder even when it is orthogonal to it. Over ~110 laps this manufactured ≥4
   documented "false summits" (e.g. `STATUS.md`'s lap-114 "the cut-elimination PRIZE is FEASIBLE, not a
   multi-year wall" — later refuted).
2. **Each route pivot re-hid the monument instead of costing it.**
   - **Route A** tried to *internalize* the girder inside IΣ₁ (to reach Con(PA) → Gödel II). That added an
     **un-precedented** arithmetization layer on top of the girder, and died on the finitary-`zInd`
     vs ω-rule expressiveness wall (the M2 probe, escape (α) dead).
   - **Route A′ (Towsner)** keeps a *meta* cut-elim wall (precedented) but still the girder.
   - **Route B (Wainer)** deletes the internalization and the Gödel-II wiring — a genuine simplification —
     but the classification's converse **is** the girder (Buchholz–Wainer prove it by ω-rule + cut-elim).
   - So the routes differ only in the **packaging/entry-point** of one un-built monument. B is the best
     *entry point* (meta-level, drops Route A's extra un-precedented layer), but it is **the same girder**.
3. **The "accept as a named axiom" escape** let every route treat the girder as a deferrable footnote
   ("decide later whether it's its own campaign"). The 2026-07-01 operator decision **deletes that escape.**

## 4. What "axiom-free or abandon" forces

With the escape gone, the project's true remaining scope collapses to a single, well-defined target:

> **Originate, in Lean 4, the Gentzen ordinal analysis of PA** — the ε₀-bounded infinitary cut-elimination
> that yields either `TI(ε₀) ⊢ Con(PA)` (Route A/A′ back-end) or the Buchholz–Wainer Σ₁-witness bounding
> theorem (Route B back-end). Same monument; the route only picks which face you climb.

Honest parameters (from the repo's own review docs + the new sources):

- **Scale:** ~thousands of Lean lines (`STATUS.md`/JUDGE: "~6–7k, Bryce–Goré-scale"). **Never done in any
  Lean library; absent from mathlib.**
- **Precedent:** it **has** been done in Coq — **Bryce & Goré, arXiv:2603.00487** (`PA_omega.v` / `Peano.v`,
  a complete `Con(PA)`). That is the port target + feasibility witness. (It is `PA_ω`/eigenvariable-free —
  a shape mismatch for a finitary-PRWO route, but a valid blueprint for the meta girder.)
- **Cadence:** roughly *one genuine reduction rung per lap* at best; this is **origination, human-architected,
  multi-month+**, not a treadmill sprint. The lower-bound half (`goodsteinLength_dominates_fastGrowing`) is
  the only "port-not-invent" piece and it is **already done, axiom-clean**.

## 5. Recommendation

1. **Re-scope `DIRECTION.md` to OWN the monument** (done today: the honest-scope block + Phase 2 rewrite +
   the deleted "treadmill decomposition" claim). The grind directive for Phase 2 should be "chip one
   Bryce–Goré-shaped lemma of the meta girder and bank it," never "finish the girder."
2. **If committing to axiom-free: build the girder at the META level (Route B / A′ shape), porting the
   Bryce–Goré Coq `Con(PA)` structure**, as a first-class, milestoned, human-architected campaign — likely
   worth its own library, since "ordinal analysis of PA in Lean" is independently valuable (it is the thing
   mathlib lacks and *every* PA-independence result needs). Do **not** resume Route A's internalized-in-IΣ₁
   shape (the un-precedented layer that just died).
3. **Decision the operator now genuinely faces** (this is the real fork, honestly stated): commit a
   human-architected, multi-month research effort to originate the Bryce–Goré-scale girder in Lean — **or
   abandon**. There is no dozen-lap path and no cheaper packaging; the literature is unanimous that the
   girder's strength is intrinsic. Everything else the expedition can do (routes, wrappers, lower bounds) is
   already done or is deck-chairs around this one monument.
