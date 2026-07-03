# Findings — is Goodstein/PA-independence (or its ε₀ girder) formalized anywhere? (2026-07-01)

> External verification for the operator's go/no-go, triangulated across 2 independent web-research
> agents + the local `papers/` corpus + `ROUTE-SCOPE-REALITY-2026-07-01.md`. All accessed 2026-07-01.
> Backs the scope-reality doc's "the literature is unanimous the girder is intrinsic" claim with citations.

## Verdict: GREENFIELD FIRST. Nothing contradicts the prior.

**The INDEPENDENCE `PA ⊬ Goodstein` (Kirby–Paris) has never been formalized in any proof assistant, by
any route.** Neither has any sibling concrete fast-growing/Ramsey PA-independence (hydra, Paris–Harrington).
A Lean 4 proof is a first in any prover.

### What exists (and is NOT the target)
- **Termination only**, everywhere: Coq `rocq-community/hydra-battles` (Castéran, ε₀ variant + Hardy/Wainer
  `F_α`/`H_α` hierarchies, axiom-free); Isabelle/AFP `Goodstein_Lambda` (Felgenhauer) + `Nested_Multisets_Ordinals`
  (Blanchette–Fleury–Traytel, `goodsteins_theorem : ∃ i. goodstein i = 0` via hereditary multisets); Lean
  `ONote.fastGrowing` (in mathlib) + Goodstein **termination in `gotrevor/lean-gallery`** (NOT in mathlib —
  `grep goodstein Mathlib/` is empty and 1000.yaml `Q1149185` has no `decl`; the gallery proof is uncredited
  into mathlib pending re-point PR `gotrevor/mathlib4#1`); personal `WilliamAngus/Goodstein`.
- **Abstract Gödel I/II incompleteness** (a DIFFERENT family, correctly separated): O'Connor Coq Gödel–Rosser
  (arXiv:cs/0505034); Paulson Isabelle `Incompleteness` (arXiv:2104.13792); Lean `FormalizedFormalLogic/Foundation`
  (Gödel I/II + first-order Gentzen Hauptsatz — but NOT ε₀ ordinal analysis of PA, no roadmap for it).

### The ε₀ girder (the actual deep debt)
- **Ordinal analysis of PA / `Con(PA)` via Gentzen cut-elimination: formalized in exactly ONE lineage, Coq,
  META** — Morgan Sinclaire (Boise State MS thesis 2019, `Morgan-Sinclaire/Gentzen`, ~5k lines) → **forked &
  extended by Bryce & Goré** (arXiv:2603.00487, Feb 2026, ~18k lines, `PA_omega.v`/`Peano.v`, main thm
  `PA_Consistent`). Both are META (reason in the prover's type theory about infinitary `PA_ω` + ω-rule +
  ordinal assignment `<ε₀`), NOT arithmetized-in-PA-over-codes. Nothing equivalent in Isabelle or Lean.
- **The Wainer/Buchholz classification itself** (provably-total ⟺ `<ε₀`-dominated) — the exact content of
  `wainer_bound_of_pa_proves_goodstein` — **formalized NOWHERE** (~85%). Math source now on disk:
  `papers/buchholz-wainer-1987-...` (open OA, proves both directions, method = embed PA in ω-logic +
  cut-elim + ordinal assignment `<ε₀`).

### 🚩 The strongest difficulty signal (concrete, not a vibe)
Coq `hydra-battles` **bundles both endpoints in one repo** — the ε₀ hydra-termination proof AND a full PA
object theory + O'Connor's Gödel–Rosser incompleteness (`theories/ordinals/Ackermann/` + `theories/goedel/`)
— **yet nobody connected them into "PA ⊬ hydra."** Castéran's book lists the PA-provability link as
unfinished future work and says the ε₀ proofs deliberately *"do not use any knowledge about Peano
arithmetic."* The single most-motivated project on earth had both halves in hand and did not build the
bridge. That IS the load-bearing step, and it is unbuilt everywhere.

### Trackers (read verbatim from raw `1000.yaml` / Freek 1000+)
- `Q1149185 Goodstein's theorem` — listed, no `decl` (= termination sense, unformalized in Lean master; even
  the `lean-gallery` termination isn't credited yet, pending re-point PR `gotrevor/mathlib4#1`).
- `Q1149185X Kirby–Paris theorem` — distinct entry = **the independence**, unclaimed across all 6 provers.
- `Q7137494 Paris–Harrington` — listed, unclaimed, ~zero formalization footprint anywhere.

## Implication (confirms `ROUTE-SCOPE-REALITY-2026-07-01.md`)
Under full-discharge-or-abandon, the remaining deliverable = **originate the Bryce–Goré-scale (~6–7k Lean
line) meta ε₀ ordinal analysis of PA in Lean** (port target + feasibility witness = the Coq Sinclaire/Bryce–Goré
`Con(PA)`; the classification bounding-lemma on top is net-new nowhere) → bridge to the repo's already-done,
axiom-clean `goodsteinLength_dominates_fastGrowing` lower bound. Multi-month, human-architected, a genuine
first. No dozen-lap path, no cheaper packaging. The fork is: **commit to that monument, or abandon.**

## Sources
arXiv:2603.00487 · github.com/aarondroidbryce/Gentzen · github.com/Morgan-Sinclaire/Gentzen ·
scholarworks.boisestate.edu/td/1546 · rocq-community.org/hydra-battles/doc/hydras.pdf ·
github.com/rocq-community/hydra-battles · isa-afp.org/entries/Goodstein_Lambda.html ·
isa-afp.org/entries/Nested_Multisets_Ordinals.html · epub.ub.uni-muenchen.de/3843/1/3843.pdf (Buchholz–Wainer
1987) · raw.githubusercontent.com/leanprover-community/mathlib4/master/docs/1000.yaml ·
1000-plus.github.io · github.com/FormalizedFormalLogic/Foundation · arXiv:cs/0505034 · arXiv:2104.13792
