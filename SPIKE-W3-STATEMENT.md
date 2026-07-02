# SPIKE W3 — the global budgeted-embedding STATEMENT spike (operator-commissioned, 2026-07-01)

> **One bounded session. Deliverable = a typed skeleton + a binary verdict file. NOT a proof campaign.**
> This is deciding experiment #1 of `MASTERPLAN-2026-07-01-ZERO-AXIOMS.md` (§5 W3). Its whole purpose
> is to surface, in ONE session, whether the witness-budget discipline survives the *global* embedding
> induction — the place a >100-lap wall could hide. Sorries are expected and correct here; a spike that
> "makes progress proving cases" instead of pinning the global shape has FAILED its assignment.

## Context (read first)

- `MASTERPLAN-2026-07-01-ZERO-AXIOMS.md` §3–§5 (the engine; why someK is the Wainer-discharge substrate).
- `src/GoodsteinPA/Embedding.lean:525` — `embedC`, the complete UNBOUNDED embedding (kernel-verified
  axiom-clean). Its 10 Derivation2 cases are your structural template; your job is the budgeted twin.
- `src/GoodsteinPA/OperatorZinfty.lean` — the `Zekd` calculus (:47), `ZekdSomeK` surface (:1991–2295),
  `ZekdBoundedTruth`/`ofBoundedTruth` (:1747/:2046), closed-term `exI` probes (:1924–1989), the
  induction-leaf cut-tower + running-index probes (:1033, :2467, :2546).
- Towsner §15–§16 (`papers/towsner-goodstein-epsilon0-unprovability.pdf`) — the witness-bounded
  embedding on paper. Ground every budget decision in the paper, not in memory.

## Objective

In `wip/SpikeW3Embedding.lean` (new file, `GoodsteinPABlueprint` root so it builds):

1. **Pin the master statement.** Candidate signature (amend if the math demands — but any amendment is
   itself a finding to document):

   ```lean
   theorem budgetedEmbedding
       {Γ : Finset (SyntacticFormula ℒₒᵣ)}
       (d : Derivation2 (𝗣𝗔 : Schema ℒₒᵣ) Γ) :
       ∃ c d₀ : ℕ, ∀ env : ℕ → ℕ, ∃ α e : ONote, α.NF ∧ e.NF ∧
         ZekdSomeK α e d₀ c (Γ.image (Rewriting.app (asg env)))
   ```

   Discipline (Towsner §16): `c`/`d₀` structural (derivation-only, OUTSIDE `∀ env`); the numeral budget
   `K` lives inside `ZekdSomeK`'s `∃K` and MAY depend on `env`; `α` finite-per-node is fine.
2. **One named sorried lemma per Derivation2 rule case** (mirror `embedC`'s case split exactly: axL,
   verum, and/or, all, ex, wk, cut, shift, axm — whatever the true inventory is), each stated with the
   SAME budget discipline, and the master theorem assembled from them **by a real (non-sorry) induction**.
3. **Consistency check against the banked locals**: the `axm`-induction case obligation must be
   satisfiable by the shape of `inductionLeaf_cutTowerStepWithTerm_someK_probe` + `…allOmegaFromStep…`;
   the `ex` case by `embedding_closedTermExI_someK_probe`; the axiom leaves by `ofBoundedTruth`. If a
   case obligation CONTRADICTS a proven probe's signature, that is a FAIL finding — write it up, don't
   paper over it.

## Verdict criteria — write `SPIKE-W3-VERDICT.md`, then STOP

- **PASS** = (a) the master statement + all case lemmas ELABORATE (build green, sorries disclosed);
  (b) NO case needs a budget depending on the ω-branch index or instantiation beyond what `∃K`-inside-
  `∀env` absorbs; (c) the three probe-consistency checks hold. State which cases look mechanical vs hard.
- **FAIL** = some rule case structurally cannot carry the budget (needs per-branch non-uniform `e`/`c`,
  or a `K` no quantifier placement absorbs). Name the rule, the exact obstruction, and whether Buchholz
  fully-operator-controlled derivations (the fallback architecture) would dodge it. This fires trigger
  **T-W3** — a valuable outcome, not a failure of the session.
- Either way: real `#print axioms` on the assembled master (expect `sorryAx` + canonical only — NO new
  `axiom` declarations anywhere), verdict file written, commit, stop.

## Forbidden

- Proving the case lemmas beyond what pinning the statement requires (skeleton spike, not a grind).
- New `axiom` declarations; touching LOCK files (`Defs`/`Bridge`/`Encoding` RHS); editing `DIRECTION.md`;
  redesigning `Zekd`/`ZekdSomeK` (a needed redesign = a FAIL finding to document, not to execute).
- Working around a wall silently. The wall IS the data.
