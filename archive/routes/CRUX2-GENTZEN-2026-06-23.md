# Crux 2 — Gentzen `PRWO(ε₀) → Con(PA)` (Rathjen 2014 Thm 2.8) — grounded decomposition

**Source (read lap 49, pp. 8–11 of `papers/rathjen-2014-goodsteins-theorem-revisited.pdf`).** This is the
Phase-2 ordinal-analysis girder the operator named. Quotes/structure below are FROM the paper — do not
reconstruct from memory (CLAUDE.md confabulation warning applies hardest here).

## The exact statements

**PRWO(ε₀)** (Rathjen, p. 10): *"there are no infinitely descending primitive recursive sequences of
ordinals below ε₀."* (Ordinals `< ε₀` ARE their complete Cantor normal forms — the repo's `InternalONote`
codes with `icmp`/`isNF`.)

**Theorem 2.8 (Gentzen 1936, 1938):**
- (i) **PRA proves `PRWO(ε₀) → Con(PA)`.**
- (ii) Assuming PA consistent, **PA does not prove `PRWO(ε₀)`** — *by Gödel II* (this is the
  `peano_not_proves_consistency` hook, already surfaced in `Reduction.lean`).

**Cor 2.7** (gives the §3/crux-1 side): over PA, *"every primitive recursive Goodstein sequence
terminates" ⟺ "no infinitely descending primitive recursive ε₀-sequence"* (= PRWO(ε₀)).

## Proof structure of 2.8(i) (Gentzen via Buchholz [6], sequent calculus) — p. 9

Quoting: *"he defined an assignment `ord` of ordinals to derivations of PA such [that] for every
derivation `D` of PA in his sequent calculus, `ord(D)` is an ordinal `< ε₀`. He then defined a reduction
procedure `R` such that whenever `D` is a derivation of the empty sequent in PA then `R(D)` is another
derivation of the empty sequent in PA but with a smaller ordinal assigned to it, i.e.*
```
        ord(R(D)) < ord(D).                                              (5)
```
*Moreover, both `ord` and `R` are primitive recursive functions and only finitist means [are] used in
showing (5)."*

⟹ If PA ⊢ ⊥ (a derivation `D₀` of the empty sequent exists), then `n ↦ ord(Rⁿ(D₀))` is a **primitive
recursive infinitely descending ε₀-sequence**, contradicting PRWO(ε₀). Hence `PRWO(ε₀) → Con(PA)`. ∎

## Lean decomposition (build over Foundation's ARITHMETIZED derivations)

Foundation substrate located (lap 49):
- `LO.FirstOrder.Theory.Derivation : V → Prop` + `DerivationOf d s` (coded sequent derivations),
  `Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean:459` — the Σ₁ provability substrate
  (same one Gödel II / `Theory.consistent : 𝚷₁.Sentence` use).
- `Foundation/FirstOrder/Hauptsatz.lean` — finitary cut-elimination (related machinery).
- `LO.FirstOrder.Theory.consistent` (`Incompleteness/Consistency.lean:36`) = `Con(·)`.

Lemma-by-lemma (each a disclosed `sorry` to chip; KEEP in `wip/` until green so `src/` stays clean):
1. **`prwoSentence : Sentence ℒₒᵣ`** — formulate PRWO(ε₀). Candidate Π-form: "for every code `e` of a
   total primrec `f : ℕ → ε₀-code`, ¬(∀n, `isNF(f n)` ∧ `icmp (f (n+1)) (f n) = 0`)". CAUTION: faithfully
   expressing "primitive recursive `f`" in `ℒₒᵣ` needs a universal primrec predicate / Kleene-T; ground
   the encoding against Foundation's representation framework (`R0.Representation`, `codeOfREPred`) before
   committing — highest confabulation risk in the whole project.
2. **`ord : V → V`** (coded derivation → ε₀-code), primrec; `ord_lt_eps0 : T.Derivation d → isNF (ord d)`.
3. **`R : V → V`** (Gentzen reduction), primrec; `R_derivationOf_empty : DerivationOf d ⊥ → DerivationOf (R d) ⊥`.
4. **`ord_R_lt : DerivationOf d ⊥ → icmp (ord (R d)) (ord d) = 0`** — the eq (5). THE deep core (Gentzen's
   reduction-procedure ordinal-descent; ground in Buchholz [6] = `buchholz-on-gentzens-first-consistency-proof.pdf`
   + `siders-gentzen-consistency-proofs-arithmetic.pdf`).
5. **`prwo_implies_consistency : ... ⊢ prwoSentence → T.consistent`** — assemble: a `DerivationOf d ⊥`
   ⟹ primrec descent `n ↦ ord (R^[n] d)` ⟹ ¬prwoSentence. Then chain into
   `Reduction.goodstein_implies_consistency` with crux 1 (`γ → PRWO`) + Gödel II.

## Why this is distinct from crux 1 (and NOT blocked on Ackermann)
Crux 1 (§3, `γ → PRWO`) needs the internal Grzegorczyk `F` (Lemma 3.2/3.3) — Ackermann-level, needs the
full-PA reduct + internal iteration infra (lap-49 generic-`V` `icorAlpha` tower is its lead/slow-down half).
Crux 2 here is pure syntactic proof theory over coded derivations — no fast-growing hierarchy. Independent
threads; both gate `goodstein_implies_consistency`. PRWO formulation (step 1) is the shared hinge.
