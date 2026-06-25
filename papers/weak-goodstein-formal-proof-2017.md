# Formal Proof of the Weak Goodstein Theorem — summary

## Provenance

- **File**: `weak-goodstein-formal-proof-2017.pdf`
- **Title**: *Formal Proof of the Weak Goodstein Theorem*
- **Author**: Jean-Raymond Abrial (Marseille, France) — the creator of the B Method and Event-B
- **Source**: arXiv:1701.01673v1 [cs.SE], dated 29 Nov 2016 (arXiv id stamp says 2017)
- **Length**: 6 pages, short pedagogical note
- **Citation**: J.-R. Abrial, *Formal Proof of the Weak Goodstein Theorem*, arXiv:1701.01673 (2016/2017).

## Abstract

A short, pedagogically-motivated note in which Abrial reconstructs and presents a **simple** proof of the *weak* Goodstein theorem — the variant where numbers are written in ordinary (non-hereditary) base notation. His stated aim is to give students an explicit, mechanical, system-development example of how to prove **loop termination** (the Weak Goodstein loop), using lexicographical/well-founded ordering over finite sequences of natural numbers, *without* transfinite ordinals. He explicitly contrasts this with the standard literature proofs (which use transfinite ordinals and which he found "rather complicated"), and notes that he **tried and so far failed** to extend the simpler approach to the *strong* (hereditary-base) Goodstein theorem.

## Key content

**What "weak Goodstein" is.** The weak Goodstein sequence writes a number in ordinary base notation (e.g. `25 = 1·2^4 + 1·2^3 + 0·2^2 + 0·2^1 + 1·2^0`, i.e. the digit sequence `11001`), then repeatedly: increment the base, reinterpret the *same digit sequence* in the new base, and subtract 1. The values balloon (1000₂ → 222₃ → 221₄ → … hundreds, then thousands) but the theorem states the sequence eventually **decreases to 0 and terminates**. This is the easy cousin of the full ("strong") Goodstein theorem, which uses *hereditary* base notation (the exponents are themselves written in the base, recursively: `h_base_2(25) = 2^{2^2} + 2^{2+1} + 1`).

**The proof idea (the crux).** Increasing the base does **not** change the *digit-sequence* representation of a number; only the subtraction of 1 changes it. So each weak-Goodstein step yields a digit sequence that is **lexicographically smaller** than the previous one. Lexicographical order on fixed-length tuples of naturals is well-founded, so the sequence must terminate. Abrial builds this up via:
- **Lemma 1**: `x^n − 1 = (x−1)·x^{n−1} + (x−1)·x^{n−2} + … + (x−1)·x^0` (proved by induction on `n`) — the algebraic engine showing how "subtract 1" rewrites a digit string into a lexicographically smaller one regardless of base.
- A **sequence data structure** `seq_b(n)` (digits low-to-high) with a recursive constructor, and an inverse `val_b(s)` that evaluates a sequence back to a number; these are mutually inverse.
- The **Weak Goodstein loop**: `n := some natural; b := 2; while n ≠ 0 do { n := val_{b+1}(seq_b(n)) − 1; b := b+1 }`. The whole theorem reduces to: *does this loop terminate?*

**Formalization approach + system used.** This is **not** a mechanically-checked end-to-end formal proof in the modern ITP sense. It is a *formal-methods* (program-correctness) treatment aimed at a course, organized around proving **loop termination** via a well-founded variant. The intended toolset is **Rodin** (the Event-B / B-Method tooling) — §7.4's "Formal Development Outline" lists "demo with Rodin toolset" for well-founded relations, proving well-foundedness, strong well-ordering, and lexicographical-ordering relations, culminating in step 7 "Final Proof for the Weak Goodstein Loop." So: the proof obligation is framed in Abrial's Event-B/refinement idiom; what the paper *delivers* is the informal+semi-formal argument and the course scaffolding, with the actual machine-checking left to the Rodin demos. It proves **termination only** — there is no growth-rate bound and no independence result.

## Relevance to the full Goodstein independence work

- **Variant, not the prize.** This handles the *weak* (ordinary-base) theorem, whose termination is provable in PA by ordinary (transfinite-free) well-founded induction over finite tuples. It deliberately **sidesteps** exactly the ingredient that makes the *strong* Goodstein theorem interesting for our repo: the hereditary base notation whose ordinal assignment reaches up to ε₀. Abrial himself flags that his simpler method **does not** extend to the strong theorem.
- **No ordinal / growth-rate / independence content.** The thing we care about for Goodstein *independence* (Kirby–Paris) is the ε₀ ordinal descent and the resulting unprovability-in-PA / growth-rate (length-of-sequence) machinery. This paper carries **none** of that — by design it *avoids* transfinite ordinals. The lexicographic-order-on-fixed-length-tuples trick is well-founded only because the digit count is bounded; that boundedness is precisely what breaks in the hereditary case (the "tree" representation in §4 is where strong Goodstein lives, and §4/§5 record that Abrial "failed" to push the tree-based proof through).
- **Reusable techniques?** Marginal for the independence target. The reusable kernels are generic, not Goodstein-specific: (1) the `x^n − 1` digit-rewrite Lemma 1; (2) modelling a base representation as an explicit `seq`/`val` pair with mutual-inverse proofs; (3) reducing the theorem to **loop termination via a well-founded variant**. mathlib already has well-founded recursion, lexicographic orders, and (crucially) ordinal arithmetic up to ε₀, so none of Abrial's hand-built machinery is needed there. Its value to us is mostly **expository/contrastive** — a clean statement of *why* the weak theorem is PA-provable and the strong one is not (the hereditary/ordinal gap), which is useful framing for documenting the independence result, not a technical lever for proving it.

**References of note in the paper**: Goodstein (1944) original; Kirby & Paris, *Accessible Independent Results for Peano Arithmetic* (1982) — the actual independence result; Rathjen (2014), Caicedo (2007), Perez (2009) survey/alternative proofs.

---

### Verdict

This is a formalization of the **easy variant only** (ordinary-base "weak" Goodstein), proving **termination, not independence or any growth-rate bound**, and it is a B-Method/Event-B (Rodin-toolset) *loop-termination* exercise rather than a machine-checked ITP proof. Its whole point is to **avoid** transfinite ordinals — the exact machinery the full Goodstein independence result depends on — and the author explicitly reports that the approach does **not** extend to the strong theorem. Contribution to our independence work is essentially expository (a crisp account of the weak/strong + ordinary/hereditary gap) rather than reusable proof technique.
