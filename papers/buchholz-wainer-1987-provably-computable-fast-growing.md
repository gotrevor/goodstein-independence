# Buchholz & Wainer (1987) — Provably Computable Functions and the Fast Growing Hierarchy

## Provenance

- **File**: `buchholz-wainer-1987-provably-computable-fast-growing.pdf` (gitignored; local/bind-mount only)
- **Title**: *Provably Computable Functions and the Fast Growing Hierarchy*
- **Authors**: Wilfried Buchholz (Munich) & Stan S. Wainer (Leeds)
- **Source**: in *Logic and Combinatorics* (S. G. Simpson, ed.), Proceedings of the AMS–IMS–SIAM Joint Summer Research Conference, Aug 4–10 1985; **Contemporary Mathematics vol. 65**, American Mathematical Society, 1987, **pp. 179–198**.
- **Citation**: W. Buchholz & S. S. Wainer, "Provably computable functions and the fast growing hierarchy," in *Logic and Combinatorics*, Contemp. Math. **65**, AMS, 1987, 179–198.
- **Open access**: full text free at the LMU Munich OA repository — `https://epub.ub.uni-muenchen.de/3843/1/3843.pdf` (downloaded 2026-07-01). This is the **open, primary-source replacement for the paywalled Fairtlough–Wainer Handbook ch. III** for the specific classification theorem Route B needs.
- **Phase**: **fast-growing** (Route B capstone) — and, load-bearingly, **ε₀ girder** (see the faithfulness caveat).

---

## Why this paper matters here (BLUF)

This is the **canonical, open, peer-reviewed source that states AND proves both directions of the Wainer
classification** — the exact theorem the growth-rate route's remaining axiom
(`GoodsteinPA.WainerRoute.wainer_bound_of_pa_proves_goodstein`) encodes. It resolves the
"Fairtlough–Wainer access gap" flagged in `DIRECTION.md` / `SOURCES.md`: the statement fidelity risk is
gone, because the classification is right here in a citable form.

**But it also settles what the pivot does NOT buy.** The direction the axiom needs — "every
PA-provably-computable function is eventually dominated by some fixed `F_α`, `α < ε₀`" — is proved in this
paper by *embedding PA in the infinitary ω-logic system and running cut-elimination*. That is the same ε₀
ordinal-analysis monument as Route A. The Wainer packaging relocates the girder into one named theorem; it
does not dissolve it.

---

## The hierarchy (as used here)

Fast-growing functions `F_α`, `α < ε₀`, over a fixed assignment of fundamental sequences (Ketonen–Solovay
style):

- `F_0(n) = n + 1`
- `F_{α+1}(n) = F_α^{(n)}(n)` (n-fold iterate)
- `F_λ(n) = F_{λ_n}(n)` at a limit `λ` with fundamental sequence `{λ_n}`.

(Closely related to the Hardy hierarchy `H_α`; `F_α = H_{2^α}` in Wainer's slides' `B`-normalization.)

## Key results

- **Ketonen–Solovay `≺` machinery (Lemma 1 / Theorem 1 region).** For limit `λ < ε₀`: if `β ≺_x λ` then
  `β + 1 ≺_x λ`; and `m < n ⟹ λ_m ≺ λ_n`. The stepping-down relation that makes the ordinal bookkeeping
  work.
- **Theorem 3 (the "easy"/positive direction).** Each `F_α` with `α < ε₀` is **provably total / provably
  recursive in PA** (its defining program's totality is a theorem of PA). Constructive, no proof theory
  needed.
- **"Bounding the Provably Computable Functions" (§ near p. 186 — "the converse of Theorem 3").** The
  **load-bearing direction**: every function whose totality PA proves is **eventually dominated by some
  fixed `F_α`, `α < ε₀`**. Verbatim on method:
  > "The strategy is to first **embed PA in an infinitary system** of arithmetic which replaces the
  > induction axioms and the ∀-rule by the so-called **ω-rule** … Then by well-known proof-theoretic
  > methods, all but the most trivial applications of the **Cut-rule can be eliminated** and from the
  > resulting proofs we can read off bounds on existential theorems. The cut-elimination method stems from
  > Gentzen, then Schütte, Tait, Takeuti, Feferman, Prawitz … The proof here is due to **Buchholz** and is
  > based on the treatment by **Tait [1968]**. See also **Schwichtenberg [1977]**."
  - The essential ingredient is a careful **ordinal assignment `< ε₀`** to ω-proofs that both measures
    proof "length" and gives **direct estimates of number-theoretic witness bounds** for existential
    (Σ₁) theorems. Inversion lemmas + the reduction of a `∃xB(x)` / `∀x¬B` cut drive it.

Together: **`f` is PA-provably-recursive ⟺ `f` is (elementary in / dominated by) some `F_α`, `α < ε₀`**,
and `F_{ε₀}` is not PA-provably-total. This is exactly the classification cited by Cichoń (1983) to get
Goodstein independence.

## Relevance to the expedition

- **Source discipline**: use this as the **named citation** for the Wainer classification wherever the repo
  currently defers to Fairtlough–Wainer. It is open, primary, and proves both directions.
- **The axiom `wainer_bound_of_pa_proves_goodstein` = the "Bounding" converse here.** If the project's
  terminal state must be **axiom-free** (operator decision, 2026-07-01), then this section is the
  **blueprint to formalize** — and it is the ε₀ girder: embed PA in ω-logic (`PA_∞`), ordinal-assign
  `< ε₀`, partial cut-elimination, read off Σ₁ witness bounds. Un-formalized in any prover; ~Bryce–Goré
  scale in Lean. It is **origination, not decomposition** (cf. `EXPEDITION-PLAN.md`).
- **Merit of the Buchholz operator method vs. Route A**: it works at the **meta level** (ordinary
  reasoning about `PA_∞` derivations), so it drops Route A's extra un-precedented layer (arithmetizing the
  bridge *inside* IΣ₁ for Gödel II). Same girder, cleaner entry point.

## Faithfulness caveat

- The exact constants/forms in Theorem 3 and its converse (which normalization of `F_α`, the precise
  "eventually dominated" vs "elementary-in" phrasing) should be **read off the PDF** before being pinned
  into a Lean `Statement`, not transcribed from this summary. The OCR of the scanned AMS volume is lossy;
  this summary captures the architecture and method, not verbatim displayed formulas.
