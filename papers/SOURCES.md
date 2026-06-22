# Sources — offline proof-theory literature for the Goodstein-independence box

This is the tracked catalog of the open-access literature backing the formalization of
**"Peano Arithmetic does not prove Goodstein's theorem" (Kirby–Paris 1982)** via
**Gentzen's ordinal analysis** (`TI(ε₀) ⊢ Con(PA)`, infinitary PA∞ + ε₀-bounded
cut-elimination) plus Gödel's 2nd incompleteness theorem.

The PDFs themselves live next to this file but are **gitignored** (`papers/**/*.pdf`,
per the KB "never commit PDFs to eventually-public repos" rule) and bind-mounted read-only
into the network-isolated box. This `SOURCES.md` is the only tracked artifact: provenance +
per-source relevance, so the literature is reconstructible and the box knows what each PDF is for.

Phase legend (where each source bites in the formalization):
- **encoding** — base-bumping ↔ Cantor-normal-form / ε₀ ordinal notation, the `G_n(m)` ↔ ordinal map
- **Goodstein ⟹ TI(ε₀)** — Goodstein termination reduces to / is equivalent to transfinite induction below ε₀
- **ε₀ girder** — Gentzen: PA∞ (ω-rule), ordinal assignment < ε₀, ε₀-bounded cut-elimination ⟹ Con(PA)
- **Gödel II hook** — PA ⊬ Con(PA), so PA ⊬ TI(ε₀), so PA ⊬ Goodstein
- **fast-growing** — Hardy / fast-growing hierarchy, provably-total functions of PA (the recursion-theoretic Route B)
- **formalization** — prior machine-checked work (Lean/Isabelle/Coq) informing reuse

All downloads were verified: size > 40 KB, `file` reports `PDF document`, magic bytes `%PDF`.
Verified open-access at download time 2026-06-22 (US network).

## Downloaded

### Kirby, L. & Paris, J. (1982). "Accessible independence results for Peano arithmetic." Bull. London Math. Soc. 14(4), 285–293.
- Source URL: https://mathcircles.org/wp-content/uploads/2022/03/accessible_independence_results.pdf (open scan; canonical paywalled at https://doi.org/10.1112/blms/14.4.285)
- Local file: `kirby-paris-1982-accessible-independence.pdf`
- **The source independence result.** Theorem 1: Goodstein's theorem (formalized in first-order arithmetic) is **not provable in PA** — plus the Hydra game. This is the headline statement the whole box exists to formalize. Page-1 verified: contains the `G_n(m)` definition and the "not provable in P" claim. Phase: **encoding** + **Goodstein ⟹ TI(ε₀)** (the target theorem itself).

### Goodstein, R. L. (1944). "On the restricted ordinal theorem." J. Symbolic Logic 9, 33–41. — see "Needs access"
(No open copy found; original is JSTOR/paywalled. The *content* — the termination theorem via base-bumping ↔ ordinals — is reproduced faithfully in Caicedo, Agboola, Towsner, and Cichon below, which suffice for the encoding phase.)

### Cichoń, E. A. (1983). "A short proof of two recently discovered independence results using recursion theoretic methods." Proc. AMS 87(4), 704–706.
- Source URL: https://www.ams.org/journals/proc/1983-087-04/S0002-9939-1983-0687646-0/S0002-9939-1983-0687646-0.pdf (AMS open)
- Local file: `cichon-1983-short-proof-independence.pdf`
- **Route B (Hardy hierarchy).** Goodstein independence via slow-growing / Hardy hierarchies of functions rather than via Gentzen cut-elimination — the recursion-theoretic alternative path. Page-1 verified (correct paper, p. 704). Phase: **fast-growing** + **Goodstein ⟹ TI(ε₀)** (alternate route).

### Rathjen, M. (2006). "The art of ordinal analysis." Proc. ICM Madrid 2006, vol. II, 45–69. EMS.
- Source URL: https://web.archive.org/web/2id_/https://www1.maths.leeds.ac.uk/~rathjen/ICMend.pdf (Wayback mirror of the author's now-retired Leeds homepage `www1.maths.leeds.ac.uk/~rathjen/ICMend.pdf`, which no longer resolves)
- Local file: `rathjen-2006-art-of-ordinal-analysis.pdf`
- **The map of the whole subject.** Survey of ordinal analysis from Gentzen onward: proof-theoretic ordinals, consistency strength, ε₀ for PA. Page-1 verified (title + abstract + §1 Introduction). Phase: **ε₀ girder** (orientation / canonical references).

### Rathjen, M. (2014). "Goodstein revisited." arXiv:1405.4484 (later in *Gentzen's Centenary*, 2015).
- Source URL: https://arxiv.org/pdf/1405.4484
- Local file: `rathjen-2014-goodsteins-theorem-revisited.pdf`
- **Elementary unprovability of special Goodstein sequences in PA**, using 1940s/50s-era methods. Directly the Goodstein⟹ε₀ link with an eye to what is needed proof-theoretically. Author/title confirmed via arXiv abstract (MSC 03F30/03F50/03C62). Phase: **Goodstein ⟹ TI(ε₀)** + **encoding**.

### Buss, S. R. (1998). "An introduction to proof theory." Handbook of Proof Theory, ch. I, 1–78. Elsevier.
- Source URL: https://mathweb.ucsd.edu/~sbuss/ResearchWeb/handbookI/ChapterI.pdf (author's open copy)
- Local file: `buss-handbook-ch1-intro-proof-theory.pdf`
- **Sequent calculus + cut-elimination foundations.** Gentzen's sequent calculus, the first-order sequent calculus, and the cut-elimination theorem (§2.4) — the proof-theoretic machinery the ε₀ girder is built on. Page-1 verified (TOC: cut elimination at p. 36). Phase: **ε₀ girder** (the cut-elimination engine, finitary version).

### Buss, S. R. (1998). "First-order proof theory of arithmetic." Handbook of Proof Theory, ch. II, 79–147. Elsevier.
- Source URL: https://mathweb.ucsd.edu/~sbuss/ResearchWeb/handbookII/ChapterII.pdf (author's open copy)
- Local file: `buss-handbook-ch2-first-order-proof-theory-arithmetic.pdf`
- **PA proof theory + Gentzen consistency.** Theories of arithmetic, the ordinal ε₀, Gentzen's consistency proof of PA, provably-total functions. The single most on-target modern textbook chapter for the ε₀-girder phase. Phase: **ε₀ girder** + **Gödel II hook** + **fast-growing**.

### Buchholz, W. "Beweistheorie" (Skriptum, 4-std. Vorlesung, WS 2002/03). LMU München. (German)
- Source URL: https://www.mathematik.uni-muenchen.de/~buchholz/articles/beweisth.pdf (author's homepage)
- Local file: `buchholz-beweistheorie-lecture-notes.pdf`
- **The canonical Gentzen-consistency lecture notes.** Buchholz's full proof-theory course: PA, the ω-rule / PA∞, ordinal assignment < ε₀, ε₀-bounded cut-elimination ⟹ Con(PA). 67 pp. Page-1 verified (bibliography cites all three Gentzen consistency papers 1936/1938/1943). **Language: German** — the math (sequent calculus, ordinals, derivations) is symbol-heavy and largely language-independent; pair with the Buss/Siders English expositions. Phase: **ε₀ girder** (the cleanest end-to-end PA∞ construction).

### Buchholz, W. "On Gentzen's first consistency proof for arithmetic." (In *Gentzen's Centenary*, 2015.)
- Source URL: https://www.mathematik.uni-muenchen.de/~buchholz/articles/BuchholzGentzCent1.pdf (author's homepage)
- Local file: `buchholz-on-gentzens-first-consistency-proof.pdf`
- **Modern reconstruction of Gentzen's *original* 1936 consistency proof** (the reduction-procedure form, pre-cut-elimination). Useful for the historical/ordinal-assignment view of the ε₀ girder. 6 pp. Phase: **ε₀ girder** (Gentzen's reduction procedure + ordinal assignment).

### Siders, A. "Gentzen's consistency proofs for arithmetic." (JAIST lecture notes.)
- Source URL: http://www.jaist.ac.jp/~mizuhito/jss12/Siders.pdf (open course notes)
- Local file: `siders-gentzen-consistency-proofs-arithmetic.pdf`
- **Compact modern English exposition of Gentzen's PA consistency proof.** Good companion to the German Buchholz notes for the same ε₀-bounded argument. Phase: **ε₀ girder**.

### Arai, T. (2023). "Lectures on ordinal analysis." arXiv:2304.00246.
- Source URL: https://arxiv.org/pdf/2304.00246
- Local file: `arai-lectures-on-ordinal-analysis.pdf`
- **Modern, self-contained ordinal-analysis lecture notes** (84 pp): ordinal notations, infinitary derivations, cut-elimination, proof-theoretic ordinals. Author confirmed (Toshiyasu Arai). Phase: **ε₀ girder** + **encoding** (ordinal notation systems).

### Freund, A. (2021). "Unprovability in mathematics: a first course on ordinal analysis." arXiv:2109.06258.
- Source URL: https://arxiv.org/pdf/2109.06258
- Local file: `freund-unprovability-first-course-ordinal-analysis.pdf`
- **Pedagogical first course** aimed squarely at independence/unprovability via ordinal analysis (32 pp) — the most accessible on-ramp tying PA, ε₀, cut-elimination, and Gödel II together for the box's exact thesis. Author confirmed (Anton Freund). Phase: **ε₀ girder** + **Gödel II hook** + **Goodstein ⟹ TI(ε₀)**.

### Freund, A. (2022). "Impredicativity and trees with gap condition: a second course on ordinal analysis." arXiv:2204.09321.
- Source URL: https://arxiv.org/pdf/2204.09321
- Local file: `freund-second-course-ordinal-analysis.pdf`
- Companion follow-on to the first course (34 pp). Goes beyond ε₀ into impredicativity; the early sections reinforce the ε₀-girder material. Phase: **ε₀ girder** (deeper/reference).

### Caicedo, A. E. "Goodstein's function." (Expository notes.)
- Source URL: https://andrescaicedo.files.wordpress.com/2008/04/goodstein.pdf (author's site)
- Local file: `caicedo-goodstein-function-notes.pdf`
- Short, clean exposition of Goodstein sequences and the base-bumping ↔ ordinal correspondence. Phase: **encoding** (the `G_n(m)` ↔ CNF/ε₀ map, stated crisply).

### Agboola, A. "The termite and the tower: Goodstein sequences and provability in PA." (UCSB course notes.)
- Source URL: https://web.math.ucsb.edu/~agboola/teaching/2022/spring/8/notes/goodstein.pdf (course site)
- Local file: `agboola-termite-and-tower-goodstein.pdf`
- 22-pp lecture notes walking the full arc: Goodstein sequences → ε₀ → unprovability in PA. A readable end-to-end narrative of the box's whole storyline. Phase: **encoding** + **Goodstein ⟹ TI(ε₀)** + **Gödel II hook**.

### Towsner, H. "Goodstein's theorem, ε₀, and unprovability." (Notes, UPenn.)
- Source URL: https://www.sas.upenn.edu/~htowsner/GoodsteinsTheorem.pdf (author's site)
- Local file: `towsner-goodstein-epsilon0-unprovability.pdf`
- Focused exposition: Goodstein termination ↔ well-foundedness of ε₀, and why that is exactly what PA cannot prove. Phase: **Goodstein ⟹ TI(ε₀)** + **Gödel II hook**.

### Felgenhauer, B. et al. "Nested multisets, hereditary multisets, and syntactic ordinals in Isabelle/HOL." FSCD 2017, LIPIcs 84, art. 11.
- Source URL: https://drops.dagstuhl.de/opus/volltexte/2017/7715/pdf/LIPIcs-FSCD-2017-11.pdf (Dagstuhl LIPIcs, open)
- Local file: `nested-multisets-syntactic-ordinals-isabelle-fscd2017.pdf`
- **Existing Isabelle/HOL formalization** of ordinals < ε₀ as hereditary multisets, with a machine-checked Goodstein's theorem (AFP entry `Nested_Multisets_Ordinals`, theory `Goodstein_Sequence`). Direct reuse model for the ε₀ ordinal-notation layer. Phase: **formalization** (encoding + Goodstein⟹ε₀ in a real proof assistant).
  - Companion AFP entry (not downloaded — browse online): `Goodstein_Lambda` (Felgenhauer), Goodstein function in λ-calculus, outline at https://www.isa-afp.org/browser_info/current/AFP/Goodstein_Lambda/outline.pdf

### Castéran, P. et al. "Hydra battles in Coq" (book; project: *Hydras & Co.*, coq/rocq-community).
- Source URL: https://www.labri.fr/perso/casteran/hydras.pdf (author's site)
- Local file: `casteran-hydra-battles-in-coq.pdf`
- **Existing Coq formalization** (book-length, ~1 MB): ordinal notations up to ε₀ (and toward Γ₀), the Kirby–Paris Hydra battle, and Goodstein sequences as case studies. Builds on the Castéran–Contejean `Cantor` contribution. The richest reuse reference for the encoding + Hydra layers. Phase: **formalization** (encoding + Hydra/Goodstein in Coq).
  - Project repo: https://github.com/coq-community/hydra-battles (HAL paper "Hydras & Co.": https://hal.science/hal-03404668 — landing page only, no open PDF).

### Anonymous / authors. "Formal proof of the weak Goodstein theorem." arXiv:1701.01673 (2017).
- Source URL: https://arxiv.org/pdf/1701.01673
- Local file: `weak-goodstein-formal-proof-2017.pdf`
- Short paper (6 pp) on a machine-formalized proof of the *weak* Goodstein theorem (the base-2/fixed-base variant). Useful as a scoped warm-up target and a comparison point for the encoding. Phase: **formalization** (a smaller, fully-formalized fragment).

### Reuse note: Lean / mathlib4
- Searched `leanprover-community/mathlib4` for "Goodstein" (via `gh api search/code`): hits are **only** in `docs/references.bib` and `docs/1000.yaml` (the "1000 theorems" tracking list). **Goodstein's theorem is NOT yet formalized in mathlib4** — it is a listed but unclaimed target. Implication: this box's Lean formalization would be net-new in the Lean ecosystem; the Isabelle (`Nested_Multisets_Ordinals`) and Coq (`hydra-battles`) formalizations above are the cross-prover references to port intuition from. (No mathlib Goodstein PDF to download.)

## Needs access (paywalled — Cornell EZproxy or manual)

- **Goodstein, R. L. (1944).** "On the restricted ordinal theorem." *Journal of Symbolic Logic* 9(2), 33–41. DOI 10.2307/2268019. JSTOR/Cambridge, paywalled; no open scan located. (Original statement + proof of the termination theorem; content faithfully covered by Caicedo/Agboola/Towsner/Cichon above.) Phase: **encoding** / **Goodstein ⟹ TI(ε₀)**.
- **Gentzen, G. (1936).** "Die Widerspruchsfreiheit der reinen Zahlentheorie." *Math. Ann.* 112, 493–565. (English: "The consistency of elementary number theory," in *The Collected Papers of Gerhard Gentzen*, ed. M. E. Szabó, North-Holland 1969.) Original is German/paywalled; the open Szabó English translation could not be located. (The *source* of the ε₀ girder; reconstructed in Buchholz/Buss/Siders above.) Phase: **ε₀ girder**.
- **Gentzen, G. (1938).** "Neue Fassung des Widerspruchsfreiheitsbeweises für die reine Zahlentheorie." *Forschungen zur Logik*, NS 4, 19–44. (The cut-elimination-style "new version.") Paywalled. Phase: **ε₀ girder**.
- **Gentzen, G. (1943).** "Beweisbarkeit und Unbeweisbarkeit von Anfangsfällen der transfiniten Induktion in der reinen Zahlentheorie." *Math. Ann.* 119, 140–161. (TI below ε₀ is exactly what PA can/can't prove — the sharpness result.) Paywalled. Phase: **Gödel II hook** / **ε₀ girder**.
- **Pohlers, W.** *Proof Theory: The First Step into Impredicativity.* Springer (Universitext), 2009. Textbook, paywalled. (Modern PA∞ + ε₀ cut-elimination textbook.) Phase: **ε₀ girder**.
- **Schütte, K.** *Proof Theory.* Springer (Grundlehren 225), 1977. Textbook, paywalled. (Classic infinitary proof theory.) Phase: **ε₀ girder**.
- **Takeuti, G.** *Proof Theory*, 2nd ed. North-Holland, 1987 (Dover repr.). Textbook, paywalled. (The classic; Gentzen consistency + ordinal diagrams.) Phase: **ε₀ girder**.
- **Fairtlough, M. & Wainer, S. S. (1998).** "Hierarchies of provably recursive functions." Handbook of Proof Theory (ed. Buss), ch. III, 149–207. Elsevier. (Buss posts only his own chs. I & II openly; this chapter is paywalled via Elsevier/ScienceDirect.) (Fast-growing/Hardy hierarchy, provably-total functions of PA — the canonical reference for Route B.) Phase: **fast-growing**.
- **Buchholz, W. (1997).** "Explaining Gentzen's consistency proof within infinitary proof theory." *KGC '97*, LNCS 1289, 4–17. Springer, paywalled (SpringerLink content/pdf returned the paywall page, not the PDF). (The PA-deduction ↔ PA∞-deduction ordinal-assignment correspondence.) Phase: **ε₀ girder**. (Partial substitute downloaded: Buchholz's "On Gentzen's first consistency proof" + the German "Beweistheorie" notes.)
