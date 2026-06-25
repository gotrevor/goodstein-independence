# Castéran — "Hydra Battles in Coq"

## Provenance

- **File**: `casteran-hydra-battles-in-coq.pdf` (this directory)
- **Title**: *Hydra Battles in Coq*
- **Author**: Pierre Castéran (LaBRI, Univ. Bordeaux, CNRS UMR 5800, Bordeaux-INP), with contributions by Évelyne Contejean, Florian Hatat, Pascal Manoury
- **Version**: DRAFT dated November 4, 2020 (a book-length, evolving document, ~166 pp)
- **Source repo**: `https://github.com/coq-community/hydra-battles` (the Coq development the book documents; libraries under `theories/`, coqdoc HTML under `theories/html/hydras.*`)
- **Built with**: Coq 8.11.0, plug-ins `coq-paramcoq` and `coq-equations`
- **Primary scholarly references it adapts**: Kirby & Paris (KP82) "Accessible independence results for Peano arithmetic"; Ketonen & Solovay (KS81) "Rapidly growing Ramsey functions" (*Ann. of Math.* 113); Schütte (Sch77) *Proof Theory*, ch. V; Manolios & Vroon (MV05) ordinal arithmetic; Wainer (Wai70), Buchholz-Wainer (BW85), Prömel (Prö13) on the fast-growing hierarchy.

## Abstract / Scope

A large Coq library + accompanying textbook formalizing the **Kirby–Paris Hydra game** and the proof-theoretic apparatus of ordinals below ε₀ (and a first draft of Γ₀). The central narrative: prove in Coq that **every (free) Hydra battle terminates** via an ordinal variant `m : Hydra → T1` mapping into `[0, ε₀)` (`every_battle_terminates`), then — following Ketonen–Solovay — prove the **converse impossibility**: there is **no** variant bounded by any `μ < ε₀` (so the full strength of ε₀ is genuinely needed). It then **measures how long battles are** in terms of the **Hardy hierarchy** `H_α` and **Wainer hierarchy** `F_α` of rapidly-growing functions. The development is constructive and axiom-free except in the Schütte chapter (which is axiomatic/classical). Goodstein sequences are mentioned (KP82, Goo44, Sla07 "The Termite and the Tower") as a sibling unprovable-in-PA termination problem, but **the book contains no formalized Goodstein development** — no Goodstein sequence type, no `goodstein_length`, no Goodstein↔ordinal map. The repo *as a whole* (coq-community/hydra-battles) is known to also host a Goodstein module, but that material is **not in this PDF**.

## Key Content (what is formalized, with Coq names)

### ε₀ ordinal notations (Ch. 4, module `Epsilon0.T1` / `Epsilon0.E0`)
- `Inductive T1 := zero | ocons : T1 → nat → T1 → T1` — Cantor normal form terms; `ocons α n β` means ω^α × (n+1) + β. (`T2` with `gcons` is the Γ₀ / Veblen-normal-form analogue, Ch. 8.)
- Notations: `phi0 α` = ω^α; `omega`; `FS n`/`fin` coercion for finite ordinals; `omega_tower height` builds ω-towers approximating ε₀.
- `compare`, `lt_b`/`lt`, `nf_b`/`nf` (Boolean + Prop "is in Cantor normal form"); `LT`/`LE` = `lt`/`le` restricted to normal forms.
- `Class E0 := {cnf : T1; cnf_ok : nf cnf}` — the **subset type of genuinely well-formed ordinals < ε₀** (sigma of a T1 term + a normality proof), used wherever total recursive functions over ordinals are needed.
- Arithmetic: `succ`, `plus`, `mult` (structural on T1; non-commutative); `succb`/`limitb` classify successors/limits; `zero_succ_limit` case-split.
- **Well-foundedness + transfinite induction**: `nf_Acc`/`T1_wf` (`well_founded LT`), `transfinite_recursor`, the `transfinite_induction` tactic. (Alt. proof via Contejean's RPO in `Epsilon0rpo`.)
- `Hessenberg`/natural sum `oplus` (`o+`, `α ⊕ β`), commutative+associative+strictly monotone — the variant used for chopping Hydra heads.
- `ON`/ordinal-notation type class + `Epsilon0_correct` proving the T1 model matches Schütte's axiomatic ordinals (Ch. 7).

### Canonical (fundamental) sequences (Ch. 5, module `Epsilon0.Canon`)
- `canonS : T1 → nat → T1` with `canonS α i = {α}(i+1)`, and `canon α i` = `{α}(i)`. This is the **fundamental-sequence assignment** `{α}(i)` — exactly the machinery a Goodstein/Hardy route needs.
- Key proved properties: `canonS_succ` (`{α+1}(i)=α`), `canonS_LT` (`{α}(i) < α` for α≠0), `canonS_limit_strong`/`canonS_limit_lub` (a limit λ is the strict lub of its canonical sequence).

### Accessibility / paths inside ε₀ (Ch. 5, module `Epsilon0.Paths`)
- `transition`, `path_to` (inductive), `LT_path_to` (every β<α is reachable by a finite path of canonical-sequence steps), `path_to_LT`.
- `Hydra.O2H`: injection `iota : T1 → Hydra` (`ι(α)`) translating ordinals to hydras; `canonS_iota` and `path_to_battle` map canonical-sequence steps ↔ hydra-battle rounds. The **Ketonen–Solovay "standard path"** apparatus (`Epsilon0.KS`): `standard_path`, `const_path` (i-paths), `Cor12` (index-raising), `constant_to_standard_path`, `standard_gnaw`.

### Large sets + length functions L_α (Ch. 6, module `Epsilon0.Large_Sets`, `L_alpha`)
- `mlarge α s` / `gnaw` / `large` — minimally-α-large sequences.
- **`L_ α (k)`** = length of the minimal large sequence / number of steps of the standard battle from ι(α) with replication factor k. Defined as a total function over `E0` via `coq-equations` well-founded recursion: `L_zero_eqn` (`L_ 0 i = i`), `L_lim_eqn`, `L_succ_eqn`. Exact closed forms proved for small α: `L_omega`, `L_omega_mult` (`L_{ω·i}(k)=2^i(k+1)−1`), `L_omega_square`, `L_omega_cube`, etc. `L_correct : L_spec (cnf α) (L_ α)`.
- `battle_length_std` ties standard-battle length to `L_α`.

### Hardy / Wainer–Hardy hierarchy H_α (Ch. 6 §6.3, module `Epsilon0.H_alpha`)
- **`H_ : E0 → nat → nat`** = the **Hardy function `H_α`**, defined by transfinite recursion over E0 via `coq-equations`:
  - `H_α(k)=k` (α=0), `H_{α+1}(k)=H_α(k+1)`, `H_λ(k)=H_{ {λ}(k+1) }(k)` (limit).
  - Rewrite lemmas `H_eq1..H_eq4`, `H_eqn`. Exact formulas: `H_Fin`, `H_omega` (`H_ω(k)=2k+1`... up to bookkeeping), `H_omega_i`, `H_omega_sqr` (`H_{ω²}(k)=2^{k+1}(k+1)−1`), `H_omega_cube`, `H_Phi0_omega` / `H_Phi0_omega_closed_formula` (a closed form for `H_{ω^ω}`).
- **Abstract properties** (Record `P`, theorem `P_alpha`): `H_α` strictly monotone, `n<H_α(n)` for α≠0, `H_α ≤ H_{α+1}` pointwise, `H_{α+1}` dominates `H_α` from 1, and the **β<α ⇒ comparison** monotonicity. Also `H_non_mono1` proving H is **not** monotone in its ordinal argument (a non-theorem warning).

### Wainer hierarchy F_α (Ch. 6 §6.4, module `Epsilon0.F_alpha`)
- **`F_ : E0 → nat → nat`** = the **Wainer fast-growing function `F_α`**: `F_0(i)=i+1`, `F_{β+1}(i)=(F_β)^{(i+1)}(i)` (iteration), `F_α(i)=F_{ {α}(i) }(i)` (limit). Defined via `coq-equations` with a lexicographic-on-`(E0,nat)` well-founded order (a workaround `F_star` because the naive `iterate` definition fails Coq's guard checker — documented as `Fail Equations`).
- Rewrite eqns `F_zero_eqn`/`F_lim_eqn`/`F_succ_eqn`; abstract properties `F_alpha_mono`, `F_alpha_ge_S`, `F_alpha_Succ_le`, `F_alpha_dom`, `F_alpha_beta`, `Propp284` (β<α ⇒ F_α dominates F_β).
- **L↔H comparison**: `H_L_` (`H_α i ≤ L_α (S i)`), `battle_length_std_Hardy`. **H↔F comparison** stated as Exercise 6.1 quoting KS81 p.297: `H_{ω^α}(n+1) ≥ F_α(n)` and `F_α(n+1) ≥ H_{ω^α}(n)` — i.e. `F_α` and `H_{ω^α}` have the same growth rate (this relation is **stated as an exercise, not proved in the text**).

### Schütte axiomatic countable ordinals (Ch. 7, module `Ordinals.Schutte` / `Ord`)
- A **non-constructive, axiomatic** development (uses excluded middle, Hilbert ε, description ι) of countable ordinals `Ord` as a strictly-ordered set with three axioms (well-order; bounded ⇒ countable; countable ⇒ bounded). Provides 0, succ, ω, ε₀, Cantor normal form, critical ordinals, and an embedding `T1 ↪ Ord` validating the constructive model. **This is the only axiom-using part of the library.**

### Provably-total classification?
The book does **not** prove a Wainer-style "classification of the provably-recursive functions of PA" theorem. It proves the *combinatorial* Ketonen–Solovay impossibility (no variant below ε₀) and builds the `H_α`/`F_α`/`L_α` hierarchies with their domination lemmas, explicitly *citing* KS81/Wai70/Prö13 for the classification context but leaving the PA-provability classification itself as cited background / future work (§9.1 lists "relationship with primitive recursive functions and provability in PA" as a planned extension).

## Relevance to the Growth-Rate Route (CRITICAL)

A "growth-rate / meta-level" Goodstein independence route typically needs: (1) a Cantor-normal-form ordinal notation < ε₀ with `<` well-founded; (2) **fundamental sequences** `{α}(n)`; (3) the **Hardy hierarchy** `H_α` (Goodstein length is `H_{ε₀}`-ish / each Goodstein step ≈ a Hardy step at the running base); (4) the **Wainer hierarchy** `F_α` and the eventual-domination / Schwichtenberg–Wainer "F_{ε₀} is not provably total in PA" leverage; (5) a clean Goodstein-length ↔ Hardy-value formula.

**What Castéran's library already contains (items 1–4): essentially all of it, and well-tested.**
- (1) ✅ `T1`/`E0` with `nf`, `LT`, `T1_wf` (well-foundedness) + `transfinite_induction` — fully proved, axiom-free.
- (2) ✅ `canonS`/`canon` = `{α}(i)` with all the load-bearing lemmas (`canonS_LT`, limit-is-lub).
- (3) ✅ The **Hardy hierarchy `H_α` is fully formalized** (`Epsilon0.H_alpha`) with exact small-α formulas and the five KS81 abstract growth properties proved.
- (4) ✅ The **Wainer hierarchy `F_α` is fully formalized** (`Epsilon0.F_alpha`) with domination lemmas. The `F_α`↔`H_{ω^α}` same-growth-rate relation is *stated* (Exercise 6.1) but **left unproved** in the book.
- (5) ❌ **The Goodstein-length formula is NOT here.** There is no Goodstein sequence, no base-bumping function, and no theorem of the form "Goodstein length of n = H_{...}(...)". The length results that *are* proved (`L_α`, `battle_length_std`, `battle_length_std_Hardy`) are about **Hydra** standard battles, not Goodstein sequences. The Hydra↔ordinal map `iota` is Hydra-specific; a Goodstein route would need an analogous (and absent) Goodstein↔ordinal/base-n map.

**Bryce–Goré reuse (~4.5k lines of Castéran ordinals)** is entirely plausible against exactly these modules — the ε₀ CNF type, well-foundedness, canonical sequences, and the H/F hierarchies are the reusable, self-contained core and are the part most cited downstream.

**Coq → Lean portability**: this is a **Coq** development (Calculus of Inductive Constructions; depends on `coq-equations` and, for Ch. 7 only, classical axioms). It is **not** directly importable into Lean. A port would mean re-deriving the constructions in Lean 4. The structural recursion + `coq-equations` well-founded definitions translate to Lean's `termination_by`/`WellFounded.fix` and would hit the **same guard-checker friction** the book documents for `F_α` (the `Fail Equations` workaround) — Lean's well-founded recursion is the analogue and has its own non-reducibility-in-kernel pain (cf. the repo's own `[[lean-wf-recursion-no-kernel-reduce]]` note).

**Does mathlib already cover this?** Mathlib has ordinals, `ω`, CNF (`Ordinal.CNF`), and well-foundedness, but as of recent knowledge it does **not** ship a packaged Hardy hierarchy `H_α`, Wainer hierarchy `F_α`, fundamental-sequence assignment `{α}(n)` below ε₀, or Goodstein-length↔Hardy machinery. So the growth-rate route in Lean cannot just `import Mathlib` for items (2)–(4); those would need to be built (porting Castéran's design is a reasonable blueprint) or sourced from an existing Lean ordinal-analysis effort.

**Does Castéran prove or assume Wainer's classification?** Neither in this PDF — the Wainer/Ketonen–Solovay classification of provably-recursive functions is **cited as context** (KS81, Wai70, Prö13), the `F_α`/`H_α` hierarchies and their domination lemmas are *built and proved*, but the PA-provability classification theorem itself is not formalized here (listed as future work). The `F_α ≈ H_{ω^α}` linking relation is stated as an unproved exercise.

## What to read first (if porting)
- Ch. 4 (`Epsilon0.T1`, `Epsilon0.E0`) — the ordinal type, normality, well-foundedness, transfinite induction.
- Ch. 5 §5.2 (`Epsilon0.Canon`) — fundamental sequences.
- Ch. 6 §6.3 (`Epsilon0.H_alpha`) and §6.4 (`Epsilon0.F_alpha`) — the Hardy and Wainer hierarchies (the heart of any growth-rate argument), including the `F_α` guard-checker workaround.
- `Epsilon0.Large_Sets` / `L_alpha` — length functions, if a length↔hierarchy formula is wanted (note: Hydra, not Goodstein).
