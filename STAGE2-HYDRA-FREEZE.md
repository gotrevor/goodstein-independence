# Stage 2 freeze: PA ⊬ the canonical hydra battle — statement for review

**Status: PROPOSED 2026-09-26, awaiting ratification.**  Decision (a) (Trevor + Astra): one
computable legal strategy; headline = PA cannot prove termination even for this strategy.

## 1. The object (DONE, sorry-free) — `lean-gallery` PR #18

`LeanGallery/Logic/Hydra/Canonical.lean` (branch `hydra-canonical`), on the gallery's own
`Hydra` / `Chop` / `Step`:

- `ord : Hydra → ONote` — Kirby–Paris ordinal, CNF natural sum `♯ ω^{ord c}`.
- `canonStep n : Hydra → Hydra` — descend along the **first child of minimal `ord`** until a head
  is reached; chop it.  Turn `n` leaves **`n + 1` copies total, the survivor included**
  (`Chop.grand`).  Dead hydra fixed.
- `battle h : ℕ → Hydra` — `battle h 0 = h`, `battle h (k+1) = canonStep k (battle h k)`: starts at
  turn 0.
- `ofCode : ℕ → Hydra` — bijection (`0 ↦ leaf`, `⟪a,b⟫+1 ↦` `ofCode b` with child `ofCode a`
  prepended); inverse `toCode`.

Proved there: **`canonStep_legal`** (`h ≠ leaf → Step n h (canonStep n h)`, the bridge Astra asked
for), `battle_terminates` (axiom-clean, from `hydra_terminates`), `ofCode_surjective`.  Anchors:
battle lengths 1, 2, 4 for `ord` = 1, ω, ω+1, hand-computed.

Why minimal-`ord` rather than list position: `Chop` fixes its output shapes (regrown copies go to
the END, a deep result to the FRONT), so any "leftmost/rightmost in stored order" rule stops
tracking the fundamental sequence after one move.  The minimal-`ord` rule is order-independent up
to ties between equal-ordinal children.

## 2. The headline — PROPOSED

Quantify over **every** Σ₁ formula that defines the battle correctly in ℕ, instead of freezing one
hand-built internal formula:

```lean
theorem pa_not_proves_hydra
    (φ : Semisentence ℒₒᵣ 2) (hφ : Arithmetic.Hierarchy 𝚺 1 φ)
    (hdef : ∀ m N : ℕ, (ℕ ⊧/![N, m] φ) ↔ battle (ofCode m) N = leaf) :
    𝗣𝗔 ⊬ ↑(∀⁰ ∃⁰ φ : Sentence ℒₒᵣ)

/-- Anti-vacuity: the hypothesis class is inhabited. -/
theorem exists_sigma1_battle_def :
    ∃ φ : Semisentence ℒₒᵣ 2, Arithmetic.Hierarchy 𝚺 1 φ ∧
      ∀ m N : ℕ, (ℕ ⊧/![N, m] φ) ↔ battle (ofCode m) N = leaf
```

Why this form:
- **Not gameable.**  The Goodstein repo freezes a specific `igoodsteinDef`, and its bridge alone
  does not pin it (the July handoff: the iff collapses to "ℕ ⊨ γ" because the RHS is a theorem).
  Here the only trusted objects are the ℕ-side definitions above; every correct Σ₁ encoding is
  covered at once, including any one a reader writes.
- **No internal battle arithmetization to grind.**  `pa_not_proves_hydra` follows from stage 1
  (`pa_provable_pi2_eventually_witnessed_below_fastGrowing`) plus the lower bound below.
  `exists_sigma1_battle_def` should come from Foundation's Σ₁-representation of r.e. relations
  (the Goodstein bridge already uses `REPred`); `battle` is computable.

## 3. The grind — the lower bound (route, not yet a bridge)

```lean
theorem battle_escapes_fastGrowing (o : ONote) (ho : o.NF) :
    ∀ M, ∃ m ≥ M, ∀ N ≤ fastGrowing o m, battle (ofCode m) N ≠ leaf
```

Proposed route (Astra: "essentially Hardy" is the route, not the bridge):
1. Canonical move = fundamental sequence: `ord (canonStep n h) = (ord h)[n]` (the Cichoń/
   Buchholz–Wainer fundamental sequences, `ω^{β+1}[n] = ω^β·(n+1)`), for `ord h` a limit; and
   `ord` drops by one on a successor.
2. Hence battle length from turn `t` is a Hardy-type function of `ord h` (Cichoń 1983's
   hydra ↔ Hardy correspondence; the repo already has `hardy`, `fastGrowing`, and Goodstein's
   version of this step in `LowerBound.lean` / `Domination.lean`).
3. Escape: take `h_k` = the ω-tower of height `k`.  `toCode h_k` grows elementarily in `k`, the
   battle length grows like `H_{ω↑↑k}`, so for each `o < ε₀` the length eventually beats
   `f_o(toCode h_k)`.

## 4. Packaging

g-i pins mathlib v4.31.0 (Foundation); lean-gallery pins v4.33.1, so g-i cannot `require` the
gallery as-is.  Plan: split `Logic/Hydra/{Basic,Engine,Statement,Canonical}` into a small Lake
package (a subdirectory of lean-gallery, `require`d at a SHA by both, mathlib unpinned there so
each root's pin wins).  Needs a check that the four files compile on both mathlib versions.
