# Stage 2 freeze: PA ⊬ the canonical hydra battle — statement for review

**Status: RATIFIED 2026-09-26** (Trevor + Astra, 98%): `pa_not_proves_hydra` and `exists_sigma1_battle_def` exactly as below.  Keep the **pointwise** `(m, N)` equivalence in `hdef` (never weaken it to equivalence of the `∃ N` termination statements); the existence theorem ships with the headline; the lower bound is against the actual numeric code `m` (growth in tower height alone would not suffice); minimal-ordinal strategy, legality bridge and turn convention approved.  PA need not prove `hdef` - its truth in ℕ is all the argument uses.  Decision (a) (Trevor + Astra): one
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

## 2. The headline — RATIFIED

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
  Here no particular formula is trusted: every correct Σ₁ encoding is covered at once, including
  any one a reader writes.  What a reader still audits: the ℕ-side definitions, the Σ₁
  restriction, PA provability and the semantic interpretation `ℕ ⊧/![N, m]` (Astra's correction:
  this *reduces* the formula-specific audit burden, it does not remove the statement from audit).
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

## 5. Status and grind plan (2026-09-26, branch `eps0/hydra`)

**Landed:** packaging (g-i `require`s LeanGallery at a SHA; ⚠️ never `lake update LeanGallery`,
it drags in the gallery's mathlib v4.33.1 pin and bumps `lean-toolchain` — bump the rev by editing
`lakefile.toml` + `lake-manifest.json` by hand), and
`GoodsteinPA.Hydra.pa_not_proves_hydra_of_escape` (`src/GoodsteinPA/HydraIndependence.lean`): the
ratified headline from stage 1, with the lower bound `Escapes` as a hypothesis.

**Remaining, two independent items:**

**(A) `Escapes` — the lower bound.**
- **P1** `ord (canonStep n h)` is Mathlib's `fundamentalSequence` step of `ord h` (predecessor on
  a successor, `f n` on a limit).  Mathlib's convention already matches the gallery's regrowth:
  `ω^(a+1)[i] = ω^a·(i+1)` (`i + 1` copies at turn `i`), `ω^λ[i] = ω^(λ[i])`, and a coefficient
  `m+1` chops the last copy.  Needs: `ord` is NF and permutation-invariant; the minimal child is
  the last CNF term (`ord (node cs) = ord (node rest) + ω^(ord c)`).
- **P2** `t + len(h, t) ≥ hardy (ord h) t`, by induction along the battle: `hardy_succ`,
  `hardy_limit`, `hardy_monotone` (all in `Hardy.lean`).
- **P3** escape by comparison with Goodstein, on the **padded** family (Astra correction,
  2026-09-26): `pad m := node (leaf :: leaf :: children of ofONote (seqONote m 0))`, ordinal
  `seqONote m 0 + 2`.  The canonical strategy chops the two root heads at turns 0 and 1, so the
  intended hydra starts at turn 2, and P2 at argument 0 gives
  `len (pad m) ≥ hardy (seqONote m 0 + 2) 0 = hardy (seqONote m 0) 2 = goodsteinLength m + 2`
  (`Domination.lean`).  ⚠️ The unpadded comparison is FALSE: `seqONote 3 0 = ω+1` dies in 4 moves
  while `goodsteinLength 3 = 5`.  Then
  `goodsteinLength_eventually_strictly_dominates_fixed_fastGrowing` escapes every `f_o`; the code
  bound is proved for `pad m` (Cantor pairing ~ squares per child, elementary in `m`), so
  `f_o(code) ≤ f_{o'}(m)` for a slightly larger `o'`.  Needs `ofONote` with
  `ord (ofONote α) = α`.  The ratified battle and headline are unchanged; only the comparison
  family is.

**(B) `exists_sigma1_battle_def`.**  Foundation's `codeOfPartrec'` (arity 2) +
`code_sigma_one` give a Σ₁ formula for any partial-recursive relation; the work is proving
`fun m N => toCode (battle (ofCode m) N)` is `Computable` (well-founded recursion on a nested
inductive through `ONote`, so not auto-derived — the Goodstein analogue was `primrec_goodsteinSeq`).

## 6. Progress (2026-09-26 evening)

- ✅ **P1** `ord_canonStep` (lean-gallery `hydra-canonical` @ 47b095d, `Logic/Hydra/Ordinal.lean` +
  `Canonical.lean`): `ord` redefined as the natural sum `sumTerms` (fold of `insertTerm`), with the
  three fundamental-sequence lemmas; axiom-clean.
- ✅ **P2** `runFrom_alive_of_lt_hardy` (`src/GoodsteinPA/HydraLowerBound.lean`).
- ✅ **P3** `escapes : Escapes` (`src/GoodsteinPA/HydraEscape.lean`), and so the ratified
  **`pa_not_proves_hydra`**, axiom-clean.  ⚠️ **Route deviation from §5 P3:** no Goodstein
  comparison was needed.  The witness is `k` heads next to the hydra of `ω^P + ω^3`, `P = o + 4`;
  the chain is `f_o(code) < f_P(code) ≤ H_{ω^P}(code) ≤ H_{ω^P}(H_{ω^3}(k)) = H_{ω^P + ω^3}(k)`
  (`fastGrowing_lt_succ_index`, `fastGrowing_le_hardy_omega_pow`, `hardy_add_comp`), with the code
  bounded by one squaring per head (`toCode_padded`: `code + 2 ≤ (C + 2)^(2^k)`, `code ≥ k`) and
  `(C + 2)^(2^k) ≤ 2^(2^k·k) ≤ f_3(k)`.  The padded-Goodstein family (Astra's correction) stays
  valid but unused.
- ✅ **(B)** `exists_sigma1_battle_def` (`src/GoodsteinPA/HydraComputable.lean`): the battle is
  primitive recursive on codes (`primrec_battleC`; `computable_battle` is Astra's sufficient
  target), via `insC` / `ordC` / `pickIdxC` / `chopCC` / `canonC`, each a strong recursion on codes
  with a spec against the gallery definition; then Foundation's `codeOfPartrec'` (arity 2) +
  `code_sigma_one`.  Axioms: the three standard ones plus the inherited `native_decide` of
  `ONoteComp.cmpStep_spec` (exposed as `primrec_Cnat`); the headline itself stays standard.
  Both pinned in `scripts/AxiomCheck.lean`.
- ⏭️ Still open for the stage's discipline: a comparator entry for `pa_not_proves_hydra` (its
  closure is lean-gallery's hydra definitions, which a Challenge would re-declare verbatim under
  their own names, as the gallery's own `Comparator/Hydra` does); merge gallery PR #18, then re-pin.
