# WAINER-LOWER — open obligations

Target: `GoodsteinWu.fastGrowing_provably_total` (frozen) in `GoodsteinWu/WainerLower.lean`.

## Route (refined lap 2; supersedes the sketch in WAINER-LOWER.md where they differ)

Everything is done with `φ` **X-free** (the image of an arithmetic formula under `lMap toLX`), so
`SubstX.substX` is not needed: `gentzen_upper_bound` already takes an arbitrary
`φ : Semiformula LX ℕ 1`.

1. **Conservation** — DONE, lap 1, sorry-free (`GoodsteinWu/Conservation.lean`,
   `peano_of_paLX`).  This was the only ingredient absent from Wu's package.
2. **Internal fundamental sequences** — definitions DONE, lap 2, sorry-free
   (`GoodsteinWu/InternalFund.lean`): `ifd c n = ⟪kind, value⟫` with kind `0/1/2` =
   zero/successor/limit, by a course-of-values table on the code `c` (parameter `n`), plus the
   recursion lemma `ifd_ocOadd`.  Mirrors `ONote.fundamentalSequence` clause by clause.
   Correctness against mathlib DONE, lap 3, sorry-free (`GoodsteinWu/FundBridge.lean`,
   `ifd_modelCode`): for every external `o : ONote` and every standard `n : ℕ`,
   `ifd (modelCode o) n = ⟪fsKind o, modelCode (fsVal o n)⟫`.  The transcription — including
   mathlib's `i.succPNat` ↦ internal `n + 1` and the `m.natPred` coefficient bookkeeping — is
   therefore confirmed, before any internal induction is spent on it.
   Internal descent DONE, lap 4, sorry-free: `ifd_kind_ne_zero` (only `0` has kind `0`) and
   **`icmp_ifdVal_lt`** — `isNF c → c ≠ 0 → icmp (ifdVal c n) c = 0`, i.e. `c[n] ≺ c` and
   `pred c ≺ c`, uniformly in `n`.  `𝚺₁` course-of-values induction on the code.
   Normal-form closure DONE, lap 5, sorry-free: `isNF_ifdVal` — `isNF c → isNF (ifdVal c n)`,
   proved together with the invariant "the leading exponent never increases", which is what the
   `r ≠ 0` branch needs to rebuild the tail condition.  **The `InternalFund` layer is complete.**
3. **The Σ₁ graph of `fastGrowing`** — not started.  Design: a Δ₀ "justification sequence"
   predicate.  A witness is a sequence of entries `⟪d, m, v, u⟫`, each justified by *earlier*
   entries: `d = 0 ∧ v = m+1`; or `d` a successor with predecessor `e` and `u` a sequence with
   `lh u = m+1`, `u_0 = m`, `u_m = v`, every `⟪e, u_i, u_{i+1}, _⟫` earlier; or `d` a limit and
   `⟪ifdVal d m, m, v, _⟫` earlier.  `F(c,n,y) := ∃w (T(w) ∧ last w = ⟪c,n,y,_⟫)` is then Σ₁ and
   the fast-growing recursion equations are witness surgery, not induction.
   Functionality of `F` is only ever needed **at ℕ**, externally (step 6), never inside PA.
4. **Progressiveness**: `𝗣𝗔 ⊢ Prog(≺, ψ)` for `ψ(c) := isNF c → ∀n ∃y F(c,n,y)`.
   Zero case trivial; limit case one step (`ifdVal c n ≺ c`); successor case is the only one
   needing induction — Σ₁-induction on `i ≤ n` building the iteration sequence `u`.
5. **Apply `gentzen_upper_bound`** at `φ := lMap toLX (emb ψ)` and `a := o+1`, add
   `arithmetic_nonote_prec` for `o ≺ o+1`, then step 1 to come back to `𝗣𝗔`.
6. **Read off** the frozen statement: Σ₁-ness of `F(⌜o⌝, ·, ·)` and its ℕ-reading
   `↔ y = ONote.fastGrowing o n` (external induction: soundness = functionality at ℕ,
   completeness = build the witness).

## Next attack (lap 6) — step 3, the Σ₁ graph of `fastGrowing`

Everything `InternalFund` owes is paid.  Build `GoodsteinWu/FastGrowingGraph.lean`:

* `fgEntry`-shaped witnesses.  A witness `w` is a `Seq` whose `i`-th entry is `⟪⟪d, m⟫, ⟪v, u⟫⟫`,
  read "`f_d(m) = v`, justified by the auxiliary iteration sequence `u`".  The justification
  predicate `fgJust w i` is Δ₀ (every quantifier bounded by `w`):
  - `d = 0` and `v = m + 1`;   (kind `0`)
  - `ifdKind d = 1`, `e := ifdVal d 0`, and `u` is a `Seq` with `lh u = m + 1`, `znth u 0 = m`,
    `znth u m = v`, and for every `i < m` some earlier entry is `⟪⟪e, znth u i⟫, ⟪znth u (i+1), _⟫⟫`;
  - `ifdKind d = 2` and some earlier entry is `⟪⟪ifdVal d m, m⟫, ⟪v, _⟫⟫`.
* `fgGraph c n y := ∃ w, (∀ i < lh w, fgJust w i) ∧ last entry of w is ⟪⟪c, n⟫, ⟪y, _⟫⟫` — `𝚺₁`.
* `𝚺₁`-definability of `fgGraph` (`fgGraphDef`) and its evaluation lemma.

Design notes that matter: the auxiliary `u` is *inside* the entry, so the whole justification
stays Δ₀ and `fgGraph` is a single existential; functionality of `fgGraph` is never needed
inside PA, only at ℕ in step 6.  The `ifdKind d = 1` clause uses `ifdVal d 0` because the
predecessor does not depend on the index.
