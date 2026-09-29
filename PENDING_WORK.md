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
   *Open*: the internal order lemmas — see "Next attack" below.
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

## Next attack (lap 4)

The internal order layer of `InternalFund`:

* `icmp_ifdVal_lt` : `isNF c → ifdKind c ≠ 0 → icmp (ifdVal c n) c = 0`
  (**the load-bearing internal lemma** — it is what makes step 4 a one-step argument).
  Internal `𝚺₁` course-of-values induction on `c`, mirroring `icmp_trans`'s `∀ w, ∀ a ≤ w` shape.
* `isNF_ifdVal` : `isNF c → isNF (ifdVal c n)`.

`icmp_ifdVal_lt` is the load-bearing one and the next real wall: it is an *internal* `𝚺₁`
course-of-values induction on the code, of the same shape as Wu's `icmp_trans`
(`∀ w, ∀ a ≤ w, …`), and it is what turns the limit case of progressiveness into a single step.
