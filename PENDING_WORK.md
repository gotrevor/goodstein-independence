# WAINER-LOWER — open obligations

**NONE.  The target is met.**  `GoodsteinWu.fastGrowing_provably_total` and
`GoodsteinWu.wainer_classification` are proved sorry-free with
`#print axioms = [propext, Classical.choice, Quot.sound]` (zero mathematical axioms), audited by
`scripts/AxiomCheckWu.lean`.  See `STATUS.md` for the overview and `DIRECTION.md` for the closing
directive.  The route record below is kept as the reference for how it was done.

Target (met): `GoodsteinWu.fastGrowing_provably_total` (frozen) in `GoodsteinWu/WainerLower.lean`.

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
3. **The Σ₁ graph of `fastGrowing`** — DONE, lap 6, sorry-free
   (`GoodsteinWu/FastGrowingGraph.lean`).  `fgGraph c n y` ("`f_c(n) = y`") is
   `∃ w, fgWit w ∧ fgStepIn w c n y`, with `𝚺₁.Semisentence` `fgGraphDef`.

   The witness `w` is an HFS **set** of entries `⟪⟪d, m⟫, ⟪v, u⟫⟫`, every member justified by
   other members (`fgWit`), with no index ordering — a justifier may be any member.  Clauses:
   `d = 0 ∧ v = m+1`; `ifdKind d = 1` with an iteration sequence `u` of length `m+1` from `m`
   to `v` all of whose steps `⟪p, u_j⟫ ↦ u_{j+1}` (`p = ifdVal d 0`) are in `w`; `ifdKind d = 2`
   with `⟪ifdVal d m, m⟫ ↦ v` in `w`.

   Why a set and not a sequence: `fgJust` is monotone in `w` (`fgJust_mono`, via
   `le_of_subset`), so `fgWit w → fgWit w' → fgWit (w ∪ w')` (`fgWit_union`) — witnesses merge
   for free and the progressiveness proof never concatenates or reindexes.  Well-foundedness is
   not used inside PA at all; it is only needed externally at ℕ, where every justifier's
   ordinal is `≺`-smaller by `icmp_ifdVal_lt`.

4. **Progressiveness** — internal half DONE, lap 7, sorry-free (`GoodsteinWu/Progressive.lean`,
   `fgTotal_progressive`: in every model of `𝗜𝚺₁`, `(∀ d, isNF d → isNF c → icmp d c = 0 →
   fgTotal d) → fgTotal c`, where `fgTotal c := isNF c → ∀ n, ∃ y, fgGraph c n y`).  All three
   cases closed: zero (singleton witness), limit (one step off `icmp_ifdVal_lt` + `isNF_ifdVal`),
   successor (`fgIter`, a `𝚺₁` succ-induction building the iteration sequence).  Helpers added to
   `InternalFund.lean`: `ifd_kind_indep` (the kind tag does not depend on the index — needed
   because the `fgJust` limit clause reads `ifd c n` while the successor clause reads `ifd c 0`)
   and `ifd_kind_cases`.  **Remaining for step 4:** turn this into `𝗣𝗔 ⊢ Prog(precCode, ψ)` —
   pick the `LX`-formula `ψ` (the image under `lMap toLX` of `fgTotalDef`, a Π₂ arithmetic
   formula), prove its evaluation lemma in an arbitrary model, and apply completeness.
   [old text] `𝗣𝗔 ⊢ Prog(≺, ψ)` for `ψ(c) := isNF c → ∀n ∃y F(c,n,y)`.
   Zero case trivial; limit case one step (`ifdVal c n ≺ c`); successor case is the only one
   needing induction — Σ₁-induction on `i ≤ n` building the iteration sequence `u`.
4b. **Progressiveness in `PA[X]`** — DONE, lap 8, sorry-free (`GoodsteinWu/ProgTransfer.lean`,
   `concrete_prog : paLX ⊢ progStatement` with `progStatement = (progAt precCode fgTotalCode).univCl`).
   `fgTotalDef : ArithmeticSemisentence 1` is `“c. !nfDef c → ∀ n, ∃ y, !fgGraphDef c n y”`,
   `fgTotalCode = liftCode fgTotalDef`.  Route: `arithProgStatement` (the ℒₒᵣ mirror) is proved
   in `𝗜𝚺₁` by completeness + `fgTotal_progressive`; `map_prog_body` is the syntactic
   `lMap toLX`-identity; `paLX_of_peano_semantic` transports.  *simp discipline*: a bare `simp`
   on the whole statement OOM-kills the elaborator (Wu's W7) — evaluation goes through the two
   small lemmas `eval_arithPrecAt` / `eval_arithFgAt`, and `Matrix.empty_eq` does not fire, so
   the substitution vector is rewritten by an explicit `show … from funext`.

5. **Apply `gentzen_upper_bound`** at `φ := lMap toLX (emb ψ)` and `a := o+1`, add
   `arithmetic_nonote_prec` for `o ≺ o+1`, then step 1 to come back to `𝗣𝗔`.
   DONE, lap 9, sorry-free (`GoodsteinWu/ApplyTI.lean`): `peano_fg (a : NONote) : 𝗣𝗔 ⊢ arithFgClosed a`,
   where `arithFgClosed a = (arithFgAt ⌜nonoteCode a⌝).univCl`, i.e. `𝗣𝗔` proves
   `isNF ⌜a⌝ → ∀ n, ∃ y, fgGraph ⌜a⌝ n y`.  `b` is taken from `exists_lt_nonoteTower` rather
   than `a+1` (no NF side condition to discharge).  Added `peano_of_paLX_semantic` to
   `Conservation.lean` (the mirror of Wu's `paLX_of_peano_semantic`).

6. **Read off** the frozen statement — DONE, lap 10, sorry-free.
   `GoodsteinWu/Readoff.lean`: `fgStepIn_sound` / `fgGraph_sound`, the ℕ soundness of `fgGraph`.
   The recursion is **Lean's own**, on `o : ONote` with the order `ONote.fastGrowing` itself
   recurses on (`InvImage.wf ONote.repr Ordinal.lt_wf`), and — the one simplification over the plan
   — it needs **no `NF` hypothesis and no internal `icmp`/`isNF` reasoning at all**:
   `fsVal o n < o` holds for *every* `o`, straight out of mathlib's
   `fundamentalSequence_has_prop` (`o.repr = succ (fsVal o 0).repr` in the successor case,
   `(h.2.1 n).2.1` in the limit case).  `FundBridge.ifd_modelCode` turns each `fgJust` clause into
   the matching `fundamentalSequence` clause; the successor clause closes with an ordinary
   ℕ-induction showing `znth u j = (fastGrowing (fsVal o 0))^[j] n`.
   So `icmp_ifdVal_lt` and `isNF_ifdVal` (laps 4–5) are load-bearing for step 4 only, not step 6.

   `GoodsteinWu/FgFormula.lean` assembles the frozen statement:
   `fgSem o = fgGraphDef.rew (Rew.subst ![⌜code o⌝, #1, #0])`, so `fgFormula o := (fgSem o).val` is
   Σ₁ by `sigma_prop` (no hand-rolled hierarchy proof).  `exists_fgGraph` discharges the
   `isNF ⌜o⌝` guard of `peano_fg` by `isNF_modelCode` in an arbitrary model of `𝗣𝗔`;
   `peano_fgFormula` lifts that to `𝗣𝗔 ⊢ ∀ n, ∃ y, fgFormula o` by
   `FirstOrder.Arithmetic.complete.{0} 𝗣𝗔`.  The `←` half of the frozen `↔` is the ℕ-instance of
   that proof (no witness built by hand), with `fgGraph_sound` naming its value.

## Next attack — none (target met).  Superseded record below: the lap-7 attack plan for step 4.

`GoodsteinWu/Progressive.lean`.  Work internally in a model `V ⊧ 𝗣𝗔` (then transfer by
completeness, as Wu does throughout).  With `ψ(c) := isNF c → ∀ n, ∃ y, fgGraph c n y`, prove

    (∀ d, isNF d → isNF c → icmp d c = 0 → ψ d) → ψ c

by cases on `ifdKind c` (using `ifd_ocOadd` / `ifd_kind_ne_zero`):

* `c = 0`: the singleton witness `{⟪⟪0,n⟫,⟪n+1,0⟫⟫}`.
* `ifdKind c = 2`: `d := ifdVal c n` is `≺ c` (lap 4) and `isNF` (lap 5); take its witness `w`,
  return `w ∪ {⟪⟪c,n⟫,⟪y,0⟫⟫}` and close with `fgWit_union` + `fgJust_mono`.
* `ifdKind c = 1`, `p := ifdVal c 0`: `𝚺₁`-induction on `j ≤ n` for
  `∃ w u, fgWit w ∧ Seq u ∧ lh u = j+1 ∧ znth u 0 = n ∧ ∀ i < j, fgStepIn w p (znth u i) (znth u (i+1))`
  (a `𝚺₁` statement).  Step: apply `ψ p` at `znth u j`, union the witnesses, `seqCons` the value
  onto `u`.  At `j = n`, add the entry `⟪⟪c,n⟫,⟪znth u n, u⟫⟫`.

The only genuinely new Lean work is that `𝚺₁`-induction; everything it needs is banked.

--- superseded design notes (lap 6, now implemented) ---

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
