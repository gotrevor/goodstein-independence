# ON-LINE-FINDINGS — §19.6 commuting ω-rule bound: the Hardy inequality, operator control, and the bounding/cut-elim split

**Fulfils:** `ON-LINE-REQUEST.md` (lap-7/8, narrowed): the §19.6 commuting-`allω` cut-reduction bound for
the witness-bounded `Zᵏ`/`Zekd` calculus. Asks: (1) confirm/correct the Hardy inequality
`h_{βₙ#ω}(max{k,n}) ≤ max{h_{β#ω}(k), n}`; (2) Buchholz operator-controlled derivations for PA/ε₀;
(3) Schwichtenberg–Wainer Ch. 4 Bounding Lemma.

**Host session, 2026-06-22.** Sources: faithful page-by-page read of the on-disk
`papers/buchholz-beweistheorie-lecture-notes.pdf` (67 pp) and `papers/towsner-…pdf` (§15–§20, verbatim);
web (Buchholz operator method LNL chapter; Schwichtenberg–Wainer *Proofs and Computations*; *Slow vs
Fast Growing*, Synthese). Aligned to the live lap-8 state: `wip/OperatorZinfty.lean:780 cutReduceAllAux`
is a disclosed `sorry` (signature validated) — this file is for that proof.

---

## TL;DR — three verdicts

1. **The inequality is FALSE.** `h_{βₙ#ω}(max{k,n}) ≤ max{h_{β#ω}(k), n}` fails for all large `n` whenever
   `βₙ ↛ 0`. Your `+α` analysis is correct. (§1)
2. **Towsner genuinely hand-waves the commuting case** — verbatim "*The other cases follow immediately
   from the inductive hypothesis as in previous arguments*" (p.33), with **no** numeric bookkeeping. What
   "follows immediately" is the **ordinal** part (`α#βₙ < α#β`, `#`-monotonicity); the **numeric-index**
   part is exactly what he skips, and it does **not** hold pointwise. The single-number `k` is the leak.
   (§2)
3. **The on-disk Buchholz notes do NOT contain a PA operator-controlled `H[X]` calculus.** Buchholz's PA
   `Z∞` is **pure-ordinal** (`⊢^α_m`, no numeric `k`, no `τ`); it absorbs `+α` by `#`-monotonicity alone.
   The `H[X]`-operator-closed-under-`#` you described is the **Buchholz-1992/Pohlers** presentation (a
   different text). For PA/ε₀ you don't need set-valued `H` at all — which is exactly why your single
   control ordinal `e` (ADDENDUM 5) is the right-sized fix. (§3)

**Net recommendation:** your `Zekd` `e`-control design is sound and is the minimal correct numeric form.
The conceptually cleanest alternative — and the reason the literature finds the commuting case trivial —
is to **separate cut-elimination (pure ordinals) from witness-bounding (Hardy, on the cut-free proof)**;
the `+α`/`max{k,n}` clash you hit only exists because you thread the witness index *through* cut-elim.
(§4, §5)

---

## §1 — The Hardy inequality is FALSE (you were right; "confirm" requested)

**Claim under test:** `h_{βₙ#ω}(max{k,n}) ≤ max{h_{β#ω}(k), n}` for `βₙ < β`, `τ(βₙ) < max{k,n}`.

**Counterexample.** It is enough to refute it for one admissible family. Fix any single `β'` with
`0 < β' < β` and `τ(β')` finite (so `τ(β') < max{k,n}` holds for all `n`, and a constant ω-rule premise
family `βₙ := β'` is admissible). Then for `n > max{k, h_{β#ω}(k)}`:

- **LHS** `= h_{β'#ω}(max{k,n}) = h_{β'#ω}(n)`. Hardy functions are inflationary and `β'#ω ≥ ω`, so
  `h_{β'#ω}(n) ≥ h_ω(n) = h_n(n) = 2n` (using `ω[n]=n`, `h_n(x)=x+n`). For `β' ≥ ω` it is far larger.
- **RHS** `= max{h_{β#ω}(k), n} = n` (since `n > h_{β#ω}(k)`, and `h_{β#ω}(k)` is a **fixed** constant
  once `k` is fixed).

So `LHS ≥ 2n > n = RHS`. The inequality fails for every sufficiently large `n`. ∎

**Why it fails structurally** (matches your ADDENDUM-1/4 analysis): the conclusion index `h_{β#ω}(k)` is a
constant in `k`, but the IH applied to ω-premise `n` is forced to argument `max{k,n}` (the premise's own
index), and `h_{·}(max{k,n})` **grows with `n`**. Monotonicity of Hardy in the argument runs the wrong way
— you can never pull a witness bound at a larger argument back down to a smaller one. This is the same
wall as the `Hdom`/Lemma-16.10 issue from lap-4 (a bound at `max k n` cannot be lowered to `k`), now one
level up inside cut-reduction. **No Hardy fundamental-sequence identity rescues it in the single-`k`
form.** I checked the candidate `h_{βₙ#ω}(max{k,n}) ≤ h_{β#ω}(k)` (would let the IH output sit under the
conclusion index): also false, same reason (`β_n ↑ β`, `n > k` ⟹ `h_{β_n#ω}(n) > h_{β#ω}(k)`).

---

## §2 — What Towsner actually writes, and why "follows immediately" is legitimate-but-incomplete

**Towsner's ω-rule** (`I∀`), verbatim, Towsner p.23:

> "If, for every `n`, there is a `β_n < α` with `τ(β_n) < max{k,n}` so that `Z∞ ⊢^{β_n, max{k,n}} Γ, φ[n]`
> then `Z∞ ⊢^{α,k} Γ, ∀x φ`."

(So your `Zk.allω` shape is **correct**: premise index `max{k,n}`, side condition `τ(β_n) < max{k,n}`,
premise ordinal `β_n < α` the **conclusion** ordinal.)

**Towsner Thm 19.6** (`cutReduceAll`), verbatim p.33:

> "Suppose `rk(φ) < c`, for every `n`, `Z∞ ⊢^{α,max{k,n}}_c Γ, φ[n]`, and
> `Z∞ ⊢^{β,k}_c Δ, ∃x∼φ, …, ∃x∼φ`. Then `Z∞ ⊢^{α#β, h_{β#ω}(k)}_c Γ, Δ`."

**The whole treatment of the commuting cases**, verbatim p.33 (this is *all* he writes):

> "The main case is `I∃` introducing `∃x∼φ`: … We may apply a cut with `φ[x↦n]` … (Adding ω ensures
> that `h_{β#ω}(k) > 2k > τ(α#β')`.) If the rule is contraction on `∃x∼φ`, the claim follows immediately
> by the inductive hypothesis. **The other cases follow immediately from the inductive hypothesis as in
> previous arguments.**"

**Reading.** Split the bookkeeping into `(ordinal, numeric-index)`:

- **Ordinal part — genuinely immediate.** Re-applying the commuting rule rebuilds the conclusion ordinal
  because `α#β_n < α#β` (`#`-monotonicity in the 2nd arg). This is the exact step Towsner *does* show
  explicitly in the neighbouring fully-written cases (Thm 19.3 ∧/∨, Thm 19.5 `∼φ∨∼φ`: "`τ(α#β') < 2k`",
  "`α#β' < α#β`"). For the pure-ordinal control this is the *only* obligation, so "immediately" is honest.
- **Numeric-index part — the gap.** The IH produces ω-premise `n` at index `h_{β_n#ω}(max{k,n})`, which by
  §1 **exceeds** the reconstructed rule's budget `max{h_{β#ω}(k), n}` for large `n`. Towsner's prose
  inherits "immediately" from the ordinal-only intuition and does not discharge this. It is a real gap in
  the *numeric* presentation, not in the mathematics — which is precisely your discovery.

**Bottom line:** the single numeric `k` is too rigid to be `#`-stable in the commuting case. This is not a
defect you can patch with a cleverer Hardy lemma; it is intrinsic to collapsing the control to one number.
Confidence ~85% (the math is solid; the 15% is "maybe Towsner intends a non-obvious simultaneous
induction that I and the box both failed to reconstruct from the text" — but the verbatim gives no such
hint, and the standard literature routes around it exactly as in §3–§4).

⚠️ **Note on the prior agent extraction:** the digest in
`archive/findings/…lower-bound-verification-and-hardy.md` and the paper-read summary claimed the commuting
case works because "`α#β_ι < α#β` and the numeric bound `h_{β#ω}(k)` is uniform." That is right for the
**ordinal** and over-states the **numeric index** (the IH output index is `h_{β_n#ω}(max{k,n})`, *not*
`h_{β#ω}(k)`). Don't lean on "uniform numeric bound" — it's the thing that fails.

---

## §3 — Operator-controlled derivations for PA (corrects the request's premise)

**Correction first.** The on-disk `buchholz-beweistheorie-lecture-notes.pdf` does **not** present a PA
operator-controlled `H ⊢^α_c Γ` calculus. Its PA/ε₀ material (§4–§7, pp.22–45) is the **pure-ordinal**
Tait system `Z∞ ⊢^α_m Γ`:

- **ω-rule** (the `⋀_∀xA` instance, p.27): from `⊢^{α_t}_m Γ, A(t)` for all `t`, with `α_t < α`, conclude
  `⊢^α_m Γ, ∀xA`. **No second numeric index, no `τ`.** Control = ordinal height + the strict descent
  `α_t < α`, plus a separate finite cut-rank `m`.
- **Reduction Lemma 5.1** (p.28): `d ⊢^α_m Γ,C  &  e ⊢^β_m Γ,¬C  &  rk(C)≤m  ⟹  R_C(d,e) ⊢^{α#β}_m Γ`.
  Commuting case literally: IH gives `⊢^{α_ι#β}_m`, and `α_ι#β < α#β`, reapply the rule. **There is no
  numeric index to thread, so the commuting case is one line.** ← this is the cleanest statement of why
  your obstruction is an artifact of the numeric index.
- **Cut-Elimination 5.2** (p.28): `⊢^α_{m+1} Γ ⟹ E(d) ⊢^{3^α}_m Γ`. (NB: base **3**, not `2^α` and not
  Towsner's `ω^α`. The `Rep` rule exists to make `o(E d) = 3^{o(d)}` definable.)
- **Embedding 5.5 + Cor** (p.30): `Z ⊢ Γ` closed ⟹ `Z∞ ⊢^{ω·k}_m Γ`.
- **Boundedness 5.4** (p.29): for X-positive `Γ`, `Z∞ ⊢^β_1 ¬Prog, ¬Xs₁,…,Γ` with `|sᵢ|≤α` ⟹
  `⊨^{α+2^β} Γ`. Cor: `Z∞ ⊢^β_1 TI_≺(X) ⟹ ‖≺‖ ≤ 2^β`.
- **Composition law** you asked about IS here, as **Lemma 6.9(a)** (p.41): `NF(α,β) ⟹ H_{α+β}=H_α∘H_β`
  (your `hardy_add_collapse`). And **Lemma 6.8** (p.40) is the Hardy monotonicity suite. (Towsner has the
  monotonicity but **not** the composition law as a named lemma — see §6.)
- **Buchholz §7 (p.44) proves Goodstein-in-PA directly** (Satz 7.4: `Z ⊬ ∀x∃y[GS(x,y)=0]`), via
  `h_α(n)=h_{P_n(α)}(n+1)` (Lemma 7.3). ⚠️ §7 is marked "*To be revised*" — draft-quality, cross-check.

**The genuine operator-controlled `H[X]` machinery** (what the request wanted) is **Buchholz's 1992
"operator method"**, a *simplification of Pohlers' local predicativity* (sources below). The PA shape:

- An **operator** `H` is a class function on sets of ordinals that is **monotone** (`X⊆Y ⟹ H(X)⊆H(Y)`),
  **inflationary** (`X ⊆ H(X)`), **idempotent-ish/closed** (`H(H(X))=H(X)`), and **closed under the
  ordinal functions in play** (`+`, natural sum `#`, `α↦ω^α`, and the constants `0,1,…`). Write
  `H[X] := H(· ∪ X)`, and `H[n] := H(· ∪ {n})`.
- **`H ⊢^α_c Γ`** rules: the **ω-rule** requires, for each `n`, `H[n] ⊢^{α_n}_c Γ, A(n)` with
  `α_n < α` and `α_n, n ∈ H[n]`; the **∨/∃-rule** requires the witness and `α₀ ∈ H`; **Cut** of rank `<c`
  with both premises `H`-controlled. The invariant maintained: every ordinal/numeral mentioned in the
  derivation lies in `H[∅]`.
- **Why it absorbs `+α` where `max{k,n}` cannot:** in the commuting ω-case, the IH gives `H[n] ⊢^{α#β_n}`.
  Reapplying the rule needs `α#β_n ∈ H[n]` — which is **immediate** because `H` is **closed under `#`** and
  both `α ∈ H` (the cut formula's side) and `β_n ∈ H[n]` (the ∃-side derivation). No inequality, no Hardy
  identity. The operator is *defined* to contain whatever the ordinal functions produce. That closure is
  the structural content your numeric `k` lacked.
- For **PA/ε₀** the operator never needs a collapsing function `ψ` (those appear only for
  `ID_ν`/`KP`, Buchholz notes §8–§11, in ZFC). A sufficient PA operator is essentially
  `H_η(X) = ` "the closure of `X ∪ {0,η}` under `+,#,ω^·`" for a parameter `η`. **Your single control
  ordinal `e` is the rank-1 shadow of this**: instead of carrying a set closed under the functions, you
  carry one ordinal `e` that *dominates* the relevant closure and is raised only at the top cut (`mono_e`).
  For the PA witness-bounding that is enough, because the only closure you actually consume is "the
  witness stays `≤ hardy e (k+d)`," and `hardy_le_of_lt` + your two composition lemmas reproduce exactly
  the `H`-closure facts you'd otherwise need. So: **`e` ≈ operator control specialized to ε₀; full
  set-valued `H` is not required.** (Confidence the `e`-form suffices for PA: ~80%; the residual risk is
  a commuting case where you need closure under *two different* growth rates at once — watch the principal
  `exI` witness `≤ hardy e (k+d)` interacting with a commuting ω-premise; if that ever needs `e` to depend
  on `n`, you've hit the place where a single ordinal is too weak and you'd promote `e` to a controlled
  `e(n)` — the function-valued index of your ADDENDUM 2.)

---

## §4 — Schwichtenberg–Wainer Bounding Lemma, and the architectural key

S–W *Proofs and Computations* Ch. 4 is **not on disk**; the precise statement below is from the book's
described content + the *Slow vs Fast Growing* literature (Wainer; Cichoń; Weiermann), flagged where I
could not see the page.

**The architectural fact (high confidence, multiply sourced):**

> In a **cut-free** infinitary calculus, the **slow-growing** hierarchy `G_α` bounds the truth-witnesses
> of existential (Σ) statements; **once Cut is added**, the **fast-growing** `F_α` (equivalently Hardy
> `H_{ω^α}=F_α`) supply the bounding functions.

**Bounding Lemma (shape).** If `⊢^α_0 Γ` is a **cut-free** PA_∞ derivation of a `Σ₁` sequent `Γ`
(a disjunction of `∃`-formulas / true atoms), then some disjunct is witnessed by a numeral
`≤ H_α(N)` (Hardy), where `N` bounds the numerals already in `Γ`. Adding cuts of rank `≤ c` first requires
cut-elimination (`α ↦ ω_c^α` / `3^α`-per-level), *then* the cut-free bound applies to the result.

**The key takeaway for your port:** the literature **never** threads the witness/Hardy index *through*
cut-elimination. It runs **two phases**:

1. **Cut-elimination** in a system with **no witness index** (pure ordinal `α`, or operator `H`): the
   ordinal grows (`α ↦ ω_c^α`), the commuting cases are one-liners (`#`-monotonicity / `H`-closure).
2. **Bounding** the resulting **cut-free** ε₀-derivation by `H_α`: here there is no cut, hence no `+α`
   growth, hence the `max{k,n}`-vs-`+α` clash **cannot arise**.

Your `Zk`/`Zekd` tries to do (1) and (2) **simultaneously** with one index — which is *why* §19.6's
commuting case is hard for you and "immediate" for Towsner/Buchholz. Towsner can fuse them only because
his *lower bound* (Thm 17.1, `∀k`) is robust to whatever `k` cut-elim spits out; the fusion is an
optimization, and §19.6 is where the optimization's seams show.

---

## §5 — Recommendation for the Lean port (actionable for `cutReduceAllAux`)

Ranked, hardest-first is **not** the right order here — easiest-correct-first:

1. **(Cleanest, if you can stomach the refactor) Two-phase split.** Define cut-elimination on a
   **witness-index-free** calculus `Z∞ ⊢^α_c Γ` (ordinal + cut-rank only; ω-rule `α_n < α`, no `max{k,n}`,
   no `e`,`d`). Port Buchholz 5.1/5.2 (`R_C`/`E`, `α#β` / `3^α` or your `ω^α`). The commuting ω-case is
   then a **one-liner** (`α#β_n < α#β`). *Separately*, bound the cut-free output by `hardy` — this is your
   existing `lowerBound_hardy_selfcontained` (`∀α NF, ∀k`), already axiom-clean, applied at `c=0`. This
   discards the `(k,d,e)` bookkeeping inside cut-elim entirely. **Most faithful to the literature; biggest
   one-time refactor.**
2. **(Your current path) Keep `Zekd`, finish `cutReduceAllAux` with `e` inert in commuting cases.** This
   is viable (≈80%). The `e`-control *is* the operator specialization; the commuting ω-case keeps `e`
   fixed and bumps only `d ↦ d + norm α` (norm budget) — closes ADDENDUM-1; obstruction-2's witness index
   stays `≤ hardy e (k+d)` because `e` doesn't move (ADDENDUM 5). **The one thing to verify in
   `cutReduceAllAux`:** that you generalize the induction over **both** `k` *and* the premise argument
   (your lap-8 "generalize k,dd") so the IH can be invoked at the ω-premise's own `max k n` *without*
   forcing `e` to grow — i.e. the IH's output witness index must be expressible as `hardy e (max(k,n)+d')`
   with the **same `e`**, then dominated by `hardy_shift_lt_goodsteinLength` (slope 1). If you find a
   commuting case that forces `e` to depend on `n`, that's the §1 wall resurfacing — fall back to (1).
3. **Leaf-NF (ADDENDUM 5 option b) is the correct micro-fix and is faithful.** Every `Z∞` node ordinal is
   `< ε₀` in *both* Towsner (ONote-by-construction) and Buchholz (`ō(d) < ε₀`), so `NF` is a genuine global
   invariant of the calculus, not an artifact. NF-ifying the `Zekd` leaf rules (`trueRel/trueNrel/axL/
   verumR`) so `norm_add_le` applies is **sound** — it matches "every node `<ε₀` ⟹ NF." Your lap-8 commit
   `c8cd83d` (NF-ify leaves) + the `ZekdProv` wrapper is the right call. ✅

**My pick:** if `cutReduceAllAux` closes within a lap or two on the `e`-form, ship (2). If it keeps
spawning sub-obstructions, (1) is the principled escape and reuses your lower bound wholesale.

---

## §6 — Faithfulness corrections (carry these into any write-up)

- **Lemma 16.10 exact statement** (Towsner p.29, verbatim): `α < β ∧ τ(α) < k ⟹ h_α(k) < h_β(k)`
  (**strict**; smaller ordinal under τ-control ⟹ strictly smaller Hardy value). Your KB recollection had
  the variables flipped (`β<α … h_β ≤ h_α`) and `≤` for `<`. Same content, but transcribe Towsner's form.
  Supporting: 16.8 `β>α ∧ τ(α)<k ⟹ β[k]≥α`; 16.9 `α<β ∧ τ(α)<k ⟹ ∃m. β[k][k+1]…[k+m]=α`.
- **`h_{β#ω}(k) = h_β(2k)` is NOT a Towsner lemma.** The paper states only the inline inequality
  `h_{β#ω}(k) > 2k > τ(α#β')` (p.33). The `=h_β(2k)` identity is a *reconstruction* (mine/yours) — treat
  as heuristic, not citable. (It's plausible via `(β#ω)[k]=β#k` + `h_{β+k}=h_β∘h_k`, `h_k(k)=2k`, but
  needs the non-absorbing-sum NF condition; don't assert it without proof.)
- **τ (norm) def** (Towsner Def 8.1, p.10): `τ(0)=0`; for `α = ω^{α₁}c₁ # … # ω^{α_k}c_k` (α₁>…>α_k),
  `τ(α) = max{c₁,…,c_k, τ(α₁),…,τ(α_k)}` — the largest coefficient anywhere in `α`, recursively. Confirms
  `norm = τ`.
- **Cut-elim ordinal base differs by system** — Towsner `ω^α` (Thm 19.7), Buchholz `3^α` (Thm 5.2),
  finitary PL1 `2^k` (Thm 1.5). None is `2^α`. Cite the right one for whichever calculus a doc references.
- **Don't cite "Buchholz lecture notes" for an `H[X]` operator** — they don't have it for PA. Cite
  Buchholz-1992 *"Explaining Gentzen's consistency proof / operator controlled derivations"* or the LNL
  *"How to characterize provably total functions by the Buchholz operator method"* (Möllerfeld/… ) for the
  operator machinery; cite the on-disk notes for the **pure-ordinal** `Z∞` + Hardy 6.8/6.9.
- (Already noted in the prior findings, repeating so it ships) the unprovability survey is **Freund**, not
  Pakhomov: `freund-unprovability-first-course-ordinal-analysis.pdf`.

---

## Sources

- `papers/towsner-goodstein-epsilon0-unprovability.pdf` — ω-rule p.23; Thm 19.6 + commuting-case prose
  p.33; Thm 19.5/19.7/19.9 p.33–34; `h_α` Def 6.3 p.8; Lemma 16.8–16.10 p.28–29; τ Def 8.1 p.10. (read
  verbatim this session)
- `papers/buchholz-beweistheorie-lecture-notes.pdf` — `Z∞` rules p.27; Reduction 5.1 / Cut-elim 5.2 p.28;
  Boundedness 5.4 p.29; Embedding 5.5 p.30; Hardy 6.8 / composition 6.9(a) p.40–41; Goodstein §7 p.44;
  ψ-collapsing (ID_ν, not PA) §8–§11 p.46–66. (read verbatim this session)
- W. Buchholz, *"How to characterize provably total functions by the Buchholz operator method"*, Lecture
  Notes in Logic — operator-controlled derivations as a simplification of Pohlers' local predicativity,
  PA provably-recursive = ε₀-recursive. https://projecteuclid.org/ebooks/lecture-notes-in-logic/G%C3%B6del-96/chapter/How-to-characterize-provably-total-functions-by-the-Buchholz-operator/lnl/1235417024.pdf
- Schwichtenberg & Wainer, *Proofs and Computations* (Perspectives in Logic, CUP) — Ch. 4 bounding;
  cut-free→slow-growing, +Cut→fast-growing. https://www.cambridge.org/core/books/proofs-and-computations/0C1BA20F6462D1E273E45B8A266987FF
- *Slow versus Fast Growing*, Synthese — the cut-free/with-cut ⇄ slow/fast-growing dichotomy.
  https://link.springer.com/article/10.1023/A:1020899506400

---

### Net
The §19.6 commuting bound cannot be closed in a single-numeric-`k` system (§1 inequality is false, §2
Towsner skips it). The principled resolutions are operator/pure-ordinal control of cut-elimination,
*separated* from Hardy witness-bounding (§3–§4). Your `e`-control `Zekd` is the right minimal numeric
form; finish `cutReduceAllAux` with `e` inert in commuting cases (only `d` bumps), and if a case forces
`e` to depend on `n`, fall back to the two-phase split. Leaf-NF (option b) is faithful — ship it. No host
git run during the live lap; this file is left untracked for the box's next-lap `git add` to self-close.
