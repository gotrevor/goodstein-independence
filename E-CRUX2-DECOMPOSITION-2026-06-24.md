# E — Crux-2 decomposition: turning eq-(5) into a punch-list (judge, 2026-06-24)

> **VALIDATE, don't trust.** Source-grounded (Buchholz [6] §§3–5 read in full from the PDF). Goal per the
> operator: break the one genuinely-hard remaining piece (crux-2, the Gentzen reduction descent) into
> ordered, citation-backed, Lean-shaped sub-lemmas — most of them low-hanging — so the forward-grinder can
> plow. **The single most useful thing in this doc:** the difficulty is NOT spread across "step 2 (iR) +
> step 4 (C3)". It is concentrated in **ONE reduction case (5.1, the critical/cut-elimination case)**, and
> that case is **gated behind two prerequisites (Lemma 3.1 + Theorem 3.4) the current plan omits.**
> Everything else is õ-bookkeeping the box already has the algebra for.

Maps onto the box's own objects (`idg`/`iõ`/`iord` = Buchholz `dg`/`õ`/`o`; `ZDerivation`/`z*` codes;
`iR` = `d↦d[0]`) and its extraction `CRUX2-ORD-ASSIGNMENT-2026-06-24.md`. Citations are to
`papers/buchholz-on-gentzens-first-consistency-proof.pdf` unless noted.

## 0. The one insight that reorders the whole attack
Buchholz `o(d) = ω_{dg(d)}(õ(d))`, a tower of height `dg(d)` over pre-ordinal `õ(d)`. The descent
`o(d[n]) < o(d)` (Thm 4.2) splits, via Lemma 4.1, into two regimes:
- **Non-critical / structural cases** (atomic, I∀, I¬, Ind, chain-non-critical): `dg` does **not rise** and
  `õ` **strictly drops** — pure natural-sum (`#`) order bookkeeping. The box's F1–F4 + tower lemmas already
  discharge these. **LOW-HANGING.**
- **The ONE critical case (5.1)** — a `R_A`/`L^k_A` redex is eliminated: here `õ` may *jump up* to `< ω^{õ(d)}`,
  and the descent survives **only because `dg` strictly drops by 1**. This degree-drop IS cut-elimination,
  and it is the only place the tower height falls. **THE NUT.** It needs `rk(A(d)) < dg(d)` — which is *not*
  free; it comes from Theorem 3.4, which needs Lemma 3.1.

⟹ **Reordered plan:** build objects → plow the LOW-HANGING descent cases first (they validate the engine and
are cheap) → then the two prerequisites → then the nut → then Thm 4.2 (a 3-line tower combine) → bridge.

## 1. Dependency tree (hardest isolated)
```
C0   ZDerivation : V→Prop            (Fixpoint over z* codes)         ← box step 1, START
C0'  iR : V→V  (= d↦d[0]) SKELETON   (Def 3.2 dispatch on zTag)       ← box step 2, but see §3
 ├─ L3.1  critical-pair existence    (Lemma 3.1)            ◄ PREREQ, currently UNLISTED
 ├─ T3.4  rk(A(d)) < r + d{0}/d{1}   (Theorem 3.4)          ◄ PREREQ, currently UNLISTED
C3a  Lemma 4.1 — LOW-HANGING cases   (atomic,I∀,I¬,Ind,5.2) ← do FIRST, cheap, validates engine
C3b  Lemma 4.1(b)(ii) — case 5.1     (the cut-elim nut)     ← THE NUT, needs L3.1+T3.4
C3c  Theorem 4.2                     (tower combine)         ← ~3 lines given C3a+C3b + tower mono
C0.5 Foundation→Z bridge             (PA-⊥-proof → Z-⊥-deriv)← parallel; Bryce–Goré Peano.v blueprint
C4   isNF/≠0 of iord on ⊥-derivs     (feeds gentzenDescentφ_realized)
C5   assembly: gentzenDescentφ, d₀    (least ⊥-proof via C0.5)
```

## 2. The LOW-HANGING punch-list (plow these right after objects exist)
Each is a one-case fragment of Lemma 4.1; state it as `idg (iR d) ≤ idg d ∧ icmp (iõ (iR d)) (iõ d) = 0`
for the relevant `zTag d`, then `iord`-combine via the tower. Order of increasing effort:

| # | Buchholz case | `d[n]` is | Descent obligation | Discharged by | Effort |
|---|---|---|---|---|---|
| LH1 | **case 3 (I¬)** `d=I_{¬A}d₀` | `d[0]=d₀` | `õ(d₀) < õ(d₀)+1`, `dg` eq | `self_lt_iadd_one` | trivial |
| LH2 | **case 2 (I∀)** `d=I^a_{∀xF}d₀` | `d[n]=d₀(a/n)` | same; uses `õ(d(a/t))=õ(d)` (Remark p.10) | + the substitution-invariance remark | trivial |
| LH3 | **case 5.2.2** (chain, `dᵢ` non-crit) | `d[n]=K^r(i/dᵢ[n])` | one summand `ω^{õ(dᵢ)}↦ω^{õ(dᵢ[n])}` drops, `#` rest fixed | **F1** (left-cancel/mono) + IH(a) | low |
| LH4 | **case 4 (Ind)** `d=Ind^{a,k}_F d₀d₁` | `d[0]=K^r d₀ d₁(0)…d₁(k−1)` | `õ(d[0]) = ω^{õ(d₀)} # (k copies of ω^{õ(d₁)}) < ω^{õ(d₀)} # ω^{õ(d₁)+1} = õ(d)` | **F3** (`ω^β·k ≺ ω^{β+1}`) | low-med |
| LH5 | **case 5.2.1** (chain, `dᵢ` crit) | `d[0]=K^{r'}(i/dᵢ{0},dᵢ{1})` | descent by IH(b)(i) on `dᵢ{0}`,`dᵢ{1}`; `#` two summands below one | **F1+F2** + IH(b)(i) | med |

LH1–LH3 should each be ~one lap. **Doing these first is high-value:** they exercise `ZDerivation`/`iR` end-to-end
on the easy rules, so when you hit the nut the machinery is already debugged. (This is the box's own
"objects-first" instinct, pushed one level further: *easy-descent-cases* before the hard one.)

## 3. PREREQUISITES the current plan omits (build before the nut)
The plan jumps `iR` → "per-rule C3". But the critical case's descent (`rk(A(d)) < dg(d)`) is **not provable
from the assignment alone** — it is a theorem about the reduction:

- **L3.1 — Lemma 3.1 (critical-pair existence), p.8.** In a chain inference whose succedent is false-minimal,
  among the premises' inference symbols there exist `i<j` with `Iᵢ = R_{Aᵢ}`, `I_j = L^k_{Aᵢ}`, `0 < rk(Aᵢ)`.
  This is what makes `tp(d)` well-defined in the critical branch and identifies the redex `iR` eliminates.
  *Lean shape:* a `Σ₁` search over the (coded) premise list returning the least such `(i,j,k)`; pure
  combinatorics on `zTag`/inference-symbol codes, **no ordinals**. Order-induction on the premise index.
  *Effort:* medium, self-contained. **This is genuinely low-hanging and unblocks the nut — do it early.**
- **T3.4 — Theorem 3.4(a), p.9.** For critical `d = K^r…`: the auxiliary derivations satisfy
  `d{0} ⊢ Π·A(d)`, `d{1} ⊢ A(d),Π`, **and `rk(A(d)) < r`.** The rank bound is the linchpin of the degree-drop.
  *Lean shape:* `ZDerivation d → critical d → ... ∧ rk (zCutFormula d) < zRank d`. Proof is structural
  (the redex formula's rank is bounded by the chain-rule rank). *Effort:* medium; depends on L3.1.

**Add L3.1 and T3.4 as explicit milestones between `iR` and the critical-case C3.** Without them, C3b cannot
even be *stated* truthfully (it would have to assume `rk(A(d)) < dg(d)` as a hypothesis — a hidden gap).

## 4. THE NUT — Lemma 4.1(b)(ii), case 5.1 (cut-elimination), p.11
`d = K^r_Π d₀…d_l` critical, redex `(i,j,k)` from L3.1; `d[0] = K^{r−1}_Π d{0} d{1}` where `d{0}`,`d{1}` are
the auxiliary derivations from T3.4. Three obligations:
1. **`dg(d[0]) < dg(d)`** — the degree strictly drops. Buchholz: `dg(d[0]) = max{dg(d{0})−1, dg(d{1})−1, r−1}`,
   and by IH(b)(i) `dg(d{ν}) ≤ dg(d)`, plus `rk(A(d)) < r ≤ dg(d)` (T3.4) ⟹ each component `< dg(d)`.
   **This is the cut-elimination heart — the only degree-drop in the whole proof.**
2. **`õ(d[0]) < ω^{õ(d)}`** — pre-ordinal stays below one ω-power of `õ(d)`. From IH(b)(i)
   `õ(d{ν}) < õ(d)` and `õ(d[0]) = ω^{õ(d{0})} # ω^{õ(d{1})} < ω^{õ(d)}` via **F2** (two powers below one).
3. **`rk(A(d)) < dg(d)`** — directly T3.4 + `r ≤ dg(d)`.
Then Thm 4.2: `o(d[0]) = ω_{dg(d[0])}(õ(d[0])) < ω_{dg(d[0])}(ω^{õ(d)}) ≤ ω_{dg(d)}(õ(d)) = o(d)` — the
*degree-drop* (1) absorbs the *pre-ordinal jump* (2) through the tower (`ω_{m}(ω^α) = ω_{m+1}(α) ≤ ω_{m+1+…}`).
**The order-fact `ω_m(ω^α) ≤ ω_{m+1}(α)` is the one tower lemma to confirm exists** (`icmp_iotower_lt_succ_of_le`
looks like it — VALIDATE it gives exactly this).

The genuine work in the nut is **constructing `d{0}`/`d{1}` as `ZDerivation`s** (nested chain rules, Buchholz
14.253 / 3.2(5.1)) and the IH plumbing — *not* the ordinal inequality, which is two F-lemmas + a tower step.
So even the nut is mostly the **object construction** `iR`-critical-branch, which is C0'/T3.4 work, with a
short ordinal tail.

## 5. C0.5 bridge — sub-decomposition (Foundation-PA-⊥ → Z-⊥), parallelizable
`Z ⊇ PA` on closed sequents. Three sub-obligations (Bryce–Goré `Peano.v`, ~1215 lines, is the worked template
— skeleton being extracted; will append):
- **B1** each PA logical+equality+arithmetic axiom is a Z-axiom/short Z-derivation (Buchholz §5 `Ax(Z)`).
- **B2** each Foundation inference rule (`axL`/`andIntro`/…/`cutRule`/`axm`) is Z-derivable from premises. The
  **induction `axm` schema** is the only subtle one — Z's `Ind` rule absorbs it (this is why Buchholz-Z, not
  finite cut-elim on Tait+cut: lap-58 finding, correct).
- **B3** compose B1+B2: `𝗣𝗔.DerivationOf d ⊥ → ∃ z, ZDerivesEmpty z`, **M-internally** (Σ₁ / per-model).
Independent of §§3–4 — run it in a worktree when the descent stalls.

## 6. Literature map (which paper in `papers/` decomposes each piece further)
The box is offline but `papers/` is in-repo — point each hard node at its richest secondary source:
- **The nut (5.1) / cut-elim:** `buchholz-beweistheorie-lecture-notes.pdf` (Buchholz's own longer course
  treatment of the same Z system — more steps shown than [6]); `buss-handbook-ch2-first-order-proof-theory-arithmetic.pdf`
  (standard cut-elimination, the canonical reference); `arai-lectures-on-ordinal-analysis.pdf` (alternative
  ordinal-assignment exposition — cross-check the degree-drop).
- **L3.1 / T3.4:** `buchholz-on-gentzens-first-consistency-proof.pdf` pp.8–9 (primary, complete proofs);
  `siders-gentzen-consistency-proofs-arithmetic.pdf` (the cited eq-5 companion).
- **Bridge (C0.5):** Bryce–Goré `Peano.v` (Coq, the direct analogue); `buchholz-beweistheorie` (PA→PA_ω
  embedding, § embedding); Rathjen `rathjen-2006-art-of-ordinal-analysis.pdf` for context.
- **Tower / `o(d)` reindex:** [6] §4 + `arai-lectures` (the `ω_n` hierarchy conventions).

## 7. How this could be wrong / validation checklist
- I read [6]'s §§3–5 but mapped cases to the box's `zTag`/`iR` from the handoffs, not from `InternalZ.lean`
  source — **confirm `iR`'s critical branch actually constructs `d{0}`/`d{1}` per 3.2(5.1)**, not a
  shortcut that silently changes the ordinal bound.
- **Confirm `icmp_iotower_lt_succ_of_le` proves `ω_m(ω^α) ≤ ω_{m+1}(α)`** (the exact step the nut's Thm-4.2
  combine needs). If it proves something weaker, that's a missing tower lemma — flag it.
- The "LOW-HANGING first" ordering assumes `ZDerivation` + a minimal `iR` exist for the easy rules before the
  hard one — true if `iR` is built rule-by-rule (it should be).
- If `iR`'s degree drop in case 5.1 turns out NOT to need T3.4 (e.g. the box encodes ranks so `rk<r` is
  definitional), then T3.4 collapses to a definitional unfolding — *check before building it as a theorem*.
- Credit: the box's F1–F4 isolation and the `icmp_insTerm_congr` nut-identification (lap 59) are exactly
  right and feed LH3/LH5 + nut-step 2. This doc reorders and gates; it does not relitigate the algebra.
```
```
