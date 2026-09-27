# Paris-Harrington lower bound: transcription of Buchholz, *Beweistheorie* (1997/98), §7

Source: `papers/ph-buchholz-bewth98.pdf`.  **Page numbers below are the PRINTED page numbers**
(the PDF page index is printed + 1: printed p. 46 = PDF p. 47).

Read from page images: printed pp. 15, 36, 38, 39, 40, 45, 46, 47, 48, 49 (PDF 16, 37, 39-41, 46-50).
The PH section is printed pp. 46-49.  German is translated; the source's own mixture of German
and English is flattened to English.

Marking conventions in this file:
- **[added]** = a step or justification not written by Buchholz, supplied by the transcriber.
- **[reconstructed, uncertain]** = content not on the page at all (e.g. a proof Buchholz omits).
- Everything else is what is on the page.

---

## 0. Background conventions (earlier sections)

### 0.1 Cantor normal form / additive principal numbers (printed p. 15)

- **Abbreviation (CNF).**  α =_CNF ω^{α_0}·k_0 + … + ω^{α_n}·k_n  :⟺  α = ω^{α_0}·k_0 + … + ω^{α_n}·k_n & α_0 > … > α_n.
  (On the page the last coefficient is typeset `k_n` and the last exponent `α_k`; it is a typo for `α_n`.)
- **Definition (additive principal number).**  γ ∈ On is an *additive Hauptzahl* iff γ > 0 ∧ ∀ξ,η < γ (ξ + η < γ).  H := class of all additive principal numbers.
- **Lemma 3.15.**  a) α ↦ ω^α is the enumerating function of H.  b) γ ∈ H ⟺ γ > 0 ∧ ∀ξ < γ (ξ + γ = γ).
- **Abbreviation (NF).**  α =_NF α_0 + … + α_n  :⟺  α = α_0 + … + α_n & α_0, …, α_n ∈ H & α_0 ≥ … ≥ α_n.
  (So NF is the CNF with each ω^β·k written as k copies of ω^β; indices start at 0.)
- **Lemma 3.16.**  a) Every α > 0 has exactly one tuple α_0,…,α_n ∈ H with α =_NF α_0 + … + α_n.
  b) If α = α_0 + … + α_n with additive principal α_0 ≥ … ≥ α_n, then for each k < n: α_0 + … + α_k < α and α_{k+1} + … + α_n < α.
- *Lim* = class of limit ordinals (λ ≠ 0 and not a successor); ω is the least one (printed p. ~10, only located via text dump).

### 0.2 ω-towers, first version (printed p. 36)

> β_0(α) := α,  β_{m+1}(α) := β^{β_m(α)}.   ω_m := ω_m(1), i.e. ω_0 = 1, ω_1 = ω, ω_2 = ω^ω, ω_3 = ω^{ω^ω} (= ω^{(ω^ω)}), ….

(Here β is a generic base; the notation ω_m(α) is the instance β = ω.  **Note ω_m (no argument) = ω_m(1).**)

Also p. 36: OT ⊆ ℕ, ≺ ⊆ ℕ×ℕ are the primitive-recursive notation system of §4, (OT, ≺) has order type ε_0, ⌜α⌝ is the code of α < ε_0.  Not needed for 7.5.

### 0.3 Fundamental sequences (printed p. 38, "DIE HARDY-HIERARCHIE")

**Definition (fundamental sequences for ordinals < ε_0).**  For n ∈ ℕ:
1. 0[n] := 1[n] := 0.
2. ω^{α+1}[n] := ω^α · (n+1).
3. ω^λ[n] := ω^{λ[n]}, for λ ∈ Lim.
4. α[n] := α_0 + … + α_{k−1} + α_k[n], if α =_NF α_0 + … + α_k.

**Proposition.**  (α+1)[n] = α.

**Definition (norm).**  Nα := Nα_1 + … + Nα_k + k  if α = ω^{α_1} + … + ω^{α_k} with k ≥ 0 and α_k ≤ … ≤ α_1 < ε_0.
(The page omits a "+" before the last summand: "ω^{α_1} + … ω^{α_k}".)  So N0 = 0, and N counts the total number of ω-symbols.  Used only in the Corollary to 7.5, not in 7.5 itself.

**Lemma 6.8** (p. 38)
- a) α ∈ Lim ⇒ ∀n(α[n] < α[n+1]) & α = sup{α[n] : n ∈ ℕ}
- b) α > 0 ⇒ Nα[0] < Nα
- c) α[n] < β < α ⇒ α[n] ≤ β[0]
- d) α[n] < β < α ⇒ Nα[n] < Nβ
- e) β < α ⇒ β ≤ α[Nβ]

Proof (p. 38): a), b) obvious.  c) Let β =_NF β_0 + … + β_k.  (1) If ω^α·(n+1) < β < ω^{α+1}: then k > n and β_0 = … = β_n = ω^α, hence ω^α·(n+1) ≤ β_0 + … + β_{k−1} + β_k[0] = β[0].  (2) If ω^{λ[n]} < β < ω^λ, λ ∈ Lim: then ω^{λ[n]} ≤ β_0 = ω^γ < ω^λ.  If k = 0 then λ[n] < γ < λ, so by IH λ[n] ≤ γ[0], hence ω^{λ[n]} ≤ ω^{γ[0]} = ω^γ[0] = β[0].  If k > 0 then ω^{λ[n]} ≤ β_0 + … + β_{k−1} + β_k[0] = β[0].  (3) If α =_NF α_0 + … + α_m, m > 0, and α[n] = α_0 + … + α_{m−1} + α_m[n] < β < α: then m ≤ k, α_m[n] < β_m < α_m and α_i = β_i for i < m.  By IH α_m[n] ≤ β_m[0], so α[n] ≤ β_0 + … + β_{m−1} + β_m[0] ≤ β_0 + … + β_{k−1} + β_k[0] = β[0].
d) By c), α[n] = β[0]…[0].  Hence Nα[n] ≤ Nβ[0] < Nβ.
e) Let α ∈ Lim.  By a), d): ∀n(Nα[n] < Nα[n+1]), therefore Nβ ≤ Nα[Nβ].  Together with d) this gives the claim.

### 0.4 Hardy hierarchy (printed p. 38)

**Definition of H_α : ℕ → ℕ for α < ε_0.**
1. H_0(n) := n,
2. H_α(n) := H_{α[n]}(n+1), for α > 0.

That is the whole definition: **one uniform clause for all α > 0** (successor and limit alike).  With (α+1)[n] = α this gives H_{α+1}(n) = H_α(n+1); for λ ∈ Lim, H_λ(n) = H_{λ[n]}(n+1).  **The limit clause does carry the +1 on the argument.**

**Lemma 6.9** (p. 38)
- a) H_α(n) < H_α(n+1),
- b) β[m] < α < β ⇒ H_{β[m]}(n+1) ≤ H_α(n),
- c) β < α & Nβ ≤ n ⇒ H_β(n) < H_α(n),
- d) α > 0 ⇒ H_α(n) = min{k ≥ n : α[n]…[k−1] = 0} = n + min{l : α[n][n+1]…[n+l−1] = 0}.

Proof (p. 39): a), b) simultaneous induction on α; let α > 0.
a) 1. α ∈ Lim: H_α(n) = H_{α[n]}(n+1) <^{IHa} H_{α[n]}(n+3) ≤^{IHb} H_{α[n+1]}(n+2) = H_α(n+1).  2. α = α_0+1: H_α(n) = H_{α_0}(n+1) <^{IHa} H_{α_0}(n+2) = H_α(n+1).
b) From β[m] < α < β, Lemma 6.8 gives β[m] ≤ α[n] < β.  Hence H_{β[m]}(n) ≤^{IHb} H_{α[n]}(n) <^{IHa} H_{α[n]}(n+1) = H_α(n).  (Note: the page proves H_{β[m]}(n) ≤ … while the statement says H_{β[m]}(n+1); see Uncertain.)
c) Induction on α: β < α ⇒^{L.6.8e} β ≤ α[Nβ] ≤ α[n] ⇒^{a)+IH} H_β(n) < H_β(n+1) ≤ H_{α[n]}(n+1) = H_α(n).
d) Let k ≥ n minimal with α[n]…[k−1] = 0.  Then H_α(n) = H_{α[n]}(n+1) = … = H_{α[n]…[k−1]}(k) = H_0(k) = k.

**Abbreviation** (p. 39): NF(α,β) :⟺ α = 0 or β = 0 or [α = ω^{α_0} + … + ω^{α_n} & β = ω^{β_0} + … + ω^{β_m} with α_0 ≥ … ≥ α_n ≥ β_0 ≥ … ≥ β_m].
**Proposition**: NF(α,β) & β > 0 ⇒ (α+β)[n] = α + β[n] & NF(α, β[n]).
**Lemma 6.10** a) NF(α,β) ⇒ H_{α+β} = H_α ∘ H_β.  b) H_{ω^{α+1}}(n) = H_{ω^α}^{(n+1)}(n+1), H_{ω^λ}(n) = H_{ω^{λ[n]}}(n+1).  (Not used by 7.5.)

**Theorem 6.12** (p. 40; used only in the Corollary to 7.5): If Z_m ⊢ ∀x∃yA(x,y) (A atomic, m ≥ 1) then there is an α < ω_{m+1} such that ∀n ∃l < H_α(n) ℕ ⊨ A(n,l).
(Z_m is the fragment of arithmetic defined earlier in the notes; its definition was **not transcribed** - it only matters for the Corollary.)

---

## 1. Ramsey notation and PH (printed p. 46)

**Abbreviations.**  Let k, m, n, r ∈ ℕ (= ω), κ a cardinal, N a set.
- [N]^m := {X ⊆ N : card(X) = m}.
- Let f be a function with dom(f) = [N]^m:
  **X is f-homogeneous :⟺ ∅ ≠ X ⊆ N & f↾[X]^m is constant.**
- N ⟶ (κ)^m_r  :⟺  ∀f : [N]^m → r ∃X (X f-homogeneous & card(X) ≥ κ).
- **N ⟶\* (κ)^m_r  :⟺  ∀f : [N]^m → r ∃X (X f-homogeneous & card(X) ≥ max{κ, min(X)})**  (for N ⊆ ℕ).

Numbers are von Neumann ordinals: r = {0,…,r−1}, and for N ∈ ℕ, [N]^m = m-subsets of {0,…,N−1}.

- **Ramsey Theorem** ∀m,r ∈ ω (ω ⟶ (ω)^m_r).
- **Finite Ramsey Theorem** ∀m,r,κ ∈ ω ∃N ∈ ω (N ⟶ (κ)^m_r).
- **PH** ∀m,r,κ ∈ ω ∃N ∈ ω (N ⟶\* (κ)^m_r).
- (Proof of the Finite Ramsey Theorem in PA: cf. Hájek-Pudlák Ch. 2, Sec. 1.)

**Proof of PH** (p. 46).  Fix m, r, κ ∈ ω.  To prove: ∃n ∈ ω ∀f ¬Φ(f,n), where
Φ(f,n) :⟺ f : [n]^m → r & ∀X (X f-hom ⇒ card(X) < max{κ, min(X)}).
Assume ∀n ∃f Φ(f,n).  By König's Lemma there is f\* : [ω]^m → r such that (+) ∀n Φ(f\*↾[n]^m, n).  By Ramsey's Theorem there is an infinite f\*-homogeneous X ⊆ ω.  Choose N < ω with card(X ∩ N) > max{κ, min(X)}.  For f := f\*↾[N]^m we have f↾[X∩N]^m = f\*↾[X∩N]^m = constant.  Hence X ∩ N is f-homogeneous and card(X∩N) > max{κ, min(X)} = max{κ, min(X∩N)}, i.e. ¬Φ(f,N).  Contradiction to (+).
[[ Construction of f\*: Let Φ_n := {f : Φ(f,n)} and M(f) := {i : ∃g ∈ Φ_i (f ⊆ g)}.  Starting with f_0 := ∅ define (f_n)_{n∈ω} with f_n ∈ Φ_n & f_n ⊆ f_{n+1} & card(M(f_n)) ≥ ω, and set f\* := ⋃_{n∈ω} f_n.  Definition of f_{n+1}: let E := {f ∈ Φ_{n+1} : f_n ⊆ f}.  Then M(f_n) = {n} ∪ ⋃_{f∈E} M(f), and E is finite.  Together with ∀i > n ∀f ∈ Φ_i (f↾[n+1]^m ∈ Φ_{n+1}) this implies there is f_{n+1} ∈ E with card(M(f_{n+1})) ≥ ω. ]]
(Note: min(X) in "card(X∩N) > max{κ, min(X)}" is fine because X ∩ N contains min(X) once N > min X [added].)

**Theorem 7.5** (p. 46)
> ∀m ≥ 1 ∀k ( H_{ω_m(k)}(k+1) < R_m(k) )  with  R_m(k) := min{N : N ⟶\* (2m+k+4)^{m+1}_{k+Σ_{i<m}3^i}}.

So: Ramsey exponent **m+1**, size parameter κ = **2m+k+4**, number of colours **k + Σ_{i<m} 3^i**.
(R_m(k) exists by PH.)

**Corollary** (p. 46)
- a) Z_m ⊬ ∀κ,r ∃N (N ⟶\* (κ)^{m+1}_r)   (m ≥ 1)
- b) Z ⊬ ∀m,κ,r ∃N (N ⟶\* (κ)^{m+1}_r)

**Proof of the Corollary** (p. 47).
a) Assume Z_m ⊢ ∀κ,r ∃N (N ⟶\* (κ)^{m+1}_r).  Then Z_m ⊢ ∀k ∃N (N ⟶\* (2m+k+4)^{m+1}_{k+Σ_{i<m}3^i}).  [The page writes "∀κ,r" here and has a stray "}"; the quantified variable must be k - see Uncertain.]  By 6.12 there is α < ω_{m+1} with ∀k (R_m(k) < H_α(k)).  Let k ∈ ω with α < ω_m(k) and N(α) ≤ k.  Then H_{ω_m(k)}(k+1) <^{7.5} R_m(k) < H_α(k) < H_{ω_m(k)}(k).  Contradiction [with Lemma 6.9a: H_{ω_m(k)}(k) < H_{ω_m(k)}(k+1) - added].  (Last step uses 6.9c with β = α, N(α) ≤ k [added].)
b) Z ⊢ ∀n,κ,r ∃N (N ⟶\* (κ)^{n+1}_r) ⟹ Z_m ⊢ ∀n,κ,r ∃N(N ⟶\* (κ)^{n+1}_r) for suitable m ⟹ Z_m ⊢ ∀κ,r ∃N (N ⟶\* (κ)^{m+1}_r), contradicting a).

"The rest of this section is spent with the proof of 7.5."

---

## 2. Definitions for the proof of 7.5 (printed p. 47-48)

### 2.1 ω-towers and r(α) (p. 47)

**Definition.**
1. ω_0(α) := α,  ω_{m+1}(α) := ω^{ω_m(α)}.
2. Let α = ω^{α_1}n_1 + … + ω^{α_t}n_t with t ≥ 0 & n_1,…,n_t > 0 & α > α_1 > … > α_t:
   **r(α) := max{t, n_1, …, n_t, r(α_1), …, r(α_t)}.**

Remarks [added]: α > α_1 forces α < ε_0.  r(0) = max{0} = 0 (t = 0).  For finite k > 0, r(k) = max{1, k, r(0)} = k.  ω_1(k) = ω^k, ω_1(0) = ω^0 = 1.  Note ω_m(k) with argument k ∈ ℕ is NOT ω_m = ω_m(1) of §0.2 unless k = 1.  CNF indices here run **1..t** (contrast NF indices 0..k in §0.3).

### 2.2 Lemma 7.6 (p. 47)
- a) r(α[k]) ≤ max{r(α), k} + 1
- b) r(α) < n ⟹ r(α[n−1]) < n+1
- c) r(ω_m(k) + n) ≤ n + 1, if 1 ≤ m and k < n.

**Proof of c)** (only c) is proved on the page):
1. k = 0 and m = 1: ω_m(k) + n = ω^0(n+1).  [So r = max{1, n+1, r(0)} = n+1 - added.]
2. k ≠ 0 and m = 1: r(ω_m(k) + n) = max{2, 1, n, r(k)} ≤ n+1.  [ω^k·1 + ω^0·n, t = 2 since n > k ≥ 1; r(k) = k < n; r(0) = 0 - added.]
3. m > 1: r(ω_m(k) + n) = max{2, 1, n, r(ω_{m−1}(k))} = max{2, n, k} ≤ n+1.
   [added: ω_m(k) + n = ω^{ω_{m−1}(k)}·1 + ω^0·n with t = 2 (n > k ≥ 0 so n ≥ 1).  The equality with max{2,n,k} uses r(ω_j(k)) ≤ max{1,k} for all j ≥ 0 (induction: r(ω_0(k)) = r(k) ≤ k; r(ω_{j+1}(k)) = r(ω^{ω_j(k)}) = max{1, 1, r(ω_j(k))}).  Then max{2,n,k} ≤ n+1 because n ≥ 1 and k < n.]

**Proof of a)** [reconstructed, uncertain - no proof on the page].  Let α = ω^{α_1}n_1 + … + ω^{α_t}n_t (CNF, t ≥ 1; α = 0 is trivial since 0[k] = 0).  By the NF clause 4, α[k] = ω^{α_1}n_1 + … + ω^{α_t}(n_t − 1) + ω^{α_t}[k].
- α_t = 0: α[k] = α − 1; the CNF of α[k] has the same or fewer terms and coefficients ≤ those of α, so r(α[k]) ≤ r(α).
- α_t = γ+1: ω^{γ+1}[k] = ω^γ(k+1); α[k] = … + ω^{α_t}(n_t−1) + ω^γ(k+1) is in CNF (γ < α_t) with ≤ t+1 terms, coefficients from α or k+1, and exponents from α plus γ where r(γ) ≤ r(γ+1) = r(α_t).  So r(α[k]) ≤ max{r(α)+1, k+1}.
- α_t = λ ∈ Lim: ω^λ[k] = ω^{λ[k]}; ≤ t+1 terms, new exponent λ[k] with r(λ[k]) ≤ max{r(λ),k}+1 by IH.  Same bound.
**Proof of b)** [added]: from a) with k := n−1 (n ≥ 1 since r(α) < n): r(α[n−1]) ≤ max{r(α), n−1} + 1 ≤ n < n+1.

### 2.3 S_i, E_i, K_i, d, K, E (p. 47)

**Definition.**  Let α = ω^{α_1}n_1 + … + ω^{α_t}n_t with t ≥ 0 & n_1,…,n_t > 0 & α > α_1 > … > α_t:
- S_i(α) := ω^{α_i} n_i,  E_i(α) := α_i,  K_i(α) := n_i  for i ∈ {1,…,t};
- S_i(α) := E_i(α) := K_i(α) := 0  for i ∉ {1,…,t}.

**Definition.**  For α > β:
d(α,β) := min{i : S_i(α) > S_i(β)},  K(α,β) := K_{d(α,β)}(α),  E(α,β) := E_{d(α,β)}(α).

[added] Since S_0 = 0 for every ordinal, d(α,β) ≥ 1; since α > β, at the first index where S_i(α) ≠ S_i(β) one has S_i(α) > S_i(β), so d(α,β) is the first index where the CNF terms differ, and 1 ≤ d(α,β) ≤ t(α).  Hence K(α,β) ≥ 1 and K(α,β), d(α,β) ≤ r(α).

### 2.4 Lemma 7.7 (p. 47)

> α > β > γ & d(α,β) ≤ d(β,γ) & K(α,β) ≤ K(β,γ) ⟹ E(α,β) > E(β,γ).

Proof.
Case 1: d(α,β) = d(β,γ) = i.  Then E(α,β) = E_i(α), E(β,γ) = E_i(β) and K_i(α) ≤ K_i(β).  Because α > β [page says "α < β", a typo] and K_i(α) ≤ K_i(β), E_i(α) > E_i(β) must hold.
[added: S_i(α) = ω^{E_i(α)}K_i(α) > S_i(β) = ω^{E_i(β)}K_i(β) (definition of d) and i ≤ t(β) (as S_i(β) > S_i(γ) ≥ 0); if E_i(α) ≤ E_i(β) then with K_i(α) ≤ K_i(β) we'd get S_i(α) ≤ S_i(β).]
Case 2: i = d(α,β) < d(β,γ) = j.  Then E(α,β) = E_i(α) ≥ E_i(β) > E_j(β) = E(β,γ).
[added: E_i(α) ≥ E_i(β) because S_i(α) > S_i(β); E_i(β) > E_j(β) because i < j ≤ t(β) and CNF exponents strictly decrease.]
(The case d(α,β) > d(β,γ) is excluded by hypothesis.)

### 2.5 The 3-colouring χ (p. 47)

**Definition** (χ : [ε_0]^3 → {0̂, 1̂, 2̂}).  For β_0 > β_1 > β_2:
```
                      ⎧ 0̂   if d(β_1,β_2) < d(β_0,β_1)
χ(β_0,β_1,β_2) :=     ⎨ 1̂   if d(β_0,β_1) ≤ d(β_1,β_2) & K(β_1,β_2) < K(β_0,β_1)
                      ⎩ 2̂   otherwise
```
So χ = 2̂ ⟺ d(β_0,β_1) ≤ d(β_1,β_2) & K(β_0,β_1) ≤ K(β_1,β_2) [added] - exactly the hypothesis of 7.7.

### 2.6 Lemma 7.8 (p. 48)

> Let β_0 > … > β_ℓ with ℓ ≥ 2, and let c ∈ {0̂,1̂,2̂} with {χ(β_i,β_{i+1},β_{i+2}) : i ≤ ℓ−2} = {c}.
> a) c ∈ {0̂,1̂} ⟹ ℓ ≤ r(β_0)
> b) c = 2̂ ⟹ E(β_0,β_1) > … > E(β_{ℓ−1},β_ℓ)

Proof.  a) Let d_i := d(β_i,β_{i+1}) and k_i := K(β_i,β_{i+1}) (i < ℓ).
Clearly d_0, k_0 ≤ r(β_0).  [added: d_0 ≤ t(β_0) and k_0 is a CNF coefficient of β_0, see §2.3.]
If c = 0̂, then d_0 > d_1 > … > d_{ℓ−1} ≥ 1, whence ℓ ≤ d_0.
If c = 1̂, then k_0 > k_1 > … > k_{ℓ−1} ≥ 1, whence ℓ ≤ k_0.
[added: c = 0̂ at triple i means d_{i+1} < d_i; c = 1̂ means k_{i+1} < k_i; each d_i, k_i ≥ 1 by §2.3; ℓ strictly decreasing values in {1,…,d_0} force ℓ ≤ d_0.]
b) follows from Lemma 7.7.  [added: c = 2̂ at triple i gives d_i ≤ d_{i+1} & k_i ≤ k_{i+1}; apply 7.7 to β_i > β_{i+1} > β_{i+2} for each i ≤ ℓ−2.]

### 2.7 The colourings χ^k_m and colour sets C^k_m (p. 48)

**Definition** (χ^k_m : [ω_m(k+1)]^{m+1} → C^k_m, for m ≥ 1, k ≥ 0).  Tuples are listed in **decreasing** order.
1. For α = ω^k n_0 + … + ω^0 n_k > ω^k n'_0 + … + ω^0 n'_k = β we set **χ^k_1(α,β) := min{i : n'_i < n_i}.**
   [Here α, β < ω_1(k+1) = ω^{k+1} are written with **all** k+1 base-ω digits, zeros allowed, and n_i is the coefficient of ω^{k−i}.  The value lies in {0,…,k} = C^k_1 and is the first digit position (from the top) where α, β differ - added.]
2. Let m ≥ 1, ω_{m+1}(k+1) > β_0 > … > β_{m+1}, δ_i := E(β_i, β_{i+1}), and c_i := χ(β_i, β_{i+1}, β_{i+2}).
```
                                  ⎧ χ^k_m(δ_0,…,δ_m)   if c_0 = … = c_{m−1} = 2̂
χ^k_{m+1}(β_0,…,β_{m+1}) :=       ⎨
                                  ⎩ (c_0,…,c_{m−1})    otherwise
```
   (Note that by L.7.8, ω_m(k+1) > δ_0 > … > δ_m if c_0 = … = c_{m−1} = 2̂.)
   [added: 7.8b with ℓ = m+1 ≥ 2 gives δ_0 > … > δ_m; δ_0 is a CNF exponent of β_0 < ω^{ω_m(k+1)}, so δ_0 < ω_m(k+1).]
3. **C^k_1 := {0,…,k},  C^k_{m+1} := C^k_m ∪ {0̂,1̂,2̂}^m.**

[added] Colour count: the union is meant disjoint (numbers vs. m-tuples of hatted symbols, tuples of different lengths distinct).  |C^k_1| = k+1, |C^k_{m+1}| = |C^k_m| + 3^m, so |C^k_m| = k + 1 + Σ_{1≤i<m} 3^i = **k + Σ_{i<m} 3^i**, the r of Theorem 7.5.  In the proof of 7.5 C^k_m is tacitly identified with r = {0,…,r−1} by a bijection.

### 2.8 Lemma 7.9 (p. 48)

> From 1 ≤ m < ℓ & ω_m(k+1) > β_0 > … > β_ℓ & c ∈ C^k_m it follows:
> ∀i ≤ ℓ−m ( χ^k_m(β_i,…,β_{i+m}) = c ) ⟹ ℓ < r(β_0) + m.

(Only **consecutive windows** of length m+1 are assumed to have colour c.)

Proof by induction on m.

**I. m = 1.**  Let β_i = ω^k n_{i,0} + … + ω^0 n_{i,k}.  Then n_{0,c} > … > n_{ℓ,c}, and hence ℓ ≤ n_{0,c} ≤ r(β_0) < r(β_0) + m.
[added: χ^k_1(β_i,β_{i+1}) = c means digit c is the first differing digit, so n_{i+1,c} < n_{i,c}; ℓ+1 strictly decreasing naturals give ℓ ≤ n_{0,c}; n_{0,c} is 0 or a CNF coefficient of β_0, so ≤ r(β_0).]

**II. m → m+1.**  Let 1 ≤ m & m+1 < ℓ & c ∈ C^k_{m+1} & ω_{m+1}(k+1) > β_0 > … > β_ℓ and χ^k_{m+1}(β_i,…,β_{i+m+1}) = c for all i ≤ ℓ−m−1.  (Goal: ℓ < r(β_0) + m + 1.)

CASE 1: c ∈ {0̂,1̂,2̂}^m.
Let c_i := χ(β_i,β_{i+1},β_{i+2}) (i ≤ ℓ−2).  For all i ≤ ℓ−m−2 we then have
(c_i,…,c_{i+m−1}) = χ^k_{m+1}(β_i,…,β_{i+m+1}) = χ^k_{m+1}(β_{i+1},…,β_{i+m+2}) = (c_{i+1},…,c_{i+m}).
This implies ∀i ≤ ℓ−m−2 (c_i = c_{i+1} = … = c_{i+m}) and hence c_0 = … = c_{ℓ−2}.
[added detail: since c is a tuple, every window i ≤ ℓ−m−1 is in the "otherwise" clause, so (c_i,…,c_{i+m−1}) = c.  Because m+1 < ℓ, window i = 1 exists, giving c_0 = c_1 = … = c_m.  Any p ≤ ℓ−2 can be written p = i + j with i ≤ ℓ−m−1, j ≤ m−1, so c_p = c_j = c_0.]
Together with χ^k_{m+1}(β_0,…,β_{m+1}) ∈ {0̂,1̂,2̂}^m it follows that c_0 ∈ {0̂,1̂} [added: window 0 is in the "otherwise" clause, so not all of c_0..c_{m−1} are 2̂, and they are all equal to c_0], and then ℓ < r(β_0) + m + 1 by Lemma 7.8a (which gives ℓ ≤ r(β_0); ℓ ≥ 2 holds).

CASE 2: c ∈ C^k_m.
Then c_0 = … = c_{ℓ−2} = 2̂.  [added: each window i ≤ ℓ−m−1 must be in the first clause (the second clause yields tuples ∉ C^k_m), so c_i = … = c_{i+m−1} = 2̂; these windows cover indices 0..ℓ−2.]
By L.7.8b, δ_0 > … > δ_{ℓ−1} (δ_i := E(β_i,β_{i+1})).  Further c = χ^k_{m+1}(β_i,…,β_{i+m+1}) = χ^k_m(δ_i,…,δ_{i+m}) for i ≤ ℓ−1−m.
By IH [applied to δ_0 > … > δ_{ℓ−1}, i.e. with ℓ−1 in place of ℓ] it follows that ℓ−1 < r(δ_0) + m.  So ℓ < r(δ_0) + m + 1 ≤ r(β_0) + m + 1.
[added: IH hypotheses: m < ℓ−1 since m+1 < ℓ; ω_m(k+1) > δ_0 as in §2.7; c ∈ C^k_m.  r(δ_0) ≤ r(β_0) because δ_0 = E_{d}(β_0) is one of the CNF exponents α_d of β_0 and r(β_0) takes the max over r(α_d).]

---

## 3. Proof of Theorem 7.5 (printed pp. 48-49)

Let m ≥ 1, k ≥ 0,
- n := m+k+2,
- κ := m+n+2 = 2m+k+4,
- r := k + Σ_{i<m} 3^i,
- H := H_{ω_m(k)}(k+1).

Then the following holds:
```
H < R_m(k)
⟺ ∀n ≤ H ¬(n ⟶* (κ)^{m+1}_r)
⟺ ∀n ≤ H ∃f (f : [n]^{m+1} → r & ∀X (X f-homogeneous ⇒ card(X) < max{κ, min(X)}))
⟺ ∃N ≥ H ∃f (f : [N]^{m+1} → r & ∀X (X f-homogeneous ⇒ card(X) < max{κ, min(X)}))   (*)
```
(The bound variable "n" in these lines shadows n := m+k+2; it is a fresh variable.)
[added: the first ⟺ uses that R_m(k) is a minimum and that N ⟶\* is upward-monotone in N (restrict a colouring of [N']^{m+1} to [N]^{m+1} for N ≤ N'; a homogeneous set for the restriction is homogeneous for the original).  The third ⟺: "⇒" take N := H; "⇐" by the same monotonicity, a bad colouring on [N] restricts to one on [n] for each n ≤ H ≤ N.  Only "(*) ⇒ H < R_m(k)" is needed.]

It remains to prove (*).

**Setup.**  Let α_0 := ω_m(k) + n,  α_{i+1} := α_i[i ∸ (m+1)],  N := min{i : α_i = 0}.  Then ∀i < N (α_i > α_{i+1}).
(∸ is truncated subtraction.)
[added: α_i > 0 ⇒ α_i[x] < α_i (fundamental sequences decrease; Lemma 6.8a / the definition); a strictly decreasing sequence of ordinals reaches 0, so N exists.  Once α_i = 0, all later α_j = 0.]
[added: For i ≤ n, α_i = ω_m(k) + (n − i), because each of the first n steps is a successor step and (α+1)[x] = α regardless of x.  In particular **α_n = ω_m(k)** > 0, hence N > n.]

**HS 1 (auxiliary claim 1):**  ∀i ≤ n (r(α_i) + m < κ)  and  ∀i ≥ n (r(α_i) + m < i).

Proof.  i ≤ n ⇒ r(α_i) + m ≤ r(α_0) + m ≤ n+1+m < κ.
[added: r(α_0) ≤ n+1 is Lemma 7.6c (1 ≤ m, k < n).  r(α_i) ≤ r(α_0) for i ≤ n since α_i = ω_m(k) + (n−i) has the same CNF as α_0 except a smaller (or dropped) last coefficient.  n+1+m < m+n+2 = κ.]
r(α_n) + m ≤ k+1+m < n;  and by L.7.6b:  r(α_i) + m < i ⇒ r(α_{i+1}) = r(α_i[i−m−1]) < i−m+1 ⇒ r(α_{i+1}) + m < i+1.
[added: r(α_n) = r(ω_m(k)) ≤ max{1,k} ≤ k+1 (see §2.2); k+1+m < m+k+2 = n.  For i ≥ n > m+1, i ∸ (m+1) = i−m−1; apply 7.6b with its n := i−m: r(α_i) < i−m ⇒ r(α_i[i−m−1]) < i−m+1.  Induction on i ≥ n.  For i ≥ N, α_i = 0, r = 0, still fine.]

**HS 2:**  H ≤ N.

Proof.  n ≤ i < N ⇒ H_{α_i}(i−m−1) = H_{α_{i+1}}(i+1−m−1).
[added: α_i > 0 and i−m−1 = i ∸ (m+1) ≥ 0, so by the Hardy clause H_{α_i}(x) = H_{α_i[x]}(x+1) with x = i−m−1.]
Hence H = H_{ω_m(k)}(k+1) = H_{α_n}(n−m−1) = H_{α_N}(N−m−1) = N−m−1 ≤ N.
[added: α_n = ω_m(k) and n−m−1 = k+1; iterate from i = n to N−1; α_N = 0 and H_0(x) = x.]

**Definition.**  f : [N]^{m+1} → r,  f({i_0,…,i_m}_<) := χ^k_m({α_{i_0},…,α_{i_m}}_>).
(Subscript < : the i's listed increasingly; subscript > : the α's listed decreasingly.  Since i_0 < … < i_m < N, α_{i_0} > … > α_{i_m}.  Values in C^k_m, identified with r.)
[added: well-defined because α_{i_0} ≤ α_0 = ω_m(k) + n < ω_m(k+1): ω_m(k+1) = ω^{ω_{m−1}(k+1)} is additive principal, ω_m(k) < ω_m(k+1), and n < ω ≤ ω_m(k+1) (for m = 1, k = 0: α_0 = n+1 < ω = ω_1(1)).]

**Conclusion.**  Let X = {i_0,…,i_ℓ}_< be f-homogeneous.  Then {α_{i_0},…,α_{i_ℓ}}_> is χ^k_m-homogeneous, and by Lemma 7.9
card(X) = ℓ + 1 ≤ r(α_{i_0}) + m <^{HS1} max{κ, i_0} = max{κ, min(X)}.
[added: Lemma 7.9 needs m < ℓ.  If ℓ ≤ m then card(X) = ℓ+1 ≤ m+1 < κ ≤ max{κ, min X} directly - Buchholz does not mention this case.  If ℓ > m: apply 7.9 to β_j := α_{i_j} (j ≤ ℓ), c := the constant colour; all windows (β_i,…,β_{i+m}) are (m+1)-subsets of X so have colour c; get ℓ < r(β_0) + m, i.e. ℓ+1 ≤ r(α_{i_0}) + m.  HS1 with i := i_0: if i_0 ≤ n it is < κ, if i_0 ≥ n it is < i_0; either way < max{κ, i_0}.]
So f witnesses (*) with N ≥ H (HS2).  ∎

---

## 4. Convention hazards

1. **ℕ starts at 0; numbers are sets.**  r = {0,…,r−1}; for N ∈ ℕ, [N]^{m+1} is (m+1)-subsets of {0,…,N−1}.  So "N ⟶\* …" is about colourings of subsets of {0,…,N−1}.  The index i in α_i and the elements of X are the same numbers; min(X) = i_0 can be 0.
2. **Relatively large:** X is good iff card(X) ≥ max{κ, min(X)}, i.e. **min(X) ≤ |X|** (non-strict) and κ ≤ |X|.  A "bad" colouring has every homogeneous X with |X| < max{κ, min X}.
3. **Homogeneous requires X ≠ ∅** (so min X exists).  Sets with |X| ≤ m (fewer than m+1 elements) are vacuously homogeneous; they are handled by |X| ≤ m+1 < κ [added case].
4. **Hardy hierarchy has a single clause** H_α(n) = H_{α[n]}(n+1) for all α > 0, H_0(n) = n; limits DO get the +1 on the argument; successors via (α+1)[n] = α.  Contrast the "h" hierarchy on p. 40/45: h_λ(n) = h_{λ[n]}(n), no +1 (not used here).
5. **Fundamental sequences:** ω^{α+1}[n] = ω^α·(n+1) (n+1 copies, not n); 0[n] = 1[n] = 0; (α+1)[n] = α.
6. **Theorem 7.5 argument is k+1:** H_{ω_m(k)}(k+1), with ω_m(k) := tower of m ω's topped by the natural number k (ω_1(k) = ω^k, ω_1(0) = 1).  Beware ω_m (no argument) = ω_m(1) from p. 36, used in 6.12 / Corollary (α < ω_{m+1}).
7. **Parameters in the proof:** n = m+k+2, κ = 2m+k+4, exponent m+1, colours r = k + Σ_{i<m}3^i = |C^k_m| (C^k_1 = {0..k} has k+1 = k + 3^0 elements).  In R_m(k) the exponent is m+1 while the colouring χ^k_m has subscript m.
8. **Descent step uses truncated subtraction:** α_{i+1} = α_i[i ∸ (m+1)]; for i ≤ m+1 the index is 0.  For i ≤ n the steps are successor steps regardless.
9. **HS2 offset:** H_{α_i}(i−m−1) invariant for n ≤ i < N; conclusion H = N−m−1.
10. **Three index conventions for ordinals:** r / S_i / E_i / K_i use CNF indices **1..t** (index 0 is a dummy with value 0, making d ≥ 1); fundamental sequences use NF indices **0..k**; χ^k_1 uses digit positions **0..k counted from the top** (n_i is the coefficient of ω^{k−i}, zeros allowed).
11. **d(α,β) uses "S_i(α) > S_i(β)"**, which coincides with "first index where the CNF terms differ" because α > β.
12. **χ outputs:** 0̂ when d strictly drops; 1̂ when d doesn't drop but K strictly drops; 2̂ otherwise.  Order of tests matters (0̂ first).
13. **χ^k_{m+1}'s tuple colour** has length m (c_0..c_{m−1}), built from the first m of the triples in an (m+2)-tuple; the recursive colour uses all m+1 δ's.  The union C^k_m ∪ {0̂,1̂,2̂}^m must be disjoint for the count.
14. **Lemma 7.9 only uses consecutive windows**, and its bound is strict: ℓ < r(β_0) + m, where ℓ+1 is the number of elements.

## 5. Unreadable / uncertain

Page images are clean (typeset LaTeX, read at 130-200 dpi); no glyph was illegible.  Items that are uncertain for other reasons:
1. **Lemma 7.6 a) and b) have no proof in the source**; the proofs in §2.2 are [reconstructed, uncertain].  In particular the r(γ) ≤ r(γ+1) and "≤ t+1 terms" steps for 7.6a should be checked when formalizing.
2. **Lemma 7.7 proof, Case 1 says "Wegen α < β"** - read as a typo for α > β.
3. **Lemma 6.9b**: statement has H_{β[m]}(n+1) ≤ H_α(n) but the proof line derives H_{β[m]}(n) ≤ … ; which is intended is unclear.  Not used by 7.5.
4. **Corollary proof, line 2** reads "Z_m ⊢ ∀κ,r∃N(N ⟶\* (2m+k+4)^{m+1}_{k+Σ_{i<m}3^i}})" with a stray "}" and quantifier ∀κ,r; presumably ∀k.  Not used by 7.5.
5. **Norm definition** omits a "+" (ω^{α_1} + … ω^{α_k}); meaning clear.
6. **"(Man beachte …" in the χ^k_{m+1} definition** has no closing parenthesis; content clear.
7. **Z_m and Theorem 6.7 / §4 notation system** were not transcribed; they matter only for the Corollary, not for Theorem 7.5.
8. **Definition of Lim** was located via the text dump only (printed p. ~10, "Limeszahl: ≠ 0 and not a successor") and not read from the page image.
9. HS1 step "i ≤ n ⇒ r(α_i) ≤ r(α_0)" is asserted without justification on the page; my justification [added] relies on α_i = ω_m(k) + (n−i).
