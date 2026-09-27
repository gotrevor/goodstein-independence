# Stage 3 plan: PA ⊬ Paris–Harrington

**Statement RATIFIED 2026-09-26 by Astra** (in Trevor's place, per his standing instruction):
`src/GoodsteinPA/PH/Statement.lean` (`RelLarge`, `Homog`, `PH`, `PHx`), headline + existence as in
`drafts/PHDraft.lean`, and `ph_true`.  Degenerate parameters: `PH e 0 k N ↔ e ≤ N` (no colours:
true iff the domain is nonempty; `PH 1 0 0 0` is false — anchor it).

## Done
- **2026-09-26: stage 3 COMPLETE.**  `PH/Main.lean`: `pa_not_proves_ph` (= `pa_not_proves_ph_of_escape LB.escapes`)
  and `exists_sigma1_ph_def` (`PH/Computable.lean`), both pinned in `scripts/AxiomCheck.lean`.  Lower bound in
  `PH/LB/{Cnf,Colour,Descent,Bad,Escape}.lean` per `PH-BUCHHOLZ-SPEC.md`: statements designed in the attended
  session, proved by five parallel subagents; Part A by one treadmill lap.
- `infinite_ramsey` (all exponents), `ph_true` (Rado selection + Ramsey) — axiom-clean.
- `pa_not_proves_ph_of_escape` — headline from stage 1 + `Escapes`.

## Lower bound: Buchholz, *Beweistheorie* notes (1998), pp. 46–49 (after Loebl–Nešetřil 1992)
`papers/ph-buchholz-bewth98.pdf` (Astra retrieved it; gitignored).  Thm 7.5:
`H_{ω_m(k)}(k+1) < R_m(k)`, `R_m(k)` = least `N` with `N →* (2m+k+4)^{m+1}_{k+Σ_{i<m}3^i}`.

Formalisation steps (on `ONote`, Mathlib's fundamental sequences):
1. CNF term data `S_i, E_i, K_i`; `d(α,β)` (first differing term), `K(α,β)`, `E(α,β)`; norm `r(α)`.
2. L7.7 (E strictly drops under d/K monotonicity), the 3-colouring `χ` of triples, L7.8 (a: a chain
   homogeneous in 0̂/1̂ has length ≤ r(β₀); b: in 2̂ the `E`'s descend).
3. `χ_m^k` on `(m+1)`-chains below `ω_m(k+1)` (recursive via the `δ_i = E(β_i, β_{i+1})`), colour set
   `C_m^k` of size `k + Σ_{i<m} 3^i`; L7.9 (homogeneous chain of length ℓ ⇒ ℓ < r(β₀) + m).
4. Norm lemma L7.6 for Mathlib's `fundamentalSequence`.
5. Descent `α₀ = ω_m(k) + n`, `α_{i+1} = α_i[i ∸ (m+1)]`, `n = m+k+2`; HS1 norm bounds; length
   `N ≥ hardy-style bound` via our P2 argument (not Buchholz's `H` convention — transfer).
6. Colouring `f(i₀<…<i_m) := χ_m^k(α_{i₀},…,α_{i_m})`; shift `[0,N)` → `[1,N]` for our `PH`.
7. `Escapes`: for `o < ε₀` pick `m` with `ω^P + ω^2 < ω_m(k)`, compare as in hydra P3
   (`fastGrowing_le_hardy_omega_pow`, `hardy_add_comp`, `hardy_le_of_lt`), the input code
   `x = ⟪m+1, ⟪r, κ⟫⟫` polynomial in `k`.

## Existence
`PHx` primitive recursive via bitmask / base-`r` digit encoding (`PH/Computable.lean`, in progress),
then `codeOfPartrec'` as for the hydra.
