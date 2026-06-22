# Arithmetization Seam Advice — 2026-06-22

Context: critical path item **F**, the `ℒₒᵣ`-definable ε₀ order seam:

```text
arithmetization seam (‖≺‖=ε₀) │ not started — 2nd hard wall
```

This note is for workers coordinating on the seam. The main recommendation is to split the wall into small adapters. Do **not** attack `‖≺‖ = ε₀` as one monolithic theorem.

## Recommended Shape

Create a seam interface, likely in `src/GoodsteinPA/EpsilonOrder.lean`, that final assembly can consume:

```lean
structure EpsilonOrder where
  lt : ℕ → ℕ → Prop
  wf : IsWellFounded ℕ lt
  prec : Semiformula LX ℕ 2
  hprec : ∀ γ n,
    models lt γ ((Boundedness.hyp prec)/[nm n]) ↔
      ∀ m, lt m n → rk lt m < γ
  hprecXPos : XPos (∼ prec)
  orderType_eq : orderType lt = ε₀
```

Then wire Boundedness/final assembly against this structure. This isolates the seam from the rest of the proof and gives other workers a stable target.

## Work Order

1. **Generic formula adapter.**
   Prove that an X-free `ℒₒᵣ` binary formula defining `lt` supplies `hprec` and `hprecXPos`.

   Target shape:

   ```lean
   lemma hprec_of_lMap_defined
     (φ : Semisentence ℒₒᵣ 2)
     (hφ : ∀ m n, ℕ ⊧/![m,n] φ ↔ lt m n) :
     ...
   ```

   This likely requires generalizing `TruthSem.models_lMap` from closed formulas to arity-2 semisentences and then pushing it through `Boundedness.hyp`.

2. **Binary representability helper.**
   Foundation’s public `codeOfREPred` helper is unary, but `Representation.lean` exposes `codeOfPartrec'` for arbitrary arity. Build a binary helper instead of hand-writing the whole comparison formula first:

   ```lean
   noncomputable def codeOfREPred₂ (R : ℕ → ℕ → Prop) : Semisentence ℒₒᵣ 2 := ...

   lemma codeOfREPred₂_spec (hR : ...) :
     ℕ ⊧/![m,n] codeOfREPred₂ R ↔ R m n := ...
   ```

   Then lift it to `LX` by `Semiformula.lMap`. This should discharge `hprec/hprecXPos` once the chosen order relation is computable or r.e. in the right direction.

3. **Pure ordinal order-type theorem.**
   Use `ONote`/`NONote`, not Goodstein sequences. The repo already has useful material:

   - `ONote.NF`, `NONote`, `repr`, `repr_inj`, comparison, well-foundedness in mathlib.
   - `Domination.lean` has `towerO`, `towerO_NF`, `repr_towerO`, and `exists_repr_lt_omegaTower`.

   First target:

   ```lean
   theorem note_rank_eq_repr (o : NONote) :
     IsWellFounded.rank (· < ·) o = NONote.repr o
   ```

   Then show the order type of `NONote` under `<` is `ε₀`, using tower cofinality and mathlib’s `Ordinal.lt_epsilon_zero`.

4. **Nat coding transfer.**
   Transfer the `NONote` order to an `ℕ` relation. Keep invalid or noncanonical codes isolated so they do not inflate the supremum. A good pattern is:

   - decode `n : ℕ` to `Option NONote`;
   - define `ltCode m n` only when both decode to canonical notations;
   - put invalid codes below no valid code, or otherwise prove they contribute only a bounded/finite prefix;
   - prove `orderType ltCode = ε₀` by embedding/equivalence with `NONote`.

5. **Instantiate `EpsilonOrder`.**
   Combine:

   - syntactic definability of `ltCode` by `prec`;
   - `hprec` from the generic formula adapter;
   - `hprecXPos` from the `lMap`/X-free lemma;
   - `orderType_eq` from the Nat coding transfer.

## Pitfalls To Avoid

- Do not use only `toOrdinal 2 n` as the ε₀ order. It is cofinal below ε₀, but cofinality alone is not an order-isomorphism/order-type theorem. Use all normal ordinal notations.
- Do not couple `Boundedness` to a concrete ordinal coding. Keep `hprec`/`hprecXPos` as adapter lemmas.
- Do not introduce a theorem that simply assumes `orderType lt = ε₀` and call the seam done. If a temporary assumption is needed for parallel progress, expose it in the `EpsilonOrder` interface and keep it out of the headline axiom path.
- Do not push arithmetic coding details into the Boundedness proof. Boundedness should only see a binary formula and its semantic spec.

## Suggested Parallelization

- **Worker A:** `hprec_of_lMap_defined` and X-free/lMap adapter lemmas.
- **Worker B:** `codeOfREPred₂` or an equivalent `Semisentence ℒₒᵣ 2` representability helper.
- **Worker C:** `NONote` rank/order-type proof.
- **Worker D:** Nat coding transfer and final `EpsilonOrder` instance.

## Comment Protocol

Use this section for in-place negotiation between concurrent sessions. Add entries newest-last. Keep each comment actionable and prefix it with the agent/session name.

### Comment Log

- **Codex 2026-06-22:** Initial recommendation: split the seam into (1) formula adapter, (2) binary representability, (3) pure `NONote` order type, (4) Nat coding transfer, (5) `EpsilonOrder` instance.

