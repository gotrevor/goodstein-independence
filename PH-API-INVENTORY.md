# API inventory for an ordinal-descent lower bound (Paris–Harrington via Hardy functions)

Read-only research artifact. Everything below was read directly from source in this worktree
(`/Users/gotrevor/src/goodstein-independence/worktrees/gotrevor/hydra`, detached HEAD) on
2026-09-26. Every entry gives full name, exact `file:line`, and the exact source bytes (verbatim
quote, not paraphrase). Anything I did not open myself is explicitly marked **UNVERIFIED**.

Mathlib pin (`lake-manifest.json`): `leanprover-community/mathlib4` rev
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`, `inputRev "v4.31.0"`. Hardy.lean's own header confirms
it was ported against "mathlib rev fabf563a7c95, identical to this repo's pin."

---

## 0. The one-paragraph answer to "what's the fundamental-sequence convention?"

Mathlib's `ONote.fundamentalSequence` (quoted in full in §1.2) uses **zero-indexed `n : ℕ`** and
the **`succPNat` (`+1`) convention throughout**, never the bare index:

- **Successor**: `fundamentalSequence (β + 1) = Sum.inl (some β)` — literal predecessor, no index at
  all.
- **`ω^(α+1)` (successor exponent)**: `(ω^(α+1))[n] = ω^α · (n+1)`, i.e. **`·(n+1)`, not `·n`**.
  Source: match arm `| Sum.inl (some a'), 0 => Sum.inr fun i => oadd a' i.succPNat zero` (`i.succPNat
  = i+1`), restated as the repo's own `fundamentalSequence_omega_pow_succ` (Hardy.lean:247).
- **`ω^λ` (limit exponent `λ`)**: `(ω^λ)[n] = ω^(λ[n])` — direct descent into the exponent's own
  fundamental sequence, no `+1` shift (restated as `fundamentalSequence_omega_pow_limit`,
  Hardy.lean:254).
- **`ω^α·M` for `M ≥ 2`**: `(ω^α·M)[n] = ω^α·(M−1) + (ω^α)[n]` — peel one coefficient, then recurse
  into the single-coefficient case above.
- **Tail descent** `(ω^a·m + b)[n]`: if `b` is a limit, `= ω^a·m + b[n]`; if `b = b'+1`, the whole
  thing is a successor of `ω^a·m + b'`.
- Concretely: `ω = oadd 1 1 0` has `fundamentalSequence ω = Sum.inr (fun i => ofNat (i+1))`, i.e.
  **`ω[n] = n+1`, not `n`** — pinned by `rfl` at Hardy.lean:329, 462, 1308, 1337 and exercised by
  `hardy_omega : hardy (oadd 1 1 0) n = 2 * n + 1` (Hardy.lean:1336, whose docstring explicitly
  flags "the `+1` over the classical `H_ω(n)=n`").

The Hardy-hierarchy characterization that encodes this for `hardy` is `hardy_limit` (Hardy.lean:1130,
quoted in §2.6):
```
theorem hardy_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) :
    hardy o = fun n => hardy (f n) n := by
  rw [hardy_def h]
```
i.e. **at a limit, the same index `n` is fed to both the fundamental-sequence choice `f n` and the
recursive argument** — the "diagonal" self-application that makes the hierarchy fast-growing. There
is no further `+1` hiding in `hardy_limit` itself; every shift comes from mathlib's
`fundamentalSequence`, not from `hardy`/`fastGrowing`.

---

## 1. Mathlib `ONote` API

File: `.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/Notation.lean` (1298 lines).

### 1.1 The type, `repr`, `NF`/`NFBelow`

**`ONote`** — `Notation.lean:40-43`
```
inductive ONote : Type
  | zero : ONote
  | oadd : ONote → ℕ+ → ONote → ONote
  deriving DecidableEq
```
Module docstring (`Notation.lean:14-27`): *"We define a type `ONote`, with constructors `0 : ONote`
and `ONote.oadd e n a` representing `ω ^ e * n + a`. We say that `o` is in Cantor normal form -
`ONote.NF o` - if either `o = 0` or `o = ω ^ e * n + a` with `a < ω ^ e` and `a` in Cantor normal
form."*

**`ONote.repr`** — `Notation.lean:69-71`
```
noncomputable def repr : ONote → Ordinal.{0}
  | 0 => 0
  | oadd e n a => ω ^ repr e * n + repr a
```

**`ONote.lt_def` / `le_def`** — `Notation.lean:111,114` (unread bodies, `x < y ↔ repr x < repr y`
and `≤` analogue; used everywhere to move between `ONote`'s `<` and `Ordinal`'s).

**`ONote.NFBelow`** — `Notation.lean:178-181`
```
/-- `NFBelow o b` says that `o` is a normal form ordinal notation satisfying `repr o < ω ^ b`. -/
inductive NFBelow : ONote → Ordinal.{0} → Prop
  | zero {b} : NFBelow 0 b
  | oadd' {e n a eb b} : NFBelow e eb → NFBelow a (repr e) → repr e < b → NFBelow (oadd e n a) b
```

**`ONote.NF`** — `Notation.lean:192-196`
```
class NF (o : ONote) : Prop where
  out : Exists (NFBelow o)

instance NF.zero : NF 0 :=
  ⟨⟨0, NFBelow.zero⟩⟩
```

Constructor/projection lemmas actually used downstream (all `Notation.lean:198-251`):
```
theorem NFBelow.oadd {e n a b} : NF e → NFBelow a (repr e) → repr e < b → NFBelow (oadd e n a) b
theorem NF.fst {e n a} : NF (oadd e n a) → NF e
theorem NF.snd' {e n a} : NF (oadd e n a) → NFBelow a (repr e)
theorem NF.snd {e n a} (h : NF (oadd e n a)) : NF a
theorem NF.oadd {e a} (h₁ : NF e) (n) (h₂ : NFBelow a (repr e)) : NF (oadd e n a)
instance NF.oadd_zero (e n) [h : NF e] : NF (ONote.oadd e n 0) := h.oadd _ NFBelow.zero
theorem NFBelow.repr_lt {o b} (h : NFBelow o b) : repr o < ω ^ b
theorem NFBelow.mono {o b₁ b₂} (bb : b₁ ≤ b₂) (h : NFBelow o b₁) : NFBelow o b₂
theorem NF.below_of_lt' : ∀ {o b}, repr o < ω ^ b → NF o → NFBelow o b
```

**`ofNat`** — `Notation.lean:124-139`
```
@[coe] def ofNat : ℕ → ONote
  | 0 => 0
  | Nat.succ n => oadd 0 n.succPNat 0

@[simp] theorem ofNat_zero : ofNat 0 = 0 := rfl
@[simp] theorem ofNat_succ (n) : ofNat (Nat.succ n) = oadd 0 n.succPNat 0 := rfl
@[simp 1200] theorem ofNat_one : ofNat 1 = 1 := rfl
@[simp] theorem repr_ofNat (n : ℕ) : repr (ofNat n) = n := by cases n <;> simp
```

**Ordering facts on `oadd`** (`Notation.lean:143-277`) — the trichotomy toolkit `GoodsteinPA.norm`
work is built on:
```
theorem omega0_le_oadd (e n a) : ω ^ repr e ≤ repr (oadd e n a)
theorem oadd_pos (e n a) : 0 < oadd e n a
def cmp : ONote → ONote → Ordering
  | 0, 0 => Ordering.eq
  | _, 0 => Ordering.gt
  | 0, _ => Ordering.lt
  | _o₁@(oadd e₁ n₁ a₁), _o₂@(oadd e₂ n₂ a₂) =>
    (cmp e₁ e₂).then <| (_root_.cmp (n₁ : ℕ) n₂).then (cmp a₁ a₂)
theorem cmp_compares : ∀ (a b : ONote) [NF a] [NF b], (cmp a b).Compares a b   -- (line 280)
theorem repr_inj {a b} [NF a] [NF b] : repr a = repr b ↔ a = b                -- (line 319, unread body)
theorem oadd_lt_oadd_1 {e₁ n₁ o₁ e₂ n₂ o₂} (h₁ : NF (oadd e₁ n₁ o₁)) (h : e₁ < e₂) :
    oadd e₁ n₁ o₁ < oadd e₂ n₂ o₂
theorem oadd_lt_oadd_2 {e o₁ o₂ : ONote} {n₁ n₂ : ℕ+} (h₁ : NF (oadd e n₁ o₁)) (h : (n₁ : ℕ) < n₂) :
    oadd e n₁ o₁ < oadd e n₂ o₂
theorem oadd_lt_oadd_3 {e n a₁ a₂} (h : a₁ < a₂) : oadd e n a₁ < oadd e n a₂
```

`ONote.add`, `ONote.addAux`, `ONote.add_nf` (instance, `Notation.lean:419`, body unread) — ordinal
addition and its NF-preservation; used by `GoodsteinPA.FastGrowing.hardy_add_comp` and by
`HydraEscape.lean`'s `oadd P 1 0 + oadd (ofNat 3) 1 0` construction.

### 1.2 `fundamentalSequence` and `FundamentalSequenceProp` — exact source

**`ONote.fundamentalSequence`** — `Notation.lean:968-986`
```
/-- Given an ordinal, returns:

* `inl none` for `0`
* `inl (some a)` for `a + 1`
* `inr f` for a limit ordinal `a`, where `f i` is a sequence converging to `a` -/
def fundamentalSequence : ONote → (Option ONote) ⊕ (ℕ → ONote)
  | zero => Sum.inl none
  | oadd a m b =>
    match fundamentalSequence b with
    | Sum.inr f => Sum.inr fun i => oadd a m (f i)
    | Sum.inl (some b') => Sum.inl (some (oadd a m b'))
    | Sum.inl none =>
      match fundamentalSequence a, m.natPred with
      | Sum.inl none, 0 => Sum.inl (some zero)
      | Sum.inl none, m + 1 => Sum.inl (some (oadd zero m.succPNat zero))
      | Sum.inl (some a'), 0 => Sum.inr fun i => oadd a' i.succPNat zero
      | Sum.inl (some a'), m + 1 => Sum.inr fun i => oadd a m.succPNat (oadd a' i.succPNat zero)
      | Sum.inr f, 0 => Sum.inr fun i => oadd (f i) 1 zero
      | Sum.inr f, m + 1 => Sum.inr fun i => oadd a m.succPNat (oadd (f i) 1 zero)
```
Note the inner `match … , m.natPred with | …, m + 1 => …` **shadows** the outer `m : ℕ+` with a new
`ℕ`-valued `m` bound to `outer_m.natPred - 1`; i.e. the branch fires when `outer_m ≥ 2` and the
shadowed `m = outer_m - 2`.

**`ONote.FundamentalSequenceProp`** — `Notation.lean:1009-1020`
```
/-- The property satisfied by `fundamentalSequence o`:

* `inl none` means `o = 0`
* `inl (some a)` means `o = succ a`
* `inr f` means `o` is a limit ordinal and `f` is a strictly increasing sequence which converges to
  `o` -/
def FundamentalSequenceProp (o : ONote) : (Option ONote) ⊕ (ℕ → ONote) → Prop
  | Sum.inl none => o = 0
  | Sum.inl (some a) => o.repr = succ a.repr ∧ (o.NF → a.NF)
  | Sum.inr f =>
    IsSuccLimit o.repr ∧
      (∀ i, f i < f (i + 1) ∧ f i < o ∧ (o.NF → (f i).NF)) ∧ ∀ a, a < o.repr → ∃ i, a < (f i).repr
```
Unfolding lemmas (`Iff.rfl`, `Notation.lean:1022-1035`):
```
theorem fundamentalSequenceProp_inl_none (o) : FundamentalSequenceProp o (Sum.inl none) ↔ o = 0
theorem fundamentalSequenceProp_inl_some (o a) :
    FundamentalSequenceProp o (Sum.inl (some a)) ↔ o.repr = succ a.repr ∧ (o.NF → a.NF)
theorem fundamentalSequenceProp_inr (o f) :
    FundamentalSequenceProp o (Sum.inr f) ↔
      IsSuccLimit o.repr ∧
        (∀ i, f i < f (i + 1) ∧ f i < o ∧ (o.NF → (f i).NF)) ∧
        ∀ a, a < o.repr → ∃ i, a < (f i).repr
```

**`ONote.fundamentalSequence_has_prop`** — `Notation.lean:1037`
```
theorem fundamentalSequence_has_prop (o) : FundamentalSequenceProp o (fundamentalSequence o) := by
  -- structural induction on o, one case per branch of `fundamentalSequence`; ~50 lines, Notation.lean:1038-1102
```
This is the correctness certificate GoodsteinPA's `Reaches`/`hardy`/`fastGrowing` machinery invokes
by name at essentially every well-founded-recursion step (`rw [e] at hp; exact hp.1` / `hp.2.1 n`
idioms throughout Hardy.lean).

### 1.3 `ONote.fastGrowing` (mathlib's own fast-growing hierarchy)

**Definition** — `Notation.lean:1104-1121`
```
/-- The fast growing hierarchy for ordinal notations `< ε₀`. This is a sequence of functions `ℕ → ℕ`
indexed by ordinals, with the definition:

* `f_0(n) = n + 1`
* `f_(α + 1)(n) = f_α^[n](n)`
* `f_α(n) = f_(α[n])(n)` where `α` is a limit ordinal and `α[i]` is the fundamental sequence
  converging to `α` -/
def fastGrowing : ONote → ℕ → ℕ
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => Nat.succ
    | Sum.inl (some a), h =>
      have : a < o := by rw [lt_def, h.1]; apply lt_succ
      fun i => (fastGrowing a)^[i] i
    | Sum.inr f, h => fun i =>
      have : f i < o := (h.2.1 i).2.1
      fastGrowing (f i) i
  termination_by o => o
```

Characterization lemmas — `Notation.lean:1123-1150`
```
theorem fastGrowing_def {o : ONote} {x} (e : fundamentalSequence o = x) :
    fastGrowing o =
      match
        (motive := (x : Option ONote ⊕ (ℕ → ONote)) → FundamentalSequenceProp o x → ℕ → ℕ)
        x, e ▸ fundamentalSequence_has_prop o with
      | Sum.inl none, _ => Nat.succ
      | Sum.inl (some a), _ => fun i => (fastGrowing a)^[i] i
      | Sum.inr f, _ => fun i => fastGrowing (f i) i := by
  subst x
  rw [fastGrowing]

theorem fastGrowing_zero' (o : ONote) (h : fundamentalSequence o = Sum.inl none) :
    fastGrowing o = Nat.succ := by rw [fastGrowing_def h]

theorem fastGrowing_succ (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    fastGrowing o = fun i => (fastGrowing a)^[i] i := by rw [fastGrowing_def h]

theorem fastGrowing_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) :
    fastGrowing o = fun i => fastGrowing (f i) i := by rw [fastGrowing_def h]

@[simp] theorem fastGrowing_zero : fastGrowing 0 = Nat.succ
@[simp] theorem fastGrowing_one : fastGrowing 1 = fun n => 2 * n
@[simp] theorem fastGrowing_two : fastGrowing 2 = fun n => (2 ^ n) * n
```

**`ONote.fastGrowingε₀`** — `Notation.lean:1162-1171`
```
/-- We can extend the fast growing hierarchy one more step to `ε₀` itself, using `ω ^ (ω ^ (⋯ ^ ω))`
as the fundamental sequence converging to `ε₀` (which is not an `ONote`). Extending the fast
growing hierarchy beyond this requires a definition of fundamental sequence for larger ordinals. -/
def fastGrowingε₀ (i : ℕ) : ℕ :=
  fastGrowing ((fun a => a.oadd 1 0)^[i] 0) i

theorem fastGrowingε₀_zero : fastGrowingε₀ 0 = 1
theorem fastGrowingε₀_one : fastGrowingε₀ 1 = 2
theorem fastGrowingε₀_two : fastGrowingε₀ 2 = 2048   -- Notation.lean:1173
```

Mathlib does **not** define a Hardy hierarchy at all, and per Hardy.lean's own docstring proves only
these "small values," none of the growth theory (monotonicity, domination, index comparison) — that
is exactly what `GoodsteinPA.FastGrowing` (§2 below) supplies.

`NONote` (`Notation.lean:1184+`, not read in detail) is a bundled `{o : ONote // o.NF}`-style
subtype with its own `repr`, `cmp`, `+`,`-`,`*`,`^`; GoodsteinPA works directly on raw `ONote` +
`NF` hypotheses instead, so `NONote` is likely irrelevant to this task — **UNVERIFIED whether
anything in GoodsteinPA touches `NONote`** (a repo-wide grep for `NONote` was not run).

---

## 2. `GoodsteinPA.FastGrowing` (`src/GoodsteinPA/Hardy.lean`, 2171 lines) — the reusable growth-theory API

Namespace `GoodsteinPA.FastGrowing`, `open ONote Ordinal`. Module header (`Hardy.lean:1-6`):
*"Verbatim merge of FastGrowing/{Basic,Domination,Hardy}.lean (mathlib rev fabf563a7c95, identical
to this repo's pin). Provides `hardy`, `norm`, `hardy_le_of_lt` (= Hmono), `hardy_monotone` (=
Hmono_n), `fastGrowing_*`. WIP — not in build target. Namespace localized."* **This file is WIP and
not wired into the build target** — confirm current build-membership status before relying on
"proved" claims in its docstrings without re-checking (`lake env lean` on it, or checking
`GoodsteinPA.lean`'s import list) — not done as part of this inventory.

This file has three ported sections (Basic / Domination / Hardy); I follow that structure.

### 2.1 `Reaches` — the structural descent relation (Basic, `Hardy.lean:125-165`)

```
inductive Reaches (x : ℕ) : ONote → ONote → Prop
  | refl (a : ONote) : Reaches x a a
  | succ {β γ α : ONote} (h : fundamentalSequence β = Sum.inl (some γ))
      (hr : Reaches x γ α) : Reaches x β α
  | limit {β α : ONote} {g : ℕ → ONote} (h : fundamentalSequence β = Sum.inr g)
      (hr : Reaches x (g x) α) : Reaches x β α
```
"From `β` one can step down to `α` through `fundamentalSequence`, using predecessor steps at
successor notations and index-`x` steps at limit notations." (`Hardy.lean:120-124`)

```
theorem Reaches.trans {x : ℕ} {a b c : ONote} (h1 : Reaches x a b) (h2 : Reaches x b c) :
    Reaches x a c                                                          -- Hardy.lean:133
theorem fastGrowing_le_of_reaches {x : ℕ} (hx : 1 ≤ x) {β α : ONote}
    (h : Reaches x β α) : fastGrowing α x ≤ fastGrowing β x                -- Hardy.lean:145
theorem reaches_le {x : ℕ} {β α : ONote} (h : Reaches x β α) : α ≤ β       -- Hardy.lean:153
theorem Reaches.oadd_tail {x : ℕ} {a : ONote} {m : ℕ+} {δ' δ : ONote}
    (h : Reaches x δ' δ) : Reaches x (oadd a m δ') (oadd a m δ)            -- Hardy.lean:191
theorem reaches_zero (o : ONote) (x : ℕ) : Reaches x o 0                  -- Hardy.lean:201
theorem reaches_coeff_step' (e : ONote) (j x : ℕ) :
    Reaches x (oadd e (j + 1).succPNat 0) (oadd e j.succPNat 0)            -- Hardy.lean:220
theorem reaches_coeff_chain (e : ONote) (j x : ℕ) :
    Reaches x (oadd e j.succPNat 0) (oadd e (0 : ℕ).succPNat 0)            -- Hardy.lean:240
theorem reaches_omega_pow_lift {x : ℕ} {γ' γ : ONote}
    (h : Reaches x γ' γ) : Reaches x (oadd γ' 1 0) (oadd γ 1 0)            -- Hardy.lean:264
```

Restated `fundamentalSequence` equations used to build `Reaches` steps for `oadd`/`ω^·`
(`Hardy.lean:177-259`):
```
theorem fundamentalSequence_oadd_succ {a : ONote} {m : ℕ+} {b b' : ONote}
    (h : fundamentalSequence b = Sum.inl (some b')) :
    fundamentalSequence (oadd a m b) = Sum.inl (some (oadd a m b'))
theorem fundamentalSequence_oadd_limit {a : ONote} {m : ℕ+} {b : ONote} {h : ℕ → ONote}
    (hb : fundamentalSequence b = Sum.inr h) :
    fundamentalSequence (oadd a m b) = Sum.inr (fun i => oadd a m (h i))
theorem fundamentalSequence_omega_pow_succ {γ' δ : ONote}
    (he : fundamentalSequence γ' = Sum.inl (some δ)) :
    fundamentalSequence (oadd γ' 1 0) = Sum.inr (fun i => oadd δ i.succPNat 0)
theorem fundamentalSequence_omega_pow_limit {γ' : ONote} {q : ℕ → ONote}
    (he : fundamentalSequence γ' = Sum.inr q) :
    fundamentalSequence (oadd γ' 1 0) = Sum.inr (fun i => oadd (q i) 1 0)
theorem fundamentalSequence_ofNat_succ (k : ℕ) :
    fundamentalSequence (ofNat (k + 1)) = Sum.inl (some (ofNat k))          -- Hardy.lean:276
```

**The Bachmann reachability crux (A3)** — `Hardy.lean:355`
```
theorem fastGrowing_bachmann_reach {o : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence o = Sum.inr f) (n : ℕ) :
    Reaches (n + 1) (f (n + 1)) (f n)
```
*"the descent of `f (n+1)` (at the fixed index `n+1`) passes exactly through `f n`"* — proved fully,
structural recursion, `[propext, choice, Quot.sound]` only (`Hardy.lean:338-339`). This is the
theorem `hardy_monotone`/`hardy_fundSeq_step` (§2.6) and `fastGrowing_monotone` both bottom out in.

### 2.2 `fastGrowing` growth theory (A1–A3, `Hardy.lean:44-565`)

```
theorem le_fastGrowing (o : ONote) (n : ℕ) : n ≤ fastGrowing o n                       -- 54
theorem lt_fastGrowing (o : ONote) {n : ℕ} (hn : 1 ≤ n) : n < fastGrowing o n           -- 85
theorem fastGrowing_le_succ_index {o a : ONote}
    (h : fundamentalSequence o = Sum.inl (some a)) {n : ℕ} (hn : 1 ≤ n) :
    fastGrowing a n ≤ fastGrowing o n                                                   -- 113
theorem fastGrowing_fundSeq_step {o : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence o = Sum.inr f) (n : ℕ) :
    fastGrowing (f n) (n + 1) ≤ fastGrowing (f (n + 1)) (n + 1)                          -- 395
theorem fastGrowing_le_succ (o : ONote) (n : ℕ) :
    fastGrowing o n ≤ fastGrowing o (n + 1)                                              -- 530
theorem fastGrowing_monotone (o : ONote) : Monotone (fastGrowing o)                      -- 564
```
Also present but narrower/instance-specific (index/argument monotonicity built up to the general
theorems above): `fastGrowing_succ_chain_mono`, `fastGrowing_ofNat_mono`,
`fastGrowing_ofNat_monotone`, `fastGrowing_monotone_omega(')`, `fastGrowing_monotone_omega_mul`,
`fundamentalSequence_oadd_ofNat_succ`, `fastGrowing_omega_sq_index_step`,
`fastGrowing_monotone_omega_sq`, `fastGrowing_monotone_succ`,
`fastGrowing_monotone_of_succ_chain_limit`, `fastGrowing_fundSeq_step_of_succ` — all
`Hardy.lean:282-525`, statements listed but not re-quoted here (they are stepping-stones consumed
by `fastGrowing_le_succ`/`_monotone`, not final API surface).

### 2.3 CNF `norm` and general Bachmann reachability (A4 core, `Hardy.lean:605-891`)

**`norm`** — `Hardy.lean:635-642`
```
/-- **CNF norm** of a notation: the maximum finite coefficient appearing anywhere in its
Cantor normal form (recursively through exponents and tails). `norm 0 = 0`,
`norm (ω^e·n + a) = max (norm e) (max n (norm a))`. -/
def norm : ONote → ℕ
  | 0 => 0
  | oadd e n a => max (norm e) (max (n : ℕ) (norm a))

@[simp] theorem norm_zero : norm 0 = 0 := rfl
@[simp] theorem norm_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    norm (oadd e n a) = max (norm e) (max (n : ℕ) (norm a)) := rfl
```

```
theorem repr_lt_opow_repr : ∀ (o : ONote), o.NF → o.repr < ω ^ o.repr                    -- 610
theorem lt_oadd_cases {ea : ONote} {na : ℕ+} {ba e : ONote} {m : ℕ+} {b : ONote}
    (hα : NF (oadd ea na ba)) (hβ : NF (oadd e m b)) (h : oadd ea na ba < oadd e m b) :
    ea < e ∨ (ea = e ∧ (na : ℕ) < (m : ℕ)) ∨ (ea = e ∧ na = m ∧ ba < b)                  -- 646
theorem lt_oadd_of_lead_le {x : ℕ} {c : ONote} (hc : c.NF) {δ : ONote} (hδ : δ.NF)
    (hlead : δ.repr < ω ^ c.repr * ω) (hnorm : norm δ ≤ x) :
    δ < oadd c x.succPNat 0                                                             -- 669
```

**The key cofinality bound (the one genuinely new theorem of A4)** — `Hardy.lean:700`
```
theorem lt_fundamentalSequence_of_norm_le {x : ℕ} :
    ∀ (β : ONote), β.NF → ∀ (g : ℕ → ONote), fundamentalSequence β = Sum.inr g →
      ∀ (α : ONote), α.NF → α < β → norm α ≤ x → α < g x
```
*"For a normal-form limit `β` with standard fundamental sequence `g`, every `α < β` whose CNF norm
is `≤ x` already sits below the `x`-th rung `g x`."* — the budget condition that lets an arbitrary
`α < β` (not just consecutive indices) be reached.

**General Bachmann reachability** — `Hardy.lean:836`
```
theorem reaches_of_lt {x : ℕ} :
    ∀ (β : ONote), β.NF → ∀ (α : ONote), α.NF → α < β → norm α ≤ x → Reaches x β α
```

```
theorem fastGrowing_lt_succ_index {o a : ONote}
    (h : fundamentalSequence o = Sum.inl (some a)) {n : ℕ} (hn : 2 ≤ n) :
    fastGrowing a n < fastGrowing o n                                                   -- 866
```

**`fastGrowing_le_of_lt` — the general index-monotonicity API** — `Hardy.lean:889`
```
theorem fastGrowing_le_of_lt {x : ℕ} (hx : 1 ≤ x) {α β : ONote} (hα : α.NF) (hβ : β.NF)
    (hαβ : α < β) (hnorm : norm α ≤ x) : fastGrowing α x ≤ fastGrowing β x :=
  fastGrowing_le_of_reaches hx (reaches_of_lt β hβ α hα hαβ hnorm)
```
**This — and its Hardy-side twin `hardy_le_of_lt` (§2.7) — is the single most-reused comparison
lemma in the whole file**: "normal-form `α < β` plus budget `x ≥ norm α` (and `x ≥ 1`) gives
`fastGrowing α x ≤ fastGrowing β x`."

### 2.4 `osucc`, `tower`, and the A4 headline domination (`Hardy.lean:893-1067`)

**`osucc`** (notation successor, structural) — `Hardy.lean:903-906`
```
def osucc : ONote → ONote
  | 0 => oadd 0 1 0
  | oadd 0 n _ => oadd 0 (n + 1) 0
  | oadd (oadd e' n' a') m b => oadd (oadd e' n' a') m (osucc b)
```
```
theorem repr_osucc : ∀ {o : ONote}, o.NF → (osucc o).repr = o.repr + 1               -- 908
theorem osucc_NF : ∀ {o : ONote}, o.NF → (osucc o).NF                                -- 924
theorem fundamentalSequence_osucc : ∀ {o : ONote}, o.NF →
    fundamentalSequence (osucc o) = Sum.inl (some o)                                 -- 937
theorem norm_osucc_le : ∀ {o : ONote}, norm (osucc o) ≤ norm o + 1                    -- 951
```

**`tower`** (the diagonal `0, 1, ω, ω^ω, …` underlying `fastGrowingε₀`) — `Hardy.lean:961`
```
def tower (i : ℕ) : ONote := (fun a => oadd a 1 0)^[i] 0

@[simp] theorem tower_zero : tower 0 = 0 := rfl
theorem tower_succ (i : ℕ) : tower (i + 1) = oadd (tower i) 1 0                       -- 966
theorem tower_NF : ∀ i, (tower i).NF                                                 -- 970
theorem tower_lt_succ (i : ℕ) : tower i < tower (i + 1)                              -- 976
theorem tower_strictMono : StrictMono tower                                          -- 984
theorem repr_tower_succ (i : ℕ) : (tower (i + 1)).repr = ω ^ (tower i).repr          -- 988
theorem tower_cofinal : ∀ (o : ONote), o.NF → ∃ k, o < tower k                       -- 995
theorem fastGrowingε₀_eq (i : ℕ) : fastGrowingε₀ i = fastGrowing (tower i) i := rfl   -- 1010
```
Anti-vacuity anchor: `example : tower 3 = oadd (oadd 1 1 0) 1 0 := by native_decide` — confirms
`tower 3 = ω^ω` (a genuine limit-of-limits).

**A4 headline** — `Hardy.lean:1018,1049`
```
theorem fastGrowing_lt_of_lt_tower {o : ONote} (ho : o.NF) (n : ℕ)
    (hn : norm o < n) (h2 : 2 ≤ n) (h : o < tower n) :
    fastGrowing o n < fastGrowing (tower n) n

theorem fastGrowing_lt_fastGrowingε₀ (o : ONote) (ho : o.NF) :
    ∃ N, ∀ n ≥ N, fastGrowing o n < fastGrowingε₀ n
```
*This is the exact Kirby–Paris "growth gap": every fixed level is eventually strictly dominated.*

### 2.5 `hardy` — the Hardy hierarchy: definition and characterization lemmas

**`hardy`** — `Hardy.lean:1095-1105`
```
/-- The **Hardy hierarchy** `H_α : ℕ → ℕ` for ordinal notations `< ε₀`:
`H₀ = id`, `H_{α+1}(n) = H_α(n+1)`, `H_λ(n) = H_{λ[n]}(n)` (limit `λ`, via
`ONote.fundamentalSequence`). Same well-founded recursion as `ONote.fastGrowing`. -/
def hardy : ONote → ℕ → ℕ
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => id
    | Sum.inl (some a), h =>
      have : a < o := by rw [lt_def, h.1]; exact Order.lt_succ _
      fun n => hardy a (n + 1)
    | Sum.inr f, h => fun n =>
      have : f n < o := (h.2.1 n).2.1
      hardy (f n) n
  termination_by o => o
```

**`hardy_def`, `hardy_zero'`, `hardy_succ`, `hardy_limit`** — `Hardy.lean:1108-1132` (exact)
```
theorem hardy_def {o : ONote} {x} (e : fundamentalSequence o = x) :
    hardy o =
      match
        (motive := (x : Option ONote ⊕ (ℕ → ONote)) → FundamentalSequenceProp o x → ℕ → ℕ)
        x, e ▸ fundamentalSequence_has_prop o with
      | Sum.inl none, _ => id
      | Sum.inl (some a), _ => fun n => hardy a (n + 1)
      | Sum.inr f, _ => fun n => hardy (f n) n := by
  subst x
  rw [hardy]

theorem hardy_zero' (o : ONote) (h : fundamentalSequence o = Sum.inl none) :
    hardy o = id := by rw [hardy_def h]

/-- `H_o(n) = H_a(n+1)` when `o` is the successor of `a`. -/
theorem hardy_succ (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    hardy o = fun n => hardy a (n + 1) := by rw [hardy_def h]

/-- `H_o(n) = H_{o[n]}(n)` when `o` is a limit with fundamental sequence `f`. -/
theorem hardy_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) :
    hardy o = fun n => hardy (f n) n := by rw [hardy_def h]
```

```
@[simp] theorem hardy_zero : hardy 0 = id                                            -- 1136
theorem hardy_one : hardy 1 = fun n => n + 1                                          -- 1140
theorem hardy_two : hardy 2 = fun n => n + 2                                          -- 1144
theorem hardy_ofNat (k x : ℕ) : hardy (ofNat k) x = x + k                             -- 1326
theorem hardy_omega (n : ℕ) : hardy (oadd 1 1 0) n = 2 * n + 1                        -- 1336
```
`hardy_omega`'s docstring: *"mathlib's `ω[n] = ofNat (n+1)` makes the limit step land on the finite
level `n+1`, so `H_ω(n) = H_{n+1}(n) = n + (n+1) = 2n+1`. (The `+1` over the classical `H_ω(n)=n` is
exactly the `ω[n]=n+1` convention shift.)"* — the convention consequence spelled out by the repo
itself, matching §0.

### 2.6 `hardy` growth theory: expansiveness, monotonicity, index comparison

```
theorem le_hardy (o : ONote) (n : ℕ) : n ≤ hardy o n                                            -- 1152
theorem hardy_le_of_reaches {x : ℕ} {β α : ONote} (h : Reaches x β α) :
    (∀ γ, Reaches x β γ → Monotone (hardy γ)) → hardy α x ≤ hardy β x                            -- 1175
theorem hardy_monotone (o : ONote) : Monotone (hardy o)                                          -- 1197
theorem hardy_le_succ (o : ONote) (n : ℕ) : hardy o n ≤ hardy o (n + 1) :=
  hardy_monotone o (Nat.le_succ n)                                                               -- 1227
theorem hardy_fundSeq_step {o : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence o = Sum.inr f) (n : ℕ) :
    hardy (f n) (n + 1) ≤ hardy (f (n + 1)) (n + 1)                                              -- 1277
theorem hardy_le_fastGrowing (o : ONote) (n : ℕ) (hn : 2 ≤ n) :
    hardy o n ≤ fastGrowing o n                                                                  -- 1907
```

**`hardy_le_of_lt` — the general index-monotonicity API for `hardy`** — `Hardy.lean:1320`
```
theorem hardy_le_of_lt {x : ℕ} {α β : ONote} (hα : α.NF) (hβ : β.NF)
    (hαβ : α < β) (hnorm : norm α ≤ x) : hardy α x ≤ hardy β x :=
  hardy_le_of_reaches (reaches_of_lt β hβ α hα hαβ hnorm) (fun γ _ => hardy_monotone γ)
```
Exact `hardy` analogue of `fastGrowing_le_of_lt` (§2.3) — the module docstring calls it `Hmono`.

### 2.7 `hardy` composition / additivity laws (the "combine two levels" toolkit)

```
theorem hardy_add_ofNat {α : ONote} (hα : α.NF) :
    ∀ (c n : ℕ), hardy (α + ofNat c) n = hardy α (n + c)                                 -- 1257
theorem hardy_oadd_tail (a : ONote) (m : ℕ+) (b : ONote) (n : ℕ) :
    hardy (oadd a m b) n = hardy (oadd a m 0) (hardy b n)                                -- 1505
theorem hardy_oadd_coeff_step (β : ONote) (hβ : β ≠ 0) (k x : ℕ) :
    hardy (oadd β (k + 1).succPNat 0) x
      = hardy (oadd β k.succPNat 0) (hardy (oadd β 1 0) x)                               -- 1536
theorem hardy_oadd_coeff (β : ONote) (hβ : β ≠ 0) (k x : ℕ) :
    hardy (oadd β k.succPNat 0) x = (hardy (oadd β 1 0))^[k + 1] x                        -- 1564
def lastExp : ONote → ONote
  | 0 => 0
  | oadd e _ a => match a with
    | 0 => e
    | oadd _ _ _ => lastExp a                                                            -- 1583
```

**`hardy_add_comp` — the general non-absorbing additive composition law** — `Hardy.lean:1639`
```
/-- **The general non-absorbing Hardy additive composition law.** For normal-form `γ`, `δ`
with `δ` lying strictly below `γ`'s least exponent (so `γ + δ` is genuine Cantor-normal-form
concatenation, no coefficient merge / absorption), the Hardy hierarchy composes:
`H_{γ+δ}(x) = H_γ(H_δ(x))`. -/
theorem hardy_add_comp : ∀ (γ : ONote), γ.NF → ∀ (δ : ONote), δ.NF →
    (δ = 0 ∨ δ.repr < ω ^ (lastExp γ).repr) → ∀ x,
    hardy (γ + δ) x = hardy γ (hardy δ x)
```
Non-absorbing side condition is essential: `1+ω=ω` makes the *unconditional* equality false
(`H_{1+ω}=H_ω ≠ H_1∘H_ω`, remarked at `Hardy.lean:1579`). Corollary used directly by
`HydraEscape.lean` (§4):
```
theorem hardy_add_collapse {e α : ONote} (he : e.NF) (hα : α.NF)
    (hbelow : α = 0 ∨ α.repr < ω ^ (lastExp e).repr) (x : ℕ) :
    hardy (e + α) x = hardy e (hardy α x) :=
  hardy_add_comp e he α hα hbelow x                                                      -- 1686
```

**`hardy_add_le_comp` — the unconditional inequality (survives absorption)** — `Hardy.lean:1725`
```
theorem hardy_add_le_comp : ∀ (e : ONote), e.NF → ∀ (β : ONote), β.NF → ∀ x,
    hardy (e + β) x ≤ hardy e (hardy β x)
```
plus its principal-raise specialization:
```
theorem hardy_add_omega_pow_le {e α : ONote} (he : e.NF) (hα : α.NF) (x : ℕ) :
    hardy (e + oadd α 1 0) x ≤ hardy e (hardy (oadd α 1 0) x)                             -- 1809
```

### 2.8 `hstep` — the budget-incrementing Hardy step

```
def hstep : ONote → ℕ → ONote
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => fun _ => 0
    | Sum.inl (some a), _ => fun _ => a
    | Sum.inr f, h => fun n =>
      have : f n < o := (h.2.1 n).2.1
      hstep (f n) n
  termination_by o => o                                                                  -- 1403

theorem hstep_succ (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    hstep o = fun _ => a                                                                 -- 1425
theorem hstep_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) :
    hstep o = fun n => hstep (f n) n                                                     -- 1429

/-- **Intrinsic Hardy step invariant.** `H_o(n) = H_{hstep o n}(n+1)` for `o ≠ 0`. -/
theorem hardy_hstep (o : ONote) (n : ℕ) (h : o ≠ 0) :
    hardy o n = hardy (hstep o n) (n + 1)                                                -- 1436
theorem hstep_oadd_tail (E : ONote) (C : ℕ+) (b : ℕ) :
    ∀ R, R ≠ 0 → hstep (oadd E C R) b = oadd E C (hstep R b)                              -- 1453
```
This is the engine the docstring says is the "FastGrowing-side prerequisite for C3
(`Goodstein/Growth.lean`)" — telescoping a unit-step ordinal descent into a Hardy value. Likely
directly relevant to a PH lower bound if the PH descent is phrased as a sequence of single
fundamental-sequence steps (as the hydra battle is, see §4).

### 2.9 The B4 bracket: `hardy (ω^α)` vs `fastGrowing α` — the two named target lemmas

```
theorem hardy_omega_pow_ofNat (k x : ℕ) :
    hardy (oadd (ofNat k) 1 0) x + 1 = fastGrowing (ofNat k) (x + 1)                      -- 1871
theorem hardy_omega_pow_omega (n : ℕ) :
    hardy (oadd (oadd 1 1 0) 1 0) n + 1 = fastGrowing (ofNat (n + 1)) (n + 1)             -- 1888
```
Both docstrings stress the classical identity `H_{ω^α} = f_α` is **exact only at finite/successor
`α`**; at a limit `α` it degrades to an inequality (worked example: `H_{ω^ω}(1)+1 = 8 ≠ f_ω(2) =
2048`).

**Unconditional two-sided bracket** (the load-bearing pair for any new domination argument):
```
theorem hardy_omega_pow_add_one_le (α : ONote) : ∀ n : ℕ,
    hardy (oadd α 1 0) n + 1 ≤ fastGrowing α (n + 1)                                      -- 2004

theorem hardy_omega_pow_lt_fastGrowing (α : ONote) (n : ℕ) :
    hardy (oadd α 1 0) n < fastGrowing α (n + 1) :=
  by have h := hardy_omega_pow_add_one_le α n; omega                                      -- 2037
```

```
/-- **B4 LOWER bound at an arbitrary exponent `α`** — `f_α(n) ≤ H_{ω^α}(n)`, unconditional. -/
theorem fastGrowing_le_hardy_omega_pow (α : ONote) : ∀ n : ℕ,
    fastGrowing α n ≤ hardy (oadd α 1 0) n                                                -- 2062
```
(Full induction: `α=0` trivial; `α` successor reduces via `hardy_oadd_coeff` +
`iterate_le_iterate_of_le` (`Hardy.lean:2047`, private) to `(fastGrowing β)^[n] n ≤ (hardy (oadd β 1
0))^[n] n`; `α` limit is the IH verbatim at the fundamental-sequence index.)

```
/-- **The two-sided E–W Lemma 19 bracket at `ω^α`:** `f_α(n) ≤ H_{ω^α}(n) < f_α(n+1)`. -/
theorem hardy_omega_pow_bracket (α : ONote) (n : ℕ) :
    fastGrowing α n ≤ hardy (oadd α 1 0) n ∧ hardy (oadd α 1 0) n < fastGrowing α (n + 1) :=
  ⟨fastGrowing_le_hardy_omega_pow α n, hardy_omega_pow_lt_fastGrowing α n⟩             -- 2105
```
Coefficient-general lifts of the bracket (useful if a PH descent needs `ω^α·k` rather than a bare
`ω^α`):
```
theorem fastGrowing_iterate_le_hardy_coeff (α : ONote) (hα : α ≠ 0) (k n : ℕ) :
    (fastGrowing α)^[k + 1] n ≤ hardy (oadd α k.succPNat 0) n                             -- 2112
theorem hardy_coeff_add_one_le (α : ONote) (hα : α ≠ 0) (k n : ℕ) :
    hardy (oadd α k.succPNat 0) n + 1 ≤ (fastGrowing α)^[k + 1] (n + 1)                   -- 2131
theorem hardy_omega_pow_coeff_bracket (α : ONote) (hα : α ≠ 0) (k n : ℕ) :
    (fastGrowing α)^[k + 1] n ≤ hardy (oadd α k.succPNat 0) n
      ∧ hardy (oadd α k.succPNat 0) n < (fastGrowing α)^[k + 1] (n + 1)                   -- 2139
```
ε₀-diagonal capstone (only relevant if a PH bound needs to reach past every fixed level to
`fastGrowingε₀`, cf. `Hardy.lean:2145-2169`): `fastGrowingε₀_le_hardy_tower_succ`,
`hardy_tower_succ_lt_fastGrowing`.

---

## 3. `GoodsteinPA.HardyMajorization` (`src/GoodsteinPA/HardyMajorization.lean`, 1396 lines)

**Scope note**: this file is a *different, more specialized* pipeline — majorizing the `ewIter`
read-off value of the §19.6 cut-elimination / operator-calculus machinery (`OperatorZef2`,
`OperatorZeh`) by a single fixed `hardy` level, for the E1-embedding proof. It is almost certainly
**not** the file to build a PH lower bound on top of, but it contains a handful of genuinely generic
`hardy`/`norm` lemmas worth knowing about. Namespace `GoodsteinPA.HardyMajorization`, `open ONote
Ordinal GoodsteinPA.FastGrowing GoodsteinPA.OperatorZeh`.

Generic, reusable (quoted in full):
```
noncomputable def Wpow (x : ONote) : ONote := oadd x 1 0                                 -- 63
theorem Wpow_NF {x : ONote} (hx : x.NF) : (Wpow x).NF := NF.oadd hx 1 NFBelow.zero        -- 65
theorem Wpow_lt {x y : ONote} (h : x < y) : Wpow x < Wpow y                               -- 170

theorem hardy_succ_ge (o : ONote) (n : ℕ) : hardy o n + 1 ≤ hardy o (n + 1)               -- 142
theorem hardy_arg_add (o : ONote) (n c : ℕ) : hardy o n + c ≤ hardy o (n + c)             -- 160

def normSum : ONote → ℕ
  | 0 => 0
  | oadd e n a => max (norm e) (n : ℕ) + normSum a                                        -- 184
theorem norm_addAux_le (e : ONote) (n : ℕ+) (o : ONote) :
    norm (addAux e n o) ≤ max (norm e) (n : ℕ) + norm o                                   -- 188
theorem norm_add_le : ∀ (x y : ONote), norm (x + y) ≤ normSum x + norm y                  -- 213
```
`norm_lt_two_pow_Nlog` / `norm_lt_of_Nlog_le` (`HardyMajorization.lean:27,49`) bridge the linear CNF
`norm` (§2.3) to a log-scaled `Nlog` (defined in `OperatorZeh`, **UNVERIFIED** — not opened) used by
the `ewIter` pipeline; unlikely to matter for PH unless the new proof also needs a log-vs-linear
norm bridge.

Everything else in this file — `stepOrd`/`stepOrd3`, `hardy_chain_eq`, `hardy_step_raise`,
`hardy_step`, `hardy_chain3_eq`, `stepOrd3_lt_Wpow`, `ewIter_hardy_le`, `hEng_of_dom*`,
`ewIterTower_dom_pad`, `dom_pad_*`, `Sstar_dom_pad`, `Scirc_dom_pad`, `master_conversion`
(`HardyMajorization.lean:60-1396`) — is `ewIter`/read-off-pipeline-specific plumbing, listed by
signature only (§ grep in the transcript above), not quoted; **UNVERIFIED in detail** beyond the
signatures already shown, since it appears out of scope for a self-contained PH ordinal-descent
argument built directly on `hardy`/`fastGrowing`.

---

## 4. `HydraLowerBound.lean` + `HydraEscape.lean` — the existing lower-bound + escape precedent

This is the closest existing analogue to "an ordinal-descent lower bound via Hardy functions," and
`GoodsteinPA.PH` (stage 3, same repo) is **already scaffolded to mirror it exactly** — see §4.4.

### 4.1 `HydraLowerBound.lean` (78 lines) — full content

Namespace `GoodsteinPA.Hydra`, imports `GoodsteinPA.Hardy` and (external)
`LeanGallery.Logic.Hydra.Canonical`. Module doc: *"Because each canonical move is one
fundamental-sequence step of `ord` (`LeanGallery.Logic.Hydra.ord_canonStep`), the battle is still
alive at step `k` whenever `t + k < hardy (ord h) t`: the successor case is `hardy_succ`, the limit
case `hardy_limit` plus `hardy_le_succ`."*

```
def runFrom (h : Hydra) (t : ℕ) : ℕ → Hydra
  | 0 => h
  | k + 1 => canonStep (t + k) (runFrom h t k)                                            -- 25

theorem battle_eq_runFrom (h : Hydra) : ∀ k, battle h k = runFrom h 0 k                    -- 29
theorem runFrom_succ (h : Hydra) (t : ℕ) :
    ∀ k, runFrom h t (k + 1) = runFrom (canonStep t h) (t + 1) k                           -- 33

/-- **P2.** Started at turn `t`, the canonical battle is alive at every step `k` with
`t + k < hardy (ord h) t`. -/
theorem runFrom_alive_of_lt_hardy :
    ∀ (h : Hydra) (t k : ℕ), t + k < hardy (ord h) t → runFrom h t k ≠ Hydra.leaf          -- 43
```
Proof shape of `runFrom_alive_of_lt_hardy` (`Hardy.lean:44-77` sic, actually
`HydraLowerBound.lean:44-77`): well-founded induction on `ONote.repr (ord h)` (via
`WellFoundedLT.induction`); at each step, case on `ord_canonStep t h hl : (fundamentalSequence (ord
h) = Sum.inl (some s)) ∨ ∃ f, fundamentalSequence (ord h) = Sum.inr f ∧ ord (canonStep t h) = f
t`:
- **successor branch**: `rw [hardy_succ _ hs] at hlt` turns the hypothesis `t+(k+1) <
  hardy (ord h) t` into `t+(k+1) < hardy s (t+1)`, then recurses with `t+1, k`.
- **limit branch**: `rw [hardy_limit _ hf] at hlt` plus `hardy_le_succ (f t) t` (the two named
  lemmas the module doc calls out) absorb the turn-advance `t → t+1` into a
  `hardy (f t) t ≤ hardy (f t) (t+1)` step before recursing.

`ord_canonStep`, `ord_leaf`, `ord_NF`, `Hydra`, `canonStep`, `battle`, `Hydra.leaf` are all from the
external package `LeanGallery.Logic.Hydra.Canonical`
(`.lake/packages/LeanGallery/LeanGallery/Logic/Hydra/Canonical.lean`) — **UNVERIFIED / not opened**;
their exact statements were not read for this inventory since item 3 named only the two GoodsteinPA
files. If a PH proof follows the same "battle is alive / witness exceeds bound" pattern, this
external file (and the `ord : Hydra → ONote` assignment + `ord_canonStep`'s trichotomy) is the model
to imitate — but the PH object won't be a `Hydra` at all (see §4.4), so probably only the *shape* of
the induction (§4.1's proof sketch above) transfers, not the identifiers.

### 4.2 `HydraEscape.lean` (187 lines) — full content, the "arbitrarily large witnesses" composition

Namespace `GoodsteinPA.Hydra`, imports `HydraLowerBound`, `HydraIndependence`, `Domination`. Module
doc: *"For each `o < ε₀` we exhibit arbitrarily large codes `m` whose canonical battle is still
alive at every step `N ≤ f_o(m)`. The witness is `padded P k`: `k` single heads next to the hydra of
`ω^P + ω^3`, `P = o + 4` (`osucc` four times). The heads go first, so the battle outlasts `hardy
(ω^P + ω^3) k = hardy (ω^P) (hardy (ω^3) k)`; the code grows by one squaring per head, so it stays
below `f_3(k) ≤ hardy (ω^3) k`; and `f_o < f_P ≤ hardy (ω^P)` finishes the comparison."*

Section 1 — CNF-to-hydra encoding (`kids`, `ord_kids`, `iterate_insertTerm_top`,
`iterate_insertTerm_zero_NF`) and the key **argument-shift lemma**:
```
/-- Each extra head shifts the Hardy argument by one. -/
theorem hardy_iterate_insertTerm_zero (β : ONote) [β.NF] :
    ∀ (k t : ℕ), hardy ((insertTerm 0)^[k] β) t = hardy β (t + k)                          -- 70-80
```
(proved by induction on `k` via `hardy_succ _ (fundamentalSequence_insertTerm_zero …)` — note
`fundamentalSequence_insertTerm_zero` is another external `LeanGallery` lemma, **UNVERIFIED / not
opened**).

Section 2 — code-growth combinatorics (`pair_zero_bounds`, `toCode_padded`): "each extra head
squares the code (plus change), and adds at least one" — pure `ℕ` arithmetic, no ordinal content.

Section 3 — the escape itself:
```
theorem fastGrowing_lt_osucc {o : ONote} (ho : o.NF) {x : ℕ} (hx : 2 ≤ x) :
    fastGrowing o x < fastGrowing (osucc o) x :=
  fastGrowing_lt_succ_index (fundamentalSequence_osucc ho) hx                              -- 112
```

**`escapes` — the P3 lower-bound theorem, full walkthrough** (`HydraEscape.lean:118-172`):
```
theorem escapes : Escapes := by
  intro o ho M
  -- P := osucc (osucc (osucc (osucc o)))   (o bumped up by 4 notation-successors)
  -- hchain : ∀ x, 2 ≤ x → fastGrowing o x < fastGrowing P x     (chain fastGrowing_lt_osucc ×4)
  -- γ := oadd P 1 0 + oadd (ofNat 3) 1 0   (= ω^P + ω^3, NF, non-absorbing: 3 < P since P ≥ o+4)
  -- hcomp : ∀ x, hardy γ x = hardy (oadd P 1 0) (hardy (oadd (ofNat 3) 1 0) x)
  --   := hardy_add_comp _ hωP _ hδ (Or.inr hcond)          -- THE composition step
  -- k := M + toCode (node (kids γ)) + 4  (a sufficiently large head-count)
  -- Hk := node (List.replicate k leaf ++ kids γ)   (k extra heads in front of the hydra of γ)
  -- goal reduces (via runFrom_alive_of_lt_hardy) to:
  --   N ≤ hardy γ (toCode Hk)   for every N ≤ fastGrowing o (toCode Hk)
  -- chain:
  --   N ≤ fastGrowing o (toCode Hk)
  --     < fastGrowing P (toCode Hk)                         -- hchain
  --     ≤ hardy (oadd P 1 0) (toCode Hk)                     -- fastGrowing_le_hardy_omega_pow P _
  --     ≤ hardy (oadd P 1 0) (hardy (oadd (ofNat 3) 1 0) k)  -- hardy_monotone _ hcode
  --   and toCode Hk ≤ hardy (oadd (ofNat 3) 1 0) k because
  --     toCode Hk ≤ (C+2)^(2^k) ≤ (2^k)^(2^k) = 2^(2^k·k)
  --       ≤ fastGrowing (ofNat 3) k                          -- GoodsteinPA.Dom.two_pow_le_fastGrowing_ofNat_three
  --       ≤ hardy (oadd (ofNat 3) 1 0) k                      -- fastGrowing_le_hardy_omega_pow _ k
```
The three named `GoodsteinPA.FastGrowing` lemmas doing all the ordinal-comparison work in this proof
are exactly `hardy_add_comp` (§2.7), `fastGrowing_le_hardy_omega_pow` (§2.9), and `hardy_monotone`
(§2.6) — plus `fastGrowing_lt_succ_index`/`osucc` (§2.2/2.4) for the `o → P` bump and
`hardy_iterate_insertTerm_zero`/`runFrom_alive_of_lt_hardy` for the hydra-specific wiring. **This is
the template**: bump the target ordinal by a fixed finite amount to clear a "budget" side condition,
build a single `oadd`/`+`-composite ordinal whose two pieces are non-absorbing, convert `hardy` of
the sum to a composition via `hardy_add_comp`, and squeeze the actual combinatorial witness (here, a
hydra code) between `fastGrowing` at the bumped ordinal (upper) and `hardy` at a small fixed ordinal
(lower, to control the witness's own growth against the padding).

`GoodsteinPA.Dom.two_pow_le_fastGrowing_ofNat_three` (from `Domination.lean`) — **UNVERIFIED / not
opened**, but used exactly once, to convert an explicit `2^(2^k·k)` bound into a `fastGrowing
(ofNat 3) k` bound; the analogous step for a PH proof will need whatever elementary-recursive
witness-growth bound the PH combinatorics itself produces (Ramsey-type bounds are typically doubly
or iteratively exponential, so an `ofNat`-level or small-`ω^k`-level anchor like this is plausible
"connective tissue").

Section "Headline" (`HydraEscape.lean:174-185`) discharges the actual independence result from
`escapes`:
```
theorem pa_not_proves_hydra
    (φ : Semisentence ℒₒᵣ 2) (hφ : Arithmetic.Hierarchy 𝚺 1 φ)
    (hdef : ∀ m N : ℕ, (ℕ ⊧/![N, m] φ) ↔ battle (ofCode m) N = Hydra.leaf) :
    𝗣𝗔 ⊬ ↑(∀⁰ ∃⁰ φ : Sentence ℒₒᵣ) :=
  pa_not_proves_hydra_of_escape escapes φ hφ hdef
```

### 4.3 `HydraIndependence.lean` (48 lines) — the `Escapes` shape and its consumer

```
/-- The lower bound the grind must deliver: for every `o < ε₀` there are arbitrarily large codes
`m` whose canonical battle is still alive at every step `N ≤ f_o(m)`. -/
def Escapes : Prop :=
  ∀ o : ONote, o.NF → ∀ M : ℕ, ∃ m ≥ M, ∀ N ≤ fastGrowing o m, battle (ofCode m) N ≠ Hydra.leaf

/-- **The headline, modulo the lower bound.** -/
theorem pa_not_proves_hydra_of_escape (hesc : Escapes)
    (φ : Semisentence ℒₒᵣ 2) (hφ : Arithmetic.Hierarchy 𝚺 1 φ)
    (hdef : ∀ m N : ℕ, (ℕ ⊧/![N, m] φ) ↔ battle (ofCode m) N = Hydra.leaf) :
    𝗣𝗔 ⊬ ↑(∀⁰ ∃⁰ φ : Sentence ℒₒᵣ) := by
  intro h
  obtain ⟨o, ho, M, hM⟩ :=
    GoodsteinPA.Wainer.pa_provable_pi2_eventually_witnessed_below_fastGrowing φ hφ h
  obtain ⟨m, hm, hlive⟩ := hesc o ho M
  obtain ⟨N, hN, hsem⟩ := hM m hm
  exact hlive N hN ((hdef m N).mp hsem)
```
`GoodsteinPA.Wainer.pa_provable_pi2_eventually_witnessed_below_fastGrowing` (from
`WainerGeneral.lean`) — **UNVERIFIED / not opened in detail**; from its use here it is the "stage 1"
fact that any PA-provable `Π₂` statement's witness function is eventually bounded by some fixed
`fastGrowing o`. This is presumably shared, unmodified infrastructure a PH proof also calls (see
§4.4 — `PH.Independence` already calls the identical lemma).

### 4.4 The PH-side scaffold already in the repo — this is the actual target

`src/GoodsteinPA/PH/` (all four files small, all already present; git log shows this is an active
"stage 3" effort, most recent commits at HEAD: *"Stage 3: frozen headline target PH/Main.lean"*,
*"Stage 3: plan (Buchholz/Loebl–Nešetřil lower bound) + reduction to Escapes"*, *"Stage 3: infinite
Ramsey (all exponents) and the truth of Paris–Harrington"*, *"Stage 3 draft: Paris–Harrington
statement for ratification"*).

**`PH/Statement.lean`** (51 lines, full content read) defines the actual combinatorial object:
```
def RelLarge (H : Finset ℕ) : Prop := ∀ a ∈ H, (∀ b ∈ H, a ≤ b) → a ≤ H.card
def Homog {N e r : ℕ} (c : (Icc 1 N).powersetCard e → Fin r) (H : Finset ℕ) : Prop :=
  ∃ i : Fin r, ∀ (s : Finset ℕ) (hs : s ∈ (Icc 1 N).powersetCard e), s ⊆ H → c ⟨s, hs⟩ = i
def PH (e r k N : ℕ) : Prop :=
  ∀ c : (Icc 1 N).powersetCard e → Fin r,
    ∃ H ∈ (Icc 1 N).powerset, k ≤ H.card ∧ RelLarge H ∧ Homog c H
def PHx (x N : ℕ) : Prop := PH x.unpair.1 x.unpair.2.unpair.1 x.unpair.2.unpair.2 N
```

**`PH/Independence.lean`** (36 lines, full content read) — **the exact `Escapes` analogue**:
```
/-- The lower bound the grind must deliver. -/
def Escapes : Prop :=
  ∀ o : ONote, o.NF → ∀ M : ℕ, ∃ x ≥ M, ∀ N ≤ fastGrowing o x, ¬ PHx x N

theorem pa_not_proves_ph_of_escape (hesc : Escapes)
    (φ : Semisentence ℒₒᵣ 2) (hφ : Arithmetic.Hierarchy 𝚺 1 φ)
    (hdef : ∀ x N : ℕ, (ℕ ⊧/![N, x] φ) ↔ PHx x N) :
    𝗣𝗔 ⊬ ↑(∀⁰ ∃⁰ φ : Sentence ℒₒᵣ) := by
  intro h
  obtain ⟨o, ho, M, hM⟩ :=
    GoodsteinPA.Wainer.pa_provable_pi2_eventually_witnessed_below_fastGrowing φ hφ h
  obtain ⟨x, hx, hbad⟩ := hesc o ho M
  obtain ⟨N, hN, hsem⟩ := hM x hx
  exact hbad N hN ((hdef x N).mp hsem)
```
Compare directly to §4.3: **byte-for-byte the same architecture**, `battle (ofCode m) N ≠ leaf`
replaced by `¬ PHx x N`. This confirms exactly what a new `HydraEscape`-style file needs to prove:

```
GoodsteinPA.PH.Escapes  :=  ∀ o : ONote, o.NF → ∀ M : ℕ, ∃ x ≥ M, ∀ N ≤ fastGrowing o x, ¬ PHx x N
```
i.e. **for every ordinal notation `o`, arbitrarily large PH-inputs `x` whose PH property fails for
every `N` up to `fastGrowing o x`** — the direct PH counterpart of "arbitrarily large hydra codes
whose battle survives every step up to `fastGrowing o x`." The natural proof shape, by analogy with
§4.2's `escapes`, is: assign each `x` (or each witness structure) an ordinal via some `ord`-style
map into `ONote`, bound the growth of that assignment by a `hardy`/`fastGrowing` comparison
(`hardy_add_comp`, `fastGrowing_le_hardy_omega_pow`, `hardy_monotone`, `hardy_le_of_lt`,
`fastGrowing_le_of_lt` all being the reusable comparison lemmas from §2), and push a "budget bump"
through `osucc`/`+4` exactly as `HydraEscape.escapes` does for its own `P := osucc^[4] o`.

**`PH/Main.lean`** (35 lines, full content read) — the frozen headline (currently `sorry`):
```
theorem pa_not_proves_ph
    (φ : Semisentence ℒₒᵣ 2) (hφ : Arithmetic.Hierarchy 𝚺 1 φ)
    (hdef : ∀ x N : ℕ, (ℕ ⊧/![N, x] φ) ↔ PHx x N) :
    𝗣𝗔 ⊬ ↑(∀⁰ ∃⁰ φ : Sentence ℒₒᵣ) := sorry

theorem exists_sigma1_ph_def :
    ∃ φ : Semisentence ℒₒᵣ 2, Arithmetic.Hierarchy 𝚺 1 φ ∧
      ∀ x N : ℕ, (ℕ ⊧/![N, x] φ) ↔ PHx x N := sorry
```
Module doc: *"The two statements below are RATIFIED (Astra, 2026-09-26, in Trevor's place). Their
statements are frozen: do not weaken, generalise, or re-state them."*

`PH/Ramsey.lean` (85 lines), `PH/Truth.lean` (74 lines), `PH/Computable.lean` (93 lines) —
**UNVERIFIED / not opened in this pass** (out of the three explicitly-scoped items, but clearly
adjacent — `Ramsey.lean` almost certainly proves the ordinary (non-Paris–Harrington) infinite Ramsey
theorem the git log mentions, `Truth.lean` presumably the truth/model-theoretic side of `PHx`,
`Computable.lean` presumably decidability/computability of `PH`/`PHx`). Also present at the repo
root but **not opened**: `PH-BUCHHOLZ-SPEC.md`, `PH-TREADMILL.md`, `STAGE3-PH-PLAN.md`,
`ROADMAP-EPSILON0.md`, `drafts/PHDraft.lean` — these almost certainly contain the actual proof
strategy (git log references "Buchholz/Loebl–Nešetřil lower bound" and "reduction to Escapes"), and
should be read before starting the ordinal-descent proof itself; they were left unopened here to
keep this pass to the literal API-inventory scope requested.

---

## 5. Quick reference — theorems most likely to be reused directly

| Purpose | Lemma | Location |
|---|---|---|
| Index comparison, `fastGrowing` | `fastGrowing_le_of_lt` | Hardy.lean:889 |
| Index comparison, `hardy` | `hardy_le_of_lt` | Hardy.lean:1320 |
| Argument monotonicity, `hardy` | `hardy_monotone`, `hardy_le_succ` | Hardy.lean:1197,1227 |
| Successor/limit unfolding, `hardy` | `hardy_succ`, `hardy_limit` | Hardy.lean:1125,1130 |
| `H_{γ+δ} = H_γ∘H_δ` (non-absorbing) | `hardy_add_comp` | Hardy.lean:1639 |
| `H_{e+β} ≤ H_e∘H_β` (unconditional) | `hardy_add_le_comp` | Hardy.lean:1725 |
| `f_α(n) ≤ H_{ω^α}(n) < f_α(n+1)` | `hardy_omega_pow_bracket` | Hardy.lean:2105 |
| Notation successor (`+1` bump) | `osucc`, `osucc_NF`, `fundamentalSequence_osucc` | Hardy.lean:903,924,937 |
| Bump `fastGrowing` across `osucc` | `fastGrowing_lt_succ_index` | Hardy.lean:866 |
| CNF budget for reachability | `norm`, `reaches_of_lt` | Hardy.lean:635,836 |
| Diagonal tower / ε₀ domination | `tower`, `tower_cofinal`, `fastGrowing_lt_fastGrowingε₀` | Hardy.lean:961,995,1049 |
| The `Escapes` target shape | `GoodsteinPA.PH.Escapes` | PH/Independence.lean:22 |
| The escape-composition template | `GoodsteinPA.Hydra.escapes` | HydraEscape.lean:118 |
