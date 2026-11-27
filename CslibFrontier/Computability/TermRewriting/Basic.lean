module

public import Mathlib.ModelTheory.Syntax
public import Mathlib.Data.ENat.Lattice
public import Cslib.Foundations.Relation.RelatesInSteps
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Foundations of First-Order Term Rewriting and Derivation Height

This module provides textbook foundations for first-order term rewriting built directly on
Mathlib's `FirstOrder.Language.Term` and Cslib's `Relation.RelatesInSteps`, under standard Lean
axioms:
- **Term size, variables, positions, and replacement**: `termSize`, `vars`, `subtermAt`,
  `replaceAt`, and `IsPos`, together with the core position-algebra identities for prefix,
  parallel, appended, substituted, and language-mapped positions.
- **Rewrite rules and $\mathcal{Q}$-restricted relative rewriting**: `RewriteRule`, `RewriteStepAt`,
  `RewriteStep`, `IsNormalForm`, `QRewriteAt`, `QRewrite`, and `RelQRewrite`.
- **Step-counting derivations and derivation height**: `Derives` (tracking strict steps modulo weak
  steps) and `dheight` (derivation height in `ℕ∞`), together with monotonicity, simulation, and
  decreasing-measure bounds.

## Main definitions

- `CslibFrontier.Computability.TermRewriting.termSize`,
  `CslibFrontier.Computability.TermRewriting.vars`,
  `CslibFrontier.Computability.TermRewriting.subtermAt`,
  `CslibFrontier.Computability.TermRewriting.replaceAt`,
  `CslibFrontier.Computability.TermRewriting.IsPos`
- `CslibFrontier.Computability.TermRewriting.RewriteRule`,
  `CslibFrontier.Computability.TermRewriting.RewriteStepAt`,
  `CslibFrontier.Computability.TermRewriting.RewriteStep`,
  `CslibFrontier.Computability.TermRewriting.IsNormalForm`
- `CslibFrontier.Computability.TermRewriting.QRewriteAt`,
  `CslibFrontier.Computability.TermRewriting.QRewrite`,
  `CslibFrontier.Computability.TermRewriting.RelQRewrite`
- `CslibFrontier.Computability.TermRewriting.Derives`,
  `CslibFrontier.Computability.TermRewriting.dheight`

## Main results

- `CslibFrontier.Computability.TermRewriting.subtermAt_replaceAt_self`,
  `CslibFrontier.Computability.TermRewriting.subtermAt_replaceAt_of_parallel`,
  `CslibFrontier.Computability.TermRewriting.subtermAt_replaceAt_prefix`,
  `CslibFrontier.Computability.TermRewriting.subtermAt_replaceAt_append`,
  `CslibFrontier.Computability.TermRewriting.replaceAt_append`,
  `CslibFrontier.Computability.TermRewriting.replaceAt_subst`
- `CslibFrontier.Computability.TermRewriting.isNormalForm_of_subtermAt`,
  `CslibFrontier.Computability.TermRewriting.isNormalForm_subst_var_of_qRewriteAt`
- `CslibFrontier.Computability.TermRewriting.relatesInSteps_of_derives_pos`,
  `CslibFrontier.Computability.TermRewriting.derives_of_relatesInSteps`
- `CslibFrontier.Computability.TermRewriting.dheight_le_iff`,
  `CslibFrontier.Computability.TermRewriting.dheight_le_of_step_sim`,
  `CslibFrontier.Computability.TermRewriting.dheight_le_of_measure`
-/

public section

namespace CslibFrontier.Computability.TermRewriting

open FirstOrder FirstOrder.Language

universe u v w u' v' w'

section TermBasics

variable {L : FirstOrder.Language.{u, v}} {L' : FirstOrder.Language.{u', v'}}
variable {V : Type w} {W : Type w'}

/-- The symbol-count size of a first-order term (`|x| = 1`, `|f(t₁,…,tₙ)| = 1 + ∑ |tᵢ|`). -/
def termSize : L.Term V → ℕ
  | .var _ => 1
  | .func _ ts => 1 + ∑ i, termSize (ts i)

@[simp]
theorem termSize_var (x : V) : termSize (L := L) (.var x) = 1 := by
  simp [termSize]

@[simp]
theorem termSize_func {n : ℕ} (f : L.Functions n) (ts : Fin n → L.Term V) :
    termSize (.func f ts) = 1 + ∑ i, termSize (ts i) := by
  simp [termSize]

/-- Every first-order term has size at least `1`. -/
theorem one_le_termSize (t : L.Term V) : 1 ≤ termSize t := by
  cases t with
  | var _ => simp
  | func f ts => simp

/-- Every first-order term has strictly positive size. -/
theorem termSize_pos (t : L.Term V) : 0 < termSize t :=
  one_le_termSize t

/-- Mapping function symbols along a language homomorphism preserves term size. -/
@[simp]
theorem termSize_onTerm (φ : L →ᴸ L') (t : L.Term V) :
    termSize (φ.onTerm t) = termSize t := by
  induction t with
  | var _ => rfl
  | func f ts ih =>
    simp only [LHom.onTerm, termSize_func]
    congr 1
    exact Finset.sum_congr rfl fun i _ => ih i

/-- The set of variables occurring in a first-order term (decidability-free). -/
def vars : L.Term V → Set V
  | .var x => {x}
  | .func _ ts => ⋃ i, vars (ts i)

@[simp]
theorem vars_var (x : V) : vars (L := L) (.var x) = {x} := by
  simp [vars]

@[simp]
theorem vars_func {n : ℕ} (f : L.Functions n) (ts : Fin n → L.Term V) :
    vars (.func f ts) = ⋃ i, vars (ts i) := by
  simp [vars]

/-- A variable occurs in `t.subst σ` iff it occurs in `σ x` for some variable `x` of `t`. -/
theorem mem_vars_subst_iff (t : L.Term V) (σ : V → L.Term W) (y : W) :
    y ∈ vars (t.subst σ) ↔ ∃ x ∈ vars t, y ∈ vars (σ x) := by
  induction t with
  | var x => simp [Term.subst]
  | func f ts ih =>
    simp only [Term.subst, vars_func, Set.mem_iUnion, ih]
    constructor
    · rintro ⟨i, x, hx, hy⟩
      exact ⟨x, ⟨i, hx⟩, hy⟩
    · rintro ⟨x, ⟨i, hx⟩, hy⟩
      exact ⟨i, x, hx, hy⟩

/-- Two substitutions agreeing on `vars t` yield the same substituted term. -/
theorem subst_eq_of_eq_on_vars {t : L.Term V} {σ τ : V → L.Term W}
    (h : ∀ x ∈ vars t, σ x = τ x) : t.subst σ = t.subst τ := by
  induction t with
  | var x => exact h x (by simp)
  | func f ts ih =>
    simp only [Term.subst]
    congr 1
    funext i
    exact ih i fun x hx => h x (by rw [vars_func, Set.mem_iUnion]; exact ⟨i, hx⟩)

/-- Mapping function symbols along a language homomorphism preserves variables. -/
@[simp]
theorem vars_onTerm (φ : L →ᴸ L') (t : L.Term V) : vars (φ.onTerm t) = vars t := by
  induction t with
  | var _ => rfl
  | func f ts ih => simp [LHom.onTerm, ih]

/-- Language homomorphisms commute with term substitution. -/
theorem onTerm_subst (φ : L →ᴸ L') (t : L.Term V) (σ : V → L.Term W) :
    φ.onTerm (t.subst σ) = (φ.onTerm t).subst (fun x => φ.onTerm (σ x)) := by
  induction t with
  | var _ => rfl
  | func f ts ih =>
    simp only [Term.subst, LHom.onTerm]
    congr 1
    funext i
    exact ih i

/-- If `φ.onFunction` is injective at every arity, then `φ.onTerm` is injective. -/
theorem onTerm_injective (φ : L →ᴸ L')
    (hφ : ∀ {n : ℕ}, Function.Injective (φ.onFunction (n := n))) :
    Function.Injective (φ.onTerm (α := V)) := by
  intro s t h
  induction s generalizing t with
  | var x =>
    cases t with
    | var y => simpa [LHom.onTerm] using h
    | func g us => simp [LHom.onTerm] at h
  | func f ts ih =>
    cases t with
    | var y => simp [LHom.onTerm] at h
    | func g us =>
      simp only [LHom.onTerm, Term.func.injEq] at h
      obtain ⟨rfl, hfg, hts⟩ := h
      have hfg' : f = g := hφ (eq_of_heq hfg)
      subst hfg'
      congr 1
      funext i
      exact ih i (congrFun (eq_of_heq hts) i)

/-- The subterm of `t` at position `p : List ℕ`, or `none` if `p` is not a valid position of `t`. -/
def subtermAt : L.Term V → List ℕ → Option (L.Term V)
  | t, [] => some t
  | .var _, _ :: _ => none
  | .func (l := l) _ ts, i :: p =>
    if h : i < l then subtermAt (ts ⟨i, h⟩) p else none

@[simp]
theorem subtermAt_nil (t : L.Term V) : subtermAt t [] = some t := by
  cases t <;> simp [subtermAt]

@[simp]
theorem subtermAt_var_cons (x : V) (i : ℕ) (p : List ℕ) :
    subtermAt (L := L) (.var x) (i :: p) = none := by
  simp [subtermAt]

theorem subtermAt_func_cons {n : ℕ} (f : L.Functions n) (ts : Fin n → L.Term V)
    (i : ℕ) (p : List ℕ) :
    subtermAt (.func f ts) (i :: p) = if h : i < n then subtermAt (ts ⟨i, h⟩) p else none := by
  simp [subtermAt]

theorem subtermAt_func_cons_of_lt {n : ℕ} (f : L.Functions n) (ts : Fin n → L.Term V)
    {i : ℕ} (h : i < n) (p : List ℕ) :
    subtermAt (.func f ts) (i :: p) = subtermAt (ts ⟨i, h⟩) p := by
  simp [subtermAt, h]

theorem subtermAt_func_cons_of_not_lt {n : ℕ} (f : L.Functions n) (ts : Fin n → L.Term V)
    {i : ℕ} (h : ¬ i < n) (p : List ℕ) :
    subtermAt (.func f ts) (i :: p) = none := by
  simp [subtermAt, h]

/-- Replaces the subterm of `t` at position `p` with `u`, leaving `t` unchanged if `p` is
invalid. -/
def replaceAt : L.Term V → List ℕ → L.Term V → L.Term V
  | _, [], u => u
  | .var x, _ :: _, _ => .var x
  | .func (l := l) f ts, i :: p, u =>
    if h : i < l then
      .func f (Function.update ts ⟨i, h⟩ (replaceAt (ts ⟨i, h⟩) p u))
    else
      .func f ts

@[simp]
theorem replaceAt_nil (t u : L.Term V) : replaceAt t [] u = u := by
  cases t <;> simp [replaceAt]

@[simp]
theorem replaceAt_var_cons (x : V) (i : ℕ) (p : List ℕ) (u : L.Term V) :
    replaceAt (L := L) (.var x) (i :: p) u = .var x := by
  simp [replaceAt]

theorem replaceAt_func_cons_of_lt {n : ℕ} (f : L.Functions n) (ts : Fin n → L.Term V)
    {i : ℕ} (h : i < n) (p : List ℕ) (u : L.Term V) :
    replaceAt (.func f ts) (i :: p) u =
      .func f (Function.update ts ⟨i, h⟩ (replaceAt (ts ⟨i, h⟩) p u)) := by
  simp [replaceAt, h]

theorem replaceAt_func_cons_of_not_lt {n : ℕ} (f : L.Functions n) (ts : Fin n → L.Term V)
    {i : ℕ} (h : ¬ i < n) (p : List ℕ) (u : L.Term V) :
    replaceAt (.func f ts) (i :: p) u = .func f ts := by
  simp [replaceAt, h]

/-- Predicate asserting that `p : List ℕ` is a valid position in term `t`. -/
@[expose]
def IsPos (t : L.Term V) (p : List ℕ) : Prop :=
  (subtermAt t p).isSome

@[simp]
theorem isPos_nil (t : L.Term V) : IsPos t [] := by
  simp [IsPos]

theorem isPos_iff_exists_subtermAt (t : L.Term V) (p : List ℕ) :
    IsPos t p ↔ ∃ s, subtermAt t p = some s := by
  simp [IsPos, Option.isSome_iff_exists]

/-- Subterm lookup distributes over position concatenation. -/
theorem subtermAt_append (t : L.Term V) (p q : List ℕ) :
    subtermAt t (p ++ q) = (subtermAt t p).bind (fun s => subtermAt s q) := by
  induction p generalizing t with
  | nil => simp
  | cons i p ih =>
    cases t with
    | var _ => simp
    | @func n f ts =>
      by_cases h : i < n
      · simp [subtermAt, h, ih]
      · simp [subtermAt, h]

/-- Valid positions are closed under prefixes. -/
theorem isPos_of_prefix {t : L.Term V} {p q : List ℕ} (h : q <+: p) (hp : IsPos t p) :
    IsPos t q := by
  obtain ⟨r, rfl⟩ := h
  rw [isPos_iff_exists_subtermAt] at hp ⊢
  obtain ⟨s, hs⟩ := hp
  rw [subtermAt_append] at hs
  cases hq : subtermAt t q with
  | none => simp [hq] at hs
  | some u => exact ⟨u, rfl⟩

/-- Replacing at a valid position `p` places `u` at `p`. -/
theorem subtermAt_replaceAt_self {t u : L.Term V} {p : List ℕ} (hp : IsPos t p) :
    subtermAt (replaceAt t p u) p = some u := by
  induction p generalizing t with
  | nil => simp
  | cons i p ih =>
    cases t with
    | var _ => simp [IsPos] at hp
    | @func n f ts =>
      simp only [IsPos, subtermAt] at hp
      by_cases h : i < n
      · simp only [h, ↓reduceDIte] at hp
        simp [replaceAt, subtermAt, h, ih hp]
      · simp [h] at hp

/-- Replacing at `p` does not change subterms at any position parallel to `p`. -/
theorem subtermAt_replaceAt_of_parallel {t u : L.Term V} {p q : List ℕ}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) :
    subtermAt (replaceAt t p u) q = subtermAt t q := by
  induction p generalizing t q with
  | nil => exact absurd (List.nil_prefix) hpq
  | cons i p ih =>
    cases q with
    | nil => exact absurd (List.nil_prefix) hqp
    | cons j q =>
      cases t with
      | var _ => simp
      | @func n f ts =>
        by_cases hi : i < n
        · by_cases hj : j < n
          · by_cases hij : i = j
            · subst hij
              have hpq' : ¬ p <+: q := fun h => hpq (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
              have hqp' : ¬ q <+: p := fun h => hqp (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
              simp [replaceAt, subtermAt, hi, ih hpq' hqp']
            · have hne : (⟨j, hj⟩ : Fin n) ≠ ⟨i, hi⟩ := by
                intro heq
                exact hij (congrArg Fin.val heq).symm
              simp [replaceAt, subtermAt, hi, hj, Function.update_of_ne hne]
          · simp [replaceAt, subtermAt, hi, hj]
        · simp [replaceAt, hi]

/-- Looking up at a prefix `q` of `p` after replacing at `p` yields the inner replacement. -/
theorem subtermAt_replaceAt_prefix {t u : L.Term V} {p q : List ℕ} (h : q <+: p) :
    subtermAt (replaceAt t p u) q =
      (subtermAt t q).map (fun s => replaceAt s (p.drop q.length) u) := by
  obtain ⟨r, rfl⟩ := h
  induction q generalizing t with
  | nil => simp
  | cons j q ih =>
    cases t with
    | var _ => simp
    | @func n f ts =>
      by_cases hj : j < n
      · simp [replaceAt, subtermAt, hj, ih]
      · simp [replaceAt, subtermAt, hj]

/-- Looking up at `p ++ q` after replacing at a valid position `p` looks up `q` in `u`. -/
theorem subtermAt_replaceAt_append {t u : L.Term V} {p : List ℕ} (hp : IsPos t p) (q : List ℕ) :
    subtermAt (replaceAt t p u) (p ++ q) = subtermAt u q := by
  rw [subtermAt_append, subtermAt_replaceAt_self hp]
  rfl

/-- Replacing a subterm by itself leaves the term unchanged. -/
theorem replaceAt_subtermAt_eq {t s : L.Term V} {p : List ℕ} (hs : subtermAt t p = some s) :
    replaceAt t p s = t := by
  induction p generalizing t with
  | nil =>
    simp only [subtermAt_nil, Option.some.injEq] at hs
    rw [replaceAt_nil, hs]
  | cons i p ih =>
    cases t with
    | var _ => simp at hs
    | @func n f ts =>
      simp only [subtermAt] at hs
      by_cases h : i < n
      · simp only [h, ↓reduceDIte] at hs
        simp [replaceAt, h, ih hs]
      · simp [h] at hs

/-- Replacing at `p` followed by replacing at `p` keeps only the second replacement. -/
theorem replaceAt_replaceAt_self {t u v : L.Term V} {p : List ℕ} (hp : IsPos t p) :
    replaceAt (replaceAt t p u) p v = replaceAt t p v := by
  induction p generalizing t with
  | nil => simp
  | cons i p ih =>
    cases t with
    | var _ => simp [IsPos] at hp
    | @func n f ts =>
      simp only [IsPos, subtermAt] at hp
      by_cases h : i < n
      · simp only [h, ↓reduceDIte] at hp
        simp [replaceAt, h, ih hp]
      · simp [h] at hp

/-- Replacing at an appended position `p ++ q` decomposes into two nested replacements. -/
theorem replaceAt_append {t s u : L.Term V} {p : List ℕ} (q : List ℕ)
    (hs : subtermAt t p = some s) :
    replaceAt t (p ++ q) u = replaceAt t p (replaceAt s q u) := by
  induction p generalizing t with
  | nil =>
    simp only [subtermAt_nil, Option.some.injEq] at hs
    subst hs
    simp
  | cons i p ih =>
    cases t with
    | var _ => simp at hs
    | @func n f ts =>
      simp only [subtermAt] at hs
      by_cases h : i < n
      · simp only [h, ↓reduceDIte] at hs
        simp [replaceAt, h, ih hs]
      · simp [h] at hs

/-- Replacements at parallel positions commute. -/
theorem replaceAt_comm {t u v : L.Term V} {p q : List ℕ}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) :
    replaceAt (replaceAt t p u) q v = replaceAt (replaceAt t q v) p u := by
  induction p generalizing t q with
  | nil => exact absurd (List.nil_prefix) hpq
  | cons i p ih =>
    cases q with
    | nil => exact absurd (List.nil_prefix) hqp
    | cons j q =>
      cases t with
      | var _ => simp
      | @func n f ts =>
        by_cases hi : i < n
        · by_cases hj : j < n
          · by_cases hij : i = j
            · subst hij
              have hpq' : ¬ p <+: q := fun h => hpq (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
              have hqp' : ¬ q <+: p := fun h => hqp (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
              simp [replaceAt, hi, ih hpq' hqp']
            · have hne : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := by
                intro heq
                exact hij (congrArg Fin.val heq)
              simp [replaceAt, hi, hj, Function.update_of_ne hne, Function.update_of_ne hne.symm,
                Function.update_comm hne]
          · simp [replaceAt, hi, hj]
        · by_cases hj : j < n <;> simp [replaceAt, hi, hj]

/-- Substitution commutes with looking up a valid subterm position. -/
theorem subtermAt_subst_of_subtermAt_eq {t s : L.Term V} {p : List ℕ} (σ : V → L.Term W)
    (hs : subtermAt t p = some s) :
    subtermAt (t.subst σ) p = some (s.subst σ) := by
  induction p generalizing t with
  | nil =>
    simp at hs
    simp [hs]
  | cons i p ih =>
    cases t with
    | var _ => simp at hs
    | @func n f ts =>
      simp only [subtermAt] at hs
      by_cases h : i < n
      · simp only [h, ↓reduceDIte] at hs
        simp [Term.subst, subtermAt, h, ih hs]
      · simp [h] at hs

/-- Substitution commutes with replacement at a valid position. -/
theorem replaceAt_subst {t u : L.Term V} {p : List ℕ} (σ : V → L.Term W) (hp : IsPos t p) :
    (replaceAt t p u).subst σ = replaceAt (t.subst σ) p (u.subst σ) := by
  induction p generalizing t with
  | nil => simp
  | cons i p ih =>
    cases t with
    | var _ => simp [IsPos] at hp
    | @func n f ts =>
      simp only [IsPos, subtermAt] at hp
      by_cases h : i < n
      · simp only [h, ↓reduceDIte] at hp
        simp only [replaceAt, h, ↓reduceDIte, Term.subst, Term.func.injEq, heq_eq_eq, true_and]
        funext j
        by_cases hj : j = ⟨i, h⟩
        · subst hj
          simp [ih hp]
        · simp [hj]
      · simp [h] at hp

/-- Language homomorphisms commute with `subtermAt`. -/
theorem subtermAt_onTerm (φ : L →ᴸ L') (t : L.Term V) (p : List ℕ) :
    subtermAt (φ.onTerm t) p = (subtermAt t p).map φ.onTerm := by
  induction p generalizing t with
  | nil => simp
  | cons i p ih =>
    cases t with
    | var _ => simp
    | @func n f ts =>
      by_cases h : i < n
      · simp [LHom.onTerm, subtermAt, h, ih]
      · simp [LHom.onTerm, subtermAt, h]

/-- Language homomorphisms commute with `replaceAt`. -/
theorem replaceAt_onTerm (φ : L →ᴸ L') (t u : L.Term V) (p : List ℕ) :
    replaceAt (φ.onTerm t) p (φ.onTerm u) = φ.onTerm (replaceAt t p u) := by
  induction p generalizing t with
  | nil => simp
  | cons i p ih =>
    cases t with
    | var _ => simp
    | @func n f ts =>
      by_cases h : i < n
      · simp only [LHom.onTerm, replaceAt, h, ↓reduceDIte, Term.func.injEq, heq_eq_eq, true_and]
        funext j
        by_cases hj : j = ⟨i, h⟩
        · subst hj
          simp [ih]
        · simp [hj]
      · simp [LHom.onTerm, replaceAt, h]

/-- Variables of any subterm are contained in the variables of the ambient term. -/
theorem mem_vars_of_subtermAt {t s : L.Term V} {p : List ℕ} (hs : subtermAt t p = some s) :
    vars s ⊆ vars t := by
  induction p generalizing t with
  | nil =>
    simp at hs
    simp [hs]
  | cons i p ih =>
    cases t with
    | var _ => simp at hs
    | @func n f ts =>
      simp only [subtermAt] at hs
      by_cases h : i < n
      · simp only [h, ↓reduceDIte] at hs
        intro x hx
        simp only [vars_func, Set.mem_iUnion]
        exact ⟨⟨i, h⟩, ih hs hx⟩
      · simp [h] at hs

/-- Variables of a replaced term lie in `vars t ∪ vars u`. -/
theorem vars_replaceAt_subset (t u : L.Term V) (p : List ℕ) :
    vars (replaceAt t p u) ⊆ vars t ∪ vars u := by
  induction p generalizing t with
  | nil =>
    intro x hx
    rw [replaceAt_nil] at hx
    exact Or.inr hx
  | cons i p ih =>
    cases t with
    | var y =>
      intro x hx
      rw [replaceAt_var_cons] at hx
      exact Or.inl hx
    | @func n f ts =>
      by_cases h : i < n
      · intro x hx
        simp only [replaceAt, h, ↓reduceDIte, vars_func, Set.mem_iUnion] at hx
        obtain ⟨j, hj⟩ := hx
        by_cases hji : j = ⟨i, h⟩
        · subst hji
          simp only [Function.update_self] at hj
          rcases ih (ts ⟨i, h⟩) hj with h1 | h2
          · left
            simp only [vars_func, Set.mem_iUnion]
            exact ⟨⟨i, h⟩, h1⟩
          · exact Or.inr h2
        · simp only [Function.update_of_ne hji] at hj
          left
          simp only [vars_func, Set.mem_iUnion]
          exact ⟨j, hj⟩
      · intro x hx
        simp only [replaceAt, h, ↓reduceDIte] at hx
        exact Or.inl hx

/-- If `t` is not a variable and `x ∈ vars t`, then `σ x` is a proper subterm of `t.subst σ`. -/
theorem exists_proper_subtermAt_subst_of_mem_vars {t : L.Term V} {x : V} (σ : V → L.Term W)
    (hnotvar : ∀ y, t ≠ .var y) (hx : x ∈ vars t) :
    ∃ p, p ≠ [] ∧ subtermAt (t.subst σ) p = some (σ x) := by
  cases t with
  | var y => exact absurd rfl (hnotvar y)
  | func f ts =>
    simp only [vars_func, Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    have hsub : ∀ (s : L.Term V), x ∈ vars s → ∃ q, subtermAt (s.subst σ) q = some (σ x) := by
      intro s hs
      induction s with
      | var y =>
        simp only [vars_var, Set.mem_singleton_iff] at hs
        subst hs
        exact ⟨[], by simp⟩
      | func g us ih =>
        simp only [vars_func, Set.mem_iUnion] at hs
        obtain ⟨j, hj⟩ := hs
        obtain ⟨q, hq⟩ := ih j hj
        exact ⟨j.val :: q, by simp [Term.subst, subtermAt, j.isLt, hq]⟩
    obtain ⟨q, hq⟩ := hsub (ts i) hi
    exact ⟨i.val :: q, List.cons_ne_nil _ _, by simp [Term.subst, subtermAt, i.isLt, hq]⟩

end TermBasics

section Rewriting

variable {L : FirstOrder.Language.{u, v}} {L' : FirstOrder.Language.{u', v'}}
variable {V : Type w}

/-- A first-order rewrite rule `lhs → rhs` with non-variable LHS and `vars rhs ⊆ vars lhs`. -/
@[ext]
structure RewriteRule (L : FirstOrder.Language.{u, v}) (V : Type w) where
  /-- The left-hand side of the rewrite rule. -/
  lhs : L.Term V
  /-- The right-hand side of the rewrite rule. -/
  rhs : L.Term V
  /-- Standard TRS condition: the left-hand side is not a variable. -/
  lhs_not_var : ∀ x, lhs ≠ .var x
  /-- Standard TRS condition: every variable in the right-hand side occurs in the left-hand side. -/
  vars_subset : ∀ x, x ∈ vars rhs → x ∈ vars lhs

/-- Maps a rewrite rule along a language homomorphism. -/
@[expose]
def RewriteRule.map (φ : L →ᴸ L') (rule : RewriteRule L V) : RewriteRule L' V where
  lhs := φ.onTerm rule.lhs
  rhs := φ.onTerm rule.rhs
  lhs_not_var x h := by
    cases hrule : rule.lhs with
    | var y => exact rule.lhs_not_var y hrule
    | func f ts =>
      rw [hrule] at h
      simp [LHom.onTerm] at h
  vars_subset x hx := by
    rw [vars_onTerm] at hx ⊢
    exact rule.vars_subset x hx

/-- A full rewrite step using `R` at position `p`. -/
@[expose]
def RewriteStepAt (R : Set (RewriteRule L V)) (p : List ℕ) (s t : L.Term V) : Prop :=
  ∃ rule ∈ R, ∃ σ : V → L.Term V,
    subtermAt s p = some (rule.lhs.subst σ) ∧ t = replaceAt s p (rule.rhs.subst σ)

/-- Full term rewriting `s →_R t` (at some position). -/
@[expose]
def RewriteStep (R : Set (RewriteRule L V)) (s t : L.Term V) : Prop :=
  ∃ p, RewriteStepAt R p s t

/-- A term `t` is an `R`-normal form (`t ∈ NF(R)`) if no `R`-rewrite step starts at `t`. -/
@[expose]
def IsNormalForm (R : Set (RewriteRule L V)) (t : L.Term V) : Prop :=
  ∀ u, ¬ RewriteStep R t u

/-- Every subterm of an `R`-normal form is an `R`-normal form. -/
theorem isNormalForm_of_subtermAt {R : Set (RewriteRule L V)} {t s : L.Term V} {p : List ℕ}
    (ht : IsNormalForm R t) (hs : subtermAt t p = some s) :
    IsNormalForm R s := by
  rintro u ⟨q, rule, hmem, σ, hsub, rfl⟩
  apply ht (replaceAt t (p ++ q) (rule.rhs.subst σ))
  refine ⟨p ++ q, rule, hmem, σ, ?_, rfl⟩
  rw [subtermAt_append, hs]
  exact hsub

/-- Every term is a normal form of the empty TRS. -/
theorem isNormalForm_empty (t : L.Term V) : IsNormalForm (∅ : Set (RewriteRule L V)) t := by
  rintro u ⟨p, rule, hmem, _⟩
  exact hmem

/-- A `Q`-restricted rewrite step using `R` at position `p`: the redex matches `rule.lhs.subst σ`
at `p`, and every proper subterm of the redex is in `NF(Q)`. -/
@[expose]
def QRewriteAt (Q R : Set (RewriteRule L V)) (p : List ℕ) (s t : L.Term V) : Prop :=
  ∃ rule ∈ R, ∃ σ : V → L.Term V,
    subtermAt s p = some (rule.lhs.subst σ) ∧
    t = replaceAt s p (rule.rhs.subst σ) ∧
    ∀ q, q ≠ [] → ∀ u, subtermAt (rule.lhs.subst σ) q = some u → IsNormalForm Q u

/-- `Q`-restricted rewriting `s →_{Q, R} t`. -/
@[expose]
def QRewrite (Q R : Set (RewriteRule L V)) (s t : L.Term V) : Prop :=
  ∃ p, QRewriteAt Q R p s t

/-- Relative `Q`-restricted rewriting `s →_{Q, S/W} t`: zero or more `W`-steps, one `S`-step,
and zero or more `W`-steps. -/
@[expose]
def RelQRewrite (Q S W : Set (RewriteRule L V)) (s t : L.Term V) : Prop :=
  ∃ u v, Relation.ReflTransGen (QRewrite Q W) s u ∧
    QRewrite Q S u v ∧
    Relation.ReflTransGen (QRewrite Q W) v t

/-- Every `Q`-restricted rewrite step at `p` is a full rewrite step at `p`. -/
theorem qRewriteAt_imp_rewriteStepAt {Q R : Set (RewriteRule L V)} {p : List ℕ} {s t : L.Term V}
    (h : QRewriteAt Q R p s t) : RewriteStepAt R p s t := by
  obtain ⟨rule, hmem, σ, hsub, ht, _⟩ := h
  exact ⟨rule, hmem, σ, hsub, ht⟩

/-- Every `Q`-restricted rewrite step is a full rewrite step. -/
theorem qRewrite_imp_rewriteStep {Q R : Set (RewriteRule L V)} {s t : L.Term V}
    (h : QRewrite Q R s t) : RewriteStep R s t := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, qRewriteAt_imp_rewriteStepAt hp⟩

/-- `Q`-restricted rewriting is monotone in `R` and antimonotone in `Q`. -/
theorem qRewriteAt_mono {Q₁ Q₂ R₁ R₂ : Set (RewriteRule L V)} {p : List ℕ} {s t : L.Term V}
    (hQ : Q₂ ⊆ Q₁) (hR : R₁ ⊆ R₂) (h : QRewriteAt Q₁ R₁ p s t) :
    QRewriteAt Q₂ R₂ p s t := by
  obtain ⟨rule, hmem, σ, hsub, ht, hnf⟩ := h
  refine ⟨rule, hR hmem, σ, hsub, ht, fun q hq u hu => ?_⟩
  intro v ⟨r, r_rule, hr_mem, τ, hsub', hv⟩
  exact hnf q hq u hu v ⟨r, r_rule, hQ hr_mem, τ, hsub', hv⟩

/-- `Q`-restricted rewriting is monotone in `R` and antimonotone in `Q`. -/
theorem qRewrite_mono {Q₁ Q₂ R₁ R₂ : Set (RewriteRule L V)} {s t : L.Term V}
    (hQ : Q₂ ⊆ Q₁) (hR : R₁ ⊆ R₂) (h : QRewrite Q₁ R₁ s t) :
    QRewrite Q₂ R₂ s t := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, qRewriteAt_mono hQ hR hp⟩

/-- `Q`-restricted rewriting distributes over unions of rule sets. -/
theorem qRewrite_union_iff {Q R₁ R₂ : Set (RewriteRule L V)} {s t : L.Term V} :
    QRewrite Q (R₁ ∪ R₂) s t ↔ QRewrite Q R₁ s t ∨ QRewrite Q R₂ s t := by
  constructor
  · rintro ⟨p, rule, hmem | hmem, σ, hsub, ht, hnf⟩
    · exact Or.inl ⟨p, rule, hmem, σ, hsub, ht, hnf⟩
    · exact Or.inr ⟨p, rule, hmem, σ, hsub, ht, hnf⟩
  · rintro (h | h)
    · exact qRewrite_mono subset_rfl Set.subset_union_left h
    · exact qRewrite_mono subset_rfl Set.subset_union_right h

/-- No `Q`-restricted rewrite step exists for the empty TRS. -/
theorem not_qRewrite_empty (Q : Set (RewriteRule L V)) (s t : L.Term V) :
    ¬ QRewrite Q ∅ s t := by
  rintro ⟨_, _, hmem, _⟩
  exact hmem

/-- No relative `Q`-restricted rewrite step exists when the strict component is empty. -/
theorem not_relQRewrite_empty (Q W : Set (RewriteRule L V)) (s t : L.Term V) :
    ¬ RelQRewrite Q ∅ W s t := by
  rintro ⟨_, _, _, hS, _⟩
  exact not_qRewrite_empty Q _ _ hS

/-- Relative `Q`-restricted rewriting is monotone in both `S` and `W`. -/
theorem relQRewrite_mono {Q S₁ S₂ W₁ W₂ : Set (RewriteRule L V)} {s t : L.Term V}
    (hS : S₁ ⊆ S₂) (hW : W₁ ⊆ W₂) (h : RelQRewrite Q S₁ W₁ s t) :
    RelQRewrite Q S₂ W₂ s t := by
  obtain ⟨u, v, h1, h2, h3⟩ := h
  exact ⟨u, v,
    Relation.ReflTransGen.mono (fun _ _ => qRewrite_mono subset_rfl hW) _ _ h1,
    qRewrite_mono subset_rfl hS h2,
    Relation.ReflTransGen.mono (fun _ _ => qRewrite_mono subset_rfl hW) _ _ h3⟩

/-- Context closure of `Q`-restricted rewriting: a step inside a subterm lifts to the ambient
term. -/
theorem qRewriteAt_context {Q R : Set (RewriteRule L V)} {s u v : L.Term V} {q p : List ℕ}
    (hs : subtermAt s q = some u) (h : QRewriteAt Q R p u v) :
    QRewriteAt Q R (q ++ p) s (replaceAt s q v) := by
  obtain ⟨rule, hmem, σ, hsub, rfl, hnf⟩ := h
  refine ⟨rule, hmem, σ, ?_, ?_, hnf⟩
  · rw [subtermAt_append, hs]
    exact hsub
  · rw [replaceAt_append p hs]

/-- If `s →_{Q, R, p} t` is witnessed by `rule` and `σ`, then `σ x` is in `NF(Q)` for every
variable `x` occurring in `rule.rhs`. -/
theorem isNormalForm_subst_var_of_qRewriteAt {Q : Set (RewriteRule L V)}
    {rule : RewriteRule L V} {σ : V → L.Term V} {x : V}
    (hnf : ∀ q, q ≠ [] → ∀ u, subtermAt (rule.lhs.subst σ) q = some u → IsNormalForm Q u)
    (hx : x ∈ vars rule.rhs) :
    IsNormalForm Q (σ x) := by
  obtain ⟨q, hq, hsub⟩ :=
    exists_proper_subtermAt_subst_of_mem_vars σ rule.lhs_not_var (rule.vars_subset x hx)
  exact hnf q hq (σ x) hsub

/-- Context closure for full `Q`-restricted rewriting under a single function-symbol step. -/
theorem qRewrite_func_update {Q R : Set (RewriteRule L V)} {n : ℕ} (f : L.Functions n)
    (ts : Fin n → L.Term V) (i : Fin n) {v : L.Term V} (h : QRewrite Q R (ts i) v) :
    QRewrite Q R (.func f ts) (.func f (Function.update ts i v)) := by
  obtain ⟨p, hp⟩ := h
  have hsub : subtermAt (.func f ts) [i.val] = some (ts i) := by
    simp [subtermAt, i.isLt]
  have hctx := qRewriteAt_context hsub hp
  refine ⟨[i.val] ++ p, ?_⟩
  simpa [replaceAt, i.isLt] using hctx

/-- Context closure for reflexive-transitive `Q`-restricted rewriting under a function symbol. -/
theorem reflTransGen_qRewrite_func_update {Q R : Set (RewriteRule L V)} {n : ℕ}
    (f : L.Functions n) (ts : Fin n → L.Term V) (i : Fin n) {v : L.Term V}
    (h : Relation.ReflTransGen (QRewrite Q R) (ts i) v) :
    Relation.ReflTransGen (QRewrite Q R) (.func f ts) (.func f (Function.update ts i v)) := by
  induction h with
  | refl =>
    rw [Function.update_eq_self]
  | @tail b c _ hstep ih =>
    apply Relation.ReflTransGen.tail ih
    have h' : QRewrite Q R ((Function.update ts i b) i) c := by simpa using hstep
    simpa [Function.update_idem] using qRewrite_func_update f (Function.update ts i b) i h'

/-- Context closure for relative `Q`-restricted rewriting under a function symbol. -/
theorem relQRewrite_func_update {Q S W : Set (RewriteRule L V)} {n : ℕ} (f : L.Functions n)
    (ts : Fin n → L.Term V) (i : Fin n) {v : L.Term V} (h : RelQRewrite Q S W (ts i) v) :
    RelQRewrite Q S W (.func f ts) (.func f (Function.update ts i v)) := by
  obtain ⟨a, b, h1, h2, h3⟩ := h
  refine ⟨.func f (Function.update ts i a), .func f (Function.update ts i b),
    reflTransGen_qRewrite_func_update f ts i h1, ?_, ?_⟩
  · have h2' : QRewrite Q S ((Function.update ts i a) i) b := by simpa using h2
    simpa [Function.update_idem] using qRewrite_func_update f (Function.update ts i a) i h2'
  · have h3' := reflTransGen_qRewrite_func_update f (Function.update ts i b) i (by simpa using h3)
    simpa [Function.update_idem] using h3'

end Rewriting

section DerivationHeight

variable {α : Type u}

/-- Step-counting relative derivations: `Derives W S a b k` holds iff `a` reaches `b` using
`W`-steps and exactly `k` `S`-steps. -/
inductive Derives (W S : α → α → Prop) : α → α → ℕ → Prop
  | refl (a : α) : Derives W S a a 0
  | weak {a b : α} (h : W a b) : Derives W S a b 0
  | strict {a b : α} (h : S a b) : Derives W S a b 1
  | trans {a b c : α} {m n : ℕ} (h₁ : Derives W S a b m) (h₂ : Derives W S b c n) :
      Derives W S a c (m + n)

/-- Reflexive-transitive weak closure embeds into `0`-step `Derives`. -/
theorem derives_zero_of_reflTransGen {W S : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen W a b) : Derives W S a b 0 := by
  induction h with
  | refl => exact .refl _
  | tail _ hstep ih => simpa using Derives.trans ih (.weak hstep)

/-- A `0`-step `Derives` derivation consists solely of weak steps. -/
theorem reflTransGen_of_derives_zero {W S : α → α → Prop} {a b : α}
    (h : Derives W S a b 0) : Relation.ReflTransGen W a b := by
  generalize hk : (0 : ℕ) = k at h
  induction h with
  | refl _ => exact .refl
  | weak hw => exact Relation.ReflTransGen.single hw
  | strict _ => exact absurd hk (by omega)
  | @trans _ _ _ m n h₁ h₂ ih₁ ih₂ =>
    have hm : m = 0 := by omega
    have hn : n = 0 := by omega
    exact (ih₁ hm.symm).trans (ih₂ hn.symm)

/-- The relative composition `W* ∘ S ∘ W*`. -/
@[expose]
def RelStep (W S : α → α → Prop) (a b : α) : Prop :=
  ∃ u v, Relation.ReflTransGen W a u ∧ S u v ∧ Relation.ReflTransGen W v b

/-- Every `k`-step `RelStep` derivation yields a `k`-step `Derives` derivation. -/
theorem derives_of_relatesInSteps {W S : α → α → Prop} {a b : α} {k : ℕ}
    (h : Relation.RelatesInSteps (RelStep W S) a b k) : Derives W S a b k := by
  induction h with
  | refl => exact .refl _
  | tail t' t'' _ _ hstep ih =>
    obtain ⟨u, v, h1, h2, h3⟩ := hstep
    have hstep' : Derives W S t' t'' 1 := by
      have hA := derives_zero_of_reflTransGen (S := S) h1
      have hB := Derives.strict (W := W) h2
      have hC := derives_zero_of_reflTransGen (S := S) h3
      simpa using Derives.trans (Derives.trans hA hB) hC
    exact Derives.trans ih hstep'

/-- Every `Derives` derivation with `k > 0` strict steps yields a `k`-step `RelStep` derivation. -/
theorem relatesInSteps_of_derives_pos {W S : α → α → Prop} {a b : α} {k : ℕ}
    (hk : 0 < k) (h : Derives W S a b k) :
    Relation.RelatesInSteps (RelStep W S) a b k := by
  induction h with
  | refl _ => omega
  | weak _ => omega
  | strict hs => exact .single ⟨_, _, .refl, hs, .refl⟩
  | @trans a b c m n h₁ h₂ ih₁ ih₂ =>
    by_cases hm : 0 < m
    · by_cases hn : 0 < n
      · exact (ih₁ hm).trans (ih₂ hn)
      · have hn0 : n = 0 := by omega
        subst hn0
        have hw : Relation.ReflTransGen W b c := reflTransGen_of_derives_zero h₂
        cases m with
        | zero => omega
        | succ m' =>
          obtain ⟨b', hpre, u, v, hu, hS, hv⟩ := (ih₁ hm).succ
          exact .tail _ _ _ _ hpre ⟨u, v, hu, hS, hv.trans hw⟩
    · have hm0 : m = 0 := by omega
      subst hm0
      have hn : 0 < n := by omega
      have hw : Relation.ReflTransGen W a b := reflTransGen_of_derives_zero h₁
      cases n with
      | zero => omega
      | succ n' =>
        obtain ⟨b', ⟨u, v, hu, hS, hv⟩, hpost⟩ := (ih₂ hn).succ'
        have hn' : 0 + (n' + 1) = n' + 1 := by omega
        rw [hn']
        exact .head _ _ _ _ ⟨u, v, hw.trans hu, hS, hv⟩ hpost

/-- Mapping `Derives` through a simulation that sends `W` to `W'` and `S` to `S'`. -/
theorem derives_map {β : Type v} {W S : α → α → Prop} {W' S' : β → β → Prop}
    (g : α → β) (hW : ∀ a b, W a b → W' (g a) (g b))
    (hS : ∀ a b, S a b → S' (g a) (g b)) {a b : α} {k : ℕ}
    (h : Derives W S a b k) : Derives W' S' (g a) (g b) k := by
  induction h with
  | refl a => exact .refl (g a)
  | weak hw => exact .weak (hW _ _ hw)
  | strict hs => exact .strict (hS _ _ hs)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- The derivation height `dh(a, r) ∈ ℕ∞` of `a` with respect to a binary relation `r`.
Returns `⊤` iff arbitrarily long `r`-derivations start at `a`. -/
noncomputable def dheight (r : α → α → Prop) (a : α) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ∃ b, Relation.RelatesInSteps r a b n), (n : ℕ∞)

/-- Every `n`-step `r`-derivation from `a` witnesses `n ≤ dheight r a`. -/
theorem le_dheight_of_relatesInSteps {r : α → α → Prop} {a b : α} {n : ℕ}
    (h : Relation.RelatesInSteps r a b n) : (n : ℕ∞) ≤ dheight r a :=
  le_iSup₂_of_le n ⟨b, h⟩ le_rfl

/-- Characterization of upper bounds on `dheight r a`. -/
theorem dheight_le_iff {r : α → α → Prop} {a : α} {k : ℕ∞} :
    dheight r a ≤ k ↔ ∀ n b, Relation.RelatesInSteps r a b n → (n : ℕ∞) ≤ k := by
  simp only [dheight, iSup_le_iff]
  constructor
  · intro h n b hb
    exact h n ⟨b, hb⟩
  · rintro h n ⟨b, hb⟩
    exact h n b hb

/-- Derivation height is monotone in the relation. -/
theorem dheight_mono_rel {r₁ r₂ : α → α → Prop} (h : ∀ x y, r₁ x y → r₂ x y) (a : α) :
    dheight r₁ a ≤ dheight r₂ a := by
  rw [dheight_le_iff]
  intro n b hb
  exact le_dheight_of_relatesInSteps (hb.map id h)

/-- An empty relation has derivation height `0` everywhere. -/
theorem dheight_eq_zero_of_empty {r : α → α → Prop} (h : ∀ x y, ¬ r x y) (a : α) :
    dheight r a = 0 := by
  apply le_antisymm _ zero_le
  rw [dheight_le_iff]
  intro n b hb
  cases hb with
  | refl => simp
  | tail _ _ _ _ hstep => exact absurd hstep (h _ _)

/-- Step-wise simulation implies inequality of derivation heights. -/
theorem dheight_le_of_step_sim {β : Type v} {r₁ : α → α → Prop} {r₂ : β → β → Prop}
    (Good : α → β → Prop)
    (hstep : ∀ s t u, r₁ s t → Good s u → ∃ v, r₂ u v ∧ Good t v)
    {s : α} {u : β} (hgood : Good s u) :
    dheight r₁ s ≤ dheight r₂ u := by
  rw [dheight_le_iff]
  intro n t hrel
  suffices ∀ (k : ℕ) (a b : α) (x : β), Relation.RelatesInSteps r₁ a b k → Good a x →
      ∃ y, Relation.RelatesInSteps r₂ x y k ∧ Good b y by
    obtain ⟨y, hy, _⟩ := this n s t u hrel hgood
    exact le_dheight_of_relatesInSteps hy
  intro k a b x hrel
  induction hrel generalizing x with
  | refl =>
    intro hgx
    exact ⟨x, .refl x, hgx⟩
  | tail _ _ _ _ hr ih =>
    intro hgx
    obtain ⟨y, hy, hgy⟩ := ih x hgx
    obtain ⟨z, hz, hgz⟩ := hstep _ _ _ hr hgy
    exact ⟨z, .tail _ _ _ _ hy hz, hgz⟩

/-- A decreasing measure `G : α → ℕ` on reachable `r`-steps bounds `dheight r a ≤ G a`. -/
theorem dheight_le_of_measure {r : α → α → Prop} (G : α → ℕ) (a : α)
    (hdec : ∀ s t, Relation.ReflTransGen r a s → r s t → G t < G s) :
    dheight r a ≤ (G a : ℕ∞) := by
  rw [dheight_le_iff]
  intro n b hb
  suffices ∀ (k : ℕ) (c : α), Relation.RelatesInSteps r a c k → G c + k ≤ G a by
    have h := this n b hb
    exact_mod_cast (by omega : n ≤ G a)
  intro k c hc
  induction hc with
  | refl => omega
  | tail t' t'' _ hpre hr ih =>
    have hlt := hdec t' t'' hpre.reflTransGen hr
    omega

end DerivationHeight

section Examples

-- Private non-vacuity check on a concrete unary-symbol language.
private inductive UnaryFun : ℕ → Type
  | z : UnaryFun 0
  | s : UnaryFun 1

private def unaryLang : FirstOrder.Language.{0, 0} where
  Functions := UnaryFun
  Relations := fun _ => PEmpty

private example :
    termSize (L := unaryLang) (V := ℕ) (.func UnaryFun.s ![.func UnaryFun.z Fin.elim0]) = 2 := by
  simp [termSize]

end Examples

end CslibFrontier.Computability.TermRewriting
