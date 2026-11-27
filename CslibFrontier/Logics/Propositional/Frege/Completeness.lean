module

public import Cslib.Logics.Propositional.Defs
public import CslibFrontier.Logics.Propositional.Frege
public import CslibFrontier.Logics.Propositional.Semantics
public import Mathlib.Data.List.Basic

import Mathlib.Data.Bool.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Ring

/-!
# Propositional Formula Size, Substitution, and Completeness of Frege Systems

Syntactic size, variable lists, derived connectives (`iff`, `xor`, `bigAnd`, `bigOr`, `snocOr`),
single-variable substitution, and computable Kalmár completeness for `Cslib.Logic.PL.Proposition`
and the Hilbert–Frege system `Cslib.Logic.PL.Frege`.

## Main definitions

- `CslibFrontier.Logics.Propositional.Frege.PropSize`: node-count size, derived connectives
  (`iff`, `xor`, `substVar`, `bigAnd`, `bigOr`, `snocOr`), and variable list `vars` on
  `Cslib.Logic.PL.Proposition`.
- `CslibFrontier.Logics.Propositional.Frege.FregeDeriv`: constructive Frege derivation trees over
  `Cslib.Logic.PL.Frege.IsAxiom`, with computable compilation into `Cslib.Logic.PL.Frege.IsProof`
  lists, computable deduction theorem `FregeDeriv.deduct`, and substitution `FregeDeriv.subst`.
- `CslibFrontier.Logics.Propositional.Frege.FregeDeriv.kalmar`: computable Kalmár completeness
  deriving any Boolean tautology in `Cslib.Logic.PL.Frege`.

## Main results

- `CslibFrontier.Logics.Propositional.Frege.isProof_subst`: substitution closedness of
  `Cslib.Logic.PL.Frege.IsProof`.
- `CslibFrontier.Logics.Propositional.Frege.proofSize_map_subst_le`: linear formula-size bound
  under substitution.
- `CslibFrontier.Logics.Propositional.Frege.frege_complete`: every propositional tautology over
  `Cslib.Logic.PL.Proposition` is derivable in `Cslib.Logic.PL.Frege`.
-/

public section

namespace CslibFrontier.Logics.Propositional.Frege

open Cslib.Logic.PL
open Cslib.Logic.PL.Frege

/-! ### Propositional Formula Size, Variables, and Derived Connectives -/

section Syntax

variable {V W : Type*}

/-- Number of syntax-tree nodes in a `Cslib.Logic.PL.Proposition`. -/
@[expose] def propSize : Proposition V → ℕ
  | .atom _ => 1
  | .falsum => 1
  | .and φ ψ => propSize φ + propSize ψ + 1
  | .or φ ψ => propSize φ + propSize ψ + 1
  | .imp φ ψ => propSize φ + propSize ψ + 1

@[simp] theorem propSize_atom (v : V) : propSize (Proposition.atom v) = 1 := rfl
@[simp] theorem propSize_falsum : propSize (Proposition.falsum : Proposition V) = 1 := rfl
@[simp] theorem propSize_bot : propSize (⊥ : Proposition V) = 1 := rfl
@[simp] theorem propSize_and (φ ψ : Proposition V) :
    propSize (Proposition.and φ ψ) = propSize φ + propSize ψ + 1 := rfl
@[simp] theorem propSize_or (φ ψ : Proposition V) :
    propSize (Proposition.or φ ψ) = propSize φ + propSize ψ + 1 := rfl
@[simp] theorem propSize_imp (φ ψ : Proposition V) :
    propSize (Proposition.imp φ ψ) = propSize φ + propSize ψ + 1 := rfl
@[simp] theorem propSize_neg (φ : Proposition V) :
    propSize (Proposition.neg φ) = propSize φ + 2 := rfl
theorem propSize_verum : propSize (Proposition.verum : Proposition V) = 3 := rfl
@[simp] theorem propSize_top : propSize (⊤ : Proposition V) = 3 := rfl

/-- Every propositional formula has size at least `1`. -/
theorem one_le_propSize (φ : Proposition V) : 1 ≤ propSize φ := by
  cases φ <;> simp [propSize]

/-- List of variable occurrences (with multiplicity) in a `Proposition`. -/
@[expose] def propVars : Proposition V → List V
  | .atom v => [v]
  | .falsum => []
  | .and φ ψ => propVars φ ++ propVars ψ
  | .or φ ψ => propVars φ ++ propVars ψ
  | .imp φ ψ => propVars φ ++ propVars ψ

@[simp] theorem propVars_atom (v : V) : propVars (Proposition.atom v) = [v] := rfl
@[simp] theorem propVars_falsum : propVars (Proposition.falsum : Proposition V) = [] := rfl
@[simp] theorem propVars_bot : propVars (⊥ : Proposition V) = [] := rfl
@[simp] theorem propVars_and (φ ψ : Proposition V) :
    propVars (Proposition.and φ ψ) = propVars φ ++ propVars ψ := rfl
@[simp] theorem propVars_or (φ ψ : Proposition V) :
    propVars (Proposition.or φ ψ) = propVars φ ++ propVars ψ := rfl
@[simp] theorem propVars_imp (φ ψ : Proposition V) :
    propVars (Proposition.imp φ ψ) = propVars φ ++ propVars ψ := rfl
theorem propVars_neg (φ : Proposition V) :
    propVars (Proposition.neg φ) = propVars φ := by simp [propVars]
@[simp] theorem propVars_top : propVars (⊤ : Proposition V) = [] := rfl

/-- Boolean evaluation of `Proposition.neg` under `σ : V → Bool`. -/
theorem eval_neg_bool (σ : V → Bool) (φ : Proposition V) :
    (Proposition.neg φ).eval σ = !φ.eval σ :=
  (Proposition.eval_imp_bool σ φ ⊥).trans (by simp)

/-- Boolean evaluation of `⊤` (`Proposition.verum`) under `σ : V → Bool`. -/
@[simp] theorem eval_top_bool (σ : V → Bool) :
    (⊤ : Proposition V).eval σ = true := rfl

/-- Boolean evaluation of `Proposition.verum` under `σ : V → Bool`. -/
@[simp] theorem eval_verum_bool (σ : V → Bool) :
    (Proposition.verum : Proposition V).eval σ = true := rfl

/-- Boolean evaluation depends only on variables in `propVars φ`. -/
theorem eval_congr_propVars {σ τ : V → Bool} {φ : Proposition V}
    (h : ∀ v ∈ propVars φ, σ v = τ v) : φ.eval σ = φ.eval τ := by
  induction φ with
  | atom v => exact h v (by simp)
  | falsum => rfl
  | and ψ χ ih1 ih2 | or ψ χ ih1 ih2 | imp ψ χ ih1 ih2 =>
    simp only [Proposition.eval_and_bool, Proposition.eval_or_bool, Proposition.eval_imp_bool]
    rw [ih1 (fun v hv ↦ h v (List.mem_append_left _ hv)),
        ih2 (fun v hv ↦ h v (List.mem_append_right _ hv))]

/-- Substitution of `Proposition.neg`. -/
theorem subst_neg (f : V → Proposition W) (φ : Proposition V) :
    (Proposition.neg φ).subst f = Proposition.neg (φ.subst f) := rfl

/-- Substitution of `⊤`. -/
@[simp] theorem subst_top (f : V → Proposition W) :
    (⊤ : Proposition V).subst f = ⊤ := rfl

/-- Substitution of `⊥`. -/
@[simp] theorem subst_bot (f : V → Proposition W) :
    (⊥ : Proposition V).subst f = ⊥ := rfl

/-- Substitution of `and`. -/
@[simp] theorem subst_and (f : V → Proposition W) (φ ψ : Proposition V) :
    (Proposition.and φ ψ).subst f = Proposition.and (φ.subst f) (ψ.subst f) := rfl

/-- Substitution of `or`. -/
@[simp] theorem subst_or (f : V → Proposition W) (φ ψ : Proposition V) :
    (Proposition.or φ ψ).subst f = Proposition.or (φ.subst f) (ψ.subst f) := rfl

/-- Substitution of `imp`. -/
@[simp] theorem subst_imp (f : V → Proposition W) (φ ψ : Proposition V) :
    (Proposition.imp φ ψ).subst f = Proposition.imp (φ.subst f) (ψ.subst f) := rfl

/-- Boolean evaluation of `Proposition.subst`. -/
@[simp] theorem eval_subst_bool (σ : W → Bool) (f : V → Proposition W) (φ : Proposition V) :
    (φ.subst f).eval σ = φ.eval (fun v ↦ (f v).eval σ) := by
  induction φ with
  | atom v => rfl
  | falsum => rfl
  | and ψ χ ih1 ih2 =>
    rw [subst_and, Proposition.eval_and_bool, Proposition.eval_and_bool, ih1, ih2]
  | or ψ χ ih1 ih2 =>
    rw [subst_or, Proposition.eval_or_bool, Proposition.eval_or_bool, ih1, ih2]
  | imp ψ χ ih1 ih2 =>
    rw [subst_imp, Proposition.eval_imp_bool, Proposition.eval_imp_bool, ih1, ih2]

/-- If `f v = atom v` for all `v ∈ propVars φ`, then `φ.subst f = φ`. -/
theorem subst_eq_self_of_forall {f : V → Proposition V} {φ : Proposition V}
    (h : ∀ v ∈ propVars φ, f v = .atom v) : φ.subst f = φ := by
  induction φ with
  | atom v => exact h v (by simp)
  | falsum => rfl
  | and ψ χ ih1 ih2 =>
    rw [subst_and, ih1 (fun v hv ↦ h v (List.mem_append_left _ hv)),
        ih2 (fun v hv ↦ h v (List.mem_append_right _ hv))]
  | or ψ χ ih1 ih2 =>
    rw [subst_or, ih1 (fun v hv ↦ h v (List.mem_append_left _ hv)),
        ih2 (fun v hv ↦ h v (List.mem_append_right _ hv))]
  | imp ψ χ ih1 ih2 =>
    rw [subst_imp, ih1 (fun v hv ↦ h v (List.mem_append_left _ hv)),
        ih2 (fun v hv ↦ h v (List.mem_append_right _ hv))]

/-- Variable occurrences in `φ.subst f`. -/
theorem mem_propVars_subst_iff {f : V → Proposition W} {φ : Proposition V} {w : W} :
    w ∈ propVars (φ.subst f) ↔ ∃ v ∈ propVars φ, w ∈ propVars (f v) := by
  induction φ with
  | atom v =>
    change w ∈ propVars (f v) ↔ _
    simp only [propVars_atom, List.mem_singleton, exists_eq_left]
  | falsum =>
    change w ∈ propVars Proposition.falsum ↔ _
    simp
  | and ψ χ ih1 ih2 =>
    rw [subst_and, propVars_and, propVars_and, List.mem_append, ih1, ih2]
    exact ⟨fun h ↦ h.elim (fun ⟨v, hv, hw⟩ ↦ ⟨v, List.mem_append_left _ hv, hw⟩)
        (fun ⟨v, hv, hw⟩ ↦ ⟨v, List.mem_append_right _ hv, hw⟩),
      fun ⟨v, hv, hw⟩ ↦ (List.mem_append.mp hv).elim (fun h ↦ Or.inl ⟨v, h, hw⟩)
        (fun h ↦ Or.inr ⟨v, h, hw⟩)⟩
  | or ψ χ ih1 ih2 =>
    rw [subst_or, propVars_or, propVars_or, List.mem_append, ih1, ih2]
    exact ⟨fun h ↦ h.elim (fun ⟨v, hv, hw⟩ ↦ ⟨v, List.mem_append_left _ hv, hw⟩)
        (fun ⟨v, hv, hw⟩ ↦ ⟨v, List.mem_append_right _ hv, hw⟩),
      fun ⟨v, hv, hw⟩ ↦ (List.mem_append.mp hv).elim (fun h ↦ Or.inl ⟨v, h, hw⟩)
        (fun h ↦ Or.inr ⟨v, h, hw⟩)⟩
  | imp ψ χ ih1 ih2 =>
    rw [subst_imp, propVars_imp, propVars_imp, List.mem_append, ih1, ih2]
    exact ⟨fun h ↦ h.elim (fun ⟨v, hv, hw⟩ ↦ ⟨v, List.mem_append_left _ hv, hw⟩)
        (fun ⟨v, hv, hw⟩ ↦ ⟨v, List.mem_append_right _ hv, hw⟩),
      fun ⟨v, hv, hw⟩ ↦ (List.mem_append.mp hv).elim (fun h ↦ Or.inl ⟨v, h, hw⟩)
        (fun h ↦ Or.inr ⟨v, h, hw⟩)⟩

/-- Size bound for `φ.subst f` when `(f v).size ≤ M` on all variables of `φ`. -/
theorem propSize_subst_le {f : V → Proposition W} {M : ℕ} (hM : 1 ≤ M)
    (φ : Proposition V) (hf : ∀ v ∈ propVars φ, propSize (f v) ≤ M) :
    propSize (φ.subst f) ≤ propSize φ * M := by
  induction φ with
  | atom v =>
    change propSize (f v) ≤ _
    simpa only [propSize_atom, Nat.one_mul] using hf v (by simp)
  | falsum =>
    change propSize Proposition.falsum ≤ _
    simpa only [propSize_falsum, Nat.one_mul] using hM
  | and ψ χ ih1 ih2 =>
    simp only [subst_and, propSize_and]
    have h1 := ih1 (fun v hv ↦ hf v (List.mem_append_left _ hv))
    have h2 := ih2 (fun v hv ↦ hf v (List.mem_append_right _ hv))
    calc propSize (ψ.subst f) + propSize (χ.subst f) + 1
        ≤ propSize ψ * M + propSize χ * M + M := by omega
      _ = (propSize ψ + propSize χ + 1) * M := by ring
  | or ψ χ ih1 ih2 =>
    simp only [subst_or, propSize_or]
    have h1 := ih1 (fun v hv ↦ hf v (List.mem_append_left _ hv))
    have h2 := ih2 (fun v hv ↦ hf v (List.mem_append_right _ hv))
    calc propSize (ψ.subst f) + propSize (χ.subst f) + 1
        ≤ propSize ψ * M + propSize χ * M + M := by omega
      _ = (propSize ψ + propSize χ + 1) * M := by ring
  | imp ψ χ ih1 ih2 =>
    simp only [subst_imp, propSize_imp]
    have h1 := ih1 (fun v hv ↦ hf v (List.mem_append_left _ hv))
    have h2 := ih2 (fun v hv ↦ hf v (List.mem_append_right _ hv))
    calc propSize (ψ.subst f) + propSize (χ.subst f) + 1
        ≤ propSize ψ * M + propSize χ * M + M := by omega
      _ = (propSize ψ + propSize χ + 1) * M := by ring

/-- Propositional biconditional `(φ → ψ) ∧ (ψ → φ)`. -/
@[expose] def propIff (φ ψ : Proposition V) : Proposition V :=
  Proposition.and (Proposition.imp φ ψ) (Proposition.imp ψ φ)

@[simp] theorem eval_propIff_bool (σ : V → Bool) (φ ψ : Proposition V) :
    (propIff φ ψ).eval σ = (φ.eval σ == ψ.eval σ) := by
  simp only [propIff, Proposition.eval_and_bool, Proposition.eval_imp_bool]
  cases φ.eval σ <;> cases ψ.eval σ <;> rfl

@[simp] theorem propSize_propIff (φ ψ : Proposition V) :
    propSize (propIff φ ψ) = 2 * propSize φ + 2 * propSize ψ + 3 := by
  simp [propIff]; omega

@[simp] theorem subst_propIff (f : V → Proposition W) (φ ψ : Proposition V) :
    (propIff φ ψ).subst f = propIff (φ.subst f) (ψ.subst f) := rfl

theorem mem_propVars_propIff_iff (φ ψ : Proposition V) (v : V) :
    v ∈ propVars (propIff φ ψ) ↔ v ∈ propVars φ ∨ v ∈ propVars ψ := by
  simp only [propIff, propVars_and, propVars_imp, List.mem_append]; tauto

/-- Propositional exclusive-or `¬(φ ↔ ψ)`. -/
@[expose] def propXor (φ ψ : Proposition V) : Proposition V :=
  Proposition.neg (propIff φ ψ)

@[simp] theorem eval_propXor_bool (σ : V → Bool) (φ ψ : Proposition V) :
    (propXor φ ψ).eval σ = (φ.eval σ != ψ.eval σ) := by
  simp only [propXor, eval_neg_bool, eval_propIff_bool]
  cases φ.eval σ <;> cases ψ.eval σ <;> rfl

@[simp] theorem propSize_propXor (φ ψ : Proposition V) :
    propSize (propXor φ ψ) = 2 * propSize φ + 2 * propSize ψ + 5 := by
  simp [propXor]

@[simp] theorem subst_propXor (f : V → Proposition W) (φ ψ : Proposition V) :
    (propXor φ ψ).subst f = propXor (φ.subst f) (ψ.subst f) := rfl

theorem mem_propVars_propXor_iff (φ ψ : Proposition V) (v : V) :
    v ∈ propVars (propXor φ ψ) ↔ v ∈ propVars φ ∨ v ∈ propVars ψ := by
  simp [propXor, mem_propVars_propIff_iff]

/-- Single-variable substitution `φ[a := θ]`. -/
@[expose] def substVar [DecidableEq V] (φ : Proposition V) (a : V) (θ : Proposition V) :
    Proposition V :=
  φ.subst (fun b ↦ if b = a then θ else .atom b)

@[simp] theorem substVar_atom [DecidableEq V] (a b : V) (θ : Proposition V) :
    substVar (.atom b) a θ = if b = a then θ else .atom b := rfl

@[simp] theorem substVar_falsum [DecidableEq V] (a : V) (θ : Proposition V) :
    substVar (.falsum : Proposition V) a θ = .falsum := rfl

@[simp] theorem substVar_bot [DecidableEq V] (a : V) (θ : Proposition V) :
    substVar (⊥ : Proposition V) a θ = ⊥ := rfl

@[simp] theorem substVar_top [DecidableEq V] (a : V) (θ : Proposition V) :
    substVar (⊤ : Proposition V) a θ = ⊤ := rfl

@[simp] theorem substVar_and [DecidableEq V] (a : V) (θ φ ψ : Proposition V) :
    substVar (.and φ ψ) a θ = .and (substVar φ a θ) (substVar ψ a θ) := rfl

@[simp] theorem substVar_or [DecidableEq V] (a : V) (θ φ ψ : Proposition V) :
    substVar (.or φ ψ) a θ = .or (substVar φ a θ) (substVar ψ a θ) := rfl

@[simp] theorem substVar_imp [DecidableEq V] (a : V) (θ φ ψ : Proposition V) :
    substVar (.imp φ ψ) a θ = .imp (substVar φ a θ) (substVar ψ a θ) := rfl

theorem substVar_neg [DecidableEq V] (a : V) (θ φ : Proposition V) :
    substVar (Proposition.neg φ) a θ = Proposition.neg (substVar φ a θ) := rfl

@[simp] theorem substVar_propIff [DecidableEq V] (a : V) (θ φ ψ : Proposition V) :
    substVar (propIff φ ψ) a θ = propIff (substVar φ a θ) (substVar ψ a θ) := rfl

@[simp] theorem substVar_propXor [DecidableEq V] (a : V) (θ φ ψ : Proposition V) :
    substVar (propXor φ ψ) a θ = propXor (substVar φ a θ) (substVar ψ a θ) := rfl

/-- Evaluation of single-variable substitution. -/
theorem eval_substVar_bool [DecidableEq V] (σ : V → Bool) (a : V) (θ φ : Proposition V) :
    (substVar φ a θ).eval σ = φ.eval (Function.update σ a (θ.eval σ)) := by
  rw [substVar, eval_subst_bool]
  refine eval_congr_propVars fun v _ ↦ ?_
  by_cases hva : v = a
  · subst hva; simp
  · simp [hva]

/-- If `a ∉ propVars φ`, substituting `a := θ` leaves `φ` unchanged. -/
theorem substVar_eq_self_of_not_mem [DecidableEq V] {a : V} {φ : Proposition V}
    (h : a ∉ propVars φ) (θ : Proposition V) : substVar φ a θ = φ :=
  subst_eq_self_of_forall fun v hv ↦ by
    have hva : v ≠ a := fun heq ↦ h (heq ▸ hv)
    simp [hva]

/-- Finite right-associated conjunction (`[] ↦ ⊤`, `[φ] ↦ φ`). -/
@[expose] def bigAnd : List (Proposition V) → Proposition V
  | [] => ⊤
  | [φ] => φ
  | φ :: ψ :: rest => Proposition.and φ (bigAnd (ψ :: rest))

@[simp] theorem bigAnd_nil : (bigAnd [] : Proposition V) = ⊤ := rfl
@[simp] theorem bigAnd_singleton (φ : Proposition V) : bigAnd [φ] = φ := rfl
@[simp] theorem bigAnd_cons_cons (φ ψ : Proposition V) (rest : List (Proposition V)) :
    bigAnd (φ :: ψ :: rest) = Proposition.and φ (bigAnd (ψ :: rest)) := rfl

/-- Finite right-associated disjunction (`[] ↦ ⊥`, `[φ] ↦ φ`). -/
@[expose] def bigOr : List (Proposition V) → Proposition V
  | [] => ⊥
  | [φ] => φ
  | φ :: ψ :: rest => Proposition.or φ (bigOr (ψ :: rest))

@[simp] theorem bigOr_nil : (bigOr [] : Proposition V) = ⊥ := rfl
@[simp] theorem bigOr_singleton (φ : Proposition V) : bigOr [φ] = φ := rfl
@[simp] theorem bigOr_cons_cons (φ ψ : Proposition V) (rest : List (Proposition V)) :
    bigOr (φ :: ψ :: rest) = Proposition.or φ (bigOr (ψ :: rest)) := rfl

@[simp] theorem eval_bigAnd_bool (σ : V → Bool) (L : List (Proposition V)) :
    (bigAnd L).eval σ = L.all (fun φ ↦ φ.eval σ) := by
  induction L with
  | nil => rfl
  | cons φ rest ih =>
    cases rest with
    | nil => simp [bigAnd]
    | cons ψ tail => simp [bigAnd, ih]

@[simp] theorem eval_bigOr_bool (σ : V → Bool) (L : List (Proposition V)) :
    (bigOr L).eval σ = L.any (fun φ ↦ φ.eval σ) := by
  induction L with
  | nil => rfl
  | cons φ rest ih =>
    cases rest with
    | nil => simp [bigOr]
    | cons ψ tail => simp [bigOr, ih]

/-- Size bound for `bigAnd`. -/
theorem propSize_bigAnd_le (L : List (Proposition V)) :
    propSize (bigAnd L) ≤ (L.map propSize).sum + L.length + 3 := by
  induction L with
  | nil => simp [bigAnd]
  | cons φ rest ih =>
    cases rest with
    | nil => simp [bigAnd]; omega
    | cons ψ tail =>
      simp only [bigAnd, propSize_and, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      omega

/-- Size bound for `bigOr`. -/
theorem propSize_bigOr_le (L : List (Proposition V)) :
    propSize (bigOr L) ≤ (L.map propSize).sum + L.length + 1 := by
  induction L with
  | nil => simp [bigOr]
  | cons φ rest ih =>
    cases rest with
    | nil => simp [bigOr]; omega
    | cons ψ tail =>
      simp only [bigOr, propSize_or, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      omega

/-- Variable occurrence membership for `bigAnd`. -/
theorem mem_propVars_bigAnd_iff {L : List (Proposition V)} {v : V} :
    v ∈ propVars (bigAnd L) ↔ ∃ φ ∈ L, v ∈ propVars φ := by
  induction L with
  | nil => simp [bigAnd]
  | cons φ rest ih =>
    cases rest with
    | nil => simp [bigAnd]
    | cons ψ tail =>
      simp only [bigAnd, propVars_and, List.mem_append, ih, List.mem_cons]
      exact ⟨fun h ↦ h.elim (fun hv ↦ ⟨φ, Or.inl rfl, hv⟩)
        (fun ⟨χ, hχ, hv⟩ ↦ ⟨χ, Or.inr hχ, hv⟩),
        fun ⟨χ, hχ, hv⟩ ↦ hχ.elim (fun h ↦ Or.inl (h ▸ hv)) (fun h ↦ Or.inr ⟨χ, h, hv⟩)⟩

/-- Variable occurrence membership for `bigOr`. -/
theorem mem_propVars_bigOr_iff {L : List (Proposition V)} {v : V} :
    v ∈ propVars (bigOr L) ↔ ∃ φ ∈ L, v ∈ propVars φ := by
  induction L with
  | nil => simp [bigOr]
  | cons φ rest ih =>
    cases rest with
    | nil => simp [bigOr]
    | cons ψ tail =>
      simp only [bigOr, propVars_or, List.mem_append, ih, List.mem_cons]
      exact ⟨fun h ↦ h.elim (fun hv ↦ ⟨φ, Or.inl rfl, hv⟩)
        (fun ⟨χ, hχ, hv⟩ ↦ ⟨χ, Or.inr hχ, hv⟩),
        fun ⟨χ, hχ, hv⟩ ↦ hχ.elim (fun h ↦ Or.inl (h ▸ hv)) (fun h ↦ Or.inr ⟨χ, h, hv⟩)⟩

/-- Snoc disjunction: `snocOr [] = ⊥`, `snocOr (φ :: rest) = (snocOr rest) ∨ φ`. -/
@[expose] def snocOr : List (Proposition V) → Proposition V
  | [] => ⊥
  | φ :: rest => Proposition.or (snocOr rest) φ

@[simp] theorem snocOr_nil : (snocOr [] : Proposition V) = ⊥ := rfl
@[simp] theorem snocOr_cons (φ : Proposition V) (rest : List (Proposition V)) :
    snocOr (φ :: rest) = Proposition.or (snocOr rest) φ := rfl

@[simp] theorem eval_snocOr_bool (σ : V → Bool) (L : List (Proposition V)) :
    (snocOr L).eval σ = L.any (fun φ ↦ φ.eval σ) := by
  induction L with
  | nil => rfl
  | cons φ rest ih => simp [snocOr, ih, Bool.or_comm]

/-- Exact size formula for `snocOr`. -/
theorem propSize_snocOr (L : List (Proposition V)) :
    propSize (snocOr L) = (L.map propSize).sum + L.length + 1 := by
  induction L with
  | nil => simp [snocOr]
  | cons φ rest ih => simp [snocOr, ih]; omega

/-- Variable occurrence membership for `snocOr`. -/
theorem mem_propVars_snocOr_iff {L : List (Proposition V)} {v : V} :
    v ∈ propVars (snocOr L) ↔ ∃ φ ∈ L, v ∈ propVars φ := by
  induction L with
  | nil => simp [snocOr]
  | cons φ rest ih =>
    simp only [snocOr, propVars_or, List.mem_append, ih, List.mem_cons]
    exact ⟨fun h ↦ h.elim (fun ⟨ψ, hψ, hv⟩ ↦ ⟨ψ, Or.inr hψ, hv⟩) (fun hv ↦ ⟨φ, Or.inl rfl, hv⟩),
      fun ⟨ψ, hψ, hv⟩ ↦ hψ.elim (fun h ↦ Or.inr (h ▸ hv)) (fun h ↦ Or.inl ⟨ψ, h, hv⟩)⟩

end Syntax

/-! ### Substitution Closedness of `Cslib.Logic.PL.Frege` -/

section SubstProof

variable {V W : Type*}

/-- Every `Cslib.Logic.PL.Frege.IsAxiom` schema is closed under formula substitution. -/
theorem isAxiom_subst (f : V → Proposition W) {φ : Proposition V} (h : IsAxiom φ) :
    IsAxiom (φ.subst f) := by
  cases h with
  | k a b => exact .k (a.subst f) (b.subst f)
  | s a b c => exact .s (a.subst f) (b.subst f) (c.subst f)
  | dne a => exact .dne (a.subst f)
  | andElimL a b => exact .andElimL (a.subst f) (b.subst f)
  | andElimR a b => exact .andElimR (a.subst f) (b.subst f)
  | andIntro a b => exact .andIntro (a.subst f) (b.subst f)
  | orIntroL a b => exact .orIntroL (a.subst f) (b.subst f)
  | orIntroR a b => exact .orIntroR (a.subst f) (b.subst f)
  | orElim a b c => exact .orElim (a.subst f) (b.subst f) (c.subst f)

/-- `Cslib.Logic.PL.Frege.IsProof` is closed under formula substitution. -/
theorem isProof_subst (f : V → Proposition W) {Γ L : List (Proposition V)}
    (h : IsProof Γ L) : IsProof (Γ.map (·.subst f)) (L.map (·.subst f)) := by
  induction h with
  | nil => exact .nil
  | hyp _ hφ ih => exact ih.hyp (List.mem_map_of_mem hφ)
  | ax _ hax ih => exact ih.ax (isAxiom_subst f hax)
  | mp _ h₁ h₂ ih =>
    exact ih.mp (List.mem_map_of_mem h₁) (List.mem_map_of_mem h₂)

/-- Total formula size of a list of formulas. -/
@[expose] def proofSize (L : List (Proposition V)) : ℕ :=
  (L.map propSize).sum

/-- Linear formula-size bound under substitution on a list of formulas. -/
theorem proofSize_map_subst_le {f : V → Proposition W} {M : ℕ} (hM : 1 ≤ M)
    (L : List (Proposition V)) (hf : ∀ φ ∈ L, ∀ v ∈ propVars φ, propSize (f v) ≤ M) :
    proofSize (L.map (·.subst f)) ≤ proofSize L * M := by
  induction L with
  | nil => simp [proofSize]
  | cons φ rest ih =>
    simp only [proofSize, List.map_cons, List.sum_cons] at ih ⊢
    have hφ := propSize_subst_le hM φ (hf φ List.mem_cons_self)
    have hrest := ih (fun ψ hψ ↦ hf ψ (List.mem_cons_of_mem _ hψ))
    calc propSize (φ.subst f) + ((rest.map (·.subst f)).map propSize).sum
        ≤ propSize φ * M + (rest.map propSize).sum * M := Nat.add_le_add hφ hrest
      _ = (propSize φ + (rest.map propSize).sum) * M := (Nat.add_mul _ _ _).symm

end SubstProof

/-! ### Constructive Frege Derivation Trees and Computable Kalmár Completeness -/

/-- Constructive tree representation of a Frege derivation from hypotheses `Γ`, over
`Cslib.Logic.PL.Frege.IsAxiom`. -/
inductive FregeDeriv {V : Type*} (Γ : List (Proposition V)) : Proposition V → Type _
  /-- Hypothesis leaf `φ ∈ Γ`. -/
  | hyp {φ : Proposition V} (h : φ ∈ Γ) : FregeDeriv Γ φ
  /-- Axiom schema leaf `IsAxiom φ`. -/
  | ax {φ : Proposition V} (h : IsAxiom φ) : FregeDeriv Γ φ
  /-- Modus ponens from `φ → ψ` and `φ`. -/
  | mp {φ ψ : Proposition V} (d₁ : FregeDeriv Γ (Proposition.imp φ ψ))
      (d₂ : FregeDeriv Γ φ) : FregeDeriv Γ ψ

namespace FregeDeriv

variable {V W : Type*}

/-- Identity combinator `φ → φ`. -/
@[expose] def id (Γ : List (Proposition V)) (φ : Proposition V) :
    FregeDeriv Γ (Proposition.imp φ φ) :=
  .mp (.mp (.ax (.s φ (Proposition.imp φ φ) φ)) (.ax (.k φ (Proposition.imp φ φ))))
    (.ax (.k φ φ))

/-- Weakening under an antecedent `a`. -/
def weaken {Γ : List (Proposition V)} (a : Proposition V) {φ : Proposition V}
    (d : FregeDeriv Γ φ) : FregeDeriv Γ (Proposition.imp a φ) :=
  .mp (.ax (.k φ a)) d

/-- Composition of implications `φ → ψ` and `ψ → χ`. -/
def trans {Γ : List (Proposition V)} {φ ψ χ : Proposition V}
    (d₁ : FregeDeriv Γ (Proposition.imp φ ψ)) (d₂ : FregeDeriv Γ (Proposition.imp ψ χ)) :
    FregeDeriv Γ (Proposition.imp φ χ) :=
  .mp (.mp (.ax (.s φ ψ χ)) (weaken φ d₂)) d₁

/-- Computable deduction theorem: discharge hypothesis `a` from `a :: Γ`. -/
def deduct [DecidableEq V] {Γ : List (Proposition V)} {a φ : Proposition V} :
    FregeDeriv (a :: Γ) φ → FregeDeriv Γ (Proposition.imp a φ)
  | .hyp (φ := ψ) h =>
    if hψa : ψ = a then
      hψa ▸ id Γ ψ
    else
      weaken a (.hyp ((List.mem_cons.mp h).resolve_left hψa))
  | .ax h => weaken a (.ax h)
  | .mp d₁ d₂ => .mp (.mp (.ax (.s a _ _)) (deduct d₁)) (deduct d₂)

/-- Monotonicity of `FregeDeriv` under hypothesis inclusion. -/
def mono {Γ Δ : List (Proposition V)} {φ : Proposition V} (hsub : ∀ ψ ∈ Γ, ψ ∈ Δ) :
    FregeDeriv Γ φ → FregeDeriv Δ φ
  | .hyp h => .hyp (hsub _ h)
  | .ax h => .ax h
  | .mp d₁ d₂ => .mp (mono hsub d₁) (mono hsub d₂)

/-- Substitution of variables throughout a `FregeDeriv` tree. -/
@[expose] def subst (f : V → Proposition W) {Γ : List (Proposition V)} {φ : Proposition V} :
    FregeDeriv Γ φ → FregeDeriv (Γ.map (·.subst f)) (φ.subst f)
  | .hyp h => .hyp (List.mem_map_of_mem h)
  | .ax h => .ax (isAxiom_subst f h)
  | .mp d₁ d₂ => .mp (subst f d₁) (subst f d₂)

@[simp] theorem subst_hyp (f : V → Proposition W) {Γ : List (Proposition V)} {φ : Proposition V}
    (h : φ ∈ Γ) : (FregeDeriv.hyp h).subst f = .hyp (List.mem_map_of_mem h) := rfl

@[simp] theorem subst_ax (f : V → Proposition W) {Γ : List (Proposition V)} {φ : Proposition V}
    (h : IsAxiom φ) : (FregeDeriv.ax (Γ := Γ) h).subst f = .ax (isAxiom_subst f h) := rfl

@[simp] theorem subst_mp (f : V → Proposition W) {Γ : List (Proposition V)} {φ ψ : Proposition V}
    (d₁ : FregeDeriv Γ (Proposition.imp φ ψ)) (d₂ : FregeDeriv Γ φ) :
    (FregeDeriv.mp d₁ d₂).subst f = .mp (d₁.subst f) (d₂.subst f) := rfl

/-- Compile a `FregeDeriv` tree into a reverse-chronological `Cslib.Logic.PL.Frege.IsProof`
line list whose head is the conclusion `φ`. -/
def toLines {Γ : List (Proposition V)} : {φ : Proposition V} → FregeDeriv Γ φ →
    List (Proposition V)
  | φ, .hyp _ => [φ]
  | φ, .ax _ => [φ]
  | ψ, .mp d₁ d₂ => ψ :: (toLines d₂ ++ toLines d₁)

/-- The head of `d.toLines` is the conclusion `φ`. -/
theorem mem_toLines {Γ : List (Proposition V)} {φ : Proposition V} (d : FregeDeriv Γ φ) :
    φ ∈ d.toLines := by
  cases d <;> simp [toLines]

/-- `d.toLines` is always a valid `Cslib.Logic.PL.Frege.IsProof` from `Γ`. -/
theorem isProof_toLines {Γ : List (Proposition V)} {φ : Proposition V} (d : FregeDeriv Γ φ) :
    IsProof Γ d.toLines := by
  induction d with
  | hyp h => exact IsProof.nil.hyp h
  | ax h => exact IsProof.nil.ax h
  | mp d₁ d₂ ih1 ih2 =>
    exact (ih1.append ih2).mp (List.mem_append_left _ (mem_toLines d₂))
      (List.mem_append_right _ (mem_toLines d₁))

/-- Ex falso quodlibet `⊥ → φ`. -/
def efq (Γ : List (Proposition V)) (φ : Proposition V) :
    FregeDeriv Γ (Proposition.imp ⊥ φ) :=
  trans (.ax (.k ⊥ (Proposition.neg φ))) (.ax (.dne φ))

/-- Double-negation introduction `φ → ¬¬φ`. -/
def dni [DecidableEq V] (Γ : List (Proposition V)) (φ : Proposition V) :
    FregeDeriv Γ (Proposition.imp φ (Proposition.neg (Proposition.neg φ))) :=
  deduct (deduct (.mp (.hyp List.mem_cons_self) (.hyp (List.mem_cons_of_mem _ List.mem_cons_self))))

/-- Contraposition `(φ → ψ) → (¬ψ → ¬φ)`. -/
def contrapose [DecidableEq V] {Γ : List (Proposition V)} {φ ψ : Proposition V}
    (d : FregeDeriv Γ (Proposition.imp φ ψ)) :
    FregeDeriv Γ (Proposition.imp (Proposition.neg ψ) (Proposition.neg φ)) :=
  deduct (deduct (.mp (.hyp (List.mem_cons_of_mem _ List.mem_cons_self))
    (.mp (mono (fun _ h ↦ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)) d)
      (.hyp List.mem_cons_self))))

/-- Excluded middle `φ ∨ ¬φ`. -/
def em [DecidableEq V] (Γ : List (Proposition V)) (φ : Proposition V) :
    FregeDeriv Γ (Proposition.or φ (Proposition.neg φ)) :=
  let h1 : FregeDeriv (Proposition.neg (Proposition.or φ (Proposition.neg φ)) :: Γ)
      (Proposition.neg φ) :=
    deduct (.mp (.hyp (List.mem_cons_of_mem _ List.mem_cons_self))
      (.mp (.ax (.orIntroL φ (Proposition.neg φ))) (.hyp List.mem_cons_self)))
  let h2 : FregeDeriv (Proposition.neg (Proposition.or φ (Proposition.neg φ)) :: Γ) ⊥ :=
    .mp (.hyp List.mem_cons_self) (.mp (.ax (.orIntroR φ (Proposition.neg φ))) h1)
  .mp (.ax (.dne _)) (deduct h2)

/-- Case split: from `a :: Γ ⊢ φ` and `¬a :: Γ ⊢ φ`, derive `Γ ⊢ φ`. -/
def caseSplit [DecidableEq V] {Γ : List (Proposition V)} {a φ : Proposition V}
    (dT : FregeDeriv (a :: Γ) φ) (dF : FregeDeriv (Proposition.neg a :: Γ) φ) :
    FregeDeriv Γ φ :=
  .mp (.mp (.mp (.ax (.orElim a (Proposition.neg a) φ)) (deduct dT)) (deduct dF)) (em Γ a)

/-- Helper literal formula for Kalmár's completeness proof: `v` if `b`, else `¬v`. -/
@[expose] def kalmarLit (v : V) (b : Bool) : Proposition V :=
  if b then .atom v else Proposition.neg (.atom v)

/-- Signed variable context for valuation `σ` and variable list `vs`. -/
@[expose] def kalmarCtx (σ : V → Bool) (vs : List V) : List (Proposition V) :=
  vs.map (fun v ↦ kalmarLit v (σ v))

/-- Signed formula `φ` if `φ.eval σ = true`, else `¬φ`. -/
@[expose] def kalmarSigned (σ : V → Bool) (φ : Proposition V) : Proposition V :=
  if φ.eval σ then φ else Proposition.neg φ

/-- Helper for `kalmarEval` on `and`. -/
private def kalmarAnd [DecidableEq V] {Γ : List (Proposition V)} {ψ χ : Proposition V} :
    (b₁ b₂ : Bool) →
    FregeDeriv Γ (if b₁ then ψ else Proposition.neg ψ) →
    FregeDeriv Γ (if b₂ then χ else Proposition.neg χ) →
    FregeDeriv Γ (if (b₁ && b₂) then Proposition.and ψ χ else Proposition.neg (Proposition.and ψ χ))
  | false, _, dψ, _ =>
    deduct (.mp (mono (fun _ h ↦ List.mem_cons_of_mem _ h) dψ)
      (.mp (.ax (.andElimL ψ χ)) (.hyp List.mem_cons_self)))
  | true, false, _, dχ =>
    deduct (.mp (mono (fun _ h ↦ List.mem_cons_of_mem _ h) dχ)
      (.mp (.ax (.andElimR ψ χ)) (.hyp List.mem_cons_self)))
  | true, true, dψ, dχ => .mp (.mp (.ax (.andIntro ψ χ)) dψ) dχ

/-- Helper for `kalmarEval` on `or`. -/
private def kalmarOr [DecidableEq V] {Γ : List (Proposition V)} {ψ χ : Proposition V} :
    (b₁ b₂ : Bool) →
    FregeDeriv Γ (if b₁ then ψ else Proposition.neg ψ) →
    FregeDeriv Γ (if b₂ then χ else Proposition.neg χ) →
    FregeDeriv Γ (if (b₁ || b₂) then Proposition.or ψ χ else Proposition.neg (Proposition.or ψ χ))
  | false, false, dψ, dχ =>
    deduct (.mp (.mp (.mp (.ax (.orElim ψ χ ⊥))
      (mono (fun _ h ↦ List.mem_cons_of_mem _ h) dψ))
      (mono (fun _ h ↦ List.mem_cons_of_mem _ h) dχ)) (.hyp List.mem_cons_self))
  | false, true, _, dχ => .mp (.ax (.orIntroR ψ χ)) dχ
  | true, _, dψ, _ => .mp (.ax (.orIntroL ψ χ)) dψ

/-- Helper for `kalmarEval` on `imp`. -/
private def kalmarImp [DecidableEq V] {Γ : List (Proposition V)} {ψ χ : Proposition V} :
    (b₁ b₂ : Bool) →
    FregeDeriv Γ (if b₁ then ψ else Proposition.neg ψ) →
    FregeDeriv Γ (if b₂ then χ else Proposition.neg χ) →
    FregeDeriv Γ
      (if (!b₁ || b₂) then Proposition.imp ψ χ else Proposition.neg (Proposition.imp ψ χ))
  | false, _, dψ, _ =>
    deduct (.mp (efq _ χ) (.mp (mono (fun _ h ↦ List.mem_cons_of_mem _ h) dψ)
      (.hyp List.mem_cons_self)))
  | true, false, dψ, dχ =>
    deduct (.mp (mono (fun _ h ↦ List.mem_cons_of_mem _ h) dχ)
      (.mp (.hyp List.mem_cons_self) (mono (fun _ h ↦ List.mem_cons_of_mem _ h) dψ)))
  | true, true, _, dχ => weaken ψ dχ

/-- Kalmár's evaluation lemma: under `kalmarCtx σ vs` covering `propVars φ`, either `φ`
(if `φ.eval σ = true`) or `¬φ` (if `φ.eval σ = false`) is constructively derivable. -/
def kalmarEval [DecidableEq V] (σ : V → Bool) (vs : List V) :
    (φ : Proposition V) → (∀ v ∈ propVars φ, v ∈ vs) →
    FregeDeriv (kalmarCtx σ vs) (kalmarSigned σ φ)
  | .atom v, hvs =>
    .hyp (List.mem_map_of_mem (hvs v (by simp)))
  | .falsum, _ => id _ ⊥
  | .and ψ χ, hvs =>
    kalmarAnd (ψ.eval σ) (χ.eval σ)
      (kalmarEval σ vs ψ (fun v hv ↦ hvs v (List.mem_append_left _ hv)))
      (kalmarEval σ vs χ (fun v hv ↦ hvs v (List.mem_append_right _ hv)))
  | .or ψ χ, hvs =>
    kalmarOr (ψ.eval σ) (χ.eval σ)
      (kalmarEval σ vs ψ (fun v hv ↦ hvs v (List.mem_append_left _ hv)))
      (kalmarEval σ vs χ (fun v hv ↦ hvs v (List.mem_append_right _ hv)))
  | .imp ψ χ, hvs => by
    have h := kalmarImp (ψ.eval σ) (χ.eval σ)
      (kalmarEval σ vs ψ (fun v hv ↦ hvs v (List.mem_append_left _ hv)))
      (kalmarEval σ vs χ (fun v hv ↦ hvs v (List.mem_append_right _ hv)))
    simpa only [kalmarSigned, Proposition.eval_imp_bool] using h

/-- Variable-elimination recursion for Kalmár's completeness proof. -/
def kalmarElim [DecidableEq V] (φ : Proposition V) :
    (vs : List V) →
    (∀ σ : V → Bool, FregeDeriv (kalmarCtx σ vs) φ) →
    FregeDeriv [] φ
  | [], h => h (fun _ ↦ false)
  | v :: rest, h =>
    kalmarElim φ rest fun σ ↦
      let hT : FregeDeriv (Proposition.atom v :: kalmarCtx σ rest) φ :=
        mono (by
          intro ψ hψ
          simp only [kalmarCtx, List.map_cons, List.mem_cons] at hψ ⊢
          rcases hψ with rfl | hr
          · exact Or.inl (by simp [kalmarLit])
          · rcases List.mem_map.mp hr with ⟨w, hw, rfl⟩
            by_cases hwv : w = v
            · subst hwv; exact Or.inl (by simp [kalmarLit])
            · exact Or.inr (List.mem_map.mpr ⟨w, hw, by simp [Function.update_of_ne hwv]⟩))
          (h (Function.update σ v true))
      let hF : FregeDeriv (Proposition.neg (Proposition.atom v) :: kalmarCtx σ rest) φ :=
        mono (by
          intro ψ hψ
          simp only [kalmarCtx, List.map_cons, List.mem_cons] at hψ ⊢
          rcases hψ with rfl | hr
          · exact Or.inl (by simp [kalmarLit])
          · rcases List.mem_map.mp hr with ⟨w, hw, rfl⟩
            by_cases hwv : w = v
            · subst hwv; exact Or.inl (by simp [kalmarLit])
            · exact Or.inr (List.mem_map.mpr ⟨w, hw, by simp [Function.update_of_ne hwv]⟩))
          (h (Function.update σ v false))
      caseSplit hT hF

/-- **Computable Kalmár completeness** for `Cslib.Logic.PL.Frege`: given any tautology `φ`,
constructs a `FregeDeriv [] φ` derivation tree. -/
def kalmar [DecidableEq V] (φ : Proposition V) (htaut : ∀ σ : V → Bool, φ.eval σ = true) :
    FregeDeriv [] φ :=
  kalmarElim φ (propVars φ) fun σ ↦ by
    have d := kalmarEval σ (propVars φ) φ (fun _ h ↦ h)
    simpa only [kalmarSigned, htaut σ, ↓reduceIte] using d

end FregeDeriv

/-- **Completeness of `Cslib.Logic.PL.Frege`**: every propositional tautology over
`Cslib.Logic.PL.Proposition` has a `Cslib.Logic.PL.Frege.IsProof []` derivation. -/
theorem frege_complete {V : Type*} {φ : Proposition V}
    (htaut : ∀ σ : V → Bool, φ.eval σ = true) :
    ∃ L : List (Proposition V), IsProof [] L ∧ φ ∈ L := by
  classical
  let d := FregeDeriv.kalmar φ htaut
  exact ⟨d.toLines, d.isProof_toLines, d.mem_toLines⟩

end CslibFrontier.Logics.Propositional.Frege
