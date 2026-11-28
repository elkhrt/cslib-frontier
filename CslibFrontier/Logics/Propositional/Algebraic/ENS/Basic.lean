/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic

import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Proof Complexity Foundations: Bounded-Degree Polynomials and $F(\mathrm{MOD}_p)$-Frege Systems

This module provides reusable infrastructure for algebraic and propositional proof complexity over
prime fields $\mathbb{F}_p$, verified under standard Lean axioms.

## Main definitions

- `CslibFrontier.Logic.PL.ENS.PolyBoundedDeg`: the $\mathbb{F}_p$-subspace $\mathbb{F}_p^{\le d}[V]$
  of multivariate polynomials in `MvPolynomial V (ZMod p)` of total degree at most `d`, with unit,
  constant, variable, degree-lifting, renaming, and finiteness APIs.
- `CslibFrontier.Logic.PL.ENS.ModFregeFormula`, `CslibFrontier.Logic.PL.ENS.ModFregeFormula.depth`,
  `CslibFrontier.Logic.PL.ENS.ModFregeFormula.IsModAxiom`: flattened De Morgan and modular-counting
  formulas, formula depth, and $\mathrm{MOD}_p$ axiom schemas.
- `CslibFrontier.Logic.PL.ENS.ModFregeFormula.FregeCalculus`,
  `CslibFrontier.Logic.PL.ENS.ModFregeFormula.FregeDerivation`: schematic Frege calculi and
  bounded-depth $F_\ell(\mathrm{MOD}_p)$ derivations.
- `CslibFrontier.Logic.PL.ENS.polyEqZeroFormula`: depth-`≤ 2` encoding of polynomial equations
  $f = 0$ over $0/1$ assignments.

## Main results

- `CslibFrontier.Logic.PL.ENS.ModFregeFormula.evalBool_eq_true_of_isModAxiom`,
  `CslibFrontier.Logic.PL.ENS.ModFregeFormula.FregeDerivation.evalBool_eq_true`, and
  `FregeDerivation.exists_step_hyp_evalBool_false_of_isRefutation`:
  semantic soundness of $\mathrm{MOD}_p$ axioms and bounded-depth $F_\ell(\mathrm{MOD}_p)$
  derivations and refutations.
- `CslibFrontier.Logic.PL.ENS.depth_polyEqZeroFormula_le_two`,
  `CslibFrontier.Logic.PL.ENS.evalBool_polyEqZeroFormula_iff`: depth bound and semantic faithfulness
  of the $F(\mathrm{MOD}_p)$ polynomial equation encoding.
-/

public section

namespace CslibFrontier.Logic.PL.ENS

section PolyBoundedDeg

/-- The $\mathbb{F}_p$-vector space $\mathbb{F}_p^{\le d}[V]$ of polynomials over `ZMod p` in
variables `V` of total degree at most `d`. -/
abbrev PolyBoundedDeg (V : Type*) (p d : ℕ) : Type _ :=
  MvPolynomial.restrictTotalDegree V (ZMod p) d

namespace PolyBoundedDeg

/-- Total degree bound of an element of `PolyBoundedDeg V p d`. -/
theorem totalDegree_le {V : Type*} {p d : ℕ} (f : PolyBoundedDeg V p d) :
    f.1.totalDegree ≤ d :=
  (MvPolynomial.mem_restrictTotalDegree V d f.1).mp f.2

/-- The constant polynomial `1` in `PolyBoundedDeg V p d`. -/
noncomputable def one (V : Type*) (p d : ℕ) : PolyBoundedDeg V p d :=
  ⟨1, (MvPolynomial.mem_restrictTotalDegree V d (1 : MvPolynomial V (ZMod p))).mpr (by simp)⟩

@[simp]
theorem coe_one (V : Type*) (p d : ℕ) :
    ((one V p d : PolyBoundedDeg V p d) : MvPolynomial V (ZMod p)) = 1 := by
  rfl

/-- Constant polynomial `C a` in `PolyBoundedDeg V p d`. -/
noncomputable def const (V : Type*) (p d : ℕ) (a : ZMod p) : PolyBoundedDeg V p d :=
  ⟨MvPolynomial.C a,
    (MvPolynomial.mem_restrictTotalDegree V d (MvPolynomial.C a : MvPolynomial V (ZMod p))).mpr
      (by simp)⟩

@[simp]
theorem coe_const (V : Type*) (p d : ℕ) (a : ZMod p) :
    ((const V p d a : PolyBoundedDeg V p d) : MvPolynomial V (ZMod p)) = MvPolynomial.C a := by
  rfl

theorem const_eq_smul_one (V : Type*) (p d : ℕ) (a : ZMod p) :
    const V p d a = a • one V p d := by
  ext
  simp [Algebra.smul_def]

theorem const_zero (V : Type*) (p d : ℕ) :
    const V p d 0 = 0 := by
  ext
  simp

theorem const_one (V : Type*) (p d : ℕ) :
    const V p d 1 = one V p d := by
  ext
  simp

/-- Single variable `X v` in `PolyBoundedDeg V p d` when `1 ≤ d`. -/
noncomputable def var {V : Type*} (p : ℕ) {d : ℕ} (hd : 1 ≤ d) (v : V) :
    PolyBoundedDeg V p d :=
  ⟨MvPolynomial.X v,
    (MvPolynomial.mem_restrictTotalDegree V d (MvPolynomial.X v : MvPolynomial V (ZMod p))).mpr
      (by
        rcases subsingleton_or_nontrivial (ZMod p) with _ | _
        · have h0 : (MvPolynomial.X v : MvPolynomial V (ZMod p)) = 0 := Subsingleton.elim _ _
          simp [h0]
        · exact (MvPolynomial.totalDegree_X v).le.trans hd)⟩

@[simp]
theorem coe_var {V : Type*} (p : ℕ) {d : ℕ} (hd : 1 ≤ d) (v : V) :
    ((var p hd v : PolyBoundedDeg V p d) : MvPolynomial V (ZMod p)) = MvPolynomial.X v := by
  rfl

/-- Inclusion of `PolyBoundedDeg V p d₁` into `PolyBoundedDeg V p d₂` for `d₁ ≤ d₂`. -/
def liftLinear {V : Type*} (p : ℕ) {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
    PolyBoundedDeg V p d₁ →ₗ[ZMod p] PolyBoundedDeg V p d₂ where
  toFun f :=
    ⟨f.1, (MvPolynomial.mem_restrictTotalDegree V d₂ f.1).mpr (f.totalDegree_le.trans h)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_liftLinear {V : Type*} (p : ℕ) {d₁ d₂ : ℕ} (h : d₁ ≤ d₂)
    (f : PolyBoundedDeg V p d₁) :
    ((liftLinear p h f : PolyBoundedDeg V p d₂) : MvPolynomial V (ZMod p)) = f.1 := by
  rfl

@[simp]
theorem liftLinear_one {V : Type*} (p : ℕ) {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
    liftLinear p h (one V p d₁) = one V p d₂ := by
  rfl

/-- Variable-renaming linear equivalence on bounded-degree polynomials. -/
noncomputable def renameEquiv {V W : Type*} (p d : ℕ) (e : V ≃ W) :
    PolyBoundedDeg V p d ≃ₗ[ZMod p] PolyBoundedDeg W p d where
  toFun f :=
    ⟨MvPolynomial.rename e f.1,
      (MvPolynomial.mem_restrictTotalDegree W d (MvPolynomial.rename e f.1)).mpr
        ((MvPolynomial.totalDegree_rename_le e f.1).trans f.totalDegree_le)⟩
  invFun g :=
    ⟨MvPolynomial.rename e.symm g.1,
      (MvPolynomial.mem_restrictTotalDegree V d (MvPolynomial.rename e.symm g.1)).mpr
        ((MvPolynomial.totalDegree_rename_le e.symm g.1).trans g.totalDegree_le)⟩
  left_inv f := by
    ext
    simp
  right_inv g := by
    ext
    simp
  map_add' f g := by
    ext
    simp
  map_smul' a f := by
    ext
    simp

@[simp]
theorem coe_renameEquiv {V W : Type*} (p d : ℕ) (e : V ≃ W) (f : PolyBoundedDeg V p d) :
    ((renameEquiv p d e f : PolyBoundedDeg W p d) : MvPolynomial W (ZMod p)) =
      MvPolynomial.rename e f.1 := by
  rfl

@[simp]
theorem renameEquiv_one {V W : Type*} (p d : ℕ) (e : V ≃ W) :
    renameEquiv p d e (one V p d) = one W p d := by
  ext
  simp

/-- Freeness of $\mathbb{F}_p^{\le d}[V]$ over $\mathbb{F}_p$ via the restricted monomial basis. -/
noncomputable scoped instance instModuleFree (V : Type*) (p d : ℕ) :
    Module.Free (ZMod p) (PolyBoundedDeg V p d) :=
  Module.Free.of_basis (MvPolynomial.basisRestrictSupport (ZMod p) _)

/-- Finiteness of $\mathbb{F}_p^{\le d}[V]$ when $V$ is finite and $p \neq 0$. -/
noncomputable scoped instance instFintype (V : Type*) [Finite V] (p d : ℕ) [NeZero p] :
    Fintype (PolyBoundedDeg V p d) :=
  @Fintype.ofFinite _
    (Module.finite_iff_finite.mp (inferInstance : Module.Finite (ZMod p) _))

end PolyBoundedDeg

end PolyBoundedDeg

section ModFrege

/-- Formulas in the propositional language $F(\mathrm{MOD}_p)$ over variable type `V`,
built from Boolean constants, atoms, negation, binary conjunction/disjunction, and unbounded-fan-in
modular counting connectives $\mathrm{MOD}_{p, r}$. -/
inductive ModFregeFormula (V : Type*) (p : ℕ) : Type _ where
  | const (b : Bool) : ModFregeFormula V p
  | atom (v : V) : ModFregeFormula V p
  | neg (φ : ModFregeFormula V p) : ModFregeFormula V p
  | conj (φ ψ : ModFregeFormula V p) : ModFregeFormula V p
  | disj (φ ψ : ModFregeFormula V p) : ModFregeFormula V p
  | mod (rem : Fin p) (args : List (ModFregeFormula V p)) : ModFregeFormula V p

namespace ModFregeFormula

/-- Custom induction principle for the nested inductive type `ModFregeFormula`. -/
@[elab_as_elim]
private def recOn' {V : Type*} {p : ℕ} {motive : ModFregeFormula V p → Sort*}
    (const : ∀ b, motive (.const b))
    (atom : ∀ v, motive (.atom v))
    (neg : ∀ φ, motive φ → motive (.neg φ))
    (conj : ∀ φ ψ, motive φ → motive ψ → motive (.conj φ ψ))
    (disj : ∀ φ ψ, motive φ → motive ψ → motive (.disj φ ψ))
    (mod : ∀ rem args, (∀ χ ∈ args, motive χ) → motive (.mod rem args)) :
    ∀ φ, motive φ
  | .const b => const b
  | .atom v => atom v
  | .neg φ => neg φ (recOn' const atom neg conj disj mod φ)
  | .conj φ ψ =>
      conj φ ψ (recOn' const atom neg conj disj mod φ)
        (recOn' const atom neg conj disj mod ψ)
  | .disj φ ψ =>
      disj φ ψ (recOn' const atom neg conj disj mod φ)
        (recOn' const atom neg conj disj mod ψ)
  | .mod rem args =>
      mod rem args fun χ _ =>
        recOn' const atom neg conj disj mod χ
termination_by φ => sizeOf φ
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := List.sizeOf_lt_of_mem ‹_›; omega)

/-- Material implication in $F(\mathrm{MOD}_p)$. -/
def imp {V : Type*} {p : ℕ} (φ ψ : ModFregeFormula V p) : ModFregeFormula V p :=
  .disj (.neg φ) ψ

/-- Material biconditional in $F(\mathrm{MOD}_p)$. -/
def iff {V : Type*} {p : ℕ} (φ ψ : ModFregeFormula V p) : ModFregeFormula V p :=
  .conj (imp φ ψ) (imp ψ φ)

/-- Repeated conjunction of a list of formulas, defaulting to `const true` on `[]`. -/
def bigConj {V : Type*} {p : ℕ} : List (ModFregeFormula V p) → ModFregeFormula V p
  | [] => .const true
  | [φ] => φ
  | φ :: ψ :: rest => .conj φ (bigConj (ψ :: rest))

/-- Truth-value evaluation of an $F(\mathrm{MOD}_p)$-formula under a Boolean assignment
`α : V → Bool`. -/
def evalBool {V : Type*} {p : ℕ} (α : V → Bool) : ModFregeFormula V p → Bool
  | .const b => b
  | .atom v => α v
  | .neg φ => !(evalBool α φ)
  | .conj φ ψ => evalBool α φ && evalBool α ψ
  | .disj φ ψ => evalBool α φ || evalBool α ψ
  | .mod rem args =>
      decide (((args.attach.countP (fun ⟨χ, _⟩ => evalBool α χ) : ℕ) : ZMod p) = (rem : ZMod p))
termination_by φ => sizeOf φ
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := List.sizeOf_lt_of_mem ‹_›; omega)

@[simp]
theorem evalBool_const {V : Type*} {p : ℕ} (α : V → Bool) (b : Bool) :
    (const b : ModFregeFormula V p).evalBool α = b := by
  rw [evalBool]

@[simp]
theorem evalBool_atom {V : Type*} {p : ℕ} (α : V → Bool) (v : V) :
    (atom v : ModFregeFormula V p).evalBool α = α v := by
  rw [evalBool]

@[simp]
theorem evalBool_neg {V : Type*} {p : ℕ} (α : V → Bool) (φ : ModFregeFormula V p) :
    (neg φ).evalBool α = !(φ.evalBool α) := by
  rw [evalBool]

@[simp]
theorem evalBool_conj {V : Type*} {p : ℕ} (α : V → Bool) (φ ψ : ModFregeFormula V p) :
    (conj φ ψ).evalBool α = (φ.evalBool α && ψ.evalBool α) := by
  rw [evalBool]

@[simp]
theorem evalBool_disj {V : Type*} {p : ℕ} (α : V → Bool) (φ ψ : ModFregeFormula V p) :
    (disj φ ψ).evalBool α = (φ.evalBool α || ψ.evalBool α) := by
  rw [evalBool]

@[simp]
theorem evalBool_mod {V : Type*} {p : ℕ} (α : V → Bool) (rem : Fin p)
    (args : List (ModFregeFormula V p)) :
    (mod rem args).evalBool α =
      decide (((args.countP (evalBool α) : ℕ) : ZMod p) = (rem : ZMod p)) := by
  rw [evalBool, List.countP_attach]

@[simp]
theorem evalBool_imp {V : Type*} {p : ℕ} (α : V → Bool) (φ ψ : ModFregeFormula V p) :
    (imp φ ψ).evalBool α = (!(φ.evalBool α) || ψ.evalBool α) := by
  rw [imp, evalBool_disj, evalBool_neg]

@[simp]
theorem evalBool_iff {V : Type*} {p : ℕ} (α : V → Bool) (φ ψ : ModFregeFormula V p) :
    (iff φ ψ).evalBool α = (φ.evalBool α == ψ.evalBool α) := by
  rw [iff, evalBool_conj, evalBool_imp, evalBool_imp]
  cases φ.evalBool α <;> cases ψ.evalBool α <;> rfl

theorem evalBool_bigConj {V : Type*} {p : ℕ} (α : V → Bool)
    (l : List (ModFregeFormula V p)) :
    (bigConj l).evalBool α = l.all (evalBool α) := by
  match l with
  | [] => simp [bigConj]
  | [φ] => simp [bigConj]
  | φ :: ψ :: rest =>
    rw [bigConj, evalBool_conj, evalBool_bigConj α (ψ :: rest)]
    simp

/-- Top-level conjuncts of a formula, flattening nested binary conjunctions. -/
def conjChildren {V : Type*} {p : ℕ} : ModFregeFormula V p → List (ModFregeFormula V p)
  | .conj φ ψ => conjChildren φ ++ conjChildren ψ
  | φ => [φ]

/-- Top-level disjuncts of a formula, flattening nested binary disjunctions. -/
def disjChildren {V : Type*} {p : ℕ} : ModFregeFormula V p → List (ModFregeFormula V p)
  | .disj φ ψ => disjChildren φ ++ disjChildren ψ
  | φ => [φ]

mutual
/-- Formula depth in $F(\mathrm{MOD}_p)$, where constants and atoms have depth `0`, unary negation
and modular counting gates add `1`, and unbounded-fan-in flattened conjunctions and disjunctions
add `1` to the maximum depth of their flattened children. -/
def depth {V : Type*} {p : ℕ} : ModFregeFormula V p → ℕ
  | .const _ => 0
  | .atom _ => 0
  | .neg φ => depth φ + 1
  | .conj φ ψ => max (conjDepth φ) (conjDepth ψ) + 1
  | .disj φ ψ => max (disjDepth φ) (disjDepth ψ) + 1
  | .mod _ args => modDepth args + 1

/-- Auxiliary depth helper flattening nested conjunctions. -/
def conjDepth {V : Type*} {p : ℕ} : ModFregeFormula V p → ℕ
  | .conj φ ψ => max (conjDepth φ) (conjDepth ψ)
  | φ => depth φ

/-- Auxiliary depth helper flattening nested disjunctions. -/
def disjDepth {V : Type*} {p : ℕ} : ModFregeFormula V p → ℕ
  | .disj φ ψ => max (disjDepth φ) (disjDepth ψ)
  | φ => depth φ

/-- Auxiliary maximum depth over a list of arguments. -/
def modDepth {V : Type*} {p : ℕ} : List (ModFregeFormula V p) → ℕ
  | [] => 0
  | χ :: rest => max (depth χ) (modDepth rest)
end

private theorem modDepth_le {V : Type*} {p : ℕ} (args : List (ModFregeFormula V p)) {d : ℕ}
    (hargs : ∀ χ ∈ args, χ.depth ≤ d) : modDepth args ≤ d := by
  induction args with
  | nil => rw [modDepth]; exact Nat.zero_le d
  | cons a t ih =>
    rw [modDepth, max_le_iff]
    exact ⟨hargs a (by simp), ih fun x hx => hargs x (by simp [hx])⟩

private theorem conjDepth_le {V : Type*} {p : ℕ} :
    (φ : ModFregeFormula V p) → ∀ {d : ℕ},
      (∀ χ ∈ conjChildren φ, χ.depth ≤ d) → conjDepth φ ≤ d
  | .const b, _, hφ => by simp only [conjDepth]; exact hφ (.const b) (by simp [conjChildren])
  | .atom v, _, hφ => by simp only [conjDepth]; exact hφ (.atom v) (by simp [conjChildren])
  | .neg φ, _, hφ => by simp only [conjDepth]; exact hφ (.neg φ) (by simp [conjChildren])
  | .conj φ ψ, _, hφ => by
    simp only [conjChildren, List.mem_append] at hφ
    rw [conjDepth, max_le_iff]
    exact ⟨conjDepth_le φ fun x hx => hφ x (Or.inl hx),
      conjDepth_le ψ fun x hx => hφ x (Or.inr hx)⟩
  | .disj φ ψ, _, hφ => by
    simp only [conjDepth]; exact hφ (.disj φ ψ) (by simp [conjChildren])
  | .mod rem args, _, hφ => by
    simp only [conjDepth]; exact hφ (.mod rem args) (by simp [conjChildren])

@[simp]
theorem depth_const {V : Type*} {p : ℕ} (b : Bool) :
    (const b : ModFregeFormula V p).depth = 0 := by
  rw [depth]

@[simp]
theorem depth_atom {V : Type*} {p : ℕ} (v : V) :
    (atom v : ModFregeFormula V p).depth = 0 := by
  rw [depth]

@[simp]
theorem depth_neg {V : Type*} {p : ℕ} (φ : ModFregeFormula V p) :
    (neg φ).depth = φ.depth + 1 := by
  rw [depth]

theorem depth_mod_le {V : Type*} {p : ℕ} (rem : Fin p)
    (args : List (ModFregeFormula V p)) {d : ℕ}
    (hargs : ∀ χ ∈ args, χ.depth ≤ d) :
    (mod rem args).depth ≤ d + 1 := by
  rw [depth]
  exact Nat.add_le_add_right (modDepth_le args hargs) 1

theorem depth_conj_le {V : Type*} {p : ℕ} (φ ψ : ModFregeFormula V p) {d : ℕ}
    (hφ : ∀ χ ∈ conjChildren φ, χ.depth ≤ d)
    (hψ : ∀ χ ∈ conjChildren ψ, χ.depth ≤ d) :
    (conj φ ψ).depth ≤ d + 1 := by
  rw [depth]
  exact Nat.add_le_add_right (max_le (conjDepth_le φ hφ) (conjDepth_le ψ hψ)) 1

private theorem conjChildren_bigConj_atoms {V : Type*} {p : ℕ} :
    (v : V) → (vs : List V) →
      ∀ χ ∈ conjChildren (bigConj ((v :: vs).map (atom (p := p)))), ∃ w, χ = atom w
  | v, [], χ, hχ => by
    simp only [List.map_cons, List.map_nil, bigConj, conjChildren, List.mem_singleton] at hχ
    exact ⟨v, hχ⟩
  | v₁, v₂ :: rest, χ, hχ => by
    rw [List.map_cons, List.map_cons, bigConj, conjChildren, List.mem_append] at hχ
    rcases hχ with h1 | h2
    · simp only [conjChildren, List.mem_singleton] at h1
      exact ⟨v₁, h1⟩
    · exact conjChildren_bigConj_atoms v₂ rest χ h2

theorem depth_bigConj_atoms_le_one {V : Type*} {p : ℕ} (vs : List V) :
    (bigConj (vs.map (atom (p := p)))).depth ≤ 1 := by
  match vs with
  | [] => simp [bigConj]
  | [v] => simp [bigConj]
  | v₁ :: v₂ :: rest =>
    rw [List.map_cons, List.map_cons, bigConj]
    refine depth_conj_le _ _ ?_ ?_
    · intro χ hχ
      simp only [conjChildren, List.mem_singleton] at hχ
      rw [hχ, depth_atom]
    · intro χ hχ
      obtain ⟨w, rfl⟩ := conjChildren_bigConj_atoms v₂ rest χ hχ
      simp

/-- Substitution of formulas for schema indices `ℕ` in $F(\mathrm{MOD}_p)$. -/
def subst {V : Type*} {p : ℕ} (σ : ℕ → ModFregeFormula V p) :
    ModFregeFormula ℕ p → ModFregeFormula V p
  | .const b => .const b
  | .atom n => σ n
  | .neg φ => .neg (subst σ φ)
  | .conj φ ψ => .conj (subst σ φ) (subst σ ψ)
  | .disj φ ψ => .disj (subst σ φ) (subst σ ψ)
  | .mod rem args => .mod rem (args.map (subst σ))
termination_by φ => sizeOf φ
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := List.sizeOf_lt_of_mem ‹_›; omega)

@[simp]
theorem subst_const {V : Type*} {p : ℕ} (σ : ℕ → ModFregeFormula V p) (b : Bool) :
    (const b : ModFregeFormula ℕ p).subst σ = const b := by
  rw [subst]

@[simp]
theorem subst_atom {V : Type*} {p : ℕ} (σ : ℕ → ModFregeFormula V p) (n : ℕ) :
    (atom n : ModFregeFormula ℕ p).subst σ = σ n := by
  rw [subst]

@[simp]
theorem subst_neg {V : Type*} {p : ℕ} (σ : ℕ → ModFregeFormula V p)
    (φ : ModFregeFormula ℕ p) :
    (neg φ).subst σ = neg (φ.subst σ) := by
  rw [subst]

@[simp]
theorem subst_conj {V : Type*} {p : ℕ} (σ : ℕ → ModFregeFormula V p)
    (φ ψ : ModFregeFormula ℕ p) :
    (conj φ ψ).subst σ = conj (φ.subst σ) (ψ.subst σ) := by
  rw [subst]

@[simp]
theorem subst_disj {V : Type*} {p : ℕ} (σ : ℕ → ModFregeFormula V p)
    (φ ψ : ModFregeFormula ℕ p) :
    (disj φ ψ).subst σ = disj (φ.subst σ) (ψ.subst σ) := by
  rw [subst]

@[simp]
theorem subst_mod {V : Type*} {p : ℕ} (σ : ℕ → ModFregeFormula V p) (rem : Fin p)
    (args : List (ModFregeFormula ℕ p)) :
    (mod rem args).subst σ = mod rem (args.map (subst σ)) := by
  rw [subst]

theorem evalBool_subst {V : Type*} {p : ℕ} (α : V → Bool)
    (σ : ℕ → ModFregeFormula V p) (φ : ModFregeFormula ℕ p) :
    (φ.subst σ).evalBool α = φ.evalBool (fun n => (σ n).evalBool α) := by
  induction φ using ModFregeFormula.recOn' with
  | const b => simp
  | atom n => simp
  | neg φ ih => simp [ih]
  | conj φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | mod rem args ih =>
    rw [subst_mod, evalBool_mod, evalBool_mod, decide_eq_decide]
    have hcnt : (args.map (subst σ)).countP (evalBool α) =
        args.countP (evalBool (fun n => (σ n).evalBool α)) := by
      induction args with
      | nil => rfl
      | cons a t iht =>
        simp only [List.map_cons, List.countP_cons]
        rw [ih a (by simp), iht (fun x hx => ih x (by simp [hx]))]
    rw [hcnt]

/-- The three $\mathrm{MOD}_p$ axiom schemas of $F(\mathrm{MOD}_p)$:
1. $\mathrm{MOD}_{p, 0}(\emptyset)$,
2. $\neg \mathrm{MOD}_{p, i}(\emptyset)$ for $1 \le i < p$,
3. $\mathrm{MOD}_{p, i}(\Gamma, \phi) \leftrightarrow
   (\mathrm{MOD}_{p, i}(\Gamma) \land \neg \phi) \lor
   (\mathrm{MOD}_{p, i-1}(\Gamma) \land \phi)$. -/
inductive IsModAxiom (V : Type*) (p : ℕ) [Fact p.Prime] : ModFregeFormula V p → Prop where
  | empty_zero : IsModAxiom V p (.mod ⟨0, (Fact.out : Nat.Prime p).pos⟩ [])
  | empty_nonzero (i : Fin p) (hi : i.1 ≠ 0) : IsModAxiom V p (.neg (.mod i []))
  | step (i : Fin p) (Γ : List (ModFregeFormula V p)) (φ : ModFregeFormula V p) :
      IsModAxiom V p
        (.iff (.mod i (Γ ++ [φ]))
          (.disj (.conj (.mod i Γ) (.neg φ))
            (.conj (.mod ⟨(i.1 + p - 1) % p, Nat.mod_lt _ (Fact.out : Nat.Prime p).pos⟩ Γ) φ)))

/-- Soundness of every $\mathrm{MOD}_p$ axiom under any Boolean valuation. -/
theorem evalBool_eq_true_of_isModAxiom {V : Type*} {p : ℕ} [Fact p.Prime]
    (α : V → Bool) {ψ : ModFregeFormula V p} (hψ : IsModAxiom V p ψ) :
    ψ.evalBool α = true := by
  cases hψ with
  | empty_zero => simp
  | empty_nonzero i hi =>
    simp only [evalBool_neg, evalBool_mod, List.countP_nil]
    by_contra h
    have heq : (((0 : ℕ) : ZMod p)) = (i : ZMod p) := of_decide_eq_true (by simpa using h)
    have hval : (((0 : ℕ) : ZMod p)).val = (i : ZMod p).val := congrArg ZMod.val heq
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.zero_mod, Nat.mod_eq_of_lt i.2] at hval
    exact hi hval.symm
  | step i Γ φ =>
    simp only [evalBool_iff, evalBool_mod, evalBool_disj, evalBool_conj, evalBool_neg,
      beq_iff_eq]
    have hcnt : (Γ ++ [φ]).countP (evalBool α) =
        Γ.countP (evalBool α) + if φ.evalBool α then 1 else 0 := by
      simp [List.countP_append]
    rw [hcnt]
    have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
    have hprev :
        (((⟨(i.1 + p - 1) % p, Nat.mod_lt _ hp_pos⟩ : Fin p) : ℕ) : ZMod p) =
          (i : ZMod p) - 1 := by
      have hsub : i.1 + p - 1 = i.1 + (p - 1) := by omega
      rw [ZMod.natCast_mod, hsub, Nat.cast_add, Nat.cast_sub hp_pos, Nat.cast_one,
        ZMod.natCast_self, sub_eq_add_neg, zero_add, ← sub_eq_add_neg]
    cases hφ : φ.evalBool α <;> simp [hprev, eq_sub_iff_add_eq]

/-- A sound schematic inference rule of a Frege system $F$. -/
structure FregeRule (p : ℕ) [Fact p.Prime] where
  /-- Schematic premise formulas indexed by schema variables `ℕ`. -/
  premises : List (ModFregeFormula ℕ p)
  /-- Schematic conclusion formula indexed by schema variables `ℕ`. -/
  conclusion : ModFregeFormula ℕ p
  sound : ∀ (β : ℕ → Bool),
    (∀ A ∈ premises, A.evalBool β = true) → conclusion.evalBool β = true

/-- A Frege calculus $F$ specified by a finite set of sound schematic inference rules. -/
structure FregeCalculus (p : ℕ) [Fact p.Prime] where
  /-- Finite set of schematic inference rules of the calculus. -/
  rules : Finset (FregeRule p)

/-- A derivation in $F_\ell(\mathrm{MOD}_p)$ from hypotheses `hyps` of depth at most
`depthBound`. -/
structure FregeDerivation {V : Type*} {p : ℕ} [Fact p.Prime]
    (F : FregeCalculus p) (hyps : Set (ModFregeFormula V p)) (depthBound : ℕ) where
  /-- Sequence of formulas constituting the derivation. -/
  steps : List (ModFregeFormula V p)
  nonempty_steps : steps ≠ []
  depth_le : ∀ φ ∈ steps, φ.depth ≤ depthBound
  step_valid : ∀ (i : ℕ) (hi : i < steps.length),
    steps[i] ∈ hyps ∨ IsModAxiom V p steps[i] ∨
      ∃ r ∈ F.rules, ∃ σ : ℕ → ModFregeFormula V p,
        steps[i] = r.conclusion.subst σ ∧
          ∀ A ∈ r.premises, ∃ (j : ℕ) (hj : j < i), steps[j] = A.subst σ

namespace FregeDerivation

/-- Number of steps in a derivation. -/
@[expose] def length {V : Type*} {p : ℕ} [Fact p.Prime] {F : FregeCalculus p}
    {hyps : Set (ModFregeFormula V p)} {depthBound : ℕ}
    (D : FregeDerivation F hyps depthBound) : ℕ :=
  D.steps.length

/-- Whether a derivation concludes `const false` (a refutation). -/
@[expose] def isRefutation {V : Type*} {p : ℕ} [Fact p.Prime] {F : FregeCalculus p}
    {hyps : Set (ModFregeFormula V p)} {depthBound : ℕ}
    (D : FregeDerivation F hyps depthBound) : Prop :=
  D.steps.getLast D.nonempty_steps = .const false

/-- Semantic soundness of $F_\ell(\mathrm{MOD}_p)$ derivations: every formula appearing in a
derivation from `hyps` evaluates to `true` under any Boolean assignment satisfying the hypotheses
actually used in `D.steps`. -/
theorem evalBool_eq_true {V : Type*} {p : ℕ} [Fact p.Prime] {F : FregeCalculus p}
    {hyps : Set (ModFregeFormula V p)} {depthBound : ℕ}
    (D : FregeDerivation F hyps depthBound) (α : V → Bool)
    (hα : ∀ φ ∈ hyps, φ ∈ D.steps → φ.evalBool α = true) :
    ∀ (i : ℕ) (hi : i < D.steps.length), D.steps[i].evalBool α = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    rcases D.step_valid i hi with h_hyp | h_mod | ⟨r, _, σ, h_conc, h_prem⟩
    · exact hα _ h_hyp (List.getElem_mem hi)
    · exact evalBool_eq_true_of_isModAxiom α h_mod
    · rw [h_conc, evalBool_subst]
      refine r.sound (fun n => (σ n).evalBool α) fun A hA => ?_
      obtain ⟨j, hj, hstep⟩ := h_prem A hA
      rw [← evalBool_subst, ← hstep]
      exact ih j hj (hj.trans hi)

/-- In any $F_\ell(\mathrm{MOD}_p)$-refutation of `hyps`, every Boolean assignment falsifies at
least one hypothesis that explicitly appears as a step in the refutation. -/
theorem exists_step_hyp_evalBool_false_of_isRefutation {V : Type*} {p : ℕ} [Fact p.Prime]
    {F : FregeCalculus p} {hyps : Set (ModFregeFormula V p)} {depthBound : ℕ}
    (D : FregeDerivation F hyps depthBound) (href : D.isRefutation) (α : V → Bool) :
    ∃ φ ∈ hyps, φ ∈ D.steps ∧ φ.evalBool α = false := by
  by_contra! h_all
  have hlast_idx : D.steps.length - 1 < D.steps.length :=
    Nat.sub_lt (List.length_pos_of_ne_nil D.nonempty_steps) Nat.one_pos
  have htrue := D.evalBool_eq_true α (fun φ hφ hmem => ?_) (D.steps.length - 1) hlast_idx
  · rw [← List.getLast_eq_getElem D.nonempty_steps, href, evalBool_const] at htrue
    exact Bool.false_ne_true htrue
  · cases hval : φ.evalBool α
    · exact False.elim (h_all φ hφ hmem hval)
    · rfl

end FregeDerivation

end ModFregeFormula

end ModFrege

/-- Conversion from `Bool` to `{0, 1} ⊆ ZMod p`. -/
@[expose] def boolToZMod (p : ℕ) (b : Bool) : ZMod p :=
  if b then 1 else 0

@[simp]
theorem boolToZMod_true (p : ℕ) : boolToZMod p true = 1 :=
  rfl

@[simp]
theorem boolToZMod_false (p : ℕ) : boolToZMod p false = 0 :=
  rfl

/-- Conjunction of atoms corresponding to the support of a monomial `m : V →₀ ℕ`. -/
noncomputable def monomialConjFormula {V : Type*} {p : ℕ} (m : V →₀ ℕ) : ModFregeFormula V p :=
  ModFregeFormula.bigConj ((Finsupp.toMultiset m).toList.map ModFregeFormula.atom)

theorem depth_monomialConjFormula_le_one {V : Type*} {p : ℕ} (m : V →₀ ℕ) :
    (monomialConjFormula (p := p) m).depth ≤ 1 :=
  ModFregeFormula.depth_bigConj_atoms_le_one _

theorem boolToZMod_evalBool_monomialConjFormula {V : Type*} (p : ℕ)
    (α : V → Bool) (m : V →₀ ℕ) :
    boolToZMod p ((monomialConjFormula (p := p) m).evalBool α) =
      ∏ v ∈ m.support, (boolToZMod p (α v)) ^ m v := by
  rw [monomialConjFormula, ModFregeFormula.evalBool_bigConj]
  by_cases hall : ∀ v ∈ m.support, α v = true
  · have hlist :
        ((Finsupp.toMultiset m).toList.map (ModFregeFormula.atom (p := p))).all
          (ModFregeFormula.evalBool α) = true := by
      rw [List.all_eq_true]
      intro χ hχ
      rcases List.mem_map.mp hχ with ⟨v, hv, rfl⟩
      rw [Multiset.mem_toList, Finsupp.mem_toMultiset] at hv
      rw [ModFregeFormula.evalBool_atom]
      exact hall v hv
    rw [hlist, boolToZMod_true]
    symm
    refine Finset.prod_eq_one fun v hv => ?_
    rw [hall v hv, boolToZMod_true, one_pow]
  · push Not at hall
    obtain ⟨v₀, hv₀, hαv₀⟩ := hall
    have hfalse : α v₀ = false := Bool.eq_false_iff.mpr hαv₀
    have hlist :
        ((Finsupp.toMultiset m).toList.map (ModFregeFormula.atom (p := p))).all
          (ModFregeFormula.evalBool α) = false := by
      rw [Bool.eq_false_iff, ne_eq, List.all_eq_true]
      push Not
      refine ⟨ModFregeFormula.atom v₀, List.mem_map.mpr ⟨v₀, ?_, rfl⟩, ?_⟩
      · rw [Multiset.mem_toList, Finsupp.mem_toMultiset]
        exact hv₀
      · simp [hfalse]
    rw [hlist, boolToZMod_false]
    symm
    refine Finset.prod_eq_zero hv₀ ?_
    rw [hfalse, boolToZMod_false, zero_pow (Finsupp.mem_support_iff.mp hv₀)]

/-- Encoding of a polynomial equation `f = 0` over `{0, 1}` valuations as a depth-`≤ 2`
formula $\mathrm{MOD}_{p, 0}(\Gamma)$ in $F(\mathrm{MOD}_p)$. -/
noncomputable def polyEqZeroFormula {V : Type*} {p : ℕ} [Fact p.Prime]
    (f : MvPolynomial V (ZMod p)) : ModFregeFormula V p :=
  .mod ⟨0, (Fact.out : Nat.Prime p).pos⟩
    (f.support.toList.flatMap fun m => List.replicate (f.coeff m).val (monomialConjFormula m))

theorem depth_polyEqZeroFormula_le_two {V : Type*} {p : ℕ} [Fact p.Prime]
    (f : MvPolynomial V (ZMod p)) :
    (polyEqZeroFormula f).depth ≤ 2 := by
  rw [polyEqZeroFormula]
  refine ModFregeFormula.depth_mod_le _ _ fun χ hχ => ?_
  rw [List.mem_flatMap] at hχ
  obtain ⟨m, _, hm⟩ := hχ
  rw [List.mem_replicate] at hm
  rw [hm.2]
  exact depth_monomialConjFormula_le_one m

theorem evalBool_polyEqZeroFormula_iff {V : Type*} {p : ℕ} [Fact p.Prime]
    (f : MvPolynomial V (ZMod p)) (α : V → Bool) :
    (polyEqZeroFormula f).evalBool α = true ↔
      MvPolynomial.eval (fun v => boolToZMod p (α v)) f = 0 := by
  rw [polyEqZeroFormula, ModFregeFormula.evalBool_mod, decide_eq_true_eq]
  have hcount :
      (((f.support.toList.flatMap fun m =>
          List.replicate (f.coeff m).val (monomialConjFormula (p := p) m)).countP
          (ModFregeFormula.evalBool α) : ℕ) : ZMod p) =
        MvPolynomial.eval (fun v => boolToZMod p (α v)) f := by
    have hmap :
        (f.support.toList.map
          (List.countP (ModFregeFormula.evalBool α) ∘ fun m =>
            List.replicate (f.coeff m).val (monomialConjFormula (p := p) m))) =
        f.support.toList.map fun m =>
          if (monomialConjFormula (p := p) m).evalBool α then (f.coeff m).val else 0 := by
      refine List.map_congr_left fun m _ => ?_
      simp [List.countP_replicate]
    rw [List.countP_flatMap, hmap, Nat.cast_list_sum, List.map_map, Function.comp_def,
      Finset.sum_map_toList, MvPolynomial.eval_eq]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← boolToZMod_evalBool_monomialConjFormula p α m]
    cases (monomialConjFormula (p := p) m).evalBool α <;> simp
  rw [hcount]
  simp

end CslibFrontier.Logic.PL.ENS
