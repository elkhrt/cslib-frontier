module

public import CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.Circuit
public import CslibFrontier.Computability.Circuit.Formula
public import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Noncommutative Algebraic Formulas

This module defines binary-tree noncommutative algebraic formulas over a commutative semiring or
ring, their syntactic complexity invariants (`size`, `depth`, `leafCount`, `mulCount`, `vars`,
`varCount`), substitution and variable renaming, homogeneous component extraction `homogPart` in
`FreeAlgebra`, evaluations in `FreeAlgebra`, `MvPolynomial`, and arbitrary `F`-algebras, and a
canonical equivalence with `Cslib.Circuits.Formula` over `arithSignature`.

## Main definitions

* `CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.NoncommFormula`: binary-tree
  noncommutative algebraic formulas.
* `CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.homogPart`: degree-`d` homogeneous
  component in `FreeAlgebra`.
* `CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.NoncommFormula.eval`, `evalComm`,
  `evalAlg`: evaluations in `FreeAlgebra`, `MvPolynomial`, and arbitrary `F`-algebras.
* `CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.NoncommFormula.equivCslibFormula`:
  equivalence with `Cslib.Circuits.Formula (arithSignature F) n`.
-/

public section

namespace CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative

open Cslib.Circuits Cslib.Circuits.Arithmetic FreeAlgebra

/-! ### Noncommutative algebraic formulas -/

/-- A noncommutative algebraic formula over scalars `F` and variables `V` :
a rooted binary tree whose leaves are field constants or variables and whose internal nodes are
addition or ordered multiplication gates. -/
inductive NoncommFormula (F V : Type*) : Type _
  /-- A constant leaf `c ∈ F`. -/
  | const (c : F) : NoncommFormula F V
  /-- A variable leaf `x_v`. -/
  | var (v : V) : NoncommFormula F V
  /-- An addition gate `l + r`. -/
  | add (l r : NoncommFormula F V) : NoncommFormula F V
  /-- An ordered (noncommutative) multiplication gate `l * r`. -/
  | mul (l r : NoncommFormula F V) : NoncommFormula F V
  deriving DecidableEq

/-! ### Homogeneous components in `FreeAlgebra` -/

section HomogPart

variable {F V : Type*} [CommSemiring F]

private theorem coeff_eq_repr (a : FreeAlgebra F V) (w : FreeMonoid V) :
    FreeAlgebra.coeff w a = ((FreeAlgebra.basisFreeMonoid F V).repr a) w := by
  classical
  have hsum := ((FreeAlgebra.basisFreeMonoid F V).linearCombination_repr a).symm
  conv_lhs => rw [hsum]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  have hterm : ∀ w' : FreeMonoid V,
      FreeAlgebra.coeff w (((FreeAlgebra.basisFreeMonoid F V).repr a) w' •
        FreeAlgebra.basisFreeMonoid F V w') =
        if w' = w then ((FreeAlgebra.basisFreeMonoid F V).repr a) w else 0 := fun w' => by
    rw [map_smul, FreeAlgebra.basisFreeMonoid_apply, FreeAlgebra.coeff_lift_ι, smul_eq_mul]
    by_cases h : w' = w
    · subst h; simp
    · simp [Finsupp.single_eq_of_ne' h, h]
  simp only [hterm, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hm).symm

/-- The degree-`d` homogeneous component of a noncommutative polynomial in `FreeAlgebra F V`,
retaining all monomials of word length `d`. -/
noncomputable def homogPart (d : ℕ) (a : FreeAlgebra F V) : FreeAlgebra F V :=
  (FreeAlgebra.basisFreeMonoid F V).repr.symm
    (Finsupp.filter (fun w : FreeMonoid V => w.toList.length = d)
      ((FreeAlgebra.basisFreeMonoid F V).repr a))

/-- The coefficient of `w` in `homogPart d a` is `coeff w a` when `|w| = d` and `0` otherwise. -/
theorem coeff_homogPart (d : ℕ) (a : FreeAlgebra F V) (w : FreeMonoid V) :
    FreeAlgebra.coeff w (homogPart d a) =
      if w.toList.length = d then FreeAlgebra.coeff w a else 0 := by
  classical
  rw [coeff_eq_repr, homogPart, LinearEquiv.apply_symm_apply, Finsupp.filter_apply, coeff_eq_repr]

/-- `homogPart d a` is homogeneous of degree `d`. -/
theorem isHomogeneous_homogPart (d : ℕ) (a : FreeAlgebra F V) :
    (homogPart d a).IsHomogeneous d := by
  intro w hw
  rw [coeff_homogPart] at hw
  by_contra hne
  exact hw (by simp [hne])

/-- `homogPart d` preserves `0`. -/
@[simp] theorem homogPart_zero (d : ℕ) : homogPart d (0 : FreeAlgebra F V) = 0 := by
  apply FreeAlgebra.ext_coeff
  intro w
  simp [coeff_homogPart]

/-- `homogPart d` is additive. -/
theorem homogPart_add (d : ℕ) (a b : FreeAlgebra F V) :
    homogPart d (a + b) = homogPart d a + homogPart d b := by
  apply FreeAlgebra.ext_coeff
  intro w
  simp only [map_add, coeff_homogPart]
  split_ifs <;> simp

/-- `homogPart d` commutes with scalar multiplication. -/
theorem homogPart_smul (d : ℕ) (c : F) (a : FreeAlgebra F V) :
    homogPart d (c • a) = c • homogPart d a := by
  apply FreeAlgebra.ext_coeff
  intro w
  simp only [map_smul, coeff_homogPart, smul_eq_mul]
  split_ifs <;> simp

/-- `homogPart d` fixes every homogeneous polynomial of degree `d`. -/
theorem homogPart_eq_self_of_isHomogeneous {d : ℕ} {a : FreeAlgebra F V}
    (ha : a.IsHomogeneous d) : homogPart d a = a := by
  apply FreeAlgebra.ext_coeff
  intro w
  rw [coeff_homogPart]
  split_ifs with h
  · rfl
  · exact (ha.coeff_eq_zero h).symm

/-- `homogPart d` annihilates any homogeneous polynomial of degree `e ≠ d`. -/
theorem homogPart_eq_zero_of_isHomogeneous_ne {d e : ℕ} {a : FreeAlgebra F V}
    (ha : a.IsHomogeneous e) (hne : e ≠ d) : homogPart d a = 0 := by
  apply FreeAlgebra.ext_coeff
  intro w
  rw [coeff_homogPart, map_zero]
  split_ifs with h
  · exact ha.coeff_eq_zero (by omega)
  · rfl

/-- `homogPart d` of a finite sum of homogeneous polynomials of distinct degrees picks out the
degree-`d` summand. -/
theorem homogPart_sum_of_isHomogeneous {N : ℕ} {f : ℕ → FreeAlgebra F V}
    (hf : ∀ k < N, (f k).IsHomogeneous k) {d : ℕ} (hd : d < N) :
    homogPart d (∑ k ∈ Finset.range N, f k) = f d := by
  apply FreeAlgebra.ext_coeff
  intro w
  rw [coeff_homogPart, map_sum]
  split_ifs with hw
  · rw [Finset.sum_eq_single d]
    · intro k hk hkd
      exact (hf k (Finset.mem_range.mp hk)).coeff_eq_zero (by omega)
    · intro h
      exact absurd (Finset.mem_range.mpr hd) h
  · exact ((hf d hd).coeff_eq_zero hw).symm

/-- A polynomial vanishes iff all of its homogeneous components vanish. -/
theorem eq_zero_iff_forall_homogPart (a : FreeAlgebra F V) :
    a = 0 ↔ ∀ d : ℕ, homogPart d a = 0 := by
  refine ⟨fun h d => by simp [h], fun h => FreeAlgebra.ext_coeff fun w => ?_⟩
  have hw := congrArg (FreeAlgebra.coeff w) (h w.toList.length)
  simpa [coeff_homogPart] using hw

/-- `homogPart 0 a` equals `algebraMap F _ (coeff 1 a)`. -/
theorem homogPart_zero_eq_algebraMap (a : FreeAlgebra F V) :
    homogPart 0 a = algebraMap F (FreeAlgebra F V) (FreeAlgebra.coeff 1 a) := by
  apply FreeAlgebra.ext_coeff
  intro w
  rw [coeff_homogPart, FreeAlgebra.coeff_algebraMap]
  by_cases hw : w = 1
  · subst hw; simp
  · have hlen : w.toList.length ≠ 0 := by
      intro h
      exact hw (FreeMonoid.ext (List.length_eq_zero_iff.mp h))
    simp [hlen, Finsupp.single_eq_of_ne hw]

end HomogPart

namespace NoncommFormula

section Basic

variable {F V : Type*}

/-- The total number of nodes in the underlying tree of a noncommutative formula. -/
@[expose] def size : NoncommFormula F V → ℕ
  | const _ => 1
  | var _ => 1
  | add l r => l.size + r.size + 1
  | mul l r => l.size + r.size + 1

/-- The depth of a noncommutative formula (maximal path length from root to leaf). -/
@[expose] def depth : NoncommFormula F V → ℕ
  | const _ => 0
  | var _ => 0
  | add l r => max l.depth r.depth + 1
  | mul l r => max l.depth r.depth + 1

/-- The number of leaves (constants and variables) in a formula. -/
@[expose] def leafCount : NoncommFormula F V → ℕ
  | const _ => 1
  | var _ => 1
  | add l r => l.leafCount + r.leafCount
  | mul l r => l.leafCount + r.leafCount

/-- The number of multiplication gates in a formula. -/
@[expose] def mulCount : NoncommFormula F V → ℕ
  | const _ => 0
  | var _ => 0
  | add l r => l.mulCount + r.mulCount
  | mul l r => l.mulCount + r.mulCount + 1

/-- Every formula has size at least `1`. -/
theorem one_le_size (Φ : NoncommFormula F V) : 1 ≤ Φ.size := by
  cases Φ <;> simp [size]

/-- Every formula has at least one leaf. -/
theorem one_le_leafCount (Φ : NoncommFormula F V) : 1 ≤ Φ.leafCount := by
  induction Φ with
  | const _ | var _ => simp [leafCount]
  | add l r ihl ihr | mul l r ihl ihr => simp [leafCount]; omega

/-- The node count of a binary tree equals `2 * leafCount - 1`. -/
theorem size_add_one_eq_two_mul_leafCount (Φ : NoncommFormula F V) :
    Φ.size + 1 = 2 * Φ.leafCount := by
  induction Φ with
  | const _ | var _ => simp [size, leafCount]
  | add l r ihl ihr | mul l r ihl ihr => simp [size, leafCount]; omega

/-- `mulCount + 1 ≤ leafCount`. -/
theorem mulCount_add_one_le_leafCount (Φ : NoncommFormula F V) :
    Φ.mulCount + 1 ≤ Φ.leafCount := by
  induction Φ with
  | const _ | var _ => simp [mulCount, leafCount]
  | add l r ihl ihr | mul l r ihl ihr => simp [mulCount, leafCount]; omega

/-- `2 * mulCount + 1 ≤ size`. -/
theorem two_mul_mulCount_add_one_le_size (Φ : NoncommFormula F V) :
    2 * Φ.mulCount + 1 ≤ Φ.size := by
  have h1 := Φ.size_add_one_eq_two_mul_leafCount
  have h2 := Φ.mulCount_add_one_le_leafCount
  omega

/-- `mulCount + 1 ≤ size`. -/
theorem mulCount_add_one_le_size (Φ : NoncommFormula F V) :
    Φ.mulCount + 1 ≤ Φ.size := by
  have := Φ.two_mul_mulCount_add_one_le_size
  omega

/-- Scalar multiplication formula `c * Φ`. -/
@[expose] def smul (c : F) (Φ : NoncommFormula F V) : NoncommFormula F V :=
  .mul (.const c) Φ

/-- Subtraction formula `l + (-1) * r`. -/
@[expose] def sub [Ring F] (l r : NoncommFormula F V) : NoncommFormula F V :=
  .add l (.mul (.const (-1)) r)

/-- Size of a scalar multiple formula. -/
@[simp] theorem size_smul (c : F) (Φ : NoncommFormula F V) :
    (Φ.smul c).size = Φ.size + 2 := by
  simp [smul, size]; omega

/-- Size of a subtraction formula. -/
@[simp] theorem size_sub [Ring F] (l r : NoncommFormula F V) :
    (l.sub r).size = l.size + r.size + 3 := by
  simp [sub, size]; omega

/-- The finset of variables syntactically occurring in a formula. -/
@[expose] def vars [DecidableEq V] : NoncommFormula F V → Finset V
  | const _ => ∅
  | var v => {v}
  | add l r => l.vars ∪ r.vars
  | mul l r => l.vars ∪ r.vars

/-- The number of syntactic occurrences of a variable `z` in a formula. -/
@[expose] def varCount [DecidableEq V] (z : V) : NoncommFormula F V → ℕ
  | const _ => 0
  | var v => if v = z then 1 else 0
  | add l r => l.varCount z + r.varCount z
  | mul l r => l.varCount z + r.varCount z

/-- A variable occurs in `Φ.vars` iff its occurrence count is positive. -/
theorem mem_vars_iff_varCount_pos [DecidableEq V] {z : V} {Φ : NoncommFormula F V} :
    z ∈ Φ.vars ↔ 0 < Φ.varCount z := by
  induction Φ with
  | const _ => simp [vars, varCount]
  | var v =>
    by_cases h : v = z
    · subst h; simp [vars, varCount]
    · simp [vars, varCount, h, Ne.symm h]
  | add l r ihl ihr | mul l r ihl ihr =>
    simp only [vars, varCount, Finset.mem_union, ihl, ihr]
    omega

/-- Syntactic substitution `Φ[h / z]`, replacing every leaf `var z` by `h`. -/
@[expose] def subst [DecidableEq V] (Φ : NoncommFormula F V) (z : V) (h : NoncommFormula F V) :
    NoncommFormula F V :=
  match Φ with
  | const c => const c
  | var v => if v = z then h else var v
  | add l r => add (l.subst z h) (r.subst z h)
  | mul l r => mul (l.subst z h) (r.subst z h)

/-- Substituting for a variable not occurring in `Φ` leaves `Φ` unchanged. -/
theorem subst_of_varCount_eq_zero [DecidableEq V] {z : V} {h Φ : NoncommFormula F V}
    (hz : Φ.varCount z = 0) : Φ.subst z h = Φ := by
  induction Φ with
  | const _ => rfl
  | var v =>
    simp only [varCount] at hz
    have hv : v ≠ z := by intro heq; simp [heq] at hz
    simp [subst, hv]
  | add l r ihl ihr | mul l r ihl ihr =>
    simp only [varCount, Nat.add_eq_zero_iff] at hz
    simp [subst, ihl hz.1, ihr hz.2]

/-- Size of `Φ[h / z]` in terms of `varCount z`. -/
theorem size_subst [DecidableEq V] (z : V) (h Φ : NoncommFormula F V) :
    (Φ.subst z h).size + Φ.varCount z = Φ.size + Φ.varCount z * h.size := by
  induction Φ with
  | const _ => simp [subst, size, varCount]
  | var v =>
    by_cases hv : v = z
    · subst hv; simp [subst, size, varCount]; omega
    · simp [subst, size, varCount, hv]
  | add l r ihl ihr | mul l r ihl ihr =>
    simp only [subst, size, varCount, Nat.add_mul]
    omega

/-- Substituting a constant for a variable preserves formula size. -/
theorem size_subst_const [DecidableEq V] (z : V) (c : F) (Φ : NoncommFormula F V) :
    (Φ.subst z (.const c)).size = Φ.size := by
  have h := size_subst z (.const c) Φ
  have hc : (const c : NoncommFormula F V).size = 1 := rfl
  rw [hc, mul_one] at h
  omega

/-- Variables of `Φ[const c / z]` are `Φ.vars.erase z`. -/
theorem vars_subst_const [DecidableEq V] (z : V) (c : F) (Φ : NoncommFormula F V) :
    (Φ.subst z (.const c)).vars = Φ.vars.erase z := by
  induction Φ with
  | const _ => simp [subst, vars]
  | var v =>
    by_cases hv : v = z
    · subst hv; simp [subst, vars]
    · have hne : z ≠ v := Ne.symm hv
      simp [subst, vars, hv, Finset.erase_eq_of_notMem, hne]
  | add l r ihl ihr | mul l r ihl ihr =>
    simp [subst, vars, ihl, ihr, Finset.erase_union_distrib]

/-- Simultaneous substitution of formulas for all variables. -/
@[expose] def bind {W : Type*} (f : V → NoncommFormula F W) :
    NoncommFormula F V → NoncommFormula F W
  | const c => const c
  | var v => f v
  | add l r => add (l.bind f) (r.bind f)
  | mul l r => mul (l.bind f) (r.bind f)

/-- Renaming variables of a formula. -/
@[expose] def rename {W : Type*} (f : V → W) (Φ : NoncommFormula F V) : NoncommFormula F W :=
  Φ.bind fun v => var (f v)

/-- Renaming variables preserves formula size. -/
@[simp] theorem size_rename {W : Type*} (f : V → W) (Φ : NoncommFormula F V) :
    (Φ.rename f).size = Φ.size := by
  induction Φ with
  | const _ | var _ => rfl
  | add l r ihl ihr | mul l r ihl ihr =>
    exact congrArg (· + 1) (congrArg₂ (· + ·) ihl ihr)

/-- Size bound when substituting formulas of size at most `k` for each variable. -/
theorem size_bind_le {W : Type*} {f : V → NoncommFormula F W} {k : ℕ}
    (hk : ∀ v, (f v).size ≤ k) (Φ : NoncommFormula F V) :
    (Φ.bind f).size ≤ (k + 1) * Φ.size := by
  induction Φ with
  | const _ => simp [bind, size]
  | var v =>
    simp only [bind, size, mul_one]
    exact (hk v).trans (Nat.le_succ k)
  | add l r ihl ihr | mul l r ihl ihr =>
    simp only [bind, size, Nat.mul_add, mul_one]
    omega

/-- Sum of a list of noncommutative formulas (associated to the right). -/
@[expose] def sumList [Zero F] : List (NoncommFormula F V) → NoncommFormula F V
  | [] => .const 0
  | [Φ] => Φ
  | Φ :: Ψ :: rest => .add Φ (sumList (Ψ :: rest))

/-- Product of a list of noncommutative formulas (associated to the right). -/
@[expose] def prodList [One F] : List (NoncommFormula F V) → NoncommFormula F V
  | [] => .const 1
  | [Φ] => Φ
  | Φ :: Ψ :: rest => .mul Φ (prodList (Ψ :: rest))

/-- Size bound for `sumList`. -/
theorem size_sumList_le [Zero F] (ls : List (NoncommFormula F V)) :
    (sumList ls).size ≤ (ls.map size).sum + ls.length + 1 := by
  match ls with
  | [] => simp [sumList, size]
  | [Φ] => simp [sumList]; omega
  | Φ :: Ψ :: rest =>
    have ih := size_sumList_le (Ψ :: rest)
    simp only [sumList, size, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

/-- Size bound for `prodList`. -/
theorem size_prodList_le [One F] (ls : List (NoncommFormula F V)) :
    (prodList ls).size ≤ (ls.map size).sum + ls.length + 1 := by
  match ls with
  | [] => simp [prodList, size]
  | [Φ] => simp [prodList]; omega
  | Φ :: Ψ :: rest =>
    have ih := size_prodList_le (Ψ :: rest)
    simp only [prodList, size, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

end Basic

section Eval

variable {F V : Type*} [CommSemiring F]

/-- Evaluation of a noncommutative formula in `FreeAlgebra F V`. -/
@[expose] noncomputable def eval : NoncommFormula F V → FreeAlgebra F V
  | const c => algebraMap F (FreeAlgebra F V) c
  | var v => FreeAlgebra.ι F v
  | add l r => l.eval + r.eval
  | mul l r => l.eval * r.eval

/-- Evaluation of a formula as a commutative polynomial in `MvPolynomial V F`. -/
@[expose] noncomputable def evalComm : NoncommFormula F V → MvPolynomial V F
  | const c => MvPolynomial.C c
  | var v => MvPolynomial.X v
  | add l r => l.evalComm + r.evalComm
  | mul l r => l.evalComm * r.evalComm

/-- Evaluation of a noncommutative formula in an arbitrary (possibly noncommutative) `F`-algebra. -/
@[expose] def evalAlg {A : Type*} [Semiring A] [Algebra F A] (x : V → A) :
    NoncommFormula F V → A
  | const c => algebraMap F A c
  | var v => x v
  | add l r => l.evalAlg x + r.evalAlg x
  | mul l r => l.evalAlg x * r.evalAlg x

/-- Evaluation of a constant leaf in `FreeAlgebra`. -/
@[simp] theorem eval_const (c : F) : (const c : NoncommFormula F V).eval = algebraMap F _ c := rfl

/-- Evaluation of a variable leaf in `FreeAlgebra`. -/
@[simp] theorem eval_var (v : V) : (var v : NoncommFormula F V).eval = FreeAlgebra.ι F v := rfl

/-- Evaluation of an addition gate in `FreeAlgebra`. -/
@[simp] theorem eval_add (l r : NoncommFormula F V) : (add l r).eval = l.eval + r.eval := rfl

/-- Evaluation of a multiplication gate in `FreeAlgebra`. -/
@[simp] theorem eval_mul (l r : NoncommFormula F V) : (mul l r).eval = l.eval * r.eval := rfl

/-- Commutative evaluation of a constant leaf. -/
@[simp] theorem evalComm_const (c : F) :
    (const c : NoncommFormula F V).evalComm = MvPolynomial.C c := rfl

/-- Commutative evaluation of a variable leaf. -/
@[simp] theorem evalComm_var (v : V) :
    (var v : NoncommFormula F V).evalComm = MvPolynomial.X v := rfl

/-- Commutative evaluation of an addition gate. -/
@[simp] theorem evalComm_add (l r : NoncommFormula F V) :
    (add l r).evalComm = l.evalComm + r.evalComm := rfl

/-- Commutative evaluation of a multiplication gate. -/
@[simp] theorem evalComm_mul (l r : NoncommFormula F V) :
    (mul l r).evalComm = l.evalComm * r.evalComm := rfl

/-- Evaluation of a scalar multiple in `FreeAlgebra`. -/
@[simp] theorem eval_smul (c : F) (Φ : NoncommFormula F V) :
    (Φ.smul c).eval = c • Φ.eval := by
  simp [smul, Algebra.smul_def]

/-- Commutative evaluation of a scalar multiple. -/
@[simp] theorem evalComm_smul (c : F) (Φ : NoncommFormula F V) :
    (Φ.smul c).evalComm = MvPolynomial.C c * Φ.evalComm := rfl

/-- Evaluation of a subtraction formula in `FreeAlgebra`. -/
@[simp] theorem eval_sub {K : Type*} [CommRing K] (l r : NoncommFormula K V) :
    (l.sub r).eval = l.eval - r.eval := by
  simp [sub, map_neg, map_one, sub_eq_add_neg]

/-- Commutative evaluation of a subtraction formula. -/
@[simp] theorem evalComm_sub {K : Type*} [CommRing K] (l r : NoncommFormula K V) :
    (l.sub r).evalComm = l.evalComm - r.evalComm := by
  simp [sub, map_neg, map_one, sub_eq_add_neg]

/-- Evaluation of `sumList` is the sum of evaluations. -/
theorem eval_sumList (ls : List (NoncommFormula F V)) :
    (sumList ls).eval = (ls.map eval).sum := by
  match ls with
  | [] => simp [sumList]
  | [Φ] => simp [sumList]
  | Φ :: Ψ :: rest =>
    rw [sumList, eval_add, eval_sumList (Ψ :: rest)]
    rfl

/-- Commutative evaluation of `sumList` is the sum of commutative evaluations. -/
theorem evalComm_sumList (ls : List (NoncommFormula F V)) :
    (sumList ls).evalComm = (ls.map evalComm).sum := by
  match ls with
  | [] => simp [sumList]
  | [Φ] => simp [sumList]
  | Φ :: Ψ :: rest =>
    rw [sumList, evalComm_add, evalComm_sumList (Ψ :: rest)]
    rfl

/-- Evaluation of `prodList` is the product of evaluations. -/
theorem eval_prodList (ls : List (NoncommFormula F V)) :
    (prodList ls).eval = (ls.map eval).prod := by
  match ls with
  | [] => simp [prodList]
  | [Φ] => simp [prodList]
  | Φ :: Ψ :: rest =>
    rw [prodList, eval_mul, eval_prodList (Ψ :: rest)]
    rfl

/-- Commutative evaluation of `prodList` is the product of commutative evaluations. -/
theorem evalComm_prodList (ls : List (NoncommFormula F V)) :
    (prodList ls).evalComm = (ls.map evalComm).prod := by
  match ls with
  | [] => simp [prodList]
  | [Φ] => simp [prodList]
  | Φ :: Ψ :: rest =>
    rw [prodList, evalComm_mul, evalComm_prodList (Ψ :: rest)]
    rfl

/-- Lifting an `F`-algebra assignment `x : V → A` along `FreeAlgebra.lift` agrees with `evalAlg`. -/
theorem lift_eval_eq_evalAlg {A : Type*} [Semiring A] [Algebra F A] (x : V → A)
    (Φ : NoncommFormula F V) : FreeAlgebra.lift F x Φ.eval = Φ.evalAlg x := by
  induction Φ with
  | const c => simp [eval, evalAlg]
  | var v => simp [eval, evalAlg]
  | add l r ihl ihr => simp [eval, evalAlg, ihl, ihr]
  | mul l r ihl ihr => simp [eval, evalAlg, ihl, ihr]

/-- Abelianizing `Φ.eval` yields `Φ.evalComm`. -/
theorem lift_X_eval (Φ : NoncommFormula F V) :
    FreeAlgebra.lift F (MvPolynomial.X : V → MvPolynomial V F) Φ.eval = Φ.evalComm := by
  induction Φ with
  | const c => simp [eval, evalComm, MvPolynomial.algebraMap_eq]
  | var v => simp [eval, evalComm]
  | add l r ihl ihr => simp [eval, evalComm, ihl, ihr]
  | mul l r ihl ihr => simp [eval, evalComm, ihl, ihr]

/-- Evaluating a formula at `0` recovers its constant term `coeff 1 Φ.eval`. -/
theorem evalAlg_zero_eq_coeff_one (Φ : NoncommFormula F V) :
    Φ.evalAlg (fun _ => (0 : F)) = FreeAlgebra.coeff 1 Φ.eval := by
  induction Φ with
  | const c => simp [evalAlg, eval, FreeAlgebra.coeff_algebraMap]
  | var v =>
    have hne : FreeMonoid.of v ≠ (1 : FreeMonoid V) := by
      intro h
      have := congrArg (fun w : FreeMonoid V => w.toList.length) h
      simp at this
    rw [evalAlg, eval_var, FreeAlgebra.coeff_ι, Finsupp.single_eq_of_ne' hne]
  | add l r ihl ihr => simp [evalAlg, eval, map_add, ihl, ihr]
  | mul l r ihl ihr =>
    simp only [evalAlg, eval, FreeAlgebra.coeff_mul, FreeMonoid.toList_one, List.length_nil,
      Nat.zero_add, Finset.range_one, Finset.sum_singleton, List.take_nil, List.drop_nil,
      FreeMonoid.ofList_nil, ihl, ihr]

/-- Evaluation of `Φ.bind f` lifts `fun v => (f v).eval`. -/
theorem eval_bind {W : Type*} (f : V → NoncommFormula F W) (Φ : NoncommFormula F V) :
    (Φ.bind f).eval = FreeAlgebra.lift F (fun v => (f v).eval) Φ.eval := by
  induction Φ with
  | const c => simp [bind, eval]
  | var v => simp [bind, eval]
  | add l r ihl ihr => simp [bind, eval, ihl, ihr]
  | mul l r ihl ihr => simp [bind, eval, ihl, ihr]

/-- Commutative evaluation of `Φ.bind f` lifts `fun v => (f v).evalComm`. -/
theorem evalComm_bind {W : Type*} (f : V → NoncommFormula F W) (Φ : NoncommFormula F V) :
    (Φ.bind f).evalComm = MvPolynomial.aeval (fun v => (f v).evalComm) Φ.evalComm := by
  induction Φ with
  | const c => simp [bind, evalComm]
  | var v => simp [bind, evalComm]
  | add l r ihl ihr => simp [bind, evalComm, ihl, ihr]
  | mul l r ihl ihr => simp [bind, evalComm, ihl, ihr]

/-- Evaluation of `Φ.subst z h` lifts substituting `h.eval` for `z`. -/
theorem eval_subst [DecidableEq V] (z : V) (h Φ : NoncommFormula F V) :
    (Φ.subst z h).eval =
      FreeAlgebra.lift F (fun v => if v = z then h.eval else FreeAlgebra.ι F v) Φ.eval := by
  induction Φ with
  | const c => simp [subst, eval]
  | var v => by_cases hv : v = z <;> simp [subst, eval, hv]
  | add l r ihl ihr => simp [subst, eval, ihl, ihr]
  | mul l r ihl ihr => simp [subst, eval, ihl, ihr]

private theorem lift_zeroVar_basisFreeMonoid [DecidableEq V] (z : V) (w' : FreeMonoid V) :
    FreeAlgebra.lift F (fun v => if v = z then (0 : FreeAlgebra F V) else FreeAlgebra.ι F v)
      (FreeAlgebra.basisFreeMonoid F V w') =
      if z ∈ w'.toList then 0 else FreeAlgebra.basisFreeMonoid F V w' := by
  simp only [FreeAlgebra.basisFreeMonoid_apply]
  suffices ∀ l : List V,
      FreeAlgebra.lift F (fun v => if v = z then (0 : FreeAlgebra F V) else FreeAlgebra.ι F v)
        (FreeMonoid.lift (FreeAlgebra.ι F) (FreeMonoid.ofList l)) =
        if z ∈ l then 0 else FreeMonoid.lift (FreeAlgebra.ι F) (FreeMonoid.ofList l) by
    simpa [FreeMonoid.ofList_toList] using this w'.toList
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    have hcons : FreeMonoid.ofList (a :: t) = FreeMonoid.of a * FreeMonoid.ofList t := rfl
    rw [hcons, map_mul, map_mul, FreeMonoid.lift_eval_of, FreeAlgebra.lift_ι_apply, ih]
    by_cases ha : a = z
    · subst ha; simp
    · by_cases ht : z ∈ t <;> simp [ha, ht, Ne.symm ha]

/-- Substituting `0` for `z` in a `FreeAlgebra` element zeroes out exactly words containing `z`. -/
theorem coeff_lift_zeroVar [DecidableEq V] (z : V) (a : FreeAlgebra F V) (w : FreeMonoid V) :
    FreeAlgebra.coeff w
      (FreeAlgebra.lift F (fun v => if v = z then (0 : FreeAlgebra F V) else FreeAlgebra.ι F v)
        a) = if z ∈ w.toList then 0 else FreeAlgebra.coeff w a := by
  classical
  have hsum := ((FreeAlgebra.basisFreeMonoid F V).linearCombination_repr a).symm
  conv_lhs => rw [hsum]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_sum]
  have hterm : ∀ w' : FreeMonoid V,
      FreeAlgebra.coeff w
        (FreeAlgebra.lift F
          (fun v => if v = z then (0 : FreeAlgebra F V) else FreeAlgebra.ι F v)
          (((FreeAlgebra.basisFreeMonoid F V).repr a) w' •
            FreeAlgebra.basisFreeMonoid F V w')) =
        if w' = w then (if z ∈ w.toList then 0 else FreeAlgebra.coeff w a) else 0 := by
    intro w'
    rw [map_smul, lift_zeroVar_basisFreeMonoid]
    by_cases hww : w' = w
    · subst hww
      by_cases hz : z ∈ w'.toList
      · simp [hz]
      · simp only [hz, ↓reduceIte, map_smul, FreeAlgebra.basisFreeMonoid_apply,
          FreeAlgebra.coeff_lift_ι, Finsupp.single_eq_same, smul_eq_mul, mul_one]
        exact (coeff_eq_repr a w').symm
    · by_cases hz : z ∈ w'.toList
      · simp [hz, hww]
      · simp only [hz, hww, ↓reduceIte, map_smul, FreeAlgebra.basisFreeMonoid_apply,
          FreeAlgebra.coeff_lift_ι, Finsupp.single_eq_of_ne' hww, smul_zero]
  simp only [hterm, Finset.sum_ite_eq']
  split_ifs with hmem hz
  · rfl
  · rfl
  · rfl
  · rw [coeff_eq_repr]
    exact (Finsupp.notMem_support_iff.mp hmem).symm

/-- Substituting `0` for `z` in a formula zeroes out exactly the words containing `z`. -/
theorem coeff_eval_subst_zero [DecidableEq V] (z : V) (Φ : NoncommFormula F V)
    (w : FreeMonoid V) :
    FreeAlgebra.coeff w (Φ.subst z (.const 0)).eval =
      if z ∈ w.toList then 0 else FreeAlgebra.coeff w Φ.eval := by
  rw [eval_subst]
  simpa only [eval_const, map_zero] using coeff_lift_zeroVar z Φ.eval w

/-- Every word with nonzero coefficient in `Φ.eval` has length at most `Φ.mulCount + 1`. -/
theorem length_le_mulCount_add_one_of_coeff_ne_zero (Φ : NoncommFormula F V)
    {w : FreeMonoid V} (hw : FreeAlgebra.coeff w Φ.eval ≠ 0) :
    w.toList.length ≤ Φ.mulCount + 1 := by
  induction Φ generalizing w with
  | const c =>
    rw [eval_const, FreeAlgebra.coeff_algebraMap] at hw
    by_cases h1 : w = 1
    · simp [h1, mulCount]
    · exact absurd (Finsupp.single_eq_of_ne h1) hw
  | var v =>
    rw [eval_var, FreeAlgebra.coeff_ι] at hw
    by_cases h1 : w = FreeMonoid.of v
    · simp [h1, mulCount]
    · exact absurd (Finsupp.single_eq_of_ne h1) hw
  | add l r ihl ihr =>
    rw [eval_add, map_add] at hw
    by_cases hl : FreeAlgebra.coeff w l.eval = 0
    · rw [hl, zero_add] at hw
      have := ihr hw
      simp [mulCount]; omega
    · have := ihl hl
      simp [mulCount]; omega
  | mul l r ihl ihr =>
    rw [eval_mul, FreeAlgebra.coeff_mul] at hw
    obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    have h1 := ihl (left_ne_zero_of_mul hne)
    have h2 := ihr (right_ne_zero_of_mul hne)
    simp only [List.length_take, List.length_drop, Finset.mem_range] at h1 h2 hi
    simp [mulCount]; omega

/-- A formula vanishes iff its homogeneous components of degrees `0, ..., Φ.mulCount + 1` vanish. -/
theorem eval_eq_zero_iff_forall_homogPart (Φ : NoncommFormula F V) :
    Φ.eval = 0 ↔ ∀ d ≤ Φ.mulCount + 1, homogPart d Φ.eval = 0 := by
  refine ⟨fun h d _ => by simp [h], fun h => (eq_zero_iff_forall_homogPart _).2 fun d => ?_⟩
  by_cases hd : d ≤ Φ.mulCount + 1
  · exact h d hd
  · apply FreeAlgebra.ext_coeff
    intro w
    rw [coeff_homogPart, map_zero]
    split_ifs with hw
    · by_contra hne
      have := Φ.length_le_mulCount_add_one_of_coeff_ne_zero hne
      omega
    · rfl

/-- Every word with nonzero coefficient in `Φ.eval` uses only variables syntactically in `Φ`. -/
theorem mem_vars_of_coeff_ne_zero [DecidableEq V] (Φ : NoncommFormula F V)
    {w : FreeMonoid V} (hw : FreeAlgebra.coeff w Φ.eval ≠ 0) {v : V} (hv : v ∈ w.toList) :
    v ∈ Φ.vars := by
  induction Φ generalizing w with
  | const c =>
    rw [eval_const, FreeAlgebra.coeff_algebraMap] at hw
    by_cases h1 : w = 1
    · subst h1; simp at hv
    · exact absurd (Finsupp.single_eq_of_ne h1) hw
  | var u =>
    rw [eval_var, FreeAlgebra.coeff_ι] at hw
    by_cases h1 : w = FreeMonoid.of u
    · subst h1; simp only [FreeMonoid.toList_of, List.mem_singleton] at hv; simp [vars, hv]
    · exact absurd (Finsupp.single_eq_of_ne h1) hw
  | add l r ihl ihr =>
    rw [eval_add, map_add] at hw
    simp only [vars, Finset.mem_union]
    by_cases hl : FreeAlgebra.coeff w l.eval = 0
    · rw [hl, zero_add] at hw; exact Or.inr (ihr hw hv)
    · exact Or.inl (ihl hl hv)
  | mul l r ihl ihr =>
    rw [eval_mul, FreeAlgebra.coeff_mul] at hw
    obtain ⟨i, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    simp only [vars, Finset.mem_union]
    have hmem : v ∈ w.toList.take i ++ w.toList.drop i := by rwa [List.take_append_drop]
    rcases List.mem_append.1 hmem with h1 | h2
    · exact Or.inl (ihl (left_ne_zero_of_mul hne) (by simpa using h1))
    · exact Or.inr (ihr (right_ne_zero_of_mul hne) (by simpa using h2))

/-- Conversion to `Cslib.Circuits.Formula (arithSignature F) n`. -/
@[expose] def toCslibFormula {n : ℕ} :
    NoncommFormula F (Fin n) → Formula (arithSignature F) n
  | const c => Formula.gate (.const c) Fin.elim0
  | var v => Formula.input v
  | add l r => Formula.gate₂ .add rfl l.toCslibFormula r.toCslibFormula
  | mul l r => Formula.gate₂ .mul rfl l.toCslibFormula r.toCslibFormula

/-- Conversion from `Cslib.Circuits.Formula (arithSignature F) n`. -/
@[expose] def ofCslibFormula {n : ℕ} :
    Formula (arithSignature F) n → NoncommFormula F (Fin n)
  | Formula.input v => var v
  | Formula.gate (.const c) _ => const c
  | Formula.gate .add args => add (ofCslibFormula (args 0)) (ofCslibFormula (args 1))
  | Formula.gate .mul args => mul (ofCslibFormula (args 0)) (ofCslibFormula (args 1))

/-- Equivalence between `NoncommFormula F (Fin n)` and
`Cslib.Circuits.Formula (arithSignature F) n`. -/
@[expose] def equivCslibFormula {n : ℕ} :
    NoncommFormula F (Fin n) ≃ Formula (arithSignature F) n where
  toFun := toCslibFormula
  invFun := ofCslibFormula
  left_inv Φ := by
    induction Φ with
    | const _ | var _ => rfl
    | add l r ihl ihr => simp [toCslibFormula, ofCslibFormula, Formula.gate₂, ihl, ihr]
    | mul l r ihl ihr => simp [toCslibFormula, ofCslibFormula, Formula.gate₂, ihl, ihr]
  right_inv F := by
    induction F with
    | input _ => rfl
    | gate op args ih =>
      cases op with
      | const c =>
        simp only [ofCslibFormula, toCslibFormula]
        congr 1
        funext i
        exact Fin.elim0 i
      | add =>
        simp only [ofCslibFormula, toCslibFormula, Formula.gate₂]
        congr 1
        funext j
        fin_cases j <;> simp [ih]
      | mul =>
        simp only [ofCslibFormula, toCslibFormula, Formula.gate₂]
        congr 1
        funext j
        fin_cases j <;> simp [ih]

/-- Evaluating `Φ.toCslibFormula.toCircuit` as a noncommutative polynomial agrees with `Φ.eval`. -/
theorem toCircuit_noncommPolynomial_eq_eval {n : ℕ} (Φ : NoncommFormula F (Fin n)) :
    Φ.toCslibFormula.toCircuit.noncommPolynomial 0 = Φ.eval := by
  rw [Circuit.noncommPolynomial_eq_eval, Formula.eval_toCircuit]
  induction Φ with
  | const c => rfl
  | var v => rfl
  | add l r ihl ihr => simp [toCslibFormula, ihl, ihr]
  | mul l r ihl ihr => simp [toCslibFormula, ihl, ihr]

end Eval

end NoncommFormula

end CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative
