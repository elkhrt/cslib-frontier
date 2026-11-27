module

public import CslibFrontier.Computability.Complexity.Problems.CoveringRadius
public import CslibFrontier.Computability.Complexity.Parameterized
import CslibFrontier.Computability.Complexity.FineGrained.ExhaustiveSearch
import CslibFrontier.Computability.PolyTime.LinearAlgebra.RationalElimination
import CslibFrontier.Foundations.LinearAlgebra.Matrix.IntegerKernel
import CslibFrontier.Foundations.Data.Int.Radix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import Mathlib.Data.Finset.Card
import Mathlib.Order.WellFounded

/-!
# Binary Closest String is Fixed-Parameter Tractable in the Number of Strings

This module formalizes the binary **Closest String** decision problem, proves that
`CoveringRadius` parameterized by the number of codewords `|C|` fpt-reduces to
`BinaryClosestString` parameterized by the number of strings, and proves directly under standard
Lean axioms that `BinaryClosestString` belongs to `FPT` parameterized by the number of strings
.

The FPT algorithm uses the column-type integer linear program with `p = 2 ^ m` column types,
the bounded-kernel independent-large-coordinates theorem
(`exists_int_mulVec_eq_zero_of_not_injective` and `Int.eq_zero_of_sum_mul_pow_eq_zero`),
`Cslib.LinearAlgebra.ratSolve` (polynomial-time Bareiss–Jordan rational linear system solving),
and `DecidableInExpTime.of_exhaustiveSearch`.

## Main definitions

- `ClosestStringInstance`, `encClosestString`: binary closest-string instances and encoding.
- `BinaryClosestString`: the binary closest-string decision language.

## Main results

- `fptReducible_CoveringRadius_BinaryClosestString`: `CoveringRadius` (param `|C|`) fpt-reduces to
  `BinaryClosestString` (param `|strings|`).
- `BinaryClosestString_mem_FPT`: `BinaryClosestString ∈ FPT encClosestString (·.strings.length)`.
-/

public section

namespace Cslib.Complexity

open Cslib.LinearAlgebra Turing.MultiTapeTM ComputableInPolyTime Finset
open scoped Matrix

private theorem getD_eq_getElem_of_lt {α : Type*} {l : List α} {i : ℕ} {d : α}
    (hi : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

private theorem testBit_foldr_bit (l : List Bool) (i : ℕ) :
    (l.foldr Nat.bit 0).testBit i = l.getD i false := by
  induction l generalizing i with
  | nil => simp
  | cons b tl ih =>
    cases i with
    | zero =>
      simp only [List.foldr_cons, Nat.testBit_zero, Nat.bit_val, List.getD_cons_zero]
      cases b <;> simp
    | succ i =>
      rw [List.foldr_cons, Nat.testBit_succ, Nat.bit_val]
      have hdiv : (2 * tl.foldr Nat.bit 0 + b.toNat) / 2 = tl.foldr Nat.bit 0 := by
        cases b <;> (simp only [Bool.toNat_false, Bool.toNat_true, add_zero]; omega)
      rw [hdiv, ih]
      rfl

/-! ### Binary Closest String Problem Definition -/

/-- An instance of the binary **Closest String** problem: common string length `len`, list of
binary strings `strings`, and maximum Hamming distance `radius`. -/
@[ext]
structure ClosestStringInstance where
  /-- Common bit-length of all strings. -/
  len : ℕ
  /-- Explicit list of binary input strings. -/
  strings : List (List Bool)
  /-- Maximum allowed Hamming distance. -/
  radius : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Encoding of `ClosestStringInstance`: unary `len`, framed list of bit strings `strings`, and
binary `radius`. -/
enc_structure encClosestString : ClosestStringInstance where
  len : encUnary,
  strings : (encList encBits),
  radius : encNat

attribute [fun_prop] encClosestString_len_polyTime encClosestString_strings_polyTime
  encClosestString_radius_polyTime encClosestString_mk_polyTime

/-- Well-formedness of a closest-string instance: every string has length `len`. -/
@[expose]
def ClosestStringInstance.WellFormed (x : ClosestStringInstance) : Prop :=
  ∀ s ∈ x.strings, s.length = x.len

/-- The binary **Closest String** decision problem: is there a length-`len` binary string at
Hamming distance at most `radius` from every string in `strings`? -/
@[expose]
def BinaryClosestString : Set ClosestStringInstance :=
  {x | x.WellFormed ∧ ∃ v : List Bool, v.length = x.len ∧
    ∀ s ∈ x.strings, hammingDist v s ≤ x.radius}

/-- Polynomial-time well-formedness check for `ClosestStringInstance`. -/
@[expose]
def validClosestString (x : ClosestStringInstance) : Bool :=
  x.strings.all fun s => decide (s.length = x.len)

theorem validClosestString_eq_true_iff (x : ClosestStringInstance) :
    validClosestString x = true ↔ x.WellFormed := by
  simp [validClosestString, ClosestStringInstance.WellFormed]

@[fun_prop]
theorem computableInPolyTime_validClosestString :
    ComputableInPolyTime validClosestString encClosestString encBool := by
  unfold validClosestString
  exact allWithInput (encClosestString_strings_polyTime id')
    (decide_eq' (length_bits.comp (snd _ _)) (encClosestString_len_polyTime (fst _ _)))

/-! ### FPT Reduction from Covering Radius to Binary Closest String -/

/-- Well-formedness check for `CoveringRadiusInstance`. -/
@[expose]
def validCoveringRadius (x : CoveringRadiusInstance) : Bool :=
  x.code.all fun c => decide (c.length = x.len)

private theorem validCoveringRadius_eq_true_iff (x : CoveringRadiusInstance) :
    validCoveringRadius x = true ↔ x.WellFormed := by
  simp [validCoveringRadius, CoveringRadiusInstance.WellFormed]

/-- Map a `CoveringRadiusInstance` to a `ClosestStringInstance` by complementing each codeword
and setting radius `n - r - 1` (handling empty codes and `r ≥ n` directly). -/
@[expose]
def coveringRadiusToClosestString (x : CoveringRadiusInstance) : ClosestStringInstance :=
  if validCoveringRadius x then
    if x.code.isEmpty then ⟨0, [], 0⟩
    else if decide (x.len ≤ x.radius) then ⟨0, [[true]], 0⟩
    else ⟨x.len, x.code.map (List.map (!·)), x.len - x.radius - 1⟩
  else ⟨0, [[true]], 0⟩

/-- `CoveringRadius` parameterized by `|C|` fpt-reduces to `BinaryClosestString` parameterized by
`|strings|`. -/
theorem fptReducible_CoveringRadius_BinaryClosestString :
    FPTReducible encCoveringRadius encClosestString
      (fun x => x.code.length) (fun x => x.strings.length)
      CoveringRadius BinaryClosestString := by
  have hpoly : ComputableInPolyTime coveringRadiusToClosestString
      encCoveringRadius encClosestString := by
    have hval : ComputableInPolyTime validCoveringRadius encCoveringRadius encBool := by
      unfold validCoveringRadius
      exact allWithInput (encCoveringRadius_code_polyTime id')
        (decide_eq' (length_bits.comp (snd _ _)) (encCoveringRadius_len_polyTime (fst _ _)))
    have hempty : ComputableInPolyTime (fun x : CoveringRadiusInstance => x.code.isEmpty)
        encCoveringRadius encBool :=
      (listIsEmpty' encBits).comp (encCoveringRadius_code_polyTime id')
    have hle : ComputableInPolyTime (fun x : CoveringRadiusInstance => decide (x.len ≤ x.radius))
        encCoveringRadius encBool :=
      binary_le.comp ((unary_to_binary.comp (encCoveringRadius_len_polyTime id')).prod
        (encCoveringRadius_radius_polyTime id'))
    have hcomp : ComputableInPolyTime
        (fun x : CoveringRadiusInstance => x.code.map (List.map (!·)))
        encCoveringRadius (encList encBits) :=
      mapWithInput (encCoveringRadius_code_polyTime id')
        (listToBits.comp (mapWithInput (bitsToList.comp (snd _ _)) (bool_not.comp (snd _ _))))
    have hrad : ComputableInPolyTime
        (fun x : CoveringRadiusInstance => x.len - x.radius - 1)
        encCoveringRadius encNat :=
      binary_sub' (binary_sub' (unary_to_binary.comp (encCoveringRadius_len_polyTime id'))
        (encCoveringRadius_radius_polyTime id')) (const 1)
    unfold coveringRadiusToClosestString
    exact hval.ite
      (hempty.ite (const (⟨0, [], 0⟩ : ClosestStringInstance))
        (hle.ite (const (⟨0, [[true]], 0⟩ : ClosestStringInstance))
          (encClosestString_mk_polyTime (encCoveringRadius_len_polyTime id') hcomp hrad)))
      (const (⟨0, [[true]], 0⟩ : ClosestStringInstance))
  refine FPTReducible.of_computableInPolyTime hpoly (h := fun m => m + 1)
    (fun x => ?_) (fun x => ?_)
  · unfold coveringRadiusToClosestString
    split_ifs <;> simp only [List.length_nil, List.length_cons, List.length_map] <;> omega
  · by_cases hWF : x.WellFormed
    · have hv : validCoveringRadius x = true := (validCoveringRadius_eq_true_iff x).mpr hWF
      by_cases hemp : x.code.isEmpty
      · have hnil : x.code = [] := List.isEmpty_iff.mp hemp
        simp only [coveringRadiusToClosestString, hv, hemp, ↓reduceIte]
        constructor
        · intro _
          exact ⟨(fun _ h => nomatch h), [], rfl, fun _ h => nomatch h⟩
        · intro _
          refine ⟨hWF, List.replicate x.len false, List.length_replicate, fun c hc => ?_⟩
          rw [hnil] at hc; exact nomatch hc
      · have hne : x.code ≠ [] := mt List.isEmpty_iff.mpr hemp
        by_cases hle : x.len ≤ x.radius
        · simp only [coveringRadiusToClosestString, hv, hemp, hle, decide_true, ↓reduceIte,
            Bool.false_eq_true]
          constructor
          · rintro ⟨_, v, hvlen, hgt⟩
            obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil x.code hne
            have hdist : hammingDist v c ≤ x.len := by
              rw [← hvlen]; simpa [hammingDist] using List.countP_le_length (l :=
                List.range v.length)
            have := hgt c hc; omega
          · rintro ⟨hbad, _⟩
            have := hbad [true] (List.mem_singleton_self _); simp at this
        · have hlt : x.radius < x.len := Nat.lt_of_not_le hle
          simp only [coveringRadiusToClosestString, hv, hemp, hle, decide_false, ↓reduceIte,
            Bool.false_eq_true]
          constructor
          · rintro ⟨_, v, hvlen, hgt⟩
            refine ⟨fun s hs => ?_, v, hvlen, fun s hs => ?_⟩
            · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
              simpa using hWF c hc
            · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
              have hclen := hWF c hc
              rw [hammingDist_map_not (hvlen.trans hclen.symm), hvlen]
              have := hgt c hc; dsimp only; omega
          · rintro ⟨_, v, hvlen, hle'⟩
            dsimp only at hvlen hle'
            refine ⟨hWF, v, hvlen, fun c hc => ?_⟩
            have hclen := hWF c hc
            have hd := hle' (c.map (!·)) (List.mem_map.mpr ⟨c, hc, rfl⟩)
            rw [hammingDist_map_not (hvlen.trans hclen.symm), hvlen] at hd
            have hbound : hammingDist v c ≤ x.len := by
              rw [← hvlen]; simpa [hammingDist] using List.countP_le_length (l :=
                List.range v.length)
            omega
    · have hv : validCoveringRadius x = false :=
        Bool.eq_false_iff.mpr (mt (validCoveringRadius_eq_true_iff x).mp hWF)
      simp only [coveringRadiusToClosestString, hv, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro hx; exact (hWF hx.1).elim
      · rintro ⟨hbad, _⟩
        have := hbad [true] (List.mem_singleton_self _); simp at this

/-! ### Independent-Large-Coordinates Integer Programming Lemma -/

/-- If an integer equality system `A *ᵥ x₀ = b, x₀ ≥ 0` with `|A i j| ≤ B` has a nonnegative
integer solution, then it has one whose large coordinates (`≥ K`, where `K` depends only on the
matrix dimensions and `B`,
  NOT on `b`) correspond to linearly independent columns of `A` over `ℚ`. -/
theorem exists_nonneg_int_solution_independent_large {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℤ} {b : Fin m → ℤ} {B : ℕ}
    (hA : ∀ i j, |A i j| ≤ B) {x₀ : Fin n → ℤ} (hx₀ : 0 ≤ x₀) (hAx₀ : A *ᵥ x₀ = b) :
    ∃ x : Fin n → ℤ, 0 ≤ x ∧ A *ᵥ x = b ∧
      Function.Injective
        ((A.submatrix id (fun j : {j //
          (n.factorial * (m * ((n + 1) * B) ^ 2 + 1) ^ n : ℕ) ≤ x j} => j.1)).map
          (Int.cast : ℤ → ℚ)).mulVecLin := by
  classical
  let K := n.factorial * (m * ((n + 1) * B) ^ 2 + 1) ^ n
  let cost (x : Fin n → ℤ) : ℤ := ∑ j, x j * (K + 1 : ℤ) ^ j.val
  let S : Set (Fin n → ℤ) := {x | 0 ≤ x ∧ A *ᵥ x = b}
  have hS : S.Nonempty := ⟨x₀, hx₀, hAx₀⟩
  let x := Function.argminOn (fun x => (cost x).toNat) S hS
  have hxS : x ∈ S := Function.argminOn_mem _ S hS
  obtain ⟨hx, hAx⟩ := hxS
  have hcost : ∀ y : Fin n → ℤ, 0 ≤ y → 0 ≤ cost y := fun y hy =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hy j) (by positivity)
  have hmin : ∀ y, 0 ≤ y → A *ᵥ y = b → cost x ≤ cost y := fun y hy hAy => by
    have h : (cost x).toNat ≤ (cost y).toNat :=
      Function.argminOn_le (fun x => (cost x).toNat) S ⟨hy, hAy⟩
    have := hcost x hx
    have := hcost y hy
    omega
  refine ⟨x, hx, hAx, ?_⟩
  by_contra hinj
  let J := {j : Fin n // (K : ℤ) ≤ x j}
  let AJ : Matrix (Fin m) J ℤ := A.submatrix id Subtype.val
  obtain ⟨cJ, hcJ, hAcJ, hcJB⟩ := Matrix.exists_int_mulVec_eq_zero_of_not_injective AJ
    (fun i j => hA i j.1) (r := n) (by
      calc Fintype.card J ≤ Fintype.card (Fin n) := Fintype.card_subtype_le _
        _ ≤ n + 1 := by simp) hinj
  let c : Fin n → ℤ := fun j => if hj : (K : ℤ) ≤ x j then cJ ⟨j, hj⟩ else 0
  have hcB (j : Fin n) : |c j| ≤ x j ∧ |c j| ≤ K := by
    by_cases hj : (K : ℤ) ≤ x j
    · have h : |cJ ⟨j, hj⟩| ≤ K := by simpa only [Fintype.card_fin] using hcJB ⟨j, hj⟩
      simpa only [c, dite_eq_left hj] using ⟨h.trans hj, h⟩
    · simpa [c, hj] using hx j
  have hAc : A *ᵥ c = 0 := by
    ext i
    change ∑ j, A i j * c j = 0
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j => (K : ℤ) ≤ x j)]
    have hzero : ∑ j : {j : Fin n // ¬(K : ℤ) ≤ x j}, A i j.1 * c j.1 = 0 :=
      Finset.sum_eq_zero fun j _ => by simp [c, j.2]
    rw [hzero, add_zero]
    have heq : ∀ j : J, c j.1 = cJ j := fun j => by simp [c, j.2]
    simpa only [AJ, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq, heq,
      Pi.zero_apply] using congrFun hAcJ i
  have hplus : 0 ≤ x + c := fun j => by
    change 0 ≤ x j + c j
    linarith [(abs_le.mp (hcB j).1).1]
  have hminus : 0 ≤ x - c := fun j => sub_nonneg.mpr (le_abs_self _ |>.trans (hcB j).1)
  have h1 := hmin (x + c) hplus (by rw [Matrix.mulVec_add, hAx, hAc, add_zero])
  have h2 := hmin (x - c) hminus (by rw [Matrix.mulVec_sub, hAx, hAc, sub_zero])
  have hcost_add : cost (x + c) = cost x + cost c := by
    simp [cost, add_mul, Finset.sum_add_distrib]
  have hcost_sub : cost (x - c) = cost x - cost c := by
    simp [cost, sub_mul, Finset.sum_sub_distrib]
  have hc0 : cost c = 0 := by linarith
  have hc_eq : c = 0 := by
    let a : ℕ → ℤ := fun j => if hj : j < n then c ⟨j, hj⟩ else 0
    have hsum : ∑ j ∈ Finset.range n, a j * (K + 1 : ℤ) ^ j = 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      simpa [a, cost] using hc0
    have h := Int.eq_zero_of_sum_mul_pow_eq_zero (a := a)
      (fun j hj => by simpa [a, hj] using Int.lt_add_one_iff.mpr (hcB ⟨j, hj⟩).2) hsum
    funext j
    simpa [a, j.isLt] using h j j.isLt
  exact hcJ (funext fun j => by simpa [c, j.2] using congrFun hc_eq j.1)

/-! ### Column-Type ILP Formulation of Binary Closest String -/

/-- Number of column types `p = 2 ^ m`. -/
@[expose] def csNumTypes (m : ℕ) : ℕ := 2 ^ m

/-- Number of equations `p + m` in the column-type ILP. -/
@[expose] def csNumRows (m : ℕ) : ℕ := 2 ^ m + m

/-- Number of variables `2 * p + m` in the column-type ILP. -/
@[expose] def csNumCols (m : ℕ) : ℕ := 2 * 2 ^ m + m

/-- Bit-width allocated for each small coordinate (`< K`). -/
@[expose] def csSmallBits (m : ℕ) : ℕ := 10 * (csNumCols m + 1) ^ 2

/-- Total branching bits for the ILP solver: `N' + N' * w`. -/
@[expose] def csTotalBits (m : ℕ) : ℕ := csNumCols m + csNumCols m * csSmallBits m

/-- Column type of column `j` in `strings`, encoded as a natural `< 2 ^ strings.length` whose
`i`-th bit is `(strings.getD i []).getD j false`. -/
@[expose]
def colType (strings : List (List Bool)) (j : ℕ) : ℕ :=
  ofBits (strings.map fun s => s.getD j false)

theorem colType_lt (strings : List (List Bool)) (j : ℕ) :
    colType strings j < 2 ^ strings.length := by
  unfold colType ofBits
  have h := Nat.foldr_bit_lt (strings.map fun s => s.getD j false)
  simpa only [List.length_map] using h

theorem colType_testBit (strings : List (List Bool)) (j i : ℕ)
    (hi : i < strings.length) :
    (colType strings j).testBit i = (strings.getD i []).getD j false := by
  unfold colType ofBits
  rw [testBit_foldr_bit, getD_eq_getElem_of_lt (by simpa only [List.length_map] using hi),
    List.getElem_map, getD_eq_getElem_of_lt hi]

/-- Entry `(i, j)` of the `{0, 1}` column-type ILP matrix for `m` strings (`p = 2 ^ m`). -/
@[expose]
def csEntry (_m p i j : ℕ) : ℤ :=
  if i < p then
    if j = i ∨ j = p + i then 1 else 0
  else
    let i' := i - p
    if j < p then
      if j.testBit i' then 0 else 1
    else if j < 2 * p then
      if (j - p).testBit i' then 1 else 0
    else
      if j = 2 * p + i' then 1 else 0

theorem abs_csEntry_le_one (m p i j : ℕ) : |csEntry m p i j| ≤ 1 := by
  unfold csEntry
  repeat (first | split_ifs | norm_num)

/-- Column-type ILP matrix `A` for `m` strings. -/
@[expose]
def csMatrix (m : ℕ) : Matrix (Fin (csNumRows m)) (Fin (csNumCols m)) ℤ :=
  Matrix.of fun i j => csEntry m (2 ^ m) i.val j.val

/-- Right-hand side `b` of the column-type ILP for `x`. -/
@[expose]
def csRHS (x : ClosestStringInstance) : Fin (csNumRows x.strings.length) → ℤ :=
  fun i =>
    if i.val < 2 ^ x.strings.length then
      ((List.range x.len).countP (fun j => colType x.strings j == i.val) : ℤ)
    else
      (min x.radius x.len : ℤ)

/-- Equivalence between `BinaryClosestString` and feasibility of the column-type ILP. -/
theorem closestString_iff_ilp (x : ClosestStringInstance) (_hWF : x.WellFormed) :
    (∃ v : List Bool, v.length = x.len ∧ ∀ s ∈ x.strings, hammingDist v s ≤ x.radius) ↔
    ∃ z : Fin (csNumCols x.strings.length) → ℤ,
      0 ≤ z ∧ csMatrix x.strings.length *ᵥ z = csRHS x := by
  set m := x.strings.length
  set p := 2 ^ m
  set r := min x.radius x.len
  have hp : 2 ^ x.strings.length = p := rfl
  have hcols : csNumCols m = 2 * p + m := rfl
  have hrows : csNumRows m = p + m := rfl
  constructor
  · rintro ⟨v, hvlen, hv⟩
    let zNat : ℕ → ℕ := fun j =>
      if j < p then
        (List.range x.len).countP fun col => colType x.strings col == j && v.getD col false
      else if j < 2 * p then
        (List.range x.len).countP fun col =>
          colType x.strings col == (j - p) && !(v.getD col false)
      else
        r - hammingDist v (x.strings.getD (j - 2 * p) [])
    refine ⟨fun j => (zNat j.val : ℤ), fun j => Int.natCast_nonneg _, ?_⟩
    ext i
    simp only [csMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, csRHS, hp]
    by_cases hi : i.val < p
    · simp only [hi, ↓reduceIte, csEntry]
      have h1 : (⟨i.val, by rw [hcols]; omega⟩ : Fin (csNumCols m)) ≠
          ⟨p + i.val, by rw [hcols]; omega⟩ := by
        intro h; have := congrArg Fin.val h; dsimp only at this; omega
      have hsum :
          ∑ j : Fin (csNumCols m),
            (if j.val = i.val ∨ j.val = p + i.val then (1 : ℤ) else 0) * (zNat j.val : ℤ) =
          (zNat i.val : ℤ) + (zNat (p + i.val) : ℤ) := by
        have hsub : ∀ j : Fin (csNumCols m),
            (if j.val = i.val ∨ j.val = p + i.val then (1 : ℤ) else 0) * (zNat j.val : ℤ) =
            (if j = ⟨i.val, by rw [hcols]; omega⟩ then (zNat i.val : ℤ) else 0) +
            (if j = ⟨p + i.val, by rw [hcols]; omega⟩ then (zNat (p + i.val) : ℤ) else 0) :=
          fun j => by
            by_cases hji : j = ⟨i.val, by rw [hcols]; omega⟩
            · rw [hji]; simp [h1]
            · by_cases hjp : j = ⟨p + i.val, by rw [hcols]; omega⟩
              · rw [hjp]; simp [h1.symm]
              · have hne1 : j.val ≠ i.val := fun h => hji (Fin.ext h)
                have hne2 : j.val ≠ p + i.val := fun h => hjp (Fin.ext h)
                simp only [hji, hjp, hne1, hne2, or_self, ↓reduceIte, zero_mul, add_zero]
        simp_rw [hsub]
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
        simp
      rw [hsum]
      norm_cast
      have hsub1 : p + i.val < 2 * p := by omega
      have hnot : ¬(p + i.val < p) := by omega
      simp only [zNat, hi, ↓reduceIte, hnot, hsub1, Nat.add_sub_cancel_left]
      have hsplit := List.length_eq_countP_add_countP (fun col => v.getD col false)
        (l := (List.range x.len).filter fun col => colType x.strings col == i.val)
      have hc1 : (List.range x.len).countP
          (fun col => colType x.strings col == i.val && v.getD col false) =
          ((List.range x.len).filter fun col => colType x.strings col == i.val).countP
            (fun col => v.getD col false) := by
        rw [List.countP_filter]; exact List.countP_congr fun _ _ => by simp [Bool.and_comm]
      have hc2 : (List.range x.len).countP
          (fun col => colType x.strings col == i.val && !(v.getD col false)) =
          ((List.range x.len).filter fun col => colType x.strings col == i.val).countP
            (fun col => decide (¬v.getD col false = true)) := by
        rw [List.countP_filter]; exact List.countP_congr fun _ _ => by simp [Bool.and_comm]
      rw [hc1, hc2, ← hsplit, ← List.countP_eq_length_filter]
    · have hilt : i.val - p < m := by
        have : i.val < p + m := i.isLt; omega
      simp only [hi, ↓reduceIte, csEntry]
      -- Split the sum over `j : Fin (2 * p + m)` into `j < p`, `p ≤ j < 2p`, and `2p ≤ j`.
      have hsum_split :
          ∑ j : Fin (csNumCols m),
            (if j.val < p then if j.val.testBit (i.val - p) then (0 : ℤ) else 1
             else if j.val < 2 * p then if (j.val - p).testBit (i.val - p) then 1 else 0
             else if j.val = 2 * p + (i.val - p) then 1 else 0) * (zNat j.val : ℤ) =
          (∑ τ ∈ Finset.range p,
            if τ.testBit (i.val - p) then (zNat (p + τ) : ℤ) else (zNat τ : ℤ)) +
          (zNat (2 * p + (i.val - p)) : ℤ) := by
        rw [Fin.sum_univ_eq_sum_range
          (f := fun k =>
            (if k < p then if k.testBit (i.val - p) then (0 : ℤ) else 1
             else if k < 2 * p then if (k - p).testBit (i.val - p) then 1 else 0
             else if k = 2 * p + (i.val - p) then 1 else 0) * (zNat k : ℤ))]
        rw [hcols, Finset.sum_range_add,
          show 2 * p = p + p from by omega, Finset.sum_range_add]
        have hA : ∑ k ∈ Finset.range p,
            (if k < p then if k.testBit (i.val - p) then (0 : ℤ) else 1
             else if k < p + p then if (k - p).testBit (i.val - p) then 1 else 0
             else if k = p + p + (i.val - p) then 1 else 0) * (zNat k : ℤ) =
            ∑ τ ∈ Finset.range p, if τ.testBit (i.val - p) then 0 else (zNat τ : ℤ) := by
          refine Finset.sum_congr rfl fun τ hτ => ?_
          have hτlt := Finset.mem_range.mp hτ
          simp only [hτlt, ↓reduceIte]
          split_ifs <;> simp
        have hB : ∑ k ∈ Finset.range p,
            (if p + k < p then if (p + k).testBit (i.val - p) then (0 : ℤ) else 1
             else if p + k < p + p then if (p + k - p).testBit (i.val - p) then 1 else 0
             else if p + k = p + p + (i.val - p) then 1 else 0) * (zNat (p + k) : ℤ) =
            ∑ τ ∈ Finset.range p, if τ.testBit (i.val - p) then (zNat (p + τ) : ℤ) else 0 := by
          refine Finset.sum_congr rfl fun τ hτ => ?_
          have hτlt := Finset.mem_range.mp hτ
          have h1 : ¬(p + τ < p) := by omega
          have h2 : p + τ < p + p := by omega
          simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
          split_ifs <;> simp
        have hC : ∑ k ∈ Finset.range m,
            (if 2 * p + k < p then if (2 * p + k).testBit (i.val - p) then (0 : ℤ) else 1
             else if 2 * p + k < 2 * p then if (2 * p + k - p).testBit (i.val - p) then 1 else 0
             else if 2 * p + k = 2 * p + (i.val - p) then 1 else 0) * (zNat (2 * p + k) : ℤ) =
            (zNat (2 * p + (i.val - p)) : ℤ) := by
          have hsub : ∀ k ∈ Finset.range m,
              (if 2 * p + k < p then if (2 * p + k).testBit (i.val - p) then (0 : ℤ) else 1
               else if 2 * p + k < 2 * p then if (2 * p + k - p).testBit (i.val - p) then 1 else 0
               else if 2 * p + k = 2 * p + (i.val - p) then 1 else 0) * (zNat (2 * p + k) : ℤ) =
              if k = i.val - p then (zNat (2 * p + (i.val - p)) : ℤ) else 0 := fun k _ => by
            have h1 : ¬(2 * p + k < p) := by omega
            have h2 : ¬(2 * p + k < 2 * p) := by omega
            simp only [h1, h2, ↓reduceIte]
            by_cases hk : k = i.val - p
            · subst hk; simp
            · have hne : 2 * p + k ≠ 2 * p + (i.val - p) := by omega
              simp only [hk, hne, ↓reduceIte, zero_mul]
          rw [Finset.sum_congr rfl hsub, Finset.sum_ite_eq']
          simp [hilt]
        have hAB : (∑ τ ∈ Finset.range p, if τ.testBit (i.val - p) then (0 : ℤ) else (zNat τ : ℤ)) +
            (∑ τ ∈ Finset.range p, if τ.testBit (i.val - p) then (zNat (p + τ) : ℤ) else 0) =
            ∑ τ ∈ Finset.range p, if τ.testBit (i.val - p) then (zNat (p +
              τ) : ℤ) else (zNat τ : ℤ) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun τ _ => by split_ifs <;> simp
        rw [show p + p = 2 * p from by omega] at hA hB ⊢
        linarith [hA, hB, hC, hAB]
      rw [hsum_split]
      -- Compute the sum of `zNat` over types `τ < p` = `hammingDist v (x.strings.getD (i - p) [])`.
      have hdist_eq :
          (∑ τ ∈ Finset.range p,
            if τ.testBit (i.val - p) then zNat (p + τ) else zNat τ) =
          hammingDist v (x.strings.getD (i.val - p) []) := by
        have hterm : ∀ τ ∈ Finset.range p,
            (if τ.testBit (i.val - p) then zNat (p + τ) else zNat τ) =
            (List.range x.len).countP fun col =>
              colType x.strings col == τ &&
                (v.getD col false != (x.strings.getD (i.val - p) []).getD col false) := by
          intro τ hτ
          have hτlt := Finset.mem_range.mp hτ
          have hnot : ¬(p + τ < p) := by omega
          have hlt2 : p + τ < 2 * p := by omega
          simp only [zNat, hτlt, hnot, hlt2, ↓reduceIte, Nat.add_sub_cancel_left]
          split_ifs with hbit
          · refine List.countP_congr fun col _ => ?_
            by_cases hct : colType x.strings col = τ
            · have hb := colType_testBit x.strings col (i.val - p) hilt
              rw [hct, hbit] at hb
              rw [← hb]; simp [hct]
            · simp [hct]
          · refine List.countP_congr fun col _ => ?_
            by_cases hct : colType x.strings col = τ
            · have hb := colType_testBit x.strings col (i.val - p) hilt
              rw [hct, Bool.eq_false_iff.mpr hbit] at hb
              rw [← hb]; simp [hct]
            · simp [hct]
        rw [Finset.sum_congr rfl hterm]
        -- Sum of `countP (colType == τ && P)` over `τ < p` equals `countP P` since `colType < p`.
        have hpart : ∀ (l : List ℕ) (P : ℕ → Bool), (∀ col ∈ l, colType x.strings col < p) →
            (∑ τ ∈ Finset.range p, l.countP fun col => colType x.strings col == τ && P col) =
            l.countP P := by
          intro l P hl
          induction l with
          | nil => simp
          | cons hd tl ih =>
            simp only [List.countP_cons, Finset.sum_add_distrib, ih fun c hc =>
              hl c (List.mem_cons_of_mem _ hc)]
            congr 1
            have hhd := hl hd (List.mem_cons_self)
            cases hP : P hd
            · simp
            · simp only [Bool.and_true]
              rw [Finset.sum_eq_single (colType x.strings hd)]
              · simp
              · intro τ _ hne; simp [Ne.symm hne]
              · intro hmem; exact absurd (Finset.mem_range.mpr hhd) hmem
        rw [hpart (List.range x.len) _ (fun col _ => colType_lt x.strings col)]
        simp [hammingDist, hvlen]
      have hslack : zNat (2 * p + (i.val - p)) =
          r - hammingDist v (x.strings.getD (i.val - p) []) := by
        have h1 : ¬(2 * p + (i.val - p) < p) := by omega
        have h2 : ¬(2 * p + (i.val - p) < 2 * p) := by omega
        simp [zNat, h1, h2]
      have hle_r : hammingDist v (x.strings.getD (i.val - p) []) ≤ r := by
        have hmem : x.strings.getD (i.val - p) [] ∈ x.strings := by
          rw [getD_eq_getElem_of_lt hilt]; exact List.getElem_mem hilt
        have h1 := hv _ hmem
        have h2 : hammingDist v (x.strings.getD (i.val - p) []) ≤ x.len := by
          rw [← hvlen]; simpa [hammingDist] using List.countP_le_length (l := List.range v.length)
        exact le_min h1 h2
      have hcast_sum :
          (∑ τ ∈ Finset.range p,
            if τ.testBit (i.val - p) then (zNat (p + τ) : ℤ) else (zNat τ : ℤ)) =
          ((∑ τ ∈ Finset.range p,
            if τ.testBit (i.val - p) then zNat (p + τ) else zNat τ : ℕ) : ℤ) := by
        push_cast; refine Finset.sum_congr rfl fun τ _ => by split_ifs <;> rfl
      rw [hcast_sum, hdist_eq, hslack]
      omega
  · rintro ⟨z, hz, hAz⟩
    -- Extract integer counts `z_τ = z τ` and `y_τ = z (p + τ)` with `z_τ + y_τ = n_τ`.
    let zCnt (τ : ℕ) : ℕ := if hτ : τ < p then (z ⟨τ, by rw [hcols]; omega⟩).toNat else 0
    let yCnt (τ : ℕ) : ℕ := if hτ : τ < p then (z ⟨p + τ, by rw [hcols]; omega⟩).toNat else 0
    have hrow_type (τ : ℕ) (hτ : τ < p) :
        zCnt τ + yCnt τ = (List.range x.len).countP (fun col => colType x.strings col == τ) := by
      have hi := congrFun hAz ⟨τ, by rw [hrows]; omega⟩
      simp only [csMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, csRHS, hp, hτ, ↓reduceIte,
        csEntry] at hi
      have h1 : (⟨τ, by rw [hcols]; omega⟩ : Fin (csNumCols m)) ≠
          ⟨p + τ, by rw [hcols]; omega⟩ := by
        intro h; have := congrArg Fin.val h; dsimp only at this; omega
      have hsum :
          ∑ j : Fin (csNumCols m), (if j.val = τ ∨ j.val = p + τ then (1 : ℤ) else 0) * z j =
          z ⟨τ, by rw [hcols]; omega⟩ + z ⟨p + τ, by rw [hcols]; omega⟩ := by
        have hsub : ∀ j : Fin (csNumCols m),
            (if j.val = τ ∨ j.val = p + τ then (1 : ℤ) else 0) * z j =
            (if j = ⟨τ, by rw [hcols]; omega⟩ then z ⟨τ, by rw [hcols]; omega⟩ else 0) +
            (if j = ⟨p + τ, by rw [hcols]; omega⟩ then z ⟨p + τ, by rw [hcols]; omega⟩ else 0) :=
          fun j => by
            by_cases h1' : j = ⟨τ, by rw [hcols]; omega⟩
            · rw [h1']; simp [h1]
            · by_cases h2' : j = ⟨p + τ, by rw [hcols]; omega⟩
              · rw [h2']; simp [h1.symm]
              · have hn1 : j.val ≠ τ := fun h => h1' (Fin.ext h)
                have hn2 : j.val ≠ p + τ := fun h => h2' (Fin.ext h)
                simp only [h1', h2', hn1, hn2, or_self, ↓reduceIte, zero_mul, add_zero]
        simp_rw [hsub]
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
        simp
      rw [hsum] at hi
      have hz1 : 0 ≤ z ⟨τ, by rw [hcols]; omega⟩ := hz _
      have hz2 : 0 ≤ z ⟨p + τ, by rw [hcols]; omega⟩ := hz _
      simp only [zCnt, yCnt, hτ, ↓reduceDIte]
      omega
    -- Construct `v` of length `x.len`: set `v[col] = true` iff `#{col' < col | type = τ} < zCnt τ`.
    let v : List Bool := (List.range x.len).map fun col =>
      decide ((List.range col).countP (fun col' => colType x.strings col' == colType x.strings col)
        < zCnt (colType x.strings col))
    have hvlen : v.length = x.len := by simp [v]
    -- Key counting lemma: for `k ≤ x.len` and `τ < p`, `v` has `min tot (zCnt τ)` ones on `τ`.
    have hcount_gen : ∀ (k : ℕ), k ≤ x.len → ∀ (τ : ℕ), τ < p →
        let tot := (List.range k).countP fun col => colType x.strings col == τ
        (List.range k).countP (fun col => colType x.strings col == τ && v.getD col false) =
          min tot (zCnt τ) := by
      intro k hk τ hτ
      induction k with
      | zero => simp
      | succ k ih =>
        have hk' : k < x.len := Nat.lt_of_succ_le hk
        have ih' := ih (Nat.le_of_lt hk')
        simp only [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
        by_cases hct : colType x.strings k = τ
        · have hvget : v.getD k false =
              decide ((List.range k).countP (fun col' => colType x.strings col' == τ) < zCnt τ)
                := by
            rw [getD_eq_getElem_of_lt (by simp [v, hk'])]
            simp [v, hct]
          simp only [hct, beq_self_eq_true, Bool.true_and, hvget]
          by_cases hlt : (List.range k).countP (fun col' => colType x.strings col' == τ) < zCnt τ
          · simp only [hlt, decide_true, ↓reduceIte]
            rw [ih']; omega
          · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte, add_zero]
            rw [ih']; omega
        · simp only [beq_eq_false_iff_ne.mpr hct, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            add_zero]
          exact ih'
    have hones (τ : ℕ) (hτ : τ < p) :
        (List.range x.len).countP (fun col => colType x.strings col == τ && v.getD col false) =
          zCnt τ := by
      have h := hcount_gen x.len le_rfl τ hτ
      have hr := hrow_type τ hτ
      rw [h]; omega
    have hzeros (τ : ℕ) (hτ : τ < p) :
        (List.range x.len).countP (fun col => colType x.strings col == τ && !(v.getD col false)) =
          yCnt τ := by
      have hsplit := List.length_eq_countP_add_countP (fun col => v.getD col false)
        (l := (List.range x.len).filter fun col => colType x.strings col == τ)
      have hc1 : (List.range x.len).countP
          (fun col => colType x.strings col == τ && v.getD col false) =
          ((List.range x.len).filter fun col => colType x.strings col == τ).countP
            (fun col => v.getD col false) := by
        rw [List.countP_filter]; exact List.countP_congr fun _ _ => by simp [Bool.and_comm]
      have hc2 : (List.range x.len).countP
          (fun col => colType x.strings col == τ && !(v.getD col false)) =
          ((List.range x.len).filter fun col => colType x.strings col == τ).countP
            (fun col => decide (¬v.getD col false = true)) := by
        rw [List.countP_filter]; exact List.countP_congr fun _ _ => by simp [Bool.and_comm]
      have hlen_f : ((List.range x.len).filter fun col => colType x.strings col == τ).length =
          zCnt τ + yCnt τ := by
        rw [← List.countP_eq_length_filter, ← hrow_type τ hτ]
      have ho := hones τ hτ
      rw [← hc1, ← hc2, ho] at hsplit
      omega
    refine ⟨v, hvlen, fun s hs => ?_⟩
    obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem hs
    have hrow := congrFun hAz ⟨p + i', by rw [hrows]; omega⟩
    simp only [csMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, csRHS, hp] at hrow
    have hnotlt : ¬(p + i' < p) := by omega
    simp only [hnotlt, ↓reduceIte, csEntry, Nat.add_sub_cancel_left] at hrow
    have hsum_split :
        ∑ j : Fin (csNumCols m),
          (if j.val < p then if j.val.testBit i' then (0 : ℤ) else 1
           else if j.val < 2 * p then if (j.val - p).testBit i' then 1 else 0
           else if j.val = 2 * p + i' then 1 else 0) * z j =
        (∑ τ ∈ Finset.range p,
          if τ.testBit i' then ((yCnt τ : ℕ) : ℤ) else ((zCnt τ : ℕ) : ℤ)) +
        z ⟨2 * p + i', by rw [hcols]; omega⟩ := by
      have hrewrite :
          (∑ j : Fin (csNumCols m),
            (if j.val < p then if j.val.testBit i' then (0 : ℤ) else 1
             else if j.val < 2 * p then if (j.val - p).testBit i' then 1 else 0
             else if j.val = 2 * p + i' then 1 else 0) * z j) =
          ∑ j : Fin (csNumCols m),
            if hj : j.val < csNumCols m then
              (if j.val < p then if j.val.testBit i' then (0 : ℤ) else 1
               else if j.val < 2 * p then if (j.val - p).testBit i' then 1 else 0
               else if j.val = 2 * p + i' then 1 else 0) * z ⟨j.val, hj⟩
            else 0 :=
        Finset.sum_congr rfl fun j _ => by simp only [j.isLt, ↓reduceDIte, Fin.eta]
      rw [hrewrite, Fin.sum_univ_eq_sum_range
        (f := fun k =>
          if hk : k < csNumCols m then
            (if k < p then if k.testBit i' then (0 : ℤ) else 1
             else if k < 2 * p then if (k - p).testBit i' then 1 else 0
             else if k = 2 * p + i' then 1 else 0) * z ⟨k, hk⟩
          else 0)]
      change (∑ k ∈ Finset.range (2 * p + m),
        if hk : k < csNumCols m then
          (if k < p then if k.testBit i' then (0 : ℤ) else 1
           else if k < 2 * p then if (k - p).testBit i' then 1 else 0
           else if k = 2 * p + i' then 1 else 0) * z ⟨k, hk⟩
        else 0) = _
      have h2p : Finset.range (2 * p) = Finset.range (p + p) := by rw [two_mul]
      rw [Finset.sum_range_add, h2p, Finset.sum_range_add]
      have hA : ∑ k ∈ Finset.range p,
          (if hk : k < csNumCols m then
            (if k < p then if k.testBit i' then (0 : ℤ) else 1
             else if k < 2 * p then if (k - p).testBit i' then 1 else 0
             else if k = 2 * p + i' then 1 else 0) * z ⟨k, hk⟩
          else 0) =
          ∑ τ ∈ Finset.range p, if τ.testBit i' then (0 : ℤ) else (zCnt τ : ℤ) := by
        refine Finset.sum_congr rfl fun τ hτ => ?_
        have hτlt := Finset.mem_range.mp hτ
        have hklt : τ < csNumCols m := by rw [hcols]; omega
        have hzτ : 0 ≤ z ⟨τ, hklt⟩ := hz _
        simp only [hklt, ↓reduceDIte, hτlt, ↓reduceIte, zCnt]
        split_ifs <;> simp; omega
      have hB : ∑ k ∈ Finset.range p,
          (if hk : p + k < csNumCols m then
            (if p + k < p then if (p + k).testBit i' then (0 : ℤ) else 1
             else if p + k < 2 * p then if (p + k - p).testBit i' then 1 else 0
             else if p + k = 2 * p + i' then 1 else 0) * z ⟨p + k, hk⟩
          else 0) =
          ∑ τ ∈ Finset.range p, if τ.testBit i' then (yCnt τ : ℤ) else 0 := by
        refine Finset.sum_congr rfl fun τ hτ => ?_
        have hτlt := Finset.mem_range.mp hτ
        have hklt : p + τ < csNumCols m := by rw [hcols]; omega
        have h1 : ¬(p + τ < p) := by omega
        have h2 : p + τ < 2 * p := by omega
        have hyτ : 0 ≤ z ⟨p + τ, hklt⟩ := hz _
        simp only [hklt, ↓reduceDIte, h1, h2, ↓reduceIte, Nat.add_sub_cancel_left, yCnt, hτlt]
        split_ifs <;> simp; omega
      have hC : ∑ k ∈ Finset.range m,
          (if hk : 2 * p + k < csNumCols m then
            (if 2 * p + k < p then if (2 * p + k).testBit i' then (0 : ℤ) else 1
             else if 2 * p + k < 2 * p then if (2 * p + k - p).testBit i' then 1 else 0
             else if 2 * p + k = 2 * p + i' then 1 else 0) * z ⟨2 * p + k, hk⟩
          else 0) =
          z ⟨2 * p + i', by rw [hcols]; omega⟩ := by
        have hsub : ∀ k ∈ Finset.range m,
            (if hk : 2 * p + k < csNumCols m then
              (if 2 * p + k < p then if (2 * p + k).testBit i' then (0 : ℤ) else 1
               else if 2 * p + k < 2 * p then if (2 * p + k - p).testBit i' then 1 else 0
               else if 2 * p + k = 2 * p + i' then 1 else 0) * z ⟨2 * p + k, hk⟩
            else 0) =
            if k = i' then z ⟨2 * p + i', by rw [hcols]; omega⟩ else 0 := fun k hk => by
          have hklt : 2 * p + k < csNumCols m := by
            have := Finset.mem_range.mp hk; rw [hcols]; omega
          have h1 : ¬(2 * p + k < p) := by omega
          have h2 : ¬(2 * p + k < 2 * p) := by omega
          simp only [hklt, ↓reduceDIte, h1, h2, ↓reduceIte]
          by_cases hki : k = i'
          · subst hki; simp
          · have : 2 * p + k ≠ 2 * p + i' := by omega
            simp only [hki, this, ↓reduceIte, zero_mul]
        rw [Finset.sum_congr rfl hsub, Finset.sum_ite_eq']
        have hi'm : i' < m := hi'
        simp [hi'm]
      have hAB : (∑ τ ∈ Finset.range p, if τ.testBit i' then (0 : ℤ) else (zCnt τ : ℤ)) +
          (∑ τ ∈ Finset.range p, if τ.testBit i' then (yCnt τ : ℤ) else 0) =
          ∑ τ ∈ Finset.range p, if τ.testBit i' then (yCnt τ : ℤ) else (zCnt τ : ℤ) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun τ _ => by split_ifs <;> simp
      linarith [hA, hB, hC, hAB]
    rw [hsum_split] at hrow
    have hdist_eq :
        (∑ τ ∈ Finset.range p, if τ.testBit i' then yCnt τ else zCnt τ) =
        hammingDist v x.strings[i'] := by
      have hterm : ∀ τ ∈ Finset.range p,
          (if τ.testBit i' then yCnt τ else zCnt τ) =
          (List.range x.len).countP fun col =>
            colType x.strings col == τ && (v.getD col false != x.strings[i'].getD col false) := by
        intro τ hτ
        have hτlt := Finset.mem_range.mp hτ
        split_ifs with hbit
        · rw [← hzeros τ hτlt]
          refine List.countP_congr fun col _ => ?_
          by_cases hct : colType x.strings col = τ
          · have hb := colType_testBit x.strings col i' hi'
            rw [hct, hbit, getD_eq_getElem_of_lt hi'] at hb
            rw [← hb]; simp [hct]
          · simp [hct]
        · rw [← hones τ hτlt]
          refine List.countP_congr fun col _ => ?_
          by_cases hct : colType x.strings col = τ
          · have hb := colType_testBit x.strings col i' hi'
            rw [hct, Bool.eq_false_iff.mpr hbit, getD_eq_getElem_of_lt hi'] at hb
            rw [← hb]; simp [hct]
          · simp [hct]
      rw [Finset.sum_congr rfl hterm]
      have hpart : ∀ (l : List ℕ) (P : ℕ → Bool), (∀ col ∈ l, colType x.strings col < p) →
          (∑ τ ∈ Finset.range p, l.countP fun col => colType x.strings col == τ && P col) =
          l.countP P := by
        intro l P hl
        induction l with
        | nil => simp
        | cons hd tl ih =>
          simp only [List.countP_cons, Finset.sum_add_distrib, ih fun c hc =>
            hl c (List.mem_cons_of_mem _ hc)]
          congr 1
          have hhd := hl hd (List.mem_cons_self)
          cases hP : P hd
          · simp
          · simp only [Bool.and_true]
            rw [Finset.sum_eq_single (colType x.strings hd)]
            · simp
            · intro τ _ hne; simp [Ne.symm hne]
            · intro hmem; exact absurd (Finset.mem_range.mpr hhd) hmem
      rw [hpart (List.range x.len) _ (fun col _ => colType_lt x.strings col)]
      simp [hammingDist, hvlen]
    have hcast_sum :
        (∑ τ ∈ Finset.range p, if τ.testBit i' then (yCnt τ : ℤ) else (zCnt τ : ℤ)) =
        ((∑ τ ∈ Finset.range p, if τ.testBit i' then yCnt τ else zCnt τ : ℕ) : ℤ) := by
      push_cast; refine Finset.sum_congr rfl fun τ _ => by split_ifs <;> rfl
    rw [hcast_sum, hdist_eq] at hrow
    have hslack : 0 ≤ z ⟨2 * p + i', by rw [hcols]; omega⟩ := hz _
    have hle_int : (hammingDist v x.strings[i'] : ℤ) ≤ min (x.radius : ℤ) (x.len : ℤ) := by
      linarith
    exact Int.ofNat_le.mp (hle_int.trans (min_le_left _ _))

end Cslib.Complexity
