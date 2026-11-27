module

public import CslibFrontier.Computability.Complexity.Parameterized.ClosestStringILP
public import CslibFrontier.Algorithms.LinearAlgebra.BareissElimination
import CslibFrontier.Computability.Complexity.FineGrained.ExhaustiveSearch
import CslibFrontier.Computability.PolyTime.LinearAlgebra.RationalElimination
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD

/-!
# Binary Closest String FPT Algorithm

This module completes the FPT proof for `BinaryClosestString` parameterized by the number of
strings (`BinaryClosestString_mem_FPT`), using the column-type ILP from `ClosestStringILP.lean`,
`Cslib.LinearAlgebra.ratSolve`, and `DecidableInExpTime.of_exhaustiveSearch`.
-/

public section

namespace Cslib.Complexity

open Cslib.LinearAlgebra Turing.MultiTapeTM ComputableInPolyTime
open scoped Matrix

/-! ### Capped Branching Budget and Polynomial-Time Verifier -/

/-- Compute `min (2 ^ m) cap` in `m` steps without ever exceeding `cap` (polytime in `encUnary`). -/
@[expose]
def pow2Cap (m cap : ℕ) : ℕ :=
  (List.range m).foldl (fun acc _ => min (2 * acc) cap) 1

private theorem pow2Cap_eq (m cap : ℕ) (hcap : 1 ≤ cap) :
    pow2Cap m cap = min (2 ^ m) cap := by
  unfold pow2Cap
  induction m with
  | zero => simp [hcap]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, Nat.pow_succ, Nat.mul_comm (2 ^ m) 2]
    omega

private theorem pow2Cap_le (m cap : ℕ) (hcap : 1 ≤ cap) : pow2Cap m cap ≤ cap := by
  rw [pow2Cap_eq m cap hcap]; exact Nat.min_le_right _ _

/-- Number of branching bits `min x.len (csTotalBits x.strings.length)` (0 if `strings` is empty),
computed in polynomial time in unary. -/
@[expose]
def csBranchBits (x : ClosestStringInstance) : ℕ :=
  if x.strings.isEmpty then 0
  else
    let cap := x.len + 1
    let p := pow2Cap x.strings.length cap
    let N := min (2 * p + x.strings.length) cap
    let B := min (N + N * (10 * (N + 1) ^ 2)) cap
    min x.len B

/-- Exact bit-length bound for `K = N! * (M * (N + 1)^2 + 1)^N < 2 ^ (csSmallBits m)`. -/
private theorem csKernelBound_lt_two_pow (m : ℕ) :
    (csNumCols m).factorial *
      (csNumRows m * (csNumCols m + 1) ^ 2 + 1) ^ (csNumCols m) <
      2 ^ (csSmallBits m) := by
  refine Nat.size_le.mp ?_
  set N := csNumCols m
  set M := csNumRows m
  have hMN : M ≤ N := by unfold M N csNumRows csNumCols; omega
  have h1 : (N.factorial * (M * (N + 1) ^ 2 + 1) ^ N).size ≤
      N.factorial.size + ((M * (N + 1) ^ 2 + 1) ^ N).size := Nat.size_mul_le _ _
  have h2 : N.factorial.size ≤ N * N.size + 1 := Nat.size_factorial_le N
  have h3 : N.size ≤ N := Nat.size_le_self N
  have h4 : ((M * (N + 1) ^ 2 + 1) ^ N).size ≤ N * (M * (N + 1) ^ 2 + 1).size + 1 :=
    Nat.size_pow_le _ _
  have h5 : (M * (N + 1) ^ 2 + 1).size ≤ (M * (N + 1) ^ 2).size + 2 := by
    have := Nat.size_add_le (M * (N + 1) ^ 2) 1
    norm_num [Nat.size_one] at this; omega
  have h6 : (M * (N + 1) ^ 2).size ≤ M.size + ((N + 1) ^ 2).size := Nat.size_mul_le _ _
  have h7 : M.size ≤ M := Nat.size_le_self M
  have h8 : ((N + 1) ^ 2).size ≤ 2 * (N + 1).size + 1 := Nat.size_pow_le _ _
  have h9 : (N + 1).size ≤ N + 1 := Nat.size_le_self _
  have hmul : N * (N.size) ≤ N * N := Nat.mul_le_mul_left N h3
  have hmul2 : N * (M * (N + 1) ^ 2 + 1).size ≤ N * (M + 2 * (N + 1) + 3) :=
    Nat.mul_le_mul_left N (by omega)
  unfold csSmallBits
  change _ ≤ 10 * (N + 1) ^ 2
  nlinarith

/-- Read `len` bits starting at bit position `start` of `r` as a binary natural number. -/
@[expose]
def readChunk (r start len : ℕ) : ℕ :=
  ofBits ((List.range len).map fun t => r.testBit (start + t))

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

private theorem colType_lt_two_pow (strings : List (List Bool)) (j : ℕ) :
    colType strings j < 2 ^ strings.length := by
  unfold colType ofBits
  simpa using Nat.foldr_bit_lt (strings.map fun s => s.getD j false)

private theorem readChunk_of_pack {len : ℕ} (val : ℕ) (hval : val < 2 ^ len)
    (r start : ℕ) (hbits : ∀ t < len, r.testBit (start + t) = val.testBit t) :
    readChunk r start len = val := by
  unfold readChunk ofBits
  have hmap : (List.range len).map (fun t => r.testBit (start + t)) =
      (List.range len).map val.testBit :=
    List.map_congr_left fun t ht => hbits t (List.mem_range.mp ht)
  rw [hmap]
  exact Nat.foldr_bit_testBit (Nat.size_le.mpr hval)

/-- Assemble `v : List Bool` of length `x.len` from the first `x.len` bits of `r` and check
whether `v` is within Hamming distance `x.radius` of every string in `x.strings`. -/
@[expose]
def checkSmall (x : ClosestStringInstance) (r : ℕ) : Bool :=
  let v := (List.range x.len).map fun j => r.testBit j
  x.strings.all fun s => decide (hammingDist v s ≤ x.radius)

/-- Build the column-type ILP system for `x` with dimensions capped at `x.len + 1`, guess
`(J, x_{\bar J})` from `r`, solve for `x_J` using `Cslib.LinearAlgebra.ratSolve`, and verify
that the assembled nonnegative integer vector satisfies `A *ᵥ z = b`. -/
@[expose]
def checkLarge (x : ClosestStringInstance) (r : ℕ) : Bool :=
  let m := x.strings.length
  let cap := x.len + 1
  let p := pow2Cap m cap
  let M' := min (p + m) cap
  let N' := min (2 * p + m) cap
  let w := min (10 * (N' + 1) ^ 2) cap
  let Jcols := (List.range N').filter fun j => r.testBit j
  let small : List ℕ := (List.range N').map fun j =>
    if r.testBit j then 0 else readChunk r (N' + j * w) w
  let counts : List ℕ := (List.range p).map fun τ =>
    (List.range x.len).countP fun col => colType x.strings col == τ
  let rhsFull : List ℤ := (List.range M').map fun i =>
    if i < p then (counts.getD i 0 : ℤ) else (min x.radius x.len : ℤ)
  let rhsJ : List ℚ := (List.range M').map fun i =>
    let bi := rhsFull.getD i 0
    let sub := ((List.range N').map fun j =>
      csEntry m p i j * (small.getD j 0 : ℤ)).sum
    ((bi - sub : ℤ) : ℚ)
  let matJ : RatTable :=
    { numRows := M'
      numCols := Jcols.length
      rows := (List.range M').map fun i =>
        Jcols.map fun j => (csEntry m p i j : ℚ) }
  match (ratSolve ⟨matJ, rhsJ⟩).solution with
  | none => false
  | some sol =>
    decide (sol.length = Jcols.length) &&
    (sol.all fun q => decide (q.den = 1) && decide (0 ≤ q.num)) &&
    let zFull : List ℤ := (List.range N').map fun j =>
      match (Jcols.zip sol).find? (fun p => p.1 == j) with
      | some (_, q) => q.num
      | none => (small.getD j 0 : ℤ)
    (List.range M').all fun i =>
      decide (((List.range N').map fun j =>
        csEntry m p i j * zFull.getD j 0).sum = rhsFull.getD i 0)

/-- Full polynomial-time check for `BinaryClosestString` in the exhaustive-search reduction. -/
@[expose]
def csCheck (p : ClosestStringInstance × ℕ) : Bool :=
  let x := p.1
  let r := p.2
  if !validClosestString x then false
  else if x.strings.isEmpty then true
  else if decide (x.len ≤ x.radius) then true
  else
    let cap := x.len + 1
    let p2 := pow2Cap x.strings.length cap
    let N := min (2 * p2 + x.strings.length) cap
    let B := min (N + N * (10 * (N + 1) ^ 2)) cap
    if decide (B ≤ x.len) then checkLarge x r else checkSmall x r

private theorem csBranchBits_le_csTotalBits (x : ClosestStringInstance) :
    csBranchBits x ≤ csTotalBits x.strings.length := by
  unfold csBranchBits csTotalBits csSmallBits csNumCols
  split_ifs
  · exact Nat.zero_le _
  · set m := x.strings.length
    set cap := x.len + 1
    have hp : pow2Cap m cap ≤ 2 ^ m := by
      rw [pow2Cap_eq m cap (by omega)]; exact Nat.min_le_left _ _
    have hN : min (2 * pow2Cap m cap + m) cap ≤ 2 * 2 ^ m + m :=
      le_trans (Nat.min_le_left _ _) (by omega)
    have hB : min (min (2 * pow2Cap m cap + m) cap +
        min (2 * pow2Cap m cap + m) cap * (10 * (min (2 * pow2Cap m cap + m) cap + 1) ^ 2)) cap ≤
        (2 * 2 ^ m + m) + (2 * 2 ^ m + m) * (10 * (2 * 2 ^ m + m + 1) ^ 2) := by
      refine le_trans (Nat.min_le_left _ _) ?_
      exact Nat.add_le_add hN (Nat.mul_le_mul hN (Nat.mul_le_mul_left 10
        (Nat.pow_le_pow_left (Nat.add_le_add_right hN 1) 2)))
    exact le_trans (Nat.min_le_right _ _) hB

private theorem csBranchBits_cases (x : ClosestStringInstance) (hne : ¬x.strings.isEmpty) :
    let m := x.strings.length
    let cap := x.len + 1
    let p2 := pow2Cap m cap
    let N := min (2 * p2 + m) cap
    let B := min (N + N * (10 * (N + 1) ^ 2)) cap
    (B ≤ x.len →
      p2 = 2 ^ m ∧ min (p2 + m) cap = csNumRows m ∧ N = csNumCols m ∧
        min (10 * (N + 1) ^ 2) cap = csSmallBits m ∧
        B = csTotalBits m ∧ csBranchBits x = csTotalBits m) ∧
    (¬(B ≤ x.len) → csBranchBits x = x.len) := by
  intro m cap p2 N B
  constructor
  · intro hBle
    have hNle : N ≤ x.len := by
      have h1 : N ≤ N + N * (10 * (N + 1) ^ 2) := Nat.le_add_right _ _
      have h2 : N + N * (10 * (N + 1) ^ 2) < cap := by
        by_contra hge
        have : B = cap := Nat.min_eq_right (not_lt.mp hge)
        omega
      omega
    have h2p : 2 * p2 + m ≤ x.len := by
      by_contra hge
      have : N = cap := Nat.min_eq_right (by omega)
      omega
    have hp_eq : p2 = 2 ^ m := by
      rw [show p2 = min (2 ^ m) cap from pow2Cap_eq m cap (by omega)]
      by_cases h : 2 ^ m ≤ cap
      · exact Nat.min_eq_left h
      · exfalso; have : p2 = cap := by
          rw [show p2 = min (2 ^ m) cap from pow2Cap_eq m cap (by omega)]
          exact Nat.min_eq_right (le_of_not_ge h)
        omega
    have hM_eq : min (p2 + m) cap = csNumRows m := by
      rw [hp_eq]; exact Nat.min_eq_left (by omega)
    have hN_eq : N = csNumCols m := by
      change min (2 * p2 + m) cap = csNumCols m
      rw [hp_eq]; exact Nat.min_eq_left (by omega)
    have hB_lt : N + N * (10 * (N + 1) ^ 2) < cap := by
      by_contra hge
      have : B = cap := Nat.min_eq_right (not_lt.mp hge)
      omega
    have hw_eq : min (10 * (N + 1) ^ 2) cap = csSmallBits m := by
      have hpos : 1 ≤ N := by
        rw [hN_eq]; unfold csNumCols
        have : 1 ≤ 2 ^ m := Nat.one_le_two_pow; omega
      have hwle : 10 * (N + 1) ^ 2 ≤ N + N * (10 * (N + 1) ^ 2) := by
        nlinarith
      rw [Nat.min_eq_left (by omega), hN_eq]; rfl
    have hB_eq : B = csTotalBits m := by
      change min (N + N * (10 * (N + 1) ^ 2)) cap = csTotalBits m
      rw [Nat.min_eq_left (by omega), hN_eq]; rfl
    refine ⟨hp_eq, hM_eq, hN_eq, hw_eq, hB_eq, ?_⟩
    simp only [csBranchBits, hne]
    change min x.len B = csTotalBits m
    rw [Nat.min_eq_right hBle, hB_eq]
  · intro hnot
    simp only [csBranchBits, hne]
    change min x.len B = x.len
    exact Nat.min_eq_left (by omega)

private theorem computableInPolyTime_min_unary {α : Type} {encIn : α ↪ List Bool} {f g : α → ℕ}
    (hf : ComputableInPolyTime f encIn encUnary)
    (hg : ComputableInPolyTime g encIn encUnary) :
    ComputableInPolyTime (fun a => min (f a) (g a)) encIn encUnary := by
  convert (unary_le.comp (hf.prod hg)).ite hf hg using 1
  funext a; simp [Nat.min_def]

private theorem computableInPolyTime_pow2Cap :
    ComputableInPolyTime (fun p : ℕ × ℕ => pow2Cap p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
  unfold pow2Cap
  refine (ComputableInPolyTime.foldlWith_spec
    (encP := encUnary) (encA := encUnary) (encB := encUnary)
    (par := fun p : ℕ × ℕ => p.2)
    (list := fun p : ℕ × ℕ => List.range p.1)
    (init := fun _ => 1)
    (step := fun cap acc _ => min (2 * acc) cap)
    (snd _ _) (unary_range' (fst _ _)) (const 1)
    (by
      have h1 : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ => 2 * q.1.2)
          (encPair (encPair encUnary encUnary) encUnary) encUnary :=
        unary_mul' (const 2) ((snd _ _).comp (fst _ _))
      have h2 : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ => q.1.1)
          (encPair (encPair encUnary encUnary) encUnary) encUnary :=
        (fst _ _).comp (fst _ _)
      exact computableInPolyTime_min_unary h1 h2)
    (fun p _ acc => acc ≤ p.2 + 1)
    (fun _ => by omega)
    (fun p _ acc _ _ hinv => by omega)
    (size := fun p : ℕ × ℕ => p.2 + 1)
    (by growth_poly)
    (fun p _ acc _ hinv => by simp only [encUnary_apply, List.length_replicate]; exact hinv)).1

private theorem computableInPolyTime_csBranchBits :
    ComputableInPolyTime csBranchBits encClosestString encUnary := by
  unfold csBranchBits
  have hlen : ComputableInPolyTime (fun x : ClosestStringInstance => x.len)
      encClosestString encUnary := encClosestString_len_polyTime id'
  have hstr : ComputableInPolyTime (fun x : ClosestStringInstance => x.strings)
      encClosestString (encList encBits) := encClosestString_strings_polyTime id'
  have hm : ComputableInPolyTime (fun x : ClosestStringInstance => x.strings.length)
      encClosestString encUnary := (length_list encBits).comp hstr
  have hcap : ComputableInPolyTime (fun x : ClosestStringInstance => x.len + 1)
      encClosestString encUnary := unary_add' hlen (const 1)
  have hp : ComputableInPolyTime
      (fun x : ClosestStringInstance => pow2Cap x.strings.length (x.len + 1))
      encClosestString encUnary :=
    computableInPolyTime_pow2Cap.comp (hm.prod hcap)
  have hN := computableInPolyTime_min_unary (unary_add' (unary_mul' (const 2) hp) hm) hcap
  have hN1 := unary_add' hN (const 1)
  have hB := computableInPolyTime_min_unary
    (unary_add' hN (unary_mul' hN (unary_mul' (const 10) (unary_mul' hN1 hN1)))) hcap
  have hB_sq : ComputableInPolyTime
      (fun x : ClosestStringInstance =>
        let cap := x.len + 1
        let p := pow2Cap x.strings.length cap
        let N := min (2 * p + x.strings.length) cap
        min (N + N * (10 * (N + 1) ^ 2)) cap)
      encClosestString encUnary := by
    convert hB using 1; funext x; simp only [sq]
  exact ((listIsEmpty' encBits).comp hstr).ite (const 0)
    (computableInPolyTime_min_unary hlen hB_sq)

private theorem list_sum_map_range {α : Type*} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      Finset.sum_range_succ, ih]

private theorem computableInPolyTime_readChunk :
    ComputableInPolyTime (fun t : (ℕ × ℕ) × ℕ => readChunk t.1.1 t.1.2 t.2)
      (encPair (encPair encNat encUnary) encUnary) encNat := by
  unfold readChunk
  let e1 := encPair encNat encUnary
  let e2 := encPair e1 encUnary
  exact bitsToNat.comp (listToBits.comp (mapWithInput (unary_range' (snd e1 encUnary))
    (binary_testBit (((fst encNat encUnary).comp (fst e1 encUnary)).comp (fst e2 encUnary))
      (unary_add' (((snd encNat encUnary).comp (fst e1 encUnary)).comp (fst e2 encUnary))
        (snd e2 encUnary)))))

private theorem computableInPolyTime_colType :
    ComputableInPolyTime (fun t : List (List Bool) × ℕ => colType t.1 t.2)
      (encPair (encList encBits) encUnary) encNat := by
  unfold colType
  let e := encPair (encList encBits) encUnary
  exact bitsToNat.comp (listToBits.comp (mapWithInput (fst (encList encBits) encUnary)
    (bitsGetDWithInput (snd e encBits) ((snd (encList encBits) encUnary).comp (fst e encBits))
      false)))

private theorem computableInPolyTime_csEntry :
    ComputableInPolyTime (fun t : ((ℕ × ℕ) × ℕ) × ℕ => csEntry t.1.1.1 t.1.1.2 t.1.2 t.2)
      (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encIntBin := by
  unfold csEntry
  let e1 := encPair encUnary encUnary
  let e2 := encPair e1 encUnary
  let e3 := encPair e2 encUnary
  have hm' : ComputableInPolyTime (fun t : ((ℕ × ℕ) × ℕ) × ℕ => t.1.1.1) e3 encUnary :=
    ((fst encUnary encUnary).comp (fst e1 encUnary)).comp (fst e2 encUnary)
  have hp' : ComputableInPolyTime (fun t : ((ℕ × ℕ) × ℕ) × ℕ => t.1.1.2) e3 encUnary :=
    ((snd encUnary encUnary).comp (fst e1 encUnary)).comp (fst e2 encUnary)
  have hi' : ComputableInPolyTime (fun t : ((ℕ × ℕ) × ℕ) × ℕ => t.1.2) e3 encUnary :=
    (snd e1 encUnary).comp (fst e2 encUnary)
  have hj' : ComputableInPolyTime (fun t : ((ℕ × ℕ) × ℕ) × ℕ => t.2) e3 encUnary :=
    snd e2 encUnary
  have hbit1 : ComputableInPolyTime (fun t : ((ℕ × ℕ) × ℕ) × ℕ => t.2.testBit (t.1.2 - t.1.1.2))
      e3 encBool :=
    binary_testBit (unary_to_binary.comp hj') (unary_sub.comp (hi'.prod hp'))
  have hbit2 : ComputableInPolyTime
      (fun t : ((ℕ × ℕ) × ℕ) × ℕ => (t.2 - t.1.1.2).testBit (t.1.2 - t.1.1.2))
      e3 encBool :=
    binary_testBit (unary_to_binary.comp (unary_sub.comp (hj'.prod hp')))
      (unary_sub.comp (hi'.prod hp'))
  have h2p' := unary_mul' (const (encIn := e3) 2) hp'
  convert (unary_lt.comp (hi'.prod hp')).ite
    ((bool_or.comp ((decide_eq' hj' hi').prod
      (decide_eq' hj' (unary_add' hp' hi')))).ite
        (const (encIn := e3) (encOut := encIntBin) 1)
        (const (encIn := e3) (encOut := encIntBin) 0))
    ((unary_lt.comp (hj'.prod hp')).ite
      (hbit1.ite (const (encIn := e3) (encOut := encIntBin) 0)
        (const (encIn := e3) (encOut := encIntBin) 1))
      ((unary_lt.comp (hj'.prod h2p')).ite
        (hbit2.ite (const (encIn := e3) (encOut := encIntBin) 1)
          (const (encIn := e3) (encOut := encIntBin) 0))
        ((decide_eq' hj' (unary_add' h2p' (unary_sub' hi' hp'))).ite
          (const (encIn := e3) (encOut := encIntBin) 1)
          (const (encIn := e3) (encOut := encIntBin) 0)))) using 1
  funext t
  simp [decide_eq_true_eq]

private theorem computableInPolyTime_csCheck :
    ComputableInPolyTime csCheck (encPair encClosestString encNat) encBool := by
  have hx := fst encClosestString encNat
  have hr := snd encClosestString encNat
  have hlen : ComputableInPolyTime (fun q : ClosestStringInstance × ℕ => q.1.len)
      (encPair encClosestString encNat) encUnary :=
    encClosestString_len_polyTime hx
  have hstr : ComputableInPolyTime (fun q : ClosestStringInstance × ℕ => q.1.strings)
      (encPair encClosestString encNat) (encList encBits) :=
    encClosestString_strings_polyTime hx
  have hrad : ComputableInPolyTime (fun q : ClosestStringInstance × ℕ => q.1.radius)
      (encPair encClosestString encNat) encNat :=
    encClosestString_radius_polyTime hx
  have hm : ComputableInPolyTime (fun q : ClosestStringInstance × ℕ => q.1.strings.length)
      (encPair encClosestString encNat) encUnary := (length_list encBits).comp hstr
  have hcap : ComputableInPolyTime (fun q : ClosestStringInstance × ℕ => q.1.len + 1)
      (encPair encClosestString encNat) encUnary := unary_add' hlen (const 1)
  have hp : ComputableInPolyTime
      (fun q : ClosestStringInstance × ℕ => pow2Cap q.1.strings.length (q.1.len + 1))
      (encPair encClosestString encNat) encUnary :=
    computableInPolyTime_pow2Cap.comp (hm.prod hcap)
  have hsmall : ComputableInPolyTime (fun q : ClosestStringInstance × ℕ => checkSmall q.1 q.2)
      (encPair encClosestString encNat) encBool := by
    unfold checkSmall
    have hv : ComputableInPolyTime
        (fun q : ClosestStringInstance × ℕ => (List.range q.1.len).map fun j => q.2.testBit j)
        (encPair encClosestString encNat) encBits :=
      listToBits.comp (mapWithInput (unary_range' hlen)
        (binary_testBit (hr.comp (fst _ _)) (snd _ _)))
    exact allWithInput hstr
      (binary_le.comp ((unary_to_binary.comp (computableInPolyTime_hammingDist
        (hv.comp (fst _ _)) (snd _ _))).prod (hrad.comp (fst _ _))))
  have hlarge : ComputableInPolyTime (fun q : ClosestStringInstance × ℕ => checkLarge q.1 q.2)
      (encPair encClosestString encNat) encBool := by
    have hM' := computableInPolyTime_min_unary (unary_add' hp hm) hcap
    have hN' := computableInPolyTime_min_unary (unary_add' (unary_mul' (const 2) hp) hm) hcap
    have hN'1 := unary_add' hN' (const 1)
    have hw_sq := computableInPolyTime_min_unary
      (unary_mul' (const 10) (unary_mul' hN'1 hN'1)) hcap
    have hw : ComputableInPolyTime
        (fun q : ClosestStringInstance × ℕ =>
          let N' := min (2 * pow2Cap q.1.strings.length (q.1.len + 1) +
            q.1.strings.length) (q.1.len + 1)
          min (10 * (N' + 1) ^ 2) (q.1.len + 1))
        (encPair encClosestString encNat) encUnary := by
      convert hw_sq using 1; funext q; simp only [sq]
    have hJcols : ComputableInPolyTime
        (fun q : ClosestStringInstance × ℕ =>
          (List.range (min (2 * pow2Cap q.1.strings.length (q.1.len + 1) +
            q.1.strings.length) (q.1.len + 1))).filter fun j => q.2.testBit j)
        (encPair encClosestString encNat) (encList encUnary) :=
      filterWithInput (unary_range' hN') (binary_testBit (hr.comp (fst _ _)) (snd _ _))
    have hsmallLst : ComputableInPolyTime
        (fun q : ClosestStringInstance × ℕ =>
          let N' := min (2 * pow2Cap q.1.strings.length (q.1.len + 1) +
            q.1.strings.length) (q.1.len + 1)
          let w := min (10 * (N' + 1) ^ 2) (q.1.len + 1)
          (List.range N').map fun j =>
            if q.2.testBit j then 0 else readChunk q.2 (N' + j * w) w)
        (encPair encClosestString encNat) (encList encNat) := by
      let eQ := encPair encClosestString encNat
      let eQJ := encPair eQ encUnary
      have harg : ComputableInPolyTime
          (fun p : (ClosestStringInstance × ℕ) × ℕ =>
            let N' := min (2 * pow2Cap p.1.1.strings.length (p.1.1.len + 1) +
              p.1.1.strings.length) (p.1.1.len + 1)
            let w := min (10 * (N' + 1) ^ 2) (p.1.1.len + 1)
            ((p.1.2, N' + p.2 * w), w))
          eQJ (encPair (encPair encNat encUnary) encUnary) :=
        ((hr.comp (fst eQ encUnary)).prod
          (unary_add' (hN'.comp (fst eQ encUnary))
            (unary_mul' (snd eQ encUnary) (hw.comp (fst eQ encUnary))))).prod
          (hw.comp (fst eQ encUnary))
      exact mapWithInput (unary_range' hN')
        ((binary_testBit (hr.comp (fst eQ encUnary)) (snd eQ encUnary)).ite (const (encIn := eQJ) 0)
          (by simpa only [Function.comp_def] using computableInPolyTime_readChunk.comp harg))
    have hcounts : ComputableInPolyTime
        (fun q : ClosestStringInstance × ℕ =>
          (List.range (pow2Cap q.1.strings.length (q.1.len + 1))).map fun τ =>
            (List.range q.1.len).countP fun col => colType q.1.strings col == τ)
        (encPair encClosestString encNat) (encList encUnary) :=
      mapWithInput (unary_range' hp)
        (countPWithInput (unary_range' (hlen.comp (fst _ _)))
          (beq (computableInPolyTime_colType.comp
              (((hstr.comp (fst _ _)).comp (fst _ _)).prod (snd _ _)))
            (unary_to_binary.comp ((snd _ _).comp (fst _ _)))))
    have hrhsFull : ComputableInPolyTime
        (fun q : ClosestStringInstance × ℕ =>
          let p := pow2Cap q.1.strings.length (q.1.len + 1)
          let M' := min (p + q.1.strings.length) (q.1.len + 1)
          let counts := (List.range p).map fun τ =>
            (List.range q.1.len).countP fun col => colType q.1.strings col == τ
          (List.range M').map fun i =>
            if i < p then (counts.getD i 0 : ℤ) else (min q.1.radius q.1.len : ℤ))
        (encPair encClosestString encNat) (encList encIntBin) := by
      have hminRL : ComputableInPolyTime
          (fun q : ClosestStringInstance × ℕ => min q.1.radius q.1.len)
          (encPair encClosestString encNat) encNat := by
        convert (binary_le.comp (hrad.prod (unary_to_binary.comp hlen))).ite
          hrad (unary_to_binary.comp hlen) using 1
        funext q; simp [Nat.min_def]
      refine mapWithInput (unary_range' hM') ?_
      convert (unary_lt.comp ((snd _ _).prod (hp.comp (fst _ _)))).ite
        (intBin_natCast_unary.comp
          ((listGetD (encA := encUnary) (0 : ℕ)).comp ((hcounts.comp (fst _ _)).prod (snd _ _))))
        (intBin_natCast.comp (hminRL.comp (fst _ _))) using 1
      funext p
      simp [decide_eq_true_eq, Nat.cast_min]
    have hrhsJ : ComputableInPolyTime
        (fun q : ClosestStringInstance × ℕ =>
          let m := q.1.strings.length
          let cap := q.1.len + 1
          let p := pow2Cap m cap
          let M' := min (p + m) cap
          let N' := min (2 * p + m) cap
          let w := min (10 * (N' + 1) ^ 2) cap
          let small : List ℕ := (List.range N').map fun j =>
            if q.2.testBit j then 0 else readChunk q.2 (N' + j * w) w
          let counts : List ℕ := (List.range p).map fun τ =>
            (List.range q.1.len).countP fun col => colType q.1.strings col == τ
          let rhsFull : List ℤ := (List.range M').map fun i =>
            if i < p then (counts.getD i 0 : ℤ) else (min q.1.radius q.1.len : ℤ)
          (List.range M').map fun i =>
            let bi := rhsFull.getD i 0
            let sub := ((List.range N').map fun j =>
              csEntry m p i j * (small.getD j 0 : ℤ)).sum
            ((bi - sub : ℤ) : ℚ))
        (encPair encClosestString encNat) (encList encRat) := by
      refine mapWithInput (unary_range' hM') ?_
      let eQ := encPair encClosestString encNat
      let eQI := encPair eQ encUnary
      have hbi : ComputableInPolyTime
          (fun t : (ClosestStringInstance × ℕ) × ℕ =>
            (let p := pow2Cap t.1.1.strings.length (t.1.1.len + 1)
             let M' := min (p + t.1.1.strings.length) (t.1.1.len + 1)
             let counts := (List.range p).map fun τ =>
               (List.range t.1.1.len).countP fun col => colType t.1.1.strings col == τ
             ((List.range M').map fun i =>
               if i < p then (counts.getD i 0 : ℤ)
               else (min t.1.1.radius t.1.1.len : ℤ)).getD t.2 0))
          eQI encIntBin := by
        simpa only [Function.comp_def] using
          (listGetD (encA := encIntBin) (0 : ℤ)).comp
            ((hrhsFull.comp (fst eQ encUnary)).prod (snd eQ encUnary))
      have hsub : ComputableInPolyTime
          (fun t : (ClosestStringInstance × ℕ) × ℕ =>
            let m := t.1.1.strings.length
            let cap := t.1.1.len + 1
            let p := pow2Cap m cap
            let N' := min (2 * p + m) cap
            let w := min (10 * (N' + 1) ^ 2) cap
            let small : List ℕ := (List.range N').map fun j =>
              if t.1.2.testBit j then 0 else readChunk t.1.2 (N' + j * w) w
            ((List.range N').map fun j =>
              csEntry m p t.2 j * (small.getD j 0 : ℤ)).sum)
          eQI encIntBin := by
        refine intBin_sum.comp (mapWithInput (unary_range' (hN'.comp (fst eQ encUnary))) ?_)
        have hcsArg :=
          (((hm.comp (fst eQ encUnary)).prod (hp.comp (fst eQ encUnary))).prod
            (snd eQ encUnary)).comp (fst eQI encUnary) |>.prod (snd eQI encUnary)
        have hsmArg :=
          (((hsmallLst.comp (fst eQ encUnary)).comp (fst eQI encUnary)).prod (snd eQI encUnary))
        exact intBin_mul'
          (by simpa only [Function.comp_def] using computableInPolyTime_csEntry.comp hcsArg)
          (by
            simpa only [Function.comp_def] using
              intBin_natCast.comp ((listGetD (encA := encNat) (0 : ℕ)).comp hsmArg))
      exact rat_intCast.comp (intBin_sub' hbi hsub)
    have hmatJ : ComputableInPolyTime
        (fun q : ClosestStringInstance × ℕ =>
          let m := q.1.strings.length
          let cap := q.1.len + 1
          let p := pow2Cap m cap
          let M' := min (p + m) cap
          let N' := min (2 * p + m) cap
          let Jcols := (List.range N').filter fun j => q.2.testBit j
          ({ numRows := M'
             numCols := Jcols.length
             rows := (List.range M').map fun i =>
               Jcols.map fun j => (csEntry m p i j : ℚ) } : RatTable))
        (encPair encClosestString encNat) RatTable.enc := by
      let eQ := encPair encClosestString encNat
      let eQI := encPair eQ encUnary
      have hrows : ComputableInPolyTime
          (fun q : ClosestStringInstance × ℕ =>
            let m := q.1.strings.length
            let cap := q.1.len + 1
            let p := pow2Cap m cap
            let M' := min (p + m) cap
            let N' := min (2 * p + m) cap
            let Jcols := (List.range N').filter fun j => q.2.testBit j
            (List.range M').map fun i => Jcols.map fun j => (csEntry m p i j : ℚ))
          eQ (encList (encList encRat)) :=
        mapWithInput (unary_range' hM')
          (mapWithInput (hJcols.comp (fst eQ encUnary))
            (by
              have hcsArg :=
                ((((hm.comp (fst eQ encUnary)).prod (hp.comp (fst eQ encUnary))).prod
                  (snd eQ encUnary)).comp (fst eQI encUnary)).prod (snd eQI encUnary)
              simpa only [Function.comp_def] using
                rat_intCast.comp (computableInPolyTime_csEntry.comp hcsArg)))
      exact RatTable.enc_mk_polyTime hM' ((length_list encUnary).comp hJcols) hrows
    have hsolve : ComputableInPolyTime
        (fun q : ClosestStringInstance × ℕ =>
          let m := q.1.strings.length
          let cap := q.1.len + 1
          let p := pow2Cap m cap
          let M' := min (p + m) cap
          let N' := min (2 * p + m) cap
          let w := min (10 * (N' + 1) ^ 2) cap
          let Jcols := (List.range N').filter fun j => q.2.testBit j
          let small : List ℕ := (List.range N').map fun j =>
            if q.2.testBit j then 0 else readChunk q.2 (N' + j * w) w
          let counts : List ℕ := (List.range p).map fun τ =>
            (List.range q.1.len).countP fun col => colType q.1.strings col == τ
          let rhsFull : List ℤ := (List.range M').map fun i =>
            if i < p then (counts.getD i 0 : ℤ) else (min q.1.radius q.1.len : ℤ)
          let rhsJ : List ℚ := (List.range M').map fun i =>
            let bi := rhsFull.getD i 0
            let sub := ((List.range N').map fun j =>
              csEntry m p i j * (small.getD j 0 : ℤ)).sum
            ((bi - sub : ℤ) : ℚ)
          let matJ : RatTable :=
            { numRows := M'
              numCols := Jcols.length
              rows := (List.range M').map fun i =>
                Jcols.map fun j => (csEntry m p i j : ℚ) }
          (ratSolve ⟨matJ, rhsJ⟩).solution)
        (encPair encClosestString encNat) (encOption (encList encRat)) :=
      LinearSolveResult.enc_solution_polyTime
        (ratSolve_computableInPolyTime.comp (LinearSystemInput.enc_mk_polyTime hmatJ hrhsJ))
    unfold checkLarge
    have hbody : ComputableInPolyTime
        (fun t : (ClosestStringInstance × ℕ) × List ℚ =>
          let m := t.1.1.strings.length
          let cap := t.1.1.len + 1
          let p := pow2Cap m cap
          let M' := min (p + m) cap
          let N' := min (2 * p + m) cap
          let w := min (10 * (N' + 1) ^ 2) cap
          let Jcols := (List.range N').filter fun j => t.1.2.testBit j
          let small : List ℕ := (List.range N').map fun j =>
            if t.1.2.testBit j then 0 else readChunk t.1.2 (N' + j * w) w
          let counts : List ℕ := (List.range p).map fun τ =>
            (List.range t.1.1.len).countP fun col => colType t.1.1.strings col == τ
          let rhsFull : List ℤ := (List.range M').map fun i =>
            if i < p then (counts.getD i 0 : ℤ) else (min t.1.1.radius t.1.1.len : ℤ)
          decide (t.2.length = Jcols.length) &&
          (t.2.all fun q => decide (q.den = 1) && decide (0 ≤ q.num)) &&
          let zFull : List ℤ := (List.range N').map fun j =>
            match (Jcols.zip t.2).find? (fun p => p.1 == j) with
            | some (_, q) => q.num
            | none => (small.getD j 0 : ℤ)
          (List.range M').all fun i =>
            decide (((List.range N').map fun j =>
              csEntry m p i j * zFull.getD j 0).sum = rhsFull.getD i 0))
        (encPair (encPair encClosestString encNat) (encList encRat)) encBool := by
      have hq := fst (encPair encClosestString encNat) (encList encRat)
      have hsol := snd (encPair encClosestString encNat) (encList encRat)
      have hlen_ok : ComputableInPolyTime
          (fun t : (ClosestStringInstance × ℕ) × List ℚ =>
            decide (t.2.length =
              ((List.range (min (2 * pow2Cap t.1.1.strings.length (t.1.1.len + 1) +
                t.1.1.strings.length) (t.1.1.len + 1))).filter fun j => t.1.2.testBit j).length))
          (encPair (encPair encClosestString encNat) (encList encRat)) encBool :=
        decide_eq' ((length_list encRat).comp hsol)
          ((length_list encUnary).comp (hJcols.comp hq))
      have hnonneg_ok : ComputableInPolyTime
          (fun t : (ClosestStringInstance × ℕ) × List ℚ =>
            t.2.all fun q => decide (q.den = 1) && decide (0 ≤ q.num))
          (encPair (encPair encClosestString encNat) (encList encRat)) encBool :=
        allWithInput hsol
          (bool_and.comp ((decide_eq' (rat_den.comp (snd _ _)) (const 1)).prod
            (intBin_le.comp ((const 0).prod (rat_num.comp (snd _ _))))))
      have hzFull : ComputableInPolyTime
          (fun t : (ClosestStringInstance × ℕ) × List ℚ =>
            let m := t.1.1.strings.length
            let cap := t.1.1.len + 1
            let p := pow2Cap m cap
            let N' := min (2 * p + m) cap
            let w := min (10 * (N' + 1) ^ 2) cap
            let Jcols := (List.range N').filter fun j => t.1.2.testBit j
            let small : List ℕ := (List.range N').map fun j =>
              if t.1.2.testBit j then 0 else readChunk t.1.2 (N' + j * w) w
            (List.range N').map fun j =>
              match (Jcols.zip t.2).find? (fun p => p.1 == j) with
              | some (_, q) => q.num
              | none => (small.getD j 0 : ℤ))
          (encPair (encPair encClosestString encNat) (encList encRat)) (encList encIntBin) := by
        let eT := encPair (encPair encClosestString encNat) (encList encRat)
        let eTI := encPair eT encUnary
        let eP := encPair encUnary encRat
        refine mapWithInput (unary_range' (hN'.comp hq)) ?_
        have hzip : ComputableInPolyTime
            (fun u : ((ClosestStringInstance × ℕ) × List ℚ) × ℕ =>
              ((List.range (min (2 * pow2Cap u.1.1.1.strings.length (u.1.1.1.len + 1) +
                u.1.1.1.strings.length) (u.1.1.1.len +
                  1))).filter fun j => u.1.1.2.testBit j).zip u.1.2)
            eTI (encList eP) :=
          (zip encUnary encRat).comp
            (((hJcols.comp hq).comp (fst eT encUnary)).prod (hsol.comp (fst eT encUnary)))
        have hpred : ComputableInPolyTime
            (fun p : (((ClosestStringInstance × ℕ) × List ℚ) × ℕ) × (ℕ × ℚ) => p.2.1 == p.1.2)
            (encPair eTI eP) encBool := by
          simpa only [Function.comp_def] using
            beq ((fst encUnary encRat).comp (snd eTI eP))
              ((snd eT encUnary).comp (fst eTI eP))
        have hfind := findWithInput (test := fun u pq => pq.1 == u.2) hzip hpred
        have hnone : ComputableInPolyTime
            (fun u : ((ClosestStringInstance × ℕ) × List ℚ) × ℕ =>
              (((List.range (min (2 * pow2Cap u.1.1.1.strings.length (u.1.1.1.len + 1) +
                u.1.1.1.strings.length) (u.1.1.1.len + 1))).map fun j =>
                if u.1.1.2.testBit j then 0 else
                  readChunk u.1.1.2
                    (min (2 * pow2Cap u.1.1.1.strings.length (u.1.1.1.len + 1) +
                      u.1.1.1.strings.length) (u.1.1.1.len + 1) +
                      j * min (10 * (min (2 * pow2Cap u.1.1.1.strings.length (u.1.1.1.len + 1) +
                        u.1.1.1.strings.length) (u.1.1.1.len + 1) + 1) ^ 2)
                        (u.1.1.1.len + 1))
                    (min (10 * (min (2 * pow2Cap u.1.1.1.strings.length (u.1.1.1.len + 1) +
                      u.1.1.1.strings.length) (u.1.1.1.len + 1) + 1) ^ 2)
                      (u.1.1.1.len + 1))).getD u.2 0 : ℤ))
            eTI encIntBin := by
          have harg := (((hsmallLst.comp hq).comp (fst eT encUnary)).prod (snd eT encUnary))
          simpa only [Function.comp_def] using
            intBin_natCast.comp ((listGetD (encA := encNat) (0 : ℕ)).comp harg)
        have hsome : ComputableInPolyTime
            (fun p : (((ClosestStringInstance × ℕ) × List ℚ) × ℕ) × (ℕ × ℚ) => p.2.2.num)
            (encPair eTI eP) encIntBin := by
          simpa only [Function.comp_def] using
            rat_num.comp ((snd encUnary encRat).comp (snd eTI eP))
        have hopt := optionElimWithInput (body := fun _ (pq : ℕ × ℚ) => pq.2.num) hfind hnone hsome
        convert hopt using 1
        funext u; cases List.find? _ _ <;> rfl
      have heq_ok : ComputableInPolyTime
          (fun t : (ClosestStringInstance × ℕ) × List ℚ =>
            let m := t.1.1.strings.length
            let cap := t.1.1.len + 1
            let p := pow2Cap m cap
            let M' := min (p + m) cap
            let N' := min (2 * p + m) cap
            let w := min (10 * (N' + 1) ^ 2) cap
            let Jcols := (List.range N').filter fun j => t.1.2.testBit j
            let small : List ℕ := (List.range N').map fun j =>
              if t.1.2.testBit j then 0 else readChunk t.1.2 (N' + j * w) w
            let counts : List ℕ := (List.range p).map fun τ =>
              (List.range t.1.1.len).countP fun col => colType t.1.1.strings col == τ
            let rhsFull : List ℤ := (List.range M').map fun i =>
              if i < p then (counts.getD i 0 : ℤ) else (min t.1.1.radius t.1.1.len : ℤ)
            let zFull : List ℤ := (List.range N').map fun j =>
              match (Jcols.zip t.2).find? (fun p => p.1 == j) with
              | some (_, q) => q.num
              | none => (small.getD j 0 : ℤ)
            (List.range M').all fun i =>
              decide (((List.range N').map fun j =>
                csEntry m p i j * zFull.getD j 0).sum = rhsFull.getD i 0))
          (encPair (encPair encClosestString encNat) (encList encRat)) encBool := by
        let eT := encPair (encPair encClosestString encNat) (encList encRat)
        let eTI := encPair eT encUnary
        refine allWithInput (unary_range' (hM'.comp hq)) ?_
        have hdot : ComputableInPolyTime
            (fun u : ((ClosestStringInstance × ℕ) × List ℚ) × ℕ =>
              let m := u.1.1.1.strings.length
              let cap := u.1.1.1.len + 1
              let p := pow2Cap m cap
              let N' := min (2 * p + m) cap
              let w := min (10 * (N' + 1) ^ 2) cap
              let Jcols := (List.range N').filter fun j => u.1.1.2.testBit j
              let small : List ℕ := (List.range N').map fun j =>
                if u.1.1.2.testBit j then 0 else readChunk u.1.1.2 (N' + j * w) w
              let zFull : List ℤ := (List.range N').map fun j =>
                match (Jcols.zip u.1.2).find? (fun p => p.1 == j) with
                | some (_, q) => q.num
                | none => (small.getD j 0 : ℤ)
              ((List.range N').map fun j => csEntry m p u.2 j * zFull.getD j 0).sum)
            eTI encIntBin := by
          refine intBin_sum.comp
            (mapWithInput (unary_range' ((hN'.comp hq).comp (fst eT encUnary))) ?_)
          have hcsArg :=
            ((((hm.comp hq).prod (hp.comp hq)).comp (fst eT encUnary)).prod
              (snd eT encUnary)).comp (fst eTI encUnary) |>.prod (snd eTI encUnary)
          have hzArg :=
            (hzFull.comp ((fst eT encUnary).comp (fst eTI encUnary))).prod (snd eTI encUnary)
          exact intBin_mul'
            (by simpa only [Function.comp_def] using computableInPolyTime_csEntry.comp hcsArg)
            (by
              simpa only [Function.comp_def] using
                (listGetD (encA := encIntBin) (0 : ℤ)).comp hzArg)
        have hrhs_i : ComputableInPolyTime
            (fun u : ((ClosestStringInstance × ℕ) × List ℚ) × ℕ =>
              let p := pow2Cap u.1.1.1.strings.length (u.1.1.1.len + 1)
              let M' := min (p + u.1.1.1.strings.length) (u.1.1.1.len + 1)
              let counts := (List.range p).map fun τ =>
                (List.range u.1.1.1.len).countP fun col => colType u.1.1.1.strings col == τ
              ((List.range M').map fun i =>
                if i < p then (counts.getD i 0 : ℤ)
                else (min u.1.1.1.radius u.1.1.1.len : ℤ)).getD u.2 0)
            eTI encIntBin := by
          have hrArg := ((hrhsFull.comp hq).comp (fst eT encUnary)).prod (snd eT encUnary)
          simpa only [Function.comp_def] using (listGetD (encA := encIntBin) (0 : ℤ)).comp hrArg
        exact decide_eq' hdot hrhs_i
      exact bool_and.comp ((bool_and.comp (hlen_ok.prod hnonneg_ok)).prod heq_ok)
    have hopt := optionElimWithInput
      (body := fun (q : ClosestStringInstance × ℕ) (sol : List ℚ) =>
        let m := q.1.strings.length
        let cap := q.1.len + 1
        let p := pow2Cap m cap
        let M' := min (p + m) cap
        let N' := min (2 * p + m) cap
        let w := min (10 * (N' + 1) ^ 2) cap
        let Jcols := (List.range N').filter fun j => q.2.testBit j
        let small : List ℕ := (List.range N').map fun j =>
          if q.2.testBit j then 0 else readChunk q.2 (N' + j * w) w
        let counts : List ℕ := (List.range p).map fun τ =>
          (List.range q.1.len).countP fun col => colType q.1.strings col == τ
        let rhsFull : List ℤ := (List.range M').map fun i =>
          if i < p then (counts.getD i 0 : ℤ) else (min q.1.radius q.1.len : ℤ)
        decide (sol.length = Jcols.length) &&
        (sol.all fun q => decide (q.den = 1) && decide (0 ≤ q.num)) &&
        let zFull : List ℤ := (List.range N').map fun j =>
          match (Jcols.zip sol).find? (fun p => p.1 == j) with
          | some (_, q) => q.num
          | none => (small.getD j 0 : ℤ)
        (List.range M').all fun i =>
          decide (((List.range N').map fun j =>
            csEntry m p i j * zFull.getD j 0).sum = rhsFull.getD i 0))
      hsolve (const (encIn := encPair encClosestString encNat) false) hbody
    convert hopt using 1
    funext q; dsimp only; cases (ratSolve _).solution <;> rfl
  have hval : ComputableInPolyTime (fun q : ClosestStringInstance × ℕ => validClosestString q.1)
      (encPair encClosestString encNat) encBool :=
    computableInPolyTime_validClosestString.comp hx
  have hemp : ComputableInPolyTime (fun q : ClosestStringInstance × ℕ => q.1.strings.isEmpty)
      (encPair encClosestString encNat) encBool := (listIsEmpty' encBits).comp hstr
  have hle : ComputableInPolyTime (fun q : ClosestStringInstance × ℕ => decide (q.1.len ≤
    q.1.radius))
      (encPair encClosestString encNat) encBool :=
    binary_le.comp ((unary_to_binary.comp hlen).prod hrad)
  have hB : ComputableInPolyTime
      (fun q : ClosestStringInstance × ℕ =>
        let cap := q.1.len + 1
        let p2 := pow2Cap q.1.strings.length cap
        let N := min (2 * p2 + q.1.strings.length) cap
        decide (min (N + N * (10 * (N + 1) ^ 2)) cap ≤ q.1.len))
      (encPair encClosestString encNat) encBool := by
    have hN := computableInPolyTime_min_unary (unary_add' (unary_mul' (const 2) hp) hm) hcap
    have hN1 := unary_add' hN (const 1)
    have hB' := computableInPolyTime_min_unary
      (unary_add' hN (unary_mul' hN (unary_mul' (const 10) (unary_mul' hN1 hN1)))) hcap
    have hB_sq : ComputableInPolyTime
        (fun q : ClosestStringInstance × ℕ =>
          let cap := q.1.len + 1
          let p2 := pow2Cap q.1.strings.length cap
          let N := min (2 * p2 + q.1.strings.length) cap
          min (N + N * (10 * (N + 1) ^ 2)) cap)
        (encPair encClosestString encNat) encUnary := by
      convert hB' using 1; funext q; simp only [sq]
    exact unary_le.comp (hB_sq.prod hlen)
  unfold csCheck
  exact (bool_not.comp hval).ite (const false)
    (hemp.ite (const true) (hle.ite (const true) (hB.ite hlarge hsmall)))

/-- Correctness of `csCheck` over `r < 2 ^ csBranchBits x`. -/
private theorem csCheck_iff (x : ClosestStringInstance) :
    x ∈ BinaryClosestString ↔ ∃ r < 2 ^ csBranchBits x, csCheck (x, r) = true := by
  by_cases hWF : x.WellFormed
  · have hv : validClosestString x = true := (validClosestString_eq_true_iff x).mpr hWF
    by_cases hemp : x.strings.isEmpty
    · have hnil : x.strings = [] := List.isEmpty_iff.mp hemp
      simp only [csCheck, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hemp,
        csBranchBits, pow_zero]
      exact ⟨fun _ => ⟨0, Nat.zero_lt_one, trivial⟩,
             fun _ => ⟨hWF, List.replicate x.len false, List.length_replicate,
               fun s hs => by rw [hnil] at hs; exact nomatch hs⟩⟩
    · by_cases hle : x.len ≤ x.radius
      · simp only [csCheck, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hemp, hle,
          decide_true]
        exact ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (by positivity), trivial⟩,
               fun _ => ⟨hWF, List.replicate x.len false, List.length_replicate, fun s hs => by
                 have hbound : hammingDist (List.replicate x.len false) s ≤ x.len := by
                   simpa [hammingDist] using List.countP_le_length
                     (l := List.range (List.replicate x.len false).length)
                 exact le_trans hbound hle⟩⟩
      · simp only [csCheck, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hemp, hle,
          decide_false]
        obtain ⟨hcases_le, hcases_gt⟩ := csBranchBits_cases x hemp
        set m := x.strings.length
        set cap := x.len + 1
        set p2 := pow2Cap m cap
        set N := min (2 * p2 + m) cap
        set B := min (N + N * (10 * (N + 1) ^ 2)) cap
        by_cases hBle : B ≤ x.len
        · have hBle_raw : min (min (2 * pow2Cap x.strings.length (x.len + 1) + x.strings.length)
              (x.len + 1) + min (2 * pow2Cap x.strings.length (x.len + 1) + x.strings.length)
              (x.len + 1) * (10 * (min (2 * pow2Cap x.strings.length (x.len + 1) +
              x.strings.length) (x.len + 1) + 1) ^ 2)) (x.len + 1) ≤ x.len := hBle
          simp only [hBle_raw, decide_true, ↓reduceIte]
          obtain ⟨hp_eq, hM_eq, hN_eq, hw_eq, _, hbr_eq⟩ := hcases_le hBle
          rw [hbr_eq]
          constructor
          · -- Completeness: use `exists_nonneg_int_solution_independent_large` + `ratSolve_spec`.
            rintro ⟨_, hsol⟩
            obtain ⟨z₀, hz₀, hAz₀⟩ := (closestString_iff_ilp x hWF).mp hsol
            obtain ⟨z, hz, hAz, hinj⟩ := exists_nonneg_int_solution_independent_large
              (B := 1) (fun i j => abs_csEntry_le_one m (2 ^ m) i.val j.val) hz₀ hAz₀
            let K := (csNumCols m).factorial *
              (csNumRows m * ((csNumCols m + 1) * 1) ^ 2 + 1) ^ (csNumCols m)
            have hKlt : K < 2 ^ csSmallBits m := by
              simpa [K] using csKernelBound_lt_two_pow m
            let bits : List Bool :=
              (List.range (csNumCols m)).map (fun j =>
                if hj : j < csNumCols m then decide ((K : ℤ) ≤ z ⟨j, hj⟩) else false) ++
              ((List.range (csNumCols m)).flatMap fun j =>
                (List.range (csSmallBits m)).map fun t =>
                  if hj : j < csNumCols m then
                    if (K : ℤ) ≤ z ⟨j, hj⟩ then false else (z ⟨j, hj⟩).toNat.testBit t
                  else false)
            have hbits_len : bits.length = csTotalBits m := by
              simp [bits, csTotalBits]
            let r := ofBits bits
            have hr_lt : r < 2 ^ csTotalBits m := by
              rw [← hbits_len]; exact Nat.foldr_bit_lt bits
            have hr_testBit_head (j : ℕ) (hj : j < csNumCols m) :
                r.testBit j = decide ((K : ℤ) ≤ z ⟨j, hj⟩) := by
              dsimp only [r, ofBits]
              rw [testBit_foldr_bit,
                List.getD_eq_getElem _ _ (by rw [hbits_len]; unfold csTotalBits; omega)]
              rw [List.getElem_append_left (by simp [hj])]
              simp [hj]
            have hr_chunk (j : ℕ) (hj : j < csNumCols m) (hsmall : ¬(K : ℤ) ≤ z ⟨j, hj⟩) :
                readChunk r (csNumCols m + j * csSmallBits m) (csSmallBits m) =
                  (z ⟨j, hj⟩).toNat := by
              refine readChunk_of_pack (z ⟨j, hj⟩).toNat (by
                have hznn : 0 ≤ z ⟨j, hj⟩ := hz _
                have : (z ⟨j, hj⟩).toNat < K := by omega
                exact lt_trans this hKlt) r _ fun t ht => ?_
              dsimp only [r, ofBits]
              have hidx : csNumCols m + j * csSmallBits m + t < bits.length := by
                rw [hbits_len]; unfold csTotalBits
                have : j * csSmallBits m + t < csNumCols m * csSmallBits m := by
                  calc j * csSmallBits m + t < j * csSmallBits m + csSmallBits m := by omega
                    _ = (j + 1) * csSmallBits m := by ring
                    _ ≤ csNumCols m * csSmallBits m := Nat.mul_le_mul_right _ (by omega)
                omega
              rw [testBit_foldr_bit, List.getD_eq_getElem _ _ hidx,
                List.getElem_append_right (by simp; omega)]
              have hsub_idx : csNumCols m + j * csSmallBits m + t - csNumCols m =
                  j * csSmallBits m + t := by omega
              simp only [List.length_map, List.length_range, hsub_idx]
              -- Index into `flatMap` of uniform-length `csSmallBits m` lists:
              have hflat : ∀ (k : ℕ) (l : List ℕ) (f : ℕ → List Bool)
                  (hf : ∀ a ∈ l, (f a).length = k),
                  ∀ (idx : ℕ) (h1 : idx < l.length) (h2 : t < k)
                    (h3 : idx * k + t < (l.flatMap f).length),
                    (l.flatMap f)[idx * k + t] =
                      (f l[idx])[t]'(by rw [hf _ (List.getElem_mem h1)]; exact h2) := by
                intro k l f hf
                induction l with
                | nil => intro idx h1; simp at h1
                | cons hd tl ih =>
                  intro idx h1 h2 h3
                  cases idx with
                  | zero =>
                    simp only [zero_mul, zero_add, List.flatMap_cons, List.getElem_cons_zero]
                    exact List.getElem_append_left (by rw [hf hd (List.mem_cons_self)]; exact h2)
                  | succ idx =>
                    have hlen_hd : (f hd).length = k := hf hd List.mem_cons_self
                    simp only [List.flatMap_cons, List.getElem_cons_succ]
                    rw [List.getElem_append_right (by rw [hlen_hd, Nat.succ_mul]; omega)]
                    have heq_sub : (idx + 1) * k + t - (f hd).length = idx * k + t := by
                      rw [hlen_hd, Nat.succ_mul]; omega
                    simp only [heq_sub]
                    exact ih (fun a ha => hf a (List.mem_cons_of_mem _ ha)) idx
                      (by simpa using h1) h2 (by
                        rw [List.flatMap_cons, List.length_append, hlen_hd, Nat.succ_mul] at h3
                        omega)
              rw [hflat (csSmallBits m) (List.range (csNumCols m)) _ (fun _ _ => by simp)
                j (by simp [hj]) ht (by
                  simp only [bits, List.length_append, List.length_map, List.length_range] at hidx
                  omega)]
              simp [hj, hsmall]
            refine ⟨r, hr_lt, ?_⟩
            -- Now evaluate `checkLarge x r`: `Jcols` = `{j | K ≤ z j}`, `small` = `z` outside `J`,
            -- `ratSolve` returns `some sol` equal to `z_J`, so all checks pass!
            unfold checkLarge
            dsimp only [N, p2, cap, m] at hp_eq hM_eq hN_eq hw_eq
            rw [hp_eq] at hM_eq hN_eq hw_eq
            rw [hN_eq] at hw_eq
            simp only [hp_eq, hM_eq, hN_eq, hw_eq]
            set Jcols := (List.range (csNumCols m)).filter fun j => r.testBit j
            set small := (List.range (csNumCols m)).map fun j =>
              if r.testBit j then 0 else readChunk r (csNumCols m +
                j * csSmallBits m) (csSmallBits m)
            set counts := (List.range (2 ^ m)).map fun τ =>
              (List.range x.len).countP fun col => colType x.strings col == τ
            set rhsFull := (List.range (csNumRows m)).map fun i =>
              if i < 2 ^ m then (counts.getD i 0 : ℤ) else (min x.radius x.len : ℤ)
            set rhsJ := (List.range (csNumRows m)).map fun i =>
              let bi := rhsFull.getD i 0
              let sub := ((List.range (csNumCols m)).map fun j =>
                csEntry m (2 ^ m) i j * (small.getD j 0 : ℤ)).sum
              ((bi - sub : ℤ) : ℚ)
            set matJ : RatTable :=
              { numRows := csNumRows m
                numCols := Jcols.length
                rows := (List.range (csNumRows m)).map fun i =>
                  Jcols.map fun j => (csEntry m (2 ^ m) i j : ℚ) }
            have hJmem : ∀ j (hj : j < csNumCols m), j ∈ Jcols ↔ (K : ℤ) ≤ z ⟨j, hj⟩ := by
              intro j hj
              simp only [Jcols, List.mem_filter, List.mem_range, hj, true_and, hr_testBit_head j hj,
                decide_eq_true_eq]
            have hJlt : ∀ j ∈ Jcols, j < csNumCols m := fun j hj =>
              List.mem_range.mp (List.mem_filter.mp hj).1
            have hJnodup : Jcols.Nodup := (List.nodup_range).filter _
            have hsmall_eq : ∀ j (hj : j < csNumCols m),
                (small.getD j 0 : ℤ) = if (K : ℤ) ≤ z ⟨j, hj⟩ then 0 else z ⟨j, hj⟩ := by
              intro j hj
              rw [List.getD_eq_getElem _ _ (by simp [small, hj])]
              simp only [small, List.getElem_map, List.getElem_range, hr_testBit_head j hj,
                decide_eq_true_eq]
              split_ifs with hge
              · rfl
              · rw [hr_chunk j hj hge]
                have hzj : 0 ≤ z ⟨j, hj⟩ := hz ⟨j, hj⟩
                omega
            have hrhsFull_eq : ∀ i : Fin (csNumRows m), rhsFull.getD i.val 0 = csRHS x i := by
              intro i
              rw [List.getD_eq_getElem _ _ (by simp [rhsFull, i.isLt])]
              simp only [rhsFull, List.getElem_map, List.getElem_range, csRHS]
              split_ifs with hi
              · rw [List.getD_eq_getElem _ _ (by simp [counts, hi])]
                simp [counts]
              · rfl
            -- `z_J` solves `matJ.toMatrix *ᵥ z_J = rhsJ`!
            let zJ : Fin Jcols.length → ℚ := fun k =>
              (z ⟨Jcols[k.val], hJlt _ (List.getElem_mem k.isLt)⟩ : ℚ)
            have hmatJ_eq : ∀ (i : Fin (csNumRows m)) (k : Fin Jcols.length),
                matJ.toMatrix i k = (csEntry m (2 ^ m) i.val Jcols[k.val] : ℚ) := by
              intro i k
              have hrow : matJ.rows.getD i.val [] =
                  Jcols.map fun j => (csEntry m (2 ^ m) i.val j : ℚ) := by
                rw [List.getD_eq_getElem _ _ (by simp [matJ, i.isLt])]
                simp [matJ]
              simp only [Cslib.RowTable.toMatrix_apply, Cslib.RowTable.entry, hrow]
              rw [List.getD_eq_getElem _ _ (by simp [k.isLt]), List.getElem_map]
            have hsol_zJ : matJ.toMatrix *ᵥ zJ = fun i => rhsJ.getD i.val 0 := by
              ext i
              rw [List.getD_eq_getElem _ _ (by simp [rhsJ, matJ, i.isLt])]
              simp only [Matrix.mulVec, dotProduct, hmatJ_eq, zJ, rhsJ,
                List.getElem_map, List.getElem_range]
              rw [hrhsFull_eq i, ← congrFun hAz i]
              simp only [Matrix.mulVec, dotProduct]
              have hsum_small :
                  ((List.range (csNumCols m)).map fun j =>
                    csEntry m (2 ^ m) i.val j * (small.getD j 0 : ℤ)).sum =
                  ∑ j : Fin (csNumCols m),
                    csEntry m (2 ^ m) i.val j.val *
                      (if (K : ℤ) ≤ z j then 0 else z j) := by
                rw [list_sum_map_range, ← Fin.sum_univ_eq_sum_range]
                exact Finset.sum_congr rfl fun j _ => by rw [hsmall_eq j.val j.isLt]
              rw [hsum_small]
              push_cast
              have hsplit_J :
                  (∑ j : Fin (csNumCols m), (csEntry m (2 ^ m) i.val j.val : ℚ) * (z j : ℚ)) -
                  (∑ j : Fin (csNumCols m), (csEntry m (2 ^ m) i.val j.val : ℚ) *
                    if (K : ℤ) ≤ z j then 0 else (z j : ℚ)) =
                  ∑ j : {j : Fin (csNumCols m) // (K : ℤ) ≤ z j},
                    (csEntry m (2 ^ m) i.val j.1.val : ℚ) * (z j.1 : ℚ) := by
                rw [← Finset.sum_sub_distrib,
                  ← Fintype.sum_subtype_add_sum_subtype (fun j : Fin (csNumCols m) => (K : ℤ) ≤
                    z j)]
                have hzero : ∑ j : {j : Fin (csNumCols m) // ¬(K : ℤ) ≤ z j},
                    ((csEntry m (2 ^ m) i.val j.1.val : ℚ) * (z j.1 : ℚ) -
                     (csEntry m (2 ^ m) i.val j.1.val : ℚ) *
                       if (K : ℤ) ≤ z j.1 then 0 else (z j.1 : ℚ)) = 0 :=
                  Finset.sum_eq_zero fun j _ => by simp [j.2]
                rw [hzero, add_zero]
                exact Finset.sum_congr rfl fun j _ => by simp [j.2]
              -- Match `∑ k : Fin Jcols.length` with `∑ j : {j // K ≤ z j}` via equivalence!
              have hbij : ∃ e : Fin Jcols.length ≃ {j : Fin (csNumCols m) // (K : ℤ) ≤ z j},
                  ∀ k, (e k).1 = ⟨Jcols[k.val], hJlt _ (List.getElem_mem k.isLt)⟩ := by
                refine ⟨Equiv.ofBijective
                  (fun k => ⟨⟨Jcols[k.val], hJlt _ (List.getElem_mem k.isLt)⟩,
                    (hJmem _ _).mp (List.getElem_mem k.isLt)⟩) ⟨?_, ?_⟩, fun _ => rfl⟩
                · intro k1 k2 h
                  have hval : Jcols[k1.val] = Jcols[k2.val] := by
                    simpa [Subtype.ext_iff, Fin.ext_iff] using h
                  exact List.nodup_iff_injective_getElem.mp hJnodup hval
                · rintro ⟨⟨j, hj⟩, hge⟩
                  obtain ⟨k, hk, heq⟩ := List.getElem_of_mem ((hJmem j hj).mpr hge)
                  exact ⟨⟨k, hk⟩, Subtype.ext (Fin.ext heq)⟩
              obtain ⟨e, he⟩ := hbij
              rw [hsplit_J, ← e.sum_comp]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [he k]
            -- By `ratSolve_spec`, `ratSolve` returns `some sol` and by `hinj`, `sol = zJ`!
            obtain ⟨hspec_some, hspec_none⟩ := ratSolve_spec ⟨matJ, rhsJ⟩
            have hne_none : (ratSolve ⟨matJ, rhsJ⟩).solution ≠ none := fun hnone =>
              (hspec_none.mp hnone) ⟨zJ, hsol_zJ⟩
            obtain ⟨sol, hsol_eq⟩ := Option.ne_none_iff_exists'.mp hne_none
            rw [hsol_eq]
            obtain ⟨hsol_len, hsol_mul⟩ := hspec_some sol hsol_eq
            have hsol_len' : sol.length = Jcols.length := hsol_len
            have hsol_eq_zJ : ∀ k : Fin Jcols.length, sol.getD k.val 0 = zJ k := by
              have hdiff : matJ.toMatrix *ᵥ ((fun k : Fin Jcols.length => sol.getD k.val 0) - zJ) =
                0 := by
                rw [Matrix.mulVec_sub, hsol_mul, hsol_zJ, sub_self]
              -- Transfer injectivity of `A_J` along `e : Fin Jcols.length ≃ {j // K ≤ z j}`.
              have hbij : ∃ e : Fin Jcols.length ≃ {j : Fin (csNumCols m) // (K : ℤ) ≤ z j},
                  ∀ k, (e k).1 = ⟨Jcols[k.val], hJlt _ (List.getElem_mem k.isLt)⟩ := by
                refine ⟨Equiv.ofBijective
                  (fun k => ⟨⟨Jcols[k.val], hJlt _ (List.getElem_mem k.isLt)⟩,
                    (hJmem _ _).mp (List.getElem_mem k.isLt)⟩) ⟨?_, ?_⟩, fun _ => rfl⟩
                · intro k1 k2 h
                  have hval : Jcols[k1.val] = Jcols[k2.val] := by
                    simpa [Subtype.ext_iff, Fin.ext_iff] using h
                  exact List.nodup_iff_injective_getElem.mp hJnodup hval
                · rintro ⟨⟨j, hj⟩, hge⟩
                  obtain ⟨k, hk, heq⟩ := List.getElem_of_mem ((hJmem j hj).mpr hge)
                  exact ⟨⟨k, hk⟩, Subtype.ext (Fin.ext heq)⟩
              obtain ⟨e, he⟩ := hbij
              let d : Fin Jcols.length → ℚ := (fun k => sol.getD k.val 0) - zJ
              have hd0 : (fun j : {j : Fin (csNumCols m) // (K : ℤ) ≤ z j} => d (e.symm j)) =
                0 := by
                apply hinj
                ext i
                simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
                  map_zero, Pi.zero_apply]
                rw [← e.sum_comp]
                refine (Finset.sum_congr rfl fun k _ => ?_).trans
                  (by simpa only [Matrix.mulVec, dotProduct, hmatJ_eq, Pi.zero_apply]
                    using congrFun hdiff i)
                congr 1
                · exact congrArg Int.cast
                    (by change csEntry m (2 ^ m) i.val (e k).1.val = _; rw [he])
                · exact congrArg d (Equiv.symm_apply_apply e k)
              intro k
              have := congrFun hd0 (e k)
              simp only [Equiv.symm_apply_apply, Pi.zero_apply, d, Pi.sub_apply,
                sub_eq_zero] at this
              exact this
            have hsol_all : (sol.all fun q => decide (q.den = 1) && decide (0 ≤ q.num)) = true := by
              rw [List.all_eq_true]
              intro q hq
              obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
              have hk' : k < Jcols.length := hsol_len' ▸ hk
              have hqk : sol[k] = (z ⟨Jcols[k], hJlt _ (List.getElem_mem hk')⟩ : ℚ) := by
                have := hsol_eq_zJ ⟨k, hk'⟩
                rwa [List.getD_eq_getElem _ _ hk] at this
              rw [hqk]
              simp only [Rat.den_intCast, Rat.num_intCast, decide_true, Bool.true_and]
              exact decide_eq_true (hz ⟨Jcols[k], hJlt _ (List.getElem_mem hk')⟩)
            simp only [hsol_len', decide_true, hsol_all, Bool.true_and]
            rw [List.all_eq_true]
            intro i hi
            have hilt := List.mem_range.mp hi
            rw [decide_eq_true_eq]
            have hzFull_eq : ∀ j (hj : j < csNumCols m),
                ((List.range (csNumCols m)).map fun j =>
                  match (Jcols.zip sol).find? (fun p => p.1 == j) with
                  | some (_, q) => q.num
                  | none => (small.getD j 0 : ℤ)).getD j 0 = z ⟨j, hj⟩ := by
              intro j hj
              rw [List.getD_eq_getElem _ _ (by simp [hj]), List.getElem_map, List.getElem_range]
              by_cases hge : (K : ℤ) ≤ z ⟨j, hj⟩
              · obtain ⟨k, hk, heq⟩ := List.getElem_of_mem ((hJmem j hj).mpr hge)
                have hfind : (Jcols.zip sol).find? (fun p => p.1 == j) =
                    some (j, sol[k]'(hsol_len'.symm ▸ hk)) := by
                  have hpair : ∀ (l1 : List ℕ) (l2 : List ℚ), l1.Nodup →
                      ∀ (hle_l : l1.length = l2.length) (k : ℕ) (hk : k < l1.length),
                        (l1.zip l2).find? (fun p => p.1 == l1[k]) =
                          some (l1[k], l2[k]'(hle_l ▸ hk)) := by
                    intro l1 l2 hnd hle_l
                    induction l1 generalizing l2 with
                    | nil => intro k hk; simp at hk
                    | cons a tl ih =>
                      cases l2 with
                      | nil => simp at hle_l
                      | cons b tl2 =>
                        intro k hk
                        cases k with
                        | zero => simp
                        | succ k =>
                          have hk_tl : k < tl.length := Nat.lt_of_succ_lt_succ hk
                          have hne : a ≠ tl[k] := fun he =>
                            (List.nodup_cons.mp hnd).1 (he ▸ List.getElem_mem hk_tl)
                          simp only [List.zip_cons_cons, List.find?_cons, List.getElem_cons_succ,
                            beq_eq_false_iff_ne.mpr hne]
                          exact ih tl2 (List.nodup_cons.mp hnd).2 (Nat.succ.inj hle_l) k hk_tl
                  simpa [heq] using hpair Jcols sol hJnodup hsol_len'.symm k hk
                rw [hfind]
                have hqk := hsol_eq_zJ ⟨k, hk⟩
                rw [List.getD_eq_getElem _ _ (hsol_len'.symm ▸ hk)] at hqk
                simp [hqk, zJ, heq]
              · have hnone : (Jcols.zip sol).find? (fun p => p.1 == j) = none := by
                  rw [List.find?_eq_none]
                  intro p hp
                  have hp1 : p.1 ∈ Jcols := (List.of_mem_zip hp).1
                  rw [beq_iff_eq]
                  intro heq
                  exact hge ((hJmem j hj).mp (heq ▸ hp1))
                rw [hnone, hsmall_eq j hj]
                simp only [hge, ↓reduceIte]
            have hsum_eq :
                ((List.range (csNumCols m)).map fun j =>
                  csEntry m (2 ^ m) i j *
                    ((List.range (csNumCols m)).map fun j =>
                      match (Jcols.zip sol).find? (fun p => p.1 == j) with
                      | some (_, q) => q.num
                      | none => (small.getD j 0 : ℤ)).getD j 0).sum =
                (csMatrix m *ᵥ z) ⟨i, hilt⟩ := by
              rw [list_sum_map_range, ← Fin.sum_univ_eq_sum_range]
              simp only [csMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply]
              exact Finset.sum_congr rfl fun j _ => by rw [hzFull_eq j.val j.isLt]
            have hAz' : (csMatrix m *ᵥ z) ⟨i, hilt⟩ = csRHS x ⟨i, hilt⟩ := congrFun hAz ⟨i, hilt⟩
            rw [hsum_eq, hAz', hrhsFull_eq ⟨i, hilt⟩]
          · -- Soundness: `checkLarge x r = true` verifies `0 ≤ zFull` and `A *ᵥ zFull = b`!
            rintro ⟨r, _, hchk⟩
            unfold checkLarge at hchk
            dsimp only [N, p2, cap, m] at hp_eq hM_eq hN_eq hw_eq
            rw [hp_eq] at hM_eq hN_eq hw_eq
            rw [hN_eq] at hw_eq
            simp only [hp_eq, hM_eq, hN_eq, hw_eq] at hchk
            split at hchk
            · cases hchk
            · rename_i sol hsol_eq
              simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
              obtain ⟨⟨hlen_sol, hall_q⟩, hall_eq⟩ := hchk
              set Jcols := (List.range (csNumCols m)).filter fun j => r.testBit j
              set small := (List.range (csNumCols m)).map fun j =>
                if r.testBit j then 0 else readChunk r (csNumCols m +
                  j * csSmallBits m) (csSmallBits m)
              set zFull := (List.range (csNumCols m)).map fun j =>
                match (Jcols.zip sol).find? (fun p => p.1 == j) with
                | some (_, q) => q.num
                | none => (small.getD j 0 : ℤ)
              refine ⟨hWF, (closestString_iff_ilp x hWF).mpr ⟨fun j => zFull.getD j.val 0, ?_, ?_⟩⟩
              · intro j
                change 0 ≤ zFull.getD j.val 0
                rw [List.getD_eq_getElem _ _ (by simp [zFull, m, j.isLt])]
                simp only [zFull, List.getElem_map, List.getElem_range]
                cases hf : (Jcols.zip sol).find? (fun p => p.1 == j.val) with
                | none => exact Int.natCast_nonneg _
                | some pq =>
                  exact (hall_q pq.2 (List.of_mem_zip (List.mem_of_find?_eq_some hf)).2).2
              · ext i
                have hi := hall_eq i.val (List.mem_range.mpr i.isLt)
                simp only [csMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, csRHS]
                have hsum_eq :
                    ∑ j : Fin (csNumCols m), csEntry m (2 ^ m) i.val j.val * zFull.getD j.val 0 =
                    ((List.range (csNumCols m)).map fun j =>
                      csEntry m (2 ^ m) i.val j * zFull.getD j 0).sum := by
                  rw [list_sum_map_range, ← Fin.sum_univ_eq_sum_range]
                rw [hsum_eq, hi]
                rw [List.getD_eq_getElem _ _ (by simp [i.isLt])]
                simp only [List.getElem_map, List.getElem_range]
                split_ifs with hip
                · rw [List.getD_eq_getElem _ _ (by simp [hip])]
                  simp
                · rfl
        · -- Small `x.len < B`: brute-force `2 ^ x.len` strings `v` via `checkSmall`.
          have hBle_raw : ¬ min (min (2 * pow2Cap x.strings.length (x.len + 1) + x.strings.length)
              (x.len + 1) + min (2 * pow2Cap x.strings.length (x.len + 1) + x.strings.length)
              (x.len + 1) * (10 * (min (2 * pow2Cap x.strings.length (x.len + 1) +
              x.strings.length) (x.len + 1) + 1) ^ 2)) (x.len + 1) ≤ x.len := hBle
          simp only [hBle_raw, decide_false, Bool.false_eq_true, ↓reduceIte, hcases_gt hBle]
          constructor
          · rintro ⟨_, v, hvlen, hv⟩
            let r := ofBits v
            refine ⟨r, hvlen ▸ Nat.foldr_bit_lt v, ?_⟩
            unfold checkSmall
            have hv_eq : (List.range x.len).map (fun j => r.testBit j) = v := by
              refine List.ext_getElem (by simp [hvlen]) fun j hj _ => ?_
              simp only [List.getElem_map, List.getElem_range, r, ofBits, testBit_foldr_bit]
              exact List.getD_eq_getElem _ _ (by omega)
            rw [hv_eq, List.all_eq_true]
            intro s hs; exact decide_eq_true (hv s hs)
          · rintro ⟨r, _, hchk⟩
            unfold checkSmall at hchk
            rw [List.all_eq_true] at hchk
            exact ⟨hWF, (List.range x.len).map (fun j => r.testBit j), by simp,
              fun s hs => decide_eq_true_eq.mp (hchk s hs)⟩
  · have hv : validClosestString x = false :=
      Bool.eq_false_iff.mpr (mt (validClosestString_eq_true_iff x).mp hWF)
    simp only [csCheck, hv, Bool.not_false, ↓reduceIte, Bool.false_eq_true, and_false,
      exists_false, iff_false]
    intro hx; exact hWF hx.1

/-- **Gramm–Niedermeier–Rossmanith**: `BinaryClosestString` is fixed-parameter tractable
parameterized by the number of input strings `x.strings.length` (proved directly under standard
Lean axioms via independent-large-coordinates ILP + Bareiss–Jordan `ratSolve` +
  exhaustive search).
-/
theorem BinaryClosestString_mem_FPT :
    BinaryClosestString ∈ FPT encClosestString (fun x => x.strings.length) := by
  have hB : DecidableInExpTime ({true} : Set Bool) encBool (fun _ => 0) 0 :=
    DecidableInExpTime.of_computableInPolyTime (ComputableInPolyTime.id' (encIn := encBool))
      (fun b => by simp [Set.mem_singleton_iff])
  have hexp :=
    DecidableInExpTime.of_exhaustiveSearch
      (B := {true}) (μA := csBranchBits) (μB := fun _ => 0) (c := 0) (M := 1) (K := 0) (δ := 0)
      computableInPolyTime_csCheck computableInPolyTime_csBranchBits
      (fun x => by simpa using csCheck_iff x)
      (fun _ _ => by simp) (fun _ => by simp) (le_refl 0) hB
  exact FPT_subset_FPT_of_le_comp csBranchBits_le_csTotalBits hexp.mem_FPT

end Cslib.Complexity
