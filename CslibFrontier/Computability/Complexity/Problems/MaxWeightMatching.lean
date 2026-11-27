/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Foundations.Data.Nat.Bits
import CslibFrontier.Foundations.Data.Rat.Basic
import Mathlib.Data.List.GetD

/-!
# Maximum Weight Matching and Simple b-Matching

This module defines the decision problems for maximum-weight matching in simple undirected graphs
with nonnegative rational edge weights (`CslibFrontier.Complexity.MaxWeightMatching`) and
capacitated
maximum-weight simple `b`-matching (`CslibFrontier.Complexity.MaxWeightSimpleBMatching`), proves
polynomial-time rational list summation (`CslibFrontier.Complexity.computableInPolyTime_ratSum`),
proves that `MaxWeightMatching` lies in `NP`, establishes exact non-degenerate positive and
negative benchmarks on the triangle `K₃`, and proves the polynomial-time many-one reduction from
simple `b`-matching to ordinary maximum-weight matching via Tutte's edge-splitting gadget under
standard Lean axioms.

## Main definitions

* `CslibFrontier.Complexity.WeightedEdge`: an undirected weighted edge `(u, v, weight)`.
* `CslibFrontier.Complexity.MaxWeightMatchingInstance`: instance `(numVertices, edges, threshold)`.
* `CslibFrontier.Complexity.encMaxWeightMatching`: polynomial-time encoding with unary vertex count.
* `CslibFrontier.Complexity.MaxWeightMatching`: decision problem for maximum-weight matching.
* `CslibFrontier.Complexity.SimpleBMatchingInstance`: capacitated simple `b`-matching instance.
* `CslibFrontier.Complexity.MaxWeightSimpleBMatching`: decision problem for simple `b`-matching.

## Main results

* `CslibFrontier.Complexity.computableInPolyTime_ratSum`: `List.sum` on `ℚ` is polynomial-time.
* `CslibFrontier.Complexity.MaxWeightMatching_mem_NP`:
  `MaxWeightMatching ∈ NP encMaxWeightMatching`.
* `CslibFrontier.Complexity.polyTimeReducible_simpleBMatching_maxWeightMatching`: Tutte's
  polynomial-time
  reduction from `MaxWeightSimpleBMatching` to `MaxWeightMatching`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-- An undirected edge between vertices `u` and `v` with rational weight `weight`. -/
@[ext]
structure WeightedEdge where
  /-- First endpoint. -/
  u : ℕ
  /-- Second endpoint. -/
  v : ℕ
  /-- Edge weight. -/
  weight : ℚ
  deriving DecidableEq, Repr

/-- Binary encoding of a `WeightedEdge` as `(u, v, weight)`. -/
enc_structure encWeightedEdge : WeightedEdge where
  u : encNat, v : encNat, weight : encRat

attribute [fun_prop] encWeightedEdge_u_polyTime encWeightedEdge_v_polyTime
  encWeightedEdge_weight_polyTime encWeightedEdge_mk_polyTime

/-- An instance of the maximum-weight matching decision problem on `{0, …, numVertices - 1}`. -/
@[ext]
structure MaxWeightMatchingInstance where
  /-- Number of vertices (encoded in unary so graph size bounds `numVertices`). -/
  numVertices : ℕ
  /-- List of weighted undirected edges. -/
  edges : List WeightedEdge
  /-- Target total matching weight. -/
  threshold : ℚ
  deriving DecidableEq, Repr

/-- List encoding of weighted edges for `enc_structure`. -/
abbrev encWeightedEdgeList : List WeightedEdge ↪ List Bool := encList encWeightedEdge

/-- Encoding of `MaxWeightMatchingInstance` with `numVertices` in unary and weights in binary. -/
enc_structure encMaxWeightMatching : MaxWeightMatchingInstance where
  numVertices : encUnary, edges : encWeightedEdgeList, threshold : encRat

attribute [fun_prop] encMaxWeightMatching_numVertices_polyTime
  encMaxWeightMatching_edges_polyTime encMaxWeightMatching_threshold_polyTime
  encMaxWeightMatching_mk_polyTime

/-- Canonical unordered endpoint key of a weighted edge. -/
@[expose]
def WeightedEdge.pairKey (e : WeightedEdge) : ℕ × ℕ :=
  (min e.u e.v, max e.u e.v)

/-- Two edges are vertex-disjoint if they share no endpoint. -/
@[expose]
def WeightedEdge.Disjoint (e₁ e₂ : WeightedEdge) : Prop :=
  e₁.u ≠ e₂.u ∧ e₁.u ≠ e₂.v ∧ e₁.v ≠ e₂.u ∧ e₁.v ≠ e₂.v

/-- A `MaxWeightMatchingInstance` is well-formed when all edges are loopless, stay within
`{0, …, numVertices - 1}`, have nonnegative rational weights, and define a simple graph (no
duplicate unordered pairs). -/
@[expose]
def MaxWeightMatchingInstance.IsWellFormed (x : MaxWeightMatchingInstance) : Prop :=
  (∀ e ∈ x.edges, e.u < x.numVertices ∧ e.v < x.numVertices ∧ e.u ≠ e.v ∧ 0 ≤ e.weight) ∧
    (x.edges.map WeightedEdge.pairKey).Nodup

/-- `M` is a matching in `x` if every edge of `M` belongs to `x.edges` and distinct edges of `M`
are pairwise vertex-disjoint. -/
@[expose]
def MaxWeightMatchingInstance.IsMatching (x : MaxWeightMatchingInstance)
    (M : Finset WeightedEdge) : Prop :=
  (∀ e ∈ M, e ∈ x.edges) ∧
    ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → e₁.Disjoint e₂

/-- Total weight of a finite set of weighted edges. -/
@[expose]
def matchingWeight (M : Finset WeightedEdge) : ℚ :=
  ∑ e ∈ M, e.weight

/-- The **Maximum Weight Matching** decision problem: well-formed simple weighted graphs
admitting a matching of total weight at least `threshold`. -/
@[expose]
def MaxWeightMatching : Set MaxWeightMatchingInstance :=
  {x | x.IsWellFormed ∧ ∃ M : Finset WeightedEdge, x.IsMatching M ∧ x.threshold ≤ matchingWeight M}

/-! ### Polynomial-time rational list summation -/

private theorem rat_add_num_den_le (a b : ℚ) :
    (a + b).num.natAbs ≤ a.num.natAbs * b.den + b.num.natAbs * a.den ∧
      (a + b).den ≤ a.den * b.den := by
  have hdiv : a + b = Rat.divInt (a.num * (b.den : ℤ) + b.num * (a.den : ℤ))
      ((a.den * b.den : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div]
    conv_lhs => rw [← Rat.num_div_den a, ← Rat.num_div_den b]
    have ha : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr a.den_nz
    have hb : (b.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr b.den_nz
    push_cast
    field_simp
  have h1 : (a + b).num.natAbs ≤
      (a.num * (b.den : ℤ) + b.num * (a.den : ℤ)).natAbs := by
    rw [hdiv, Rat.natAbs_num_divInt]
    split_ifs
    · exact Nat.zero_le _
    · exact Nat.div_le_self _ _
  have h2 : (a + b).den ≤ (a.den * b.den : ℕ) := by
    rw [hdiv]
    have hpos : ((a.den * b.den : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos a.den_pos b.den_pos).ne'
    have hd := Rat.den_divInt (a.num * (b.den : ℤ) + b.num * (a.den : ℤ)) (a.den * b.den : ℕ)
    simp only [hpos, ↓reduceIte, Int.natAbs_natCast] at hd
    rw [hd]
    exact Nat.div_le_self _ _
  refine ⟨h1.trans ?_, h2⟩
  calc
    (a.num * (b.den : ℤ) + b.num * (a.den : ℤ)).natAbs
        ≤ (a.num * (b.den : ℤ)).natAbs + (b.num * (a.den : ℤ)).natAbs := Int.natAbs_add_le _ _
    _ = a.num.natAbs * b.den + b.num.natAbs * a.den := by
      simp [Int.natAbs_mul]

private theorem nat_lt_two_pow_bits_length (n : ℕ) : n < 2 ^ n.bits.length := by
  have := Nat.foldr_bit_lt n.bits
  rwa [Nat.foldr_bit_bits] at this

private theorem bits_length_le_of_lt_two_pow {n k : ℕ} (h : n < 2 ^ k) :
    n.bits.length ≤ k := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr h

private theorem encRat_length_le (q : ℚ) :
    (encRat q).length ≤ 2 * q.num.natAbs.bits.length + q.den.bits.length + 3 := by
  rw [encRat_apply, length_encPair, encIntBin_apply, List.length_cons]
  have hden : (encNat q.den).length = q.den.bits.length := by
    simp [encNat_apply]
  dsimp only at *
  omega

private theorem bits_length_le_encRat (q : ℚ) :
    q.num.natAbs.bits.length ≤ (encRat q).length ∧
      q.den.bits.length ≤ (encRat q).length := by
  rw [encRat_apply, length_encPair, encIntBin_apply, List.length_cons]
  have hden : (encNat q.den).length = q.den.bits.length := by
    simp [encNat_apply]
  dsimp only at *
  omega

/-- Rational list summation `List.sum` is computable in polynomial time under `encList encRat`. -/
@[fun_prop]
theorem computableInPolyTime_ratSum :
    ComputableInPolyTime (fun l : List ℚ => l.sum) (encList encRat) encRat := by
  have hfold : ComputableInPolyTime (fun l : List ℚ =>
    l.foldl (· + ·) 0) (encList encRat) encRat := by
    let B := fun l : List ℚ =>
      10 * (((encList encRat l).length + 1) * ((encList encRat l).length + 1))
    have hB : PolyBounded (fun l : List ℚ => (encList encRat l).length) B :=
      (PolyBounded.const 10).mul
        ((PolyBounded.self.add (.const 1)).mul (PolyBounded.self.add (.const 1)))
    refine ComputableInPolyTime.foldl' (encA := encRat) (encB := encRat) (encL := encList encRat)
      ComputableInPolyTime.id' (ComputableInPolyTime.const 0)
      ComputableInPolyTime.rat_add hB (fun l i hi => ?_)
    set M := (encList encRat l).length
    have hM_elem : ∀ q ∈ l.take i, q.num.natAbs < 2 ^ M ∧ q.den < 2 ^ M := by
      intro q hq
      have hql : q ∈ l := List.mem_of_mem_take hq
      have hlen : (encRat q).length ≤ M :=
        (SizedListEncoding.length_elem_le (encA := encRat) (encL := encList encRat) l q hql)
      have hb := bits_length_le_encRat q
      exact ⟨(nat_lt_two_pow_bits_length _).trans_le (Nat.pow_le_pow_right (by omega) (hb.1.trans
        hlen)),
        (nat_lt_two_pow_bits_length _).trans_le (Nat.pow_le_pow_right (by omega) (hb.2.trans hlen))⟩
    have hinv : ∀ (t : List ℚ), (∀ q ∈ t, q.num.natAbs < 2 ^ M ∧ q.den < 2 ^ M) →
        (t.foldl (· + ·) 0).num.natAbs ≤ t.length * 2 ^ (M * (t.length + 1)) ∧
          (t.foldl (· + ·) 0).den ≤ 2 ^ (M * t.length) := by
      intro t ht
      have hrev : ∀ (t : List ℚ) (acc : ℚ) (k : ℕ),
          (∀ q ∈ t, q.num.natAbs < 2 ^ M ∧ q.den < 2 ^ M) →
          acc.num.natAbs ≤ k * 2 ^ (M * (k + 1)) →
          acc.den ≤ 2 ^ (M * k) →
          (t.foldl (· + ·) acc).num.natAbs ≤ (k + t.length) * 2 ^ (M * (k + t.length + 1)) ∧
            (t.foldl (· + ·) acc).den ≤ 2 ^ (M * (k + t.length)) := by
        intro t
        induction t with
        | nil =>
          intro acc k _ hnum hden
          simpa using ⟨hnum, hden⟩
        | cons q qs ih =>
          intro acc k hqs hnum hden
          have hq := hqs q (List.mem_cons_self ..)
          have hqs' : ∀ x ∈ qs, x.num.natAbs < 2 ^ M ∧ x.den < 2 ^ M := fun x hx =>
            hqs x (List.mem_cons_of_mem _ hx)
          have hadd := rat_add_num_den_le acc q
          have hden' : (acc + q).den ≤ 2 ^ (M * (k + 1)) := by
            calc
              (acc + q).den ≤ acc.den * q.den := hadd.2
              _ ≤ 2 ^ (M * k) * 2 ^ M := Nat.mul_le_mul hden (le_of_lt hq.2)
              _ = 2 ^ (M * k + M) := by rw [← pow_add]
              _ = 2 ^ (M * (k + 1)) := by ring_nf
          have hnum' : (acc + q).num.natAbs ≤ (k + 1) * 2 ^ (M * (k + 1 + 1)) := by
            have hp1 : 2 ^ (M * (k + 1)) * 2 ^ M = 2 ^ (M * (k + 2)) := by
              rw [← pow_add]; ring_nf
            have hp2 : 2 ^ M * 2 ^ (M * k) ≤ 2 ^ (M * (k + 2)) := by
              rw [← pow_add]
              exact Nat.pow_le_pow_right (by omega) (by nlinarith)
            calc
              (acc + q).num.natAbs ≤ acc.num.natAbs * q.den + q.num.natAbs * acc.den := hadd.1
              _ ≤ (k * 2 ^ (M * (k + 1))) * 2 ^ M + 2 ^ M * 2 ^ (M * k) :=
                Nat.add_le_add (Nat.mul_le_mul hnum (le_of_lt hq.2))
                  (Nat.mul_le_mul (le_of_lt hq.1) hden)
              _ = k * (2 ^ (M * (k + 1)) * 2 ^ M) + 2 ^ M * 2 ^ (M * k) := by ring
              _ ≤ k * 2 ^ (M * (k + 2)) + 2 ^ (M * (k + 2)) := by
                rw [hp1]; exact Nat.add_le_add_left hp2 _
              _ = (k + 1) * 2 ^ (M * (k + 1 + 1)) := by ring
          have hres := ih (acc + q) (k + 1) hqs' hnum' hden'
          simpa only [List.foldl_cons, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hres
      simpa using hrev t 0 0 ht (by simp) (by simp)
    have htake := hinv (l.take i) hM_elem
    have hlen_le : (l.take i).length ≤ M := by
      have hlM : l.length ≤ M :=
        SizedListEncoding.length_le (encA := encRat) (encL := encList encRat) l
      rw [List.length_take]
      exact (Nat.min_le_right _ _).trans hlM
    have hpow_num : ((l.take i).foldl (· + ·) 0).num.natAbs < 2 ^ (M * (M + 2) + 1) := by
      have h1 : (l.take i).length ≤ 2 ^ M := (Nat.lt_two_pow_self).le.trans
        (Nat.pow_le_pow_right (by omega) hlen_le)
      have h2 : (l.take i).length * 2 ^ (M * ((l.take i).length + 1)) ≤
          2 ^ M * 2 ^ (M * (M + 1)) :=
        Nat.mul_le_mul h1 (Nat.pow_le_pow_right (by omega) (by nlinarith))
      have h3 : 2 ^ M * 2 ^ (M * (M + 1)) = 2 ^ (M * (M + 2)) := by
        rw [← pow_add]; ring_nf
      have h4 : 2 ^ (M * (M + 2)) < 2 ^ (M * (M + 2) + 1) :=
        Nat.pow_lt_pow_right (by omega) (by omega)
      exact lt_of_le_of_lt (htake.1.trans (h2.trans_eq h3)) h4
    have hpow_den : ((l.take i).foldl (· + ·) 0).den < 2 ^ (M * M + 1) := by
      have h2 : 2 ^ (M * (l.take i).length) ≤ 2 ^ (M * M) :=
        Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left M hlen_le)
      exact lt_of_le_of_lt (htake.2.trans h2) (Nat.pow_lt_pow_right (by omega) (by omega))
    have hb1 := bits_length_le_of_lt_two_pow hpow_num
    have hb2 := bits_length_le_of_lt_two_pow hpow_den
    have he := encRat_length_le ((l.take i).foldl (· + ·) 0)
    dsimp only [B]
    nlinarith
  exact hfold.of_enc_eq fun l => by
    congr 1
    rw [List.sum_eq_foldl]

/-! ### Non-degenerate benchmarks and NP membership for `MaxWeightMatching` -/

private def triangleInstance (t : ℚ) : MaxWeightMatchingInstance :=
  ⟨3, [⟨0, 1, 3⟩, ⟨1, 2, 4⟩, ⟨0, 2, 5⟩], t⟩

/-- Positive non-degenerate benchmark: the triangle `K₃` with weights `3, 4, 5` has a matching of
weight `5`. -/
private theorem triangleInstance_five_mem : triangleInstance 5 ∈ MaxWeightMatching := by
  refine ⟨⟨?_, ?_⟩, {⟨0, 2, 5⟩}, ⟨?_, ?_⟩, ?_⟩
  · intro e he
    simp only [triangleInstance, List.mem_cons, List.not_mem_nil, or_false] at he ⊢
    rcases he with rfl | rfl | rfl <;> norm_num
  · simp only [triangleInstance, List.map_cons, List.map_nil, WeightedEdge.pairKey]
    decide
  · intro e he
    rw [Finset.mem_singleton] at he; subst he; simp [triangleInstance]
  · intro e₁ h₁ e₂ h₂ hne
    rw [Finset.mem_singleton] at h₁ h₂; exact absurd (h₁.trans h₂.symm) hne
  · simp [matchingWeight, triangleInstance]

/-- Negative sharpness benchmark: every matching in the weighted triangle `K₃` with weights
`3, 4, 5` has weight at most `5`, so threshold `6` is rejected. -/
private theorem triangleInstance_six_notMem : triangleInstance 6 ∉ MaxWeightMatching := by
  rintro ⟨-, M, ⟨hMsub, hMdisj⟩, hwt⟩
  have hle5 : matchingWeight M ≤ 5 := by
    by_cases h0 : (⟨0, 1, 3⟩ : WeightedEdge) ∈ M
    · have hM : M = {⟨0, 1, 3⟩} := by
        ext e; simp only [Finset.mem_singleton]
        refine ⟨fun he => ?_, fun he => he ▸ h0⟩
        by_contra hne
        have hd := hMdisj e he _ h0 hne
        have hm := hMsub e he
        simp only [triangleInstance, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl
        · exact hne rfl
        · exact hd.2.1 rfl
        · exact hd.1 rfl
      rw [hM]; simp [matchingWeight]; norm_num
    · by_cases h1 : (⟨1, 2, 4⟩ : WeightedEdge) ∈ M
      · have hM : M = {⟨1, 2, 4⟩} := by
          ext e; simp only [Finset.mem_singleton]
          refine ⟨fun he => ?_, fun he => he ▸ h1⟩
          by_contra hne
          have hd := hMdisj e he _ h1 hne
          have hm := hMsub e he
          simp only [triangleInstance, List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with rfl | rfl | rfl
          · exact h0 he
          · exact hne rfl
          · exact hd.2.2.2 rfl
        rw [hM]; simp [matchingWeight]; norm_num
      · have hsub : M ⊆ {⟨0, 2, 5⟩} := by
          intro e he
          have hm := hMsub e he
          simp only [triangleInstance, List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with rfl | rfl | rfl
          · exact absurd he h0
          · exact absurd he h1
          · exact Finset.mem_singleton_self _
        by_cases h2 : (⟨0, 2, 5⟩ : WeightedEdge) ∈ M
        · have hM : M = {⟨0, 2, 5⟩} :=
            Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr h2)
          rw [hM]; simp [matchingWeight]
        · have hM : M = ∅ := by
            ext e; simp only [Finset.notMem_empty, iff_false]
            intro he; have := Finset.mem_singleton.mp (hsub he); exact h2 (this ▸ he)
          rw [hM]; simp [matchingWeight]
  simp only [triangleInstance] at hwt
  linarith

/-- Executable check for `MaxWeightMatchingInstance.IsWellFormed`. -/
private def mwmWellFormedBool (x : MaxWeightMatchingInstance) : Bool :=
  (x.edges.all fun e =>
    decide (e.u < x.numVertices) && decide (e.v < x.numVertices) &&
      decide (e.u ≠ e.v) && decide (0 ≤ e.weight)) &&
    decide (x.edges.map WeightedEdge.pairKey).Nodup

private theorem mwmWellFormedBool_iff (x : MaxWeightMatchingInstance) :
    mwmWellFormedBool x = true ↔ x.IsWellFormed := by
  simp only [mwmWellFormedBool, MaxWeightMatchingInstance.IsWellFormed, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq, and_assoc]

private def mwmCheck (p : MaxWeightMatchingInstance × List WeightedEdge) : Bool :=
  mwmWellFormedBool p.1 &&
    (p.2.all fun e₁ => p.2.all fun e₂ =>
      decide (e₁ = e₂) ||
        (decide (e₁.u ≠ e₂.u) && decide (e₁.u ≠ e₂.v) &&
          decide (e₁.v ≠ e₂.u) && decide (e₁.v ≠ e₂.v))) &&
    decide (p.1.threshold ≤ (p.2.map WeightedEdge.weight).sum)

private theorem computableInPolyTime_mwmWellFormedBool :
    ComputableInPolyTime mwmWellFormedBool encMaxWeightMatching encBool := by
  have hn : ComputableInPolyTime (fun x : MaxWeightMatchingInstance => x.numVertices)
      encMaxWeightMatching encNat :=
    ComputableInPolyTime.unary_to_binary.comp (encMaxWeightMatching_numVertices_polyTime id')
  have hstep : ComputableInPolyTime
      (fun p : ℕ × WeightedEdge =>
        decide (p.2.u < p.1) && decide (p.2.v < p.1) &&
          decide (p.2.u ≠ p.2.v) && decide (0 ≤ p.2.weight))
      (encPair encNat encWeightedEdge) encBool := by fun_prop
  have hall : ComputableInPolyTime
      (fun x : MaxWeightMatchingInstance => x.edges.all fun e =>
        decide (e.u < x.numVertices) && decide (e.v < x.numVertices) &&
          decide (e.u ≠ e.v) && decide (0 ≤ e.weight))
      encMaxWeightMatching encBool :=
    ComputableInPolyTime.allWith hstep hn (encMaxWeightMatching_edges_polyTime id')
  have hkeys : ComputableInPolyTime
      (fun x : MaxWeightMatchingInstance => x.edges.map WeightedEdge.pairKey)
      encMaxWeightMatching (encList (encPair encNat encNat)) := by
    have hk : ComputableInPolyTime WeightedEdge.pairKey encWeightedEdge (encPair encNat encNat) :=
      by
      have hite : ComputableInPolyTime
          (fun e : WeightedEdge =>
            if decide (e.u ≤ e.v) then (e.u, e.v) else (e.v, e.u))
          encWeightedEdge (encPair encNat encNat) := by fun_prop
      exact hite.of_enc_eq fun e => by
        congr 1; unfold WeightedEdge.pairKey; split_ifs with h
        · rw [decide_eq_true_eq] at h; rw [min_eq_left h, max_eq_right h]
        · rw [decide_eq_true_eq] at h
          rw [min_eq_right (le_of_not_ge h), max_eq_left (le_of_not_ge h)]
    exact (ComputableInPolyTime.map hk).comp (encMaxWeightMatching_edges_polyTime id')
  have hnd : ComputableInPolyTime
      (fun x : MaxWeightMatchingInstance => decide (x.edges.map WeightedEdge.pairKey).Nodup)
      encMaxWeightMatching encBool :=
    ComputableInPolyTime.decide_nodup hkeys
  unfold mwmWellFormedBool
  fun_prop

private theorem computableInPolyTime_mwmCheck :
    ComputableInPolyTime mwmCheck (encPair encMaxWeightMatching (encList encWeightedEdge)) encBool
      := by
  have hw := computableInPolyTime_mwmWellFormedBool.comp
    (ComputableInPolyTime.fst encMaxWeightMatching (encList encWeightedEdge))
  have hdisj : ComputableInPolyTime
      (fun p : MaxWeightMatchingInstance × List WeightedEdge =>
        p.2.all fun e₁ => p.2.all fun e₂ =>
          decide (e₁ = e₂) ||
            (decide (e₁.u ≠ e₂.u) && decide (e₁.u ≠ e₂.v) &&
              decide (e₁.v ≠ e₂.u) && decide (e₁.v ≠ e₂.v)))
      (encPair encMaxWeightMatching (encList encWeightedEdge)) encBool := by
    have hinner : ComputableInPolyTime
        (fun q : List WeightedEdge × WeightedEdge =>
          q.1.all fun e₂ =>
            decide (q.2 = e₂) ||
              (decide (q.2.u ≠ e₂.u) && decide (q.2.u ≠ e₂.v) &&
                decide (q.2.v ≠ e₂.u) && decide (q.2.v ≠ e₂.v)))
        (encPair (encList encWeightedEdge) encWeightedEdge) encBool := by
      have hpred : ComputableInPolyTime
          (fun r : WeightedEdge × WeightedEdge =>
            decide (r.1 = r.2) ||
              (decide (r.1.u ≠ r.2.u) && decide (r.1.u ≠ r.2.v) &&
                decide (r.1.v ≠ r.2.u) && decide (r.1.v ≠ r.2.v)))
          (encPair encWeightedEdge encWeightedEdge) encBool := by fun_prop
      exact ComputableInPolyTime.allWith hpred
        (ComputableInPolyTime.snd _ _) (ComputableInPolyTime.fst _ _)
    exact ComputableInPolyTime.allWith hinner
      (ComputableInPolyTime.snd _ _) (ComputableInPolyTime.snd _ _)
  have hsum : ComputableInPolyTime
      (fun p : MaxWeightMatchingInstance × List WeightedEdge =>
        (p.2.map WeightedEdge.weight).sum)
      (encPair encMaxWeightMatching (encList encWeightedEdge)) encRat := by
    have hmap : ComputableInPolyTime
        (fun l : List WeightedEdge => l.map WeightedEdge.weight)
        (encList encWeightedEdge) (encList encRat) :=
      ComputableInPolyTime.map (encWeightedEdge_weight_polyTime id')
    exact computableInPolyTime_ratSum.comp (hmap.comp (ComputableInPolyTime.snd _ _))
  have hle : ComputableInPolyTime
      (fun p : MaxWeightMatchingInstance × List WeightedEdge =>
        decide (p.1.threshold ≤ (p.2.map WeightedEdge.weight).sum))
      (encPair encMaxWeightMatching (encList encWeightedEdge)) encBool :=
    ComputableInPolyTime.rat_le'
      (encMaxWeightMatching_threshold_polyTime (ComputableInPolyTime.fst _ _)) hsum
  unfold mwmCheck
  fun_prop

/-- **Maximum Weight Matching is in NP**. -/
theorem MaxWeightMatching_mem_NP : MaxWeightMatching ∈ NP encMaxWeightMatching := by
  convert mem_NP_of_subsetWitness (enc := encMaxWeightMatching) (encγ := encWeightedEdge)
    (vs := fun x => x.edges) (check := mwmCheck)
    (P := fun x M => x.IsWellFormed ∧
      (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → e₁.Disjoint e₂) ∧
      x.threshold ≤ matchingWeight M)
    (encMaxWeightMatching_edges_polyTime id') computableInPolyTime_mwmCheck
    (fun x l hl _ => ?_) using 1
  · ext x
    simp only [MaxWeightMatching, MaxWeightMatchingInstance.IsMatching, Set.mem_ofPred_eq]
    tauto
  · simp only [mwmCheck, Bool.and_eq_true, mwmWellFormedBool_iff, List.all_eq_true,
      Bool.or_eq_true, decide_eq_true_eq, WeightedEdge.Disjoint, matchingWeight]
    have hsum : (l.map WeightedEdge.weight).sum = ∑ e ∈ l.toFinset, e.weight := by
      rw [← List.sum_toFinset _ hl]
    rw [hsum]
    constructor
    · rintro ⟨⟨hw, hdisj⟩, hwt⟩
      refine ⟨hw, fun e₁ h₁ e₂ h₂ hne => ?_, hwt⟩
      rcases hdisj e₁ (List.mem_toFinset.mp h₁) e₂ (List.mem_toFinset.mp h₂) with heq | hd
      · exact absurd heq hne
      · exact ⟨hd.1.1.1, hd.1.1.2, hd.1.2, hd.2⟩
    · rintro ⟨hw, hdisj, hwt⟩
      refine ⟨⟨hw, fun e₁ h₁ e₂ h₂ => ?_⟩, hwt⟩
      by_cases heq : e₁ = e₂
      · exact Or.inl heq
      · have hd := hdisj e₁ (List.mem_toFinset.mpr h₁) e₂ (List.mem_toFinset.mpr h₂) heq
        exact Or.inr ⟨⟨⟨hd.1, hd.2.1⟩, hd.2.2.1⟩, hd.2.2.2⟩

/-! ### Capacitated simple b-matching and Tutte's reduction -/

/-- An instance of **Maximum Weight Simple b-Matching**: vertices `0, …, numVertices - 1`,
capacities `cap[v]` (for `v < numVertices`), simple weighted edges, and a weight threshold. -/
@[ext]
structure SimpleBMatchingInstance where
  /-- Number of vertices (encoded in unary). -/
  numVertices : ℕ
  /-- Vertex degree capacities `cap[v]` for `v < numVertices`. -/
  cap : List ℕ
  /-- List of weighted undirected edges. -/
  edges : List WeightedEdge
  /-- Target total matching weight. -/
  threshold : ℚ
  deriving DecidableEq, Repr

/-- List encoding of unary natural numbers for `enc_structure`. -/
abbrev encUnaryList : List ℕ ↪ List Bool := encList encUnary

/-- Encoding of `SimpleBMatchingInstance`. -/
enc_structure encSimpleBMatching : SimpleBMatchingInstance where
  numVertices : encUnary, cap : encUnaryList,
  edges : encWeightedEdgeList, threshold : encRat

attribute [fun_prop] encSimpleBMatching_numVertices_polyTime encSimpleBMatching_cap_polyTime
  encSimpleBMatching_edges_polyTime encSimpleBMatching_threshold_polyTime
  encSimpleBMatching_mk_polyTime

/-- A `SimpleBMatchingInstance` is well-formed when the underlying weighted graph is well-formed
and `cap` has length `numVertices` with every capacity at most `numVertices`. -/
@[expose]
def SimpleBMatchingInstance.IsWellFormed (x : SimpleBMatchingInstance) : Prop :=
  (⟨x.numVertices, x.edges, x.threshold⟩ : MaxWeightMatchingInstance).IsWellFormed ∧
    x.cap.length = x.numVertices ∧
    ∀ v < x.numVertices, x.cap.getD v 0 ≤ x.numVertices

/-- `M` is a simple `b`-matching in `x` if `M ⊆ x.edges` and every vertex `v < x.numVertices` is
incident to at most `cap[v]` edges of `M`. -/
@[expose]
def SimpleBMatchingInstance.IsSimpleBMatching (x : SimpleBMatchingInstance)
    (M : Finset WeightedEdge) : Prop :=
  (∀ e ∈ M, e ∈ x.edges) ∧
    ∀ v < x.numVertices, (M.filter fun e => e.u = v ∨ e.v = v).card ≤ x.cap.getD v 0

/-- The **Maximum Weight Simple b-Matching** decision problem. -/
@[expose]
def MaxWeightSimpleBMatching : Set SimpleBMatchingInstance :=
  {x | x.IsWellFormed ∧
    ∃ M : Finset WeightedEdge, x.IsSimpleBMatching M ∧ x.threshold ≤ matchingWeight M}

/-- Executable well-formedness check for `SimpleBMatchingInstance`. -/
private def sbWellFormedBool (x : SimpleBMatchingInstance) : Bool :=
  mwmWellFormedBool ⟨x.numVertices, x.edges, x.threshold⟩ &&
    (x.cap.length == x.numVertices) &&
    x.cap.all (fun c => decide (c ≤ x.numVertices))

private theorem sbWellFormedBool_iff (x : SimpleBMatchingInstance) :
    sbWellFormedBool x = true ↔ x.IsWellFormed := by
  simp only [sbWellFormedBool, SimpleBMatchingInstance.IsWellFormed, Bool.and_eq_true,
    mwmWellFormedBool_iff, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hm, hlen⟩, hall⟩
    refine ⟨hm, hlen, fun v hv => hall _ (by simp [List.getD_eq_getElem?_getD, hlen, hv])⟩
  · rintro ⟨hm, hlen, hall⟩
    refine ⟨⟨hm, hlen⟩, fun c hc => ?_⟩
    obtain ⟨v, hv, rfl⟩ := List.mem_iff_getElem.mp hc
    have hget : x.cap.getD v 0 = x.cap[v] := by simp [List.getD_eq_getElem?_getD, hv]
    rw [← hget]
    exact hall v (hlen ▸ hv)

/-- Fixed well-formed NO-instance of `MaxWeightMatching` (threshold `1` on empty graph). -/
private def mwmNoInstance : MaxWeightMatchingInstance := ⟨0, [], 1⟩

private theorem mwmNoInstance_notMem : mwmNoInstance ∉ MaxWeightMatching := by
  rintro ⟨-, M, ⟨hM, _⟩, hwt⟩
  have hE : M = ∅ := by
    ext e; simp only [Finset.notMem_empty, iff_false]
    intro he; simpa [mwmNoInstance] using hM e he
  rw [hE] at hwt; simp [matchingWeight, mwmNoInstance] at hwt; norm_num at hwt

/-- Tutte's gadget reducing a `SimpleBMatchingInstance` to a `MaxWeightMatchingInstance`:
each original vertex `v` gets `cap[v] ≤ n` port copies `v * n + i`, and each edge `e_idx`
gets two gadget vertices `a_e = n * n + 2 * idx`, `b_e = n * n + 2 * idx + 1` connected by
an edge of weight `e.weight` plus edges of weight `e.weight` from `a_e` to all copies of `e.u`
and from `b_e` to all copies of `e.v`. -/
def tutteReduce (x : SimpleBMatchingInstance) : MaxWeightMatchingInstance :=
  if sbWellFormedBool x then
    let n := x.numVertices
    let base := n * n
    let gadgetEdges := (List.range x.edges.length).flatMap fun idx =>
      let e := x.edges.getD idx ⟨0, 0, 0⟩
      let ae := base + 2 * idx
      let be := base + 2 * idx + 1
      let cu := x.cap.getD e.u 0
      let cv := x.cap.getD e.v 0
      ⟨ae, be, e.weight⟩ ::
        (((List.range cu).map fun i => ⟨e.u * n + i, ae, e.weight⟩) ++
         ((List.range cv).map fun j => ⟨e.v * n + j, be, e.weight⟩))
    let totalW := (x.edges.map WeightedEdge.weight).sum
    ⟨base + 2 * x.edges.length, gadgetEdges, totalW + x.threshold⟩
  else
    mwmNoInstance

theorem tutteReduce_mem_iff (x : SimpleBMatchingInstance) :
    tutteReduce x ∈ MaxWeightMatching ↔ x ∈ MaxWeightSimpleBMatching := by
  classical
  by_cases hwfB : sbWellFormedBool x = true
  · have hwf : x.IsWellFormed := (sbWellFormedBool_iff x).mp hwfB
    set n := x.numVertices
    set base := n * n
    have hred : tutteReduce x =
        ⟨base + 2 * x.edges.length,
          (List.range x.edges.length).flatMap fun idx =>
            let e := x.edges.getD idx ⟨0, 0, 0⟩
            let ae := base + 2 * idx
            let be := base + 2 * idx + 1
            ⟨ae, be, e.weight⟩ ::
              (((List.range (x.cap.getD e.u 0)).map fun i => ⟨e.u * n + i, ae, e.weight⟩) ++
               ((List.range (x.cap.getD e.v 0)).map fun j => ⟨e.v * n + j, be, e.weight⟩)),
          (x.edges.map WeightedEdge.weight).sum + x.threshold⟩ := by
      simp [tutteReduce, hwfB, n, base]
    have hE_nodup : x.edges.Nodup := by
      have hkeys := hwf.1.2
      exact List.Nodup.of_map _ hkeys
    have htotal : (x.edges.map WeightedEdge.weight).sum =
        ∑ idx ∈ Finset.range x.edges.length, (x.edges.getD idx ⟨0, 0, 0⟩).weight := by
      have hmap_getD : (List.range x.edges.length).map (fun idx => x.edges.getD idx ⟨0, 0, 0⟩) =
          x.edges :=
        List.ext_getElem (by simp) fun i hi _ => by
          have hi' : i < x.edges.length := by simpa using hi
          simp [List.getElem?_eq_getElem hi']
      have hsum_range : ∀ (m : ℕ) (f : ℕ → ℚ),
          ((List.range m).map f).sum = ∑ idx ∈ Finset.range m, f idx := by
        intro m f; induction m with
        | zero => simp
        | succ m ih =>
          rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]; simp
      conv_lhs => rw [← hmap_getD, List.map_map]
      exact hsum_range _ _
    -- Prove well-formedness of tutteReduce x
    have hred_wf : (tutteReduce x).IsWellFormed := by
      rw [hred]
      refine ⟨?_, ?_⟩
      · intro ge hge
        obtain ⟨idx, hidx, hge_idx⟩ := List.mem_flatMap.mp hge
        rw [List.mem_range] at hidx
        set e := x.edges.getD idx ⟨0, 0, 0⟩
        have he_mem : e ∈ x.edges := by simp [e, List.getD_eq_getElem?_getD, hidx]
        have he_wf := hwf.1.1 e he_mem
        dsimp only at he_wf
        have hcu : x.cap.getD e.u 0 ≤ n := hwf.2.2 e.u he_wf.1
        have hcv : x.cap.getD e.v 0 ≤ n := hwf.2.2 e.v he_wf.2.1
        simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hge_idx
        rcases hge_idx with rfl | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
        · dsimp only; exact ⟨by omega, by omega, by omega, he_wf.2.2.2⟩
        · have : e.u * n + i < base := by
            have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt he_wf.1)
            dsimp only [base]; nlinarith
          dsimp only; exact ⟨by omega, by omega, by omega, he_wf.2.2.2⟩
        · have : e.v * n + j < base := by
            have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt he_wf.2.1)
            dsimp only [base]; nlinarith
          dsimp only; exact ⟨by omega, by omega, by omega, he_wf.2.2.2⟩
      · -- Nodup of pairKeys
        rw [List.map_flatMap, List.nodup_flatMap]
        refine ⟨fun idx hidx => ?_, ?_⟩
        · rw [List.mem_range] at hidx
          set e := x.edges.getD idx ⟨0, 0, 0⟩
          have he_mem : e ∈ x.edges := by simp [e, List.getD_eq_getElem?_getD, hidx]
          have he_wf := hwf.1.1 e he_mem
          dsimp only at he_wf
          have hcu : x.cap.getD e.u 0 ≤ n := hwf.2.2 e.u he_wf.1
          have hcv : x.cap.getD e.v 0 ≤ n := hwf.2.2 e.v he_wf.2.1
          have hlt_u : ∀ i < x.cap.getD e.u 0, e.u * n + i < base := fun i hi => by
            have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt he_wf.1)
            dsimp only [base]; nlinarith
          have hlt_v : ∀ j < x.cap.getD e.v 0, e.v * n + j < base := fun j hj => by
            have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt he_wf.2.1)
            dsimp only [base]; nlinarith
          simp only [List.map_cons, List.map_append, List.map_map, List.nodup_cons,
            List.mem_append, List.mem_map, List.mem_range, not_or, not_exists, not_and]
          refine ⟨⟨fun i hi h => ?_, fun j hj h => ?_⟩, ?_⟩
          · have h1 := hlt_u i hi
            simp only [Function.comp_apply, WeightedEdge.pairKey, Prod.mk.injEq] at h
            omega
          · have h1 := hlt_v j hj
            simp only [Function.comp_apply, WeightedEdge.pairKey, Prod.mk.injEq] at h
            omega
          · rw [List.nodup_append]
            refine ⟨?_, ?_, ?_⟩
            · refine (List.nodup_range).map_on fun i hi j hj h => ?_
              rw [List.mem_range] at hi hj
              have h1 := hlt_u i hi; have h2 := hlt_u j hj
              simp only [Function.comp_apply, WeightedEdge.pairKey, Prod.mk.injEq] at h
              omega
            · refine (List.nodup_range).map_on fun i hi j hj h => ?_
              rw [List.mem_range] at hi hj
              have h1 := hlt_v i hi; have h2 := hlt_v j hj
              simp only [Function.comp_apply, WeightedEdge.pairKey, Prod.mk.injEq] at h
              omega
            · intro p hp q hq heq; subst heq
              obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
              obtain ⟨j, hj, h2⟩ := List.mem_map.mp hq
              rw [List.mem_range] at hi hj
              have h1 := hlt_u i hi; have h3 := hlt_v j hj
              simp only [Function.comp_apply, WeightedEdge.pairKey, Prod.mk.injEq] at h2
              omega
        · rw [List.pairwise_iff_getElem]
          intro i j hi hj hij
          simp only [List.getElem_range]
          intro p hp1 hp2
          obtain ⟨ge1, hge1, rfl⟩ := List.mem_map.mp hp1
          obtain ⟨ge2, hge2, hpk⟩ := List.mem_map.mp hp2
          have hhi : i < x.edges.length := by simpa using hi
          have hhj : j < x.edges.length := by simpa using hj
          set e1 := x.edges.getD i ⟨0, 0, 0⟩
          set e2 := x.edges.getD j ⟨0, 0, 0⟩
          have he1_wf := hwf.1.1 e1 (by simp [e1, List.getD_eq_getElem?_getD, hhi])
          have he2_wf := hwf.1.1 e2 (by simp [e2, List.getD_eq_getElem?_getD, hhj])
          dsimp only at he1_wf he2_wf
          have hcu1 := hwf.2.2 e1.u he1_wf.1; have hcv1 := hwf.2.2 e1.v he1_wf.2.1
          have hcu2 := hwf.2.2 e2.u he2_wf.1; have hcv2 := hwf.2.2 e2.v he2_wf.2.1
          have hmax1 : max ge1.u ge1.v = base + 2 * i ∨ max ge1.u ge1.v = base + 2 * i + 1 := by
            simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hge1
            rcases hge1 with rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
            · right; dsimp only; omega
            · left; have : e1.u * n + a < base := by
                have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt he1_wf.1)
                dsimp only [base]; nlinarith
              dsimp only; omega
            · right; have : e1.v * n + a < base := by
                have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt he1_wf.2.1)
                dsimp only [base]; nlinarith
              dsimp only; omega
          have hmax2 : max ge2.u ge2.v = base + 2 * j ∨ max ge2.u ge2.v = base + 2 * j + 1 := by
            simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hge2
            rcases hge2 with rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
            · right; dsimp only; omega
            · left; have : e2.u * n + a < base := by
                have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt he2_wf.1)
                dsimp only [base]; nlinarith
              dsimp only; omega
            · right; have : e2.v * n + a < base := by
                have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt he2_wf.2.1)
                dsimp only [base]; nlinarith
              dsimp only; omega
          have hmax_eq : max ge2.u ge2.v = max ge1.u ge1.v := congrArg Prod.snd hpk
          omega
    constructor
    · -- Backward: matching in Tutte gadget → simple b-matching in x
      rintro ⟨_, M, ⟨hMsub, hMdisj⟩, hwt⟩
      rw [hred] at hMsub hwt
      -- Classify edges of M by their gadget index idx < x.edges.length
      let Midx (idx : ℕ) : Finset WeightedEdge :=
        M.filter fun ge => decide (max ge.u ge.v = base + 2 * idx ∨
          max ge.u ge.v = base + 2 * idx + 1)
      -- For each idx, either Midx idx has 2 edges (both u-copy and v-copy matched to ae and be)
      -- giving weight 2 * e.weight, or total weight in Midx idx is at most e.weight!
      let selIdx : Finset ℕ :=
        (Finset.range x.edges.length).filter fun idx => (Midx idx).card = 2
      let M0 : Finset WeightedEdge := selIdx.image fun idx => x.edges.getD idx ⟨0, 0, 0⟩
      have hge_info : ∀ ge ∈ M, ∃ idx < x.edges.length,
          (ge = ⟨base + 2 * idx, base + 2 * idx + 1, (x.edges.getD idx ⟨0, 0, 0⟩).weight⟩ ∨
           (∃ i < x.cap.getD (x.edges.getD idx ⟨0, 0, 0⟩).u 0,
              ge = ⟨(x.edges.getD idx ⟨0, 0, 0⟩).u * n + i, base + 2 * idx,
                    (x.edges.getD idx ⟨0, 0, 0⟩).weight⟩) ∨
           (∃ j < x.cap.getD (x.edges.getD idx ⟨0, 0, 0⟩).v 0,
              ge = ⟨(x.edges.getD idx ⟨0, 0, 0⟩).v * n + j, base + 2 * idx + 1,
                    (x.edges.getD idx ⟨0, 0, 0⟩).weight⟩)) := by
        intro ge hge
        obtain ⟨idx, hidx, hge_idx⟩ := List.mem_flatMap.mp (hMsub ge hge)
        rw [List.mem_range] at hidx
        simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hge_idx
        refine ⟨idx, hidx, ?_⟩
        rcases hge_idx with rfl | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨i, hi, rfl⟩)
        · exact Or.inr (Or.inr ⟨j, hj, rfl⟩)
      have hmax_of_idx : ∀ {idx : ℕ} {ge : WeightedEdge}, idx < x.edges.length →
          (ge = ⟨base + 2 * idx, base + 2 * idx + 1, (x.edges.getD idx ⟨0, 0, 0⟩).weight⟩ ∨
           (∃ i < x.cap.getD (x.edges.getD idx ⟨0, 0, 0⟩).u 0,
              ge = ⟨(x.edges.getD idx ⟨0, 0, 0⟩).u * n + i, base + 2 * idx,
                    (x.edges.getD idx ⟨0, 0, 0⟩).weight⟩) ∨
           (∃ j < x.cap.getD (x.edges.getD idx ⟨0, 0, 0⟩).v 0,
              ge = ⟨(x.edges.getD idx ⟨0, 0, 0⟩).v * n + j, base + 2 * idx + 1,
                    (x.edges.getD idx ⟨0, 0, 0⟩).weight⟩)) →
          (max ge.u ge.v = base + 2 * idx ∨ max ge.u ge.v = base + 2 * idx + 1) ∧
            ge.weight = (x.edges.getD idx ⟨0, 0, 0⟩).weight := by
        intro idx ge hidx h
        set e := x.edges.getD idx ⟨0, 0, 0⟩
        have he_wf := hwf.1.1 e (by simp [e, List.getD_eq_getElem?_getD, hidx])
        dsimp only at he_wf
        have hcu := hwf.2.2 e.u he_wf.1; have hcv := hwf.2.2 e.v he_wf.2.1
        rcases h with rfl | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
        · exact ⟨Or.inr (by dsimp only; omega), rfl⟩
        · have : e.u * n + i < base := by
            have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt he_wf.1)
            dsimp only [base]; nlinarith
          exact ⟨Or.inl (by dsimp only; omega), rfl⟩
        · have : e.v * n + j < base := by
            have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt he_wf.2.1)
            dsimp only [base]; nlinarith
          exact ⟨Or.inr (by dsimp only; omega), rfl⟩
      have hM_part : M = (Finset.range x.edges.length).biUnion Midx := by
        ext ge
        simp only [Finset.mem_biUnion, Finset.mem_range, Midx, Finset.mem_filter,
          decide_eq_true_eq]
        constructor
        · intro hge
          obtain ⟨idx, hidx, hinfo⟩ := hge_info ge hge
          exact ⟨idx, hidx, hge, (hmax_of_idx hidx hinfo).1⟩
        · rintro ⟨_, _, hge, _⟩; exact hge
      have hM_disj_idx : Set.PairwiseDisjoint (↑(Finset.range x.edges.length)) Midx := by
        intro i _ j _ hij
        change Disjoint (Midx i) (Midx j)
        rw [Finset.disjoint_left]
        intro ge h1 h2
        simp only [Midx, Finset.mem_filter, decide_eq_true_eq] at h1 h2
        omega
      have hMidx_card_le2 : ∀ idx < x.edges.length, (Midx idx).card ≤ 2 ∧
          ∑ ge ∈ Midx idx, ge.weight = ((Midx idx).card : ℚ) * (x.edges.getD idx ⟨0, 0,
            0⟩).weight := by
        intro idx hidx
        set e := x.edges.getD idx ⟨0, 0, 0⟩
        have he_wf := hwf.1.1 e (by simp [e, List.getD_eq_getElem?_getD, hidx])
        have hcu := hwf.2.2 e.u he_wf.1; have hcv := hwf.2.2 e.v he_wf.2.1
        have hwt_each : ∀ ge ∈ Midx idx, ge.weight = e.weight := by
          intro ge hge
          have hgeM : ge ∈ M := (Finset.mem_filter.mp hge).1
          have hmax := decide_eq_true_eq.mp (Finset.mem_filter.mp hge).2
          obtain ⟨idx', hidx', hinfo⟩ := hge_info ge hgeM
          have hmax' := (hmax_of_idx hidx' hinfo).1
          have heq : idx' = idx := by omega
          subst heq
          exact (hmax_of_idx hidx' hinfo).2
        have hsum_eq : ∑ ge ∈ Midx idx, ge.weight = ((Midx idx).card : ℚ) * e.weight := by
          rw [Finset.sum_congr rfl hwt_each, Finset.sum_const, nsmul_eq_mul]
        -- Each edge in Midx idx touches ae or be; since M is a matching, at most 2 edges!
        have htouch : ∀ ge ∈ Midx idx,
            ge.v = base + 2 * idx ∨ ge.v = base + 2 * idx + 1 := by
          intro ge hge
          have hgeM : ge ∈ M := (Finset.mem_filter.mp hge).1
          have hmax := decide_eq_true_eq.mp (Finset.mem_filter.mp hge).2
          obtain ⟨idx', hidx', hinfo⟩ := hge_info ge hgeM
          have hmax' := (hmax_of_idx hidx' hinfo).1
          have heq : idx' = idx := by omega
          subst heq
          rcases hinfo with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
          · exact Or.inr rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hcard : (Midx idx).card ≤ 2 := by
          let f : WeightedEdge → Fin 2 := fun ge => if ge.v = base + 2 * idx then 0 else 1
          have hinj : Set.InjOn f ↑(Midx idx) := by
            intro g1 hg1 g2 hg2 hfeq
            by_contra hne
            have hd := hMdisj g1 (Finset.mem_filter.mp hg1).1 g2 (Finset.mem_filter.mp hg2).1 hne
            rcases htouch g1 hg1 with h1 | h1 <;> rcases htouch g2 hg2 with h2 | h2
            · exact hd.2.2.2 (h1.trans h2.symm)
            · simp only [f, h1, h2, ↓reduceIte, show base + 2 * idx + 1 ≠ base + 2 * idx by omega]
                at hfeq
              exact absurd hfeq (by decide)
            · simp only [f, h1, h2, ↓reduceIte, show base + 2 * idx + 1 ≠ base + 2 * idx by omega]
                at hfeq
              exact absurd hfeq (by decide)
            · exact hd.2.2.2 (h1.trans h2.symm)
          calc
            (Midx idx).card = ((Midx idx).image f).card := (Finset.card_image_of_injOn hinj).symm
            _ ≤ (Finset.univ : Finset (Fin 2)).card := Finset.card_le_card (Finset.subset_univ _)
            _ = 2 := by simp
        exact ⟨hcard, hsum_eq⟩
      have hcard2_endpoints : ∀ idx ∈ selIdx,
          (∃ i < x.cap.getD (x.edges.getD idx ⟨0, 0, 0⟩).u 0,
            ⟨(x.edges.getD idx ⟨0, 0, 0⟩).u * n + i, base + 2 * idx,
              (x.edges.getD idx ⟨0, 0, 0⟩).weight⟩ ∈ M) ∧
          (∃ j < x.cap.getD (x.edges.getD idx ⟨0, 0, 0⟩).v 0,
            ⟨(x.edges.getD idx ⟨0, 0, 0⟩).v * n + j, base + 2 * idx + 1,
              (x.edges.getD idx ⟨0, 0, 0⟩).weight⟩ ∈ M) := by
        intro idx hidx_sel
        have hidx : idx < x.edges.length := Finset.mem_range.mp (Finset.mem_filter.mp hidx_sel).1
        have hcard2 : (Midx idx).card = 2 := (Finset.mem_filter.mp hidx_sel).2
        obtain ⟨g1, g2, hne, hpair⟩ := Finset.card_eq_two.mp hcard2
        have hg1 : g1 ∈ Midx idx := hpair ▸ Finset.mem_insert_self g1 {g2}
        have hg2 : g2 ∈ Midx idx := hpair ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self g2)
        have hg1M : g1 ∈ M := (Finset.mem_filter.mp hg1).1
        have hg2M : g2 ∈ M := (Finset.mem_filter.mp hg2).1
        have hd := hMdisj g1 hg1M g2 hg2M hne
        obtain ⟨i1, hi1, hinfo1⟩ := hge_info g1 hg1M
        obtain ⟨i2, hi2, hinfo2⟩ := hge_info g2 hg2M
        have hm1 := (hmax_of_idx hi1 hinfo1).1
        have hm2 := (hmax_of_idx hi2 hinfo2).1
        have hmax1 := decide_eq_true_eq.mp (Finset.mem_filter.mp hg1).2
        have hmax2 := decide_eq_true_eq.mp (Finset.mem_filter.mp hg2).2
        have heq1 : i1 = idx := by omega
        have heq2 : i2 = idx := by omega
        subst heq1; subst heq2
        rcases hinfo1 with rfl | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
        · rcases hinfo2 with rfl | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
          · exact absurd rfl hne
          · exact absurd rfl hd.2.1
          · exact absurd rfl hd.2.2.2
        · rcases hinfo2 with rfl | ⟨i', hi', rfl⟩ | ⟨j, hj, rfl⟩
          · exact absurd rfl hd.2.2.1
          · exact absurd rfl hd.2.2.2
          · exact ⟨⟨i, hi, hg1M⟩, ⟨j, hj, hg2M⟩⟩
        · rcases hinfo2 with rfl | ⟨i, hi, rfl⟩ | ⟨j', hj', rfl⟩
          · exact absurd rfl hd.2.2.2
          · exact ⟨⟨i, hi, hg2M⟩, ⟨j, hj, hg1M⟩⟩
          · exact absurd rfl hd.2.2.2
      refine ⟨hwf, M0, ⟨?_, ?_⟩, ?_⟩
      · intro e he
        obtain ⟨idx, hidx_sel, rfl⟩ := Finset.mem_image.mp he
        have hidx : idx < x.edges.length := Finset.mem_range.mp (Finset.mem_filter.mp hidx_sel).1
        simp [List.getD_eq_getElem?_getD, hidx]
      · -- Capacity bound at each vertex v < n
        intro v hv
        let portOf (e : WeightedEdge) : ℕ :=
          if h : ∃ idx ∈ selIdx, x.edges.getD idx ⟨0, 0, 0⟩ = e ∧
              (∃ i < x.cap.getD v 0,
                (e.u = v ∧ ⟨v * n + i, base + 2 * idx, e.weight⟩ ∈ M) ∨
                (e.v = v ∧ ⟨v * n + i, base + 2 * idx + 1, e.weight⟩ ∈ M)) then
            (h.choose_spec.2.2).choose
          else 0
        have hmaps : ∀ e ∈ M0.filter (fun e => e.u = v ∨ e.v = v),
            portOf e ∈ Finset.range (x.cap.getD v 0) := by
          intro e he
          have heM0 := (Finset.mem_filter.mp he).1
          have hinc := (Finset.mem_filter.mp he).2
          obtain ⟨idx, hidx_sel, rfl⟩ := Finset.mem_image.mp heM0
          have hcond : ∃ idx' ∈ selIdx, x.edges.getD idx' ⟨0, 0, 0⟩ = x.edges.getD idx ⟨0, 0, 0⟩ ∧
              (∃ i < x.cap.getD v 0,
                ((x.edges.getD idx ⟨0, 0, 0⟩).u = v ∧
                  ⟨v * n + i, base + 2 * idx', (x.edges.getD idx ⟨0, 0, 0⟩).weight⟩ ∈ M) ∨
                ((x.edges.getD idx ⟨0, 0, 0⟩).v = v ∧
                  ⟨v * n + i, base + 2 * idx' + 1, (x.edges.getD idx ⟨0, 0, 0⟩).weight⟩ ∈ M)) := by
            obtain ⟨⟨i, hi, hMi⟩, ⟨j, hj, hMj⟩⟩ := hcard2_endpoints idx hidx_sel
            rcases hinc with huv | hvv
            · exact ⟨idx, hidx_sel, rfl, i, huv ▸ hi, Or.inl ⟨huv, huv ▸ hMi⟩⟩
            · exact ⟨idx, hidx_sel, rfl, j, hvv ▸ hj, Or.inr ⟨hvv, hvv ▸ hMj⟩⟩
          simp only [portOf, hcond, ↓reduceDIte, Finset.mem_range]
          exact hcond.choose_spec.2.2.choose_spec.1
        have hinj : Set.InjOn portOf ↑(M0.filter (fun e => e.u = v ∨ e.v = v)) := by
          intro e1 he1 e2 he2 hpeq
          have hcond : ∀ e ∈ M0.filter (fun e => e.u = v ∨ e.v = v),
              ∃ idx ∈ selIdx, x.edges.getD idx ⟨0, 0, 0⟩ = e ∧
                (∃ i < x.cap.getD v 0,
                  (e.u = v ∧ ⟨v * n + i, base + 2 * idx, e.weight⟩ ∈ M) ∨
                  (e.v = v ∧ ⟨v * n + i, base + 2 * idx + 1, e.weight⟩ ∈ M)) := by
            intro e he
            obtain ⟨idx, hidx_sel, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp he).1
            obtain ⟨⟨i, hi, hMi⟩, ⟨j, hj, hMj⟩⟩ := hcard2_endpoints idx hidx_sel
            rcases (Finset.mem_filter.mp he).2 with huv | hvv
            · exact ⟨idx, hidx_sel, rfl, i, huv ▸ hi, Or.inl ⟨huv, huv ▸ hMi⟩⟩
            · exact ⟨idx, hidx_sel, rfl, j, hvv ▸ hj, Or.inr ⟨hvv, hvv ▸ hMj⟩⟩
          have hc1 := hcond e1 he1
          have hc2 := hcond e2 he2
          simp only [portOf, hc1, hc2, ↓reduceDIte] at hpeq
          have hspec1 := hc1.choose_spec
          have hspec2 := hc2.choose_spec
          have hp1 := hspec1.2.2.choose_spec.2
          have hp2 := hspec2.2.2.choose_spec.2
          rw [hpeq] at hp1
          have hidx_eq : hc1.choose = hc2.choose := by
            by_contra hne_idx
            rcases hp1 with ⟨_, hm1⟩ | ⟨_, hm1⟩ <;> rcases hp2 with ⟨_, hm2⟩ | ⟨_, hm2⟩ <;>
              exact (hMdisj _ hm1 _ hm2 (by
                intro h; simp only [WeightedEdge.mk.injEq] at h; omega)).1 rfl
          rw [← hspec1.2.1, ← hspec2.2.1, hidx_eq]
        calc
          (M0.filter (fun e => e.u = v ∨ e.v = v)).card
              = ((M0.filter (fun e => e.u = v ∨ e.v = v)).image portOf).card :=
            (Finset.card_image_of_injOn hinj).symm
          _ ≤ (Finset.range (x.cap.getD v 0)).card := by
            refine Finset.card_le_card ?_
            intro p hp
            obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
            exact hmaps e he
          _ = x.cap.getD v 0 := Finset.card_range _
      · -- Weight bound: matchingWeight M = ∑ idx, weight(Midx idx) ≤ totalW + matchingWeight M0
        have hM_sum : matchingWeight M =
            ∑ idx ∈ Finset.range x.edges.length, ∑ ge ∈ Midx idx, ge.weight := by
          unfold matchingWeight
          rw [hM_part, Finset.sum_biUnion hM_disj_idx]
        have hM0_sum : matchingWeight M0 =
            ∑ idx ∈ selIdx, (x.edges.getD idx ⟨0, 0, 0⟩).weight := by
          unfold matchingWeight M0
          rw [Finset.sum_image]
          intro i hi j hj heq
          have hi' : i < x.edges.length := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
          have hj' : j < x.edges.length := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
          have h1 : x.edges[i] = x.edges[j] := by
            simpa [List.getD_eq_getElem?_getD, hi', hj'] using heq
          exact congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hE_nodup)
            (a₁ := ⟨i, hi'⟩) (a₂ := ⟨j, hj'⟩) h1)
        have hbound_sum :
            ∑ idx ∈ Finset.range x.edges.length, ∑ ge ∈ Midx idx, ge.weight ≤
              (∑ idx ∈ Finset.range x.edges.length, (x.edges.getD idx ⟨0, 0, 0⟩).weight) +
                ∑ idx ∈ selIdx, (x.edges.getD idx ⟨0, 0, 0⟩).weight := by
          rw [← Finset.sum_filter_add_sum_filter_not (Finset.range x.edges.length)
            (fun idx => (Midx idx).card = 2)]
          have hsel_eq : (Finset.range x.edges.length).filter (fun idx => (Midx idx).card = 2) =
              selIdx := rfl
          rw [hsel_eq]
          have h1 : ∑ idx ∈ selIdx, ∑ ge ∈ Midx idx, ge.weight =
              ∑ idx ∈ selIdx, ((x.edges.getD idx ⟨0, 0, 0⟩).weight +
                (x.edges.getD idx ⟨0, 0, 0⟩).weight) := by
            refine Finset.sum_congr rfl fun idx hidx => ?_
            have hl := Finset.mem_range.mp (Finset.mem_filter.mp hidx).1
            have hc := (Finset.mem_filter.mp hidx).2
            rw [(hMidx_card_le2 idx hl).2, hc]; ring
          rw [h1, Finset.sum_add_distrib]
          have h2 : ∑ idx ∈ (Finset.range x.edges.length).filter (fun idx => ¬(Midx idx).card = 2),
                ∑ ge ∈ Midx idx, ge.weight ≤
              ∑ idx ∈ (Finset.range x.edges.length).filter (fun idx => ¬(Midx idx).card = 2),
                (x.edges.getD idx ⟨0, 0, 0⟩).weight := by
            refine Finset.sum_le_sum fun idx hidx => ?_
            have hl := Finset.mem_range.mp (Finset.mem_filter.mp hidx).1
            have hne2 := (Finset.mem_filter.mp hidx).2
            have hle2 := (hMidx_card_le2 idx hl).1
            have hle1 : (Midx idx).card ≤ 1 := by omega
            rw [(hMidx_card_le2 idx hl).2]
            have hw0 : 0 ≤ (x.edges.getD idx ⟨0, 0, 0⟩).weight :=
              (hwf.1.1 _ (by simp [List.getD_eq_getElem?_getD, hl])).2.2.2
            have : ((Midx idx).card : ℚ) ≤ 1 := by exact_mod_cast hle1
            nlinarith
          have hsplit_tot : ∑ idx ∈ Finset.range x.edges.length,
                (x.edges.getD idx ⟨0, 0, 0⟩).weight =
              ∑ idx ∈ selIdx, (x.edges.getD idx ⟨0, 0, 0⟩).weight +
              ∑ idx ∈ (Finset.range x.edges.length).filter (fun idx => ¬(Midx idx).card = 2),
                (x.edges.getD idx ⟨0, 0, 0⟩).weight := by
            rw [← Finset.sum_filter_add_sum_filter_not (Finset.range x.edges.length)
              (fun idx => (Midx idx).card = 2)]
          linarith
        rw [hM_sum, htotal] at hwt
        linarith
    · -- Forward: simple b-matching M0 in x → matching M in Tutte gadget
      rintro ⟨_, M0, ⟨hM0sub, hM0cap⟩, hM0wt⟩
      -- Assign each e ∈ M0 to a distinct port index at e.u and at e.v!
      let rankAt (v : ℕ) (e : WeightedEdge) : ℕ :=
        ((x.edges.filter fun e' => decide (e' ∈ M0 ∧ (e'.u = v ∨ e'.v = v))).idxOf e)
      have hrank_lt : ∀ v < n, ∀ e ∈ M0, e.u = v ∨ e.v = v → rankAt v e < x.cap.getD v 0 := by
        intro v hv e he hinc
        have hmem_f : e ∈ x.edges.filter fun e' => decide (e' ∈ M0 ∧ (e'.u = v ∨ e'.v = v)) :=
          List.mem_filter.mpr ⟨hM0sub e he, decide_eq_true ⟨he, hinc⟩⟩
        have hlt_len : rankAt v e <
            (x.edges.filter fun e' => decide (e' ∈ M0 ∧ (e'.u = v ∨ e'.v = v))).length :=
          List.idxOf_lt_length_of_mem hmem_f
        have hlen_eq : (x.edges.filter fun e' => decide (e' ∈ M0 ∧ (e'.u = v ∨ e'.v = v))).length =
            (M0.filter fun e' => e'.u = v ∨ e'.v = v).card := by
          rw [← List.toFinset_card_of_nodup (hE_nodup.filter _)]
          congr 1; ext e'
          simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_filter]
          exact ⟨fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨hM0sub e' h1, h1, h2⟩⟩
        rw [hlen_eq] at hlt_len
        exact lt_of_lt_of_le hlt_len (hM0cap v hv)
      have hrank_inj : ∀ v, ∀ e1 ∈ M0, ∀ e2 ∈ M0, (e1.u = v ∨ e1.v = v) → (e2.u = v ∨ e2.v = v) →
          rankAt v e1 = rankAt v e2 → e1 = e2 := by
        intro v e1 he1 e2 he2 hi1 hi2 heq
        have hm1 : e1 ∈ x.edges.filter fun e' => decide (e' ∈ M0 ∧ (e'.u = v ∨ e'.v = v)) :=
          List.mem_filter.mpr ⟨hM0sub e1 he1, decide_eq_true ⟨he1, hi1⟩⟩
        exact (List.idxOf_inj hm1).mp heq
      let edgeSet (idx : ℕ) : Finset WeightedEdge :=
        let e := x.edges.getD idx ⟨0, 0, 0⟩
        if e ∈ M0 then
          {⟨e.u * n + rankAt e.u e, base + 2 * idx, e.weight⟩,
           ⟨e.v * n + rankAt e.v e, base + 2 * idx + 1, e.weight⟩}
        else
          {⟨base + 2 * idx, base + 2 * idx + 1, e.weight⟩}
      let M := (Finset.range x.edges.length).biUnion edgeSet
      have hM_sub : ∀ ge ∈ M, ge ∈ (tutteReduce x).edges := by
        intro ge hge
        rw [hred]
        obtain ⟨idx, hidx, hge_e⟩ := Finset.mem_biUnion.mp hge
        rw [Finset.mem_range] at hidx
        refine List.mem_flatMap.mpr ⟨idx, List.mem_range.mpr hidx, ?_⟩
        set e := x.edges.getD idx ⟨0, 0, 0⟩ with he_def
        have he_mem : e ∈ x.edges := by simp [e, List.getD_eq_getElem?_getD, hidx]
        have he_wf := hwf.1.1 e he_mem
        dsimp only at he_wf
        dsimp only [edgeSet] at hge_e
        rw [← he_def] at hge_e
        by_cases heM0 : e ∈ M0
        · simp only [heM0, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at hge_e
          rcases hge_e with rfl | rfl
          · exact List.mem_cons_of_mem _ (List.mem_append_left _
              (List.mem_map.mpr ⟨rankAt e.u e,
                List.mem_range.mpr (hrank_lt e.u he_wf.1 e heM0 (Or.inl rfl)), rfl⟩))
          · exact List.mem_cons_of_mem _ (List.mem_append_right _
              (List.mem_map.mpr ⟨rankAt e.v e,
                List.mem_range.mpr (hrank_lt e.v he_wf.2.1 e heM0 (Or.inr rfl)), rfl⟩))
        · simp only [heM0, ↓reduceIte, Finset.mem_singleton] at hge_e
          subst hge_e
          exact List.mem_cons_self ..
      have hM_disj : ∀ g1 ∈ M, ∀ g2 ∈ M, g1 ≠ g2 → g1.Disjoint g2 := by
        intro g1 hg1 g2 hg2 hne
        obtain ⟨i1, hi1, hg1_e⟩ := Finset.mem_biUnion.mp hg1
        obtain ⟨i2, hi2, hg2_e⟩ := Finset.mem_biUnion.mp hg2
        rw [Finset.mem_range] at hi1 hi2
        set e1 := x.edges.getD i1 ⟨0, 0, 0⟩ with he1_def
        set e2 := x.edges.getD i2 ⟨0, 0, 0⟩ with he2_def
        have he1_wf := hwf.1.1 e1 (by simp [e1, List.getD_eq_getElem?_getD, hi1])
        have he2_wf := hwf.1.1 e2 (by simp [e2, List.getD_eq_getElem?_getD, hi2])
        dsimp only at he1_wf he2_wf
        have hlt_port : ∀ v < n, ∀ r < x.cap.getD v 0, v * n + r < base := fun v hv r hr => by
          have hcv := hwf.2.2 v hv; have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hv)
          dsimp only [base]; nlinarith
        have hport_eq : ∀ {v1 v2 r1 r2 : ℕ}, r1 < n → r2 < n →
            v1 * n + r1 = v2 * n + r2 → v1 = v2 ∧ r1 = r2 := by
          intro v1 v2 r1 r2 hr1 hr2 h
          have hq : (v1 * n + r1) / n = (v2 * n + r2) / n := congrArg (· / n) h
          have hm : (v1 * n + r1) % n = (v2 * n + r2) % n := congrArg (· % n) h
          have hn0 : 0 < n := by omega
          rw [Nat.mul_comm v1 n, Nat.mul_comm v2 n, Nat.mul_add_div hn0, Nat.mul_add_div hn0,
            Nat.div_eq_of_lt hr1, Nat.div_eq_of_lt hr2] at hq
          rw [Nat.mul_comm v1 n, Nat.mul_comm v2 n, Nat.mul_add_mod, Nat.mul_add_mod,
            Nat.mod_eq_of_lt hr1, Nat.mod_eq_of_lt hr2] at hm
          exact ⟨by omega, hm⟩
        by_cases heq_i : i1 = i2
        · subst heq_i
          dsimp only [edgeSet] at hg1_e hg2_e
          rw [← he1_def] at hg1_e hg2_e
          by_cases heM0 : e1 ∈ M0
          · simp only [heM0, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at hg1_e hg2_e
            have hr1 := hrank_lt e1.u he1_wf.1 e1 heM0 (Or.inl rfl)
            have hr2 := hrank_lt e1.v he1_wf.2.1 e1 heM0 (Or.inr rfl)
            have h1 := hlt_port e1.u he1_wf.1 _ hr1
            have h2 := hlt_port e1.v he1_wf.2.1 _ hr2
            rcases hg1_e with rfl | rfl <;> rcases hg2_e with rfl | rfl
            · exact absurd rfl hne
            · refine ⟨?_, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
              intro h; have := hport_eq (lt_of_lt_of_le hr1 (hwf.2.2 e1.u he1_wf.1))
                (lt_of_lt_of_le hr2 (hwf.2.2 e1.v he1_wf.2.1)) h
              exact he1_wf.2.2.1 this.1
            · refine ⟨?_, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
              intro h; have := hport_eq (lt_of_lt_of_le hr2 (hwf.2.2 e1.v he1_wf.2.1))
                (lt_of_lt_of_le hr1 (hwf.2.2 e1.u he1_wf.1)) h
              exact he1_wf.2.2.1 this.1.symm
            · exact absurd rfl hne
          · simp only [heM0, ↓reduceIte, Finset.mem_singleton] at hg1_e hg2_e
            exact absurd (hg1_e.trans hg2_e.symm) hne
        · -- Distinct edge indices i1 ≠ i2
          have he12_ne : e1 ≠ e2 := fun h => heq_i (congrArg Fin.val
            ((List.nodup_iff_injective_getElem.mp hE_nodup) (a₁ := ⟨i1, hi1⟩) (a₂ := ⟨i2, hi2⟩)
              (by simpa [e1, e2, List.getD_eq_getElem?_getD, hi1, hi2] using h)))
          dsimp only [edgeSet] at hg1_e hg2_e
          rw [← he1_def] at hg1_e; rw [← he2_def] at hg2_e
          by_cases hm1 : e1 ∈ M0 <;> by_cases hm2 : e2 ∈ M0
          · simp only [hm1, hm2, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at hg1_e hg2_e
            have hr1u := hrank_lt e1.u he1_wf.1 e1 hm1 (Or.inl rfl)
            have hr1v := hrank_lt e1.v he1_wf.2.1 e1 hm1 (Or.inr rfl)
            have hr2u := hrank_lt e2.u he2_wf.1 e2 hm2 (Or.inl rfl)
            have hr2v := hrank_lt e2.v he2_wf.2.1 e2 hm2 (Or.inr rfl)
            have hp1u := hlt_port e1.u he1_wf.1 _ hr1u
            have hp1v := hlt_port e1.v he1_wf.2.1 _ hr1v
            have hp2u := hlt_port e2.u he2_wf.1 _ hr2u
            have hp2v := hlt_port e2.v he2_wf.2.1 _ hr2v
            rcases hg1_e with rfl | rfl <;> rcases hg2_e with rfl | rfl
            · refine ⟨?_, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
              intro h; obtain ⟨hv, hr⟩ := hport_eq (lt_of_lt_of_le hr1u (hwf.2.2 _ he1_wf.1))
                (lt_of_lt_of_le hr2u (hwf.2.2 _ he2_wf.1)) h
              exact he12_ne (hrank_inj e1.u e1 hm1 e2 hm2 (Or.inl rfl) (Or.inl hv.symm) (hv ▸ hr))
            · refine ⟨?_, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
              intro h; obtain ⟨hv, hr⟩ := hport_eq (lt_of_lt_of_le hr1u (hwf.2.2 _ he1_wf.1))
                (lt_of_lt_of_le hr2v (hwf.2.2 _ he2_wf.2.1)) h
              exact he12_ne (hrank_inj e1.u e1 hm1 e2 hm2 (Or.inl rfl) (Or.inr hv.symm) (hv ▸ hr))
            · refine ⟨?_, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
              intro h; obtain ⟨hv, hr⟩ := hport_eq (lt_of_lt_of_le hr1v (hwf.2.2 _ he1_wf.2.1))
                (lt_of_lt_of_le hr2u (hwf.2.2 _ he2_wf.1)) h
              exact he12_ne (hrank_inj e1.v e1 hm1 e2 hm2 (Or.inr rfl) (Or.inl hv.symm) (hv ▸ hr))
            · refine ⟨?_, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
              intro h; obtain ⟨hv, hr⟩ := hport_eq (lt_of_lt_of_le hr1v (hwf.2.2 _ he1_wf.2.1))
                (lt_of_lt_of_le hr2v (hwf.2.2 _ he2_wf.2.1)) h
              exact he12_ne (hrank_inj e1.v e1 hm1 e2 hm2 (Or.inr rfl) (Or.inr hv.symm) (hv ▸ hr))
          · simp only [hm1, hm2, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at hg1_e hg2_e
            have hr1u := hrank_lt e1.u he1_wf.1 e1 hm1 (Or.inl rfl)
            have hr1v := hrank_lt e1.v he1_wf.2.1 e1 hm1 (Or.inr rfl)
            have hp1u := hlt_port e1.u he1_wf.1 _ hr1u
            have hp1v := hlt_port e1.v he1_wf.2.1 _ hr1v
            rcases hg1_e with rfl | rfl <;> subst hg2_e <;>
              exact ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
                by dsimp only; omega⟩
          · simp only [hm1, hm2, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at hg1_e hg2_e
            have hr2u := hrank_lt e2.u he2_wf.1 e2 hm2 (Or.inl rfl)
            have hr2v := hrank_lt e2.v he2_wf.2.1 e2 hm2 (Or.inr rfl)
            have hp2u := hlt_port e2.u he2_wf.1 _ hr2u
            have hp2v := hlt_port e2.v he2_wf.2.1 _ hr2v
            rcases hg2_e with rfl | rfl <;> subst hg1_e <;>
              exact ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
                by dsimp only; omega⟩
          · simp only [hm1, hm2, ↓reduceIte, Finset.mem_singleton] at hg1_e hg2_e
            subst hg1_e; subst hg2_e
            exact ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
              by dsimp only; omega⟩
      have hM_wt : matchingWeight M =
          (x.edges.map WeightedEdge.weight).sum + matchingWeight M0 := by
        have hdisj_e : Set.PairwiseDisjoint (↑(Finset.range x.edges.length)) edgeSet := by
          intro i hi j hj hij
          change Disjoint (edgeSet i) (edgeSet j)
          rw [Finset.disjoint_left]
          intro ge h1 h2
          rw [Finset.mem_coe, Finset.mem_range] at hi hj
          dsimp only [edgeSet] at h1 h2
          set e1 := x.edges.getD i ⟨0, 0, 0⟩ with he1_def
          set e2 := x.edges.getD j ⟨0, 0, 0⟩ with he2_def
          by_cases hm1 : e1 ∈ M0 <;> by_cases hm2 : e2 ∈ M0
          · simp only [hm1, hm2, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at h1 h2
            rcases h1 with rfl | rfl <;> rcases h2 with h | h <;> simp at h <;> omega
          · simp only [hm1, hm2, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at h1 h2
            rcases h1 with rfl | rfl <;> simp at h2 <;> omega
          · simp only [hm1, hm2, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at h1 h2
            rcases h2 with rfl | rfl <;> simp at h1 <;> omega
          · simp only [hm1, hm2, ↓reduceIte, Finset.mem_singleton] at h1 h2
            rw [h1] at h2; simp at h2; omega
        unfold matchingWeight at *
        rw [Finset.sum_biUnion hdisj_e, htotal]
        have hper : ∀ idx ∈ Finset.range x.edges.length,
            ∑ ge ∈ edgeSet idx, ge.weight =
              (x.edges.getD idx ⟨0, 0, 0⟩).weight +
                if x.edges.getD idx ⟨0, 0, 0⟩ ∈ M0 then (x.edges.getD idx ⟨0, 0,
                  0⟩).weight else 0 := by
          intro idx hidx
          rw [Finset.mem_range] at hidx
          set e := x.edges.getD idx ⟨0, 0, 0⟩ with he_def
          dsimp only [edgeSet]
          rw [← he_def]
          by_cases hm : e ∈ M0
          · simp only [hm, ↓reduceIte]
            rw [Finset.sum_pair (by intro h; simp only [WeightedEdge.mk.injEq] at h; omega)]
          · simp [hm]
        rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib]
        congr 1
        rw [← Finset.sum_filter]
        have hbij : ((Finset.range x.edges.length).filter
            (fun idx => x.edges.getD idx ⟨0, 0, 0⟩ ∈ M0)).image
            (fun idx => x.edges.getD idx ⟨0, 0, 0⟩) = M0 := by
          ext e
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨_, ⟨_, h⟩, rfl⟩; exact h
          · intro he
            obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp (hM0sub e he)
            exact ⟨idx, ⟨hidx, by simpa [List.getD_eq_getElem?_getD, hidx] using he⟩,
              by simp [List.getD_eq_getElem?_getD, hidx]⟩
        conv_rhs => rw [← hbij, Finset.sum_image (by
          intro i hi j hj heq
          have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
          have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
          exact congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hE_nodup)
            (a₁ := ⟨i, hi'⟩) (a₂ := ⟨j, hj'⟩)
            (by simpa [List.getD_eq_getElem?_getD, hi', hj'] using heq)))]
      refine ⟨hred_wf, M, ⟨hM_sub, hM_disj⟩, ?_⟩
      rw [hred, hM_wt]
      dsimp only
      linarith
  · have hwf : ¬ x.IsWellFormed := by rwa [← sbWellFormedBool_iff]
    simp only [tutteReduce, hwfB]
    exact ⟨fun h => absurd h mwmNoInstance_notMem, fun h => absurd h.1 hwf⟩

attribute [local irreducible] encWeightedEdge encMaxWeightMatching
  encSimpleBMatching encRat encNat encUnary in
theorem computableInPolyTime_tutteReduce :
    ComputableInPolyTime tutteReduce encSimpleBMatching encMaxWeightMatching := by
  have hwf : ComputableInPolyTime sbWellFormedBool encSimpleBMatching encBool := by
    have hm : ComputableInPolyTime
        (fun x : SimpleBMatchingInstance =>
          (⟨x.numVertices, x.edges, x.threshold⟩ : MaxWeightMatchingInstance))
        encSimpleBMatching encMaxWeightMatching := by fun_prop
    have h1 := computableInPolyTime_mwmWellFormedBool.comp hm
    have hlen : ComputableInPolyTime
        (fun x : SimpleBMatchingInstance => x.cap.length == x.numVertices)
        encSimpleBMatching encBool := by
      have hl : ComputableInPolyTime (fun x : SimpleBMatchingInstance => x.cap.length)
          encSimpleBMatching encUnary := by fun_prop
      fun_prop
    have hall : ComputableInPolyTime
        (fun x : SimpleBMatchingInstance => x.cap.all (fun c => decide (c ≤ x.numVertices)))
        encSimpleBMatching encBool := by
      have hle : ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.2 ≤ p.1))
          (encPair encUnary encUnary) encBool := by fun_prop
      exact ComputableInPolyTime.allWith hle
        (encSimpleBMatching_numVertices_polyTime id') (encSimpleBMatching_cap_polyTime id')
    unfold sbWellFormedBool
    fun_prop
  have hmain : ComputableInPolyTime
      (fun x : SimpleBMatchingInstance =>
        let n := x.numVertices
        let base := n * n
        let gadgetEdges := (List.range x.edges.length).flatMap fun idx =>
          let e := x.edges.getD idx ⟨0, 0, 0⟩
          let ae := base + 2 * idx
          let be := base + 2 * idx + 1
          ⟨ae, be, e.weight⟩ ::
            (((List.range (x.cap.getD e.u 0)).map fun i => ⟨e.u * n + i, ae, e.weight⟩) ++
             ((List.range (x.cap.getD e.v 0)).map fun j => ⟨e.v * n + j, be, e.weight⟩))
        let totalW := (x.edges.map WeightedEdge.weight).sum
        (⟨base + 2 * x.edges.length, gadgetEdges, totalW + x.threshold⟩ :
          MaxWeightMatchingInstance))
      encSimpleBMatching encMaxWeightMatching := by
    have hnum : ComputableInPolyTime
        (fun x : SimpleBMatchingInstance => x.numVertices * x.numVertices + 2 * x.edges.length)
        encSimpleBMatching encUnary := by fun_prop
    have htot : ComputableInPolyTime
        (fun x : SimpleBMatchingInstance => (x.edges.map WeightedEdge.weight).sum + x.threshold)
        encSimpleBMatching encRat := by
      have hmap : ComputableInPolyTime
          (fun x : SimpleBMatchingInstance => x.edges.map WeightedEdge.weight)
          encSimpleBMatching (encList encRat) :=
        (ComputableInPolyTime.map (encWeightedEdge_weight_polyTime id')).comp
          (encSimpleBMatching_edges_polyTime id')
      exact ComputableInPolyTime.rat_add' (computableInPolyTime_ratSum.comp hmap)
        (encSimpleBMatching_threshold_polyTime id')
    have hflat : ComputableInPolyTime
        (fun x : SimpleBMatchingInstance =>
          (List.range x.edges.length).flatMap fun idx =>
            let e := x.edges.getD idx ⟨0, 0, 0⟩
            let ae := x.numVertices * x.numVertices + 2 * idx
            let be := x.numVertices * x.numVertices + 2 * idx + 1
            ⟨ae, be, e.weight⟩ ::
              (((List.range (x.cap.getD e.u 0)).map fun i =>
                  ⟨e.u * x.numVertices + i, ae, e.weight⟩) ++
               ((List.range (x.cap.getD e.v 0)).map fun j =>
                  ⟨e.v * x.numVertices + j, be, e.weight⟩)))
        encSimpleBMatching (encList encWeightedEdge) := by
      have hrange : ComputableInPolyTime
          (fun x : SimpleBMatchingInstance => List.range x.edges.length)
          encSimpleBMatching (encList encUnary) := by fun_prop
      have hstep : ComputableInPolyTime
          (fun p : SimpleBMatchingInstance × ℕ =>
            let e := p.1.edges.getD p.2 ⟨0, 0, 0⟩
            let ae := p.1.numVertices * p.1.numVertices + 2 * p.2
            let be := p.1.numVertices * p.1.numVertices + 2 * p.2 + 1
            ⟨ae, be, e.weight⟩ ::
              (((List.range (p.1.cap.getD e.u 0)).map fun i =>
                  ⟨e.u * p.1.numVertices + i, ae, e.weight⟩) ++
               ((List.range (p.1.cap.getD e.v 0)).map fun j =>
                  ⟨e.v * p.1.numVertices + j, be, e.weight⟩)))
          (encPair encSimpleBMatching encUnary) (encList encWeightedEdge) := by
        have he : ComputableInPolyTime
            (fun p : SimpleBMatchingInstance × ℕ => p.1.edges.getD p.2 ⟨0, 0, 0⟩)
            (encPair encSimpleBMatching encUnary) encWeightedEdge :=
          (ComputableInPolyTime.listGetD (encA := encWeightedEdge) (d := ⟨0, 0, 0⟩)).comp
            ((encSimpleBMatching_edges_polyTime (ComputableInPolyTime.fst _ _)).prod
              (ComputableInPolyTime.snd _ _))
        have hcu : ComputableInPolyTime
            (fun p : SimpleBMatchingInstance × ℕ =>
              p.1.cap.getD (p.1.edges.getD p.2 ⟨0, 0, 0⟩).u 0)
            (encPair encSimpleBMatching encUnary) encUnary :=
          ComputableInPolyTime.listGetD_binary (d := 0)
            (encSimpleBMatching_cap_polyTime (ComputableInPolyTime.fst _ _))
            (encWeightedEdge_u_polyTime he)
        have hcv : ComputableInPolyTime
            (fun p : SimpleBMatchingInstance × ℕ =>
              p.1.cap.getD (p.1.edges.getD p.2 ⟨0, 0, 0⟩).v 0)
            (encPair encSimpleBMatching encUnary) encUnary :=
          ComputableInPolyTime.listGetD_binary (d := 0)
            (encSimpleBMatching_cap_polyTime (ComputableInPolyTime.fst _ _))
            (encWeightedEdge_v_polyTime he)
        have hn_bin : ComputableInPolyTime
            (fun p : SimpleBMatchingInstance × ℕ => p.1.numVertices)
            (encPair encSimpleBMatching encUnary) encNat :=
          ComputableInPolyTime.unary_to_binary.comp
            (encSimpleBMatching_numVertices_polyTime (ComputableInPolyTime.fst _ _))
        have hidx_bin : ComputableInPolyTime
            (fun p : SimpleBMatchingInstance × ℕ => p.2)
            (encPair encSimpleBMatching encUnary) encNat :=
          ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _)
        have hae : ComputableInPolyTime
            (fun p : SimpleBMatchingInstance × ℕ =>
              p.1.numVertices * p.1.numVertices + 2 * p.2)
            (encPair encSimpleBMatching encUnary) encNat := by fun_prop
        have hbe : ComputableInPolyTime
            (fun p : SimpleBMatchingInstance × ℕ =>
              p.1.numVertices * p.1.numVertices + 2 * p.2 + 1)
            (encPair encSimpleBMatching encUnary) encNat := by fun_prop
        have hhead : ComputableInPolyTime
            (fun p : SimpleBMatchingInstance × ℕ =>
              (⟨p.1.numVertices * p.1.numVertices + 2 * p.2,
                p.1.numVertices * p.1.numVertices + 2 * p.2 + 1,
                (p.1.edges.getD p.2 ⟨0, 0, 0⟩).weight⟩ : WeightedEdge))
            (encPair encSimpleBMatching encUnary) encWeightedEdge :=
          encWeightedEdge_mk_polyTime hae hbe (encWeightedEdge_weight_polyTime he)
        have hlistU : ComputableInPolyTime
            (fun p : SimpleBMatchingInstance × ℕ =>
              (List.range (p.1.cap.getD (p.1.edges.getD p.2 ⟨0, 0, 0⟩).u 0)).map fun i =>
                (⟨(p.1.edges.getD p.2 ⟨0, 0, 0⟩).u * p.1.numVertices + i,
                  p.1.numVertices * p.1.numVertices + 2 * p.2,
                  (p.1.edges.getD p.2 ⟨0, 0, 0⟩).weight⟩ : WeightedEdge))
            (encPair encSimpleBMatching encUnary) (encList encWeightedEdge) := by
          have hr : ComputableInPolyTime
              (fun p : SimpleBMatchingInstance × ℕ =>
                List.range (p.1.cap.getD (p.1.edges.getD p.2 ⟨0, 0, 0⟩).u 0))
              (encPair encSimpleBMatching encUnary) (encList encUnary) :=
            ComputableInPolyTime.range.comp hcu
          have hpar : ComputableInPolyTime
              (fun p : SimpleBMatchingInstance × ℕ =>
                (((p.1.edges.getD p.2 ⟨0, 0, 0⟩).u * p.1.numVertices,
                  p.1.numVertices * p.1.numVertices + 2 * p.2),
                  (p.1.edges.getD p.2 ⟨0, 0, 0⟩).weight))
              (encPair encSimpleBMatching encUnary)
              (encPair (encPair encNat encNat) encRat) := by
            have hu_mul : ComputableInPolyTime
                (fun p : SimpleBMatchingInstance × ℕ =>
                  (p.1.edges.getD p.2 ⟨0, 0, 0⟩).u * p.1.numVertices)
                (encPair encSimpleBMatching encUnary) encNat := by
              have hu := encWeightedEdge_u_polyTime he
              fun_prop
            exact (hu_mul.prod hae).prod (encWeightedEdge_weight_polyTime he)
          have hmkEdge : ComputableInPolyTime
              (fun q : ((ℕ × ℕ) × ℚ) × ℕ => (⟨q.1.1.1 + q.2, q.1.1.2, q.1.2⟩ : WeightedEdge))
              (encPair (encPair (encPair encNat encNat) encRat) encUnary) encWeightedEdge := by
            have hi_bin : ComputableInPolyTime
                (fun q : ((ℕ × ℕ) × ℚ) × ℕ => q.2)
                (encPair (encPair (encPair encNat encNat) encRat) encUnary) encNat :=
              ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _)
            fun_prop
          exact ComputableInPolyTime.mapWith hmkEdge hpar hr
        have hlistV : ComputableInPolyTime
            (fun p : SimpleBMatchingInstance × ℕ =>
              (List.range (p.1.cap.getD (p.1.edges.getD p.2 ⟨0, 0, 0⟩).v 0)).map fun j =>
                (⟨(p.1.edges.getD p.2 ⟨0, 0, 0⟩).v * p.1.numVertices + j,
                  p.1.numVertices * p.1.numVertices + 2 * p.2 + 1,
                  (p.1.edges.getD p.2 ⟨0, 0, 0⟩).weight⟩ : WeightedEdge))
            (encPair encSimpleBMatching encUnary) (encList encWeightedEdge) := by
          have hr : ComputableInPolyTime
              (fun p : SimpleBMatchingInstance × ℕ =>
                List.range (p.1.cap.getD (p.1.edges.getD p.2 ⟨0, 0, 0⟩).v 0))
              (encPair encSimpleBMatching encUnary) (encList encUnary) :=
            ComputableInPolyTime.range.comp hcv
          have hpar : ComputableInPolyTime
              (fun p : SimpleBMatchingInstance × ℕ =>
                (((p.1.edges.getD p.2 ⟨0, 0, 0⟩).v * p.1.numVertices,
                  p.1.numVertices * p.1.numVertices + 2 * p.2 + 1),
                  (p.1.edges.getD p.2 ⟨0, 0, 0⟩).weight))
              (encPair encSimpleBMatching encUnary)
              (encPair (encPair encNat encNat) encRat) := by
            have hv_mul : ComputableInPolyTime
                (fun p : SimpleBMatchingInstance × ℕ =>
                  (p.1.edges.getD p.2 ⟨0, 0, 0⟩).v * p.1.numVertices)
                (encPair encSimpleBMatching encUnary) encNat := by
              have hv := encWeightedEdge_v_polyTime he
              fun_prop
            exact (hv_mul.prod hbe).prod (encWeightedEdge_weight_polyTime he)
          have hmkEdge : ComputableInPolyTime
              (fun q : ((ℕ × ℕ) × ℚ) × ℕ => (⟨q.1.1.1 + q.2, q.1.1.2, q.1.2⟩ : WeightedEdge))
              (encPair (encPair (encPair encNat encNat) encRat) encUnary) encWeightedEdge := by
            have hj_bin : ComputableInPolyTime
                (fun q : ((ℕ × ℕ) × ℚ) × ℕ => q.2)
                (encPair (encPair (encPair encNat encNat) encRat) encUnary) encNat :=
              ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _)
            fun_prop
          exact ComputableInPolyTime.mapWith hmkEdge hpar hr
        exact ComputableInPolyTime.cons' hhead
          (ComputableInPolyTime.listAppend' hlistU hlistV)
      exact ComputableInPolyTime.flatMapWith (encA := encUnary) (encB := encWeightedEdge)
        (encP := encSimpleBMatching) hstep ComputableInPolyTime.id' hrange
    exact encMaxWeightMatching_mk_polyTime hnum hflat htot
  unfold tutteReduce
  exact ComputableInPolyTime.ite hwf hmain (ComputableInPolyTime.const mwmNoInstance)

/-- **Tutte's reduction**: `MaxWeightSimpleBMatching` reduces in polynomial time to
`MaxWeightMatching`. -/
theorem polyTimeReducible_simpleBMatching_maxWeightMatching :
    PolyTimeReducible encSimpleBMatching encMaxWeightMatching
      MaxWeightSimpleBMatching MaxWeightMatching :=
  ⟨tutteReduce, computableInPolyTime_tutteReduce, fun x => (tutteReduce_mem_iff x).symm⟩

end CslibFrontier.Complexity
