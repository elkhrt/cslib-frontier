module
/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

public import Cslib.Computability.Circuit.Boolean.Complexity
public import CslibFrontier.Computability.Circuit.Monotone.DualRail
public import CslibFrontier.Computability.Circuit.Monotone.Synthesis
public import CslibFrontier.Foundations.Data.BitString.Weight
public import Mathlib.Data.Nat.Log
import Cslib.Computability.Circuit.Composition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Monotone Circuit Complexity of Boolean Slice Functions (Berkowitz's Theorem)

A Boolean function `f : BitString n → Bool` is an `ℓ`-*slice function* if `f x = false` whenever
`BitString.weight x < ℓ` and `f x = true` whenever `ℓ < BitString.weight x`. Every slice function
is monotone. Berkowitz observed that on inputs of Hamming weight `ℓ`, each negated literal
`!(x i)` coincides with the monotone threshold predicate
`ℓ ≤ ∑ j ∈ Finset.univ.erase i, (x j).toNat` ("pseudo-complement"). Feeding these
pseudo-complements into Goldschlager's dual-rail translation (`Cslib.Circuits.Monotone.dualRail`,
doubling circuit size) and clamping the output with the monotone thresholds `ℓ ≤ weight x` and
`ℓ + 1 ≤ weight x` converts any De Morgan circuit into a monotone circuit on the `ℓ`-slice with
polynomial additive overhead.

Using simultaneous monotone prefix- and suffix-threshold dynamic programming via
`Cslib.Circuits.Synthesis`, we prove under standard Lean constraints:
* polynomial-size (`≤ 2 * n ^ 2 + 2`) monotone circuits for every unweighted threshold function;
* multi-output `ℓ`-slice monotonization of any De Morgan circuit `c : Circuit Boolean.signature n m`
  in size `≤ 2 * c.size + 6 * n ^ 2 + 6 * n + 2 * m + 6`; and
* Berkowitz's theorem `ecomplexity Monotone.interpretation (single g) ≤
  ↑(2 * complexity Boolean.interpretation (single g) + 12 * n ^ 2 * Nat.log 2 n)` for every
  `n : ℕ` and every slice function `g : BitString n → Bool`.

## Main definitions

* `CslibFrontier.BooleanSlice.IsSliceAt`: predicate that `f : BitString n → Bool` is an `ℓ`-slice
  function.
* `CslibFrontier.BooleanSlice.IsSlice`: predicate that `f : BitString n → Bool` is a slice function
  for some threshold `ℓ : ℕ`.
* `CslibFrontier.BooleanSlice.toSlice`: unique `ℓ`-slice function agreeing with `f` on weight `ℓ`.
* `CslibFrontier.BooleanSlice.sliceNeg`: unique `ℓ`-slice function agreeing with `!f` on weight `ℓ`.

## Main results

* `CslibFrontier.BooleanSlice.IsSliceAt.monotone`, `CslibFrontier.BooleanSlice.IsSlice.monotone`:
  every
  slice function is monotone.
* `CslibFrontier.BooleanSlice.exists_monotone_threshold_circuit`: every threshold function
  `x ↦ decide (ℓ ≤ weight x)` on `n` bits has a monotone circuit of size at most `2 * n ^ 2 + 2`.
* `CslibFrontier.BooleanSlice.exists_monotone_toSlice_of_circuit`: clamping every output of an
  `m`-output De Morgan circuit `c` to the `ℓ`-slice has a monotone circuit of size at most
  `2 * c.size + 6 * n ^ 2 + 6 * n + 2 * m + 6`.
* `CslibFrontier.BooleanSlice.berkowitz_monotone_complexity_le`: Berkowitz's inequality bounding the
  monotone circuit complexity of any slice function `g` on `n` bits by
  `2 * C(g) + 12 * n ^ 2 * Nat.log 2 n`.
-/

public section

namespace CslibFrontier.BooleanSlice

open Cslib Cslib.BitString Cslib.Circuits Finset

/-! ### Boolean Slice Functions -/

section SliceDefs

variable {n : ℕ}

/-- A Boolean function `f : BitString n → Bool` is an `ℓ`-slice function if it outputs `false`
below Hamming weight `ℓ` and `true` above Hamming weight `ℓ`. -/
def IsSliceAt (ℓ : ℕ) (f : BitString n → Bool) : Prop :=
  (∀ x : BitString n, weight x < ℓ → f x = false) ∧
  (∀ x : BitString n, ℓ < weight x → f x = true)

/-- A Boolean function `f : BitString n → Bool` is a slice function if it is an `ℓ`-slice
function for some threshold `ℓ : ℕ`. -/
def IsSlice (f : BitString n → Bool) : Prop :=
  ∃ ℓ : ℕ, IsSliceAt ℓ f

private theorem not_true_le_false : ¬ (true ≤ false) := by decide

private theorem toNat_le_of_bool_le {a b : Bool} (h : a ≤ b) : a.toNat ≤ b.toNat := by
  cases a <;> cases b
  · simp
  · simp
  · exact absurd h not_true_le_false
  · simp

/-- Every `ℓ`-slice function is monotone with respect to the pointwise Boolean order. -/
theorem IsSliceAt.monotone {ℓ : ℕ} {f : BitString n → Bool} (hf : IsSliceAt ℓ f) :
    Monotone f := by
  intro x y hxy
  have hw_le : weight x ≤ weight y := by
    rw [weight_eq_sum_toNat, weight_eq_sum_toNat]
    exact Finset.sum_le_sum fun i _ ↦ toNat_le_of_bool_le (hxy i)
  rcases lt_trichotomy (weight x) ℓ with hlt | heq | hgt
  · rw [hf.1 x hlt]; exact Bool.false_le _
  · rcases eq_or_lt_of_le hw_le with hweq | hwlt
    · have hxy_eq : x = y := by
        funext i
        have hi := hxy i
        cases hxi : x i <;> cases hyi : y i
        · rfl
        · exfalso
          have hlt_sum : ∑ j : Fin n, (x j).toNat < ∑ j : Fin n, (y j).toNat :=
            Finset.sum_lt_sum (fun j _ ↦ toNat_le_of_bool_le (hxy j))
              ⟨i, Finset.mem_univ i, by simp [hxi, hyi]⟩
          rw [← weight_eq_sum_toNat, ← weight_eq_sum_toNat] at hlt_sum
          omega
        · rw [hxi, hyi] at hi; exact absurd hi not_true_le_false
        · rfl
      rw [hxy_eq]
    · rw [hf.2 y (heq ▸ hwlt)]; exact Bool.le_true _
  · rw [hf.2 y (hgt.trans_le hw_le)]; exact Bool.le_true _

/-- Every slice function is monotone. -/
theorem IsSlice.monotone {f : BitString n → Bool} (hf : IsSlice f) : Monotone f :=
  let ⟨_, h⟩ := hf
  h.monotone

/-- Clamp an arbitrary Boolean function `f : BitString n → Bool` to the `ℓ`-slice: `false` when
`weight x < ℓ`, `f x` when `weight x = ℓ`, and `true` when `ℓ < weight x`. -/
def toSlice (ℓ : ℕ) (f : BitString n → Bool) (x : BitString n) : Bool :=
  (f x && decide (ℓ ≤ weight x)) || decide (ℓ + 1 ≤ weight x)

/-- `toSlice ℓ f` is an `ℓ`-slice function. -/
theorem isSliceAt_toSlice (ℓ : ℕ) (f : BitString n → Bool) : IsSliceAt ℓ (toSlice ℓ f) := by
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have h1 : ¬ (ℓ ≤ weight x) := by omega
    have h2 : ¬ (ℓ + 1 ≤ weight x) := by omega
    simp [toSlice, h1, h2]
  · have h2 : ℓ + 1 ≤ weight x := by omega
    simp [toSlice, h2]

/-- On inputs of Hamming weight `ℓ`, `toSlice ℓ f` agrees with `f`. -/
@[simp]
theorem toSlice_of_weight_eq {ℓ : ℕ} (f : BitString n → Bool) {x : BitString n}
    (hx : weight x = ℓ) : toSlice ℓ f x = f x := by
  simp [toSlice, hx]

/-- Below the `ℓ`-slice, `toSlice ℓ f` outputs `false`. -/
theorem toSlice_of_weight_lt {ℓ : ℕ} (f : BitString n → Bool) {x : BitString n}
    (hx : weight x < ℓ) : toSlice ℓ f x = false :=
  (isSliceAt_toSlice ℓ f).1 x hx

/-- Above the `ℓ`-slice, `toSlice ℓ f` outputs `true`. -/
theorem toSlice_of_weight_gt {ℓ : ℕ} (f : BitString n → Bool) {x : BitString n}
    (hx : ℓ < weight x) : toSlice ℓ f x = true :=
  (isSliceAt_toSlice ℓ f).2 x hx

/-- If `f` is already an `ℓ`-slice function, `toSlice ℓ f = f`. -/
theorem IsSliceAt.toSlice_eq {ℓ : ℕ} {f : BitString n → Bool} (hf : IsSliceAt ℓ f) :
    toSlice ℓ f = f := by
  funext x
  rcases lt_trichotomy (weight x) ℓ with hlt | heq | hgt
  · rw [toSlice_of_weight_lt f hlt, hf.1 x hlt]
  · exact toSlice_of_weight_eq f heq
  · rw [toSlice_of_weight_gt f hgt, hf.2 x hgt]

/-- The `ℓ`-slice negation of `f`: negates `f` on inputs of weight `ℓ` and outputs `false` below
and `true` above `ℓ`. -/
def sliceNeg (ℓ : ℕ) (f : BitString n → Bool) : BitString n → Bool :=
  toSlice ℓ fun x ↦ !(f x)

/-- `sliceNeg ℓ f` is an `ℓ`-slice function. -/
theorem isSliceAt_sliceNeg (ℓ : ℕ) (f : BitString n → Bool) : IsSliceAt ℓ (sliceNeg ℓ f) :=
  isSliceAt_toSlice ℓ _

/-- On the `ℓ`-slice, `sliceNeg ℓ f x = !(f x)`. -/
@[simp]
theorem sliceNeg_of_weight_eq {ℓ : ℕ} (f : BitString n → Bool) {x : BitString n}
    (hx : weight x = ℓ) : sliceNeg ℓ f x = !(f x) :=
  toSlice_of_weight_eq _ hx

end SliceDefs

/-! ### Monotone Prefix/Suffix Threshold Synthesis and Berkowitz's Theorem -/

section MonotoneSynthesis

private def prefixThr {n m : ℕ} (idx : Fin m → Fin n) (i k : ℕ) (x : BitString n) : Bool :=
  decide (k ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin m ↦ j.val < i), (x (idx j)).toNat)

private def tableSet {n m : ℕ} (idx : Fin m → Fin n) (K t : ℕ) : Set (BitString n → Bool) :=
  {fun _ ↦ false, fun _ ↦ true} ∪
    {f | ∃ i ≤ t, ∃ k ≤ K, f = prefixThr idx i k}

/-- Dynamic-programming synthesis of all prefix thresholds `prefixThr idx i k` (`i ≤ m`, `k ≤ K`)
in `2 + 2 * m * K` monotone gates. -/
private theorem synthesis_prefixTable {n K : ℕ} :
    ∀ (m t : ℕ), t ≤ m → ∀ (idx : Fin m → Fin n),
      Synthesis Monotone.interpretation (inputs n) (tableSet idx K t) (2 + 2 * t * K) := by
  intro m t
  induction t with
  | zero =>
    intro _ idx
    have hconst : Synthesis Monotone.interpretation (inputs n)
        ({fun _ ↦ false, fun _ ↦ true} : Set (BitString n → Bool)) 2 := by
      simpa [Set.pair_comm] using
        (Synthesis.monotone_const (n := n) (s := inputs n) false).union
          (Synthesis.monotone_const (n := n) (s := inputs n) true)
    refine hconst.mono Set.Subset.rfl ?_ (by omega)
    intro f hf
    rcases hf with hc | ⟨i, hi, k, _, rfl⟩
    · exact hc
    · obtain rfl : i = 0 := by omega
      rcases k with _ | k
      · right; funext x; simp [prefixThr]
      · left; funext x; simp [prefixThr]
  | succ t ih =>
    intro ht idx
    have hprev := ih (by omega) idx
    let src := inputs n ∪ tableSet idx K t
    let stepFn (k : Fin K) : BitString n → Bool := prefixThr idx (t + 1) (k.val + 1)
    have hstep : Synthesis Monotone.interpretation src (Set.range stepFn) (2 * K) := by
      have hfam := Synthesis.family (I := Monotone.interpretation) (s := src) stepFn
        (fun _ ↦ 2) fun k ↦ ?_
      · refine hfam.mono Set.Subset.rfl Set.Subset.rfl ?_
        simp [Nat.mul_comm]
      · have hmem_hi : prefixThr idx t (k.val + 1) ∈ src :=
          Set.mem_union_right _ (Set.mem_union_right _ ⟨t, le_rfl, k.val + 1, by omega, rfl⟩)
        have hmem_lo : prefixThr idx t k.val ∈ src :=
          Set.mem_union_right _ (Set.mem_union_right _ ⟨t, le_rfl, k.val, by omega, rfl⟩)
        let j₀ : Fin m := ⟨t, by omega⟩
        have hmem_in : (fun x : BitString n ↦ x (idx j₀)) ∈ src :=
          Set.mem_union_left _ ⟨idx j₀, rfl⟩
        have hgate := (Synthesis.of_mem (I := Monotone.interpretation) hmem_hi).monotone_or
          ((Synthesis.of_mem hmem_in).monotone_and (Synthesis.of_mem hmem_lo))
        have hfun : (fun x : BitString n ↦
            prefixThr idx t (k.val + 1) x || (x (idx j₀) && prefixThr idx t k.val x)) =
            stepFn k := by
          funext x
          simp only [prefixThr, stepFn]
          have hfilt : Finset.univ.filter (fun j : Fin m ↦ j.val < t + 1) =
              insert j₀ (Finset.univ.filter (fun j : Fin m ↦ j.val < t)) := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Fin.ext_iff, j₀]
            omega
          have hnot : j₀ ∉ Finset.univ.filter (fun j : Fin m ↦ j.val < t) := by simp [j₀]
          rw [hfilt, Finset.sum_insert hnot]
          set S := ∑ j ∈ Finset.univ.filter (fun j : Fin m ↦ j.val < t), (x (idx j)).toNat
          cases x (idx j₀) <;>
            (simp only [Bool.toNat_false, Bool.toNat_true, Bool.false_and, Bool.true_and,
              Bool.or_false]
             by_cases h1 : k.val + 1 ≤ S <;> by_cases h2 : k.val ≤ S <;>
               simp [h1, h2] <;> omega)
        rw [hfun] at hgate
        exact hgate
    refine (hprev.comp hstep).mono Set.Subset.rfl ?_ (by ring_nf; omega)
    intro f hf
    rcases hf with hc | ⟨i, hi, k, hk, rfl⟩
    · exact Set.mem_union_left _ (Set.mem_union_left _ hc)
    · rcases Nat.of_le_succ hi with hit | rfl
      · exact Set.mem_union_left _ (Set.mem_union_right _ ⟨i, hit, k, hk, rfl⟩)
      · rcases k with _ | k'
        · refine Set.mem_union_left _ (Set.mem_union_left _ (.inr ?_))
          funext x; simp [prefixThr]
        · exact Set.mem_union_right _ ⟨⟨k', by omega⟩, rfl⟩

/-- **Polynomial-size monotone threshold circuits**: for every `n, ℓ : ℕ`, there exists a monotone
circuit of size at most `2 * n ^ 2 + 2` computing `x ↦ decide (ℓ ≤ weight x)`. -/
theorem exists_monotone_threshold_circuit (n ℓ : ℕ) :
    ∃ c : Circuit Monotone.signature n 1,
      c.Computes Monotone.interpretation (single fun x ↦ decide (ℓ ≤ weight x)) ∧
      c.size ≤ 2 * n ^ 2 + 2 := by
  by_cases hℓ : ℓ ≤ n
  · have hsyn := synthesis_prefixTable (n := n) (K := ℓ) n n le_rfl id
    have hmem : (fun x : BitString n ↦ decide (ℓ ≤ weight x)) ∈ tableSet (id : Fin n →
      Fin n) ℓ n := by
      refine Set.mem_union_right _ ⟨n, le_rfl, ℓ, le_rfl, funext fun x ↦ ?_⟩
      simp only [prefixThr, id, weight_eq_sum_toNat]
      congr 2
      exact (Finset.sum_congr (by ext j; simp) fun _ _ ↦ rfl).symm
    exact (hsyn.mono Set.Subset.rfl (Set.singleton_subset_iff.mpr hmem)
      (by nlinarith)).exists_circuit
  · have hfn : (fun x : BitString n ↦ decide (ℓ ≤ weight x)) = fun _ ↦ false := by
      funext x
      have hlt : weight x < ℓ := (weight_le x).trans_lt (by simpa using lt_of_not_ge hℓ)
      simp [show ¬ (ℓ ≤ weight x) by omega]
    rw [hfn]
    exact ((Synthesis.monotone_const (n := n) (s := inputs n) false).mono
      Set.Subset.rfl Set.Subset.rfl (by omega)).exists_circuit

/-- Simultaneous monotone pseudo-complement and threshold circuit on `n` inputs (`ℓ ≤ n`) of size
at most `6 * n ^ 2 + 6 * n + 6`. -/
private theorem exists_pseudoComplement_circuit {n ℓ : ℕ} (hℓ : ℓ ≤ n) :
    ∃ pc : Circuit Monotone.signature n ((2 * n + 1) + 2),
      (∀ x : BitString n, weight x = ℓ →
        ∀ r : Fin (2 * n + 1),
          pc.eval Monotone.interpretation x (Fin.castAdd 2 r) = Monotone.railBitString x r) ∧
      (∀ x : BitString n,
        pc.eval Monotone.interpretation x (Fin.natAdd (2 * n + 1) 0) = decide (ℓ ≤ weight x)) ∧
      (∀ x : BitString n,
        pc.eval Monotone.interpretation x (Fin.natAdd (2 * n + 1) 1) =
          decide (ℓ + 1 ≤ weight x)) ∧
      pc.size ≤ 6 * n ^ 2 + 6 * n + 6 := by
  let rev : Fin n → Fin n := fun j ↦ ⟨n - 1 - j.val, by omega⟩
  have hP := synthesis_prefixTable (n := n) (K := ℓ + 1) n n le_rfl id
  have hS := synthesis_prefixTable (n := n) (K := ℓ) n n le_rfl rev
  have hPS := hP.union hS
  let src := inputs n ∪ (tableSet (id : Fin n → Fin n) (ℓ + 1) n ∪ tableSet rev ℓ n)
  let pseudo (i : Fin n) (x : BitString n) : Bool :=
    (List.finRange (ℓ + 1)).foldr
      (fun k acc ↦ (prefixThr id i.val k.val x && prefixThr rev (n - 1 - i.val) (ℓ - k.val) x) ||
        acc) false
  have hpseudo_syn : Synthesis Monotone.interpretation src (Set.range pseudo)
      (n * (2 * (ℓ + 1))) := by
    have hfam := Synthesis.family (I := Monotone.interpretation) (s := src) pseudo
      (fun _ ↦ 2 * (ℓ + 1)) fun i ↦ ?_
    · refine hfam.mono Set.Subset.rfl Set.Subset.rfl ?_
      simp
    · have hfalse : (fun _ : BitString n ↦ false) ∈ src :=
        Set.mem_union_right _ (Set.mem_union_left _ (Set.mem_union_left _ (.inl rfl)))
      have hfold := Synthesis.foldr (I := Monotone.interpretation) (s := src)
        (· || ·) 1
        (fun f g ↦ by
          simpa using (Synthesis.of_mem (s := {f, g}) (.inl rfl)).monotone_or
            (Synthesis.of_mem (.inr rfl)))
        (List.finRange (ℓ + 1))
        (f := fun k : Fin (ℓ + 1) ↦ fun x ↦
          prefixThr id i.val k.val x && prefixThr rev (n - 1 - i.val) (ℓ - k.val) x)
        (cost := fun _ ↦ 1)
        (Synthesis.of_mem hfalse)
        fun k _ ↦ by
          have h1 : prefixThr (id : Fin n → Fin n) i.val k.val ∈ src :=
            Set.mem_union_right _ (Set.mem_union_left _ (Set.mem_union_right _
              ⟨i.val, by omega, k.val, by omega, rfl⟩))
          have h2 : prefixThr rev (n - 1 - i.val) (ℓ - k.val) ∈ src :=
            Set.mem_union_right _ (Set.mem_union_right _ (Set.mem_union_right _
              ⟨n - 1 - i.val, by omega, ℓ - k.val, by omega, rfl⟩))
          simpa using (Synthesis.of_mem h1).monotone_and (Synthesis.of_mem h2)
      refine hfold.mono Set.Subset.rfl Set.Subset.rfl ?_
      simp [List.map_const', Nat.mul_comm]
  have hfull := (Synthesis.of_subset (I := Monotone.interpretation) (s := inputs n)
    Set.Subset.rfl).union (hPS.comp hpseudo_syn)
  let railFn (r : Fin (2 * n + 1)) : BitString n → Bool :=
    if hr0 : r.val = 0 then fun _ ↦ true
    else if (r.val - 1) % 2 = 0 then fun x ↦ x ⟨(r.val - 1) / 2, by omega⟩
    else pseudo ⟨(r.val - 1) / 2, by omega⟩
  let thrGe : BitString n → Bool := fun x ↦ decide (ℓ ≤ weight x)
  let thrGt : BitString n → Bool := fun x ↦ decide (ℓ + 1 ≤ weight x)
  let outFn : Fin ((2 * n + 1) + 2) → BitString n → Bool := Fin.append railFn ![thrGe, thrGt]
  have hcost : 0 + (2 + 2 * n * (ℓ + 1) + (2 + 2 * n * ℓ) + n * (2 * (ℓ + 1))) ≤
      6 * n ^ 2 + 6 * n + 6 := by nlinarith
  have hfilt_all : Finset.univ.filter (fun a : Fin n ↦ a.val < n) = Finset.univ :=
    Finset.filter_true_of_mem fun a _ ↦ a.isLt
  have hrange : Set.range outFn ⊆ inputs n ∪
      ((tableSet (id : Fin n → Fin n) (ℓ + 1) n ∪ tableSet rev ℓ n) ∪ Set.range pseudo) := by
    rintro _ ⟨j, rfl⟩
    refine Fin.addCases (fun r ↦ ?_) (fun t ↦ ?_) j
    · simp only [outFn, Fin.append_left, railFn]
      split_ifs
      · exact Set.mem_union_right _ (Set.mem_union_left _ (Set.mem_union_left _
          (Set.mem_union_left _ (.inr rfl))))
      · exact Set.mem_union_left _ ⟨_, rfl⟩
      · exact Set.mem_union_right _ (Set.mem_union_right _ ⟨_, rfl⟩)
    · simp only [outFn, Fin.append_right]
      fin_cases t
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        refine Set.mem_union_right _ (Set.mem_union_left _ (Set.mem_union_left _
          (Set.mem_union_right _ ⟨n, le_rfl, ℓ, by omega, funext fun x ↦ ?_⟩)))
        simp only [thrGe, prefixThr, id, hfilt_all, weight_eq_sum_toNat]
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        refine Set.mem_union_right _ (Set.mem_union_left _ (Set.mem_union_left _
          (Set.mem_union_right _ ⟨n, le_rfl, ℓ + 1, le_rfl, funext fun x ↦ ?_⟩)))
        simp only [thrGt, prefixThr, id, hfilt_all, weight_eq_sum_toNat]
  obtain ⟨pc, hpc, hsz⟩ := (hfull.mono Set.Subset.rfl hrange hcost).exists_circuit_outputs
  have hfoldr_or : ∀ (l : List (Fin (ℓ + 1))) (p : Fin (ℓ + 1) → Bool),
      l.foldr (fun a acc ↦ p a || acc) false = true ↔ ∃ a ∈ l, p a = true := by
    intro l p
    induction l with
    | nil => simp
    | cons a l ih => simp [Bool.or_eq_true, ih]
  refine ⟨pc, fun x hwx r ↦ ?_, fun x ↦ ?_, fun x ↦ ?_, hsz⟩
  · rw [congrFun (hpc x) (Fin.castAdd 2 r)]
    simp only [outFn, Fin.append_left, railFn]
    by_cases hr0 : r.val = 0
    · have h0 : r = 0 := Fin.ext hr0
      subst h0; simp [Monotone.railBitString]
    · simp only [hr0, ↓reduceDIte]
      let i : Fin n := ⟨(r.val - 1) / 2, by omega⟩
      by_cases hpar : (r.val - 1) % 2 = 0
      · simp only [hpar, ↓reduceIte]
        have hreq : r.val = Monotone.railWire true i.val := by dsimp [Monotone.railWire, i]; omega
        have hrb := Monotone.getD_railBits_true (List.ofFn x) (w := i.val) (by simp)
        change x i = (Monotone.railBits (List.ofFn x)).getD r.val false
        rw [hreq, hrb, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp [i.isLt]
      · simp only [hpar, ↓reduceIte]
        have hreq : r.val = Monotone.railWire false i.val := by dsimp [Monotone.railWire, i]; omega
        have hrb := Monotone.getD_railBits_false (List.ofFn x) (w := i.val) (by simp)
        change pseudo i x = (Monotone.railBits (List.ofFn x)).getD r.val false
        rw [hreq, hrb, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [i.isLt, ↓reduceDIte, Option.getD_some]
        change pseudo i x = !(x i)
        rw [Bool.eq_iff_iff]
        simp only [pseudo, hfoldr_or, List.mem_finRange, true_and, Bool.and_eq_true,
          prefixThr, id, decide_eq_true_iff]
        have hrev_eq :
            (∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < n - 1 - i.val),
              (x (rev j)).toNat) =
            ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ i.val < j.val), (x j).toNat := by
          refine Finset.sum_bij (fun j _ ↦ rev j)
            (fun j hj ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              have := (Finset.mem_filter.mp hj).2; dsimp [rev]; omega⟩)
            (fun a ha b hb h ↦ Fin.ext (by
              have := (Finset.mem_filter.mp ha).2
              have := (Finset.mem_filter.mp hb).2
              have hv := congrArg Fin.val h; dsimp [rev] at hv; omega))
            (fun j hj ↦ ⟨⟨n - 1 - j.val, by omega⟩, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, by have := (Finset.mem_filter.mp hj).2; simp; omega⟩,
              Fin.ext (by have := (Finset.mem_filter.mp hj).2; dsimp [rev]; omega)⟩)
            (fun _ _ ↦ rfl)
        rw [hrev_eq]
        set A := ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val), (x j).toNat
        set B := ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ i.val < j.val), (x j).toNat
        have hAB : A + (x i).toNat + B = ℓ := by
          rw [← hwx, weight_eq_sum_toNat, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
          have her : Finset.univ.erase i =
              Finset.univ.filter (fun j : Fin n ↦ j.val < i.val) ∪
              Finset.univ.filter (fun j : Fin n ↦ i.val < j.val) := by
            ext j; simp [Fin.ext_iff]
          have hdj : Disjoint (Finset.univ.filter (fun j : Fin n ↦ j.val < i.val))
              (Finset.univ.filter (fun j : Fin n ↦ i.val < j.val)) :=
            Finset.disjoint_left.mpr fun j h1 h2 ↦ by
              have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
          rw [her, Finset.sum_union hdj]; omega
        constructor
        · rintro ⟨k, hk1, hk2⟩
          cases hxi : x i <;> simp_all; omega
        · intro hnot
          have hxi : x i = false := by simpa using hnot
          have hAB' : A + B = ℓ := by simp [hxi] at hAB; omega
          exact ⟨⟨A, by omega⟩, le_rfl, by simp; omega⟩
  · simpa [outFn, thrGe] using congrFun (hpc x) (Fin.natAdd (2 * n + 1) 0)
  · simpa [outFn, thrGt] using congrFun (hpc x) (Fin.natAdd (2 * n + 1) 1)

/-- **Multi-output `ℓ`-slice monotonization**: for any De Morgan circuit
`c : Circuit Boolean.signature n m` and any `ℓ : ℕ`, there exists a monotone circuit
`cMon : Circuit Monotone.signature n m` of size at most
`2 * c.size + 6 * n ^ 2 + 6 * n + 2 * m + 6` computing
`toSlice ℓ (fun y ↦ c.eval Boolean.interpretation y j)` on every output `j : Fin m`. -/
theorem exists_monotone_toSlice_of_circuit {n m : ℕ} (c : Circuit Boolean.signature n m)
    (ℓ : ℕ) :
    ∃ cMon : Circuit Monotone.signature n m,
      (∀ (x : BitString n) (j : Fin m),
        cMon.eval Monotone.interpretation x j =
          toSlice ℓ (fun y ↦ c.eval Boolean.interpretation y j) x) ∧
      cMon.size ≤ 2 * c.size + 6 * n ^ 2 + 6 * n + 2 * m + 6 := by
  by_cases hℓ : ℓ ≤ n
  · obtain ⟨pc, hrail, hge, hgt, hpcsz⟩ := exists_pseudoComplement_circuit hℓ
    let feed : Fin (2 * n + 1) → Wire n pc.size := fun r ↦ pc.outputs (Fin.castAdd 2 r)
    let dr : Circuit Monotone.signature (2 * n + 1) m := Monotone.dualRail c
    -- Combine `dr` outputs with the two threshold outputs of `pc` in one `(m + 2)`-output circuit.
    let mid : Circuit Monotone.signature n (m + 2) :=
      ⟨pc.program.append feed dr.program,
       Fin.append (fun j ↦ Program.appendedWire feed (dr.outputs j))
         (fun t ↦ (pc.outputs (Fin.natAdd (2 * n + 1) t)).castAdd dr.size)⟩
    have hmid_sz : mid.size = pc.size + 2 * c.size := by
      change pc.size + dr.size = _
      rw [Monotone.size_dualRail]
    -- Clamp circuit on `m + 2` inputs: output `j` is `(in j && in m) || in (m + 1)`, size `2 * m`.
    have hclamp_syn : Synthesis Monotone.interpretation (inputs (m + 2))
        (Set.range fun j : Fin m ↦ fun z : BitString (m + 2) ↦
          (z (Fin.castAdd 2 j) && z (Fin.natAdd m 0)) || z (Fin.natAdd m 1)) (2 * m) := by
      have hfam := Synthesis.family (I := Monotone.interpretation) (s := inputs (m + 2))
        (fun j : Fin m ↦ fun z : BitString (m + 2) ↦
          (z (Fin.castAdd 2 j) && z (Fin.natAdd m 0)) || z (Fin.natAdd m 1))
        (fun _ ↦ 2) fun j ↦ by
          simpa using ((Synthesis.of_mem (s := inputs (m + 2)) ⟨Fin.castAdd 2 j, rfl⟩).monotone_and
            (Synthesis.of_mem ⟨Fin.natAdd m 0, rfl⟩)).monotone_or
            (Synthesis.of_mem ⟨Fin.natAdd m 1, rfl⟩)
      exact hfam.mono Set.Subset.rfl Set.Subset.rfl (by simp [Nat.mul_comm])
    obtain ⟨cl, hcl, hclsz⟩ := hclamp_syn.exists_circuit_outputs
    refine ⟨cl.comp mid, fun x j ↦ ?_, ?_⟩
    · rw [Circuit.eval_comp, congrFun (hcl _) j]
      have hmid_ge : mid.eval Monotone.interpretation x (Fin.natAdd m 0) =
          decide (ℓ ≤ weight x) := by
        simp only [mid, Circuit.eval, Function.comp_apply, Fin.append_right]
        exact (Program.trace_append_castAdd _ _ _ x _ _).trans (hge x)
      have hmid_gt : mid.eval Monotone.interpretation x (Fin.natAdd m 1) =
          decide (ℓ + 1 ≤ weight x) := by
        simp only [mid, Circuit.eval, Function.comp_apply, Fin.append_right]
        exact (Program.trace_append_castAdd _ _ _ x _ _).trans (hgt x)
      dsimp only
      rw [hmid_ge, hmid_gt]
      rcases lt_trichotomy (weight x) ℓ with hlt | heq | hgt'
      · have h1 : ¬ (ℓ ≤ weight x) := by omega
        have h2 : ¬ (ℓ + 1 ≤ weight x) := by omega
        simp [toSlice, h1, h2]
      · have h1 : ℓ ≤ weight x := by omega
        have h2 : ¬ (ℓ + 1 ≤ weight x) := by omega
        have hmid_j : mid.eval Monotone.interpretation x (Fin.castAdd 2 j) =
            c.eval Boolean.interpretation x j := by
          simp only [mid, Circuit.eval, Function.comp_apply, Fin.append_left]
          rw [Program.trace_append_appendedWire]
          have hfeed : (fun r ↦ pc.program.trace Monotone.interpretation x
              (pc.outputs (Fin.castAdd 2 r))) = Monotone.railBitString x := funext (hrail x heq)
          rw [hfeed]
          exact Monotone.eval_dualRail c x j
        simp [toSlice, h1, h2, hmid_j]
      · have h2 : ℓ + 1 ≤ weight x := by omega
        simp [toSlice, h2]
    · rw [Circuit.size_comp, hmid_sz]
      omega
  · obtain ⟨cFalse, hcF, hszF⟩ :=
      (Synthesis.monotone_const (n := n) (s := inputs n) false).exists_circuit
    refine ⟨cFalse.comapOutputs fun _ ↦ 0, fun x j ↦ ?_, ?_⟩
    · have hlt : weight x < ℓ := (weight_le x).trans_lt (by simpa using lt_of_not_ge hℓ)
      rw [toSlice_of_weight_lt _ hlt, Circuit.eval_comapOutputs, Function.comp_apply,
        congrFun (hcF x) 0, single_apply]
    · rw [Circuit.comapOutputs_size]
      omega

/-- **Berkowitz's Slice Function Theorem**: for every `n : ℕ` and every Boolean slice function
`g : BitString n → Bool`, there is a monotone circuit computing `g` of size at most
`2 * complexity Boolean.interpretation (single g) + 12 * n ^ 2 * Nat.log 2 n`; equivalently
`ecomplexity Monotone.interpretation (single g) ≤ ↑(2 * C(g) + 12 * n ^ 2 * Nat.log 2 n)`. -/
theorem berkowitz_monotone_complexity_le {n : ℕ} {g : BitString n → Bool} (hg : IsSlice g) :
    ecomplexity Monotone.interpretation (single g) ≤
      ((2 * complexity Boolean.interpretation (single g) +
        12 * n ^ 2 * Nat.log 2 n : ℕ) : ℕ∞) := by
  rw [ecomplexity_le_iff]
  obtain ⟨ℓ, hℓ⟩ := hg
  obtain ⟨c, hc, hcs⟩ := exists_computes_size_eq_complexity (I := Boolean.interpretation)
    (f := single g)
  rcases n with _ | _ | n'
  · obtain ⟨cm, hcm, hcms⟩ :=
      (Synthesis.monotone_const (n := 0) (s := inputs 0) (g Fin.elim0)).exists_circuit
    have hpos : 1 ≤ c.size := by
      rcases hsz : c.size with _ | s
      · exact (c.outputs 0).rec (fun i ↦ i.elim0) (fun i ↦ (hsz ▸ i).elim0)
      · omega
    refine ⟨cm, fun x ↦ funext fun j ↦ ?_, by omega⟩
    have hx : x = Fin.elim0 := funext fun i ↦ i.elim0
    rw [congrFun (hcm x) j, single_apply, single_apply, hx]
  · have hmono := hℓ.monotone
    have h01 : g ![false] ≤ g ![true] := hmono fun i ↦ by rw [Fin.eq_zero i]; decide
    cases hb0 : g ![false] <;> cases hb1 : g ![true]
    · obtain ⟨cm, hcm, hcms⟩ :=
        (Synthesis.monotone_const (n := 1) (s := inputs 1) false).exists_circuit
      have hgf : ∀ x : BitString 1, g x = false := fun x ↦ by
        have hx : x = ![x 0] := funext fun i ↦ by rw [Fin.eq_zero i]; rfl
        rw [hx]; cases x 0 <;> assumption
      have hpos : 1 ≤ c.size := by
        by_contra h0
        have hsz : c.size = 0 := by omega
        rcases hw : c.outputs 0 with i | i
        · have ht := congrFun (hc ![true]) 0
          simp only [Circuit.eval, Function.comp_apply, hw, single_apply, hgf] at ht
          have htr : c.program.trace Boolean.interpretation ![true] (.input i) = true := by
            rw [Fin.eq_zero i]; rfl
          exact Bool.false_ne_true (htr.symm.trans ht).symm
        · exact (hsz ▸ i).elim0
      exact ⟨cm, fun x ↦ funext fun j ↦ (congrFun (hcm x) j).trans (hgf x).symm, by omega⟩
    · refine ⟨Circuit.wiring Monotone.signature fun _ ↦ 0, fun x ↦ funext fun j ↦ ?_, by simp⟩
      simp only [Circuit.eval_wiring, Function.comp_apply, single_apply]
      have hx : x = ![x 0] := funext fun i ↦ by rw [Fin.eq_zero i]; rfl
      conv_rhs => rw [hx]
      cases x 0 <;> simp [hb0, hb1]
    · rw [hb0, hb1] at h01; exact absurd h01 not_true_le_false
    · obtain ⟨cm, hcm, hcms⟩ :=
        (Synthesis.monotone_const (n := 1) (s := inputs 1) true).exists_circuit
      have hgt : ∀ x : BitString 1, g x = true := fun x ↦ by
        have hx : x = ![x 0] := funext fun i ↦ by rw [Fin.eq_zero i]; rfl
        rw [hx]; cases x 0 <;> assumption
      have hpos : 1 ≤ c.size := by
        by_contra h0
        have hsz : c.size = 0 := by omega
        rcases hw : c.outputs 0 with i | i
        · have hf := congrFun (hc ![false]) 0
          simp only [Circuit.eval, Function.comp_apply, hw, single_apply, hgt] at hf
          have htr : c.program.trace Boolean.interpretation ![false] (.input i) = false := by
            rw [Fin.eq_zero i]; rfl
          exact Bool.false_ne_true (htr.symm.trans hf)
        · exact (hsz ▸ i).elim0
      exact ⟨cm, fun x ↦ funext fun j ↦ (congrFun (hcm x) j).trans (hgt x).symm, by omega⟩
  · obtain ⟨cm, hcm, hcms⟩ := exists_monotone_toSlice_of_circuit c ℓ
    have hcomp : cm.Computes Monotone.interpretation (single g) := fun x ↦ by
      funext j
      rw [Fin.eq_zero j, hcm x 0, single_apply]
      have hcg : (fun y ↦ c.eval Boolean.interpretation y 0) = g :=
        funext fun y ↦ (congrFun (hc y) 0).trans (single_apply g y 0)
      rw [hcg, hℓ.toSlice_eq]
    have hlog : 1 ≤ Nat.log 2 (n' + 1 + 1) := Nat.log_pos (by omega) (by omega)
    have hquad : 6 * (n' + 1 + 1) ^ 2 + 6 * (n' + 1 + 1) + 2 * 1 + 6 ≤
        12 * (n' + 1 + 1) ^ 2 * 1 := by nlinarith
    have hmul : 12 * (n' + 1 + 1) ^ 2 * 1 ≤
        12 * (n' + 1 + 1) ^ 2 * Nat.log 2 (n' + 1 + 1) := Nat.mul_le_mul_left _ hlog
    exact ⟨cm, hcomp, by omega⟩

end MonotoneSynthesis

end CslibFrontier.BooleanSlice
