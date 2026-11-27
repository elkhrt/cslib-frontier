/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Encoding
public import CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.Circuit
public import CslibFrontier.Computability.Circuit.Arithmetic.Synthesis

import CslibFrontier.Computability.Circuit.Encoding.Evaluation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.GetD

/-!
# Monomial and Partial Coefficient Algorithms for Non-Commutative Circuits

Formalizes bottom-up dynamic programming for computing the coefficient of a non-commutative
monomial in `O(d^3 · size(C))` arithmetic
operations, and constructing a non-commutative arithmetic circuit of size `O(d^2 · size(C))` for
the partial coefficient polynomial `pcoeff f m = ∑_w coeff (m * w) f • w`.

## Main definitions

* `Cslib.Circuits.Arithmetic.subword`: subword `(w.drop i).take (j - i)` in `FreeMonoid`.
* `Cslib.Circuits.Arithmetic.mcoeffProgram`, `mcoeffEval`, `mcoeffCodeStep`, `mcoeffCodeEval`:
  subword DP for `mcoeff`.
* `Cslib.Circuits.Arithmetic.pcoeff`: left-quotient / partial coefficient polynomial on
  `FreeAlgebra`.

## Main results

* `Cslib.Circuits.Arithmetic.mcoeffEval_eq_coeff`: correctness of subword DP.
* `Cslib.Circuits.Arithmetic.mcoeffCodeEval_eq_coeff`: correctness on serialized circuit codes.
* `Cslib.Circuits.Arithmetic.pcoeff_mul`: multiplication recurrence for `pcoeff`.
* `Cslib.Circuits.Arithmetic.exists_circuit_pcoeff`: `O(d^2 · size(C))` circuit for `pcoeff`.
-/

public section

namespace Cslib.Circuits.Arithmetic

open FreeAlgebra Cslib.Circuits

/-- Subword `FreeMonoid.ofList ((w.drop i).take (j - i))`. -/
def subword {X : Type*} (w : List X) (i j : ℕ) : FreeMonoid X :=
  FreeMonoid.ofList ((w.drop i).take (j - i))

theorem subword_eq_one {X : Type*} (w : List X) {i j : ℕ} (h : j ≤ i) :
    subword w i j = 1 := by
  have : j - i = 0 := Nat.sub_eq_zero_of_le h
  simp [subword, this]

theorem subword_succ {X : Type*} (w : List X) {i : ℕ} (hi : i < w.length) :
    subword w i (i + 1) = FreeMonoid.of w[i] := by
  have h1 : (w.drop i).take 1 = [w[i]] := by
    refine List.ext_getElem (by simp; omega) fun k hk1 hk2 => ?_
    have hk0 : k = 0 := by simp at hk2; omega
    subst hk0; simp
  simp only [subword, Nat.add_sub_cancel_left, h1]
  rfl

theorem subword_split {X : Type*} (w : List X) {i r j : ℕ} (hir : i ≤ r) (hrj : r ≤ j) :
    subword w i r * subword w r j = subword w i j := by
  simp only [subword, ← FreeMonoid.ofList_append]
  congr 1
  have h1 : (w.drop i).take (r - i) ++ (w.drop r).take (j - r) =
      (w.drop i).take (r - i) ++ ((w.drop i).drop (r - i)).take (j - r) := by
    rw [List.drop_drop, show i + (r - i) = r by omega]
  rw [h1, ← List.take_add, show r - i + (j - r) = j - i by omega]

/-- Bottom-up subword DP table on a `Program` computing `coeff (subword w i j)`. -/
def mcoeffProgram {K : Type*} [CommSemiring K] {n : ℕ} (w : List (Fin n)) :
    {g : ℕ} → Program (arithSignature K) n g →
      Wire n g → Fin (w.length + 1) → Fin (w.length + 1) → K
  | _, .empty, .input k, i, j =>
    if j.val = i.val + 1 ∧ w.getD i.val k = k ∧
        (if h : i.val < w.length then w[i.val] = k else False) then 1 else 0
  | _, .empty, .gate t, _, _ => Fin.elim0 t
  | _, .gate p line, u, i, j =>
    match u with
    | .input k => mcoeffProgram w p (.input k) i j
    | .gate t =>
      if ht : t.val < _ then
        mcoeffProgram w p (.gate ⟨t.val, ht⟩) i j
      else
        match line with
        | ⟨.const c, _⟩ => if i.val = j.val then c else 0
        | ⟨.add, wires⟩ =>
          mcoeffProgram w p (wires 0) i j + mcoeffProgram w p (wires 1) i j
        | ⟨.mul, wires⟩ =>
          ∑ r : Fin (j.val - i.val + 1),
            mcoeffProgram w p (wires 0) i ⟨i.val + r.val, by omega⟩ *
              mcoeffProgram w p (wires 1) ⟨i.val + r.val, by omega⟩ j

theorem mcoeffProgram_eq_coeff {K : Type*} [CommSemiring K] {n : ℕ} (w : List (Fin n)) :
    ∀ {g : ℕ} (p : Program (arithSignature K) n g) (u : Wire n g)
      (i j : Fin (w.length + 1)), i.val ≤ j.val →
      mcoeffProgram w p u i j =
        coeff (subword w i.val j.val)
          (p.trace (arithInterpretationWith K (algebraMap K (FreeAlgebra K (Fin n)))) (ι K) u) := by
  classical
  intro g p
  induction p with
  | empty =>
    intro u i j hij
    cases u with
    | gate t => exact Fin.elim0 t
    | input k =>
      dsimp only [mcoeffProgram, Program.trace_input]
      by_cases hlen : j.val = i.val + 1
      · have hi : i.val < w.length := by omega
        rw [hlen, subword_succ w hi, FreeAlgebra.coeff_ι, Finsupp.single_apply]
        simp only [FreeMonoid.of_injective.eq_iff, hi, ↓reduceDIte, List.getD_eq_getElem,
          true_and, and_self, eq_comm]
      · have hne : subword w i.val j.val ≠ FreeMonoid.of k := by
          intro h
          have hl := congrArg (fun u : FreeMonoid (Fin n) => u.toList.length) h
          simp only [subword, FreeMonoid.toList_ofList, List.length_take, List.length_drop,
            FreeMonoid.toList_of, List.length_singleton] at hl
          omega
        rw [FreeAlgebra.coeff_ι, Finsupp.single_apply]
        simp [hlen, hne.symm]
  | @gate g p line ih =>
    intro u i j hij
    cases u with
    | input k =>
      exact ih (.input k) i j hij
    | gate t =>
      by_cases ht : t.val < g
      · have hcast : t = (⟨t.val, ht⟩ : Fin g).castSucc := by ext; rfl
        have htr : (p.gate line).trace
            (arithInterpretationWith K (algebraMap K (FreeAlgebra K (Fin n)))) (ι K) (.gate t) =
            p.trace (arithInterpretationWith K (algebraMap K (FreeAlgebra K (Fin n)))) (ι K)
              (.gate ⟨t.val, ht⟩) := by
          conv_lhs => rw [hcast]
          exact Program.eval_gate_castSucc p line _ (ι K) ⟨t.val, ht⟩
        rw [htr]
        simpa [mcoeffProgram, ht] using ih (.gate ⟨t.val, ht⟩) i j hij
      · have hlast : t = Fin.last g := by ext; simp [Fin.val_last]; omega
        have htr : (p.gate line).trace
            (arithInterpretationWith K (algebraMap K (FreeAlgebra K (Fin n)))) (ι K) (.gate t) =
            (arithInterpretationWith K (algebraMap K (FreeAlgebra K (Fin n)))) line.op
              (p.trace (arithInterpretationWith K (algebraMap K (FreeAlgebra K (Fin n)))) (ι K) ∘
                line.wires) := by
          rw [hlast]
          exact Program.eval_gate_last p line _ (ι K)
        rw [htr]
        simp only [mcoeffProgram, ht, ↓reduceDIte]
        rcases line with ⟨op, wires⟩
        dsimp only at *
        cases op with
        | const c =>
          dsimp only [arithInterpretationWith]
          by_cases heq : i.val = j.val
          · simp only [heq, ↓reduceIte]
            rw [subword_eq_one w (by omega), FreeAlgebra.coeff_algebraMap, Finsupp.single_eq_same]
          · simp only [heq, ↓reduceIte]
            rw [FreeAlgebra.coeff_algebraMap, Finsupp.single_apply]
            have hne : (1 : FreeMonoid (Fin n)) ≠ subword w i.val j.val := by
              intro h
              have hl := congrArg (fun u : FreeMonoid (Fin n) => u.toList.length) h
              simp only [subword, FreeMonoid.toList_ofList, List.length_take, List.length_drop,
                FreeMonoid.toList_one, List.length_nil] at hl
              omega
            simp [hne]
        | add =>
          dsimp only [arithInterpretationWith, Function.comp_apply]
          rw [map_add, ih (wires 0) i j hij, ih (wires 1) i j hij]
        | mul =>
          dsimp only [arithInterpretationWith, Function.comp_apply]
          rw [FreeAlgebra.coeff_mul]
          have hlen : (subword w i.val j.val).toList.length = j.val - i.val := by
            simp only [subword, FreeMonoid.toList_ofList, List.length_take, List.length_drop]
            omega
          rw [hlen, ← Fin.sum_univ_eq_sum_range]
          refine Finset.sum_congr rfl fun r _ => ?_
          have htake : FreeMonoid.ofList ((subword w i.val j.val).toList.take r.val) =
              subword w i.val (i.val + r.val) := by
            simp only [subword, FreeMonoid.toList_ofList, List.take_take, Nat.add_sub_cancel_left]
            rw [Nat.min_eq_left (by omega)]
          have hdrop : FreeMonoid.ofList ((subword w i.val j.val).toList.drop r.val) =
              subword w (i.val + r.val) j.val := by
            simp only [subword, FreeMonoid.toList_ofList, List.drop_take, List.drop_drop]
            congr 2; omega
          rw [htake, hdrop, ih (wires 0) i ⟨i.val + r.val, by omega⟩ (by dsimp; omega),
            ih (wires 1) ⟨i.val + r.val, by omega⟩ j (by dsimp; omega)]

/-- Monomial coefficient computed by bottom-up subword DP. -/
def mcoeffEval {K : Type*} [CommSemiring K] {n : ℕ}
    (C : Circuit (arithSignature K) n 1) (w : List (Fin n)) : K :=
  mcoeffProgram w C.program (C.outputs 0) ⟨0, by omega⟩ ⟨w.length, by omega⟩

theorem mcoeffEval_eq_coeff {K : Type*} [CommSemiring K] {n : ℕ}
    (C : Circuit (arithSignature K) n 1) (w : List (Fin n)) :
    mcoeffEval C w = coeff (FreeMonoid.ofList w) (C.noncommPolynomial 0) := by
  rw [Circuit.noncommPolynomial_eq_eval]
  unfold mcoeffEval Circuit.eval
  rw [mcoeffProgram_eq_coeff w C.program (C.outputs 0) ⟨0, by omega⟩ ⟨w.length,
    by omega⟩ (Nat.zero_le _)]
  simp [subword]

/-- One-gate DP step operating directly on serialized gate codes `(op, argWires)`. -/
def mcoeffCodeStep {F : Type*} [CommSemiring F] (w : List ℕ) (tables : List (List (List F)))
    (g : ArithOp F × List ℕ) : List (List (List F)) :=
  let d := w.length
  let tbl : List (List F) :=
    (List.range (d + 1)).map fun i =>
      (List.range (d + 1)).map fun j =>
        if j < i then 0
        else match g.1 with
          | .const c => if i = j then c else 0
          | .add =>
            let t0 := tables.getD (g.2.getD 0 0) []
            let t1 := tables.getD (g.2.getD 1 0) []
            (t0.getD i []).getD j 0 + (t1.getD i []).getD j 0
          | .mul =>
            let t0 := tables.getD (g.2.getD 0 0) []
            let t1 := tables.getD (g.2.getD 1 0) []
            ((List.range (j - i + 1)).map fun r =>
              (t0.getD i []).getD (i + r) 0 * (t1.getD (i + r) []).getD j 0).sum
  tables ++ [tbl]

/-- Executable `mcoeff` on encoded circuit + word `(⟨n, C⟩, w)` over a semiring `F`. -/
def mcoeffCodeEval {F : Type*} [CommSemiring F]
    (x : (Σ n, Circuit (arithSignature F) n 1) × List ℕ) : F :=
  let n := x.1.1
  let C := x.1.2
  let w := x.2
  let d := w.length
  let initTables : List (List (List F)) :=
    (List.range n).map fun k =>
      (List.range (d + 1)).map fun i =>
        (List.range (d + 1)).map fun j =>
          if j = i + 1 ∧ i < d ∧ w.getD i (n + 1) = k then 1 else 0
  let finalTables := C.code.1.foldl (mcoeffCodeStep w) initTables
  let outWire := C.code.2.getD 0 0
  ((finalTables.getD outWire []).getD 0 []).getD d 0

theorem mcoeffCodeEval_eq_coeff.{u} {F : Type u} [CommSemiring F] {n : ℕ}
    (C : Circuit (arithSignature F) n 1) (w : List (Fin n)) :
    mcoeffCodeEval (⟨n, C⟩, w.map Fin.val) =
      coeff (FreeMonoid.ofList w) (C.noncommPolynomial 0) := by
  rw [← mcoeffEval_eq_coeff C w]
  unfold mcoeffCodeEval mcoeffEval
  have hgetD_map_range : ∀ {α : Type u} (m : ℕ) (f : ℕ → α) (idx : Fin m) (d : α),
      ((List.range m).map f).getD idx.val d = f idx.val := fun m f idx d => by
    rw [List.getD_eq_getElem _ _ (by simp [idx.isLt]), List.getElem_map, List.getElem_range]
  have hprog : ∀ {g : ℕ} (p : Program (arithSignature F) n g),
      let initTables : List (List (List F)) :=
        (List.range n).map fun k =>
          (List.range (w.length + 1)).map fun i =>
            (List.range (w.length + 1)).map fun j =>
              if j = i + 1 ∧ i < w.length ∧ (w.map Fin.val).getD i (n + 1) = k then 1 else 0
      let res := p.code.foldl (mcoeffCodeStep (w.map Fin.val)) initTables
      res.length = n + g ∧
      ∀ (u : Wire n g) (i j : Fin (w.length + 1)), i.val ≤ j.val →
        ((res.getD u.toNat []).getD i.val []).getD j.val 0 = mcoeffProgram w p u i j := by
    intro g p
    induction p with
    | empty =>
      dsimp only [Program.code, List.foldl_nil]
      refine ⟨by simp, fun u i j hij => ?_⟩
      cases u with
      | gate t => exact Fin.elim0 t
      | input k =>
        rw [Wire.toNat_input, hgetD_map_range, hgetD_map_range, hgetD_map_range]
        dsimp only [mcoeffProgram]
        by_cases hi : i.val < w.length
        · have hget : (w.map Fin.val).getD i.val (n + 1) = w[i.val].val := by
            rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_map]
          rw [hget, List.getD_eq_getElem _ _ hi]
          simp [hi, Fin.ext_iff]
        · have hne : j.val ≠ i.val + 1 := by omega
          simp [hi, hne]
    | @gate g p line ih =>
      obtain ⟨hlen, hval⟩ := ih
      simp only [Program.code_gate, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set res := p.code.foldl (mcoeffCodeStep (w.map Fin.val)) _
      refine ⟨by simp [mcoeffCodeStep, hlen, Nat.add_assoc], fun u i j hij => ?_⟩
      cases u with
      | input k =>
        have hlt : k.val < res.length := by omega
        rw [mcoeffCodeStep, Wire.toNat_input, List.getD_append _ _ _ _ hlt]
        exact hval (.input k) i j hij
      | gate t =>
        by_cases ht : t.val < g
        · have hlt : (Wire.gate t : Wire n (g + 1)).toNat < res.length := by
            simp [Wire.toNat, hlen]; omega
          rw [mcoeffCodeStep, List.getD_append _ _ _ _ hlt]
          simpa [mcoeffProgram, ht] using hval (.gate ⟨t.val, ht⟩) i j hij
        · have ht_eq : t.val = g := by omega
          have hpos : (Wire.gate t : Wire n (g + 1)).toNat = res.length := by
            simp [Wire.toNat, hlen, ht_eq]
          rw [mcoeffCodeStep, List.getD_append_right _ _ _ _ (by omega), hpos, Nat.sub_self,
            List.getD_cons_zero]
          simp only [List.length_map]
          rw [hgetD_map_range, hgetD_map_range]
          simp only [not_lt.mpr hij, ↓reduceIte, mcoeffProgram, ht, ↓reduceDIte, Line.code_fst]
          rcases line with ⟨op, wires⟩
          dsimp only [Line.code] at *
          cases op with
          | const c => rfl
          | add =>
            have hw0 : (List.ofFn fun a => (wires a).toNat).getD 0 0 = (wires 0).toNat := by
              rw [List.getD_eq_getElem _ _ (by simp [arithSignature, ArithOp.arity]),
                List.getElem_ofFn]; rfl
            have hw1 : (List.ofFn fun a => (wires a).toNat).getD 1 0 = (wires 1).toNat := by
              rw [List.getD_eq_getElem _ _ (by simp [arithSignature, ArithOp.arity]),
                List.getElem_ofFn]; rfl
            rw [hw0, hw1, hval (wires 0) i j hij, hval (wires 1) i j hij]
          | mul =>
            dsimp only
            have hw0 : (List.ofFn fun a => (wires a).toNat).getD 0 0 = (wires 0).toNat := by
              rw [List.getD_eq_getElem _ _ (by simp [arithSignature, ArithOp.arity]),
                List.getElem_ofFn]; rfl
            have hw1 : (List.ofFn fun a => (wires a).toNat).getD 1 0 = (wires 1).toNat := by
              rw [List.getD_eq_getElem _ _ (by simp [arithSignature, ArithOp.arity]),
                List.getElem_ofFn]; rfl
            rw [hw0, hw1, ← List.sum_ofFn]
            congr 1
            refine List.ext_getElem (by simp) fun r hr1 hr2 => ?_
            simp only [List.length_ofFn] at hr2
            simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
            rw [hval (wires 0) i ⟨i.val + r, by omega⟩ (by dsimp; omega),
              hval (wires 1) ⟨i.val + r, by omega⟩ j (by dsimp; omega)]
  have hspec := (hprog C.program).2 (C.outputs 0) ⟨0, by omega⟩ ⟨w.length, by omega⟩ (Nat.zero_le _)
  have hout : C.code.2.getD 0 0 = (C.outputs 0).toNat := by
    simp [Circuit.code]
  have hcode1 : C.code.1 = C.program.code := rfl
  dsimp only
  rw [hcode1, hout, List.length_map]
  exact hspec

/-- Partial coefficient polynomial `pcoeff f m = ∑_w coeff (m * w) f • w`. -/
noncomputable def pcoeff {K : Type*} [CommSemiring K] {X : Type*}
    (f : FreeAlgebra K X) (m : FreeMonoid X) : FreeAlgebra K X :=
  equivMonoidAlgebraFreeMonoid.symm
    (MonoidAlgebra.coeffAddEquiv.symm
      (Finsupp.onFinset
        (@Finset.image _ _ (Classical.decEq _)
          (fun w => @ite _ (m.toList <+: w.toList) (Classical.propDecidable _)
            (FreeMonoid.ofList (w.toList.drop m.toList.length)) 1)
          (equivMonoidAlgebraFreeMonoid f).coeff.support)
        (fun u => coeff (m * u) f)
        (fun u hu => by
          classical
          rw [Finset.mem_image]
          refine ⟨m * u, ?_, ?_⟩
          · rw [Finsupp.mem_support_iff]; simpa [FreeAlgebra.coeff_def] using hu
          · have hpre : m.toList <+: (m * u).toList := ⟨u.toList, rfl⟩
            simp only [hpre, ↓reduceIte]
            change FreeMonoid.ofList ((m.toList ++ u.toList).drop m.toList.length) = u
            rw [List.drop_left']; rfl)))

@[simp]
theorem coeff_pcoeff {K : Type*} [CommSemiring K] {X : Type*}
    (f : FreeAlgebra K X) (m w : FreeMonoid X) :
    coeff w (pcoeff f m) = coeff (m * w) f := by
  simp [pcoeff, FreeAlgebra.coeff_def]

theorem pcoeff_one {K : Type*} [CommSemiring K] {X : Type*} (f : FreeAlgebra K X) :
    pcoeff f 1 = f := by
  apply FreeAlgebra.ext_coeff; intro w; rw [coeff_pcoeff, one_mul]

theorem pcoeff_const {K : Type*} [CommSemiring K] {X : Type*}
    (c : K) (m : FreeMonoid X) :
    pcoeff (algebraMap K (FreeAlgebra K X) c) m =
      @ite _ (m = 1) (Classical.propDecidable _) (algebraMap K (FreeAlgebra K X) c) 0 := by
  apply FreeAlgebra.ext_coeff; intro w
  rw [coeff_pcoeff]
  split_ifs with hm
  · subst hm; rw [one_mul]
  · rw [map_zero, FreeAlgebra.coeff_algebraMap]
    refine Finsupp.single_eq_of_ne' fun h => hm ?_
    have hl := congrArg (fun u : FreeMonoid X => u.toList.length) h
    simp only [FreeMonoid.toList_mul, List.length_append, FreeMonoid.toList_one,
      List.length_nil] at hl
    have hnil : m.toList = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [← FreeMonoid.ofList_toList m, hnil]; rfl

theorem pcoeff_ι {K : Type*} [CommSemiring K] {X : Type*}
    (x : X) (m : FreeMonoid X) :
    pcoeff (ι K x) m =
      @ite _ (m = 1) (Classical.propDecidable _) (ι K x)
        (@ite _ (m = FreeMonoid.of x) (Classical.propDecidable _) 1 0) := by
  apply FreeAlgebra.ext_coeff; intro w
  rw [coeff_pcoeff]
  split_ifs with h1 h2
  · subst h1; rw [one_mul]
  · subst h2
    rw [FreeAlgebra.coeff_ι, FreeAlgebra.coeff_one]
    by_cases hw : w = 1
    · subst hw; simp
    · have hne : FreeMonoid.of x * w ≠ FreeMonoid.of x := by
        intro h; apply hw
        have hl := congrArg (fun u : FreeMonoid X => u.toList.length) h
        simp only [FreeMonoid.toList_mul, List.length_append, FreeMonoid.toList_of,
          List.length_singleton] at hl
        have hnil : w.toList = [] := List.eq_nil_of_length_eq_zero (by omega)
        rw [← FreeMonoid.ofList_toList w, hnil]; rfl
      simp [hw]
  · rw [map_zero, FreeAlgebra.coeff_ι]
    refine Finsupp.single_eq_of_ne' fun h => ?_
    have hl := congrArg (fun u : FreeMonoid X => u.toList.length) h
    simp only [FreeMonoid.toList_mul, List.length_append, FreeMonoid.toList_of,
      List.length_singleton] at hl
    have hm1 : m.toList.length = 1 ∨ m.toList.length = 0 := by omega
    rcases hm1 with hlen1 | hlen0
    · apply h2
      have hw0 : w.toList = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hw1 : w = 1 := by rw [← FreeMonoid.ofList_toList w, hw0]; rfl
      rw [hw1, mul_one] at h; exact h.symm
    · apply h1
      have hnil : m.toList = [] := List.eq_nil_of_length_eq_zero hlen0
      rw [← FreeMonoid.ofList_toList m, hnil]; rfl

theorem pcoeff_add {K : Type*} [CommSemiring K] {X : Type*}
    (g h : FreeAlgebra K X) (m : FreeMonoid X) :
    pcoeff (g + h) m = pcoeff g m + pcoeff h m := by
  apply FreeAlgebra.ext_coeff; intro w; simp [coeff_pcoeff]

/-- Exact multiplication recurrence for `pcoeff`. -/
theorem pcoeff_mul {K : Type*} [CommSemiring K] {X : Type*}
    (g h : FreeAlgebra K X) (m : List X) :
    pcoeff (g * h) (FreeMonoid.ofList m) =
      (∑ i : Fin m.length,
          coeff (FreeMonoid.ofList (m.take i.val)) g •
            pcoeff h (FreeMonoid.ofList (m.drop i.val))) +
        pcoeff g (FreeMonoid.ofList m) * h := by
  apply FreeAlgebra.ext_coeff
  intro w
  rw [coeff_pcoeff, FreeAlgebra.coeff_mul, map_add, map_sum, FreeAlgebra.coeff_mul]
  have hlen : (FreeMonoid.ofList m * w).toList.length + 1 = m.length + (w.toList.length + 1) := by
    simp [FreeMonoid.toList_mul, List.length_append]; omega
  rw [hlen, Finset.sum_range_add]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, coeff_pcoeff, smul_eq_mul]
    simp only [FreeMonoid.toList_mul, List.take_append_of_le_length (le_of_lt i.isLt),
      List.drop_append_of_le_length (le_of_lt i.isLt), FreeMonoid.ofList_append]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_pcoeff]
    simp only [FreeMonoid.toList_mul, List.take_append,
      List.take_of_length_le (Nat.le_add_right m.length i),
      Nat.add_sub_cancel_left, List.drop_append,
      List.drop_eq_nil_of_le (Nat.le_add_right m.length i), List.nil_append,
      FreeMonoid.ofList_append]

/-- Bottom-up `O(d^2 · size(C))` non-commutative arithmetic circuit computing `pcoeff`. -/
theorem exists_circuit_pcoeff {K : Type*} [CommSemiring K] {n : ℕ}
    (C : Circuit (arithSignature K) n 1) (m : List (Fin n)) :
    ∃ D : Circuit (arithSignature K) n 1,
      D.noncommPolynomial 0 = pcoeff (C.noncommPolynomial 0) (FreeMonoid.ofList m) ∧
      D.size ≤ C.size * ((m.length + 1) * (3 * m.length + 2)) + 2 := by
  let I := arithInterpretationWith K (algebraMap K (FreeAlgebra K (Fin n)))
  let Fpcoeff (f : FreeAlgebra K (Fin n)) (i : Fin (m.length + 1)) :
      (Fin n → FreeAlgebra K (Fin n)) → FreeAlgebra K (Fin n) :=
    fun x => FreeAlgebra.lift K x (pcoeff f (FreeMonoid.ofList (m.drop i.val)))
  let progFamily {g : ℕ} (p : Program (arithSignature K) n g) :
      Set ((Fin n → FreeAlgebra K (Fin n)) → FreeAlgebra K (Fin n)) :=
    {fun _ => (0 : FreeAlgebra K (Fin n)), fun _ => (1 : FreeAlgebra K (Fin n))} ∪
      Set.range (fun wi : Wire n g × Fin (m.length + 1) => Fpcoeff (p.trace I (ι K) wi.1) wi.2)
  have hprog : ∀ {g : ℕ} (p : Program (arithSignature K) n g),
      Synthesis I (inputs n) (progFamily p) (g * ((m.length + 1) * (3 * m.length + 2)) + 2) := by
    intro g p
    induction p with
    | empty =>
      have h01 : Synthesis I (inputs n)
          {fun _ => (0 : FreeAlgebra K (Fin n)), fun _ => 1} 2 := by
        have h0 := Synthesis.arith_const (K := K) (R := FreeAlgebra K (Fin n))
          (constant := algebraMap K _) (s := inputs n) (0 : K)
        have h1 := Synthesis.arith_const (K := K) (R := FreeAlgebra K (Fin n))
          (constant := algebraMap K _) (s := inputs n) (1 : K)
        simpa [Set.union_singleton, Set.pair_comm] using (h0.union h1)
      have hbase : Synthesis I (inputs n ∪ {fun _ => 0, fun _ => 1})
          (Set.range fun wi : Wire n 0 × Fin (m.length + 1) =>
            Fpcoeff ((Program.empty : Program _ n 0).trace I (ι K) wi.1) wi.2) 0 := by
        have hcost : ∑ _wi : Wire n 0 × Fin (m.length + 1), 0 = 0 := by simp
        refine (Synthesis.family _ (fun _ => 0) fun ⟨w, i⟩ => ?_).mono Set.Subset.rfl
          Set.Subset.rfl (le_of_eq hcost)
        cases w with
        | gate t => exact Fin.elim0 t
        | input k =>
          dsimp only [Fpcoeff, Program.trace_input]
          rw [pcoeff_ι]
          split_ifs with h1 h2
          · have hf : (fun x : Fin n → FreeAlgebra K (Fin n) => FreeAlgebra.lift K x (ι K k)) =
                fun x => x k := by funext x; exact FreeAlgebra.lift_ι_apply x k
            rw [hf]
            exact Synthesis.of_mem (Set.mem_union_left _ ⟨k, rfl⟩)
          · have hf : (fun x : Fin n → FreeAlgebra K (Fin n) => FreeAlgebra.lift K x 1) =
                fun _ => 1 := by funext x; exact map_one _
            rw [hf]
            exact Synthesis.of_mem (Set.mem_union_right _ (Set.mem_insert_of_mem _ rfl))
          · have hf : (fun x : Fin n → FreeAlgebra K (Fin n) => FreeAlgebra.lift K x 0) =
                fun _ => 0 := by funext x; exact map_zero _
            rw [hf]
            exact Synthesis.of_mem (Set.mem_union_right _ (Set.mem_insert _ _))
      refine (h01.comp hbase).mono Set.Subset.rfl Set.Subset.rfl (by omega)
    | @gate g p line ih =>
      let newF (i : Fin (m.length + 1)) :=
        Fpcoeff ((p.gate line).trace I (ι K) (.gate (Fin.last g))) i
      have hstep : Synthesis I (inputs n ∪ progFamily p) (Set.range newF)
          ((m.length + 1) * (3 * m.length + 2)) := by
        have havail : ∀ (w : Wire n g) (i : Fin (m.length + 1)),
            Fpcoeff (p.trace I (ι K) w) i ∈ inputs n ∪ progFamily p :=
          fun w i => Set.mem_union_right _ (Set.mem_union_right _ ⟨(w, i), rfl⟩)
        have h0_avail : (fun _ : Fin n → FreeAlgebra K (Fin n) => (0 : FreeAlgebra K (Fin n))) ∈
            inputs n ∪ progFamily p :=
          Set.mem_union_right _ (Set.mem_union_left _ (Set.mem_insert _ _))
        have heach : ∀ i : Fin (m.length + 1),
            Synthesis I (inputs n ∪ progFamily p) {newF i} (3 * m.length + 2) := by
          intro i
          dsimp only [newF, Fpcoeff]
          have htr : (p.gate line).trace I (ι K) (.gate (Fin.last g)) =
              I line.op (p.trace I (ι K) ∘ line.wires) :=
            Program.eval_gate_last p line I (ι K)
          rw [htr]
          rcases line with ⟨op, wires⟩
          dsimp only at *
          cases op with
          | const c =>
            dsimp only [I, arithInterpretationWith]
            rw [pcoeff_const]
            split_ifs with h1
            · have hf : (fun x : Fin n → FreeAlgebra K (Fin n) =>
                  FreeAlgebra.lift K x (algebraMap K _ c)) = fun _ => algebraMap K _ c := by
                funext x; exact AlgHom.commutes _ c
              rw [hf]
              exact (Synthesis.arith_const (constant := algebraMap K _) c).mono
                Set.Subset.rfl Set.Subset.rfl (by omega)
            · have hf : (fun x : Fin n → FreeAlgebra K (Fin n) => FreeAlgebra.lift K x 0) =
                  fun _ => 0 := by funext x; exact map_zero _
              rw [hf]
              exact (Synthesis.of_mem h0_avail).mono Set.Subset.rfl Set.Subset.rfl (by omega)
          | add =>
            dsimp only [I, arithInterpretationWith, Function.comp_apply]
            rw [pcoeff_add]
            have hf : (fun x : Fin n → FreeAlgebra K (Fin n) =>
                FreeAlgebra.lift K x (pcoeff (p.trace I (ι K) (wires 0))
                    (FreeMonoid.ofList (m.drop i.val)) +
                  pcoeff (p.trace I (ι K) (wires 1)) (FreeMonoid.ofList (m.drop i.val)))) =
                fun x => Fpcoeff (p.trace I (ι K) (wires 0)) i x +
                  Fpcoeff (p.trace I (ι K) (wires 1)) i x := by
              funext x; exact map_add _ _ _
            rw [hf]
            exact (Synthesis.arith_add (havail _ _) (havail _ _)).mono
              Set.Subset.rfl Set.Subset.rfl (by omega)
          | mul =>
            dsimp only [I, arithInterpretationWith, Function.comp_apply]
            rw [pcoeff_mul]
            let g0 := p.trace I (ι K) (wires 0)
            let h0 := p.trace I (ι K) (wires 1)
            let summand (t : Fin (m.drop i.val).length) :
                (Fin n → FreeAlgebra K (Fin n)) → FreeAlgebra K (Fin n) := fun x =>
              algebraMap K _ (coeff (FreeMonoid.ofList ((m.drop i.val).take t.val)) g0) *
                Fpcoeff h0 ⟨i.val + t.val, by have := t.isLt; simp at this; omega⟩ x
            have hsum_synth : Synthesis I (inputs n ∪ progFamily p)
                {fun x => ∑ t : Fin (m.drop i.val).length, summand t x}
                (3 * (m.drop i.val).length) := by
              have hs := Synthesis.arith_sum Finset.univ summand (fun _ => 2) h0_avail
                (fun t _ =>
                  (Synthesis.arith_const (constant := algebraMap K _)
                    (coeff (FreeMonoid.ofList ((m.drop i.val).take t.val)) g0)).trans
                    (Synthesis.arith_mul (Set.mem_union_right _ rfl)
                      (Set.mem_union_left _ (havail (wires 1)
                        ⟨i.val + t.val, by have := t.isLt; simp at this; omega⟩))))
              refine hs.mono Set.Subset.rfl Set.Subset.rfl ?_
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
              omega
            have hlast_term : Synthesis I (inputs n ∪ progFamily p)
                {fun x => Fpcoeff g0 i x * Fpcoeff h0 ⟨m.length, by omega⟩ x} 1 :=
              Synthesis.arith_mul (havail (wires 0) i)
                (havail (wires 1) ⟨m.length, by omega⟩)
            have hfull : (fun x : Fin n → FreeAlgebra K (Fin n) =>
                FreeAlgebra.lift K x ((∑ t : Fin (m.drop i.val).length,
                  coeff (FreeMonoid.ofList ((m.drop i.val).take t.val)) g0 •
                    pcoeff h0 (FreeMonoid.ofList ((m.drop i.val).drop t.val))) +
                  pcoeff g0 (FreeMonoid.ofList (m.drop i.val)) * h0)) =
                fun x => (∑ t : Fin (m.drop i.val).length, summand t x) +
                  Fpcoeff g0 i x * Fpcoeff h0 ⟨m.length, by omega⟩ x := by
              funext x
              rw [map_add, map_sum, map_mul]
              congr 1
              · refine Finset.sum_congr rfl fun t _ => ?_
                rw [map_smul, Algebra.smul_def]
                simp [summand, Fpcoeff, List.drop_drop]
              · simp [Fpcoeff, pcoeff_one]
            change Synthesis I (inputs n ∪ progFamily p)
              {fun x => FreeAlgebra.lift K x ((∑ t : Fin (m.drop i.val).length,
                coeff (FreeMonoid.ofList ((m.drop i.val).take t.val)) g0 •
                  pcoeff h0 (FreeMonoid.ofList ((m.drop i.val).drop t.val))) +
                pcoeff g0 (FreeMonoid.ofList (m.drop i.val)) * h0)} (3 * m.length + 2)
            rw [hfull]
            refine ((hsum_synth.union hlast_term).trans
              (Synthesis.arith_add (Set.mem_union_right _ (Set.mem_union_left _ rfl))
                (Set.mem_union_right _ (Set.mem_union_right _ rfl)))).mono
              Set.Subset.rfl Set.Subset.rfl ?_
            simp only [List.length_drop]; omega
        have hcost : ∑ _i : Fin (m.length + 1), (3 * m.length + 2) =
            (m.length + 1) * (3 * m.length + 2) := by simp
        exact (Synthesis.family newF (fun _ => 3 * m.length + 2) heach).mono
          Set.Subset.rfl Set.Subset.rfl (le_of_eq hcost)
      refine (ih.comp hstep).mono Set.Subset.rfl ?_ (by ring_nf; omega)
      rintro f (hf | ⟨⟨w, i⟩, rfl⟩)
      · exact Or.inl (Or.inl hf)
      · cases w with
        | input k =>
          refine Or.inl (Or.inr ⟨(.input k, i), ?_⟩)
          simp [Fpcoeff]
        | gate t =>
          refine Fin.lastCases ?_ (fun t' => ?_) t
          · exact Or.inr ⟨i, rfl⟩
          · refine Or.inl (Or.inr ⟨(.gate t', i), ?_⟩)
            simp [Fpcoeff]
  have hmem : Fpcoeff (C.noncommPolynomial 0) ⟨0, Nat.zero_lt_succ _⟩ ∈ progFamily C.program := by
    rw [Circuit.noncommPolynomial_eq_eval]
    exact Set.mem_union_right _ ⟨(C.outputs 0, ⟨0, Nat.zero_lt_succ _⟩), rfl⟩
  obtain ⟨D, hD, hDsize⟩ :=
    ((hprog C.program).mono Set.Subset.rfl
      (Set.singleton_subset_iff.mpr hmem) le_rfl).exists_circuit
  refine ⟨D, ?_, hDsize⟩
  have hDeval := congrFun (hD (ι K)) 0
  rw [Circuit.noncommPolynomial_eq_eval]
  change D.eval I (ι K) 0 =
    Fpcoeff (C.noncommPolynomial 0) ⟨0, Nat.zero_lt_succ _⟩ (ι K) at hDeval
  rw [hDeval]
  dsimp only [Fpcoeff]
  have hid : FreeAlgebra.lift K (ι K) = AlgHom.id K (FreeAlgebra K (Fin n)) :=
    FreeAlgebra.hom_ext (funext fun i => FreeAlgebra.lift_ι_apply _ i)
  rw [AlgHom.ext_iff.mp hid, List.drop_zero]
  rfl

end Cslib.Circuits.Arithmetic
