module
/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

public import CslibFrontier.Foundations.Combinatorics.Expander.ParvareshVardyCode
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.PolyTime.BinaryField
import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.FieldTheory.Finite.BinaryFieldTable
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Executable Parvaresh–Vardy Polynomial Arithmetic over Explicit Binary Fields

This module implements bit-level arithmetic in the quotient ring
`𝔽_{2^t}[X] / (X ^ (2 * 3 ^ k) + X ^ (3 ^ k) + 1)` over `Cslib.BinaryField t`, proves exact
algebraic agreement with the Parvaresh–Vardy neighbor map `CslibFrontier.ParvareshVardy.pvNeighbor`,
and
certifies polynomial-time computability on multi-tape Turing machines
(`Turing.MultiTapeTM.ComputableInPolyTime`) as well as polynomial-size De Morgan neighbor-list
circuits, under standard Lean constraints.

## Main definitions

* `CslibFrontier.ParvareshVardy.encPvParam`: multi-tape Turing-machine encoding for parameters
  `(searchBound, t, s, m, hBits, yBits)` of the Parvaresh–Vardy neighbor computation.
* `CslibFrontier.ParvareshVardy.pvNeighborBits`: executable bit-level computation of the
  `(m + 1) * t`
  little-endian bits of `(y, f(y), (f^h mod E)(y), …, (f^(h^(m-1)) mod E)(y))`.
* `CslibFrontier.ParvareshVardy.pvNeighborNat`: natural-number neighbor function on `Fin M` along
  `Fin (2 ^ t)` into `Fin ((2 ^ t) ^ (m + 1))`.

## Main results

* `CslibFrontier.ParvareshVardy.computableInPolyTime_pvNeighborBits`: `pvNeighborBits` is computable
  in
  polynomial time with respect to `encPair encBits encPvParam` and `encBits`.
* `CslibFrontier.ParvareshVardy.isBipartiteExpander_pvNeighborNat`: when `Nat.Coprime t 6`, `h ≥ 2`,
  `m ≥ 1`, `Nat.clog 2 M ≤ 2 * 3 ^ k * t`, `r ≤ h ^ m`, and
  `m * (h - 1) * (2 * 3 ^ k - 1) < 2 ^ t`, `pvNeighborNat` defines an `(r, 2 ^ t, (1 - ε) * 2 ^ t)`
  bipartite expander on `Fin M` and `Fin ((2 ^ t) ^ (m + 1))`.
* `CslibFrontier.ParvareshVardy.exists_circuit_pvNeighborNat`: `pvNeighborNat` admits De Morgan
  neighbor-list circuits of size at most `C₀ * (2 ^ t + Nat.clog 2 M + 2) ^ K₀` for absolute
  constants `C₀ K₀ : ℕ`.
-/

public section

namespace CslibFrontier.ParvareshVardy

open Polynomial Finset
open CslibFrontier.ProofComplexity
open Cslib Cslib.BinaryField Turing.MultiTapeTM ComputableInPolyTime

/-! ### Executable Quotient-Ring Arithmetic over `Cslib.BinaryField` -/

private def fZero (t : ℕ) : List Bool := List.replicate t false

private def fOne (t : ℕ) : List Bool := (true :: List.replicate (t - 1) false).take t

private def fAdd (t : ℕ) (a b : List Bool) : List Bool :=
  (List.range t).map fun i ↦ a.getD i false ^^ b.getD i false

private def pZero (t s : ℕ) : List (List Bool) := List.replicate (2 * s) (fZero t)

private def pOne (t s : ℕ) : List (List Bool) :=
  (List.range (2 * s)).map fun i ↦ if i == 0 then fOne t else fZero t

private def pAdd (t s : ℕ) (P Q : List (List Bool)) : List (List Bool) :=
  (List.range (2 * s)).map fun i ↦ fAdd t (P.getD i []) (Q.getD i [])

private def pScale (tab : List (List (List Bool))) (s : ℕ) (c : List Bool)
    (P : List (List Bool)) : List (List Bool) :=
  (List.range (2 * s)).map fun i ↦ fieldMul tab c (P.getD i [])

private def pMulXMod (t s : ℕ) (P : List (List Bool)) : List (List Bool) :=
  let lead := fAdd t (P.getD (2 * s - 1) []) []
  (List.range (2 * s)).map fun i ↦
    if i == 0 then lead
    else if i == s then fAdd t (P.getD (i - 1) []) lead
    else fAdd t (P.getD (i - 1) []) []

private def pMulStep (t s : ℕ) (tab : List (List (List Bool)))
    (st : List (List Bool) × List (List Bool)) (c : List Bool) :
    List (List Bool) × List (List Bool) :=
  (pMulXMod t s st.1, pAdd t s st.2 (pScale tab s c st.1))

private def pMulMod (t s : ℕ) (tab : List (List (List Bool)))
    (P Q : List (List Bool)) : List (List Bool) :=
  (Q.foldl (pMulStep t s tab) (P, pZero t s)).2

private def pPowStep (t s : ℕ) (tab : List (List (List Bool)))
    (st : List (List Bool) × List (List Bool)) (b : Bool) :
    List (List Bool) × List (List Bool) :=
  (pMulMod t s tab st.1 st.1, if b then pMulMod t s tab st.2 st.1 else st.2)

private def pPowMod (t s : ℕ) (tab : List (List (List Bool)))
    (P : List (List Bool)) (hBits : List Bool) : List (List Bool) :=
  (hBits.foldl (pPowStep t s tab) (P, pOne t s)).2

private def pEvalStep (t : ℕ) (tab : List (List (List Bool))) (y : List Bool)
    (st : List Bool × List Bool) (c : List Bool) : List Bool × List Bool :=
  (fieldMul tab st.1 y, fAdd t st.2 (fieldMul tab c st.1))

private def pEval (t : ℕ) (tab : List (List (List Bool)))
    (P : List (List Bool)) (y : List Bool) : List Bool :=
  (P.foldl (pEvalStep t tab y) (fOne t, fZero t)).2

private def decodePoly (t s : ℕ) (uBits : List Bool) : List (List Bool) :=
  (List.range (2 * s)).map fun i ↦ (List.range t).map fun j ↦ uBits.getD (i * t + j) false

private def pvIterStep (t s : ℕ) (tab : List (List (List Bool)))
    (hBits y : List Bool) (st : List (List Bool) × List Bool) (_ : ℕ) :
    List (List Bool) × List Bool :=
  (pPowMod t s tab st.1 hBits, st.2 ++ pEval t tab st.1 y)

/-- Framed encoding of Parvaresh–Vardy runtime parameters
`(searchBound, t, s, m, hBits, yBits)`, with `(searchBound, t, s, m)` in unary and
`(hBits, yBits)` as raw bit strings. -/
abbrev encPvParam : (ℕ × ℕ × ℕ × ℕ × List Bool × List Bool) ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary
    (encPair encUnary (encPair encBits encBits))))

/-- Executable computation of the `(m + 1) * t` little-endian output bits of the Parvaresh–Vardy
neighbor of `uBits` at evaluation point `yBits` over `BinaryField t` modulo
`X ^ (2 * s) + X ^ s + 1`, using irreducible-polynomial search bound `searchBound` and exponent
bits `hBits`. -/
def pvNeighborBits (uBits : List Bool) (searchBound t s m : ℕ)
    (hBits yBits : List Bool) : List Bool :=
  let tab := powerMulTable (leastIrreducibleCode searchBound t).bits
  let yPad := fAdd t yBits []
  ((List.range m).foldl (pvIterStep t s tab hBits yPad) (decodePoly t s uBits, yPad)).2

/-- Natural-number neighbor function mapping left vertex `u` (at bit width `wU`) and edge label `j`
to the Parvaresh–Vardy right neighbor in `Fin ((2 ^ t) ^ (m + 1))`. -/
@[expose] def pvNeighborNat (wU t k m h u j : ℕ) : ℕ :=
  lsbValue (pvNeighborBits (BitString.lowBits wU u) (2 ^ (t + 1)) t (3 ^ k) m h.bits
    (BitString.lowBits t j))

/-! #### Word-Length Invariants -/

private theorem wellSized_pZero (t s : ℕ) :
    (pZero t s).length = 2 * s ∧ ∀ c ∈ pZero t s, c.length ≤ t :=
  ⟨by simp [pZero], fun c hc ↦ by rw [List.eq_of_mem_replicate hc]; simp [fZero]⟩

private theorem wellSized_pOne (t s : ℕ) :
    (pOne t s).length = 2 * s ∧ ∀ c ∈ pOne t s, c.length ≤ t := by
  refine ⟨by simp [pOne], fun c hc ↦ ?_⟩
  obtain ⟨_, -, rfl⟩ := List.mem_map.1 hc
  split_ifs
  · exact List.length_take_le _ _
  · simp [fZero]

private theorem wellSized_pAdd (t s : ℕ) (P Q : List (List Bool)) :
    (pAdd t s P Q).length = 2 * s ∧ ∀ c ∈ pAdd t s P Q, c.length ≤ t := by
  refine ⟨by simp [pAdd], fun c hc ↦ ?_⟩
  obtain ⟨_, -, rfl⟩ := List.mem_map.1 hc
  simp [fAdd]

private theorem wellSized_pMulXMod (t s : ℕ) (P : List (List Bool)) :
    (pMulXMod t s P).length = 2 * s ∧ ∀ c ∈ pMulXMod t s P, c.length ≤ t := by
  refine ⟨by simp [pMulXMod], fun c hc ↦ ?_⟩
  obtain ⟨_, -, rfl⟩ := List.mem_map.1 hc
  split_ifs <;> simp [fAdd]

private theorem wellSized_decodePoly (t s : ℕ) (uBits : List Bool) :
    (decodePoly t s uBits).length = 2 * s ∧ ∀ c ∈ decodePoly t s uBits, c.length ≤ t := by
  refine ⟨by simp [decodePoly], fun c hc ↦ ?_⟩
  obtain ⟨_, -, rfl⟩ := List.mem_map.1 hc
  simp

private theorem wellSized_pMulMod (t s : ℕ) (tab : List (List (List Bool)))
    (P Q : List (List Bool)) :
    (pMulMod t s tab P Q).length = 2 * s ∧ ∀ c ∈ pMulMod t s tab P Q, c.length ≤ t := by
  dsimp [pMulMod]
  induction Q using List.reverseRecOn with
  | nil => exact wellSized_pZero t s
  | append_singleton _ _ _ =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, pMulStep]
    exact wellSized_pAdd t s _ _

private theorem wellSized_pPowMod (t s : ℕ) (tab : List (List (List Bool)))
    (P : List (List Bool)) (hBits : List Bool) :
    (pPowMod t s tab P hBits).length = 2 * s ∧ ∀ c ∈ pPowMod t s tab P hBits, c.length ≤ t := by
  dsimp [pPowMod]
  induction hBits using List.reverseRecOn with
  | nil => exact wellSized_pOne t s
  | append_singleton _ b ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, pPowStep]
    cases b
    · exact ih
    · exact wellSized_pMulMod t s tab _ _

private theorem length_pEval (t : ℕ) (tab : List (List (List Bool)))
    (P : List (List Bool)) (y : List Bool) : (pEval t tab P y).length = t := by
  dsimp [pEval]
  induction P using List.reverseRecOn with
  | nil => simp [fZero]
  | append_singleton _ _ _ => simp [pEvalStep, fAdd]

/-- `pvNeighborBits` always produces a bit string of exact length `(m + 1) * t`. -/
@[simp] theorem length_pvNeighborBits (uBits : List Bool) (searchBound t s m : ℕ)
    (hBits yBits : List Bool) :
    (pvNeighborBits uBits searchBound t s m hBits yBits).length = (m + 1) * t := by
  dsimp only [pvNeighborBits]
  induction m with
  | zero => simp [fAdd]
  | succ r ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    dsimp only [pvIterStep]
    rw [List.length_append, ih, length_pEval]; ring

/-! #### Algebraic Soundness -/

private noncomputable def toF {t : ℕ} (ht : t ≠ 0) (a : List Bool) : BinaryField t :=
  fieldOfBits (BinaryField.basis ht) a

private noncomputable def toPoly {t : ℕ} (ht : t ≠ 0) (P : List (List Bool)) :
    (BinaryField t)[X] :=
  ∑ i ∈ Finset.range P.length, C (toF ht (P.getD i [])) * X ^ i

private theorem toF_ext {t : ℕ} (ht : t ≠ 0) {a b : List Bool}
    (h : ∀ i < t, a.getD i false = b.getD i false) : toF ht a = toF ht b :=
  (BinaryField.basis ht).ext_elem fun u ↦ by
    rw [toF, toF, repr_fieldOfBits, repr_fieldOfBits, h u.val u.isLt]

private theorem toF_fZero {t : ℕ} (ht : t ≠ 0) : toF ht (fZero t) = 0 := by
  rw [← (fieldOfBits_nil (BinaryField.basis ht) : toF ht [] = 0)]
  exact toF_ext ht fun i hi ↦ by simp [fZero, List.getD_eq_getElem?_getD, hi]

private theorem toF_fOne {t : ℕ} (ht : t ≠ 0) : toF ht (fOne t) = 1 := by
  rw [← (fieldOfBits_one ht : toF ht [true] = 1)]
  refine toF_ext ht fun i hi ↦ ?_
  rcases t with _ | t'
  · exact absurd rfl ht
  · cases i with
    | zero => simp [fOne]
    | succ j => simp [fOne, List.getD_eq_getElem?_getD, hi]

private theorem toF_fAdd {t : ℕ} (ht : t ≠ 0) (a b : List Bool) :
    toF ht (fAdd t a b) = toF ht a + toF ht b := by
  have heq : fAdd t a b = BitString.listXor t [a, b] :=
    List.ext_getElem (by simp [fAdd]) fun i h₁ h₂ ↦ by
      have hi : i < t := by simpa [fAdd] using h₁
      have hgd := BitString.getD_listXor_pair t a b i hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some] at hgd
      simpa [fAdd] using hgd.symm
  rw [toF, heq, fieldOfBits_listXor]
  simp [toF]

private theorem toF_fAdd_nil {t : ℕ} (ht : t ≠ 0) (a : List Bool) :
    toF ht (fAdd t a []) = toF ht a := by
  have h0 : toF ht [] = 0 := fieldOfBits_nil _
  rw [toF_fAdd, h0, add_zero]

private theorem natDegree_toPoly_lt {t : ℕ} (ht : t ≠ 0) {n : ℕ} (hn : 0 < n)
    {P : List (List Bool)} (hlen : P.length = n) :
    (toPoly ht P).natDegree < n := by
  rw [toPoly, hlen]
  refine (natDegree_sum_le _ _).trans_lt ?_
  rw [Finset.fold_max_lt]
  exact ⟨hn, fun i hi ↦ (natDegree_C_mul_X_pow_le _ _).trans_lt (Finset.mem_range.1 hi)⟩

private theorem modByMonic_self_lt {F : Type*} [Field F] {E p : F[X]}
    (hE : E.Monic) (hp : p.natDegree < E.natDegree) : p %ₘ E = p := by
  rw [Polynomial.modByMonic_eq_self_iff hE, Polynomial.degree_eq_natDegree hE.ne_zero]
  exact Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.2 hp)

private theorem modByMonic_mul_right {F : Type*} [Field F] {E : F[X]} (hE : E.Monic)
    (a b : F[X]) : (a * (b %ₘ E)) %ₘ E = (a * b) %ₘ E := by
  apply Eq.symm
  apply Polynomial.modByMonic_eq_of_dvd_sub hE
  have h1 : E ∣ b - b %ₘ E :=
    ⟨b /ₘ E, (eq_sub_of_add_eq' (Polynomial.modByMonic_add_div b E)).symm⟩
  rw [← mul_sub]
  exact dvd_mul_of_dvd_right h1 a

private theorem toPoly_pZero {t : ℕ} (ht : t ≠ 0) (s : ℕ) : toPoly ht (pZero t s) = 0 := by
  simp only [toPoly, pZero, List.length_replicate]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  have hi' := Finset.mem_range.1 hi
  simp [List.getD_eq_getElem?_getD, hi', toF_fZero ht]

private theorem toPoly_pOne {t : ℕ} (ht : t ≠ 0) {s : ℕ} (hs : 1 ≤ s) :
    toPoly ht (pOne t s) = 1 := by
  rw [toPoly, (wellSized_pOne t s).1, Finset.sum_eq_single 0]
  · rw [pOne, List.getD_map_range _ [] (show 0 < 2 * s by omega)]
    simp [toF_fOne ht]
  · intro i hi hi0
    rw [pOne, List.getD_map_range _ [] (Finset.mem_range.1 hi)]
    simp [hi0, toF_fZero ht]
  · intro h0; exact absurd (Finset.mem_range.2 (by omega)) h0

private theorem toPoly_pAdd {t : ℕ} (ht : t ≠ 0) {s : ℕ} {P Q : List (List Bool)}
    (hP : P.length = 2 * s) (hQ : Q.length = 2 * s) :
    toPoly ht (pAdd t s P Q) = toPoly ht P + toPoly ht Q := by
  simp only [toPoly, pAdd, List.length_map, List.length_range, hP, hQ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [List.getD_map_range _ [] (Finset.mem_range.1 hi), toF_fAdd ht, map_add, add_mul]

private theorem toPoly_pScale {t : ℕ} (ht : t ≠ 0) {tab : List (List (List Bool))}
    (htab : IsMulTable (BinaryField.basis ht) tab) {s : ℕ} (c : List Bool)
    {P : List (List Bool)} (hP : P.length = 2 * s) :
    toPoly ht (pScale tab s c P) = C (toF ht c) * toPoly ht P := by
  simp only [toPoly, pScale, List.length_map, List.length_range, hP, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [List.getD_map_range _ [] (Finset.mem_range.1 hi)]
  have hm : toF ht (fieldMul tab c (P.getD i [])) = toF ht c * toF ht (P.getD i []) :=
    fieldOfBits_fieldMul htab c (P.getD i [])
  rw [hm, map_mul, mul_assoc]

private theorem toPoly_pMulXMod {t k : ℕ} (ht : t ≠ 0) {P : List (List Bool)}
    (hP : P.length = 2 * 3 ^ k) :
    toPoly ht (pMulXMod t (3 ^ k) P) = (X * toPoly ht P) %ₘ trinom (BinaryField t) k := by
  set s := 3 ^ k
  set E := trinom (BinaryField t) k
  have hs : 1 ≤ s := Nat.one_le_pow _ _ (by decide)
  have hE : E.Monic := monic_trinom _ k
  have hlen : (pMulXMod t s P).length = 2 * s := (wellSized_pMulXMod t s P).1
  have hself : toPoly ht (pMulXMod t s P) %ₘ E = toPoly ht (pMulXMod t s P) :=
    modByMonic_self_lt hE (by rw [natDegree_trinom]; exact natDegree_toPoly_lt ht (by omega) hlen)
  rw [← hself]
  apply Polynomial.modByMonic_eq_of_dvd_sub hE
  refine ⟨C (toF ht (P.getD (2 * s - 1) [])), ?_⟩
  rw [CharTwo.sub_eq_add]
  have h2s : (2 * s - 1) + 1 = 2 * s := by omega
  have hsplitP : X * toPoly ht P =
      (∑ j ∈ Finset.range (2 * s - 1), C (toF ht (P.getD j [])) * X ^ (j + 1)) +
        C (toF ht (P.getD (2 * s - 1) [])) * X ^ (2 * s) := by
    rw [toPoly, hP, ← h2s, Finset.sum_range_succ, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ ↦ by ring
    · rw [mul_comm X, mul_assoc, ← pow_succ, h2s]
  have hsplitM : toPoly ht (pMulXMod t s P) =
      C (toF ht (P.getD (2 * s - 1) [])) +
        (∑ j ∈ Finset.range (2 * s - 1), C (toF ht (P.getD j [])) * X ^ (j + 1)) +
        C (toF ht (P.getD (2 * s - 1) [])) * X ^ s := by
    rw [toPoly, hlen, ← h2s, Finset.sum_range_succ']
    have h0 : toF ht ((pMulXMod t s P).getD 0 []) = toF ht (P.getD (2 * s - 1) []) := by
      rw [pMulXMod, List.getD_map_range _ [] (show 0 < 2 * s by omega)]
      simp only [beq_self_eq_true, ↓reduceIte, toF_fAdd_nil ht]
    have hsucc : ∑ j ∈ Finset.range (2 * s - 1),
          C (toF ht ((pMulXMod t s P).getD (j + 1) [])) * X ^ (j + 1) =
        (∑ j ∈ Finset.range (2 * s - 1), C (toF ht (P.getD j [])) * X ^ (j + 1)) +
          ∑ j ∈ Finset.range (2 * s - 1),
            if j + 1 = s then C (toF ht (P.getD (2 * s - 1) [])) * X ^ (j + 1) else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hj' : j + 1 < 2 * s := by have := Finset.mem_range.1 hj; omega
      rw [pMulXMod, List.getD_map_range _ [] hj']
      simp only [beq_iff_eq, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      by_cases hjs : j + 1 = s
      · simp only [hjs, ↓reduceIte]
        rw [toF_fAdd ht, toF_fAdd_nil ht, map_add, add_mul]
      · simp only [hjs, ↓reduceIte, toF_fAdd_nil ht, add_zero]
    have hsingle : (∑ j ∈ Finset.range (2 * s - 1),
          if j + 1 = s then C (toF ht (P.getD (2 * s - 1) [])) * X ^ (j + 1) else 0) =
        C (toF ht (P.getD (2 * s - 1) [])) * X ^ s := by
      rw [Finset.sum_eq_single (s - 1)]
      · have hs1 : s - 1 + 1 = s := by omega
        simp [hs1]
      · intro j _ hne
        have : j + 1 ≠ s := by omega
        simp [this]
      · intro hmem; exact absurd (Finset.mem_range.2 (by omega)) hmem
    rw [h0, pow_zero, mul_one, hsucc, hsingle, add_comm _ (C (toF ht (P.getD (2 * s - 1) []))),
      ← add_assoc, h2s]
  rw [hsplitP, hsplitM]
  set A := ∑ j ∈ Finset.range (2 * s - 1), C (toF ht (P.getD j [])) * X ^ (j + 1)
  set c := C (toF ht (P.getD (2 * s - 1) []))
  change (c + A + c * X ^ s) + (A + c * X ^ (2 * s)) = (X ^ (2 * s) + X ^ s + 1) * c
  calc (c + A + c * X ^ s) + (A + c * X ^ (2 * s))
      = (A + A) + (X ^ (2 * s) + X ^ s + 1) * c := by ring
    _ = (X ^ (2 * s) + X ^ s + 1) * c := by rw [CharTwo.add_self_eq_zero, zero_add]

private theorem toPoly_append_singleton {t : ℕ} (ht : t ≠ 0) (l : List (List Bool))
    (c : List Bool) :
    toPoly ht (l ++ [c]) = toPoly ht l + C (toF ht c) * X ^ l.length := by
  simp only [toPoly, List.length_append, List.length_singleton, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (Finset.mem_range.1 hi)]
  · simp [List.getD_eq_getElem?_getD]

private theorem toPoly_pMulMod {t k : ℕ} (ht : t ≠ 0) {tab : List (List (List Bool))}
    (htab : IsMulTable (BinaryField.basis ht) tab) {P : List (List Bool)}
    (hP : P.length = 2 * 3 ^ k) (Q : List (List Bool)) :
    toPoly ht (pMulMod t (3 ^ k) tab P Q) =
      (toPoly ht Q * toPoly ht P) %ₘ trinom (BinaryField t) k := by
  set s := 3 ^ k
  set E := trinom (BinaryField t) k
  have hE : E.Monic := monic_trinom _ k
  have hEdeg : E.natDegree = 2 * s := natDegree_trinom _ k
  have hs_pos : 0 < 2 * s := by positivity
  suffices hinv : ∀ l : List (List Bool),
      let st := l.foldl (pMulStep t s tab) (P, pZero t s)
      st.1.length = 2 * s ∧ st.2.length = 2 * s ∧
        toPoly ht st.1 = (X ^ l.length * toPoly ht P) %ₘ E ∧
        toPoly ht st.2 = (toPoly ht l * toPoly ht P) %ₘ E from (hinv Q).2.2.2
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨hP, (wellSized_pZero t s).1, ?_, ?_⟩
    · simp only [List.foldl_nil, List.length_nil, pow_zero, one_mul]
      exact (modByMonic_self_lt hE (hEdeg ▸ natDegree_toPoly_lt ht hs_pos hP)).symm
    · simp only [List.foldl_nil, toPoly_pZero ht]
      have h0 : toPoly ht ([] : List (List Bool)) = 0 := by simp [toPoly]
      rw [h0, zero_mul, Polynomial.zero_modByMonic]
  | append_singleton l c ih =>
    obtain ⟨h1l, h2l, h1v, h2v⟩ := ih
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, pMulStep]
    set st := l.foldl (pMulStep t s tab) (P, pZero t s)
    have hsc_len : (pScale tab s c st.1).length = 2 * s := by simp [pScale]
    refine ⟨(wellSized_pMulXMod t s st.1).1, (wellSized_pAdd t s _ _).1, ?_, ?_⟩
    · rw [toPoly_pMulXMod ht h1l, h1v, modByMonic_mul_right hE, List.length_append,
        List.length_singleton, pow_succ', mul_assoc]
    · rw [toPoly_pAdd ht h2l hsc_len, h2v, toPoly_pScale ht htab c h1l]
      have hsc_mod : C (toF ht c) * toPoly ht st.1 =
          (C (toF ht c) * X ^ l.length * toPoly ht P) %ₘ E := by
        have hdeg : (C (toF ht c) * toPoly ht st.1).natDegree < E.natDegree := by
          rw [← toPoly_pScale ht htab c h1l, hEdeg]
          exact natDegree_toPoly_lt ht hs_pos hsc_len
        rw [← modByMonic_self_lt hE hdeg, h1v, modByMonic_mul_right hE, mul_assoc]
      rw [hsc_mod, ← Polynomial.add_modByMonic, toPoly_append_singleton ht, add_mul]

private theorem lsbValue_append_singleton (l : List Bool) (b : Bool) :
    lsbValue (l ++ [b]) = lsbValue l + b.toNat * 2 ^ l.length := by
  induction l with
  | nil => cases b <;> simp
  | cons a l ih =>
    simp only [List.cons_append, lsbValue_cons, ih, List.length_cons, pow_succ]
    ring

private theorem toPoly_pPowMod {t k : ℕ} (ht : t ≠ 0) {tab : List (List (List Bool))}
    (htab : IsMulTable (BinaryField.basis ht) tab) {P : List (List Bool)}
    (hP : P.length = 2 * 3 ^ k) (hBits : List Bool) :
    toPoly ht (pPowMod t (3 ^ k) tab P hBits) =
      (toPoly ht P ^ lsbValue hBits) %ₘ trinom (BinaryField t) k := by
  set s := 3 ^ k
  set E := trinom (BinaryField t) k
  have hE : E.Monic := monic_trinom _ k
  have hEdeg : E.natDegree = 2 * s := natDegree_trinom _ k
  have hs1 : 1 ≤ s := Nat.one_le_pow _ _ (by decide)
  have hs_pos : 0 < 2 * s := by positivity
  have hmod_mul : ∀ a b : (BinaryField t)[X], ((a %ₘ E) * (b %ₘ E)) %ₘ E = (a * b) %ₘ E :=
    fun a b ↦ by rw [modByMonic_mul_right hE, mul_comm, modByMonic_mul_right hE, mul_comm]
  suffices hinv : ∀ l : List Bool,
      let st := l.foldl (pPowStep t s tab) (P, pOne t s)
      st.1.length = 2 * s ∧ st.2.length = 2 * s ∧
        toPoly ht st.1 = (toPoly ht P ^ (2 ^ l.length)) %ₘ E ∧
        toPoly ht st.2 = (toPoly ht P ^ lsbValue l) %ₘ E from (hinv hBits).2.2.2
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨hP, (wellSized_pOne t s).1, ?_, ?_⟩
    · simp only [List.foldl_nil, List.length_nil, pow_zero, pow_one]
      exact (modByMonic_self_lt hE (hEdeg ▸ natDegree_toPoly_lt ht hs_pos hP)).symm
    · simp only [List.foldl_nil, lsbValue_nil, pow_zero, toPoly_pOne ht hs1]
      exact (modByMonic_self_lt hE (by rw [hEdeg]; simp; omega)).symm
  | append_singleton l b ih =>
    obtain ⟨h1l, h2l, h1v, h2v⟩ := ih
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, pPowStep]
    set st := l.foldl (pPowStep t s tab) (P, pOne t s)
    refine ⟨(wellSized_pMulMod t s tab st.1 st.1).1, ?_, ?_, ?_⟩
    · cases b
      · exact h2l
      · exact (wellSized_pMulMod t s tab st.2 st.1).1
    · rw [toPoly_pMulMod ht htab h1l st.1, h1v, hmod_mul, ← pow_add, List.length_append,
        List.length_singleton, pow_succ, mul_two]
    · cases b
      · simpa [lsbValue_append_singleton] using h2v
      · simp only [↓reduceIte, lsbValue_append_singleton, Bool.toNat_true, one_mul]
        rw [toPoly_pMulMod ht htab h2l st.1, h1v, h2v, hmod_mul, ← pow_add, add_comm]

private theorem toF_pEval {t : ℕ} (ht : t ≠ 0) {tab : List (List (List Bool))}
    (htab : IsMulTable (BinaryField.basis ht) tab) (P : List (List Bool)) (y : List Bool) :
    toF ht (pEval t tab P y) = (toPoly ht P).eval (toF ht y) := by
  suffices hinv : ∀ l : List (List Bool),
      let st := l.foldl (pEvalStep t tab y) (fOne t, fZero t)
      toF ht st.1 = toF ht y ^ l.length ∧
        toF ht st.2 = (toPoly ht l).eval (toF ht y) from (hinv P).2
  intro l
  induction l using List.reverseRecOn with
  | nil => simp [toF_fOne ht, toF_fZero ht, toPoly]
  | append_singleton l c ih =>
    obtain ⟨h1v, h2v⟩ := ih
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, pEvalStep]
    set st := l.foldl (pEvalStep t tab y) (fOne t, fZero t)
    have hm1 : toF ht (fieldMul tab st.1 y) = toF ht st.1 * toF ht y :=
      fieldOfBits_fieldMul htab st.1 y
    have hm2 : toF ht (fieldMul tab c st.1) = toF ht c * toF ht st.1 :=
      fieldOfBits_fieldMul htab c st.1
    refine ⟨by rw [hm1, h1v, List.length_append, List.length_singleton, pow_succ], ?_⟩
    rw [toF_fAdd ht, h2v, hm2, h1v, toPoly_append_singleton ht, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

private theorem decodePoly_injective {t s w : ℕ} (ht : t ≠ 0) (hw : w ≤ 2 * s * t) :
    Function.Injective (fun x : BitString w ↦ toPoly ht (decodePoly t s (List.ofFn x))) := by
  intro x₁ x₂ hpoly
  dsimp only at hpoly
  funext b
  have ht_pos : 0 < t := Nat.pos_of_ne_zero ht
  have hb_lt : b.val < 2 * s * t := lt_of_lt_of_le b.isLt hw
  have hi : b.val / t < 2 * s := Nat.div_lt_of_lt_mul (by linarith)
  have hj : b.val % t < t := Nat.mod_lt _ ht_pos
  have hij : b.val / t * t + b.val % t = b.val := by
    rw [mul_comm (b.val / t) t]; exact Nat.div_add_mod b.val t
  have hcoeff : ∀ x : BitString w,
      equivBits ht ((toPoly ht (decodePoly t s (List.ofFn x))).coeff (b.val / t))
        ⟨b.val % t, hj⟩ = x b := fun x ↦ by
    have hc : (toPoly ht (decodePoly t s (List.ofFn x))).coeff (b.val / t) =
        toF ht ((decodePoly t s (List.ofFn x)).getD (b.val / t) []) := by
      simp only [toPoly, (wellSized_decodePoly t s (List.ofFn x)).1, Polynomial.finsetSum_coeff,
        coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single (b.val / t)
        (fun i' _ hne ↦ by have : b.val / t ≠ i' := fun h ↦ hne h.symm; simp [this])
        (fun hm ↦ absurd (Finset.mem_range.2 hi) hm)]
      simp
    rw [hc, toF, equivBits_fieldOfBits ht, decodePoly, List.getD_map_range _ [] hi,
      List.getD_map_range _ false hj, hij]
    simp [List.getD_eq_getElem?_getD, b.isLt]
  rw [← hcoeff x₁, ← hcoeff x₂, hpoly]

private def flattenWords : ∀ {r : ℕ}, (Fin r → List Bool) → List Bool
  | 0, _ => []
  | _ + 1, f => flattenWords (fun i ↦ f i.castSucc) ++ f (Fin.last _)

private theorem length_flattenWords {t : ℕ} :
    ∀ {r : ℕ} (f : Fin r → List Bool), (∀ i, (f i).length = t) → (flattenWords f).length = r * t
  | 0, _, _ => by simp [flattenWords]
  | r + 1, f, hf => by
    rw [flattenWords, List.length_append, length_flattenWords _ (fun i ↦ hf i.castSucc),
      hf (Fin.last r)]
    ring

private theorem getElem_flattenWords {t : ℕ} :
    ∀ {r : ℕ} (f : Fin r → List Bool) (hf : ∀ i, (f i).length = t)
      (a : Fin r) (b : Fin t),
      (flattenWords f)[a.val * t + b.val]'(by
        rw [length_flattenWords f hf]
        have := Nat.mul_le_mul_right t a.isLt
        linarith [b.isLt]) = (f a)[b.val]'(by rw [hf a]; exact b.isLt)
  | 0, _, _, a, _ => a.elim0
  | r + 1, f, hf, a, b => by
    simp only [flattenWords]
    have hpref := length_flattenWords (fun i : Fin r ↦ f i.castSucc) (fun i ↦ hf i.castSucc)
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 a.isLt) with har | har
    · have hlt : a.val * t + b.val < r * t := by
        have := Nat.mul_le_mul_right t har
        linarith [b.isLt]
      rw [List.getElem_append_left (by omega)]
      have ha_eq : (⟨a.val, har⟩ : Fin r).castSucc = a := Fin.ext rfl
      simpa [ha_eq] using
        getElem_flattenWords (fun i : Fin r ↦ f i.castSucc) (fun i ↦ hf i.castSucc) ⟨a.val, har⟩ b
    · have ha_eq : a = Fin.last r := Fin.ext har
      subst ha_eq
      rw [List.getElem_append_right (by rw [hpref]; exact Nat.le_add_right _ _)]
      simp [hpref]

private noncomputable def rightTupleEquivFin {t : ℕ} (ht : t ≠ 0) (m : ℕ) :
    (BinaryField t × (Fin m → BinaryField t)) ≃ Fin ((2 ^ t) ^ (m + 1)) := by
  have ht_pos : 0 < t := Nat.pos_of_ne_zero ht
  have hpow : (2 ^ t) ^ (m + 1) = 2 ^ ((m + 1) * t) := by rw [← pow_mul, mul_comm t]
  let e1 : (BinaryField t × (Fin m → BinaryField t)) ≃ (Fin (m + 1) → BinaryField t) :=
    { toFun := fun v ↦ Fin.cases v.1 v.2
      invFun := fun g ↦ (g 0, fun i ↦ g i.succ)
      left_inv := fun _ ↦ by simp
      right_inv := fun g ↦ funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i }
  let e2 : (Fin (m + 1) → BinaryField t) ≃ { l : List Bool // l.length = (m + 1) * t } :=
    { toFun := fun g ↦
        ⟨flattenWords fun i ↦ List.ofFn (equivBits ht (g i)),
          length_flattenWords _ fun _ ↦ List.length_ofFn⟩
      invFun := fun l i ↦ toF ht ((List.range t).map fun j ↦ l.1.getD (i.val * t + j) false)
      left_inv := fun g ↦ funext fun i ↦ (equivBits ht).injective <| funext fun j ↦ by
        dsimp only [toF]
        rw [equivBits_fieldOfBits ht, List.getD_map_range _ false j.isLt]
        have hlen := length_flattenWords (fun k : Fin (m + 1) ↦ List.ofFn (equivBits ht (g k)))
          (fun _ ↦ List.length_ofFn)
        have hlt : i.val * t + j.val < (m + 1) * t := by
          have := Nat.mul_le_mul_right t i.isLt; linarith [j.isLt]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hlt), Option.getD_some,
          getElem_flattenWords _ (fun _ ↦ List.length_ofFn) i j, List.getElem_ofFn]
      right_inv := fun l ↦ Subtype.ext <| List.ext_getElem
          (by rw [l.2]; exact length_flattenWords _ fun _ ↦ List.length_ofFn) fun p _ h₂ ↦ by
        have hp : p < (m + 1) * t := l.2 ▸ h₂
        let a : Fin (m + 1) := ⟨p / t, Nat.div_lt_of_lt_mul (by linarith)⟩
        let b : Fin t := ⟨p % t, Nat.mod_lt _ ht_pos⟩
        have hab : a.val * t + b.val = p := by
          dsimp [a, b]; rw [mul_comm (p / t) t]; exact Nat.div_add_mod p t
        have hge := getElem_flattenWords
          (fun i : Fin (m + 1) ↦
            List.ofFn (equivBits ht (toF ht ((List.range t).map fun j ↦
              l.1.getD (i.val * t + j) false))))
          (fun _ ↦ List.length_ofFn) a b
        simp only [hab] at hge
        rw [hge, List.getElem_ofFn]; dsimp only [toF]
        rw [equivBits_fieldOfBits ht, List.getD_map_range _ false b.isLt, hab,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some] }
  let e3 : { l : List Bool // l.length = (m + 1) * t } ≃ Fin ((2 ^ t) ^ (m + 1)) :=
    { toFun := fun l ↦ ⟨lsbValue l.1, by
        have hlt := lsbValue_lt_two_pow l.1
        rw [l.2] at hlt
        rwa [hpow]⟩
      invFun := fun v ↦ ⟨BitString.lowBits ((m + 1) * t) v.val, BitString.length_lowBits _ _⟩
      left_inv := fun l ↦ Subtype.ext <| by
        have heq := lowBits_lsbValue l.1
        rwa [l.2] at heq
      right_inv := fun v ↦ Fin.ext (lsbValue_lowBits_of_lt (lt_of_lt_of_eq v.isLt hpow)) }
  exact e1.trans (e2.trans e3)

private theorem pvNeighborBits_spec {t k m h searchBound : ℕ} (ht : t ≠ 0)
    (hB : 2 ^ (t + 1) ≤ searchBound) (uBits yBits : List Bool) :
    let P := toPoly ht (decodePoly t (3 ^ k) uBits)
    have hP : P.natDegree < (trinom (BinaryField t) k).natDegree := by
      rw [natDegree_trinom]
      exact natDegree_toPoly_lt ht (by positivity) (wellSized_decodePoly t (3 ^ k) uBits).1
    lsbValue (pvNeighborBits uBits searchBound t (3 ^ k) m h.bits yBits) =
      (rightTupleEquivFin ht m
        (pvNeighbor (trinom (BinaryField t) k) h m ⟨P, hP⟩ (toF ht yBits))).val := by
  have hmod : (leastIrreducibleCode searchBound t).bits = modulusBits t :=
    congrArg Nat.bits <| polyOfCode_injective <|
      (polyOfCode_leastIrreducibleCode ht hB).trans (polyOfCode_leastIrreducibleCode ht le_rfl).symm
  have htab : IsMulTable (BinaryField.basis ht)
      (powerMulTable (leastIrreducibleCode searchBound t).bits) := by
    rw [hmod]; exact isMulTable_fieldTable ht
  set tab := powerMulTable (leastIrreducibleCode searchBound t).bits
  set s := 3 ^ k
  set E := trinom (BinaryField t) k
  have hE : E.Monic := monic_trinom _ k
  set yPad := fAdd t yBits []
  have hy_eq : toF ht yPad = toF ht yBits := toF_fAdd_nil ht yBits
  set P₀ := decodePoly t s uBits
  have hP₀_len : P₀.length = 2 * s := (wellSized_decodePoly t s uBits).1
  have hP₀_deg : (toPoly ht P₀).natDegree < E.natDegree := by
    rw [natDegree_trinom]; exact natDegree_toPoly_lt ht (by positivity) hP₀_len
  have hbits_eq : ∀ (w : List Bool) (z : BinaryField t),
      w.length = t → toF ht w = z → w = List.ofFn (equivBits ht z) := fun w z hw hz ↦ by
    subst hz
    refine List.ext_getElem (by simp [hw]) fun j h₁ _ ↦ ?_
    rw [List.getElem_ofFn]; dsimp only [toF]; rw [equivBits_fieldOfBits ht]
    simp [List.getD_eq_getElem?_getD, h₁]
  let gFn (r : ℕ) : Fin (r + 1) → List Bool :=
    Fin.cases (List.ofFn (equivBits ht (toF ht yBits))) fun i ↦
      List.ofFn (equivBits ht ((pvPowerRem E h (toPoly ht P₀) i.val).eval (toF ht yBits)))
  have hiter : ∀ r : ℕ,
      let st := (List.range r).foldl (pvIterStep t s tab h.bits yPad) (P₀, yPad)
      st.1.length = 2 * s ∧
        toPoly ht st.1 = pvPowerRem E h (toPoly ht P₀) r ∧
        st.2 = flattenWords (gFn r) := by
    intro r
    induction r with
    | zero =>
      refine ⟨hP₀_len, ?_, ?_⟩
      · simp only [List.range_zero, List.foldl_nil, pvPowerRem_zero]
        exact (modByMonic_self_lt hE hP₀_deg).symm
      · simp only [List.range_zero, List.foldl_nil, flattenWords, List.nil_append]
        exact hbits_eq yPad (toF ht yBits) (by simp [yPad, fAdd]) hy_eq
    | succ r ihr =>
      obtain ⟨h1l, h1v, h2v⟩ := ihr
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      dsimp only [pvIterStep]
      set st := (List.range r).foldl (pvIterStep t s tab h.bits yPad) (P₀, yPad)
      have hp_v := toPoly_pPowMod ht htab h1l h.bits
      rw [lsbValue_bits] at hp_v
      have hg_cast : (fun i : Fin (r + 1) ↦ gFn (r + 1) i.castSucc) = gFn r :=
        funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i
      have hg_last : gFn (r + 1) (Fin.last (r + 1)) =
          List.ofFn (equivBits ht ((pvPowerRem E h (toPoly ht P₀) r).eval (toF ht yBits))) := by
        have : Fin.last (r + 1) = (Fin.last r).succ := Fin.ext rfl
        rw [this]; rfl
      refine ⟨(wellSized_pPowMod t s tab st.1 h.bits).1, ?_, ?_⟩
      · rw [hp_v, h1v, pvPowerRem_succ hE]
      · rw [h2v]
        conv_rhs => rw [flattenWords]
        rw [hg_cast, hg_last]
        congr 1
        exact hbits_eq _ _ (length_pEval t tab st.1 yPad)
          (by rw [toF_pEval ht htab, h1v, hy_eq])
  have hout : pvNeighborBits uBits searchBound t s m h.bits yBits =
      flattenWords fun i : Fin (m + 1) ↦
        List.ofFn (equivBits ht (Fin.cases (toF ht yBits)
          (fun j : Fin m ↦ (pvPowerRem E h (toPoly ht P₀) j.val).eval (toF ht yBits)) i)) :=
    (hiter m).2.2.trans (congrArg flattenWords (funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i))
  exact congrArg lsbValue hout

/-- **Lossless bipartite expansion of executable `pvNeighborNat`**: over `BinaryField t` with
`Nat.Coprime t 6`, `pvNeighborNat` defines an `(r, 2 ^ t, (1 - ε) * 2 ^ t)`-expander on `Fin M` and
`Fin ((2 ^ t) ^ (m + 1))`. -/
theorem isBipartiteExpander_pvNeighborNat {M r t k m h : ℕ}
    (ht : 1 ≤ t) (hcop : Nat.Coprime t 6) (hh : 2 ≤ h) (hm : 1 ≤ m)
    (hcap : Nat.clog 2 M ≤ 2 * 3 ^ k * t) (hr : r ≤ h ^ m)
    (hbound : m * (h - 1) * (2 * 3 ^ k - 1) < 2 ^ t)
    {ε : ℝ} (ha : (1 - ε) * (2 ^ t : ℝ) ≤ ((2 ^ t - m * (h - 1) * (2 * 3 ^ k - 1) : ℕ) : ℝ)) :
    let d := 2 ^ t
    let N := d ^ (m + 1)
    let wU := Nat.clog 2 M
    (∀ u < M, ∀ j < d, pvNeighborNat wU t k m h u j < N) ∧
    (∀ u < M, Set.InjOn (pvNeighborNat wU t k m h u) { j | j < d }) ∧
    IsBipartiteExpander
      (fun (u : Fin M) (v : Fin N) ↦
        ∃ j : Fin d, pvNeighborNat wU t k m h u.val j.val = v.val)
      r d ((1 - ε) * (d : ℝ)) := by
  have ht0 : t ≠ 0 := by omega
  set d := 2 ^ t
  set wU := Nat.clog 2 M
  set E := trinom (BinaryField t) k
  have hcardF : Fintype.card (BinaryField t) = 2 ^ t := BinaryField.card ht0
  have hEdeg : E.natDegree = 2 * 3 ^ k := natDegree_trinom _ k
  let eRight := rightTupleEquivFin ht0 m
  let ιLeft (u : Fin M) : PvLeft (BinaryField t) E :=
    ⟨toPoly ht0 (decodePoly t (3 ^ k) (BitString.lowBits wU u.val)), by
      rw [hEdeg]
      exact natDegree_toPoly_lt ht0 (by positivity) (wellSized_decodePoly t (3 ^ k) _).1⟩
  have hιLeft : Function.Injective ιLeft := fun u₁ u₂ h12 ↦ by
    have hbits_eq : (fun i : Fin wU ↦ u₁.val.testBit i.val) =
        fun i : Fin wU ↦ u₂.val.testBit i.val :=
      decodePoly_injective ht0 hcap
        (by simpa [ιLeft, BitString.lowBits_eq_ofFn] using congrArg Subtype.val h12)
    have hlow : BitString.lowBits wU u₁.val = BitString.lowBits wU u₂.val := by
      rw [BitString.lowBits_eq_ofFn, BitString.lowBits_eq_ofFn, hbits_eq]
    have hM_le : M ≤ 2 ^ wU := Nat.le_pow_clog (by decide) M
    exact Fin.ext <| by
      rw [← lsbValue_lowBits_of_lt (lt_of_lt_of_le u₁.isLt hM_le),
        ← lsbValue_lowBits_of_lt (lt_of_lt_of_le u₂.isLt hM_le), hlow]
  let eField : Fin d ≃ BinaryField t :=
    { toFun := fun j ↦ toF ht0 (BitString.lowBits t j.val)
      invFun := fun y ↦ ⟨lsbValue (List.ofFn (equivBits ht0 y)), by
        simpa [d] using lsbValue_lt_two_pow (List.ofFn (equivBits ht0 y))⟩
      left_inv := fun j ↦ Fin.ext <| by
        dsimp only
        have heq : List.ofFn (equivBits ht0 (toF ht0 (BitString.lowBits t j.val))) =
            BitString.lowBits t j.val :=
          List.ext_getElem (by simp) fun i _ h₂ ↦ by
            rw [List.getElem_ofFn]; dsimp only [toF]
            rw [equivBits_fieldOfBits ht0, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem h₂, Option.getD_some]
        rw [heq, lsbValue_lowBits_of_lt j.isLt]
      right_inv := fun y ↦ by
        dsimp only
        have hlow : BitString.lowBits t (lsbValue (List.ofFn (equivBits ht0 y))) =
            List.ofFn (equivBits ht0 y) := by
          simpa using lowBits_lsbValue (List.ofFn (equivBits ht0 y))
        rw [hlow, toF, fieldOfBits_ofFn ht0, AddEquiv.symm_apply_apply] }
  have hspec : ∀ (u : Fin M) (j : Fin d),
      pvNeighborNat wU t k m h u.val j.val =
        (eRight (pvNeighbor E h m (ιLeft u) (eField j))).val := fun u j ↦
    pvNeighborBits_spec (k := k) (m := m) (h := h) ht0 le_rfl
      (BitString.lowBits wU u.val) (BitString.lowBits t j.val)
  refine ⟨fun u hu j hj ↦ by rw [hspec ⟨u, hu⟩ ⟨j, hj⟩]; exact (eRight _).isLt,
    fun u hu j₁ hj₁ j₂ hj₂ h12 ↦ ?_, ?_⟩
  · rw [hspec ⟨u, hu⟩ ⟨j₁, hj₁⟩, hspec ⟨u, hu⟩ ⟨j₂, hj₂⟩] at h12
    exact congrArg Fin.val
      (eField.injective (pvNeighbor_injective E h m (ιLeft ⟨u, hu⟩)
        (eRight.injective (Fin.ext h12))))
  · have hexp0 := isBipartiteExpander_pvAdj (monic_trinom (BinaryField t) k)
      (irreducible_trinom hcardF hcop k) (two_le_natDegree_trinom (BinaryField t) k) hh hm
      (by rwa [hcardF, hEdeg])
    rw [hcardF, hEdeg] at hexp0
    have hadj_eq : (fun (u : Fin M) (v : Fin (d ^ (m + 1))) ↦
        ∃ j : Fin d, pvNeighborNat wU t k m h u.val j.val = v.val) =
        fun u v ↦ pvAdj E h m (ιLeft u) (eRight.symm v) := by
      funext u v
      apply propext
      rw [pvAdj_iff_exists]
      exact ⟨fun ⟨j, hj⟩ ↦ ⟨eField j, eRight.injective <| by
          rw [eRight.apply_symm_apply]; exact Fin.ext (by rw [← hspec u j, hj])⟩,
        fun ⟨y, hy⟩ ↦ ⟨eField.symm y, by
          rw [hspec u (eField.symm y), eField.apply_symm_apply, hy, eRight.apply_symm_apply]⟩⟩
    rw [hadj_eq]
    have ha' : (1 - ε) * (d : ℝ) ≤ ((2 ^ t - m * (h - 1) * (2 * 3 ^ k - 1) : ℕ) : ℝ) := by
      simpa [d] using ha
    exact isBipartiteExpander_pullback hexp0 ιLeft hιLeft eRight hr ha'

/-! ### Multi-Tape Turing-Machine Polynomial-Time Certificates -/

section PolyTimeCerts

attribute [local irreducible] ComputableInPolyTime

private abbrev encPoly : List (List Bool) ↪ List Bool := encList encBits

private abbrev encMulPar : (ℕ × ℕ × List (List (List Bool))) ↪ List Bool :=
  encPair encUnary (encPair encUnary encTable)

private theorem length_encPoly_le {t s : ℕ} {P : List (List Bool)}
    (hlen : P.length ≤ 2 * s) (hent : ∀ c ∈ P, c.length ≤ t) :
    (encPoly P).length ≤ 2 * s * (2 * t + 1) :=
  (length_encList_le encBits P hent).trans (Nat.mul_le_mul_right _ hlen)

private theorem poly_fZero : ComputableInPolyTime fZero encUnary encBits := by
  unfold fZero; fun_prop

private theorem poly_fOne : ComputableInPolyTime fOne encUnary encBits := by
  unfold fOne
  exact bitsTakeWithInput (bitsAppend (const [true]) (by fun_prop)) id'

private theorem poly_fAdd :
    ComputableInPolyTime (fun p : ℕ × List Bool × List Bool ↦ fAdd p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBits := by
  unfold fAdd; fun_prop

private theorem poly_fAdd' {α : Type} {enc : α ↪ List Bool} {t : α → ℕ} {a b : α → List Bool}
    (ht : ComputableInPolyTime t enc encUnary) (ha : ComputableInPolyTime a enc encBits)
    (hb : ComputableInPolyTime b enc encBits) :
    ComputableInPolyTime (fun x ↦ fAdd (t x) (a x) (b x)) enc encBits :=
  poly_fAdd.comp (ht.prod (ha.prod hb))

private theorem poly_pZero :
    ComputableInPolyTime (fun p : ℕ × ℕ ↦ pZero p.1 p.2)
      (encPair encUnary encUnary) encPoly := by
  have heq : (fun p : ℕ × ℕ ↦ pZero p.1 p.2) =
      fun p ↦ (List.range (2 * p.2)).map fun _ ↦ fZero p.1 := by
    funext p; simp [pZero, List.map_const']
  rw [heq]; have := poly_fZero; fun_prop

private theorem poly_pOne :
    ComputableInPolyTime (fun p : ℕ × ℕ ↦ pOne p.1 p.2)
      (encPair encUnary encUnary) encPoly := by
  unfold pOne; have := poly_fZero; have := poly_fOne; fun_prop

private theorem poly_pAdd :
    ComputableInPolyTime
      (fun q : (ℕ × ℕ) × List (List Bool) × List (List Bool) ↦ pAdd q.1.1 q.1.2 q.2.1 q.2.2)
      (encPair (encPair encUnary encUnary) (encPair encPoly encPoly)) encPoly := by
  unfold pAdd
  refine mapWithInput (by fun_prop) ?_
  exact poly_fAdd' (by fun_prop) (listGetDWithInput (by fun_prop) (by fun_prop) [])
    (listGetDWithInput (by fun_prop) (by fun_prop) [])

private theorem poly_pScale :
    ComputableInPolyTime
      (fun q : (List (List (List Bool)) × ℕ) × List Bool × List (List Bool) ↦
        pScale q.1.1 q.1.2 q.2.1 q.2.2)
      (encPair (encPair encTable encUnary) (encPair encBits encPoly)) encPoly := by
  unfold pScale
  refine mapWithInput (by fun_prop) ?_
  exact computableInPolyTime_fieldMul' (by fun_prop) (by fun_prop)
    (listGetDWithInput (by fun_prop) (by fun_prop) [])

private theorem poly_pMulXMod :
    ComputableInPolyTime (fun q : (ℕ × ℕ) × List (List Bool) ↦ pMulXMod q.1.1 q.1.2 q.2)
      (encPair (encPair encUnary encUnary) encPoly) encPoly := by
  unfold pMulXMod
  let encE := encPair (encPair (encPair encUnary encUnary) encPoly) encUnary
  have ht : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List (List Bool)) × ℕ ↦ p.1.1.1)
      encE encUnary := by fun_prop
  have hs : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List (List Bool)) × ℕ ↦ p.1.1.2)
      encE encUnary := by fun_prop
  have hP : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List (List Bool)) × ℕ ↦ p.1.2)
      encE encPoly := by fun_prop
  have hi : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List (List Bool)) × ℕ ↦ p.2)
      encE encUnary := by fun_prop
  have hlead := poly_fAdd' ht
    (listGetDWithInput hP (unary_sub' (unary_mul' (const 2) hs) (const 1)) []) (const [])
  have hprev := listGetDWithInput hP (unary_sub' hi (const 1)) []
  refine mapWithInput (by fun_prop) ?_
  exact ComputableInPolyTime.ite' (unary_beq hi (const 0)) hlead
    (ComputableInPolyTime.ite' (unary_beq hi hs)
      (poly_fAdd' ht hprev hlead) (poly_fAdd' ht hprev (const [])))

private theorem poly_pMulMod :
    ComputableInPolyTime
      (fun q : (ℕ × ℕ × List (List (List Bool))) × List (List Bool) × List (List Bool) ↦
        pMulMod q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2)
      (encPair encMulPar (encPair encPoly encPoly)) encPoly := by
  unfold pMulMod
  let encIn := encPair encMulPar (encPair encPoly encPoly)
  let encSt := encPair encPoly encPoly
  let encStep := encPair (encPair encMulPar encSt) encBits
  have hstep : ComputableInPolyTime
      (fun p : ((ℕ × ℕ × List (List (List Bool))) ×
          (List (List Bool) × List (List Bool))) × List Bool ↦
        pMulStep p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 p.2) encStep encSt := by
    unfold pMulStep
    have ht : ComputableInPolyTime (fun p ↦ p.1.1.1) encStep encUnary := by fun_prop
    have hs : ComputableInPolyTime (fun p ↦ p.1.1.2.1) encStep encUnary := by fun_prop
    have htb : ComputableInPolyTime (fun p ↦ p.1.1.2.2) encStep encTable := by fun_prop
    have hs1 : ComputableInPolyTime (fun p ↦ p.1.2.1) encStep encPoly := by fun_prop
    have hs2 : ComputableInPolyTime (fun p ↦ p.1.2.2) encStep encPoly := by fun_prop
    have hc : ComputableInPolyTime (fun p ↦ p.2) encStep encBits := by fun_prop
    exact (poly_pMulXMod.comp ((ht.prod hs).prod hs1)).prod
      (poly_pAdd.comp ((ht.prod hs).prod (hs2.prod (poly_pScale.comp ((htb.prod hs).prod
        (hc.prod hs1))))))
  have hq1 : ComputableInPolyTime (fun q ↦ q.1.1) encIn encUnary := by fun_prop
  have hq2 : ComputableInPolyTime (fun q ↦ q.1.2.1) encIn encUnary := by fun_prop
  have hP0 : ComputableInPolyTime (fun q ↦ q.2.1) encIn encPoly := by fun_prop
  have hinit : ComputableInPolyTime (fun q ↦ (q.2.1, pZero q.1.1 q.1.2.1)) encIn encSt :=
    hP0.prod (poly_pZero.comp (hq1.prod hq2))
  let bnd (q : (ℕ × ℕ × List (List (List Bool))) × List (List Bool) × List (List Bool)) : ℕ :=
    2 * (encPoly q.2.1).length + 8 * q.1.2.1 * (2 * q.1.1 + 1) + 4
  have hbnd : PolyBounded (fun q ↦ (encIn q).length) bnd := by
    have ps : PolyBounded (fun q ↦ (encIn q).length) (fun q ↦ q.1.2.1) := by
      simpa using hq2.polyBounded_length
    have pt : PolyBounded (fun q ↦ (encIn q).length) (fun q ↦ q.1.1) := by
      simpa using hq1.polyBounded_length
    exact (((PolyBounded.of_forall_le 2 0 (by simp)).mul hP0.polyBounded_length).add
      (((PolyBounded.of_forall_le 8 0 (by simp)).mul ps).mul
        (((PolyBounded.of_forall_le 2 0 (by simp)).mul pt).add
          (.of_forall_le 1 0 (by simp))))).add (.of_forall_le 4 0 (by simp))
  exact (snd encPoly encPoly).comp
    (foldlWith_spec (encA := encBits) (encL := encPoly) (encP := encMulPar) (encB := encSt)
      (par := Prod.fst) (list := fun q ↦ q.2.2) (init := fun q ↦ (q.2.1, pZero q.1.1 q.1.2.1))
      (step := fun par st c ↦ pMulStep par.1 par.2.1 par.2.2 st c)
      (fst _ _) ((snd encPoly encPoly).comp (snd _ _)) hinit hstep
      (fun q _ st ↦
        ((encPoly st.1).length ≤ (encPoly q.2.1).length ∨
          (st.1.length = 2 * q.1.2.1 ∧ ∀ c ∈ st.1, c.length ≤ q.1.1)) ∧
        (st.2.length = 2 * q.1.2.1 ∧ ∀ c ∈ st.2, c.length ≤ q.1.1))
      (fun q ↦ ⟨.inl le_rfl, wellSized_pZero q.1.1 q.1.2.1⟩)
      (fun q _ st c _ _ ↦
        ⟨.inr (wellSized_pMulXMod q.1.1 q.1.2.1 st.1),
          wellSized_pAdd q.1.1 q.1.2.1 st.2 (pScale q.1.2.2 q.1.2.1 c st.1)⟩)
      hbnd
      (fun q _ st _ hinv ↦ by
        have h2 := length_encPoly_le hinv.2.1.le hinv.2.2
        simp only [encSt, length_encPair, bnd]
        rcases hinv.1 with h1 | ⟨h1l, h1e⟩
        · nlinarith
        · have h1 := length_encPoly_le h1l.le h1e; nlinarith)).1

private theorem poly_pPowMod :
    ComputableInPolyTime
      (fun q : (ℕ × ℕ × List (List (List Bool))) × List (List Bool) × List Bool ↦
        pPowMod q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2)
      (encPair encMulPar (encPair encPoly encBits)) encPoly := by
  unfold pPowMod
  let encIn := encPair encMulPar (encPair encPoly encBits)
  let encSt := encPair encPoly encPoly
  let encStep := encPair (encPair encMulPar encSt) encBool
  have hstep : ComputableInPolyTime
      (fun p : ((ℕ × ℕ × List (List (List Bool))) ×
          (List (List Bool) × List (List Bool))) × Bool ↦
        pPowStep p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 p.2) encStep encSt := by
    unfold pPowStep
    have hpar : ComputableInPolyTime (fun p ↦ p.1.1) encStep encMulPar := by fun_prop
    have hs1 : ComputableInPolyTime (fun p ↦ p.1.2.1) encStep encPoly := by fun_prop
    have hs2 : ComputableInPolyTime (fun p ↦ p.1.2.2) encStep encPoly := by fun_prop
    exact (poly_pMulMod.comp (hpar.prod (hs1.prod hs1))).prod
      (ComputableInPolyTime.ite' (snd _ encBool) (poly_pMulMod.comp (hpar.prod (hs2.prod hs1))) hs2)
  have hq1 : ComputableInPolyTime (fun q ↦ q.1.1) encIn encUnary := by fun_prop
  have hq2 : ComputableInPolyTime (fun q ↦ q.1.2.1) encIn encUnary := by fun_prop
  have hP0 : ComputableInPolyTime (fun q ↦ q.2.1) encIn encPoly := by fun_prop
  have hinit : ComputableInPolyTime (fun q ↦ (q.2.1, pOne q.1.1 q.1.2.1)) encIn encSt :=
    hP0.prod (poly_pOne.comp (hq1.prod hq2))
  let bnd (q : (ℕ × ℕ × List (List (List Bool))) × List (List Bool) × List Bool) : ℕ :=
    2 * (encPoly q.2.1).length + 8 * q.1.2.1 * (2 * q.1.1 + 1) + 4
  have hbnd : PolyBounded (fun q ↦ (encIn q).length) bnd := by
    have ps : PolyBounded (fun q ↦ (encIn q).length) (fun q ↦ q.1.2.1) := by
      simpa using hq2.polyBounded_length
    have pt : PolyBounded (fun q ↦ (encIn q).length) (fun q ↦ q.1.1) := by
      simpa using hq1.polyBounded_length
    exact (((PolyBounded.of_forall_le 2 0 (by simp)).mul hP0.polyBounded_length).add
      (((PolyBounded.of_forall_le 8 0 (by simp)).mul ps).mul
        (((PolyBounded.of_forall_le 2 0 (by simp)).mul pt).add
          (.of_forall_le 1 0 (by simp))))).add (.of_forall_le 4 0 (by simp))
  exact (snd encPoly encPoly).comp
    (foldlWith_spec (encA := encBool) (encL := encBits) (encP := encMulPar) (encB := encSt)
      (par := Prod.fst) (list := fun q ↦ q.2.2) (init := fun q ↦ (q.2.1, pOne q.1.1 q.1.2.1))
      (step := fun par st b ↦ pPowStep par.1 par.2.1 par.2.2 st b)
      (fst _ _) ((snd encPoly encBits).comp (snd _ _)) hinit hstep
      (fun q _ st ↦
        ((encPoly st.1).length ≤ (encPoly q.2.1).length ∨
          (st.1.length = 2 * q.1.2.1 ∧ ∀ c ∈ st.1, c.length ≤ q.1.1)) ∧
        (st.2.length = 2 * q.1.2.1 ∧ ∀ c ∈ st.2, c.length ≤ q.1.1))
      (fun q ↦ ⟨.inl le_rfl, wellSized_pOne q.1.1 q.1.2.1⟩)
      (fun q _ st b _ hinv ↦
        ⟨.inr (wellSized_pMulMod _ _ _ _ _), by
          cases b
          · exact hinv.2
          · exact wellSized_pMulMod _ _ _ _ _⟩)
      hbnd
      (fun q _ st _ hinv ↦ by
        have h2 := length_encPoly_le hinv.2.1.le hinv.2.2
        simp only [encSt, length_encPair, bnd]
        rcases hinv.1 with h1 | ⟨h1l, h1e⟩
        · nlinarith
        · have h1 := length_encPoly_le h1l.le h1e; nlinarith)).1

private theorem poly_pEval :
    ComputableInPolyTime
      (fun q : (ℕ × List (List (List Bool)) × List Bool) × List (List Bool) ↦
        pEval q.1.1 q.1.2.1 q.2 q.1.2.2)
      (encPair (encPair encUnary (encPair encTable encBits)) encPoly) encBits := by
  unfold pEval
  let encPar := encPair encUnary (encPair encTable encBits)
  let encIn := encPair encPar encPoly
  let encSt := encPair encBits encBits
  let encStep := encPair (encPair encPar encSt) encBits
  have hstep : ComputableInPolyTime
      (fun p : ((ℕ × List (List (List Bool)) × List Bool) × (List Bool × List Bool)) × List Bool ↦
        pEvalStep p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 p.2) encStep encSt := by
    unfold pEvalStep
    have ht : ComputableInPolyTime (fun p ↦ p.1.1.1) encStep encUnary := by fun_prop
    have htb : ComputableInPolyTime (fun p ↦ p.1.1.2.1) encStep encTable := by fun_prop
    have hy : ComputableInPolyTime (fun p ↦ p.1.1.2.2) encStep encBits := by fun_prop
    have hs1 : ComputableInPolyTime (fun p ↦ p.1.2.1) encStep encBits := by fun_prop
    have hs2 : ComputableInPolyTime (fun p ↦ p.1.2.2) encStep encBits := by fun_prop
    have hc : ComputableInPolyTime (fun p ↦ p.2) encStep encBits := by fun_prop
    exact (computableInPolyTime_fieldMul' htb hs1 hy).prod
      (poly_fAdd' ht hs2 (computableInPolyTime_fieldMul' htb hc hs1))
  have hq1 : ComputableInPolyTime (fun q ↦ q.1.1) encIn encUnary := by fun_prop
  have hqtb : ComputableInPolyTime (fun q ↦ q.1.2.1) encIn encTable := by fun_prop
  have hinit : ComputableInPolyTime (fun q ↦ (fOne q.1.1, fZero q.1.1)) encIn encSt :=
    (poly_fOne.comp hq1).prod (poly_fZero.comp hq1)
  let bnd (q : (ℕ × List (List (List Bool)) × List Bool) × List (List Bool)) : ℕ :=
    3 * q.1.1 + 2 * q.1.2.1.length + 4
  have hbnd : PolyBounded (fun q ↦ (encIn q).length) bnd := by
    have pt : PolyBounded (fun q ↦ (encIn q).length) (fun q ↦ q.1.1) := by
      simpa using hq1.polyBounded_length
    have ptb := hqtb.polyBounded_length.mono fun q ↦ length_le_length_encList _ q.1.2.1
    exact (((PolyBounded.of_forall_le 3 0 (by simp)).mul pt).add
      ((PolyBounded.of_forall_le 2 0 (by simp)).mul ptb)).add (.of_forall_le 4 0 (by simp))
  exact (snd encBits encBits).comp
    (foldlWith_spec (encA := encBits) (encL := encPoly) (encP := encPar) (encB := encSt)
      (par := Prod.fst) (list := Prod.snd) (init := fun q ↦ (fOne q.1.1, fZero q.1.1))
      (step := fun par st c ↦ pEvalStep par.1 par.2.1 par.2.2 st c)
      (fst _ _) (snd _ _) hinit hstep
      (fun q _ st ↦ st.1.length ≤ max q.1.1 q.1.2.1.length ∧ st.2.length ≤ q.1.1)
      (fun q ↦ ⟨(List.length_take_le _ _).trans (le_max_left _ _), by simp [fZero]⟩)
      (fun _ _ _ _ _ _ ↦ ⟨by simp [pEvalStep, length_fieldMul], by simp [pEvalStep, fAdd]⟩)
      hbnd
      (fun q _ st _ hinv ↦ by
        simp only [encSt, length_encPair, encBits_apply, bnd]
        have := hinv.1; have := hinv.2; omega)).1

attribute [local irreducible] pMulMod pPowMod pEval in
/-- `pvNeighborBits` is computable in polynomial time by a multi-tape Turing machine. -/
theorem computableInPolyTime_pvNeighborBits :
    ComputableInPolyTime
      (fun q : List Bool × (ℕ × ℕ × ℕ × ℕ × List Bool × List Bool) ↦
        pvNeighborBits q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2)
      (encPair encBits encPvParam) encBits := by
  unfold pvNeighborBits
  let encIn := encPair encBits encPvParam
  have hB : ComputableInPolyTime (fun q : List Bool × _ ↦ q.2.1) encIn encUnary := by fun_prop
  have ht : ComputableInPolyTime (fun q : List Bool × _ ↦ q.2.2.1) encIn encUnary := by fun_prop
  have hs : ComputableInPolyTime (fun q : List Bool × _ ↦ q.2.2.2.1) encIn encUnary := by fun_prop
  have hm : ComputableInPolyTime (fun q : List Bool × _ ↦ q.2.2.2.2.1) encIn encUnary := by fun_prop
  have hhB : ComputableInPolyTime (fun q : List Bool × _ ↦ q.2.2.2.2.2.1) encIn encBits := by
    fun_prop
  have hyB : ComputableInPolyTime (fun q : List Bool × _ ↦ q.2.2.2.2.2.2) encIn encBits := by
    fun_prop
  have htab := computableInPolyTime_powerMulTable.comp
    (computableInPolyTime_bits_unary.comp
      (computableInPolyTime_leastIrreducibleCode.comp (hB.prod ht)))
  have hyPad := poly_fAdd' ht hyB (const [])
  have hdec : ComputableInPolyTime (fun q : (ℕ × ℕ) × List Bool ↦ decodePoly q.1.1 q.1.2 q.2)
      (encPair (encPair encUnary encUnary) encBits) encPoly := by unfold decodePoly; fun_prop
  have hP := hdec.comp ((ht.prod hs).prod (fst encBits encPvParam))
  let encIterPar := encPair encUnary (encPair encUnary
    (encPair encTable (encPair encBits encBits)))
  let encSt := encPair encPoly encBits
  let encStep := encPair (encPair encIterPar encSt) encUnary
  have hstep : ComputableInPolyTime
      (fun p : ((ℕ × ℕ × List (List (List Bool)) × List Bool × List Bool) ×
          (List (List Bool) × List Bool)) × ℕ ↦
        pvIterStep p.1.1.1 p.1.1.2.1 p.1.1.2.2.1 p.1.1.2.2.2.1 p.1.1.2.2.2.2 p.1.2 p.2)
      encStep encSt := by
    unfold pvIterStep
    have pt : ComputableInPolyTime (fun p ↦ p.1.1.1) encStep encUnary := by fun_prop
    have ps : ComputableInPolyTime (fun p ↦ p.1.1.2.1) encStep encUnary := by fun_prop
    have ptb : ComputableInPolyTime (fun p ↦ p.1.1.2.2.1) encStep encTable := by fun_prop
    have phb : ComputableInPolyTime (fun p ↦ p.1.1.2.2.2.1) encStep encBits := by fun_prop
    have py : ComputableInPolyTime (fun p ↦ p.1.1.2.2.2.2) encStep encBits := by fun_prop
    have ps1 : ComputableInPolyTime (fun p ↦ p.1.2.1) encStep encPoly := by fun_prop
    have ps2 : ComputableInPolyTime (fun p ↦ p.1.2.2) encStep encBits := by fun_prop
    have hpow : ComputableInPolyTime
        (fun p : ((ℕ × ℕ × List (List (List Bool)) × List Bool × List Bool) ×
            (List (List Bool) × List Bool)) × ℕ ↦
          pPowMod p.1.1.1 p.1.1.2.1 p.1.1.2.2.1 p.1.2.1 p.1.1.2.2.2.1) encStep encPoly :=
      poly_pPowMod.comp ((pt.prod (ps.prod ptb)).prod (ps1.prod phb))
    have hev : ComputableInPolyTime
        (fun p : ((ℕ × ℕ × List (List (List Bool)) × List Bool × List Bool) ×
            (List (List Bool) × List Bool)) × ℕ ↦
          pEval p.1.1.1 p.1.1.2.2.1 p.1.2.1 p.1.1.2.2.2.2) encStep encBits :=
      poly_pEval.comp ((pt.prod (ptb.prod py)).prod ps1)
    exact hpow.prod (bitsAppend ps2 hev)
  let bnd (q : List Bool × (ℕ × ℕ × ℕ × ℕ × List Bool × List Bool)) : ℕ :=
    8 * q.2.2.2.1 * (2 * q.2.2.1 + 1) + (q.2.2.2.2.1 + 1) * q.2.2.1 + 4
  have hbnd : PolyBounded (fun q ↦ (encIn q).length) bnd := by
    have pt : PolyBounded (fun q ↦ (encIn q).length) (fun q ↦ q.2.2.1) := by
      simpa using ht.polyBounded_length
    have ps : PolyBounded (fun q ↦ (encIn q).length) (fun q ↦ q.2.2.2.1) := by
      simpa using hs.polyBounded_length
    have pm : PolyBounded (fun q ↦ (encIn q).length) (fun q ↦ q.2.2.2.2.1) := by
      simpa using hm.polyBounded_length
    exact ((((PolyBounded.of_forall_le 8 0 (by simp)).mul ps).mul
      (((PolyBounded.of_forall_le 2 0 (by simp)).mul pt).add (.of_forall_le 1 0 (by simp)))).add
      ((pm.add (.of_forall_le 1 0 (by simp))).mul pt)).add (.of_forall_le 4 0 (by simp))
  let parFn (q : List Bool × (ℕ × ℕ × ℕ × ℕ × List Bool × List Bool)) :=
    (q.2.2.1, (q.2.2.2.1,
      (powerMulTable (leastIrreducibleCode q.2.1 q.2.2.1).bits,
        (q.2.2.2.2.2.1, fAdd q.2.2.1 q.2.2.2.2.2.2 []))))
  let initFn (q : List Bool × (ℕ × ℕ × ℕ × ℕ × List Bool × List Bool)) :=
    (decodePoly q.2.2.1 q.2.2.2.1 q.1, fAdd q.2.2.1 q.2.2.2.2.2.2 [])
  have hpar : ComputableInPolyTime parFn encIn encIterPar :=
    ht.prod (hs.prod (htab.prod (hhB.prod hyPad)))
  have hinit : ComputableInPolyTime initFn encIn encSt := hP.prod hyPad
  have hlist : ComputableInPolyTime
      (fun q : List Bool × (ℕ × ℕ × ℕ × ℕ × List Bool × List Bool) ↦ List.range q.2.2.2.2.1)
      encIn (encList encUnary) := unary_range' hm
  have hfold : ComputableInPolyTime
      (fun q ↦ (List.range q.2.2.2.2.1).foldl
        (pvIterStep (parFn q).1 (parFn q).2.1 (parFn q).2.2.1 (parFn q).2.2.2.1
          (parFn q).2.2.2.2) (initFn q))
      encIn encSt :=
    (foldlWith_spec (encA := encUnary) (encL := encList encUnary)
      (encP := encIterPar) (encB := encSt)
      (par := parFn) (list := fun q ↦ List.range q.2.2.2.2.1) (init := initFn)
      (step := fun par st i ↦ pvIterStep par.1 par.2.1 par.2.2.1 par.2.2.2.1 par.2.2.2.2 st i)
      hpar hlist hinit hstep
      (fun q consumed st ↦
        (st.1.length = 2 * q.2.2.2.1 ∧ ∀ c ∈ st.1, c.length ≤ q.2.2.1) ∧
        st.2.length = (consumed.length + 1) * q.2.2.1)
      (fun q ↦ ⟨wellSized_decodePoly q.2.2.1 q.2.2.2.1 q.1, by simp [initFn, fAdd]⟩)
      (fun _ consumed st _ _ hinv ↦
        ⟨wellSized_pPowMod _ _ _ _ _, by
          simp only [pvIterStep, List.length_append, hinv.2, length_pEval, List.length_singleton]
          ring⟩)
      hbnd
      (fun q consumed st hpref hinv ↦ by
        have hcl : consumed.length ≤ q.2.2.2.2.1 := by simpa using hpref.length_le
        have h1 := length_encPoly_le hinv.1.1.le hinv.1.2
        have h2 : st.2.length ≤ (q.2.2.2.2.1 + 1) * q.2.2.1 :=
          hinv.2.le.trans (Nat.mul_le_mul_right _ (by omega))
        simp only [encSt, length_encPair, encBits_apply, bnd]
        nlinarith)).1
  exact (snd encPoly encBits).comp hfold

/-- Uniform polynomial-size De Morgan neighbor-list circuit builder for `pvNeighborNat`. -/
theorem exists_circuit_pvNeighborNat :
    ∃ C₀ K₀ : ℕ, ∀ (M t k m h : ℕ),
      1 ≤ t → 1 ≤ m → h ≤ 2 ^ t → 2 * 3 ^ k ≤ 3 * Nat.clog 2 M → m ≤ Nat.clog 2 M →
      let d := 2 ^ t
      let wU := Nat.clog 2 M
      let wV := (m + 1) * t
      ∃ c : Circuits.Circuit Circuits.Boolean.signature wU (d * wV),
        c.size ≤ C₀ * (d + wU + 2) ^ K₀ ∧
        ∀ (x : BitString wU) (j : Fin d) (b : Fin wV) (idx : Fin (d * wV)),
          idx.val = j.val * wV + b.val →
          c.eval Circuits.Boolean.interpretation x idx =
            (pvNeighborNat wU t k m h (lsbValue (List.ofFn x)) j.val).testBit b.val := by
  let encFull : (ℕ × (ℕ × ℕ × ℕ × ℕ × List Bool × List Bool)) ↪ List Bool :=
    encPair encUnary encPvParam
  let bitPred : List Bool × (ℕ × (ℕ × ℕ × ℕ × ℕ × List Bool × List Bool)) → Bool :=
    fun q ↦ (pvNeighborBits q.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1
      q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2).getD q.2.1 false
  have hbitPred : ComputableInPolyTime bitPred (encPair encBits encFull) encBool :=
    bitsGetDWithInput
      (computableInPolyTime_pvNeighborBits.comp
        ((fst encBits encFull).prod ((snd encUnary encPvParam).comp (snd encBits encFull))))
      ((fst encUnary encPvParam).comp (snd encBits encFull)) false
  obtain ⟨C₁, K₁, hcirc⟩ := exists_circuit_family_of_polyTime_bits hbitPred
  refine ⟨C₁ * 48 ^ K₁, 2 * K₁ + 3, fun M t k m h ht hm hh hdeg hm_le ↦ ?_⟩
  have _ := ht; have _ := hm
  set d := 2 ^ t
  set wU := Nat.clog 2 M
  set wV := (m + 1) * t
  have hwV_pos : 0 < wV := by positivity
  let mkParam (idx : Fin (d * wV)) :=
    (idx.val % wV, (2 ^ (t + 1), (t, (3 ^ k, (m, (h.bits, BitString.lowBits t (idx.val / wV)))))))
  let bitC (idx : Fin (d * wV)) := (hcirc wU (mkParam idx)).choose
  let bigC := Circuits.Circuit.pi bitC
  have ht_le_d : t ≤ d := le_of_lt Nat.lt_two_pow_self
  have hh_len : h.bits.length ≤ t + 1 := by
    rw [Nat.size_eq_bits_len]
    rcases eq_or_ne h 0 with rfl | _
    · simp
    · rw [Nat.size_le]; exact lt_of_le_of_lt hh (by rw [pow_succ]; omega)
  have hsk_le : 3 ^ k ≤ 2 * wU := by omega
  have hwV_le : wV ≤ (wU + 1) * d := Nat.mul_le_mul (by omega) ht_le_d
  have hsize_one : ∀ idx : Fin (d * wV),
      (bitC idx).size ≤ C₁ * 48 ^ K₁ * (d + wU + 2) ^ (2 * K₁) := fun idx ↦ by
    have hb_lt : idx.val % wV < wV := Nat.mod_lt _ hwV_pos
    have hb_le : idx.val % wV ≤ (wU + 1) * d := hb_lt.le.trans hwV_le
    have hlen : wU + (encFull (mkParam idx)).length + 2 ≤ 48 * (d + wU + 2) ^ 2 := by
      simp only [encFull, encPvParam, mkParam, length_encPair, encUnary_apply,
        List.length_replicate, encBits_apply, BitString.length_lowBits]
      have hd2 : 2 ^ (t + 1) = 2 * d := by dsimp [d]; ring
      rw [hd2]
      nlinarith
    calc (bitC idx).size
        ≤ C₁ * (wU + (encFull (mkParam idx)).length + 2) ^ K₁ :=
          (hcirc wU (mkParam idx)).choose_spec.1
      _ ≤ C₁ * (48 * (d + wU + 2) ^ 2) ^ K₁ :=
          Nat.mul_le_mul_left C₁ (Nat.pow_le_pow_left hlen K₁)
      _ = C₁ * 48 ^ K₁ * (d + wU + 2) ^ (2 * K₁) := by
          rw [mul_pow, ← pow_mul, ← mul_assoc]
  refine ⟨bigC, ?_, fun x j b idx hidx ↦ ?_⟩
  · have hpi : bigC.size = ∑ idx : Fin (d * wV), (bitC idx).size := by simp [bigC]
    have hdwV : d * wV ≤ (d + wU + 2) ^ 3 :=
      calc d * wV ≤ d * ((wU + 1) * d) := Nat.mul_le_mul_left d hwV_le
        _ = d ^ 2 * wU + d ^ 2 := by ring
        _ ≤ (d + wU + 2) ^ 3 := by
            have : (d + wU + 2) ^ 3 = d ^ 2 * wU + d ^ 2 +
              (d ^ 3 + 2 * d ^ 2 * wU + 5 * d ^ 2 + 3 * d * wU ^ 2 + 12 * d * wU + 12 * d +
                wU ^ 3 + 6 * wU ^ 2 + 12 * wU + 8) := by ring
            omega
    rw [hpi]
    calc ∑ idx : Fin (d * wV), (bitC idx).size
        ≤ ∑ _idx : Fin (d * wV), C₁ * 48 ^ K₁ * (d + wU + 2) ^ (2 * K₁) :=
          Finset.sum_le_sum fun idx _ ↦ hsize_one idx
      _ = d * wV * (C₁ * 48 ^ K₁ * (d + wU + 2) ^ (2 * K₁)) := by simp
      _ ≤ (d + wU + 2) ^ 3 * (C₁ * 48 ^ K₁ * (d + wU + 2) ^ (2 * K₁)) :=
          Nat.mul_le_mul_right _ hdwV
      _ = C₁ * 48 ^ K₁ * (d + wU + 2) ^ (2 * K₁ + 3) := by ring
  · have hdiv : idx.val / wV = j.val := by
      rw [hidx, mul_comm j.val wV, Nat.mul_add_div hwV_pos,
        Nat.div_eq_zero_iff.2 (.inr b.isLt), add_zero]
    have hmod : idx.val % wV = b.val := by
      rw [hidx, mul_comm j.val wV, Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]
    have hev : bigC.eval Circuits.Boolean.interpretation x idx =
        (bitC idx).eval Circuits.Boolean.interpretation x 0 := by simp [bigC]
    rw [hev, (hcirc wU (mkParam idx)).choose_spec.2 x]
    dsimp [bitPred, mkParam, pvNeighborNat]
    have hlow : BitString.lowBits wU (lsbValue (List.ofFn x)) = List.ofFn x := by
      simpa using lowBits_lsbValue (List.ofFn x)
    rw [hdiv, hmod, testBit_lsbValue, hlow]

end PolyTimeCerts

end CslibFrontier.ParvareshVardy
