/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.ThreeSum.ThreeSets
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Complexity.FineGrained
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Planar Point Collinearity and Gajentaan--Overmars 3SUM Reduction

Defines the binary-encoded **3-Set 3SUM** (`ThreeSetSum`) and **Planar Point Collinearity**
(`PointCollinearity`) decision problems together with the **3SUM Hypothesis**
(`ThreeSumHypothesis`), and proves the polynomial-time many-one reduction from `ThreeSetSum` to
`PointCollinearity` via the Gajentaan--Overmars residue-separated cubic-curve lifting
$t \mapsto (t, t^3)$ ($8a + 1$, $8b + 2$, $8c - 3$).

## Main definitions

* `CslibFrontier.Computability.Complexity.ThreeSetSumInstance`, `encThreeSetSumInstance`,
  `ThreeSetSum`, `ThreeSumHypothesis`.
* `CslibFrontier.Computability.Complexity.PointCollinearityInstance`,
  `encPointCollinearityInstance`, `PointCollinearity`.
* `CslibFrontier.Computability.Complexity.threeSetToPointCollinearity`.

## Main results

* `CslibFrontier.Computability.Complexity.cubicLift_collinear_iff`: Vieta collinearity criterion
  on $y = x^3$.
* `CslibFrontier.Computability.Complexity.polyTimeReducible_threeSetSum_pointCollinearity`:
  `PolyTimeReducible encThreeSetSumInstance encPointCollinearityInstance ThreeSetSum
  PointCollinearity`.
-/

public section

open Matrix Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open scoped Cslib.Complexity

namespace CslibFrontier.Computability.Complexity

/-- An instance `(setA, setB, setC)` of 3-Set 3SUM. -/
@[ext]
public structure ThreeSetSumInstance where
  /-- First integer list $A$. -/
  setA : List ℤ
  /-- Second integer list $B$. -/
  setB : List ℤ
  /-- Third integer list $C$. -/
  setC : List ℤ
  deriving DecidableEq, Repr, Inhabited

/-- Framed binary encoding of `ThreeSetSumInstance`. -/
public enc_structure encThreeSetSumInstance : ThreeSetSumInstance where
  setA : (encList encIntBin),
  setB : (encList encIntBin),
  setC : (encList encIntBin)

/-- The 3-Set 3SUM decision language (`Cslib.Algorithms.ThreeSum.HasThreeSetSolution`). -/
public def ThreeSetSum : Set ThreeSetSumInstance :=
  {inst | Cslib.Algorithms.ThreeSum.HasThreeSetSolution
    inst.setA.toFinset inst.setB.toFinset inst.setC.toFinset}

/-- Maximum binary encoding length across all integers in `inst.setA`, `inst.setB`, and
`inst.setC`. -/
@[expose] public def ThreeSetSumInstance.wordBitLength (inst : ThreeSetSumInstance) : ℕ :=
  ((inst.setA ++ inst.setB ++ inst.setC).map fun x ↦ (encIntBin x).length).foldr max 0

/-- The **3SUM Hypothesis**: for every $\varepsilon > 0$ and word-overhead exponent
$e \in \mathbb{N}$, 3-Set 3SUM is not decidable in time
$O((|A| + |B| + |C|)^{2 - \varepsilon} \cdot (w + 1)^e)$, where $w$ is the maximum binary encoding
length of an input integer. -/
public def ThreeSumHypothesis : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ e : ℕ,
    ¬ Cslib.Complexity.DecidableInTimeO ThreeSetSum encThreeSetSumInstance
      (fun inst ↦ ((inst.setA.length + inst.setB.length + inst.setC.length : ℕ) : ℝ) ^ (2 - ε) *
        (inst.wordBitLength + 1 : ℝ) ^ e)

/-- An instance of Planar Point Collinearity, given as a list of rational pairs `(x, y) ∈ ℚ × ℚ`. -/
@[ext]
public structure PointCollinearityInstance where
  /-- Rational planar points `(x_i, y_i)`. -/
  points : List (ℚ × ℚ)
  deriving DecidableEq, Repr, Inhabited

/-- Framed binary encoding of `PointCollinearityInstance`. -/
public enc_structure encPointCollinearityInstance : PointCollinearityInstance where
  points : (encList (encPair encRat encRat))

/-- Real planar point `Fin 2 → ℝ` for index `i` of `inst`. -/
@[expose] public def PointCollinearityInstance.realPoint (inst : PointCollinearityInstance)
    (i : Fin inst.points.length) : Fin 2 → ℝ :=
  ![((inst.points[i.1]'i.2).1 : ℝ), ((inst.points[i.1]'i.2).2 : ℝ)]

/-- **Planar Point Collinearity**: rational planar point configurations having three distinct
indices on a common real affine line $a_0 x + a_1 y + c = 0$ ($a \neq 0$). -/
public def PointCollinearity : Set PointCollinearityInstance :=
  {inst | ∃ (i₁ i₂ i₃ : Fin inst.points.length) (a : Fin 2 → ℝ) (c : ℝ),
    i₁ ≠ i₂ ∧ i₂ ≠ i₃ ∧ i₁ ≠ i₃ ∧ a ≠ 0 ∧
      dotProduct a (inst.realPoint i₁) + c = 0 ∧
      dotProduct a (inst.realPoint i₂) + c = 0 ∧
      dotProduct a (inst.realPoint i₃) + c = 0}

/-- Planar cubic lift $t \mapsto (t, t^3) \in \mathbb{R}^2$. -/
@[expose] public def cubicLift (t : ℝ) : Fin 2 → ℝ :=
  ![t, t ^ 3]

/-- Vieta's collinearity criterion on $y = x^3$: three distinct points on `cubicLift` are
collinear if and only if $u + v + w = 0$. -/
public theorem cubicLift_collinear_iff {u v w : ℝ} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w) :
    (∃ (a : Fin 2 → ℝ) (c : ℝ), a ≠ 0 ∧
      dotProduct a (cubicLift u) + c = 0 ∧
      dotProduct a (cubicLift v) + c = 0 ∧
      dotProduct a (cubicLift w) + c = 0) ↔
    u + v + w = 0 := by
  constructor
  · rintro ⟨a, c, ha, hu, hv, hw⟩
    simp only [cubicLift, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hu hv hw
    have hb : a 1 ≠ 0 := by
      intro hb0
      rw [hb0] at hu hv
      have ha0 : a 0 * (u - v) = 0 := by linarith
      rcases mul_eq_zero.mp ha0 with h0 | hdiff
      · apply ha; ext i; fin_cases i
        · exact h0
        · exact hb0
      · exact huv (sub_eq_zero.mp hdiff)
    have hq1 : (u - v) * (a 0 + a 1 * (u ^ 2 + u * v + v ^ 2)) = 0 := by
      linarith [show u ^ 3 - v ^ 3 = (u - v) * (u ^ 2 + u * v + v ^ 2) by ring]
    have hq2 : (v - w) * (a 0 + a 1 * (v ^ 2 + v * w + w ^ 2)) = 0 := by
      linarith [show v ^ 3 - w ^ 3 = (v - w) * (v ^ 2 + v * w + w ^ 2) by ring]
    have eq1 : a 0 + a 1 * (u ^ 2 + u * v + v ^ 2) = 0 :=
      (mul_eq_zero.mp hq1).resolve_left (sub_ne_zero.mpr huv)
    have eq2 : a 0 + a 1 * (v ^ 2 + v * w + w ^ 2) = 0 :=
      (mul_eq_zero.mp hq2).resolve_left (sub_ne_zero.mpr hvw)
    have eq3 : a 1 * ((u - w) * (u + v + w)) = 0 := by linarith
    exact (mul_eq_zero.mp ((mul_eq_zero.mp eq3).resolve_left hb)).resolve_left
      (sub_ne_zero.mpr huw)
  · intro hsum
    refine ⟨![-(u ^ 2 + u * v + v ^ 2), 1], -(u * v * w), ?_, ?_, ?_, ?_⟩
    · intro hzero
      have : (![-(u ^ 2 + u * v + v ^ 2), (1 : ℝ)] : Fin 2 → ℝ) 1 = 0 := congrFun hzero 1
      norm_num at this
    · simp only [cubicLift, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      have hw : w = -(u + v) := by linarith
      rw [hw]; ring
    · simp only [cubicLift, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      have hw : w = -(u + v) := by linarith
      rw [hw]; ring
    · simp only [cubicLift, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      have hw : w = -(u + v) := by linarith
      rw [hw]; ring

/-- Gajentaan--Overmars cubic-curve reduction from `ThreeSetSumInstance` to
`PointCollinearityInstance`. -/
@[expose] public def threeSetToPointCollinearity (inst : ThreeSetSumInstance) :
    PointCollinearityInstance :=
  let A' := Cslib.Complexity.selectDistinct inst.setA (List.replicate inst.setA.length true)
  let B' := Cslib.Complexity.selectDistinct inst.setB (List.replicate inst.setB.length true)
  let C' := Cslib.Complexity.selectDistinct inst.setC (List.replicate inst.setC.length true)
  let vals : List ℤ := A'.map (fun a ↦ 8 * a + 1) ++
    B'.map (fun b ↦ 8 * b + 2) ++
    C'.map (fun c ↦ 8 * c - 3)
  { points := vals.map fun z : ℤ ↦ ((z : ℚ), (z : ℚ) * ((z : ℚ) * (z : ℚ))) }

private lemma mod_eight_triple_sum_zero {u v w : ℤ}
    (hu : u % 8 = 1 ∨ u % 8 = 2 ∨ u % 8 = 5)
    (hv : v % 8 = 1 ∨ v % 8 = 2 ∨ v % 8 = 5)
    (hw : w % 8 = 1 ∨ w % 8 = 2 ∨ w % 8 = 5)
    (hsum : u + v + w = 0) :
    (u % 8 = 1 ∧ v % 8 = 2 ∧ w % 8 = 5) ∨
    (u % 8 = 1 ∧ v % 8 = 5 ∧ w % 8 = 2) ∨
    (u % 8 = 2 ∧ v % 8 = 1 ∧ w % 8 = 5) ∨
    (u % 8 = 2 ∧ v % 8 = 5 ∧ w % 8 = 1) ∨
    (u % 8 = 5 ∧ v % 8 = 1 ∧ w % 8 = 2) ∨
    (u % 8 = 5 ∧ v % 8 = 2 ∧ w % 8 = 1) := by
  rcases hu with hu | hu | hu <;>
    rcases hv with hv | hv | hv <;>
    rcases hw with hw | hw | hw <;>
    omega

attribute [local irreducible] encRat encIntBin encNat encUnary
  encThreeSetSumInstance encPointCollinearityInstance

/-- **Polynomial-Time Reduction from 3-Set 3SUM to Planar Point Collinearity**
.
-/
public theorem polyTimeReducible_threeSetSum_pointCollinearity :
    Cslib.Complexity.PolyTimeReducible encThreeSetSumInstance encPointCollinearityInstance
      ThreeSetSum PointCollinearity := by
  have hpoly : ComputableInPolyTime threeSetToPointCollinearity
      encThreeSetSumInstance encPointCollinearityInstance := by
    have hdedup : ∀ (getL : ThreeSetSumInstance → List ℤ),
        ComputableInPolyTime getL encThreeSetSumInstance (encList encIntBin) →
        ComputableInPolyTime
          (fun inst ↦ Cslib.Complexity.selectDistinct (getL inst)
            (List.replicate (getL inst).length true))
          encThreeSetSumInstance (encList encIntBin) := fun getL hget ↦
      (Cslib.Complexity.computableInPolyTime_selectDistinct encIntBin).comp
        (hget.prod ((bitsReplicate true).comp
          ((length_list encIntBin).comp hget)))
    have hA' := hdedup ThreeSetSumInstance.setA (encThreeSetSumInstance_setA_polyTime id')
    have hB' := hdedup ThreeSetSumInstance.setB (encThreeSetSumInstance_setB_polyTime id')
    have hC' := hdedup ThreeSetSumInstance.setC (encThreeSetSumInstance_setC_polyTime id')
    have hmA : ComputableInPolyTime
        (fun inst : ThreeSetSumInstance ↦
          (Cslib.Complexity.selectDistinct inst.setA
            (List.replicate inst.setA.length true)).map fun a ↦ 8 * a + 1)
        encThreeSetSumInstance (encList encIntBin) :=
      mapWith
        (intBin_add' (intBin_mul' (const 8) (snd encBool encIntBin)) (const 1))
        (const false) hA'
    have hmB : ComputableInPolyTime
        (fun inst : ThreeSetSumInstance ↦
          (Cslib.Complexity.selectDistinct inst.setB
            (List.replicate inst.setB.length true)).map fun b ↦ 8 * b + 2)
        encThreeSetSumInstance (encList encIntBin) :=
      mapWith
        (intBin_add' (intBin_mul' (const 8) (snd encBool encIntBin)) (const 2))
        (const false) hB'
    have hmC : ComputableInPolyTime
        (fun inst : ThreeSetSumInstance ↦
          (Cslib.Complexity.selectDistinct inst.setC
            (List.replicate inst.setC.length true)).map fun c ↦ 8 * c - 3)
        encThreeSetSumInstance (encList encIntBin) :=
      mapWith
        (intBin_sub' (intBin_mul' (const 8) (snd encBool encIntBin)) (const 3))
        (const false) hC'
    have hvals := (hmA.listAppend' hmB).listAppend' hmC
    have hcubic : ComputableInPolyTime
        (fun p : Bool × ℤ ↦ ((p.2 : ℚ), (p.2 : ℚ) * ((p.2 : ℚ) * (p.2 : ℚ))))
        (encPair encBool encIntBin) (encPair encRat encRat) := by
      have hz : ComputableInPolyTime (fun p : Bool × ℤ ↦ (p.2 : ℚ))
          (encPair encBool encIntBin) encRat := rat_intCast.comp (snd encBool encIntBin)
      exact hz.prod (rat_mul' hz (rat_mul' hz hz))
    have hpts := mapWith hcubic (const false) hvals
    exact (encPointCollinearityInstance_mk_polyTime hpts).of_enc_eq
      fun _ ↦ congrArg encPointCollinearityInstance rfl
  refine ⟨threeSetToPointCollinearity, hpoly, fun inst ↦ ?_⟩
  let A' := Cslib.Complexity.selectDistinct inst.setA (List.replicate inst.setA.length true)
  let B' := Cslib.Complexity.selectDistinct inst.setB (List.replicate inst.setB.length true)
  let C' := Cslib.Complexity.selectDistinct inst.setC (List.replicate inst.setC.length true)
  let vals : List ℤ := A'.map (fun a ↦ 8 * a + 1) ++
    B'.map (fun b ↦ 8 * b + 2) ++ C'.map (fun c ↦ 8 * c - 3)
  have hnodup : vals.Nodup := by
    have hA : (A'.map (fun a : ℤ ↦ 8 * a + 1)).Nodup :=
      (Cslib.Complexity.nodup_selectDistinct _ _).map fun _ _ h ↦ by omega
    have hB : (B'.map (fun b : ℤ ↦ 8 * b + 2)).Nodup :=
      (Cslib.Complexity.nodup_selectDistinct _ _).map fun _ _ h ↦ by omega
    have hC : (C'.map (fun c : ℤ ↦ 8 * c - 3)).Nodup :=
      (Cslib.Complexity.nodup_selectDistinct _ _).map fun _ _ h ↦ by omega
    have hAB : ∀ x ∈ A'.map (fun a : ℤ ↦ 8 * a + 1),
        ∀ y ∈ B'.map (fun b : ℤ ↦ 8 * b + 2), x ≠ y := by
      intro x hx y hy hEq
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hy
      omega
    have hABC : ∀ x ∈ A'.map (fun a : ℤ ↦ 8 * a + 1) ++ B'.map (fun b : ℤ ↦ 8 * b + 2),
        ∀ y ∈ C'.map (fun c : ℤ ↦ 8 * c - 3), x ≠ y := by
      intro x hx y hy hEq
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hy
      rcases List.mem_append.mp hx with hxA | hxB
      · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hxA; omega
      · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hxB; omega
    exact List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hA, hB, hAB⟩, hC, hABC⟩
  have hlen : (threeSetToPointCollinearity inst).points.length = vals.length := by
    simp [threeSetToPointCollinearity, vals, A', B', C']
  have hreal_pt : ∀ (i : Fin (threeSetToPointCollinearity inst).points.length),
      (threeSetToPointCollinearity inst).realPoint i =
        cubicLift (vals[i.1]'(by rw [← hlen]; exact i.2) : ℝ) := by
    intro i
    have hpt_i :
        (threeSetToPointCollinearity inst).points[i.1]'i.2 =
          ((vals[i.1]'(by rw [← hlen]; exact i.2) : ℚ),
            (vals[i.1]'(by rw [← hlen]; exact i.2) : ℚ) *
              ((vals[i.1]'(by rw [← hlen]; exact i.2) : ℚ) *
                (vals[i.1]'(by rw [← hlen]; exact i.2) : ℚ))) :=
      @List.getElem_map ℤ (ℚ × ℚ)
        (fun z : ℤ ↦ ((z : ℚ), (z : ℚ) * ((z : ℚ) * (z : ℚ)))) vals i.1 i.2
    unfold PointCollinearityInstance.realPoint cubicLift
    rw [hpt_i]
    ext j
    fin_cases j
    · simp
    · simp
      ring
  have h3sum_iff : inst ∈ ThreeSetSum ↔
      ∃ a ∈ inst.setA, ∃ b ∈ inst.setB, ∃ c ∈ inst.setC, a + b + c = 0 := by
    simp [ThreeSetSum, Cslib.Algorithms.ThreeSum.HasThreeSetSolution]
  rw [h3sum_iff]
  change (∃ a ∈ inst.setA, ∃ b ∈ inst.setB, ∃ c ∈ inst.setC, a + b + c = 0) ↔
    ∃ (i₁ i₂ i₃ : Fin (threeSetToPointCollinearity inst).points.length)
      (a : Fin 2 → ℝ) (c : ℝ),
      i₁ ≠ i₂ ∧ i₂ ≠ i₃ ∧ i₁ ≠ i₃ ∧ a ≠ 0 ∧
        dotProduct a ((threeSetToPointCollinearity inst).realPoint i₁) + c = 0 ∧
        dotProduct a ((threeSetToPointCollinearity inst).realPoint i₂) + c = 0 ∧
        dotProduct a ((threeSetToPointCollinearity inst).realPoint i₃) + c = 0
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, hsum⟩
    have ha' : a ∈ A' := Cslib.Complexity.mem_selectDistinct_replicate.mpr ha
    have hb' : b ∈ B' := Cslib.Complexity.mem_selectDistinct_replicate.mpr hb
    have hc' : c ∈ C' := Cslib.Complexity.mem_selectDistinct_replicate.mpr hc
    have hu_in : 8 * a + 1 ∈ vals :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨a, ha', rfl⟩))
    have hv_in : 8 * b + 2 ∈ vals :=
      List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨b, hb', rfl⟩))
    have hw_in : 8 * c - 3 ∈ vals :=
      List.mem_append_right _ (List.mem_map.mpr ⟨c, hc', rfl⟩)
    obtain ⟨iu, hiu, hu_eq⟩ := List.getElem_of_mem hu_in
    obtain ⟨iv, hiv, hv_eq⟩ := List.getElem_of_mem hv_in
    obtain ⟨iw, hiw, hw_eq⟩ := List.getElem_of_mem hw_in
    have huv_v : (8 * a + 1 : ℤ) ≠ 8 * b + 2 := by omega
    have hvw_v : (8 * b + 2 : ℤ) ≠ 8 * c - 3 := by omega
    have huw_v : (8 * a + 1 : ℤ) ≠ 8 * c - 3 := by omega
    obtain ⟨normal, offset, hnormal, h1, h2, h3⟩ :=
      (cubicLift_collinear_iff (by exact_mod_cast huv_v) (by exact_mod_cast hvw_v)
        (by exact_mod_cast huw_v)).mpr
        (show ((8 * a + 1 : ℤ) : ℝ) + ((8 * b + 2 : ℤ) : ℝ) + ((8 * c - 3 : ℤ) : ℝ) = 0 by
          exact_mod_cast (by omega : (8 * a + 1) + (8 * b + 2) + (8 * c - 3) = 0))
    let f1 : Fin (threeSetToPointCollinearity inst).points.length := ⟨iu, by rwa [hlen]⟩
    let f2 : Fin (threeSetToPointCollinearity inst).points.length := ⟨iv, by rwa [hlen]⟩
    let f3 : Fin (threeSetToPointCollinearity inst).points.length := ⟨iw, by rwa [hlen]⟩
    refine ⟨f1, f2, f3, normal, offset,
      fun h ↦ huv_v (by rw [← hu_eq, ← hv_eq]; congr 1; exact congrArg Fin.val h),
      fun h ↦ hvw_v (by rw [← hv_eq, ← hw_eq]; congr 1; exact congrArg Fin.val h),
      fun h ↦ huw_v (by rw [← hu_eq, ← hw_eq]; congr 1; exact congrArg Fin.val h),
      hnormal, ?_, ?_, ?_⟩
    · rw [hreal_pt f1]; dsimp [f1]; rw [hu_eq]; exact h1
    · rw [hreal_pt f2]; dsimp [f2]; rw [hv_eq]; exact h2
    · rw [hreal_pt f3]; dsimp [f3]; rw [hw_eq]; exact h3
  · rintro ⟨i₁, i₂, i₃, normal, offset, h12, h23, h13, hnormal, h1, h2, h3⟩
    rw [hreal_pt i₁] at h1
    rw [hreal_pt i₂] at h2
    rw [hreal_pt i₃] at h3
    let u : ℤ := vals[i₁.1]'(by rw [← hlen]; exact i₁.2)
    let v : ℤ := vals[i₂.1]'(by rw [← hlen]; exact i₂.2)
    let w : ℤ := vals[i₃.1]'(by rw [← hlen]; exact i₃.2)
    have hne_uv : u ≠ v := fun h ↦ h12 (Fin.ext ((List.Nodup.getElem_inj_iff hnodup).mp h))
    have hne_vw : v ≠ w := fun h ↦ h23 (Fin.ext ((List.Nodup.getElem_inj_iff hnodup).mp h))
    have hne_uw : u ≠ w := fun h ↦ h13 (Fin.ext ((List.Nodup.getElem_inj_iff hnodup).mp h))
    have hsumR : (u : ℝ) + (v : ℝ) + (w : ℝ) = 0 :=
      (cubicLift_collinear_iff (by exact_mod_cast hne_uv) (by exact_mod_cast hne_vw)
        (by exact_mod_cast hne_uw)).mp ⟨normal, offset, hnormal, h1, h2, h3⟩
    have hsumZ : u + v + w = 0 := by exact_mod_cast hsumR
    have hmem_res : ∀ z ∈ vals,
        (∃ a ∈ inst.setA, z = 8 * a + 1) ∨
        (∃ b ∈ inst.setB, z = 8 * b + 2) ∨
        (∃ c ∈ inst.setC, z = 8 * c - 3) := by
      intro z hz
      simp only [vals, List.mem_append, List.mem_map] at hz
      rcases hz with (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩) | ⟨c, hc, rfl⟩
      · exact Or.inl ⟨a, Cslib.Complexity.mem_selectDistinct_replicate.mp ha, rfl⟩
      · exact Or.inr (Or.inl ⟨b, Cslib.Complexity.mem_selectDistinct_replicate.mp hb, rfl⟩)
      · exact Or.inr (Or.inr ⟨c, Cslib.Complexity.mem_selectDistinct_replicate.mp hc, rfl⟩)
    have hmod_of : ∀ z ∈ vals, z % 8 = 1 ∨ z % 8 = 2 ∨ z % 8 = 5 := by
      intro z hz
      rcases hmem_res z hz with ⟨a, _, rfl⟩ | ⟨b, _, rfl⟩ | ⟨c, _, rfl⟩ <;> omega
    have hu_in : u ∈ vals := List.getElem_mem _
    have hv_in : v ∈ vals := List.getElem_mem _
    have hw_in : w ∈ vals := List.getElem_mem _
    have pickA : ∀ z ∈ vals, z % 8 = 1 → ∃ a ∈ inst.setA, z = 8 * a + 1 := by
      intro z hz hm; rcases hmem_res z hz with h | ⟨_, _, rfl⟩ | ⟨_, _,
        rfl⟩ <;> [exact h; omega; omega]
    have pickB : ∀ z ∈ vals, z % 8 = 2 → ∃ b ∈ inst.setB, z = 8 * b + 2 := by
      intro z hz hm; rcases hmem_res z hz with ⟨_, _, rfl⟩ | h | ⟨_, _,
        rfl⟩ <;> [omega; exact h; omega]
    have pickC : ∀ z ∈ vals, z % 8 = 5 → ∃ c ∈ inst.setC, z = 8 * c - 3 := by
      intro z hz hm; rcases hmem_res z hz with ⟨_, _, rfl⟩ | ⟨_, _,
        rfl⟩ | h <;> [omega; omega; exact h]
    rcases mod_eight_triple_sum_zero (hmod_of u hu_in) (hmod_of v hv_in)
      (hmod_of w hw_in) hsumZ with
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · obtain ⟨a, ha, _⟩ := pickA u hu_in h1
      obtain ⟨b, hb, _⟩ := pickB v hv_in h2
      obtain ⟨c, hc, _⟩ := pickC w hw_in h3
      exact ⟨a, ha, b, hb, c, hc, by omega⟩
    · obtain ⟨a, ha, _⟩ := pickA u hu_in h1
      obtain ⟨c, hc, _⟩ := pickC v hv_in h2
      obtain ⟨b, hb, _⟩ := pickB w hw_in h3
      exact ⟨a, ha, b, hb, c, hc, by omega⟩
    · obtain ⟨b, hb, _⟩ := pickB u hu_in h1
      obtain ⟨a, ha, _⟩ := pickA v hv_in h2
      obtain ⟨c, hc, _⟩ := pickC w hw_in h3
      exact ⟨a, ha, b, hb, c, hc, by omega⟩
    · obtain ⟨b, hb, _⟩ := pickB u hu_in h1
      obtain ⟨c, hc, _⟩ := pickC v hv_in h2
      obtain ⟨a, ha, _⟩ := pickA w hw_in h3
      exact ⟨a, ha, b, hb, c, hc, by omega⟩
    · obtain ⟨c, hc, _⟩ := pickC u hu_in h1
      obtain ⟨a, ha, _⟩ := pickA v hv_in h2
      obtain ⟨b, hb, _⟩ := pickB w hw_in h3
      exact ⟨a, ha, b, hb, c, hc, by omega⟩
    · obtain ⟨c, hc, _⟩ := pickC u hu_in h1
      obtain ⟨b, hb, _⟩ := pickB v hv_in h2
      obtain ⟨a, ha, _⟩ := pickA w hw_in h3
      exact ⟨a, ha, b, hb, c, hc, by omega⟩

end CslibFrontier.Computability.Complexity
