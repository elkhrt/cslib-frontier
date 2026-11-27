/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.OneInThreeSAT.Reduction
public import CslibFrontier.Computability.Complexity.Problems.ThreeExactCover

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Common
import Mathlib.Tactic.IntervalCases

/-!
# 3-Regular Exact Cover by 3-Sets (`3XC-3`): Variable Gadgets

Variable gadgets (`gadget1`, `gadget2`, `gadget3`, `varGadget`), true/false branch covers
(`gadgetTrue`, `gadgetFalse`), polynomial-time computability (`computableInPolyTime_varGadget`),
exact `3`-regularity (`varGadget_props`), and forcing (`varGadget_forcing`) for `3XC-3`
.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

namespace ThreeExactCoverRegular

/-- Variable gadget for `d = 1` (`O = [j0]`): `3` `T`-sets, `2` `F`-sets, and `2` `G`-sets. -/
@[expose] def gadget1 (base j0 : ℕ) : List (List ℕ) :=
  let e0 := 3 * j0; let e1 := 3 * j0 + 1; let e2 := 3 * j0 + 2
  let a0 := base; let b0 := base + 1
  let a1 := base + 2; let b1 := base + 3
  let a2 := base + 4; let b2 := base + 5
  [[e0, a0, b0], [e1, a1, b1], [e2, a2, b2],
   [a0, b1, a2], [b0, a1, b2],
   [a0, b1, b2], [a1, b0, a2]]

/-- Variable gadget for `d = 2` (`O = [j0, j1]`): `6` `T`-sets, `4` `F`-sets, and `4` `G`-sets. -/
@[expose] def gadget2 (base j0 j1 : ℕ) : List (List ℕ) :=
  let e0 := 3 * j0; let e1 := 3 * j0 + 1; let e2 := 3 * j0 + 2
  let e3 := 3 * j1; let e4 := 3 * j1 + 1; let e5 := 3 * j1 + 2
  let a0 := base; let b0 := base + 1
  let a1 := base + 2; let b1 := base + 3
  let a2 := base + 4; let b2 := base + 5
  let a3 := base + 6; let b3 := base + 7
  let a4 := base + 8; let b4 := base + 9
  let a5 := base + 10; let b5 := base + 11
  [[e0, a0, b0], [e1, a1, b1], [e2, a2, b2], [e3, a3, b3], [e4, a4, b4], [e5, a5, b5],
   [a0, b3, a4], [b0, a1, b4], [b1, a2, a5], [b2, a3, b5],
   [a0, b1, b4], [a1, b2, a5], [a2, b3, b5], [a3, b0, a4]]

/-- Variable gadget for `d = 3` (`O = [j0, j1, j2]`): `9` `T`-sets, `6` `F`-sets, and
`6` `G`-sets. -/
@[expose] def gadget3 (base j0 j1 j2 : ℕ) : List (List ℕ) :=
  let e0 := 3 * j0; let e1 := 3 * j0 + 1; let e2 := 3 * j0 + 2
  let e3 := 3 * j1; let e4 := 3 * j1 + 1; let e5 := 3 * j1 + 2
  let e6 := 3 * j2; let e7 := 3 * j2 + 1; let e8 := 3 * j2 + 2
  let a0 := base; let b0 := base + 1
  let a1 := base + 2; let b1 := base + 3
  let a2 := base + 4; let b2 := base + 5
  let a3 := base + 6; let b3 := base + 7
  let a4 := base + 8; let b4 := base + 9
  let a5 := base + 10; let b5 := base + 11
  let a6 := base + 12; let b6 := base + 13
  let a7 := base + 14; let b7 := base + 15
  let a8 := base + 16; let b8 := base + 17
  [[e0, a0, b0], [e1, a1, b1], [e2, a2, b2], [e3, a3, b3], [e4, a4, b4],
   [e5, a5, b5], [e6, a6, b6], [e7, a7, b7], [e8, a8, b8],
   [a0, b5, a6], [b0, a1, b6], [b1, a2, a7], [b2, a3, b7], [b3, a4, a8], [b4, a5, b8],
   [a0, b1, b6], [a1, b2, a7], [a2, b3, b7], [a3, b4, a8], [a4, b5, b8], [a5, b0, a6]]

/-- Dispatch variable gadget for occurrence list `O` of length `1, 2, 3`. -/
@[expose] def varGadget (base : ℕ) (O : List ℕ) : List (List ℕ) :=
  if O.length == 1 then gadget1 base (O.getD 0 0)
  else if O.length == 2 then gadget2 base (O.getD 0 0) (O.getD 1 0)
  else if O.length == 3 then gadget3 base (O.getD 0 0) (O.getD 1 0) (O.getD 2 0)
  else []

/-- True-branch exact cover of a single variable gadget (`T`-sets). -/
@[expose] def gadgetTrue (base : ℕ) (O : List ℕ) : List (List ℕ) :=
  O.zipIdx.flatMap fun p ↦
    [[3 * p.1, base + 6 * p.2, base + 6 * p.2 + 1],
     [3 * p.1 + 1, base + 6 * p.2 + 2, base + 6 * p.2 + 3],
     [3 * p.1 + 2, base + 6 * p.2 + 4, base + 6 * p.2 + 5]]

/-! ### Polynomial-time computability of `varGadget` -/

open ComputableInPolyTime

private theorem computableInPolyTime_gadget1 :
    ComputableInPolyTime (fun p : ℕ × ℕ ↦ gadget1 p.1 p.2)
      (encPair encNat encNat) encNatSetList := by
  unfold gadget1
  fun_prop

private theorem computableInPolyTime_gadget2 :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ ↦ gadget2 p.1.1 p.1.2 p.2)
      (encPair (encPair encNat encNat) encNat) encNatSetList := by
  unfold gadget2
  fun_prop

private theorem computableInPolyTime_gadget3 :
    ComputableInPolyTime (fun p : ((ℕ × ℕ) × ℕ) × ℕ ↦ gadget3 p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encNat encNat) encNat) encNat) encNatSetList := by
  unfold gadget3
  fun_prop

/-- The variable-gadget dispatcher `varGadget` is computable in polynomial time. -/
theorem computableInPolyTime_varGadget :
    ComputableInPolyTime (fun p : ℕ × List ℕ ↦ varGadget p.1 p.2)
      (encPair encNat (encList encNat)) encNatSetList := by
  unfold varGadget
  have hlen : ComputableInPolyTime (fun p : ℕ × List ℕ ↦ p.2.length)
      (encPair encNat (encList encNat)) encUnary :=
    (ComputableInPolyTime.length_list encNat).comp (ComputableInPolyTime.snd _ _)
  have hc1 := ComputableInPolyTime.unary_beq hlen (.const 1)
  have hc2 := ComputableInPolyTime.unary_beq hlen (.const 2)
  have hc3 := ComputableInPolyTime.unary_beq hlen (.const 3)
  have hsnd : ComputableInPolyTime (fun p : ℕ × List ℕ ↦ p.2)
      (encPair encNat (encList encNat)) (encList encNat) :=
    ComputableInPolyTime.snd encNat (encList encNat)
  have hfst : ComputableInPolyTime (fun p : ℕ × List ℕ ↦ p.1)
      (encPair encNat (encList encNat)) encNat :=
    ComputableInPolyTime.fst encNat (encList encNat)
  have hg0 := ComputableInPolyTime.listGetDWithInput hsnd
    (ComputableInPolyTime.const (encIn := encPair encNat (encList encNat))
      (encOut := encUnary) 0) 0
  have hg1 := ComputableInPolyTime.listGetDWithInput hsnd
    (ComputableInPolyTime.const (encIn := encPair encNat (encList encNat))
      (encOut := encUnary) 1) 0
  have hg2 := ComputableInPolyTime.listGetDWithInput hsnd
    (ComputableInPolyTime.const (encIn := encPair encNat (encList encNat))
      (encOut := encUnary) 2) 0
  have h1 := computableInPolyTime_gadget1.comp (hfst.prod hg0)
  have h2 := computableInPolyTime_gadget2.comp ((hfst.prod hg0).prod hg1)
  have h3 := computableInPolyTime_gadget3.comp (((hfst.prod hg0).prod hg1).prod hg2)
  exact ComputableInPolyTime.ite' hc1 h1
    (ComputableInPolyTime.ite' hc2 h2 (ComputableInPolyTime.ite' hc3 h3 (.const [])))


/-! ### Gadget internal invariants (`d = 1, 2, 3`) -/

private lemma unpack_triple_occ {base j0 j1 j2 : ℕ}
    (hO_nd : ([j0, j1, j2] : List ℕ).Nodup)
    (hO_lt : ∀ j ∈ ([j0, j1, j2] : List ℕ), 3 * j + 2 < base) :
    3 * j0 + 2 < base ∧ 3 * j1 + 2 < base ∧ 3 * j2 + 2 < base ∧
      (j0 ≠ j1 ∧ j0 ≠ j2 ∧ j1 ≠ j2) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hO_nd
  exact ⟨hO_lt j0 (by simp), hO_lt j1 (by simp), hO_lt j2 (by simp),
    ⟨hO_nd.1.1, hO_nd.1.2, hO_nd.2.1⟩⟩


private lemma varGadget_one (base j0 : ℕ) : varGadget base [j0] = gadget1 base j0 := rfl
private lemma varGadget_two (base j0 j1 : ℕ) : varGadget base [j0, j1] = gadget2 base j0 j1 := rfl
private lemma varGadget_three (base j0 j1 j2 : ℕ) :
    varGadget base [j0, j1, j2] = gadget3 base j0 j1 j2 := rfl

private lemma countP_triple_pos {x a b c : ℕ} {l : List (List ℕ)}
    (h : x = a ∨ x = b ∨ x = c) :
    ([a, b, c] :: l).countP (fun S ↦ decide (x ∈ S)) =
      1 + l.countP (fun S ↦ decide (x ∈ S)) := by
  have hm : x ∈ [a, b, c] := by simpa using h
  simp [hm, Nat.add_comm]

private lemma countP_triple_neg {x a b c : ℕ} {l : List (List ℕ)}
    (h : x ≠ a ∧ x ≠ b ∧ x ≠ c) :
    ([a, b, c] :: l).countP (fun S ↦ decide (x ∈ S)) =
      l.countP (fun S ↦ decide (x ∈ S)) := by
  have hm : x ∉ [a, b, c] := by simpa using h
  simp [hm]

private lemma cp1 {x a b c : ℕ} {l : List (List ℕ)} (h : x = a) :
    ([a, b, c] :: l).countP (fun S ↦ decide (x ∈ S)) = 1 + l.countP (fun S ↦ decide (x ∈ S)) :=
  countP_triple_pos (Or.inl h)

private lemma cp2 {x a b c : ℕ} {l : List (List ℕ)} (h : x = b) :
    ([a, b, c] :: l).countP (fun S ↦ decide (x ∈ S)) = 1 + l.countP (fun S ↦ decide (x ∈ S)) :=
  countP_triple_pos (Or.inr (Or.inl h))

private lemma cp3 {x a b c : ℕ} {l : List (List ℕ)} (h : x = c) :
    ([a, b, c] :: l).countP (fun S ↦ decide (x ∈ S)) = 1 + l.countP (fun S ↦ decide (x ∈ S)) :=
  countP_triple_pos (Or.inr (Or.inr h))

private lemma cp0 {x a b c : ℕ} {l : List (List ℕ)} (ha : x ≠ a) (hb : x ≠ b) (hc : x ≠ c) :
    ([a, b, c] :: l).countP (fun S ↦ decide (x ∈ S)) = l.countP (fun S ↦ decide (x ∈ S)) :=
  countP_triple_neg ⟨ha, hb, hc⟩

private lemma flatten_T3 {base u x y z j c : ℕ} {O : List ℕ} (hj : j ∈ O) (hc : c < 3)
    (hx : x = 3 * j + c) (hy : base ≤ y ∧ y < base + 18) (hz : base ≤ z ∧ z < base + 18)
    (hu : u ∈ [x, y, z]) :
    (∃ j' ∈ O, ∃ c' < 3, u = 3 * j' + c') ∨ (base ≤ u ∧ u < base + 18) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact Or.inl ⟨j, hj, c, hc, hx⟩
  · exact Or.inr hy
  · exact Or.inr hz

private lemma flatten_FG3 {base u x y z : ℕ} (hx : base ≤ x ∧ x < base + 18)
    (hy : base ≤ y ∧ y < base + 18) (hz : base ≤ z ∧ z < base + 18) (hu : u ∈ [x, y, z]) :
    base ≤ u ∧ u < base + 18 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl <;> assumption

private lemma countP_gadgetTrue_aux {O : List ℕ} {base k : ℕ}
    (hnd : O.Nodup) (hlt : ∀ j ∈ O, 3 * j + 2 < base) :
    let T := (O.zipIdx k).flatMap fun p ↦
      [[3 * p.1, base + 6 * p.2, base + 6 * p.2 + 1],
       [3 * p.1 + 1, base + 6 * p.2 + 2, base + 6 * p.2 + 3],
       [3 * p.1 + 2, base + 6 * p.2 + 4, base + 6 * p.2 + 5]]
    (∀ j ∈ O, ∀ c < 3, T.countP (fun S ↦ decide (3 * j + c ∈ S)) = 1) ∧
    (∀ u, u < base → (∀ j ∈ O, ∀ c < 3, u ≠ 3 * j + c) →
      T.countP (fun S ↦ decide (u ∈ S)) = 0) ∧
    (∀ u, base + 6 * (k + O.length) ≤ u → T.countP (fun S ↦ decide (u ∈ S)) = 0) := by
  induction O generalizing k with
  | nil => simp
  | cons a L ih =>
    simp only [List.nodup_cons] at hnd
    have ha : 3 * a + 2 < base := hlt a (by simp)
    have hL : ∀ j ∈ L, 3 * j + 2 < base := fun j hj ↦ hlt j (by simp [hj])
    obtain ⟨ih1, ih2, ih3⟩ := ih (k := k + 1) hnd.2 hL
    have hflat_cons : ∀ p : List ℕ → Bool,
        (((a :: L).zipIdx k).flatMap fun p ↦
          [[3 * p.1, base + 6 * p.2, base + 6 * p.2 + 1],
           [3 * p.1 + 1, base + 6 * p.2 + 2, base + 6 * p.2 + 3],
           [3 * p.1 + 2, base + 6 * p.2 + 4, base + 6 * p.2 + 5]]).countP p =
        ([[3 * a, base + 6 * k, base + 6 * k + 1],
          [3 * a + 1, base + 6 * k + 2, base + 6 * k + 3],
          [3 * a + 2, base + 6 * k + 4, base + 6 * k + 5]]).countP p +
        ((L.zipIdx (k + 1)).flatMap fun p ↦
          [[3 * p.1, base + 6 * p.2, base + 6 * p.2 + 1],
           [3 * p.1 + 1, base + 6 * p.2 + 2, base + 6 * p.2 + 3],
           [3 * p.1 + 2, base + 6 * p.2 + 4, base + 6 * p.2 + 5]]).countP p := fun p ↦ by
      rw [List.zipIdx_cons, List.flatMap_cons, List.countP_append]
    refine ⟨?_, ?_, ?_⟩
    · intro j hj c hc
      rw [hflat_cons]
      rcases List.mem_cons.mp hj with rfl | hjL
      · have h0 : ∀ u < base, (∀ j' ∈ L, ∀ c' < 3, u ≠ 3 * j' + c') → _ := ih2
        have htail : ((L.zipIdx (k + 1)).flatMap _).countP (fun S ↦ decide (3 * j + c ∈ S)) = 0 :=
          h0 (3 * j + c) (by omega) fun j' hj' c' hc' heq ↦ hnd.1 (by
            have : j = j' := by omega
            rwa [this])
        rw [htail, add_zero]
        interval_cases c <;>
          ((repeat first | rw [cp1 (by omega)] | rw [cp0 (by omega) (by omega) (by omega)]);
           rw [List.countP_nil])
      · have hne : j ≠ a := fun heq ↦ hnd.1 (heq ▸ hjL)
        have hjlt := hL j hjL
        rw [ih1 j hjL c hc]
        have hhead : ([[3 * a, base + 6 * k, base + 6 * k + 1],
            [3 * a + 1, base + 6 * k + 2, base + 6 * k + 3],
            [3 * a + 2, base + 6 * k + 4, base + 6 * k + 5]]).countP
            (fun S ↦ decide (3 * j + c ∈ S)) = 0 := by
          (repeat rw [cp0 (by omega) (by omega) (by omega)]); exact List.countP_nil
        rw [hhead, zero_add]
    · intro u hu hne
      rw [hflat_cons, ih2 u hu (fun j hj c hc ↦ hne j (by simp [hj]) c hc), add_zero]
      have h0 := hne a (by simp) 0 (by omega)
      have h1 := hne a (by simp) 1 (by omega)
      have h2 := hne a (by simp) 2 (by omega)
      (repeat rw [cp0 (by omega) (by omega) (by omega)]); exact List.countP_nil
    · intro u hu
      have hu' : base + 6 * (k + 1 + L.length) ≤ u := by simp only [List.length_cons] at hu; omega
      rw [hflat_cons, ih3 u hu', add_zero]
      (repeat rw [cp0 (by omega) (by omega) (by omega)]); exact List.countP_nil

private lemma gadgetTrue_countP_clause {O : List ℕ} {base : ℕ}
    (hnd : O.Nodup) (hlt : ∀ j ∈ O, 3 * j + 2 < base) :
    (∀ j ∈ O, ∀ c < 3, (gadgetTrue base O).countP (fun S ↦ decide (3 * j + c ∈ S)) = 1) ∧
    (∀ u, u < base → (∀ j ∈ O, ∀ c < 3, u ≠ 3 * j + c) →
      (gadgetTrue base O).countP (fun S ↦ decide (u ∈ S)) = 0) ∧
    (∀ u, base + 6 * O.length ≤ u →
      (gadgetTrue base O).countP (fun S ↦ decide (u ∈ S)) = 0) := by
  simpa [gadgetTrue] using countP_gadgetTrue_aux (k := 0) hnd hlt

private def gadgetFG (base : ℕ) (O : List ℕ) : List (List ℕ) :=
  if O.length == 1 then
    [[base, base + 3, base + 4], [base + 1, base + 2, base + 5],
     [base, base + 3, base + 5], [base + 2, base + 1, base + 4]]
  else if O.length == 2 then
    [[base, base + 7, base + 8], [base + 1, base + 2, base + 9],
     [base + 3, base + 4, base + 10], [base + 5, base + 6, base + 11],
     [base, base + 3, base + 9], [base + 2, base + 5, base + 10],
     [base + 4, base + 7, base + 11], [base + 6, base + 1, base + 8]]
  else if O.length == 3 then
    [[base, base + 11, base + 12], [base + 1, base + 2, base + 13],
     [base + 3, base + 4, base + 14], [base + 5, base + 6, base + 15],
     [base + 7, base + 8, base + 16], [base + 9, base + 10, base + 17],
     [base, base + 3, base + 13], [base + 2, base + 5, base + 14],
     [base + 4, base + 7, base + 15], [base + 6, base + 9, base + 16],
     [base + 8, base + 11, base + 17], [base + 10, base + 1, base + 12]]
  else []

private lemma countP_varGadget_clause {base : ℕ} {O : List ℕ}
    (hO_len : 1 ≤ O.length ∧ O.length ≤ 3) (hO_nd : O.Nodup)
    (hO_lt : ∀ j ∈ O, 3 * j + 2 < base) :
    (∀ j ∈ O, ∀ c < 3, (varGadget base O).countP (fun S ↦ decide (3 * j + c ∈ S)) = 1) ∧
    (∀ u, u < base → (∀ j ∈ O, ∀ c < 3, u ≠ 3 * j + c) →
      (varGadget base O).countP (fun S ↦ decide (u ∈ S)) = 0) ∧
    (∀ u, base + 6 * O.length ≤ u →
      (varGadget base O).countP (fun S ↦ decide (u ∈ S)) = 0) := by
  have hcl := gadgetTrue_countP_clause hO_nd hO_lt
  have hsplit : varGadget base O = gadgetTrue base O ++ gadgetFG base O := by
    rcases O with _ | ⟨j0, _ | ⟨j1, _ | ⟨j2, _ | ⟨j3, t⟩⟩⟩⟩
    · simp at hO_len
    · rfl
    · rfl
    · rfl
    · simp at hO_len; omega
  have hfg_r : ∀ S ∈ gadgetFG base O, ∀ x ∈ S, base ≤ x ∧ x < base + 6 * O.length := by
    rcases O with _ | ⟨j0, _ | ⟨j1, _ | ⟨j2, _ | ⟨j3, t⟩⟩⟩⟩
    · simp at hO_len
    · intro S hS x hx
      change S ∈ [[base, base + 3, base + 4], [base + 1, base + 2, base + 5],
        [base, base + 3, base + 5], [base + 2, base + 1, base + 4]] at hS
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
      rcases hS with rfl | rfl | rfl | rfl <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false] at hx;
         rcases hx with rfl | rfl | rfl <;> simp only [List.length_cons, List.length_nil] <;>
           omega)
    · intro S hS x hx
      change S ∈ [[base, base + 7, base + 8], [base + 1, base + 2, base + 9],
        [base + 3, base + 4, base + 10], [base + 5, base + 6, base + 11],
        [base, base + 3, base + 9], [base + 2, base + 5, base + 10],
        [base + 4, base + 7, base + 11], [base + 6, base + 1, base + 8]] at hS
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
      rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false] at hx;
         rcases hx with rfl | rfl | rfl <;> simp only [List.length_cons, List.length_nil] <;>
           omega)
    · intro S hS x hx
      change S ∈ [[base, base + 11, base + 12], [base + 1, base + 2, base + 13],
        [base + 3, base + 4, base + 14], [base + 5, base + 6, base + 15],
        [base + 7, base + 8, base + 16], [base + 9, base + 10, base + 17],
        [base, base + 3, base + 13], [base + 2, base + 5, base + 14],
        [base + 4, base + 7, base + 15], [base + 6, base + 9, base + 16],
        [base + 8, base + 11, base + 17], [base + 10, base + 1, base + 12]] at hS
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
      simp only [List.length_cons, List.length_nil]
      rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact flatten_FG3 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hx
    · simp at hO_len; omega
  have hfg_zero : ∀ u, (u < base ∨ base + 6 * O.length ≤ u) →
      (gadgetFG base O).countP (fun S ↦ decide (u ∈ S)) = 0 := fun u hu ↦
    List.countP_eq_zero.mpr fun S hS ↦ by
      simp only [decide_eq_true_eq]; intro huS; have := hfg_r S hS u huS; omega
  rw [hsplit]
  refine ⟨fun j hj c hc ↦ ?_, fun u hu hne ↦ ?_, fun u hu ↦ ?_⟩
  · rw [List.countP_append, hfg_zero _ (Or.inl (by have := hO_lt j hj; omega)), add_zero]
    exact hcl.1 j hj c hc
  · rw [List.countP_append, hfg_zero u (Or.inl hu), add_zero]; exact hcl.2.1 u hu hne
  · rw [List.countP_append, hfg_zero u (Or.inr hu), add_zero]; exact hcl.2.2 u hu

private lemma varGadget_props_3 {base j0 j1 j2 : ℕ}
    (h0 : 3 * j0 + 2 < base) (h1 : 3 * j1 + 2 < base) (h2 : 3 * j2 + 2 < base)
    (hnd : j0 ≠ j1 ∧ j0 ≠ j2 ∧ j1 ≠ j2) :
    let G := varGadget base [j0, j1, j2]
    G.Nodup ∧
    G.length = 7 * [j0, j1, j2].length ∧
    (∀ S ∈ G, S.length = 3 ∧ S.Nodup) ∧
    (∀ t < 6 * [j0, j1, j2].length, G.countP (fun S ↦ decide (base + t ∈ S)) = 3) ∧
    (∀ u, u ∈ G.flatten →
      (∃ j ∈ [j0, j1, j2], ∃ c < 3, u = 3 * j + c) ∨
        (base ≤ u ∧ u < base + 6 * [j0, j1, j2].length)) ∧
    (∀ j ∈ [j0, j1, j2], ∀ c < 3, G.countP (fun S ↦ decide (3 * j + c ∈ S)) = 1) ∧
    (∀ u, u < base → (∀ j ∈ [j0, j1, j2], ∀ c < 3, u ≠ 3 * j + c) →
      G.countP (fun S ↦ decide (u ∈ S)) = 0) ∧
    (∀ u, base + 6 * [j0, j1, j2].length ≤ u → G.countP (fun S ↦ decide (u ∈ S)) = 0) := by
  simp only [varGadget_three, gadget3, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceMul]
  refine ⟨?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, List.cons.injEq]
    grind
  · intro S hS
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [List.length_cons, List.length_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, true_and]; grind)
  · intro k hk
    interval_cases k <;>
      ((repeat first | rw [cp1 (by omega)] | rw [cp2 (by omega)] | rw [cp3 (by omega)] |
          rw [cp0 (by omega) (by omega) (by omega)]);
       rw [List.countP_nil])
  · intro u hu
    rw [List.mem_flatten] at hu
    rcases hu with ⟨S, hS, huS⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact flatten_T3 (by simp : j0 ∈ [j0, j1, j2]) (by omega : 0 < 3) (by omega)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ huS
    · exact flatten_T3 (by simp : j0 ∈ [j0, j1, j2]) (by omega : 1 < 3) (by omega)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ huS
    · exact flatten_T3 (by simp : j0 ∈ [j0, j1, j2]) (by omega : 2 < 3) (by omega)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ huS
    · exact flatten_T3 (by simp : j1 ∈ [j0, j1, j2]) (by omega : 0 < 3) (by omega)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ huS
    · exact flatten_T3 (by simp : j1 ∈ [j0, j1, j2]) (by omega : 1 < 3) (by omega)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ huS
    · exact flatten_T3 (by simp : j1 ∈ [j0, j1, j2]) (by omega : 2 < 3) (by omega)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ huS
    · exact flatten_T3 (by simp : j2 ∈ [j0, j1, j2]) (by omega : 0 < 3) (by omega)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ huS
    · exact flatten_T3 (by simp : j2 ∈ [j0, j1, j2]) (by omega : 1 < 3) (by omega)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ huS
    · exact flatten_T3 (by simp : j2 ∈ [j0, j1, j2]) (by omega : 2 < 3) (by omega)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ huS
    all_goals
      exact Or.inr (flatten_FG3 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ huS)
  · have hcl := countP_varGadget_clause (base := base) (O := [j0, j1, j2])
      (by simp) (by simp [hnd]) (by
        intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl <;> omega)
    simpa only [varGadget_three, gadget3] using hcl.1
  · have hcl := countP_varGadget_clause (base := base) (O := [j0, j1, j2])
      (by simp) (by simp [hnd]) (by
        intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl <;> omega)
    simpa only [varGadget_three, gadget3] using hcl.2.1
  · have hcl := countP_varGadget_clause (base := base) (O := [j0, j1, j2])
      (by simp) (by simp [hnd]) (by
        intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl <;> omega)
    simpa only [varGadget_three, gadget3, List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceMul] using hcl.2.2

/-- Structural invariants of `varGadget base O` for `1 ≤ O.length ≤ 3`: `Nodup`, exact length,
3-uniformity, 3-regularity on internal elements, and unit/zero counts on clause copies. -/
theorem varGadget_props {base : ℕ} {O : List ℕ}
    (hO_len : 1 ≤ O.length ∧ O.length ≤ 3) (hO_nd : O.Nodup)
    (hO_lt : ∀ j ∈ O, 3 * j + 2 < base) :
    let G := varGadget base O
    G.Nodup ∧
    G.length = 7 * O.length ∧
    (∀ S ∈ G, S.length = 3 ∧ S.Nodup) ∧
    (∀ t < 6 * O.length, G.countP (fun S ↦ decide (base + t ∈ S)) = 3) ∧
    (∀ u, u ∈ G.flatten →
      (∃ j ∈ O, ∃ c < 3, u = 3 * j + c) ∨ (base ≤ u ∧ u < base + 6 * O.length)) ∧
    (∀ j ∈ O, ∀ c < 3, G.countP (fun S ↦ decide (3 * j + c ∈ S)) = 1) ∧
    (∀ u, u < base → (∀ j ∈ O, ∀ c < 3, u ≠ 3 * j + c) →
      G.countP (fun S ↦ decide (u ∈ S)) = 0) ∧
    (∀ u, base + 6 * O.length ≤ u → G.countP (fun S ↦ decide (u ∈ S)) = 0) := by
  rcases O with _ | ⟨j0, _ | ⟨j1, _ | ⟨j2, _ | ⟨j3, t⟩⟩⟩⟩
  · simp at hO_len
  · have h0 : 3 * j0 + 2 < base := hO_lt j0 (by simp)
    simp only [varGadget, gadget1, List.length_cons, List.length_nil, Nat.reduceAdd,
      beq_self_eq_true,
      ↓reduceIte, List.getD_cons_zero, mul_one]
    refine ⟨?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, List.cons.injEq]
      grind
    · intro S hS
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
      rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (simp only [List.length_cons, List.length_nil, List.nodup_cons, List.mem_cons,
          List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, true_and]; grind)
    · intro k hk
      interval_cases k <;>
        ((repeat first | rw [cp1 (by omega)] | rw [cp2 (by omega)] | rw [cp3 (by omega)] |
            rw [cp0 (by omega) (by omega) (by omega)]);
         rw [List.countP_nil])
    · intro u hu
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with ((rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl) |
        (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl)) <;>
        first | exact Or.inl ⟨j0, by simp, 0, by omega, by omega⟩
              | exact Or.inl ⟨j0, by simp, 1, by omega, by omega⟩
              | exact Or.inl ⟨j0, by simp, 2, by omega, by omega⟩
              | exact Or.inr ⟨by omega, by omega⟩
    · simpa only [varGadget, gadget1, List.length_cons, List.length_nil, Nat.reduceAdd,
        beq_self_eq_true, ↓reduceIte, List.getD_cons_zero] using
        (countP_varGadget_clause hO_len hO_nd hO_lt).1
    · simpa only [varGadget, gadget1, List.length_cons, List.length_nil, Nat.reduceAdd,
        beq_self_eq_true, ↓reduceIte, List.getD_cons_zero] using
        (countP_varGadget_clause hO_len hO_nd hO_lt).2.1
    · simpa only [varGadget, gadget1, List.length_cons, List.length_nil, Nat.reduceAdd,
        beq_self_eq_true, ↓reduceIte, List.getD_cons_zero, mul_one] using
        (countP_varGadget_clause hO_len hO_nd hO_lt).2.2
  · have h0 : 3 * j0 + 2 < base := hO_lt j0 (by simp)
    have h1 : 3 * j1 + 2 < base := hO_lt j1 (by simp)
    have h01 : j0 ≠ j1 := by simpa [List.nodup_cons] using hO_nd
    simp only [varGadget_two, gadget2, List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceMul]
    refine ⟨?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, List.cons.injEq]
      grind
    · intro S hS
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
      rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
        (simp only [List.length_cons, List.length_nil, List.nodup_cons, List.mem_cons,
          List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, true_and]; grind)
    · intro k hk
      interval_cases k <;>
        ((repeat first | rw [cp1 (by omega)] | rw [cp2 (by omega)] | rw [cp3 (by omega)] |
            rw [cp0 (by omega) (by omega) (by omega)]);
         rw [List.countP_nil])
    · intro u hu
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with ((rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl) |
        (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl) |
        (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl) |
        (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl)) <;>
        first | exact Or.inl ⟨j0, by simp, 0, by omega, by omega⟩
              | exact Or.inl ⟨j0, by simp, 1, by omega, by omega⟩
              | exact Or.inl ⟨j0, by simp, 2, by omega, by omega⟩
              | exact Or.inl ⟨j1, by simp, 0, by omega, by omega⟩
              | exact Or.inl ⟨j1, by simp, 1, by omega, by omega⟩
              | exact Or.inl ⟨j1, by simp, 2, by omega, by omega⟩
              | exact Or.inr ⟨by omega, by omega⟩
    · simpa only [varGadget_two, gadget2] using (countP_varGadget_clause hO_len hO_nd hO_lt).1
    · simpa only [varGadget_two, gadget2] using (countP_varGadget_clause hO_len hO_nd hO_lt).2.1
    · simpa only [varGadget_two, gadget2, List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceMul] using (countP_varGadget_clause hO_len hO_nd hO_lt).2.2
  · obtain ⟨h0, h1, h2, hnd⟩ := unpack_triple_occ hO_nd hO_lt
    exact varGadget_props_3 h0 h1 h2 hnd
  · simp at hO_len; omega

private lemma filter_card_eq_one_of_unique {Dg : Finset (List ℕ)} {x : ℕ} {T : List ℕ}
    (hTD : T ∈ Dg) (hxT : x ∈ T) (honly : ∀ S ∈ Dg, x ∈ S → S = T) :
    (Dg.filter (x ∈ ·)).card = 1 := by
  have heq : Dg.filter (x ∈ ·) = {T} := by
    ext S; simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun ⟨h1, h2⟩ ↦ honly S h1 h2, fun h ↦ h ▸ ⟨hTD, hxT⟩⟩
  rw [heq, Finset.card_singleton]

private lemma varGadget_forcing_2 {base j0 j1 : ℕ} {D : Finset (List ℕ)}
    (h0 : 3 * j0 + 2 < base) (h1 : 3 * j1 + 2 < base) (h01 : j0 ≠ j1)
    (hD : ∀ t < 6 * [j0, j1].length,
      ((D.filter fun S ↦ S ∈ varGadget base [j0, j1]).filter (base + t ∈ ·)).card = 1) :
    (∀ j ∈ [j0, j1], ∀ c < 3,
      ((D.filter fun S ↦ S ∈ varGadget base [j0, j1]).filter (3 * j + c ∈ ·)).card = 1) ∨
    (∀ j ∈ [j0, j1], ∀ c < 3,
      ((D.filter fun S ↦ S ∈ varGadget base [j0, j1]).filter (3 * j + c ∈ ·)).card = 0) := by
  let Dg := D.filter fun S ↦ S ∈ varGadget base [j0, j1]
  let T0 : List ℕ := [3 * j0, base, base + 1]
  let T1 : List ℕ := [3 * j0 + 1, base + 2, base + 3]
  let T2 : List ℕ := [3 * j0 + 2, base + 4, base + 5]
  let T3 : List ℕ := [3 * j1, base + 6, base + 7]
  let T4 : List ℕ := [3 * j1 + 1, base + 8, base + 9]
  let T5 : List ℕ := [3 * j1 + 2, base + 10, base + 11]
  let F0 : List ℕ := [base, base + 7, base + 8]
  let F1 : List ℕ := [base + 1, base + 2, base + 9]
  let F2 : List ℕ := [base + 3, base + 4, base + 10]
  let F3 : List ℕ := [base + 5, base + 6, base + 11]
  let G0 : List ℕ := [base, base + 3, base + 9]
  let G1 : List ℕ := [base + 2, base + 5, base + 10]
  let G2 : List ℕ := [base + 4, base + 7, base + 11]
  let G3 : List ℕ := [base + 6, base + 1, base + 8]
  have hvg : varGadget base [j0, j1] =
      [T0, T1, T2, T3, T4, T5, F0, F1, F2, F3, G0, G1, G2, G3] := rfl
  have hin : ∀ k < 12, (Dg.filter (base + k ∈ ·)).card = 1 := fun k hk ↦ hD k (by simpa using hk)
  have hDg_sub : ∀ S ∈ Dg, S = T0 ∨ S = T1 ∨ S = T2 ∨ S = T3 ∨ S = T4 ∨ S = T5 ∨
      S = F0 ∨ S = F1 ∨ S = F2 ∨ S = F3 ∨ S = G0 ∨ S = G1 ∨ S = G2 ∨ S = G3 := by
    intro S hS; have := (Finset.mem_filter.mp hS).2; simpa [hvg] using this
  have huniq : ∀ k < 12, ∀ S ∈ Dg, ∀ U ∈ Dg, base + k ∈ S → base + k ∈ U → S = U := by
    intro k hk S hS U hU hkS hkU
    obtain ⟨Z, hZ⟩ := Finset.card_eq_one.mp (hin k hk)
    have h1' : S ∈ ({Z} : Finset _) := hZ ▸ Finset.mem_filter.mpr ⟨hS, hkS⟩
    have h2' : U ∈ ({Z} : Finset _) := hZ ▸ Finset.mem_filter.mpr ⟨hU, hkU⟩
    rw [Finset.mem_singleton.mp h1', Finset.mem_singleton.mp h2']
  have hcov_k : ∀ k < 12, ∃ S ∈ Dg, base + k ∈ S := fun k hk ↦ by
    obtain ⟨S, hS⟩ := Finset.card_eq_one.mp (hin k hk)
    have hm : S ∈ Dg.filter (base + k ∈ ·) := hS ▸ Finset.mem_singleton_self S
    exact ⟨S, (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2⟩
  have hdiff : ∀ (k : ℕ) (S U : List ℕ), k < 12 → S ∈ Dg → U ∈ Dg →
      base + k ∈ S → base + k ∈ U → S ≠ U → False :=
    fun k S U hk hS hU hkS hkU hne ↦ hne (huniq k hk S hS U hU hkS hkU)
  have ha0 : T0 ∈ Dg ∨ F0 ∈ Dg ∨ G0 ∈ Dg := by
    obtain ⟨S, hSD, hkS⟩ := hcov_k 0 (by omega)
    rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
      (try exact Or.inl hSD) <;> (try exact Or.inr (Or.inl hSD)) <;>
      (try exact Or.inr (Or.inr hSD)) <;>
      (simp only [T1, T2, T3, T4, T5, F1, F2, F3, G1, G2, G3, List.mem_cons, List.not_mem_nil,
        or_false] at hkS; omega)
  have hb0 : T0 ∈ Dg ∨ F1 ∈ Dg ∨ G3 ∈ Dg := by
    obtain ⟨S, hSD, hkS⟩ := hcov_k 1 (by omega)
    rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
      (try exact Or.inl hSD) <;> (try exact Or.inr (Or.inl hSD)) <;>
      (try exact Or.inr (Or.inr hSD)) <;>
      (simp only [T1, T2, T3, T4, T5, F0, F2, F3, G0, G1, G2, List.mem_cons, List.not_mem_nil,
        or_false] at hkS; omega)
  have ha1 : T1 ∈ Dg ∨ F1 ∈ Dg ∨ G1 ∈ Dg := by
    obtain ⟨S, hSD, hkS⟩ := hcov_k 2 (by omega)
    rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
      (try exact Or.inl hSD) <;> (try exact Or.inr (Or.inl hSD)) <;>
      (try exact Or.inr (Or.inr hSD)) <;>
      (simp only [T0, T2, T3, T4, T5, F0, F2, F3, G0, G2, G3, List.mem_cons, List.not_mem_nil,
        or_false] at hkS; omega)
  have hb1 : T1 ∈ Dg ∨ F2 ∈ Dg ∨ G0 ∈ Dg := by
    obtain ⟨S, hSD, hkS⟩ := hcov_k 3 (by omega)
    rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
      (try exact Or.inl hSD) <;> (try exact Or.inr (Or.inl hSD)) <;>
      (try exact Or.inr (Or.inr hSD)) <;>
      (simp only [T0, T2, T3, T4, T5, F0, F1, F3, G1, G2, G3, List.mem_cons, List.not_mem_nil,
        or_false] at hkS; omega)
  have ha2 : T2 ∈ Dg ∨ F2 ∈ Dg ∨ G2 ∈ Dg := by
    obtain ⟨S, hSD, hkS⟩ := hcov_k 4 (by omega)
    rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
      (try exact Or.inl hSD) <;> (try exact Or.inr (Or.inl hSD)) <;>
      (try exact Or.inr (Or.inr hSD)) <;>
      (simp only [T0, T1, T3, T4, T5, F0, F1, F3, G0, G1, G3, List.mem_cons, List.not_mem_nil,
        or_false] at hkS; omega)
  have hb2 : T2 ∈ Dg ∨ F3 ∈ Dg ∨ G1 ∈ Dg := by
    obtain ⟨S, hSD, hkS⟩ := hcov_k 5 (by omega)
    rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
      (try exact Or.inl hSD) <;> (try exact Or.inr (Or.inl hSD)) <;>
      (try exact Or.inr (Or.inr hSD)) <;>
      (simp only [T0, T1, T3, T4, T5, F0, F1, F2, G0, G2, G3, List.mem_cons, List.not_mem_nil,
        or_false] at hkS; omega)
  have ha3 : T3 ∈ Dg ∨ F3 ∈ Dg ∨ G3 ∈ Dg := by
    obtain ⟨S, hSD, hkS⟩ := hcov_k 6 (by omega)
    rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
      (try exact Or.inl hSD) <;> (try exact Or.inr (Or.inl hSD)) <;>
      (try exact Or.inr (Or.inr hSD)) <;>
      (simp only [T0, T1, T2, T4, T5, F0, F1, F2, G0, G1, G2, List.mem_cons, List.not_mem_nil,
        or_false] at hkS; omega)
  have hb3 : T3 ∈ Dg ∨ F0 ∈ Dg ∨ G2 ∈ Dg := by
    obtain ⟨S, hSD, hkS⟩ := hcov_k 7 (by omega)
    rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
      (try exact Or.inl hSD) <;> (try exact Or.inr (Or.inl hSD)) <;>
      (try exact Or.inr (Or.inr hSD)) <;>
      (simp only [T0, T1, T2, T4, T5, F1, F2, F3, G0, G1, G3, List.mem_cons, List.not_mem_nil,
        or_false] at hkS; omega)
  have ha4 : T4 ∈ Dg ∨ F0 ∈ Dg ∨ G3 ∈ Dg := by
    obtain ⟨S, hSD, hkS⟩ := hcov_k 8 (by omega)
    rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
      (try exact Or.inl hSD) <;> (try exact Or.inr (Or.inl hSD)) <;>
      (try exact Or.inr (Or.inr hSD)) <;>
      (simp only [T0, T1, T2, T3, T5, F1, F2, F3, G0, G1, G2, List.mem_cons, List.not_mem_nil,
        or_false] at hkS; omega)
  have hb4 : T4 ∈ Dg ∨ F1 ∈ Dg ∨ G0 ∈ Dg := by
    obtain ⟨S, hSD, hkS⟩ := hcov_k 9 (by omega)
    rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
      (try exact Or.inl hSD) <;> (try exact Or.inr (Or.inl hSD)) <;>
      (try exact Or.inr (Or.inr hSD)) <;>
      (simp only [T0, T1, T2, T3, T5, F0, F2, F3, G1, G2, G3, List.mem_cons, List.not_mem_nil,
        or_false] at hkS; omega)
  have ha5 : T5 ∈ Dg ∨ F2 ∈ Dg ∨ G1 ∈ Dg := by
    obtain ⟨S, hSD, hkS⟩ := hcov_k 10 (by omega)
    rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
      (try exact Or.inl hSD) <;> (try exact Or.inr (Or.inl hSD)) <;>
      (try exact Or.inr (Or.inr hSD)) <;>
      (simp only [T0, T1, T2, T3, T4, F0, F1, F3, G0, G2, G3, List.mem_cons, List.not_mem_nil,
        or_false] at hkS; omega)
  have hb5 : T5 ∈ Dg ∨ F3 ∈ Dg ∨ G2 ∈ Dg := by
    obtain ⟨S, hSD, hkS⟩ := hcov_k 11 (by omega)
    rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
      (try exact Or.inl hSD) <;> (try exact Or.inr (Or.inl hSD)) <;>
      (try exact Or.inr (Or.inr hSD)) <;>
      (simp only [T0, T1, T2, T3, T4, F0, F1, F2, G0, G1, G3, List.mem_cons, List.not_mem_nil,
        or_false] at hkS; omega)
  have h_exc :
      (G0 ∈ Dg → T1 ∉ Dg ∧ F1 ∉ Dg) ∧ (G1 ∈ Dg → T2 ∉ Dg ∧ F2 ∉ Dg) ∧
      (G2 ∈ Dg → T3 ∉ Dg ∧ F3 ∉ Dg) ∧ (G3 ∈ Dg → T0 ∉ Dg ∧ F0 ∉ Dg) ∧
      (G0 ∈ Dg → T0 ∉ Dg ∧ F0 ∉ Dg ∧ T4 ∉ Dg) ∧
      (G1 ∈ Dg → T1 ∉ Dg ∧ F1 ∉ Dg ∧ T5 ∉ Dg) ∧
      (G2 ∈ Dg → T2 ∉ Dg ∧ F2 ∉ Dg ∧ T5 ∉ Dg) ∧
      (G3 ∈ Dg → T3 ∉ Dg ∧ F3 ∉ Dg ∧ T4 ∉ Dg) ∧
      (T0 ∈ Dg → F0 ∉ Dg ∧ F1 ∉ Dg) ∧ (T1 ∈ Dg → F1 ∉ Dg ∧ F2 ∉ Dg) ∧
      (T2 ∈ Dg → F2 ∉ Dg ∧ F3 ∉ Dg) ∧ (T3 ∈ Dg → F3 ∉ Dg ∧ F0 ∉ Dg) ∧
      (T4 ∈ Dg → F0 ∉ Dg ∧ F1 ∉ Dg) ∧ (T5 ∈ Dg → F2 ∉ Dg ∧ F3 ∉ Dg) := by
    refine ⟨fun hG0 ↦ ⟨fun h ↦ hdiff 3 G0 T1 (by omega) hG0 h (by simp [G0]) (by simp [T1])
          (by simp [G0, T1]),
        fun h ↦ hdiff 9 G0 F1 (by omega) hG0 h (by simp [G0]) (by simp [F1]) (by simp [G0, F1])⟩,
      fun hG1 ↦ ⟨fun h ↦ hdiff 5 G1 T2 (by omega) hG1 h (by simp [G1]) (by simp [T2])
        (by simp [G1, T2]),
        fun h ↦ hdiff 10 G1 F2 (by omega) hG1 h (by simp [G1]) (by simp [F2]) (by simp [G1, F2])⟩,
      fun hG2 ↦ ⟨fun h ↦ hdiff 7 G2 T3 (by omega) hG2 h (by simp [G2]) (by simp [T3])
        (by simp [G2, T3]),
        fun h ↦ hdiff 11 G2 F3 (by omega) hG2 h (by simp [G2]) (by simp [F3]) (by simp [G2, F3])⟩,
      fun hG3 ↦ ⟨fun h ↦ hdiff 1 G3 T0 (by omega) hG3 h (by simp [G3]) (by simp [T0])
        (by simp [G3, T0]),
        fun h ↦ hdiff 8 G3 F0 (by omega) hG3 h (by simp [G3]) (by simp [F0]) (by simp [G3, F0])⟩,
      fun hG0 ↦ ⟨fun h ↦ hdiff 0 G0 T0 (by omega) hG0 h (by simp [G0]) (by simp [T0])
        (by simp [G0, T0]),
        fun h ↦ hdiff 0 G0 F0 (by omega) hG0 h (by simp [G0]) (by simp [F0]) (by simp [G0, F0]),
        fun h ↦ hdiff 9 G0 T4 (by omega) hG0 h (by simp [G0]) (by simp [T4]) (by simp [G0, T4])⟩,
      fun hG1 ↦ ⟨fun h ↦ hdiff 2 G1 T1 (by omega) hG1 h (by simp [G1]) (by simp [T1])
        (by simp [G1, T1]),
        fun h ↦ hdiff 2 G1 F1 (by omega) hG1 h (by simp [G1]) (by simp [F1]) (by simp [G1, F1]),
        fun h ↦ hdiff 10 G1 T5 (by omega) hG1 h (by simp [G1]) (by simp [T5]) (by simp [G1, T5])⟩,
      fun hG2 ↦ ⟨fun h ↦ hdiff 4 G2 T2 (by omega) hG2 h (by simp [G2]) (by simp [T2])
        (by simp [G2, T2]),
        fun h ↦ hdiff 4 G2 F2 (by omega) hG2 h (by simp [G2]) (by simp [F2]) (by simp [G2, F2]),
        fun h ↦ hdiff 11 G2 T5 (by omega) hG2 h (by simp [G2]) (by simp [T5]) (by simp [G2, T5])⟩,
      fun hG3 ↦ ⟨fun h ↦ hdiff 6 G3 T3 (by omega) hG3 h (by simp [G3]) (by simp [T3])
        (by simp [G3, T3]),
        fun h ↦ hdiff 6 G3 F3 (by omega) hG3 h (by simp [G3]) (by simp [F3]) (by simp [G3, F3]),
        fun h ↦ hdiff 8 G3 T4 (by omega) hG3 h (by simp [G3]) (by simp [T4]) (by simp [G3, T4])⟩,
      fun hT0 ↦ ⟨fun h ↦ hdiff 0 T0 F0 (by omega) hT0 h (by simp [T0]) (by simp [F0])
        (by simp [T0, F0]),
        fun h ↦ hdiff 1 T0 F1 (by omega) hT0 h (by simp [T0]) (by simp [F1]) (by simp [T0, F1])⟩,
      fun hT1 ↦ ⟨fun h ↦ hdiff 2 T1 F1 (by omega) hT1 h (by simp [T1]) (by simp [F1])
        (by simp [T1, F1]),
        fun h ↦ hdiff 3 T1 F2 (by omega) hT1 h (by simp [T1]) (by simp [F2]) (by simp [T1, F2])⟩,
      fun hT2 ↦ ⟨fun h ↦ hdiff 4 T2 F2 (by omega) hT2 h (by simp [T2]) (by simp [F2])
        (by simp [T2, F2]),
        fun h ↦ hdiff 5 T2 F3 (by omega) hT2 h (by simp [T2]) (by simp [F3]) (by simp [T2, F3])⟩,
      fun hT3 ↦ ⟨fun h ↦ hdiff 6 T3 F3 (by omega) hT3 h (by simp [T3]) (by simp [F3])
        (by simp [T3, F3]),
        fun h ↦ hdiff 7 T3 F0 (by omega) hT3 h (by simp [T3]) (by simp [F0]) (by simp [T3, F0])⟩,
      fun hT4 ↦ ⟨fun h ↦ hdiff 8 T4 F0 (by omega) hT4 h (by simp [T4]) (by simp [F0])
        (by simp [T4, F0]),
        fun h ↦ hdiff 9 T4 F1 (by omega) hT4 h (by simp [T4]) (by simp [F1]) (by simp [T4, F1])⟩,
      fun hT5 ↦ ⟨fun h ↦ hdiff 10 T5 F2 (by omega) hT5 h (by simp [T5]) (by simp [F2])
        (by simp [T5, F2]),
        fun h ↦ hdiff 11 T5 F3 (by omega) hT5 h (by simp [T5]) (by simp [F3]) (by simp [T5, F3])⟩⟩
  have hcase : (T0 ∈ Dg ∧ T1 ∈ Dg ∧ T2 ∈ Dg ∧ T3 ∈ Dg ∧ T4 ∈ Dg ∧ T5 ∈ Dg) ∨
      (T0 ∉ Dg ∧ T1 ∉ Dg ∧ T2 ∉ Dg ∧ T3 ∉ Dg ∧ T4 ∉ Dg ∧ T5 ∉ Dg) := by
    obtain ⟨hG0, hG1, hG2, hG3, hG0', hG1', hG2', hG3', hT0e, hT1e, hT2e, hT3e, hT4e, hT5e⟩ :=
      h_exc
    have h01 : T0 ∈ Dg → T1 ∈ Dg := fun h ↦ by
      have hng1 : G1 ∉ Dg := fun hg ↦
        (hb1.resolve_left (hG1' hg).1).elim (hG1 hg).2 (fun hg0 ↦ (hG0' hg0).1 h)
      exact ha1.resolve_right (Or.elim · (hT0e h).2 hng1)
    have h12 : T1 ∈ Dg → T2 ∈ Dg := fun h ↦ by
      have hng2 : G2 ∉ Dg := fun hg ↦
        (hb2.resolve_left (hG2' hg).1).elim (hG2 hg).2 (fun hg1 ↦ (hG1' hg1).1 h)
      exact ha2.resolve_right (Or.elim · (hT1e h).2 hng2)
    have h23 : T2 ∈ Dg → T3 ∈ Dg := fun h ↦ by
      have hng3 : G3 ∉ Dg := fun hg ↦
        (hb3.resolve_left (hG3' hg).1).elim (hG3 hg).2 (fun hg2 ↦ (hG2' hg2).1 h)
      exact ha3.resolve_right (Or.elim · (hT2e h).2 hng3)
    have h30 : T3 ∈ Dg → T0 ∈ Dg := fun h ↦ by
      have hng0 : G0 ∉ Dg := fun hg ↦
        (hb0.resolve_left (hG0' hg).1).elim (hG0 hg).2 (fun hg3 ↦ (hG3' hg3).1 h)
      exact ha0.resolve_right (Or.elim · (hT3e h).2 hng0)
    have h40 : T4 ∈ Dg → T0 ∈ Dg := fun h ↦
      ha0.resolve_right (Or.elim · (hT4e h).1 (fun hg ↦ (hG0' hg).2.2 h))
    have h52 : T5 ∈ Dg → T2 ∈ Dg := fun h ↦
      ha2.resolve_right (Or.elim · (hT5e h).1 (fun hg ↦ (hG2' hg).2.2 h))
    by_cases hT0 : T0 ∈ Dg
    · have hT1 := h01 hT0; have hT2 := h12 hT1; have hT3 := h23 hT2
      have hT4 : T4 ∈ Dg := ha4.resolve_right (Or.elim · (hT0e hT0).1 (fun hg ↦ (hG3 hg).1 hT0))
      have hT5 : T5 ∈ Dg := ha5.resolve_right (Or.elim · (hT1e hT1).2 (fun hg ↦ (hG1' hg).1 hT1))
      exact Or.inl ⟨hT0, hT1, hT2, hT3, hT4, hT5⟩
    · have hT3 : T3 ∉ Dg := fun h ↦ hT0 (h30 h)
      have hT2 : T2 ∉ Dg := fun h ↦ hT3 (h23 h)
      have hT1 : T1 ∉ Dg := fun h ↦ hT2 (h12 h)
      exact Or.inr ⟨hT0, hT1, hT2, hT3, fun h ↦ hT0 (h40 h), fun h ↦ hT2 (h52 h)⟩
  rcases hcase with ⟨hT0, hT1, hT2, hT3, hT4, hT5⟩ | ⟨hT0, hT1, hT2, hT3, hT4, hT5⟩
  · have hnone_fg : ∀ S ∈ Dg, ∀ x < base, x ∈ S →
        S = T0 ∨ S = T1 ∨ S = T2 ∨ S = T3 ∨ S = T4 ∨ S = T5 := by
      intro S hSD x hx hxS
      rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      all_goals (simp [F0, F1, F2, F3, G0, G1, G2, G3] at hxS; omega)
    refine Or.inl fun j hj c hc ↦ ?_
    rcases (by simpa using hj : j = j0 ∨ j = j1) with rfl | rfl
    · interval_cases c
      · exact filter_card_eq_one_of_unique hT0 (by simp [T0]) fun S hSD hxS ↦ by
          rcases hnone_fg S hSD _ (by omega) hxS with rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | rfl
            | (dsimp [T0, T1, T2, T3, T4, T5] at hxS
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS; omega)
      · exact filter_card_eq_one_of_unique hT1 (by simp [T1]) fun S hSD hxS ↦ by
          rcases hnone_fg S hSD _ (by omega) hxS with rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | rfl
            | (dsimp [T0, T1, T2, T3, T4, T5] at hxS
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS; omega)
      · exact filter_card_eq_one_of_unique hT2 (by simp [T2]) fun S hSD hxS ↦ by
          rcases hnone_fg S hSD _ (by omega) hxS with rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | rfl
            | (dsimp [T0, T1, T2, T3, T4, T5] at hxS
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS; omega)
    · interval_cases c
      · exact filter_card_eq_one_of_unique hT3 (by simp [T3]) fun S hSD hxS ↦ by
          rcases hnone_fg S hSD _ (by omega) hxS with rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | rfl
            | (dsimp [T0, T1, T2, T3, T4, T5] at hxS
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS; omega)
      · exact filter_card_eq_one_of_unique hT4 (by simp [T4]) fun S hSD hxS ↦ by
          rcases hnone_fg S hSD _ (by omega) hxS with rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | rfl
            | (dsimp [T0, T1, T2, T3, T4, T5] at hxS
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS; omega)
      · exact filter_card_eq_one_of_unique hT5 (by simp [T5]) fun S hSD hxS ↦ by
          rcases hnone_fg S hSD _ (by omega) hxS with rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | rfl
            | (dsimp [T0, T1, T2, T3, T4, T5] at hxS
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS; omega)
  · refine Or.inr fun j hj c hc ↦ ?_
    have hlt : 3 * j + c < base := by
      rcases (by simpa using hj : j = j0 ∨ j = j1) with rfl | rfl <;> omega
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro S hSD hxS
    rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact hT0 hSD
    · exact hT1 hSD
    · exact hT2 hSD
    · exact hT3 hSD
    · exact hT4 hSD
    · exact hT5 hSD
    all_goals (simp [F0, F1, F2, F3, G0, G1, G2, G3] at hxS; omega)

private lemma varGadget_forcing_3 {base j0 j1 j2 : ℕ} {D : Finset (List ℕ)}
    (h0 : 3 * j0 + 2 < base) (h1 : 3 * j1 + 2 < base) (h2 : 3 * j2 + 2 < base)
    (hnd : j0 ≠ j1 ∧ j0 ≠ j2 ∧ j1 ≠ j2)
    (hD : ∀ t < 6 * [j0, j1, j2].length,
      ((D.filter fun S ↦ S ∈ varGadget base [j0, j1, j2]).filter (base + t ∈ ·)).card = 1) :
    (∀ j ∈ [j0, j1, j2], ∀ c < 3,
      ((D.filter fun S ↦ S ∈ varGadget base [j0, j1, j2]).filter (3 * j + c ∈ ·)).card = 1) ∨
    (∀ j ∈ [j0, j1, j2], ∀ c < 3,
      ((D.filter fun S ↦ S ∈ varGadget base [j0, j1, j2]).filter (3 * j + c ∈ ·)).card = 0) := by
  let Dg := D.filter fun S ↦ S ∈ varGadget base [j0, j1, j2]
  let T0 : List ℕ := [3 * j0, base, base + 1]
  let T1 : List ℕ := [3 * j0 + 1, base + 2, base + 3]
  let T2 : List ℕ := [3 * j0 + 2, base + 4, base + 5]
  let T3 : List ℕ := [3 * j1, base + 6, base + 7]
  let T4 : List ℕ := [3 * j1 + 1, base + 8, base + 9]
  let T5 : List ℕ := [3 * j1 + 2, base + 10, base + 11]
  let T6 : List ℕ := [3 * j2, base + 12, base + 13]
  let T7 : List ℕ := [3 * j2 + 1, base + 14, base + 15]
  let T8 : List ℕ := [3 * j2 + 2, base + 16, base + 17]
  let F0 : List ℕ := [base, base + 11, base + 12]
  let F1 : List ℕ := [base + 1, base + 2, base + 13]
  let F2 : List ℕ := [base + 3, base + 4, base + 14]
  let F3 : List ℕ := [base + 5, base + 6, base + 15]
  let F4 : List ℕ := [base + 7, base + 8, base + 16]
  let F5 : List ℕ := [base + 9, base + 10, base + 17]
  let G0 : List ℕ := [base, base + 3, base + 13]
  let G1 : List ℕ := [base + 2, base + 5, base + 14]
  let G2 : List ℕ := [base + 4, base + 7, base + 15]
  let G3 : List ℕ := [base + 6, base + 9, base + 16]
  let G4 : List ℕ := [base + 8, base + 11, base + 17]
  let G5 : List ℕ := [base + 10, base + 1, base + 12]
  have hvg : varGadget base [j0, j1, j2] =
      [T0, T1, T2, T3, T4, T5, T6, T7, T8, F0, F1, F2, F3, F4, F5, G0, G1, G2, G3, G4, G5] := rfl
  have hin : ∀ k < 18, (Dg.filter (base + k ∈ ·)).card = 1 := fun k hk ↦ hD k (by simpa using hk)
  have hDg_sub : ∀ S ∈ Dg, S = T0 ∨ S = T1 ∨ S = T2 ∨ S = T3 ∨ S = T4 ∨ S = T5 ∨
      S = T6 ∨ S = T7 ∨ S = T8 ∨ S = F0 ∨ S = F1 ∨ S = F2 ∨ S = F3 ∨ S = F4 ∨ S = F5 ∨
      S = G0 ∨ S = G1 ∨ S = G2 ∨ S = G3 ∨ S = G4 ∨ S = G5 := by
    intro S hS; have := (Finset.mem_filter.mp hS).2; simpa [hvg] using this
  have huniq : ∀ k < 18, ∀ S ∈ Dg, ∀ U ∈ Dg, base + k ∈ S → base + k ∈ U → S = U := by
    intro k hk S hS U hU hkS hkU
    obtain ⟨Z, hZ⟩ := Finset.card_eq_one.mp (hin k hk)
    have h1' : S ∈ ({Z} : Finset _) := hZ ▸ Finset.mem_filter.mpr ⟨hS, hkS⟩
    have h2' : U ∈ ({Z} : Finset _) := hZ ▸ Finset.mem_filter.mpr ⟨hU, hkU⟩
    rw [Finset.mem_singleton.mp h1', Finset.mem_singleton.mp h2']
  have hdiff : ∀ (k : ℕ) (S U : List ℕ), k < 18 → S ∈ Dg → U ∈ Dg →
      base + k ∈ S → base + k ∈ U → S ≠ U → False :=
    fun k S U hk hS hU hkS hkU hne ↦ hne (huniq k hk S hS U hU hkS hkU)
  have hcl : ∀ (k : ℕ), k < 18 → ∀ {A B C : List ℕ},
      (∀ S ∈ Dg, base + k ∈ S → S = A ∨ S = B ∨ S = C) → A ∈ Dg ∨ B ∈ Dg ∨ C ∈ Dg := by
    intro k hk A B C honly
    obtain ⟨S, hS⟩ := Finset.card_eq_one.mp (hin k hk)
    have hm : S ∈ Dg.filter (base + k ∈ ·) := hS ▸ Finset.mem_singleton_self S
    rcases Finset.mem_filter.mp hm with ⟨hSD, hkS⟩
    rcases honly S hSD hkS with rfl | rfl | rfl
    · exact Or.inl hSD
    · exact Or.inr (Or.inl hSD)
    · exact Or.inr (Or.inr hSD)
  have hdisj :
      (T0 ∈ Dg ∨ F0 ∈ Dg ∨ G0 ∈ Dg) ∧ (T0 ∈ Dg ∨ F1 ∈ Dg ∨ G5 ∈ Dg) ∧
      (T1 ∈ Dg ∨ F1 ∈ Dg ∨ G1 ∈ Dg) ∧ (T1 ∈ Dg ∨ F2 ∈ Dg ∨ G0 ∈ Dg) ∧
      (T2 ∈ Dg ∨ F2 ∈ Dg ∨ G2 ∈ Dg) ∧ (T2 ∈ Dg ∨ F3 ∈ Dg ∨ G1 ∈ Dg) ∧
      (T3 ∈ Dg ∨ F3 ∈ Dg ∨ G3 ∈ Dg) ∧ (T3 ∈ Dg ∨ F4 ∈ Dg ∨ G2 ∈ Dg) ∧
      (T4 ∈ Dg ∨ F4 ∈ Dg ∨ G4 ∈ Dg) ∧ (T4 ∈ Dg ∨ F5 ∈ Dg ∨ G3 ∈ Dg) ∧
      (T5 ∈ Dg ∨ F5 ∈ Dg ∨ G5 ∈ Dg) ∧ (T5 ∈ Dg ∨ F0 ∈ Dg ∨ G4 ∈ Dg) ∧
      (T6 ∈ Dg ∨ F0 ∈ Dg ∨ G5 ∈ Dg) ∧ (T6 ∈ Dg ∨ F1 ∈ Dg ∨ G0 ∈ Dg) ∧
      (T7 ∈ Dg ∨ F2 ∈ Dg ∨ G1 ∈ Dg) ∧ (T7 ∈ Dg ∨ F3 ∈ Dg ∨ G2 ∈ Dg) ∧
      (T8 ∈ Dg ∨ F4 ∈ Dg ∨ G3 ∈ Dg) ∧ (T8 ∈ Dg ∨ F5 ∈ Dg ∨ G4 ∈ Dg) := by
    refine ⟨hcl 0 (by omega) ?_, hcl 1 (by omega) ?_, hcl 2 (by omega) ?_, hcl 3 (by omega) ?_,
      hcl 4 (by omega) ?_, hcl 5 (by omega) ?_, hcl 6 (by omega) ?_, hcl 7 (by omega) ?_,
      hcl 8 (by omega) ?_, hcl 9 (by omega) ?_, hcl 10 (by omega) ?_, hcl 11 (by omega) ?_,
      hcl 12 (by omega) ?_, hcl 13 (by omega) ?_, hcl 14 (by omega) ?_, hcl 15 (by omega) ?_,
      hcl 16 (by omega) ?_, hcl 17 (by omega) ?_⟩ <;>
      (intro S hSD hkS;
       rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
         rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
       first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) |
         (dsimp only [T0, T1, T2, T3, T4, T5, T6, T7, T8, F0, F1, F2, F3, F4, F5, G0, G1, G2, G3,
           G4, G5] at hkS; simp only [List.mem_cons, List.not_mem_nil, or_false] at hkS; omega))
  rcases hdisj with ⟨ha0, hb0, ha1, hb1, ha2, hb2, ha3, hb3, ha4, hb4, ha5, hb5, ha6, hb6, ha7,
    hb7, ha8, hb8⟩
  have h_exc :
      (G0 ∈ Dg → T1 ∉ Dg ∧ F1 ∉ Dg ∧ T0 ∉ Dg ∧ F0 ∉ Dg ∧ T6 ∉ Dg) ∧
      (G1 ∈ Dg → T2 ∉ Dg ∧ F2 ∉ Dg ∧ T1 ∉ Dg ∧ F1 ∉ Dg ∧ T7 ∉ Dg) ∧
      (G2 ∈ Dg → T3 ∉ Dg ∧ F3 ∉ Dg ∧ T2 ∉ Dg ∧ F2 ∉ Dg ∧ T7 ∉ Dg) ∧
      (G3 ∈ Dg → T4 ∉ Dg ∧ F4 ∉ Dg ∧ T3 ∉ Dg ∧ F3 ∉ Dg ∧ T8 ∉ Dg) ∧
      (G4 ∈ Dg → T5 ∉ Dg ∧ F5 ∉ Dg ∧ T4 ∉ Dg ∧ F4 ∉ Dg ∧ T8 ∉ Dg) ∧
      (G5 ∈ Dg → T0 ∉ Dg ∧ F0 ∉ Dg ∧ T5 ∉ Dg ∧ F5 ∉ Dg ∧ T6 ∉ Dg) ∧
      (T0 ∈ Dg → F0 ∉ Dg ∧ F1 ∉ Dg) ∧ (T1 ∈ Dg → F1 ∉ Dg ∧ F2 ∉ Dg) ∧
      (T2 ∈ Dg → F2 ∉ Dg ∧ F3 ∉ Dg) ∧ (T3 ∈ Dg → F3 ∉ Dg ∧ F4 ∉ Dg) ∧
      (T4 ∈ Dg → F4 ∉ Dg ∧ F5 ∉ Dg) ∧ (T5 ∈ Dg → F5 ∉ Dg ∧ F0 ∉ Dg) ∧
      (T6 ∈ Dg → F0 ∉ Dg ∧ F1 ∉ Dg) ∧ (T7 ∈ Dg → F2 ∉ Dg ∧ F3 ∉ Dg) ∧
      (T8 ∈ Dg → F4 ∉ Dg ∧ F5 ∉ Dg) := by
    refine ⟨fun hG0 ↦ ⟨fun h ↦ hdiff 3 G0 T1 (by omega) hG0 h (by simp [G0]) (by simp [T1])
          (by simp [G0, T1]),
        fun h ↦ hdiff 13 G0 F1 (by omega) hG0 h (by simp [G0]) (by simp [F1]) (by simp [G0, F1]),
        fun h ↦ hdiff 0 G0 T0 (by omega) hG0 h (by simp [G0]) (by simp [T0]) (by simp [G0, T0]),
        fun h ↦ hdiff 0 G0 F0 (by omega) hG0 h (by simp [G0]) (by simp [F0]) (by simp [G0, F0]),
        fun h ↦ hdiff 13 G0 T6 (by omega) hG0 h (by simp [G0]) (by simp [T6]) (by simp [G0, T6])⟩,
      fun hG1 ↦ ⟨fun h ↦ hdiff 5 G1 T2 (by omega) hG1 h (by simp [G1]) (by simp [T2])
        (by simp [G1, T2]),
        fun h ↦ hdiff 14 G1 F2 (by omega) hG1 h (by simp [G1]) (by simp [F2]) (by simp [G1, F2]),
        fun h ↦ hdiff 2 G1 T1 (by omega) hG1 h (by simp [G1]) (by simp [T1]) (by simp [G1, T1]),
        fun h ↦ hdiff 2 G1 F1 (by omega) hG1 h (by simp [G1]) (by simp [F1]) (by simp [G1, F1]),
        fun h ↦ hdiff 14 G1 T7 (by omega) hG1 h (by simp [G1]) (by simp [T7]) (by simp [G1, T7])⟩,
      fun hG2 ↦ ⟨fun h ↦ hdiff 7 G2 T3 (by omega) hG2 h (by simp [G2]) (by simp [T3])
        (by simp [G2, T3]),
        fun h ↦ hdiff 15 G2 F3 (by omega) hG2 h (by simp [G2]) (by simp [F3]) (by simp [G2, F3]),
        fun h ↦ hdiff 4 G2 T2 (by omega) hG2 h (by simp [G2]) (by simp [T2]) (by simp [G2, T2]),
        fun h ↦ hdiff 4 G2 F2 (by omega) hG2 h (by simp [G2]) (by simp [F2]) (by simp [G2, F2]),
        fun h ↦ hdiff 15 G2 T7 (by omega) hG2 h (by simp [G2]) (by simp [T7]) (by simp [G2, T7])⟩,
      fun hG3 ↦ ⟨fun h ↦ hdiff 9 G3 T4 (by omega) hG3 h (by simp [G3]) (by simp [T4])
        (by simp [G3, T4]),
        fun h ↦ hdiff 16 G3 F4 (by omega) hG3 h (by simp [G3]) (by simp [F4]) (by simp [G3, F4]),
        fun h ↦ hdiff 6 G3 T3 (by omega) hG3 h (by simp [G3]) (by simp [T3]) (by simp [G3, T3]),
        fun h ↦ hdiff 6 G3 F3 (by omega) hG3 h (by simp [G3]) (by simp [F3]) (by simp [G3, F3]),
        fun h ↦ hdiff 16 G3 T8 (by omega) hG3 h (by simp [G3]) (by simp [T8]) (by simp [G3, T8])⟩,
      fun hG4 ↦ ⟨fun h ↦ hdiff 11 G4 T5 (by omega) hG4 h (by simp [G4]) (by simp [T5])
        (by simp [G4, T5]),
        fun h ↦ hdiff 17 G4 F5 (by omega) hG4 h (by simp [G4]) (by simp [F5]) (by simp [G4, F5]),
        fun h ↦ hdiff 8 G4 T4 (by omega) hG4 h (by simp [G4]) (by simp [T4]) (by simp [G4, T4]),
        fun h ↦ hdiff 8 G4 F4 (by omega) hG4 h (by simp [G4]) (by simp [F4]) (by simp [G4, F4]),
        fun h ↦ hdiff 17 G4 T8 (by omega) hG4 h (by simp [G4]) (by simp [T8]) (by simp [G4, T8])⟩,
      fun hG5 ↦ ⟨fun h ↦ hdiff 1 G5 T0 (by omega) hG5 h (by simp [G5]) (by simp [T0])
        (by simp [G5, T0]),
        fun h ↦ hdiff 12 G5 F0 (by omega) hG5 h (by simp [G5]) (by simp [F0]) (by simp [G5, F0]),
        fun h ↦ hdiff 10 G5 T5 (by omega) hG5 h (by simp [G5]) (by simp [T5]) (by simp [G5, T5]),
        fun h ↦ hdiff 10 G5 F5 (by omega) hG5 h (by simp [G5]) (by simp [F5]) (by simp [G5, F5]),
        fun h ↦ hdiff 12 G5 T6 (by omega) hG5 h (by simp [G5]) (by simp [T6]) (by simp [G5, T6])⟩,
      fun hT0 ↦ ⟨fun h ↦ hdiff 0 T0 F0 (by omega) hT0 h (by simp [T0]) (by simp [F0])
        (by simp [T0, F0]),
        fun h ↦ hdiff 1 T0 F1 (by omega) hT0 h (by simp [T0]) (by simp [F1]) (by simp [T0, F1])⟩,
      fun hT1 ↦ ⟨fun h ↦ hdiff 2 T1 F1 (by omega) hT1 h (by simp [T1]) (by simp [F1])
        (by simp [T1, F1]),
        fun h ↦ hdiff 3 T1 F2 (by omega) hT1 h (by simp [T1]) (by simp [F2]) (by simp [T1, F2])⟩,
      fun hT2 ↦ ⟨fun h ↦ hdiff 4 T2 F2 (by omega) hT2 h (by simp [T2]) (by simp [F2])
        (by simp [T2, F2]),
        fun h ↦ hdiff 5 T2 F3 (by omega) hT2 h (by simp [T2]) (by simp [F3]) (by simp [T2, F3])⟩,
      fun hT3 ↦ ⟨fun h ↦ hdiff 6 T3 F3 (by omega) hT3 h (by simp [T3]) (by simp [F3])
        (by simp [T3, F3]),
        fun h ↦ hdiff 7 T3 F4 (by omega) hT3 h (by simp [T3]) (by simp [F4]) (by simp [T3, F4])⟩,
      fun hT4 ↦ ⟨fun h ↦ hdiff 8 T4 F4 (by omega) hT4 h (by simp [T4]) (by simp [F4])
        (by simp [T4, F4]),
        fun h ↦ hdiff 9 T4 F5 (by omega) hT4 h (by simp [T4]) (by simp [F5]) (by simp [T4, F5])⟩,
      fun hT5 ↦ ⟨fun h ↦ hdiff 10 T5 F5 (by omega) hT5 h (by simp [T5]) (by simp [F5])
        (by simp [T5, F5]),
        fun h ↦ hdiff 11 T5 F0 (by omega) hT5 h (by simp [T5]) (by simp [F0]) (by simp [T5, F0])⟩,
      fun hT6 ↦ ⟨fun h ↦ hdiff 12 T6 F0 (by omega) hT6 h (by simp [T6]) (by simp [F0])
        (by simp [T6, F0]),
        fun h ↦ hdiff 13 T6 F1 (by omega) hT6 h (by simp [T6]) (by simp [F1]) (by simp [T6, F1])⟩,
      fun hT7 ↦ ⟨fun h ↦ hdiff 14 T7 F2 (by omega) hT7 h (by simp [T7]) (by simp [F2])
        (by simp [T7, F2]),
        fun h ↦ hdiff 15 T7 F3 (by omega) hT7 h (by simp [T7]) (by simp [F3]) (by simp [T7, F3])⟩,
      fun hT8 ↦ ⟨fun h ↦ hdiff 16 T8 F4 (by omega) hT8 h (by simp [T8]) (by simp [F4])
        (by simp [T8, F4]),
        fun h ↦ hdiff 17 T8 F5 (by omega) hT8 h (by simp [T8]) (by simp [F5]) (by simp [T8, F5])⟩⟩
  have hcase : (T0 ∈ Dg ∧ T1 ∈ Dg ∧ T2 ∈ Dg ∧ T3 ∈ Dg ∧ T4 ∈ Dg ∧ T5 ∈ Dg ∧ T6 ∈ Dg ∧
      T7 ∈ Dg ∧ T8 ∈ Dg) ∨
      (T0 ∉ Dg ∧ T1 ∉ Dg ∧ T2 ∉ Dg ∧ T3 ∉ Dg ∧ T4 ∉ Dg ∧ T5 ∉ Dg ∧ T6 ∉ Dg ∧
      T7 ∉ Dg ∧ T8 ∉ Dg) := by
    obtain ⟨hG0, hG1, hG2, hG3, hG4, hG5, hT0e, hT1e, hT2e, hT3e, hT4e, hT5e, hT6e, hT7e, hT8e⟩ :=
      h_exc
    have h01 : T0 ∈ Dg → T1 ∈ Dg := fun h ↦ by
      have hng1 : G1 ∉ Dg := fun hg ↦ by
        have := hG1 hg
        exact (hb1.resolve_left this.2.2.1).elim this.2.1 (fun hg0 ↦ (hG0 hg0).2.2.1 h)
      exact ha1.resolve_right (Or.elim · (hT0e h).2 hng1)
    have h12 : T1 ∈ Dg → T2 ∈ Dg := fun h ↦ by
      have hng2 : G2 ∉ Dg := fun hg ↦ by
        have := hG2 hg
        exact (hb2.resolve_left this.2.2.1).elim this.2.1 (fun hg1 ↦ (hG1 hg1).2.2.1 h)
      exact ha2.resolve_right (Or.elim · (hT1e h).2 hng2)
    have h23 : T2 ∈ Dg → T3 ∈ Dg := fun h ↦ by
      have hng3 : G3 ∉ Dg := fun hg ↦ by
        have := hG3 hg
        exact (hb3.resolve_left this.2.2.1).elim this.2.1 (fun hg2 ↦ (hG2 hg2).2.2.1 h)
      exact ha3.resolve_right (Or.elim · (hT2e h).2 hng3)
    have h34 : T3 ∈ Dg → T4 ∈ Dg := fun h ↦ by
      have hng4 : G4 ∉ Dg := fun hg ↦ by
        have := hG4 hg
        exact (hb4.resolve_left this.2.2.1).elim this.2.1 (fun hg3 ↦ (hG3 hg3).2.2.1 h)
      exact ha4.resolve_right (Or.elim · (hT3e h).2 hng4)
    have h45 : T4 ∈ Dg → T5 ∈ Dg := fun h ↦ by
      have hng5 : G5 ∉ Dg := fun hg ↦ by
        have := hG5 hg
        exact (hb5.resolve_left this.2.2.1).elim this.2.1 (fun hg4 ↦ (hG4 hg4).2.2.1 h)
      exact ha5.resolve_right (Or.elim · (hT4e h).2 hng5)
    have h50 : T5 ∈ Dg → T0 ∈ Dg := fun h ↦ by
      have hng0 : G0 ∉ Dg := fun hg ↦ by
        have := hG0 hg
        exact (hb0.resolve_left this.2.2.1).elim this.2.1 (fun hg5 ↦ (hG5 hg5).2.2.1 h)
      exact ha0.resolve_right (Or.elim · (hT5e h).2 hng0)
    have h60 : T6 ∈ Dg → T0 ∈ Dg := fun h ↦
      ha0.resolve_right (Or.elim · (hT6e h).1 (fun hg ↦ (hG0 hg).2.2.2.2 h))
    have h72 : T7 ∈ Dg → T2 ∈ Dg := fun h ↦
      ha2.resolve_right (Or.elim · (hT7e h).1 (fun hg ↦ (hG2 hg).2.2.2.2 h))
    have h84 : T8 ∈ Dg → T4 ∈ Dg := fun h ↦
      ha4.resolve_right (Or.elim · (hT8e h).1 (fun hg ↦ (hG4 hg).2.2.2.2 h))
    by_cases hT0 : T0 ∈ Dg
    · have hT1 := h01 hT0; have hT2 := h12 hT1; have hT3 := h23 hT2
      have hT4 := h34 hT3; have hT5 := h45 hT4
      have hT6 : T6 ∈ Dg := ha6.resolve_right (Or.elim · (hT0e hT0).1 (fun hg ↦ (hG5 hg).1 hT0))
      have hT7 : T7 ∈ Dg := ha7.resolve_right
        (Or.elim · (hT1e hT1).2 (fun hg ↦ (hG1 hg).2.2.1 hT1))
      have hT8 : T8 ∈ Dg := ha8.resolve_right
        (Or.elim · (hT3e hT3).2 (fun hg ↦ (hG3 hg).2.2.1 hT3))
      exact Or.inl ⟨hT0, hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8⟩
    · have hT5 : T5 ∉ Dg := fun h ↦ hT0 (h50 h)
      have hT4 : T4 ∉ Dg := fun h ↦ hT5 (h45 h)
      have hT3 : T3 ∉ Dg := fun h ↦ hT4 (h34 h)
      have hT2 : T2 ∉ Dg := fun h ↦ hT3 (h23 h)
      have hT1 : T1 ∉ Dg := fun h ↦ hT2 (h12 h)
      exact Or.inr ⟨hT0, hT1, hT2, hT3, hT4, hT5,
        fun h ↦ hT0 (h60 h), fun h ↦ hT2 (h72 h), fun h ↦ hT4 (h84 h)⟩
  rcases hcase with ⟨hT0, hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8⟩ |
      ⟨hT0, hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8⟩
  · have hnone_fg : ∀ S ∈ Dg, ∀ x < base, x ∈ S →
        S = T0 ∨ S = T1 ∨ S = T2 ∨ S = T3 ∨ S = T4 ∨ S = T5 ∨ S = T6 ∨ S = T7 ∨ S = T8 := by
      intro S hSD x hx hxS
      rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
      all_goals (simp [F0, F1, F2, F3, F4, F5, G0, G1, G2, G3, G4, G5] at hxS; omega)
    refine Or.inl fun j hj c hc ↦ ?_
    rcases (by simpa using hj : j = j0 ∨ j = j1 ∨ j = j2) with rfl | rfl | rfl
    · interval_cases c
      · exact filter_card_eq_one_of_unique hT0 (by simp [T0]) fun S hSD hxS ↦ by
          rcases hnone_fg S hSD _ (by omega) hxS with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | rfl
            | (dsimp [T0, T1, T2, T3, T4, T5, T6, T7, T8] at hxS
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS; omega)
      · exact filter_card_eq_one_of_unique hT1 (by simp [T1]) fun S hSD hxS ↦ by
          rcases hnone_fg S hSD _ (by omega) hxS with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | rfl
            | (dsimp [T0, T1, T2, T3, T4, T5, T6, T7, T8] at hxS
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS; omega)
      · exact filter_card_eq_one_of_unique hT2 (by simp [T2]) fun S hSD hxS ↦ by
          rcases hnone_fg S hSD _ (by omega) hxS with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | rfl
            | (dsimp [T0, T1, T2, T3, T4, T5, T6, T7, T8] at hxS
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS; omega)
    · interval_cases c
      · exact filter_card_eq_one_of_unique hT3 (by simp [T3]) fun S hSD hxS ↦ by
          rcases hnone_fg S hSD _ (by omega) hxS with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | rfl
            | (dsimp [T0, T1, T2, T3, T4, T5, T6, T7, T8] at hxS
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS; omega)
      · exact filter_card_eq_one_of_unique hT4 (by simp [T4]) fun S hSD hxS ↦ by
          rcases hnone_fg S hSD _ (by omega) hxS with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | rfl
            | (dsimp [T0, T1, T2, T3, T4, T5, T6, T7, T8] at hxS
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS; omega)
      · exact filter_card_eq_one_of_unique hT5 (by simp [T5]) fun S hSD hxS ↦ by
          rcases hnone_fg S hSD _ (by omega) hxS with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | rfl
            | (dsimp [T0, T1, T2, T3, T4, T5, T6, T7, T8] at hxS
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS; omega)
    · interval_cases c
      · exact filter_card_eq_one_of_unique hT6 (by simp [T6]) fun S hSD hxS ↦ by
          rcases hnone_fg S hSD _ (by omega) hxS with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | rfl
            | (dsimp [T0, T1, T2, T3, T4, T5, T6, T7, T8] at hxS
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS; omega)
      · exact filter_card_eq_one_of_unique hT7 (by simp [T7]) fun S hSD hxS ↦ by
          rcases hnone_fg S hSD _ (by omega) hxS with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | rfl
            | (dsimp [T0, T1, T2, T3, T4, T5, T6, T7, T8] at hxS
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS; omega)
      · exact filter_card_eq_one_of_unique hT8 (by simp [T8]) fun S hSD hxS ↦ by
          rcases hnone_fg S hSD _ (by omega) hxS with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | rfl
            | (dsimp [T0, T1, T2, T3, T4, T5, T6, T7, T8] at hxS
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS; omega)
  · refine Or.inr fun j hj c hc ↦ ?_
    have hlt : 3 * j + c < base := by
      rcases (by simpa using hj : j = j0 ∨ j = j1 ∨ j = j2) with rfl | rfl | rfl <;> omega
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro S hSD hxS
    rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hT0 hSD
    · exact hT1 hSD
    · exact hT2 hSD
    · exact hT3 hSD
    · exact hT4 hSD
    · exact hT5 hSD
    · exact hT6 hSD
    · exact hT7 hSD
    · exact hT8 hSD
    all_goals (simp [F0, F1, F2, F3, F4, F5, G0, G1, G2, G3, G4, G5] at hxS; omega)

/-- Core forcing lemma for a single variable gadget: if `D` covers each internal element
`base + t` (`t < 6 * O.length`) exactly once using sets from `varGadget base O`, then EITHER every
`T`-set `[3 * j + c, a_r, b_r]` is in `D` (covering every clause copy `3 * j + c` for `j ∈ O`,
`c < 3`) OR none of them is in `D` (covering no clause copy). -/
theorem varGadget_forcing {base : ℕ} {O : List ℕ} {D : Finset (List ℕ)}
    (hO_len : 1 ≤ O.length ∧ O.length ≤ 3) (hO_nd : O.Nodup)
    (hO_lt : ∀ j ∈ O, 3 * j + 2 < base)
    (hD : ∀ t < 6 * O.length,
      ((D.filter fun S ↦ S ∈ varGadget base O).filter (base + t ∈ ·)).card = 1) :
    (∀ j ∈ O, ∀ c < 3,
      ((D.filter fun S ↦ S ∈ varGadget base O).filter (3 * j + c ∈ ·)).card = 1) ∨
    (∀ j ∈ O, ∀ c < 3,
      ((D.filter fun S ↦ S ∈ varGadget base O).filter (3 * j + c ∈ ·)).card = 0) := by
  let Dg := D.filter fun S ↦ S ∈ varGadget base O
  rcases O with _ | ⟨j0, _ | ⟨j1, _ | ⟨j2, _ | ⟨j3, t⟩⟩⟩⟩
  · simp at hO_len
  · have h0 : 3 * j0 + 2 < base := hO_lt j0 (by simp)
    let T0 : List ℕ := [3 * j0, base, base + 1]
    let T1 : List ℕ := [3 * j0 + 1, base + 2, base + 3]
    let T2 : List ℕ := [3 * j0 + 2, base + 4, base + 5]
    let F0 : List ℕ := [base, base + 3, base + 4]
    let F1 : List ℕ := [base + 1, base + 2, base + 5]
    let G0 : List ℕ := [base, base + 3, base + 5]
    let G1 : List ℕ := [base + 2, base + 1, base + 4]
    have hvg : varGadget base [j0] = [T0, T1, T2, F0, F1, G0, G1] := rfl
    have hin : ∀ k < 6, (Dg.filter (base + k ∈ ·)).card = 1 := fun k hk ↦ hD k (by simpa using hk)
    have hDg_sub : ∀ S ∈ Dg, S = T0 ∨ S = T1 ∨ S = T2 ∨ S = F0 ∨ S = F1 ∨ S = G0 ∨ S = G1 := by
      intro S hS
      have := (Finset.mem_filter.mp hS).2
      simpa [hvg] using this
    have hmem_iff : ∀ k, (base + k ∈ T0 ↔ k = 0 ∨ k = 1) ∧
        (base + k ∈ T1 ↔ k = 2 ∨ k = 3) ∧ (base + k ∈ T2 ↔ k = 4 ∨ k = 5) ∧
        (base + k ∈ F0 ↔ k = 0 ∨ k = 3 ∨ k = 4) ∧ (base + k ∈ F1 ↔ k = 1 ∨ k = 2 ∨ k = 5) ∧
        (base + k ∈ G0 ↔ k = 0 ∨ k = 3 ∨ k = 5) ∧ (base + k ∈ G1 ↔ k = 2 ∨ k = 1 ∨ k = 4) := by
      intro k; simp only [T0, T1, T2, F0, F1, G0, G1, List.mem_cons, List.not_mem_nil, or_false]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    have huniq : ∀ k < 6, ∀ S ∈ Dg, ∀ U ∈ Dg, base + k ∈ S → base + k ∈ U → S = U := by
      intro k hk S hS U hU hkS hkU
      obtain ⟨Z, hZ⟩ := Finset.card_eq_one.mp (hin k hk)
      have h1 : S ∈ ({Z} : Finset _) := hZ ▸ Finset.mem_filter.mpr ⟨hS, hkS⟩
      have h2 : U ∈ ({Z} : Finset _) := hZ ▸ Finset.mem_filter.mpr ⟨hU, hkU⟩
      rw [Finset.mem_singleton.mp h1, Finset.mem_singleton.mp h2]
    have hne : T0 ≠ T1 ∧ T0 ≠ T2 ∧ T0 ≠ F0 ∧ T0 ≠ F1 ∧ T0 ≠ G0 ∧ T0 ≠ G1 ∧
        T1 ≠ T2 ∧ T1 ≠ F0 ∧ T1 ≠ F1 ∧ T1 ≠ G0 ∧ T1 ≠ G1 ∧
        T2 ≠ F0 ∧ T2 ≠ F1 ∧ T2 ≠ G0 ∧ T2 ≠ G1 ∧
        F0 ≠ F1 ∧ F0 ≠ G0 ∧ F0 ≠ G1 ∧ F1 ≠ G0 ∧ F1 ≠ G1 ∧ G0 ≠ G1 := by
      simp only [T0, T1, T2, F0, F1, G0, G1, ne_eq, List.cons.injEq, not_and]
      repeat (refine ⟨?_, ?_⟩) <;> omega
    have hcov_k : ∀ k < 6, ∃ S ∈ Dg, base + k ∈ S := fun k hk ↦ by
      obtain ⟨S, hS⟩ := Finset.card_eq_one.mp (hin k hk)
      have hm : S ∈ Dg.filter (base + k ∈ ·) := hS ▸ Finset.mem_singleton_self S
      exact ⟨S, (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2⟩
    have h0' : T0 ∈ Dg ∨ F0 ∈ Dg ∨ G0 ∈ Dg := by
      obtain ⟨S, hSD, hkS⟩ := hcov_k 0 (by omega)
      rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (try exact Or.inl hSD) <;> (try exact Or.inr (Or.inl hSD)) <;>
        (try exact Or.inr (Or.inr hSD)) <;>
        (simp only [T1, T2, F1, G1, List.mem_cons, List.not_mem_nil, or_false] at hkS; omega)
    have h1' : T0 ∈ Dg ∨ F1 ∈ Dg ∨ G1 ∈ Dg := by
      obtain ⟨S, hSD, hkS⟩ := hcov_k 1 (by omega)
      rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (try exact Or.inl hSD) <;> (try exact Or.inr (Or.inl hSD)) <;>
        (try exact Or.inr (Or.inr hSD)) <;>
        (simp only [T1, T2, F0, G0, List.mem_cons, List.not_mem_nil, or_false] at hkS; omega)
    have h2' : T1 ∈ Dg ∨ F1 ∈ Dg ∨ G1 ∈ Dg := by
      obtain ⟨S, hSD, hkS⟩ := hcov_k 2 (by omega)
      rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (try exact Or.inl hSD) <;> (try exact Or.inr (Or.inl hSD)) <;>
        (try exact Or.inr (Or.inr hSD)) <;>
        (simp only [T0, T2, F0, G0, List.mem_cons, List.not_mem_nil, or_false] at hkS; omega)
    have h3' : T1 ∈ Dg ∨ F0 ∈ Dg ∨ G0 ∈ Dg := by
      obtain ⟨S, hSD, hkS⟩ := hcov_k 3 (by omega)
      rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (try exact Or.inl hSD) <;> (try exact Or.inr (Or.inl hSD)) <;>
        (try exact Or.inr (Or.inr hSD)) <;>
        (simp only [T0, T2, F1, G1, List.mem_cons, List.not_mem_nil, or_false] at hkS; omega)
    have h4' : T2 ∈ Dg ∨ F0 ∈ Dg ∨ G1 ∈ Dg := by
      obtain ⟨S, hSD, hkS⟩ := hcov_k 4 (by omega)
      rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (try exact Or.inl hSD) <;> (try exact Or.inr (Or.inl hSD)) <;>
        (try exact Or.inr (Or.inr hSD)) <;>
        (simp only [T0, T1, F1, G0, List.mem_cons, List.not_mem_nil, or_false] at hkS; omega)
    have h5' : T2 ∈ Dg ∨ F1 ∈ Dg ∨ G0 ∈ Dg := by
      obtain ⟨S, hSD, hkS⟩ := hcov_k 5 (by omega)
      rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (try exact Or.inl hSD) <;> (try exact Or.inr (Or.inl hSD)) <;>
        (try exact Or.inr (Or.inr hSD)) <;>
        (simp only [T0, T1, F0, G1, List.mem_cons, List.not_mem_nil, or_false] at hkS; omega)
    have hdisj :
        (T0 ∈ Dg → F0 ∉ Dg ∧ G0 ∉ Dg ∧ F1 ∉ Dg ∧ G1 ∉ Dg) ∧
        (T1 ∈ Dg → F1 ∉ Dg ∧ G1 ∉ Dg ∧ F0 ∉ Dg ∧ G0 ∉ Dg) ∧
        (T2 ∈ Dg → F0 ∉ Dg ∧ G1 ∉ Dg ∧ F1 ∉ Dg ∧ G0 ∉ Dg) ∧
        (F0 ∈ Dg → G0 ∉ Dg ∧ G1 ∉ Dg) ∧
        (F1 ∈ Dg → G0 ∉ Dg ∧ G1 ∉ Dg) := by
      refine ⟨fun hT0 ↦ ⟨fun h ↦ hne.2.2.1 (huniq 0 (by omega) _ hT0 _ h (by simp [T0])
            (by simp [F0])),
          fun h ↦ hne.2.2.2.2.1 (huniq 0 (by omega) _ hT0 _ h (by simp [T0]) (by simp [G0])),
          fun h ↦ hne.2.2.2.1 (huniq 1 (by omega) _ hT0 _ h (by simp [T0]) (by simp [F1])),
          fun h ↦ hne.2.2.2.2.2.1 (huniq 1 (by omega) _ hT0 _ h (by simp [T0]) (by simp [G1]))⟩,
        fun hT1 ↦ ⟨fun h ↦ hne.2.2.2.2.2.2.2.2.1 (huniq 2 (by omega) _ hT1 _ h (by simp [T1])
            (by simp [F1])),
          fun h ↦ hne.2.2.2.2.2.2.2.2.2.2.1 (huniq 2 (by omega) _ hT1 _ h (by simp [T1])
            (by simp [G1])),
          fun h ↦ hne.2.2.2.2.2.2.2.1 (huniq 3 (by omega) _ hT1 _ h (by simp [T1]) (by simp [F0])),
          fun h ↦ hne.2.2.2.2.2.2.2.2.2.1 (huniq 3 (by omega) _ hT1 _ h (by simp [T1])
            (by simp [G0]))⟩,
        fun hT2 ↦ ⟨fun h ↦ hne.2.2.2.2.2.2.2.2.2.2.2.1 (huniq 4 (by omega) _ hT2 _ h (by simp [T2])
            (by simp [F0])),
          fun h ↦ hne.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (huniq 4 (by omega) _ hT2 _ h (by simp [T2])
            (by simp [G1])),
          fun h ↦ hne.2.2.2.2.2.2.2.2.2.2.2.2.1 (huniq 5 (by omega) _ hT2 _ h (by simp [T2])
            (by simp [F1])),
          fun h ↦ hne.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (huniq 5 (by omega) _ hT2 _ h (by simp [T2])
            (by simp [G0]))⟩,
        fun hF0 ↦ ⟨fun h ↦ hne.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (huniq 0 (by omega) _ hF0 _ h
            (by simp [F0]) (by simp [G0])),
          fun h ↦ hne.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (huniq 4 (by omega) _ hF0 _ h
            (by simp [F0]) (by simp [G1]))⟩,
        fun hF1 ↦ ⟨fun h ↦ hne.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (huniq 5 (by omega) _ hF1 _ h
            (by simp [F1]) (by simp [G0])),
          fun h ↦ hne.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (huniq 1 (by omega) _ hF1 _ h
            (by simp [F1]) (by simp [G1]))⟩⟩
    have hcase : (T0 ∈ Dg ∧ T1 ∈ Dg ∧ T2 ∈ Dg) ∨ (T0 ∉ Dg ∧ T1 ∉ Dg ∧ T2 ∉ Dg) := by
      by_cases hT0 : T0 ∈ Dg
      · obtain ⟨hF0, hG0, hF1, hG1⟩ := hdisj.1 hT0
        exact Or.inl ⟨hT0, h2'.resolve_right (by rintro (h | h) <;> contradiction),
          h4'.resolve_right (by rintro (h | h) <;> contradiction)⟩
      · have hT1 : T1 ∉ Dg := fun h1 ↦ by
          obtain ⟨_, _, hF0, hG0⟩ := hdisj.2.1 h1
          exact (h0'.resolve_left hT0).elim hF0 hG0
        have hT2 : T2 ∉ Dg := fun h2 ↦ by
          obtain ⟨hF0, _, _, hG0⟩ := hdisj.2.2.1 h2
          exact (h0'.resolve_left hT0).elim hF0 hG0
        exact Or.inr ⟨hT0, hT1, hT2⟩
    rcases hcase with ⟨hT0, hT1, hT2⟩ | ⟨hT0, hT1, hT2⟩
    · refine Or.inl fun j hj c hc ↦ ?_
      obtain rfl : j = j0 := by simpa using hj
      interval_cases c
      · exact filter_card_eq_one_of_unique hT0 (by simp [T0]) fun S hSD hxS ↦ by
          rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | rfl
            | (dsimp [T0, T1, T2, F0, F1, G0, G1] at hxS
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS; omega)
      · exact filter_card_eq_one_of_unique hT1 (by simp [T1]) fun S hSD hxS ↦ by
          rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | rfl
            | (dsimp [T0, T1, T2, F0, F1, G0, G1] at hxS
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS; omega)
      · exact filter_card_eq_one_of_unique hT2 (by simp [T2]) fun S hSD hxS ↦ by
          rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | rfl
            | (dsimp [T0, T1, T2, F0, F1, G0, G1] at hxS
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS; omega)
    · refine Or.inr fun j hj c hc ↦ ?_
      have hj_eq : j = j0 := by simpa using hj
      rw [hj_eq]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro S hSD hxS
      rcases hDg_sub S hSD with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hT0 hSD
      · exact hT1 hSD
      · exact hT2 hSD
      all_goals (simp [F0, F1, G0, G1] at hxS; omega)
  · exact varGadget_forcing_2 (hO_lt j0 (by simp)) (hO_lt j1 (by simp))
      (by simpa [List.nodup_cons] using hO_nd) hD
  · obtain ⟨h0, h1, h2, hnd⟩ := unpack_triple_occ hO_nd hO_lt
    exact varGadget_forcing_3 h0 h1 h2 hnd hD
  · simp at hO_len; omega



/-- Every set `[x0, x1, x2]` in `varGadget base O` (`1 ≤ O.length ≤ 3`) has `base ≤ x1`. -/
theorem second_ge_of_mem_varGadget {base : ℕ} {O : List ℕ}
    (hO_len : 1 ≤ O.length ∧ O.length ≤ 3) {x0 x1 x2 : ℕ}
    (hmem : [x0, x1, x2] ∈ varGadget base O) : base ≤ x1 := by
  rcases O with _ | ⟨j0, _ | ⟨j1, _ | ⟨j2, _ | ⟨j3, t⟩⟩⟩⟩
  · simp at hO_len
  · simp only [varGadget, gadget1, List.length_cons, List.length_nil, Nat.reduceAdd,
      beq_self_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false,
      List.cons.injEq] at hmem
    rcases hmem with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ |
      ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> omega
  · simp only [varGadget_two, gadget2, List.mem_cons, List.not_mem_nil, or_false,
      List.cons.injEq] at hmem
    rcases hmem with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ |
      ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ |
      ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> omega
  · simp only [varGadget_three, gadget3, List.mem_cons, List.not_mem_nil, or_false,
      List.cons.injEq] at hmem
    rcases hmem with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ |
      ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ |
      ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ |
      ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> omega
  · simp at hO_len; omega

/-- False-branch exact cover of a single variable gadget (`F`-sets). -/
@[expose] def gadgetFalse (base : ℕ) (O : List ℕ) : List (List ℕ) :=
  if O.length == 1 then
    [[base, base + 3, base + 4], [base + 1, base + 2, base + 5]]
  else if O.length == 2 then
    [[base, base + 7, base + 8], [base + 1, base + 2, base + 9],
     [base + 3, base + 4, base + 10], [base + 5, base + 6, base + 11]]
  else if O.length == 3 then
    [[base, base + 11, base + 12], [base + 1, base + 2, base + 13],
     [base + 3, base + 4, base + 14], [base + 5, base + 6, base + 15],
     [base + 7, base + 8, base + 16], [base + 9, base + 10, base + 17]]
  else []

/-- Structural properties of the true-branch cover `gadgetTrue base O`. -/
theorem gadgetTrue_props {base : ℕ} {O : List ℕ}
    (hO_len : 1 ≤ O.length ∧ O.length ≤ 3) (hO_nd : O.Nodup)
    (hO_lt : ∀ j ∈ O, 3 * j + 2 < base) :
    (∀ S ∈ gadgetTrue base O, S ∈ varGadget base O) ∧
    (gadgetTrue base O).Nodup ∧
    (∀ t < 6 * O.length, (gadgetTrue base O).countP (fun S ↦ decide (base + t ∈ S)) = 1) ∧
    (∀ j ∈ O, ∀ c < 3, (gadgetTrue base O).countP (fun S ↦ decide (3 * j + c ∈ S)) = 1) ∧
    (∀ u, u < base → (∀ j ∈ O, ∀ c < 3, u ≠ 3 * j + c) →
      (gadgetTrue base O).countP (fun S ↦ decide (u ∈ S)) = 0) ∧
    (∀ u, base + 6 * O.length ≤ u →
      (gadgetTrue base O).countP (fun S ↦ decide (u ∈ S)) = 0) := by
  have hcl := gadgetTrue_countP_clause hO_nd hO_lt
  refine ⟨?_, ?_, ?_, hcl.1, hcl.2.1, hcl.2.2⟩
  all_goals
    rcases O with _ | ⟨j0, _ | ⟨j1, _ | ⟨j2, _ | ⟨j3, t⟩⟩⟩⟩
    · simp at hO_len
    · have h0 : 3 * j0 + 2 < base := hO_lt j0 (by simp)
      simp only [gadgetTrue, varGadget, gadget1, List.zipIdx_cons, List.zipIdx_nil,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons, List.length_nil,
        Nat.reduceAdd, beq_self_eq_true, ↓reduceIte, List.getD_cons_zero, mul_zero, add_zero,
        mul_one]
      first
      | (intro S hS; simp only [List.mem_cons, List.not_mem_nil, or_false] at hS ⊢; tauto)
      | (simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          List.nodup_nil, and_true, List.cons.injEq]; grind)
      | (intro k hk; interval_cases k <;>
          ((repeat first | rw [cp2 (by omega)] | rw [cp3 (by omega)] |
              rw [cp0 (by omega) (by omega) (by omega)]);
           rw [List.countP_nil]))
    · have h0 : 3 * j0 + 2 < base := hO_lt j0 (by simp)
      have h1 : 3 * j1 + 2 < base := hO_lt j1 (by simp)
      have h01 : j0 ≠ j1 := by simpa [List.nodup_cons] using hO_nd
      simp only [gadgetTrue, varGadget_two, gadget2, List.zipIdx_cons, List.zipIdx_nil,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append,
        List.length_cons, List.length_nil, Nat.reduceAdd, mul_zero, add_zero, mul_one,
        Nat.reduceMul]
      first
      | (intro S hS; simp only [List.mem_cons, List.not_mem_nil, or_false] at hS ⊢; tauto)
      | (simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          List.nodup_nil, and_true, List.cons.injEq]; grind)
      | (intro k hk; interval_cases k <;>
          ((repeat first | rw [cp2 (by omega)] | rw [cp3 (by omega)] |
              rw [cp0 (by omega) (by omega) (by omega)]);
           rw [List.countP_nil]))
    · obtain ⟨h0, h1, h2, hnd⟩ := unpack_triple_occ hO_nd hO_lt
      simp only [gadgetTrue, varGadget_three, gadget3, List.zipIdx_cons, List.zipIdx_nil,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append,
        List.length_cons, List.length_nil, Nat.reduceAdd, mul_zero, add_zero, mul_one,
        Nat.reduceMul]
      first
      | (intro S hS; simp only [List.mem_cons, List.not_mem_nil, or_false] at hS ⊢; tauto)
      | (simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          List.nodup_nil, and_true, List.cons.injEq]; grind)
      | (intro k hk; interval_cases k <;>
          ((repeat first | rw [cp2 (by omega)] | rw [cp3 (by omega)] |
              rw [cp0 (by omega) (by omega) (by omega)]);
           rw [List.countP_nil]))
    · simp at hO_len; omega

private lemma gadgetFalse_one (base j0 : ℕ) :
    gadgetFalse base [j0] = [[base, base + 3, base + 4], [base + 1, base + 2, base + 5]] := rfl
private lemma gadgetFalse_two (base j0 j1 : ℕ) :
    gadgetFalse base [j0, j1] = [[base, base + 7, base + 8], [base + 1, base + 2, base + 9],
      [base + 3, base + 4, base + 10], [base + 5, base + 6, base + 11]] := rfl
private lemma gadgetFalse_three (base j0 j1 j2 : ℕ) :
    gadgetFalse base [j0, j1, j2] = [[base, base + 11, base + 12], [base + 1, base + 2, base + 13],
      [base + 3, base + 4, base + 14], [base + 5, base + 6, base + 15],
      [base + 7, base + 8, base + 16], [base + 9, base + 10, base + 17]] := rfl

/-- Structural properties of the false-branch cover `gadgetFalse base O`. -/
theorem gadgetFalse_props {base : ℕ} {O : List ℕ}
    (hO_len : 1 ≤ O.length ∧ O.length ≤ 3) :
    (∀ S ∈ gadgetFalse base O, S ∈ varGadget base O) ∧
    (gadgetFalse base O).Nodup ∧
    (∀ t < 6 * O.length, (gadgetFalse base O).countP (fun S ↦ decide (base + t ∈ S)) = 1) ∧
    (∀ u, u < base → (gadgetFalse base O).countP (fun S ↦ decide (u ∈ S)) = 0) ∧
    (∀ u, base + 6 * O.length ≤ u →
      (gadgetFalse base O).countP (fun S ↦ decide (u ∈ S)) = 0) := by
  rcases O with _ | ⟨j0, _ | ⟨j1, _ | ⟨j2, _ | ⟨j3, t⟩⟩⟩⟩
  · simp at hO_len
  · simp only [gadgetFalse_one, varGadget_one, gadget1, List.length_cons, List.length_nil,
      Nat.reduceAdd, mul_one]
    refine ⟨by intro S hS; simp only [List.mem_cons, List.not_mem_nil, or_false] at hS ⊢; tauto,
      ?_, ?_, ?_, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil, and_true, List.cons.injEq]; grind
    · intro k hk; interval_cases k <;>
        ((repeat first | rw [cp1 (by omega)] | rw [cp2 (by omega)] | rw [cp3 (by omega)] |
            rw [cp0 (by omega) (by omega) (by omega)]);
         rw [List.countP_nil])
    · intro u hu; (repeat rw [cp0 (by omega) (by omega) (by omega)]); exact List.countP_nil
    · intro u hu; (repeat rw [cp0 (by omega) (by omega) (by omega)]); exact List.countP_nil
  · simp only [gadgetFalse_two, varGadget_two, gadget2, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceMul]
    refine ⟨by intro S hS; simp only [List.mem_cons, List.not_mem_nil, or_false] at hS ⊢; tauto,
      ?_, ?_, ?_, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, List.cons.injEq]
      grind
    · intro k hk; interval_cases k <;>
        ((repeat first | rw [cp1 (by omega)] | rw [cp2 (by omega)] | rw [cp3 (by omega)] |
            rw [cp0 (by omega) (by omega) (by omega)]);
         rw [List.countP_nil])
    · intro u hu; (repeat rw [cp0 (by omega) (by omega) (by omega)]); exact List.countP_nil
    · intro u hu; (repeat rw [cp0 (by omega) (by omega) (by omega)]); exact List.countP_nil
  · simp only [gadgetFalse_three, varGadget_three, gadget3, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceMul]
    refine ⟨by intro S hS; simp only [List.mem_cons, List.not_mem_nil, or_false] at hS ⊢; tauto,
      ?_, ?_, ?_, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, List.cons.injEq]
      grind
    · intro k hk; interval_cases k <;>
        ((repeat first | rw [cp1 (by omega)] | rw [cp2 (by omega)] | rw [cp3 (by omega)] |
            rw [cp0 (by omega) (by omega) (by omega)]);
         rw [List.countP_nil])
    · intro u hu; (repeat rw [cp0 (by omega) (by omega) (by omega)]); exact List.countP_nil
    · intro u hu; (repeat rw [cp0 (by omega) (by omega) (by omega)]); exact List.countP_nil
  · simp at hO_len; omega

end ThreeExactCoverRegular

end Cslib.Complexity
