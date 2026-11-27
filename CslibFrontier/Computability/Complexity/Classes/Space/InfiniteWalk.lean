/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module

public import Cslib.Foundations.Relation.RelatesInSteps
public import CslibFrontier.Computability.Complexity.Classes.Space
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability

import CslibFrontier.Algorithms.Reachability.Savitch
import CslibFrontier.Computability.Complexity.Classes.Space.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.BitString.Enumeration
import CslibFrontier.Foundations.Relation.RelatesWithinSteps
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card

/-!
# Bounded Universal Quantification and Savitch Infinite-Walk Reachability in `PSPACE`

This module proves that `PSPACE` is closed under polynomially bounded universal bitstring
quantification, and that both finite-horizon reachability and infinite-walk (Büchi lasso) existence
on implicit exponentially large directed graphs of polynomially bounded vertex bit-width lie in
`PSPACE` via Savitch's theorem.

## Main definitions

* `CslibFrontier.Complexity.WidthStep`: the directed edge relation restricted to bitstring vertices
  of exact bit-length `w` satisfying `edge u v = true`.
* `CslibFrontier.Complexity.HasInfiniteWidthWalk`: existence of an infinite directed walk
  `v₀ → v₁ → v₂ → ⋯` starting at `src` in `WidthStep edge w`.

## Main results

* `CslibFrontier.Complexity.setOf_forall_mem_PSPACE`: `PSPACE` is closed under polynomially bounded
  universal bitstring quantification.
* `CslibFrontier.Complexity.reflTransGen_widthStep_iff_relatesWithinSteps`: reachability under
  `WidthStep edge w` is equivalent to reachability within `2 ^ w` steps.
* `CslibFrontier.Complexity.hasInfiniteWidthWalk_iff_lasso`: lasso characterization of infinite
  walks on vertices of bit-width `w`.
* `CslibFrontier.Complexity.widthReachable_mem_PSPACE`: implicit bounded-width reachability lies in
  `PSPACE`.
* `CslibFrontier.Complexity.hasInfiniteWidthWalk_mem_PSPACE`: implicit bounded-width infinite-walk
  existence lies in `PSPACE`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib Cslib.Complexity Cslib.Reachability Turing.MultiTapeTM

/-- Directed step relation on `List Bool` vertices of fixed bit-width `w` induced by a Boolean edge
predicate `edge`. -/
@[expose]
def WidthStep (edge : List Bool → List Bool → Bool) (w : ℕ) (u v : List Bool) : Prop :=
  u.length = w ∧ v.length = w ∧ edge u v = true

/-- Existence of an infinite directed walk `f 0 → f 1 → f 2 → ⋯` in `WidthStep edge w` starting at
`src`. -/
@[expose]
def HasInfiniteWidthWalk (edge : List Bool → List Bool → Bool) (w : ℕ) (src : List Bool) : Prop :=
  ∃ f : ℕ → List Bool, f 0 = src ∧ ∀ i : ℕ, WidthStep edge w (f i) (f (i + 1))

/-- **`PSPACE` is closed under polynomially bounded universal bitstring quantification.** -/
theorem setOf_forall_mem_PSPACE {β : Type} {encB : β ↪ List Bool} {B : Set (β × List Bool)}
    {ℓ : β → ℕ} (hB : B ∈ PSPACE (encPair encB encBits))
    (hℓ : ComputableInPolyTime ℓ encB encUnary) :
    {x | ∀ w : List Bool, w.length = ℓ x → (x, w) ∈ B} ∈ PSPACE encB := by
  have hex : {x | ∃ w : List Bool, w.length = ℓ x ∧ (x, w) ∈ Bᶜ} ∈ PSPACE encB :=
    setOf_exists_mem_PSPACE (compl_mem_PSPACE hB) hℓ
  convert compl_mem_PSPACE hex using 1
  ext x
  simp

private lemma encard_length_eq_le (w : ℕ) :
    ({u : List Bool | u.length = w} : Set (List Bool)).encard ≤ (2 ^ w : ℕ) := by
  have hsub : ({u : List Bool | u.length = w} : Set (List Bool)) ⊆
      ((BitString.enumList w).toFinset : Set (List Bool)) := by
    intro u hu
    simp [BitString.mem_enumList, hu]
  refine (Set.encard_le_encard hsub).trans ?_
  rw [Set.encard_coe_eq_coe_finsetCard]
  exact Nat.cast_le.mpr
    ((List.toFinset_card_le (BitString.enumList w)).trans (BitString.length_enumList w).le)

/-- On vertices of bit-width `w`, unbounded reflexive-transitive reachability under
`WidthStep edge w` is equivalent to reachability within `2 ^ w` steps. -/
theorem reflTransGen_widthStep_iff_relatesWithinSteps {edge : List Bool → List Bool → Bool}
    {w : ℕ} {u v : List Bool} :
    Relation.ReflTransGen (WidthStep edge w) u v ↔
      Relation.RelatesWithinSteps (WidthStep edge w) u v (2 ^ w) := by
  apply Relation.reflTransGen_iff_relatesWithinSteps_of_encard_le
  by_cases hu : u.length = w
  · have hsub : {x | Relation.ReflTransGen (WidthStep edge w) u x} ⊆ {x | x.length = w} := by
      intro x hx
      cases hx with
      | refl => exact hu
      | tail _ hstep => exact hstep.2.1
    exact (Set.encard_le_encard hsub).trans
      ((encard_length_eq_le w).trans (Nat.cast_le.mpr (Nat.le_succ _)))
  · have hno : ∀ {x : List Bool}, Relation.ReflTransGen (WidthStep edge w) u x → x = u := by
      intro x hx
      induction hx with
      | refl => rfl
      | tail _ hstep ih =>
        rw [ih] at hstep
        exact absurd hstep.1 hu
    have hsingle : {x | Relation.ReflTransGen (WidthStep edge w) u x} = {u} := by
      ext x
      exact ⟨hno, fun hx => hx ▸ .refl⟩
    rw [hsingle, Set.encard_singleton]
    exact (Nat.cast_one (R := ENat)).symm ▸ Nat.cast_le.mpr (Nat.succ_pos _)

private lemma exists_seq_of_reflTransGen {edge : List Bool → List Bool → Bool} {w : ℕ}
    {x y : List Bool} (h : Relation.ReflTransGen (WidthStep edge w) x y) :
    ∃ (k : ℕ) (seq : ℕ → List Bool), seq 0 = x ∧ seq k = y ∧
      ∀ i < k, WidthStep edge w (seq i) (seq (i + 1)) := by
  induction h with
  | refl =>
    exact ⟨0, fun _ => x, rfl, rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | @tail z c _ hzc ih =>
    obtain ⟨k, seq, h0, hk, hsteps⟩ := ih
    refine ⟨k + 1, fun i => if i ≤ k then seq i else c, by simp [h0], by simp, fun i hi => ?_⟩
    rcases lt_trichotomy i k with hlt | rfl | hgt
    · have h1 : i ≤ k := hlt.le
      have h2 : i + 1 ≤ k := hlt
      simpa [h1, h2] using hsteps i hlt
    · have h2 : ¬(i + 1 ≤ i) := Nat.not_succ_le_self i
      simpa [hk, h2] using hzc
    · omega

/-- **Lasso characterization of infinite walks on bounded-width graphs**: from any `src` of length
`w`, an infinite `WidthStep edge w`-walk exists iff `src` reaches some cycle `u → v →* u` within
`2 ^ w` steps. -/
theorem hasInfiniteWidthWalk_iff_lasso {edge : List Bool → List Bool → Bool}
    {w : ℕ} {src : List Bool} (hsrc : src.length = w) :
    HasInfiniteWidthWalk edge w src ↔
      ∃ u : List Bool, u.length = w ∧
        ∃ v : List Bool, v.length = w ∧
          Relation.RelatesWithinSteps (WidthStep edge w) src u (2 ^ w) ∧
          edge u v = true ∧
          Relation.RelatesWithinSteps (WidthStep edge w) v u (2 ^ w) := by
  constructor
  · rintro ⟨f, rfl, hstep⟩
    let g : Fin (2 ^ w + 1) → {x : List Bool // x ∈ (BitString.enumList w).toFinset} :=
      fun i => ⟨f i.1, List.mem_toFinset.mpr (BitString.mem_enumList.mpr (hstep i.1).1)⟩
    have hcard : Fintype.card {x : List Bool // x ∈ (BitString.enumList w).toFinset} <
        Fintype.card (Fin (2 ^ w + 1)) := by
      rw [Fintype.card_coe, Fintype.card_fin]
      exact Nat.lt_succ_of_le
        ((List.toFinset_card_le (BitString.enumList w)).trans (BitString.length_enumList w).le)
    obtain ⟨i, j, hij, hfg⟩ := Fintype.exists_ne_map_eq_of_card_lt g hcard
    have hval : f i.1 = f j.1 := Subtype.ext_iff.mp hfg
    have hreach : ∀ a b : ℕ, a ≤ b → Relation.ReflTransGen (WidthStep edge w) (f a) (f b) := by
      intro a b hab
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
      induction k with
      | zero => exact .refl
      | succ k ih => exact ih (Nat.le_add_right a k) |>.tail (hstep (a + k))
    obtain ⟨a, b, hab, heq⟩ : ∃ a b : ℕ, a < b ∧ f a = f b := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
      · exact ⟨i.1, j.1, hlt, hval⟩
      · exact ⟨j.1, i.1, hgt, hval.symm⟩
    refine ⟨f a, (hstep a).1, f (a + 1), (hstep a).2.1, ?_, (hstep a).2.2, ?_⟩
    · exact reflTransGen_widthStep_iff_relatesWithinSteps.mp (hreach 0 a (Nat.zero_le a))
    · have hloop : Relation.ReflTransGen (WidthStep edge w) (f (a + 1)) (f b) :=
        hreach (a + 1) b hab
      rw [← heq] at hloop
      exact reflTransGen_widthStep_iff_relatesWithinSteps.mp hloop
  · rintro ⟨u, hu, v, hv, hsu, huv, hvu⟩
    obtain ⟨k₁, s₁, hs₁0, hs₁end, hs₁step⟩ := exists_seq_of_reflTransGen hsu.reflTransGen
    obtain ⟨k₂, s₂, hs₂0, hs₂end, hs₂step⟩ := exists_seq_of_reflTransGen hvu.reflTransGen
    let cyc : ℕ → List Bool := fun m =>
      let r := m % (k₂ + 1)
      if r = 0 then u else s₂ (r - 1)
    have hcyc0 : cyc 0 = u := by simp [cyc]
    have hcyc_step : ∀ m : ℕ, WidthStep edge w (cyc m) (cyc (m + 1)) := by
      intro m
      have hpos : 0 < k₂ + 1 := Nat.succ_pos k₂
      set r := m % (k₂ + 1)
      have hr_lt : r < k₂ + 1 := Nat.mod_lt m hpos
      by_cases hr0 : r = 0
      · by_cases hk₂ : k₂ = 0
        · subst hk₂
          have hm1 : (m + 1) % 1 = 0 := Nat.mod_one _
          have hvu_eq : v = u := hs₂0.symm.trans hs₂end
          simpa [cyc, r, hr0, hm1, ← hvu_eq] using
            (show WidthStep edge w u v from ⟨hu, hv, huv⟩)
        · have hm1 : (m + 1) % (k₂ + 1) = 1 := by
            have hdiv := Nat.div_add_mod m (k₂ + 1)
            have : m + 1 = (k₂ + 1) * (m / (k₂ + 1)) + 1 := by omega
            rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
          simpa [cyc, r, hr0, hm1, hs₂0] using
            (show WidthStep edge w u v from ⟨hu, hv, huv⟩)
      · by_cases hrlast : r = k₂
        · have hk₂_ne : k₂ ≠ 0 := hrlast ▸ hr0
          have hm1 : (m + 1) % (k₂ + 1) = 0 := by
            have : m + 1 = (m / (k₂ + 1) + 1) * (k₂ + 1) := by
              have hdiv := Nat.div_add_mod m (k₂ + 1)
              rw [show m % (k₂ + 1) = k₂ from hrlast] at hdiv
              linarith
            rw [this, Nat.mul_mod_left]
          have hstep_last := hs₂step (k₂ - 1) (by omega)
          rw [show k₂ - 1 + 1 = k₂ by omega, hs₂end] at hstep_last
          simpa [cyc, r, hk₂_ne, hrlast, hm1] using hstep_last
        · have hm1 : (m + 1) % (k₂ + 1) = r + 1 := by
            have hdiv := Nat.div_add_mod m (k₂ + 1)
            have : m + 1 = (k₂ + 1) * (m / (k₂ + 1)) + (r + 1) := by omega
            rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
          have hm1_ne : r + 1 ≠ 0 := Nat.succ_ne_zero r
          have hstep_mid := hs₂step (r - 1) (by omega)
          rw [show r - 1 + 1 = r by omega] at hstep_mid
          simpa [cyc, r, hr0, hm1, hm1_ne] using hstep_mid
    refine ⟨fun i => if i < k₁ then s₁ i else cyc (i - k₁), ?_, fun i => ?_⟩
    · by_cases hk₁ : 0 < k₁
      · simp [hk₁, hs₁0]
      · have hk₁0 : k₁ = 0 := by omega
        subst hk₁0
        simp only [hk₁, ↓reduceIte, Nat.sub_zero, hcyc0]
        exact hs₁end.symm.trans hs₁0
    · rcases lt_trichotomy (i + 1) k₁ with hlt | heq | hgt
      · have hi : i < k₁ := Nat.lt_of_succ_lt hlt
        simpa [hi, hlt] using hs₁step i hi
      · have hi : i < k₁ := by omega
        have hnlt : ¬(i + 1 < k₁) := by omega
        have hsub : i + 1 - k₁ = 0 := by omega
        have hst := hs₁step i hi
        rw [heq, hs₁end] at hst
        simpa [hi, hnlt, hsub, hcyc0] using hst
      · have hnlt1 : ¬(i < k₁) := by omega
        have hnlt2 : ¬(i + 1 < k₁) := by omega
        have hsub : i + 1 - k₁ = (i - k₁) + 1 := by omega
        simpa [hnlt1, hnlt2, hsub] using hcyc_step (i - k₁)

/-- **Implicit bounded-width graph reachability lies in `PSPACE`**. -/
theorem widthReachable_mem_PSPACE {γ : Type} {encIn : γ ↪ List Bool}
    {edge : γ → List Bool → List Bool → Bool}
    (hedge : ComputableInPolyTime
      (fun q : γ × List Bool × List Bool => edge q.1 q.2.1 q.2.2)
      (encEdgeArgs encIn) encBool)
    {width : γ → ℕ} (hwidth : ComputableInPolyTime width encIn encUnary)
    {src dst : γ → List Bool}
    (hsrc_pt : ComputableInPolyTime src encIn encBits)
    (hdst_pt : ComputableInPolyTime dst encIn encBits) :
    {x | (src x).length = width x ∧ (dst x).length = width x ∧
      Relation.ReflTransGen (WidthStep (edge x) (width x)) (src x) (dst x)} ∈ PSPACE encIn := by
  let pad : List Bool → ℕ → List Bool := fun u w =>
    (u.take w) ++ List.replicate (w - (u.take w).length) true
  have hpad_len : ∀ u w, (pad u w).length = w := by
    intro u w
    simp only [pad, List.length_append, List.length_take, List.length_replicate]
    omega
  have hpad_eq : ∀ u w, u.length = w → pad u w = u := by
    intro u w hu
    simp [pad, hu]
  have hrep_true : ComputableInPolyTime (fun n : ℕ => List.replicate n true) encUnary encBits :=
    ComputableInPolyTime.of_eq fun n => (encUnary_apply n).symm
  have hpad_src : ComputableInPolyTime (fun x => pad (src x) (width x)) encIn encBits := by
    have ht := ComputableInPolyTime.bitsTakeWithInput hsrc_pt hwidth
    have htl : ComputableInPolyTime (fun x => ((src x).take (width x)).length) encIn encUnary :=
      ComputableInPolyTime.length_bits_comp ht
    have hdiff : ComputableInPolyTime
        (fun x => width x - ((src x).take (width x)).length) encIn encUnary :=
      ComputableInPolyTime.unary_sub' hwidth htl
    exact ht.bitsAppend (hrep_true.comp hdiff)
  have hpad_dst : ComputableInPolyTime (fun x => pad (dst x) (width x)) encIn encBits := by
    have ht := ComputableInPolyTime.bitsTakeWithInput hdst_pt hwidth
    have htl : ComputableInPolyTime (fun x => ((dst x).take (width x)).length) encIn encUnary :=
      ComputableInPolyTime.length_bits_comp ht
    have hdiff : ComputableInPolyTime
        (fun x => width x - ((dst x).take (width x)).length) encIn encUnary :=
      ComputableInPolyTime.unary_sub' hwidth htl
    exact ht.bitsAppend (hrep_true.comp hdiff)
  have hin : ComputableInPolyTime
      (fun x => (x, width x, width x, pad (src x) (width x), pad (dst x) (width x)))
      encIn (encArgs encIn) :=
    ComputableInPolyTime.id'.prod (hwidth.prod (hwidth.prod (hpad_src.prod hpad_dst)))
  obtain ⟨t, s, hs, hsav⟩ := exists_polyBounded_space_savitch hedge hin
    (fun x => hpad_len (src x) (width x)) (fun x => hpad_len (dst x) (width x))
  have hSavMem :
      {x | savitch (edge x) (width x) (width x)
        (pad (src x) (width x)) (pad (dst x) (width x)) = true} ∈ PSPACE encIn :=
    mem_PSPACE_of_computableInTimeAndSpace hs hsav fun _ => Iff.rfl
  have hLenMem :
      {x | (src x).length = width x ∧ (dst x).length = width x} ∈ PSPACE encIn := by
    apply P_subset_PSPACE
    refine ⟨fun x => decide ((src x).length = width x) && decide ((dst x).length = width x),
      ?_, fun x => by simp⟩
    have hsl := ComputableInPolyTime.length_bits_comp hsrc_pt
    have hdl := ComputableInPolyTime.length_bits_comp hdst_pt
    fun_prop
  convert inter_mem_PSPACE hLenMem hSavMem using 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  refine ⟨fun ⟨hsx, hdx, hr⟩ => ⟨⟨hsx, hdx⟩, ?_⟩, fun ⟨⟨hsx, hdx⟩, hs⟩ => ⟨hsx, hdx, ?_⟩⟩
  · rw [hpad_eq _ _ hsx, hpad_eq _ _ hdx, savitch_iff hsx hdx]
    exact reflTransGen_widthStep_iff_relatesWithinSteps.mp hr
  · rw [hpad_eq _ _ hsx, hpad_eq _ _ hdx, savitch_iff hsx hdx] at hs
    exact reflTransGen_widthStep_iff_relatesWithinSteps.mpr hs

/-- **Implicit bounded-width infinite-walk existence lies in `PSPACE`**. -/
theorem hasInfiniteWidthWalk_mem_PSPACE {γ : Type} {encIn : γ ↪ List Bool}
    {edge : γ → List Bool → List Bool → Bool}
    (hedge : ComputableInPolyTime
      (fun q : γ × List Bool × List Bool => edge q.1 q.2.1 q.2.2)
      (encEdgeArgs encIn) encBool)
    {width : γ → ℕ} (hwidth : ComputableInPolyTime width encIn encUnary)
    {src : γ → List Bool} (hsrc_pt : ComputableInPolyTime src encIn encBits) :
    {x | (src x).length = width x ∧
      HasInfiniteWidthWalk (edge x) (width x) (src x)} ∈ PSPACE encIn := by
  let enc1 := encPair encIn encBits
  let enc2 := encPair enc1 encBits
  have hx2 : ComputableInPolyTime (fun p : (γ × List Bool) × List Bool => p.1.1) enc2 encIn :=
    (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)
  have hu2 : ComputableInPolyTime (fun p : (γ × List Bool) × List Bool => p.1.2) enc2 encBits :=
    (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)
  have hv2 : ComputableInPolyTime (fun p : (γ × List Bool) × List Bool => p.2) enc2 encBits :=
    ComputableInPolyTime.snd _ _
  have hedge2 : ComputableInPolyTime
      (fun q : ((γ × List Bool) × List Bool) × List Bool × List Bool =>
        edge q.1.1.1 q.2.1 q.2.2)
      (encEdgeArgs enc2) encBool :=
    hedge.comp ((hx2.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _))
  have hreach_su :
      {p : (γ × List Bool) × List Bool |
        (src p.1.1).length = width p.1.1 ∧ p.1.2.length = width p.1.1 ∧
        Relation.ReflTransGen (WidthStep (edge p.1.1) (width p.1.1)) (src p.1.1) p.1.2} ∈
      PSPACE enc2 :=
    widthReachable_mem_PSPACE hedge2 (hwidth.comp hx2) (hsrc_pt.comp hx2) hu2
  have hreach_vu :
      {p : (γ × List Bool) × List Bool |
        p.2.length = width p.1.1 ∧ p.1.2.length = width p.1.1 ∧
        Relation.ReflTransGen (WidthStep (edge p.1.1) (width p.1.1)) p.2 p.1.2} ∈
      PSPACE enc2 :=
    widthReachable_mem_PSPACE hedge2 (hwidth.comp hx2) hv2 hu2
  have hedge_uv :
      {p : (γ × List Bool) × List Bool | edge p.1.1 p.1.2 p.2 = true} ∈ PSPACE enc2 :=
    P_subset_PSPACE ⟨fun p => edge p.1.1 p.1.2 p.2,
      hedge.comp (hx2.prod (hu2.prod hv2)), fun _ => Iff.rfl⟩
  have hinner := inter_mem_PSPACE hreach_su (inter_mem_PSPACE hedge_uv hreach_vu)
  have hex_v := setOf_exists_mem_PSPACE (encB := enc1)
    (ℓ := fun q : γ × List Bool => width q.1) hinner
    (hwidth.comp (ComputableInPolyTime.fst _ _))
  have hex_u := setOf_exists_mem_PSPACE (encB := encIn) (ℓ := width) hex_v hwidth
  convert hex_u using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hsx, hwalk⟩
    rw [hasInfiniteWidthWalk_iff_lasso hsx] at hwalk
    obtain ⟨u, hu, v, hv, hsu, huv, hvu⟩ := hwalk
    exact ⟨u, hu, v, hv,
      ⟨hsx, hu, reflTransGen_widthStep_iff_relatesWithinSteps.mpr hsu⟩,
      huv, ⟨hv, hu, reflTransGen_widthStep_iff_relatesWithinSteps.mpr hvu⟩⟩
  · rintro ⟨u, hu, v, hv, ⟨hsx, -, hsu⟩, huv, ⟨-, -, hvu⟩⟩
    refine ⟨hsx, (hasInfiniteWidthWalk_iff_lasso hsx).mpr ⟨u, hu, v, hv, ?_, huv, ?_⟩⟩
    · exact reflTransGen_widthStep_iff_relatesWithinSteps.mp hsu
    · exact reflTransGen_widthStep_iff_relatesWithinSteps.mp hvu

end CslibFrontier.Complexity
