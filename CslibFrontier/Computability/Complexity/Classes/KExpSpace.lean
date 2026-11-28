/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Constructible
public import CslibFrontier.Computability.Complexity.Classes.EXPSPACE
public import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Complexity.Classes.Constructible.Space
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Space
import CslibFrontier.Computability.Complexity.Classes.Space.Closure
import CslibFrontier.Computability.Complexity.Classes.Space.Quantitative
import CslibFrontier.Computability.Complexity.Classes.Space.Time
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Iterated Exponential Space and Time Complexity Classes

The $k$-fold exponential tower hierarchy of deterministic space and time complexity classes
($k\text{-}\mathrm{EXPSPACE}$ and $k\text{-}\mathrm{EXPTIME}$) over arbitrary binary instance
encodings `enc : α ↪ List Bool`:
* `Cslib.Complexity.towerTwo`: base-$2$ exponential tower `towerTwo 0 m = m`,
  `towerTwo (k + 1) m = 2 ^ towerTwo k m`.
* `Cslib.Complexity.KExpSpace` and `Cslib.Complexity.KExpTime`: deterministic $k$-fold exponential
  space and time classes $\bigcup_{d \in \mathbb{N}} \mathrm{DSPACE}(2_k^{n^d})$ and
  $\bigcup_{d \in \mathbb{N}} \mathrm{DTIME}(2_k^{n^d})$.
* `Cslib.Complexity.KExpSpaceHard` and `Cslib.Complexity.KExpSpaceComplete`: polynomial-time
  many-one hardness and completeness for `KExpSpace`.

## Main results

* `Cslib.Complexity.KExpSpace_zero_eq_PSPACE`, `Cslib.Complexity.KExpSpace_one_eq_EXPSPACE`,
  `Cslib.Complexity.KExpTime_zero_eq_P`, `Cslib.Complexity.KExpTime_one_eq_EXP`: agreement with
  `PSPACE`, `EXPSPACE`, `P`, and `EXP` at levels $0$ and $1$.
* `Cslib.Complexity.KExpTime_subset_KExpSpace`, `Cslib.Complexity.KExpSpace_subset_KExpTime_succ`:
  alternating inclusions across all tower heights $k$.
* `Cslib.Complexity.compl_mem_KExpSpace`, `Cslib.Complexity.compl_mem_KExpTime`,
  `Cslib.Complexity.mem_KExpSpace_of_polyTimeReducible`,
  `Cslib.Complexity.mem_KExpTime_of_polyTimeReducible`: closure under complement and
  polynomial-time many-one reductions.
* `Cslib.Complexity.spaceConstructible_towerTwo_succ`,
  `Cslib.Complexity.KExpSpace_ssubset_KExpSpace_succ`: space constructibility of `towerTwo (k + 1)`
  and the strict exponential-space hierarchy `KExpSpace encBits k ⊂ KExpSpace encBits (k + 1)`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Filter

/-- Base-$2$ exponential tower: `towerTwo 0 m = m` and `towerTwo (k + 1) m = 2 ^ towerTwo k m`. -/
@[expose]
def towerTwo : ℕ → ℕ → ℕ
  | 0, m => m
  | k + 1, m => 2 ^ towerTwo k m

@[simp, grind =]
theorem towerTwo_zero (m : ℕ) : towerTwo 0 m = m := rfl

@[simp, grind =]
theorem towerTwo_succ (k m : ℕ) : towerTwo (k + 1) m = 2 ^ towerTwo k m := rfl

/-- Shift identity `towerTwo k (2 ^ m) = towerTwo (k + 1) m`. -/
theorem towerTwo_two_pow (k m : ℕ) : towerTwo k (2 ^ m) = towerTwo (k + 1) m := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [towerTwo_succ, ih]

/-- Right-monotonicity of `towerTwo`. -/
@[gcongr]
theorem towerTwo_mono_right {k m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) : towerTwo k m₁ ≤ towerTwo k m₂ := by
  induction k with
  | zero => exact hm
  | succ k ih => exact Nat.pow_le_pow_right (by decide) ih

/-- Strict right-monotonicity of `towerTwo`. -/
@[gcongr]
theorem towerTwo_strictMono_right {k m₁ m₂ : ℕ} (hm : m₁ < m₂) :
    towerTwo k m₁ < towerTwo k m₂ := by
  induction k with
  | zero => exact hm
  | succ k ih => exact (Nat.pow_lt_pow_iff_right (by norm_num)).mpr ih

/-- Every `m : ℕ` is bounded above by `towerTwo k m`. -/
theorem le_towerTwo (k m : ℕ) : m ≤ towerTwo k m := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ih.trans Nat.lt_two_pow_self.le

/-- Left-monotonicity of `towerTwo`. -/
@[gcongr]
theorem towerTwo_mono_left {k₁ k₂ m : ℕ} (hk : k₁ ≤ k₂) : towerTwo k₁ m ≤ towerTwo k₂ m := by
  induction hk with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans Nat.lt_two_pow_self.le

/-- Strict positivity of `towerTwo (k + 1) m`. -/
theorem towerTwo_pos (k m : ℕ) : 0 < towerTwo (k + 1) m :=
  Nat.pow_pos (by decide)

private theorem add_one_add_towerTwo_le (k a b : ℕ) :
    a + 1 + towerTwo k b ≤ towerTwo k (a + b + 1) := by
  induction k with
  | zero => simp; omega
  | succ k ih =>
    simp only [towerTwo_succ]
    have hsum : a + 1 + 2 ^ towerTwo k b ≤ 2 ^ (a + 1 + towerTwo k b) := by
      have h1 : a + 1 ≤ 2 ^ (a + towerTwo k b) :=
        (Nat.succ_le_of_lt Nat.lt_two_pow_self).trans
          (Nat.pow_le_pow_right (by decide) (Nat.le_add_right a _))
      have h2 : 2 ^ towerTwo k b ≤ 2 ^ (a + towerTwo k b) :=
        Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ a)
      rw [show a + 1 + towerTwo k b = (a + towerTwo k b) + 1 by omega, pow_succ]
      omega
    exact hsum.trans (Nat.pow_le_pow_right (by decide) ih)

/-- Additive absorption into the argument of `towerTwo`. -/
theorem add_towerTwo_le (k a b : ℕ) : a + towerTwo k b ≤ towerTwo k (a + b + 1) :=
  (Nat.add_le_add_right (Nat.le_succ a) _).trans (add_one_add_towerTwo_le k a b)

/-- Affine-multiple absorption at positive tower heights `k + 1`. -/
theorem mul_add_towerTwo_succ_le (k c m : ℕ) :
    c * towerTwo (k + 1) m + c ≤ towerTwo (k + 1) (m + c + 2) := by
  have hpos : 1 ≤ 2 ^ towerTwo k m := Nat.one_le_two_pow
  have h1 : c * 2 ^ towerTwo k m + c ≤ (2 * c) * 2 ^ towerTwo k m := by
    rw [two_mul, add_mul]
    exact Nat.add_le_add_left (by simpa using Nat.mul_le_mul_left c hpos) _
  have h2 : 2 * c ≤ 2 ^ (c + 1) := by
    clear h1
    induction c with
    | zero => decide
    | succ n ih =>
      have hge : 2 ≤ 2 ^ (n + 1) :=
        show 2 ^ 1 ≤ 2 ^ (n + 1) from
          Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ (Nat.zero_le n))
      calc
        2 * (n + 1) = 2 * n + 2 := by ring
        _ ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := Nat.add_le_add ih hge
        _ = 2 ^ (n + 1 + 1) := by rw [pow_succ 2 (n + 1)]; ring
  calc
    c * towerTwo (k + 1) m + c ≤ (2 * c) * 2 ^ towerTwo k m := h1
    _ ≤ 2 ^ (c + 1) * 2 ^ towerTwo k m := Nat.mul_le_mul_right _ h2
    _ = 2 ^ (c + 1 + towerTwo k m) := (pow_add 2 (c + 1) (towerTwo k m)).symm
    _ ≤ 2 ^ towerTwo k (c + 1 + m + 1) :=
      Nat.pow_le_pow_right (by decide) (add_towerTwo_le k (c + 1) m)
    _ = towerTwo (k + 1) (m + c + 2) := by
      rw [towerTwo_succ]; congr 2; omega

/-- Every polynomial-argument level-$k$ tower `c * towerTwo k (n ^ d) + c` is eventually strictly
dominated by `towerTwo (k + 1) n`. -/
theorem eventually_mul_towerTwo_pow_lt_succ (k d c : ℕ) :
    ∀ᶠ n in atTop, c * towerTwo k (n ^ d) + c < towerTwo (k + 1) n := by
  cases k with
  | zero =>
    simpa only [towerTwo_zero, towerTwo_succ] using
      PolynomiallyBounded.eventually_lt_two_pow (f := fun n ↦ c * n ^ d + c) (by fun_prop)
  | succ k =>
    filter_upwards [PolynomiallyBounded.eventually_lt_two_pow
      (f := fun n ↦ n ^ d + c + 2) (by fun_prop)] with n hn
    calc
      c * towerTwo (k + 1) (n ^ d) + c
        ≤ towerTwo (k + 1) (n ^ d + c + 2) := mul_add_towerTwo_succ_le k c (n ^ d)
      _ < towerTwo (k + 1) (2 ^ n) := towerTwo_strictMono_right hn
      _ = towerTwo (k + 2) n := towerTwo_two_pow (k + 1) n

/-- Deterministic $k$-fold exponential space class $k\text{-}\mathrm{EXPSPACE}$. -/
def KExpSpace {α : Type*} (enc : α ↪ List Bool) (k : ℕ) : Set (Set α) :=
  ⋃ d : ℕ, DSPACE enc fun n ↦ towerTwo k (n ^ d)

/-- Membership characterization for `KExpSpace`. -/
theorem mem_KExpSpace_iff {α : Type*} {enc : α ↪ List Bool} {k : ℕ} {A : Set α} :
    A ∈ KExpSpace enc k ↔ ∃ d : ℕ, A ∈ DSPACE enc fun n ↦ towerTwo k (n ^ d) :=
  Set.mem_iUnion

/-- Deterministic $k$-fold exponential time class $k\text{-}\mathrm{EXPTIME}$. -/
def KExpTime {α : Type*} (enc : α ↪ List Bool) (k : ℕ) : Set (Set α) :=
  ⋃ d : ℕ, DTIME enc fun n ↦ towerTwo k (n ^ d)

/-- Membership characterization for `KExpTime`. -/
theorem mem_KExpTime_iff {α : Type*} {enc : α ↪ List Bool} {k : ℕ} {A : Set α} :
    A ∈ KExpTime enc k ↔ ∃ d : ℕ, A ∈ DTIME enc fun n ↦ towerTwo k (n ^ d) :=
  Set.mem_iUnion

/-- Polynomial-time many-one hardness for `KExpSpace`. -/
abbrev KExpSpaceHard {β : Type*} (k : ℕ) (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeHard (fun enc ↦ KExpSpace enc k) encB B

/-- Polynomial-time many-one completeness for `KExpSpace`. -/
abbrev KExpSpaceComplete {β : Type} (k : ℕ) (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeComplete (fun enc ↦ KExpSpace enc k) encB B

/-- Deterministic space `towerTwo k (h n)` for any polynomially bounded `h` lies in
`KExpSpace enc k`. -/
theorem DSPACE_towerTwo_subset_KExpSpace {α : Type*} {enc : α ↪ List Bool} {k : ℕ} {h : ℕ → ℕ}
    (hh : PolynomiallyBounded h) :
    DSPACE enc (fun n ↦ towerTwo k (h n)) ⊆ KExpSpace enc k := fun _ hA ↦
  let ⟨d, hd⟩ := hh
  mem_KExpSpace_iff.mpr ⟨d, DSPACE_mono_of_eventually_le
    (hd.mono fun _ hn ↦ towerTwo_mono_right hn) hA⟩

/-- Deterministic time `towerTwo k (h n)` for any polynomially bounded `h` lies in
`KExpTime enc k`. -/
theorem DTIME_towerTwo_subset_KExpTime {α : Type*} {enc : α ↪ List Bool} {k : ℕ} {h : ℕ → ℕ}
    (hh : PolynomiallyBounded h) :
    DTIME enc (fun n ↦ towerTwo k (h n)) ⊆ KExpTime enc k := fun _ hA ↦
  let ⟨d, hd⟩ := hh
  mem_KExpTime_iff.mpr ⟨d, DTIME_mono_of_eventually_le
    (hd.mono fun _ hn ↦ towerTwo_mono_right hn) hA⟩

/-- Level $0$ of `KExpSpace` coincides with `PSPACE`. -/
theorem KExpSpace_zero_eq_PSPACE {α : Type} (enc : α ↪ List Bool) :
    KExpSpace enc 0 = PSPACE enc :=
  Set.ext fun _ ↦ mem_KExpSpace_iff.trans mem_PSPACE_iff_exists_mem_DSPACE.symm

/-- Level $1$ of `KExpSpace` coincides with `EXPSPACE`. -/
theorem KExpSpace_one_eq_EXPSPACE {α : Type*} (enc : α ↪ List Bool) :
    KExpSpace enc 1 = EXPSPACE enc :=
  Set.ext fun _ ↦ mem_KExpSpace_iff.trans mem_EXPSPACE_iff.symm

/-- Level $0$ of `KExpTime` coincides with `P`. -/
theorem KExpTime_zero_eq_P {α : Type} (enc : α ↪ List Bool) :
    KExpTime enc 0 = P enc :=
  Set.ext fun _ ↦ mem_KExpTime_iff.trans mem_P_iff_exists_mem_DTIME.symm

/-- Level $1$ of `KExpTime` coincides with `EXP`. -/
theorem KExpTime_one_eq_EXP {α : Type*} (enc : α ↪ List Bool) :
    KExpTime enc 1 = EXP enc :=
  Set.ext fun _ ↦ mem_KExpTime_iff.trans mem_EXP_iff.symm

/-- Monotonicity of `KExpSpace` in the tower height `k`. -/
theorem KExpSpace_mono {α : Type*} {enc : α ↪ List Bool} {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    KExpSpace enc k₁ ⊆ KExpSpace enc k₂ := fun _ hA ↦
  let ⟨d, hd⟩ := mem_KExpSpace_iff.mp hA
  mem_KExpSpace_iff.mpr ⟨d, DSPACE_mono (fun _ ↦ towerTwo_mono_left hk) hd⟩

/-- Monotonicity of `KExpTime` in the tower height `k`. -/
theorem KExpTime_mono {α : Type*} {enc : α ↪ List Bool} {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    KExpTime enc k₁ ⊆ KExpTime enc k₂ := fun _ hA ↦
  let ⟨d, hd⟩ := mem_KExpTime_iff.mp hA
  mem_KExpTime_iff.mpr ⟨d, DTIME_mono (fun _ ↦ towerTwo_mono_left hk) hd⟩

/-- Time bounds space at every level: `KExpTime enc k ⊆ KExpSpace enc k`. -/
theorem KExpTime_subset_KExpSpace {α : Type*} {enc : α ↪ List Bool} {k : ℕ} :
    KExpTime enc k ⊆ KExpSpace enc k := fun _ hA ↦
  let ⟨d, hd⟩ := mem_KExpTime_iff.mp hA
  mem_KExpSpace_iff.mpr ⟨d, DTIME_subset_DSPACE hd⟩

/-- Space bounds time at the next exponential level: `KExpSpace enc k ⊆ KExpTime enc (k + 1)`. -/
theorem KExpSpace_subset_KExpTime_succ {α : Type*} {enc : α ↪ List Bool} {k : ℕ} :
    KExpSpace enc k ⊆ KExpTime enc (k + 1) := by
  intro A hA
  obtain ⟨d, hd⟩ := mem_KExpSpace_iff.mp hA
  obtain ⟨c, hc⟩ := exists_mem_DTIME_of_mem_DSPACE hd
  have hpoly : PolynomiallyBounded (fun n ↦ (c + 2) * (n ^ d + n + c + 3)) := by fun_prop
  refine DTIME_towerTwo_subset_KExpTime hpoly (DTIME_mono (fun n ↦ ?_) hc)
  have h1 : n + 2 ≤ 2 ^ (n + 2) := Nat.lt_two_pow_self.le
  calc
    (n + 2) * 2 ^ (c * towerTwo k (n ^ d))
      ≤ 2 ^ (n + 2) * 2 ^ (c * towerTwo k (n ^ d)) := Nat.mul_le_mul_right _ h1
    _ = 2 ^ (n + 2 + c * towerTwo k (n ^ d)) := (pow_add 2 _ _).symm
    _ ≤ towerTwo (k + 1) ((c + 2) * (n ^ d + n + c + 3)) := by
      rw [towerTwo_succ]
      refine Nat.pow_le_pow_right (by decide) ?_
      cases k with
      | zero =>
        simp only [towerTwo_zero]
        have hnd : c * n ^ d ≤ (c + 2) * n ^ d := Nat.mul_le_mul_right _ (by omega)
        have hrest : n + 2 ≤ (c + 2) * (n + c + 3) :=
          (by omega : n + 2 ≤ 1 * (n + c + 3)).trans (Nat.mul_le_mul_right _ (by omega))
        calc
          n + 2 + c * n ^ d ≤ (c + 2) * (n + c + 3) + (c + 2) * n ^ d :=
            Nat.add_le_add hrest hnd
          _ = (c + 2) * (n ^ d + n + c + 3) := by ring
      | succ j =>
        calc
          n + 2 + c * towerTwo (j + 1) (n ^ d)
            ≤ n + 2 + (c * towerTwo (j + 1) (n ^ d) + c) := by omega
          _ ≤ n + 2 + towerTwo (j + 1) (n ^ d + c + 2) :=
            Nat.add_le_add_left (mul_add_towerTwo_succ_le j c (n ^ d)) (n + 2)
          _ ≤ towerTwo (j + 1) ((n + 2) + (n ^ d + c + 2) + 1) :=
            add_towerTwo_le (j + 1) (n + 2) (n ^ d + c + 2)
          _ ≤ towerTwo (j + 1) ((c + 2) * (n ^ d + n + c + 3)) :=
            towerTwo_mono_right
              ((by omega : (n + 2) + (n ^ d + c + 2) + 1 ≤ 2 * (n ^ d + n + c + 3)).trans
                (Nat.mul_le_mul_right _ (by omega)))

/-- Closure of `KExpSpace` under complement. -/
theorem compl_mem_KExpSpace {α : Type} {enc : α ↪ List Bool} {k : ℕ} {A : Set α}
    (h : A ∈ KExpSpace enc k) : Aᶜ ∈ KExpSpace enc k :=
  let ⟨d, hd⟩ := mem_KExpSpace_iff.mp h
  mem_KExpSpace_iff.mpr ⟨d, compl_mem_DSPACE hd⟩

/-- Closure of `KExpTime` under complement. -/
theorem compl_mem_KExpTime {α : Type} {enc : α ↪ List Bool} {k : ℕ} {A : Set α}
    (h : A ∈ KExpTime enc k) : Aᶜ ∈ KExpTime enc k :=
  let ⟨d, hd⟩ := mem_KExpTime_iff.mp h
  mem_KExpTime_iff.mpr ⟨d, compl_mem_DTIME hd⟩

/-- Downward closure of `KExpSpace` under polynomial-time many-one reductions. -/
theorem mem_KExpSpace_of_polyTimeReducible {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {k : ℕ} {A : Set α} {B : Set β}
    (hAB : PolyTimeReducible encA encB A B) (hB : B ∈ KExpSpace encB k) :
    A ∈ KExpSpace encA k := by
  obtain ⟨f, hf, hred⟩ := hAB
  obtain ⟨d, hd⟩ := mem_KExpSpace_iff.mp hB
  obtain ⟨TB, hBO⟩ := computableInO_indicator_of_mem_DSPACE hd
  obtain ⟨Tf, Sf, -, hSf, hfO⟩ := hf.exists_computableInO
  obtain ⟨c, e, hce⟩ := (hSf.add hf.polyBounded_length).exists_le
  have hcomp := hBO.comp hfO
  have hset : A = {a | (indicator B ∘ f) a = true} := by
    ext a
    exact (hred a).trans (by simp [indicator])
  rw [hset]
  let hbound : ℕ → ℕ := fun n ↦ c * (n + 1) ^ e + (c * (n + 1) ^ e) ^ d + 1
  have hpoly : PolynomiallyBounded hbound := by fun_prop
  refine DSPACE_towerTwo_subset_KExpSpace hpoly
    (setOf_mem_DSPACE_of_computableInO hcomp fun a ↦ ?_)
  have hca := hce a
  have hlen : (encB (f a)).length ^ d ≤ (c * ((encA a).length + 1) ^ e) ^ d :=
    Nat.pow_le_pow_left (by omega) d
  calc
    Sf a + towerTwo k ((encB (f a)).length ^ d)
      ≤ c * ((encA a).length + 1) ^ e + towerTwo k ((c * ((encA a).length + 1) ^ e) ^ d) :=
        Nat.add_le_add (by omega) (towerTwo_mono_right hlen)
    _ ≤ towerTwo k (hbound (encA a).length) :=
      add_towerTwo_le k (c * ((encA a).length + 1) ^ e) ((c * ((encA a).length + 1) ^ e) ^ d)

/-- Downward closure of `KExpTime` under polynomial-time many-one reductions. -/
theorem mem_KExpTime_of_polyTimeReducible {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {k : ℕ} {A : Set α} {B : Set β}
    (hAB : PolyTimeReducible encA encB A B) (hB : B ∈ KExpTime encB k) :
    A ∈ KExpTime encA k := by
  obtain ⟨f, hf, hred⟩ := hAB
  obtain ⟨d, hd⟩ := mem_KExpTime_iff.mp hB
  obtain ⟨Tf, Sf, hTf, -, hfO⟩ := hf.exists_computableInO
  obtain ⟨c, e, hce⟩ := (hTf.add hf.polyBounded_length).exists_le
  let hbound : ℕ → ℕ := fun n ↦ c * (n + 1) ^ e + (c * (n + 1) ^ e) ^ d + 1
  have hpre : f ⁻¹' B ∈ DTIME encA (fun n ↦ towerTwo k (hbound n)) := by
    refine preimage_mem_DTIME (C := 1) hd hfO fun a ↦ ?_
    have hca := hce a
    have hlen : (encB (f a)).length ^ d ≤ (c * ((encA a).length + 1) ^ e) ^ d :=
      Nat.pow_le_pow_left (by omega) d
    have hle : Tf a + towerTwo k ((encB (f a)).length ^ d) ≤
        towerTwo k (hbound (encA a).length) := by
      calc
        Tf a + towerTwo k ((encB (f a)).length ^ d)
          ≤ c * ((encA a).length + 1) ^ e + towerTwo k ((c * ((encA a).length + 1) ^ e) ^ d) :=
            Nat.add_le_add (by omega) (towerTwo_mono_right hlen)
        _ ≤ towerTwo k (hbound (encA a).length) :=
          add_towerTwo_le k _ _
    omega
  have hA_eq : A = f ⁻¹' B := Set.ext hred
  rw [hA_eq]
  exact DTIME_towerTwo_subset_KExpTime (by fun_prop) hpre

private theorem computableInO_weaken_space {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {T S S' : α → ℕ}
    (h : ComputableInO f encIn encOut T S) (k : ℕ) (hS : ∀ a, S a ≤ k * (S' a + 1)) :
    ComputableInO f encIn encOut T S' :=
  h.mono (k + 1)
    (fun a ↦ (Nat.le_succ (T a)).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos k)))
    (fun a ↦ (hS a).trans (Nat.mul_le_mul_right _ (Nat.le_succ k)))

private theorem computableInO_unary_towerTwo (k : ℕ) :
    ∃ T : List Bool → ℕ,
      ComputableInO (fun x : List Bool ↦ towerTwo k x.length) encBits encUnary T
        (fun x ↦ towerTwo k x.length) := by
  induction k with
  | zero => exact ⟨_, ComputableInO.lengthUnary⟩
  | succ k ih =>
    obtain ⟨_, hT⟩ := ih
    refine ⟨_, computableInO_weaken_space (ComputableInO.unary_two_pow.comp hT) 2 fun x ↦ ?_⟩
    dsimp only [Function.comp_apply, towerTwo_succ]
    have hle : towerTwo k x.length ≤ 2 ^ towerTwo k x.length := Nat.lt_two_pow_self.le
    omega

/-- For every `k : ℕ`, `fun n ↦ towerTwo (k + 1) n` is space-constructible. -/
theorem spaceConstructible_towerTwo_succ (k : ℕ) :
    SpaceConstructible fun n ↦ towerTwo (k + 1) n := by
  obtain ⟨T, hT⟩ := computableInO_unary_towerTwo k
  have hbin := ((ComputableInDegree.two_pow_length encUnary).inO_one.comp_linear
    hT).of_enc_eq (encC := encNat) (g := fun x : List Bool ↦ towerTwo (k + 1) x.length) fun x ↦ by
      simp only [Function.comp_apply, encUnary_apply, List.length_replicate, towerTwo_succ]
  refine SpaceConstructible.of_computableInO 1 hbin fun x ↦ ?_
  have hle : towerTwo k x.length ≤ towerTwo (k + 1) x.length :=
    towerTwo_mono_left (Nat.le_succ k)
  omega

/-- Strict exponential-space hierarchy theorem on binary words:
`KExpSpace encBits k ⊂ KExpSpace encBits (k + 1)` for all `k : ℕ`. -/
theorem KExpSpace_ssubset_KExpSpace_succ (k : ℕ) :
    KExpSpace encBits k ⊂ KExpSpace encBits (k + 1) := by
  let G : ℕ → ℕ := fun n ↦ 4 * towerTwo (k + 1) n
  have hlog : ∀ n, Nat.log2 n ≤ towerTwo (k + 1) n := fun n ↦
    (Nat.log2_le_self n).trans (le_towerTwo (k + 1) n)
  refine (Set.ssubset_iff_of_subset (KExpSpace_mono (Nat.le_succ k))).mpr
    ⟨{x | spaceDiagonal G x = true}, ?_, fun hmem ↦ ?_⟩
  · refine mem_KExpSpace_iff.mpr ⟨1, ?_⟩
    refine DSPACE_mono_of_le_mul_add (s₁ := G) (C := 4) (fun n ↦ by simp [G]) ?_
    exact setOf_spaceDiagonal_mem_DSPACE ((spaceConstructible_towerTwo_succ k).const_mul 4)
      fun n ↦ (hlog n).trans (Nat.le_mul_of_pos_left _ (by norm_num))
  · obtain ⟨d, hd⟩ := mem_KExpSpace_iff.mp hmem
    refine setOf_spaceDiagonal_notMem_DSPACE (f := fun n ↦ towerTwo k (n ^ d))
      (fun n ↦ Nat.mul_le_mul_left 4 (hlog n)) (fun c ↦ ?_) hd
    filter_upwards [eventually_mul_towerTwo_pow_lt_succ k d c] with n hn
    exact hn.le.trans (Nat.le_mul_of_pos_left _ (by norm_num))

end Cslib.Complexity
