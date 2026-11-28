/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Computability.Communication.Protocol
public import CslibFrontier.Computability.Communication.Nondeterministic.PartitionCover
import CslibFrontier.Computability.Communication.Rectangle
import CslibFrontier.Computability.Communication.Operations

/-!
# Strengthened Partition-Cover Lower Bounds, Direct Sums, and Protocol Tree Pruning

Deterministic communication complexity lower bounds from monochromatic partition covers, direct-sum
additivity of partition cover numbers, multi-ary protocol compilation, and leaf-count pruning of
binary protocols on finite domains.

For any Boolean function `f : X → Y → Bool`, the `true`-labelled leaves of a deterministic binary
protocol partition `f⁻¹(true)` into `1`-monochromatic rectangles, giving the standard bound
`⌈log₂ χ₁(f)⌉ ≤ ecomplexityFun f` where `χ₁(f) = partitionCoverNumberFun true f Set.univ Set.univ`.
When `f` is non-constant (attaining both `true` and `false`), at least one protocol leaf must output
`false`; strong induction on protocol depth sharpens the bound by an additive bit to
`⌈log₂ χ₁(f)⌉ + 1 ≤ ecomplexityFun f`.

## Main definitions

* `CslibFrontier.Computability.Communication.IsNonConstantBoolFun`: predicate that
  `f : X → Y → Bool` attains both `true` and `false`.
* `CslibFrontier.Computability.Communication.directSumBool`: block-diagonal direct sum
  `X₁ ⊕ X₂ → Y₁ ⊕ Y₂ → Bool` of two Boolean communication matrices, vanishing off the diagonal.
* `CslibFrontier.Computability.Communication.MultiaryProtocol`: deterministic multi-ary protocol
  trees with finite positive branching arities and binary compilation `MultiaryProtocol.toProtocol`.

## Main results

* `CslibFrontier.Computability.Communication.partitionCoverNumberFun_le_true_leaves`:
  `χ₁(f)` is at most the number of `true`-labelled leaves of any binary protocol computing `f`.
* `CslibFrontier.Computability.Communication.clog_partitionCoverNumberFun_le_ecomplexityFun`:
  `⌈log₂ χ₁(f)⌉ ≤ ecomplexityFun f`.
* `clog_partitionCoverNumberFun_add_one_le_ecomplexityFun`:
  for every non-constant `f : X → Y → Bool`, `⌈log₂ χ₁(f)⌉ + 1 ≤ ecomplexityFun f`.
* `CslibFrontier.Computability.Communication.partitionCoverNumberFun_directSumBool`:
  `χ₁(directSumBool f₁ f₂) = χ₁(f₁) + χ₁(f₂)`.
* `CslibFrontier.Computability.Communication.MultiaryProtocol.ecomplexityFun_le_binaryDepth`:
  compiling a multi-ary protocol computing `f` into binary messages bounds `ecomplexityFun f` by its
  root-to-leaf ceiling-logarithm depth `binaryDepth`.
* `CslibFrontier.Computability.Communication.exists_pruned_protocol`:
  every binary protocol on non-empty `Fin rows × Fin cols` can be pruned to at most `rows * cols`
  leaves while computing the same function without increasing depth.
-/

public section

namespace CslibFrontier.Computability.Communication

open Cslib Cslib.Communication

/-! ### Non-constant Boolean matrices and block-diagonal direct sums -/

/-- A Boolean function `f : X → Y → Bool` is non-constant if it attains both `true` and `false`. -/
public def IsNonConstantBoolFun {X Y : Type*} (f : X → Y → Bool) : Prop :=
  (∃ x y, f x y = true) ∧ (∃ x y, f x y = false)

/-- Unfolding characterization of `IsNonConstantBoolFun`. -/
public theorem isNonConstantBoolFun_iff {X Y : Type*} {f : X → Y → Bool} :
    IsNonConstantBoolFun f ↔ (∃ x y, f x y = true) ∧ (∃ x y, f x y = false) := by
  rfl

/-- Block-diagonal direct sum of two Boolean functions, evaluating to `f₁` on `Sum.inl × Sum.inl`,
`f₂` on `Sum.inr × Sum.inr`, and `false` on off-diagonal blocks. -/
@[expose] public def directSumBool {X₁ Y₁ X₂ Y₂ : Type*} (f₁ : X₁ → Y₁ → Bool)
    (f₂ : X₂ → Y₂ → Bool) : X₁ ⊕ X₂ → Y₁ ⊕ Y₂ → Bool
  | .inl x₁, .inl y₁ => f₁ x₁ y₁
  | .inr x₂, .inr y₂ => f₂ x₂ y₂
  | .inl _, .inr _ => false
  | .inr _, .inl _ => false

/-! ### Multi-ary deterministic protocols and binary compilation -/

/-- A deterministic multi-ary communication protocol tree where each internal node branches over
`Fin k` for some positive arity `k`. -/
public inductive MultiaryProtocol (X Y Z : Type*) where
  /-- Leaf outputting `z`. -/
  | output (z : Z)
  /-- Alice sends a message in `Fin k` (`0 < k`). -/
  | alice (k : ℕ) (hk : 0 < k) (send : X → Fin k) (children : Fin k → MultiaryProtocol X Y Z)
  /-- Bob sends a message in `Fin k` (`0 < k`). -/
  | bob (k : ℕ) (hk : 0 < k) (send : Y → Fin k) (children : Fin k → MultiaryProtocol X Y Z)

namespace MultiaryProtocol

variable {X Y Z : Type*}

/-- Output computed by a multi-ary protocol on `(x, y)`. -/
@[expose] public def run : MultiaryProtocol X Y Z → X → Y → Z
  | output z, _, _ => z
  | alice _ _ send children, x, y => (children (send x)).run x y
  | bob _ _ send children, x, y => (children (send y)).run x y

/-- Number of leaves of a multi-ary protocol tree. -/
@[expose] public def leafCount : MultiaryProtocol X Y Z → ℕ
  | output _ => 1
  | alice k _ _ children => ∑ i : Fin k, (children i).leafCount
  | bob k _ _ children => ∑ i : Fin k, (children i).leafCount

/-- Maximum of `f : Fin k → ℕ` (`0` when `k = 0`). -/
@[expose] public def finMax : (k : ℕ) → (Fin k → ℕ) → ℕ
  | 0, _ => 0
  | _ + 1, f => Finset.sup Finset.univ f

@[simp]
public theorem le_finMax {k : ℕ} (f : Fin k → ℕ) (i : Fin k) : f i ≤ finMax k f := by
  cases k with
  | zero => exact i.elim0
  | succ _ => exact Finset.le_sup (Finset.mem_univ i)

public theorem finMax_le {k : ℕ} {f : Fin k → ℕ} {b : ℕ} (h : ∀ i, f i ≤ b) :
    finMax k f ≤ b := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ _ => exact Finset.sup_le fun i _ ↦ h i

/-- Binary depth of a multi-ary protocol tree: maximum root-to-leaf sum of `⌈log₂ k⌉`. -/
@[expose] public def binaryDepth : MultiaryProtocol X Y Z → ℕ
  | output _ => 0
  | alice k _ _ children => Nat.clog 2 k + finMax k fun i ↦ (children i).binaryDepth
  | bob k _ _ children => Nat.clog 2 k + finMax k fun i ↦ (children i).binaryDepth

/-- Encode `Fin k` into `BitString (Nat.clog 2 k)`. -/
public def encodeFin {k : ℕ} (i : Fin k) : BitString (Nat.clog 2 k) :=
  (BitString.equivFin (Nat.clog 2 k)).symm
    ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_pow_clog Nat.one_lt_two k)⟩

/-- Compile a multi-ary protocol into a binary `Protocol` by encoding each `k`-ary message in
`⌈log₂ k⌉` bits. -/
public def toProtocol (defaultOut : Z) : MultiaryProtocol X Y Z → Protocol X Y Z
  | output z => .output z
  | alice k _ send children =>
    Protocol.aliceSend (Nat.clog 2 k) (fun x ↦ encodeFin (send x)) fun m ↦
      let v := (BitString.equivFin (Nat.clog 2 k) m).val
      if h : v < k then (children ⟨v, h⟩).toProtocol defaultOut else .output defaultOut
  | bob k _ send children =>
    Protocol.bobSend (Nat.clog 2 k) (fun y ↦ encodeFin (send y)) fun m ↦
      let v := (BitString.equivFin (Nat.clog 2 k) m).val
      if h : v < k then (children ⟨v, h⟩).toProtocol defaultOut else .output defaultOut

@[simp]
public theorem run_toProtocol (defaultOut : Z) (π : MultiaryProtocol X Y Z) (x : X) (y : Y) :
    (π.toProtocol defaultOut).run x y = π.run x y := by
  induction π with
  | output z => rfl
  | alice _ _ send children ih =>
    simp only [toProtocol, Protocol.run_aliceSend, encodeFin, Equiv.apply_symm_apply,
      (send x).isLt, dite_true, Fin.eta, ih, run]
  | bob _ _ send children ih =>
    simp only [toProtocol, Protocol.run_bobSend, encodeFin, Equiv.apply_symm_apply,
      (send y).isLt, dite_true, Fin.eta, ih, run]

public theorem depth_toProtocol_le (defaultOut : Z) (π : MultiaryProtocol X Y Z) :
    (π.toProtocol defaultOut).depth ≤ π.binaryDepth := by
  induction π with
  | output _ => simp [toProtocol, binaryDepth]
  | alice k _ _ children ih =>
    simp only [toProtocol, binaryDepth]
    refine Protocol.depth_aliceSend_le fun m ↦ ?_
    split_ifs with h
    · exact (ih ⟨_, h⟩).trans (le_finMax (fun i ↦ (children i).binaryDepth) ⟨_, h⟩)
    · simp
  | bob k _ _ children ih =>
    simp only [toProtocol, binaryDepth]
    refine Protocol.depth_bobSend_le fun m ↦ ?_
    split_ifs with h
    · exact (ih ⟨_, h⟩).trans (le_finMax (fun i ↦ (children i).binaryDepth) ⟨_, h⟩)
    · simp

public theorem ecomplexityFun_le_binaryDepth {f : X → Y → Bool}
    (π : MultiaryProtocol X Y Bool) (hπ : π.run = f) :
    Protocol.ecomplexityFun f ≤ π.binaryDepth := by
  refine Protocol.ecomplexityFun_le_iff.mpr ⟨π.toProtocol false, ?_, depth_toProtocol_le false π⟩
  funext x y
  rw [run_toProtocol, hπ]

end MultiaryProtocol

/-! ### Partition-cover lower bounds on deterministic communication complexity -/

/-- The `true`-labelled leaves of any binary protocol computing `f` form a partition cover of
`f⁻¹(true)`. -/
public theorem partitionCoverNumberFun_le_true_leaves {X Y : Type*} {f : X → Y → Bool}
    (p : Protocol X Y Bool) (hp : p.run = f) :
    Nondeterministic.partitionCoverNumberFun true f Set.univ Set.univ ≤
      Fintype.card {i : Fin p.leafCount // p.leafOutput i = true} := by
  have hcov : Nondeterministic.IsPartitionCover true (fun x y b ↦ f x y = b) Set.univ Set.univ
      (fun i : {i : Fin p.leafCount // p.leafOutput i = true} ↦
        (p.leafAlice i.val, p.leafBob i.val)) := by
    refine ⟨fun i x _ hx y _ hy ↦ ?_, fun x _ y _ hnf ↦ ?_⟩
    · dsimp only
      rw [← hp, Protocol.run_eq_leafOutput hx hy, i.property]
    · have hf : f x y = true := by cases h : f x y <;> simp_all
      have hout : p.leafOutput (p.leaf x y) = true := by
        rw [← Protocol.run_eq_leafOutput_leaf, hp, hf]
      refine ⟨⟨p.leaf x y, hout⟩, ⟨Protocol.mem_leafAlice_leaf, Protocol.mem_leafBob_leaf⟩, ?_⟩
      rintro ⟨i, hi⟩ ⟨hx, hy⟩
      exact Subtype.ext (Protocol.leaf_eq_iff.mpr ⟨hx, hy⟩).symm
  exact hcov.partitionCoverNumber_le

/-- Standard partition-cover lower bound: `⌈log₂ χ₁(f)⌉ ≤ ecomplexityFun f`. -/
public theorem clog_partitionCoverNumberFun_le_ecomplexityFun {X Y : Type*} {f : X → Y → Bool}
    {r : ℕ} (hr : Nondeterministic.partitionCoverNumberFun true f Set.univ Set.univ = r) :
    (Nat.clog 2 r : ℕ∞) ≤ Protocol.ecomplexityFun f := by
  refine Protocol.le_ecomplexityFun_iff.mpr fun p hp ↦ ?_
  have hcard : Fintype.card {i : Fin p.leafCount // p.leafOutput i = true} ≤ p.leafCount :=
    (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin p.leafCount)
  have hpow : Nondeterministic.partitionCoverNumberFun true f Set.univ Set.univ ≤
      (2 ^ p.depth : ℕ) :=
    (partitionCoverNumberFun_le_true_leaves p hp).trans
      (by exact_mod_cast hcard.trans p.leafCount_le_two_pow_depth)
  have hle : r ≤ 2 ^ p.depth := by exact_mod_cast hr ▸ hpow
  exact_mod_cast Nat.clog_le_of_le_pow hle

private theorem partitionCoverNumberFun_le_one_of_not_nonConstant {X Y : Type*}
    {f : X → Y → Bool} (h : ¬IsNonConstantBoolFun f) :
    Nondeterministic.partitionCoverNumberFun true f Set.univ Set.univ ≤ 1 := by
  rw [isNonConstantBoolFun_iff, not_and_or] at h
  rcases h with hno1 | hno0
  · push Not at hno1
    have h0 : Nondeterministic.partitionCoverNumberFun true f Set.univ Set.univ ≤ (0 : ℕ) := by
      rw [Nondeterministic.partitionCoverNumberFun, Nondeterministic.partitionCoverNumber_le_iff]
      refine ⟨Fin.elim0, fun w ↦ w.elim0, fun x _ y _ hnf ↦ ?_⟩
      exact absurd (by cases hxy : f x y <;> simp_all : f x y = true) (by simp [hno1 x y])
    exact h0.trans (by norm_num)
  · push Not at hno0
    have h1 : ∀ x y, f x y = true := fun x y ↦ by cases hxy : f x y <;> simp_all
    change Nondeterministic.partitionCoverNumberFun true f Set.univ Set.univ ≤ (1 : ℕ)
    rw [Nondeterministic.partitionCoverNumberFun, Nondeterministic.partitionCoverNumber_le_iff]
    exact ⟨fun _ ↦ (Set.univ, Set.univ), fun _ _ _ _ _ _ _ ↦ h1 _ _,
      fun _ _ _ _ _ ↦ ⟨0, ⟨trivial, trivial⟩, fun w _ ↦ Subsingleton.elim w 0⟩⟩

private theorem one_le_ecomplexityFun_of_nonConstant {X Y : Type*}
    {f : X → Y → Bool} (hf : IsNonConstantBoolFun f) :
    (1 : ℕ∞) ≤ Protocol.ecomplexityFun f := by
  refine Protocol.le_ecomplexityFun_iff.mpr fun p hp ↦ ?_
  cases p with
  | output z =>
    obtain ⟨⟨x₁, y₁, h₁⟩, ⟨x₀, y₀, h₀⟩⟩ := isNonConstantBoolFun_iff.mp hf
    have hz₁ : z = true := by simpa [← hp] using h₁
    have hz₀ : z = false := by simpa [← hp] using h₀
    exact Bool.noConfusion (hz₁.symm.trans hz₀)
  | alice _ _ _ | bob _ _ _ => simp

private theorem partitionCoverNumberFun_eq_one_of_depth_eq_one {X Y : Type*} {f : X → Y → Bool}
    (hf : IsNonConstantBoolFun f) (p : Protocol X Y Bool) (hp : p.run = f) (hd : p.depth = 1) :
    Nondeterministic.partitionCoverNumberFun true f Set.univ Set.univ = 1 := by
  obtain ⟨⟨x₁, y₁, h₁⟩, ⟨x₀, y₀, h₀⟩⟩ := isNonConstantBoolFun_iff.mp hf
  apply le_antisymm
  · have hlt : Fintype.card {i : Fin p.leafCount // p.leafOutput i = true} < p.leafCount := by
      have hne : p.leafOutput (p.leaf x₀ y₀) ≠ true := by
        rw [← Protocol.run_eq_leafOutput_leaf, hp, h₀]; decide
      have hcard := Fintype.card_subtype_lt
        (p := fun i : Fin p.leafCount ↦ p.leafOutput i = true) hne
      rwa [Fintype.card_fin] at hcard
    have hleaf : p.leafCount ≤ 2 := by simpa [hd] using p.leafCount_le_two_pow_depth
    have hle1 : Fintype.card {i : Fin p.leafCount // p.leafOutput i = true} ≤ 1 := by omega
    exact (partitionCoverNumberFun_le_true_leaves p hp).trans (by exact_mod_cast hle1)
  · refine Nondeterministic.le_partitionCoverNumber_iff.mpr fun r C hC ↦ ?_
    obtain ⟨w, _⟩ := (hC.2 x₁ trivial y₁ trivial (by simp [h₁])).exists
    exact_mod_cast Fin.pos w

private theorem partitionCoverNumberFun_le_add_aliceSplit {X Y : Type*} (f : X → Y → Bool)
    (send : X → Bool) :
    Nondeterministic.partitionCoverNumberFun true f Set.univ Set.univ ≤
      Nondeterministic.partitionCoverNumberFun true
          (fun (x : {x : X // send x = false}) y ↦ f x.val y) Set.univ Set.univ +
        Nondeterministic.partitionCoverNumberFun true
          (fun (x : {x : X // send x = true}) y ↦ f x.val y) Set.univ Set.univ := by
  have hfib := Nondeterministic.partitionCoverNumber_le_sum_fibers
    (z := true) (R := fun x y b ↦ f x y = b) (A := Set.univ) (B := Set.univ)
    send (fun _ : Y ↦ ())
  refine hfib.trans ?_
  rw [Fintype.sum_bool, Fintype.sum_unique, Fintype.sum_unique, add_comm]
  refine add_le_add ?_ ?_
  · refine Nondeterministic.le_partitionCoverNumber_iff.mpr fun r C hC ↦ ?_
    have hcov : Nondeterministic.IsPartitionCover true (fun x y b ↦ f x y = b)
        (Set.univ ∩ send ⁻¹' {false}) (Set.univ ∩ (fun _ : Y ↦ ()) ⁻¹' {()})
        (fun i ↦ (Subtype.val '' (C i).1, (C i).2)) := by
      refine ⟨?_, fun x hx y _ hnf ↦ ?_⟩
      · rintro i x _ ⟨x', hx', rfl⟩ y _ hy
        exact hC.1 i x' trivial hx' y trivial hy
      · obtain ⟨w, ⟨hxw, hyw⟩, huniq⟩ := hC.2 ⟨x, hx.2⟩ trivial y trivial hnf
        refine ⟨w, ⟨⟨⟨x, hx.2⟩, hxw, rfl⟩, hyw⟩, ?_⟩
        rintro w' ⟨⟨x', hx', hval⟩, hy'⟩
        have hxeq : x' = ⟨x, hx.2⟩ := Subtype.ext hval
        exact huniq w' ⟨hxeq ▸ hx', hy'⟩
    exact hcov.partitionCoverNumber_le.trans_eq (by simp)
  · refine Nondeterministic.le_partitionCoverNumber_iff.mpr fun r C hC ↦ ?_
    have hcov : Nondeterministic.IsPartitionCover true (fun x y b ↦ f x y = b)
        (Set.univ ∩ send ⁻¹' {true}) (Set.univ ∩ (fun _ : Y ↦ ()) ⁻¹' {()})
        (fun i ↦ (Subtype.val '' (C i).1, (C i).2)) := by
      refine ⟨?_, fun x hx y _ hnf ↦ ?_⟩
      · rintro i x _ ⟨x', hx', rfl⟩ y _ hy
        exact hC.1 i x' trivial hx' y trivial hy
      · obtain ⟨w, ⟨hxw, hyw⟩, huniq⟩ := hC.2 ⟨x, hx.2⟩ trivial y trivial hnf
        refine ⟨w, ⟨⟨⟨x, hx.2⟩, hxw, rfl⟩, hyw⟩, ?_⟩
        rintro w' ⟨⟨x', hx', hval⟩, hy'⟩
        have hxeq : x' = ⟨x, hx.2⟩ := Subtype.ext hval
        exact huniq w' ⟨hxeq ▸ hx', hy'⟩
    exact hcov.partitionCoverNumber_le.trans_eq (by simp)

private theorem partitionCoverNumberFun_le_add_bobSplit {X Y : Type*} (f : X → Y → Bool)
    (send : Y → Bool) :
    Nondeterministic.partitionCoverNumberFun true f Set.univ Set.univ ≤
      Nondeterministic.partitionCoverNumberFun true
          (fun x (y : {y : Y // send y = false}) ↦ f x y.val) Set.univ Set.univ +
        Nondeterministic.partitionCoverNumberFun true
          (fun x (y : {y : Y // send y = true}) ↦ f x y.val) Set.univ Set.univ := by
  have hfib := Nondeterministic.partitionCoverNumber_le_sum_fibers
    (z := true) (R := fun x y b ↦ f x y = b) (A := Set.univ) (B := Set.univ)
    (fun _ : X ↦ ()) send
  refine hfib.trans ?_
  rw [Fintype.sum_unique, Fintype.sum_bool, add_comm]
  refine add_le_add ?_ ?_
  · refine Nondeterministic.le_partitionCoverNumber_iff.mpr fun r C hC ↦ ?_
    have hcov : Nondeterministic.IsPartitionCover true (fun x y b ↦ f x y = b)
        (Set.univ ∩ (fun _ : X ↦ ()) ⁻¹' {()}) (Set.univ ∩ send ⁻¹' {false})
        (fun i ↦ ((C i).1, Subtype.val '' (C i).2)) := by
      refine ⟨?_, fun x _ y hy hnf ↦ ?_⟩
      · rintro i x _ hx y _ ⟨y', hy', rfl⟩
        exact hC.1 i x trivial hx y' trivial hy'
      · obtain ⟨w, ⟨hxw, hyw⟩, huniq⟩ := hC.2 x trivial ⟨y, hy.2⟩ trivial hnf
        refine ⟨w, ⟨hxw, ⟨⟨y, hy.2⟩, hyw, rfl⟩⟩, ?_⟩
        rintro w' ⟨hx', ⟨y', hy', hval⟩⟩
        have hyeq : y' = ⟨y, hy.2⟩ := Subtype.ext hval
        exact huniq w' ⟨hx', hyeq ▸ hy'⟩
    exact hcov.partitionCoverNumber_le.trans_eq (by simp)
  · refine Nondeterministic.le_partitionCoverNumber_iff.mpr fun r C hC ↦ ?_
    have hcov : Nondeterministic.IsPartitionCover true (fun x y b ↦ f x y = b)
        (Set.univ ∩ (fun _ : X ↦ ()) ⁻¹' {()}) (Set.univ ∩ send ⁻¹' {true})
        (fun i ↦ ((C i).1, Subtype.val '' (C i).2)) := by
      refine ⟨?_, fun x _ y hy hnf ↦ ?_⟩
      · rintro i x _ hx y _ ⟨y', hy', rfl⟩
        exact hC.1 i x trivial hx y' trivial hy'
      · obtain ⟨w, ⟨hxw, hyw⟩, huniq⟩ := hC.2 x trivial ⟨y, hy.2⟩ trivial hnf
        refine ⟨w, ⟨hxw, ⟨⟨y, hy.2⟩, hyw, rfl⟩⟩, ?_⟩
        rintro w' ⟨hx', ⟨y', hy', hval⟩⟩
        have hyeq : y' = ⟨y, hy.2⟩ := Subtype.ext hval
        exact huniq w' ⟨hx', hyeq ▸ hy'⟩
    exact hcov.partitionCoverNumber_le.trans_eq (by simp)

private noncomputable def liftAliceBranch {X Y : Type*} {P : X → Prop}
    (q : Protocol {x : X // P x} Y Bool) : Protocol X Y Bool := by
  classical
  exact if hne : Nonempty {x : X // P x} then
    q.comap (fun x ↦ if hx : P x then ⟨x, hx⟩ else hne.some) id
  else
    .output false

private theorem run_liftAliceBranch {X Y : Type*} {P : X → Prop}
    (q : Protocol {x : X // P x} Y Bool) {x : X} (hx : P x) (y : Y) :
    (liftAliceBranch q).run x y = q.run ⟨x, hx⟩ y := by
  have hne : Nonempty {x : X // P x} := ⟨⟨x, hx⟩⟩
  simp [liftAliceBranch, hne, hx]

private theorem depth_liftAliceBranch_le {X Y : Type*} {P : X → Prop}
    (q : Protocol {x : X // P x} Y Bool) :
    (liftAliceBranch q).depth ≤ q.depth := by
  classical
  by_cases hne : Nonempty {x : X // P x} <;> simp [liftAliceBranch, hne]

private noncomputable def liftBobBranch {X Y : Type*} {P : Y → Prop}
    (q : Protocol X {y : Y // P y} Bool) : Protocol X Y Bool := by
  classical
  exact if hne : Nonempty {y : Y // P y} then
    q.comap id (fun y ↦ if hy : P y then ⟨y, hy⟩ else hne.some)
  else
    .output false

private theorem run_liftBobBranch {X Y : Type*} {P : Y → Prop}
    (q : Protocol X {y : Y // P y} Bool) (x : X) {y : Y} (hy : P y) :
    (liftBobBranch q).run x y = q.run x ⟨y, hy⟩ := by
  have hne : Nonempty {y : Y // P y} := ⟨⟨y, hy⟩⟩
  simp [liftBobBranch, hne, hy]

private theorem depth_liftBobBranch_le {X Y : Type*} {P : Y → Prop}
    (q : Protocol X {y : Y // P y} Bool) :
    (liftBobBranch q).depth ≤ q.depth := by
  classical
  by_cases hne : Nonempty {y : Y // P y} <;> simp [liftBobBranch, hne]

private theorem optimal_alice_step {X Y : Type*} {f : X → Y → Bool} {send : X → Bool}
    {p₀ p₁ : Protocol X Y Bool} {s : ℕ}
    (hp : (Protocol.alice send p₀ p₁).run = f)
    (hopt : Protocol.ecomplexityFun f = (s : ℕ∞))
    (hs : (Protocol.alice send p₀ p₁).depth = s) :
    ∃ d₀ d₁ : ℕ,
      Protocol.ecomplexityFun (fun (x : {x : X // send x = false}) y ↦ f x.val y) = d₀ ∧
      Protocol.ecomplexityFun (fun (x : {x : X // send x = true}) y ↦ f x.val y) = d₁ ∧
      s = 1 + max d₀ d₁ := by
  let f₀ : {x : X // send x = false} → Y → Bool := fun x y ↦ f x.val y
  let f₁ : {x : X // send x = true} → Y → Bool := fun x y ↦ f x.val y
  have hp₀ : (p₀.comap Subtype.val id).run = f₀ := by
    funext ⟨x, hx⟩ y
    simpa [Protocol.run_alice, hx, f₀] using congrFun₂ hp x y
  have hp₁ : (p₁.comap Subtype.val id).run = f₁ := by
    funext ⟨x, hx⟩ y
    simpa [Protocol.run_alice, hx, f₁] using congrFun₂ hp x y
  have hle₀ : Protocol.ecomplexityFun f₀ ≤ p₀.depth := by
    simpa using Protocol.ecomplexityFun_le_depth hp₀
  have hle₁ : Protocol.ecomplexityFun f₁ ≤ p₁.depth := by
    simpa using Protocol.ecomplexityFun_le_depth hp₁
  obtain ⟨d₀, hd₀⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle₀)
  obtain ⟨d₁, hd₁⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle₁)
  obtain ⟨q₀, hq₀, hqd₀⟩ := Protocol.ecomplexityFun_le_iff.mp hd₀.symm.le
  obtain ⟨q₁, hq₁, hqd₁⟩ := Protocol.ecomplexityFun_le_iff.mp hd₁.symm.le
  refine ⟨d₀, d₁, hd₀.symm, hd₁.symm, le_antisymm ?_ ?_⟩
  · let q : Protocol X Y Bool := .alice send (liftAliceBranch q₀) (liftAliceBranch q₁)
    have hqrun : q.run = f := by
      funext x y
      cases hx : send x
      · simpa [q, hx, run_liftAliceBranch q₀ hx] using congrFun₂ hq₀ ⟨x, hx⟩ y
      · simpa [q, hx, run_liftAliceBranch q₁ hx] using congrFun₂ hq₁ ⟨x, hx⟩ y
    have hqdepth : q.depth ≤ 1 + max d₀ d₁ := by
      have h0 := (depth_liftAliceBranch_le q₀).trans hqd₀
      have h1 := (depth_liftAliceBranch_le q₁).trans hqd₁
      simp only [q, Protocol.depth_alice]; omega
    have hs_le : (s : ℕ∞) ≤ q.depth := hopt ▸ Protocol.ecomplexityFun_le_depth hqrun
    exact (ENat.natCast_le_natCast.mp hs_le).trans hqdepth
  · have hd₀_le : d₀ ≤ p₀.depth := by exact_mod_cast hd₀ ▸ hle₀
    have hd₁_le : d₁ ≤ p₁.depth := by exact_mod_cast hd₁ ▸ hle₁
    simp only [Protocol.depth_alice] at hs; omega

private theorem optimal_bob_step {X Y : Type*} {f : X → Y → Bool} {send : Y → Bool}
    {p₀ p₁ : Protocol X Y Bool} {s : ℕ}
    (hp : (Protocol.bob send p₀ p₁).run = f)
    (hopt : Protocol.ecomplexityFun f = (s : ℕ∞))
    (hs : (Protocol.bob send p₀ p₁).depth = s) :
    ∃ d₀ d₁ : ℕ,
      Protocol.ecomplexityFun (fun x (y : {y : Y // send y = false}) ↦ f x y.val) = d₀ ∧
      Protocol.ecomplexityFun (fun x (y : {y : Y // send y = true}) ↦ f x y.val) = d₁ ∧
      s = 1 + max d₀ d₁ := by
  let f₀ : X → {y : Y // send y = false} → Bool := fun x y ↦ f x y.val
  let f₁ : X → {y : Y // send y = true} → Bool := fun x y ↦ f x y.val
  have hp₀ : (p₀.comap id Subtype.val).run = f₀ := by
    funext x ⟨y, hy⟩
    simpa [Protocol.run_bob, hy, f₀] using congrFun₂ hp x y
  have hp₁ : (p₁.comap id Subtype.val).run = f₁ := by
    funext x ⟨y, hy⟩
    simpa [Protocol.run_bob, hy, f₁] using congrFun₂ hp x y
  have hle₀ : Protocol.ecomplexityFun f₀ ≤ p₀.depth := by
    simpa using Protocol.ecomplexityFun_le_depth hp₀
  have hle₁ : Protocol.ecomplexityFun f₁ ≤ p₁.depth := by
    simpa using Protocol.ecomplexityFun_le_depth hp₁
  obtain ⟨d₀, hd₀⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle₀)
  obtain ⟨d₁, hd₁⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle₁)
  obtain ⟨q₀, hq₀, hqd₀⟩ := Protocol.ecomplexityFun_le_iff.mp hd₀.symm.le
  obtain ⟨q₁, hq₁, hqd₁⟩ := Protocol.ecomplexityFun_le_iff.mp hd₁.symm.le
  refine ⟨d₀, d₁, hd₀.symm, hd₁.symm, le_antisymm ?_ ?_⟩
  · let q : Protocol X Y Bool := .bob send (liftBobBranch q₀) (liftBobBranch q₁)
    have hqrun : q.run = f := by
      funext x y
      cases hy : send y
      · simpa [q, hy, run_liftBobBranch q₀ x hy] using congrFun₂ hq₀ x ⟨y, hy⟩
      · simpa [q, hy, run_liftBobBranch q₁ x hy] using congrFun₂ hq₁ x ⟨y, hy⟩
    have hqdepth : q.depth ≤ 1 + max d₀ d₁ := by
      have h0 := (depth_liftBobBranch_le q₀).trans hqd₀
      have h1 := (depth_liftBobBranch_le q₁).trans hqd₁
      simp only [q, Protocol.depth_bob]; omega
    have hs_le : (s : ℕ∞) ≤ q.depth := hopt ▸ Protocol.ecomplexityFun_le_depth hqrun
    exact (ENat.natCast_le_natCast.mp hs_le).trans hqdepth
  · have hd₀_le : d₀ ≤ p₀.depth := by exact_mod_cast hd₀ ▸ hle₀
    have hd₁_le : d₁ ≤ p₁.depth := by exact_mod_cast hd₁ ▸ hle₁
    simp only [Protocol.depth_bob] at hs; omega

private theorem one_add_clog_add_le (a b : ℕ) :
    1 + Nat.clog 2 (a + b) ≤ 2 + max (Nat.clog 2 a) (Nat.clog 2 b) := by
  let m := max (Nat.clog 2 a) (Nat.clog 2 b)
  have ha : a ≤ 2 ^ m :=
    (Nat.le_pow_clog Nat.one_lt_two a).trans (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  have hb : b ≤ 2 ^ m :=
    (Nat.le_pow_clog Nat.one_lt_two b).trans (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
  have hab : a + b ≤ 2 ^ (m + 1) := by rw [Nat.pow_succ]; omega
  have hclog : Nat.clog 2 (a + b) ≤ m + 1 := Nat.clog_le_of_le_pow hab
  omega

private theorem clog_add_one_le_of_cc_eq.{u, v} :
    ∀ (s : ℕ) {X : Type u} {Y : Type v} (f : X → Y → Bool),
      IsNonConstantBoolFun f → Protocol.ecomplexityFun f = (s : ℕ∞) →
      ∃ r : ℕ, Nondeterministic.partitionCoverNumberFun true f Set.univ Set.univ = r ∧
        Nat.clog 2 r + 1 ≤ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro X Y f hf hcc
    have hs1 : 1 ≤ s := by
      have h1 := one_le_ecomplexityFun_of_nonConstant hf
      rw [hcc] at h1
      exact_mod_cast h1
    have hnetop : Protocol.ecomplexity (fun x y z ↦ f x y = z) Set.univ Set.univ ≠ ⊤ := by
      change Protocol.ecomplexityFun f ≠ ⊤
      rw [hcc]; exact ENat.natCast_ne_top s
    obtain ⟨p, hp_solves, hp_depth⟩ :=
      Protocol.exists_solves_depth_eq_ecomplexity (Protocol.ecomplexity_ne_top_iff.mp hnetop)
    have hp : p.run = f := Protocol.solves_univ_iff.mp hp_solves
    have hpd : p.depth = s := by
      have : (p.depth : ℕ∞) = (s : ℕ∞) := hp_depth.trans hcc
      exact_mod_cast this
    rcases eq_or_lt_of_le hs1 with rfl | hs_gt
    · exact ⟨1, partitionCoverNumberFun_eq_one_of_depth_eq_one hf p hp hpd, by simp⟩
    · cases p with
      | output _ => simp at hpd; omega
      | alice send p₀ p₁ =>
        let f₀ : {x : X // send x = false} → Y → Bool := fun x y ↦ f x.val y
        let f₁ : {x : X // send x = true} → Y → Bool := fun x y ↦ f x.val y
        obtain ⟨d₀, d₁, hd₀, hd₁, hs_eq⟩ := optimal_alice_step hp hcc hpd
        have hbound : ∀ {A : Type u} (g : A → Y → Bool) (d : ℕ),
            Protocol.ecomplexityFun g = d → d < s →
            ∃ r : ℕ, Nondeterministic.partitionCoverNumberFun true g Set.univ Set.univ = r ∧
              Nat.clog 2 r + 2 ≤ s := by
          intro A g d hgd hdlt
          by_cases hg : IsNonConstantBoolFun g
          · obtain ⟨r, hr, hle⟩ := ih d hdlt g hg hgd
            exact ⟨r, hr, by omega⟩
          · have hrle := partitionCoverNumberFun_le_one_of_not_nonConstant hg
            obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by simp) hrle)
            have hr1 : r ≤ 1 := by exact_mod_cast hr ▸ hrle
            have hclog0 : Nat.clog 2 r = 0 := Nat.clog_of_right_le_one hr1 2
            exact ⟨r, hr.symm, by omega⟩
        obtain ⟨r₀, hr₀, hb₀⟩ := hbound f₀ d₀ hd₀ (by omega)
        obtain ⟨r₁, hr₁, hb₁⟩ := hbound f₁ d₁ hd₁ (by omega)
        have hsub : Nondeterministic.partitionCoverNumberFun true f Set.univ Set.univ ≤
            ((r₀ + r₁ : ℕ) : ℕ∞) := by
          simpa [f₀, f₁, hr₀, hr₁] using partitionCoverNumberFun_le_add_aliceSplit f send
        obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp
          (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hsub)
        have hrr : r ≤ r₀ + r₁ := by exact_mod_cast hr ▸ hsub
        have hclog_le : Nat.clog 2 r ≤ Nat.clog 2 (r₀ + r₁) := Nat.clog_mono_right 2 hrr
        have hcalc := one_add_clog_add_le r₀ r₁
        exact ⟨r, hr.symm, by omega⟩
      | bob send p₀ p₁ =>
        let f₀ : X → {y : Y // send y = false} → Bool := fun x y ↦ f x y.val
        let f₁ : X → {y : Y // send y = true} → Bool := fun x y ↦ f x y.val
        obtain ⟨d₀, d₁, hd₀, hd₁, hs_eq⟩ := optimal_bob_step hp hcc hpd
        have hbound : ∀ {B : Type v} (g : X → B → Bool) (d : ℕ),
            Protocol.ecomplexityFun g = d → d < s →
            ∃ r : ℕ, Nondeterministic.partitionCoverNumberFun true g Set.univ Set.univ = r ∧
              Nat.clog 2 r + 2 ≤ s := by
          intro B g d hgd hdlt
          by_cases hg : IsNonConstantBoolFun g
          · obtain ⟨r, hr, hle⟩ := ih d hdlt g hg hgd
            exact ⟨r, hr, by omega⟩
          · have hrle := partitionCoverNumberFun_le_one_of_not_nonConstant hg
            obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by simp) hrle)
            have hr1 : r ≤ 1 := by exact_mod_cast hr ▸ hrle
            have hclog0 : Nat.clog 2 r = 0 := Nat.clog_of_right_le_one hr1 2
            exact ⟨r, hr.symm, by omega⟩
        obtain ⟨r₀, hr₀, hb₀⟩ := hbound f₀ d₀ hd₀ (by omega)
        obtain ⟨r₁, hr₁, hb₁⟩ := hbound f₁ d₁ hd₁ (by omega)
        have hsub : Nondeterministic.partitionCoverNumberFun true f Set.univ Set.univ ≤
            ((r₀ + r₁ : ℕ) : ℕ∞) := by
          simpa [f₀, f₁, hr₀, hr₁] using partitionCoverNumberFun_le_add_bobSplit f send
        obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp
          (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hsub)
        have hrr : r ≤ r₀ + r₁ := by exact_mod_cast hr ▸ hsub
        have hclog_le : Nat.clog 2 r ≤ Nat.clog 2 (r₀ + r₁) := Nat.clog_mono_right 2 hrr
        have hcalc := one_add_clog_add_le r₀ r₁
        exact ⟨r, hr.symm, by omega⟩

/-- **Strengthened partition-cover lower bound:** for every non-constant Boolean function
`f : X → Y → Bool`, `⌈log₂ χ₁(f)⌉ + 1 ≤ ecomplexityFun f`. -/
public theorem clog_partitionCoverNumberFun_add_one_le_ecomplexityFun {X Y : Type*}
    {f : X → Y → Bool} (hf : IsNonConstantBoolFun f) {r : ℕ}
    (hr : Nondeterministic.partitionCoverNumberFun true f Set.univ Set.univ = r) :
    ((Nat.clog 2 r + 1 : ℕ) : ℕ∞) ≤ Protocol.ecomplexityFun f := by
  by_cases htop : Protocol.ecomplexityFun f = ⊤
  · simp [htop]
  · obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp htop
    obtain ⟨r', hr', hle⟩ := clog_add_one_le_of_cc_eq s f hf hs.symm
    have hreq : r = r' := by
      have : (r : ℕ∞) = (r' : ℕ∞) := hr.symm.trans hr'
      exact_mod_cast this
    rw [← hs, hreq]
    exact_mod_cast hle

/-! ### Direct-sum additivity of `partitionCoverNumberFun` -/

/-- Direct-sum additivity of `1`-partition cover numbers:
`χ₁(directSumBool f₁ f₂) = χ₁(f₁) + χ₁(f₂)`. -/
public theorem partitionCoverNumberFun_directSumBool {X₁ Y₁ X₂ Y₂ : Type*}
    (f₁ : X₁ → Y₁ → Bool) (f₂ : X₂ → Y₂ → Bool) :
    Nondeterministic.partitionCoverNumberFun true (directSumBool f₁ f₂) Set.univ Set.univ =
      Nondeterministic.partitionCoverNumberFun true f₁ Set.univ Set.univ +
        Nondeterministic.partitionCoverNumberFun true f₂ Set.univ Set.univ := by
  apply le_antisymm
  · by_cases htop :
        Nondeterministic.partitionCoverNumberFun true f₁ Set.univ Set.univ = ⊤ ∨
          Nondeterministic.partitionCoverNumberFun true f₂ Set.univ Set.univ = ⊤
    · rcases htop with h | h <;> simp [h]
    · push Not at htop
      obtain ⟨r₁, hr₁⟩ := ENat.ne_top_iff_exists.mp htop.1
      obtain ⟨r₂, hr₂⟩ := ENat.ne_top_iff_exists.mp htop.2
      obtain ⟨C₁, hC₁⟩ :=
        Nondeterministic.partitionCoverNumber_le_iff.mp (hr₁.ge)
      obtain ⟨C₂, hC₂⟩ :=
        Nondeterministic.partitionCoverNumber_le_iff.mp (hr₂.ge)
      rw [← hr₁, ← hr₂, ← Nat.cast_add, Nondeterministic.partitionCoverNumberFun,
        Nondeterministic.partitionCoverNumber_le_iff]
      let C : Fin r₁ ⊕ Fin r₂ → Set (X₁ ⊕ X₂) × Set (Y₁ ⊕ Y₂)
        | .inl i => (Sum.inl '' (C₁ i).1, Sum.inl '' (C₁ i).2)
        | .inr j => (Sum.inr '' (C₂ j).1, Sum.inr '' (C₂ j).2)
      refine ⟨C ∘ (finSumFinEquiv (m := r₁) (n := r₂)).symm, fun w x _ hx y _ hy ↦ ?_,
        fun x _ y _ hnf ↦ ?_⟩
      · rcases h : finSumFinEquiv.symm w with i | j <;>
          simp only [Function.comp_apply, h, C] at hx hy
        · obtain ⟨x₁, hx₁, rfl⟩ := hx; obtain ⟨y₁, hy₁, rfl⟩ := hy
          exact hC₁.1 i x₁ trivial hx₁ y₁ trivial hy₁
        · obtain ⟨x₂, hx₂, rfl⟩ := hx; obtain ⟨y₂, hy₂, rfl⟩ := hy
          exact hC₂.1 j x₂ trivial hx₂ y₂ trivial hy₂
      · cases x with
        | inl x₁ =>
          cases y with
          | inl y₁ =>
            obtain ⟨i, ⟨hx, hy⟩, huniq⟩ :=
              hC₁.2 x₁ trivial y₁ trivial (by simpa [directSumBool] using hnf)
            refine ⟨finSumFinEquiv (.inl i), by simp [C, hx, hy], fun w' ⟨hx', hy'⟩ ↦ ?_⟩
            apply finSumFinEquiv.symm.injective
            rcases h' : finSumFinEquiv.symm w' with i' | j' <;>
              simp only [Function.comp_apply, h', C, Equiv.symm_apply_apply] at hx' hy' ⊢
            · obtain ⟨_, hx1, hxeq⟩ := hx'; obtain ⟨_, hy1, hyeq⟩ := hy'
              cases hxeq; cases hyeq
              exact congrArg Sum.inl (huniq i' ⟨hx1, hy1⟩)
            · obtain ⟨_, _, h⟩ := hx'; cases h
          | inr y₂ => exact absurd rfl hnf
        | inr x₂ =>
          cases y with
          | inl y₁ => exact absurd rfl hnf
          | inr y₂ =>
            obtain ⟨j, ⟨hx, hy⟩, huniq⟩ :=
              hC₂.2 x₂ trivial y₂ trivial (by simpa [directSumBool] using hnf)
            refine ⟨finSumFinEquiv (.inr j), by simp [C, hx, hy], fun w' ⟨hx', hy'⟩ ↦ ?_⟩
            apply finSumFinEquiv.symm.injective
            rcases h' : finSumFinEquiv.symm w' with i' | j' <;>
              simp only [Function.comp_apply, h', C, Equiv.symm_apply_apply] at hx' hy' ⊢
            · obtain ⟨_, _, h⟩ := hx'; cases h
            · obtain ⟨_, hx2, hxeq⟩ := hx'; obtain ⟨_, hy2, hyeq⟩ := hy'
              cases hxeq; cases hyeq
              exact congrArg Sum.inr (huniq j' ⟨hx2, hy2⟩)
  · refine Nondeterministic.le_partitionCoverNumber_iff.mpr fun r C hC ↦ ?_
    classical
    let touches₁ (w : Fin r) : Prop := ∃ x₁ y₁, Sum.inl x₁ ∈ (C w).1 ∧ Sum.inl y₁ ∈ (C w).2
    have hnot_both : ∀ w : Fin r, touches₁ w →
        ∀ x₂ y₂, ¬(Sum.inr x₂ ∈ (C w).1 ∧ Sum.inr y₂ ∈ (C w).2) := by
      rintro w ⟨x₁, _, hx₁, _⟩ x₂ y₂ ⟨_, hy₂⟩
      have h0 := hC.1 w (.inl x₁) trivial hx₁ (.inr y₂) trivial hy₂
      simp [directSumBool] at h0
    let κ₁ := {w : Fin r // touches₁ w}
    let κ₂ := {w : Fin r // ¬touches₁ w}
    have hcov₁ : Nondeterministic.IsPartitionCover true (fun x y b ↦ f₁ x y = b) Set.univ Set.univ
        (fun u : κ₁ ↦ ({x₁ | Sum.inl x₁ ∈ (C u.val).1}, {y₁ | Sum.inl y₁ ∈ (C u.val).2})) := by
      refine ⟨fun u x₁ _ hx₁ y₁ _ hy₁ ↦ ?_, fun x₁ _ y₁ _ hnf ↦ ?_⟩
      · simpa [directSumBool] using hC.1 u.val (.inl x₁) trivial hx₁ (.inl y₁) trivial hy₁
      · obtain ⟨w, ⟨hx, hy⟩, huniq⟩ := hC.2 (.inl x₁) trivial (.inl y₁) trivial
          (by simpa [directSumBool] using hnf)
        refine ⟨⟨w, ⟨x₁, y₁, hx, hy⟩⟩, ⟨hx, hy⟩, fun ⟨w', _⟩ ⟨hx', hy'⟩ ↦ ?_⟩
        exact Subtype.ext (huniq w' ⟨hx', hy'⟩)
    have hcov₂ : Nondeterministic.IsPartitionCover true (fun x y b ↦ f₂ x y = b) Set.univ Set.univ
        (fun v : κ₂ ↦ ({x₂ | Sum.inr x₂ ∈ (C v.val).1}, {y₂ | Sum.inr y₂ ∈ (C v.val).2})) := by
      refine ⟨fun v x₂ _ hx₂ y₂ _ hy₂ ↦ ?_, fun x₂ _ y₂ _ hnf ↦ ?_⟩
      · simpa [directSumBool] using hC.1 v.val (.inr x₂) trivial hx₂ (.inr y₂) trivial hy₂
      · obtain ⟨w, ⟨hx, hy⟩, huniq⟩ := hC.2 (.inr x₂) trivial (.inr y₂) trivial
          (by simpa [directSumBool] using hnf)
        have hnt : ¬touches₁ w := fun ht ↦ hnot_both w ht x₂ y₂ ⟨hx, hy⟩
        refine ⟨⟨w, hnt⟩, ⟨hx, hy⟩, fun ⟨w', _⟩ ⟨hx', hy'⟩ ↦ ?_⟩
        exact Subtype.ext (huniq w' ⟨hx', hy'⟩)
    have hsum : Fintype.card κ₁ + Fintype.card κ₂ = r := by
      have hc := Fintype.card_subtype_compl touches₁
      have hle : Fintype.card κ₁ ≤ r := (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin r)
      simp only [Fintype.card_fin] at hc
      dsimp only [κ₁, κ₂] at hle ⊢
      rw [hc]; omega
    calc Nondeterministic.partitionCoverNumberFun true f₁ Set.univ Set.univ +
          Nondeterministic.partitionCoverNumberFun true f₂ Set.univ Set.univ
        ≤ Fintype.card κ₁ + Fintype.card κ₂ :=
          add_le_add hcov₁.partitionCoverNumber_le hcov₂.partitionCoverNumber_le
      _ = r := by exact_mod_cast hsum

/-! ### Pruning unreachable branches in finite-domain binary protocols -/

private theorem exists_pruned_on_rect {rows cols : ℕ}
    (p : Protocol (Fin rows) (Fin cols) Bool)
    (A : Finset (Fin rows)) (B : Finset (Fin cols))
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ q : Protocol (Fin rows) (Fin cols) Bool,
      (∀ i ∈ A, ∀ j ∈ B, q.run i j = p.run i j) ∧
      q.depth ≤ p.depth ∧
      q.leafCount ≤ A.card * B.card := by
  induction p generalizing A B with
  | output z =>
    exact ⟨.output z, fun _ _ _ _ ↦ rfl, le_rfl, Nat.mul_pos hA.card_pos hB.card_pos⟩
  | alice send p₀ p₁ ih₀ ih₁ =>
    let A₀ := A.filter fun i ↦ send i = false
    let A₁ := A.filter fun i ↦ send i = true
    have hcard_sum : A₀.card + A₁.card = A.card := by
      have hu : A₀ ∪ A₁ = A := by
        ext i; simp only [A₀, A₁, Finset.mem_union, Finset.mem_filter]; cases send i <;> simp
      have hd : Disjoint A₀ A₁ := Finset.disjoint_left.mpr fun i h0 h1 ↦
        Bool.noConfusion (((Finset.mem_filter.mp h0).2).symm.trans (Finset.mem_filter.mp h1).2)
      rw [← Finset.card_union_of_disjoint hd, hu]
    by_cases h0 : A₀.Nonempty
    · by_cases h1 : A₁.Nonempty
      · obtain ⟨q₀, hr₀, hd₀, hl₀⟩ := ih₀ A₀ B h0 hB
        obtain ⟨q₁, hr₁, hd₁, hl₁⟩ := ih₁ A₁ B h1 hB
        refine ⟨.alice send q₀ q₁, fun i hi j hj ↦ ?_, by simp; omega, ?_⟩
        · simp only [Protocol.run_alice]
          cases hs : send i
          · exact hr₀ i (Finset.mem_filter.mpr ⟨hi, hs⟩) j hj
          · exact hr₁ i (Finset.mem_filter.mpr ⟨hi, hs⟩) j hj
        · simp only [Protocol.leafCount_alice]
          calc q₀.leafCount + q₁.leafCount
              ≤ A₀.card * B.card + A₁.card * B.card := Nat.add_le_add hl₀ hl₁
            _ = A.card * B.card := by rw [← Nat.add_mul, hcard_sum]
      · obtain ⟨q₀, hr₀, hd₀, hl₀⟩ := ih₀ A₀ B h0 hB
        refine ⟨q₀, fun i hi j hj ↦ ?_, hd₀.trans (by simp; omega),
          hl₀.trans (Nat.mul_le_mul_right _ (by omega))⟩
        have hs : send i = false := by
          cases hsi : send i
          · rfl
          · exact absurd ⟨i, Finset.mem_filter.mpr ⟨hi, hsi⟩⟩ h1
        simpa [Protocol.run_alice, hs] using hr₀ i (Finset.mem_filter.mpr ⟨hi, hs⟩) j hj
    · have h1 : A₁.Nonempty := by
        obtain ⟨i₀, hi₀⟩ := hA
        cases hsi : send i₀
        · exact absurd ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, hsi⟩⟩ h0
        · exact ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, hsi⟩⟩
      obtain ⟨q₁, hr₁, hd₁, hl₁⟩ := ih₁ A₁ B h1 hB
      refine ⟨q₁, fun i hi j hj ↦ ?_, hd₁.trans (by simp; omega),
        hl₁.trans (Nat.mul_le_mul_right _ (by omega))⟩
      have hs : send i = true := by
        cases hsi : send i
        · exact absurd ⟨i, Finset.mem_filter.mpr ⟨hi, hsi⟩⟩ h0
        · rfl
      simpa [Protocol.run_alice, hs] using hr₁ i (Finset.mem_filter.mpr ⟨hi, hs⟩) j hj
  | bob send p₀ p₁ ih₀ ih₁ =>
    let B₀ := B.filter fun j ↦ send j = false
    let B₁ := B.filter fun j ↦ send j = true
    have hcard_sum : B₀.card + B₁.card = B.card := by
      have hu : B₀ ∪ B₁ = B := by
        ext j; simp only [B₀, B₁, Finset.mem_union, Finset.mem_filter]; cases send j <;> simp
      have hd : Disjoint B₀ B₁ := Finset.disjoint_left.mpr fun j h0 h1 ↦
        Bool.noConfusion (((Finset.mem_filter.mp h0).2).symm.trans (Finset.mem_filter.mp h1).2)
      rw [← Finset.card_union_of_disjoint hd, hu]
    by_cases h0 : B₀.Nonempty
    · by_cases h1 : B₁.Nonempty
      · obtain ⟨q₀, hr₀, hd₀, hl₀⟩ := ih₀ A B₀ hA h0
        obtain ⟨q₁, hr₁, hd₁, hl₁⟩ := ih₁ A B₁ hA h1
        refine ⟨.bob send q₀ q₁, fun i hi j hj ↦ ?_, by simp; omega, ?_⟩
        · simp only [Protocol.run_bob]
          cases hs : send j
          · exact hr₀ i hi j (Finset.mem_filter.mpr ⟨hj, hs⟩)
          · exact hr₁ i hi j (Finset.mem_filter.mpr ⟨hj, hs⟩)
        · simp only [Protocol.leafCount_bob]
          calc q₀.leafCount + q₁.leafCount
              ≤ A.card * B₀.card + A.card * B₁.card := Nat.add_le_add hl₀ hl₁
            _ = A.card * B.card := by rw [← Nat.mul_add, hcard_sum]
      · obtain ⟨q₀, hr₀, hd₀, hl₀⟩ := ih₀ A B₀ hA h0
        refine ⟨q₀, fun i hi j hj ↦ ?_, hd₀.trans (by simp; omega),
          hl₀.trans (Nat.mul_le_mul_left _ (by omega))⟩
        have hs : send j = false := by
          cases hsj : send j
          · rfl
          · exact absurd ⟨j, Finset.mem_filter.mpr ⟨hj, hsj⟩⟩ h1
        simpa [Protocol.run_bob, hs] using hr₀ i hi j (Finset.mem_filter.mpr ⟨hj, hs⟩)
    · have h1 : B₁.Nonempty := by
        obtain ⟨j₀, hj₀⟩ := hB
        cases hsj : send j₀
        · exact absurd ⟨j₀, Finset.mem_filter.mpr ⟨hj₀, hsj⟩⟩ h0
        · exact ⟨j₀, Finset.mem_filter.mpr ⟨hj₀, hsj⟩⟩
      obtain ⟨q₁, hr₁, hd₁, hl₁⟩ := ih₁ A B₁ hA h1
      refine ⟨q₁, fun i hi j hj ↦ ?_, hd₁.trans (by simp; omega),
        hl₁.trans (Nat.mul_le_mul_left _ (by omega))⟩
      have hs : send j = true := by
        cases hsj : send j
        · exact absurd ⟨j, Finset.mem_filter.mpr ⟨hj, hsj⟩⟩ h0
        · rfl
      simpa [Protocol.run_bob, hs] using hr₁ i hi j (Finset.mem_filter.mpr ⟨hj, hs⟩)

/-- Every deterministic binary protocol on non-empty `Fin rows × Fin cols` can be pruned to at most
`rows * cols` leaves without increasing depth. -/
public theorem exists_pruned_protocol {rows cols : ℕ} (hr : 0 < rows) (hc : 0 < cols)
    (p : Protocol (Fin rows) (Fin cols) Bool) :
    ∃ q : Protocol (Fin rows) (Fin cols) Bool,
      q.run = p.run ∧ q.depth ≤ p.depth ∧ q.leafCount ≤ rows * cols := by
  have hA : (Finset.univ : Finset (Fin rows)).Nonempty := ⟨⟨0, hr⟩, Finset.mem_univ _⟩
  have hB : (Finset.univ : Finset (Fin cols)).Nonempty := ⟨⟨0, hc⟩, Finset.mem_univ _⟩
  obtain ⟨q, hrun, hd, hl⟩ := exists_pruned_on_rect p Finset.univ Finset.univ hA hB
  refine ⟨q, funext fun i ↦ funext fun j ↦ hrun i (Finset.mem_univ _) j (Finset.mem_univ _),
    hd, ?_⟩
  simpa using hl

end CslibFrontier.Computability.Communication
