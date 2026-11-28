module

public import CslibFrontier.Computability.Circuit.Boolean.Unbounded
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson
public import CslibFrontier.Foundations.Data.BitString.Parity

import CslibFrontier.Computability.Circuit.Boolean.AC0
import CslibFrontier.Computability.Circuit.Boolean.Hastad
import CslibFrontier.Computability.Circuit.Boolean.Hastad.Sharp
import CslibFrontier.Computability.Circuit.CompositionDepth
import CslibFrontier.Computability.Circuit.Pi
import CslibFrontier.Computability.DecisionTree.Parity
import CslibFrontier.Foundations.Data.BitString.PartialAssignment
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


/-!
# Average-Case Håstad Parity Bound and AC⁰ Nisan–Wigderson Reconstruction

This module establishes:

1. **Average-case Håstad parity bound** (`abs_parity_agree_sub_half_le`): any unbounded fan-in
   circuit `C` of AND/OR depth at most `e + 1` on `n` bits with `s ≥ 2` and
   `s (16 s + 1)^e ≤ n / 17` agrees with `parity n` on a fraction of inputs within
   `C.size / 2^(s + 1)` of `1 / 2`.
2. **Nisan–Wigderson reconstruction for unbounded fan-in circuits** (`nw_unbounded_advantage_le`):
   lifting next-bit prediction reconstruction to `Circuit Unbounded.signature` with free negations
   (`andOrCost`).

## Main results

* `CslibFrontier.Computability.Circuit.Boolean.Hastad.abs_parity_agree_sub_half_le`:
  average-case Håstad correlation bound for parity.
* `CslibFrontier.Computability.Circuit.Boolean.Hastad.exists_unbounded_circuit_of_dependsOn`:
  small depth-2 DNF unbounded fan-in circuit for any Boolean function depending on a subset `S`.
* `CslibFrontier.Computability.Circuit.Boolean.Hastad.nw_unbounded_advantage_le`:
  two-sided Nisan–Wigderson distinguishing advantage bound for unbounded fan-in circuits.
-/

public section

namespace CslibFrontier.Computability.Circuit.Boolean.Hastad

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Unbounded
open Cslib.Crypto.PRG Cslib.Crypto.PRG.NisanWigderson Cslib.DecisionTree Cslib.Probability.PMF
open Finset

/-! ### Part 1: Average-Case Håstad Parity Bound -/

/-- Any decision tree of depth strictly less than `#(ρ.free ∩ σ.free)` agrees with
`parity n (ρ.fill y)` on exactly half of the inputs `y` agreeing with `σ`. -/
private theorem two_mul_card_agree_parity_of_decisionTree {n : ℕ}
    (ρ σ : PartialAssignment (Fin n)) (t : DecisionTree (Fin n) Bool)
    (ht : t.depth < #(ρ.free ∩ σ.free)) :
    2 * #{y : BitString n | σ.Agrees y ∧ t.eval y = parity n (ρ.fill y)} =
      #{y : BitString n | σ.Agrees y} := by
  induction t generalizing σ with
  | leaf b =>
    have hne : (ρ.free ∩ σ.free).Nonempty := Finset.card_pos.mp (by simpa using ht)
    obtain ⟨i, hi⟩ := hne
    rw [Finset.mem_inter, PartialAssignment.mem_free, PartialAssignment.mem_free] at hi
    obtain ⟨hρi, hσi⟩ := hi
    let flip (y : BitString n) : BitString n := Function.update y i (!y i)
    have hflip_inv (y : BitString n) : flip (flip y) = y := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [flip]
      · simp [flip, hj]
    have hflip_agrees (y : BitString n) : σ.Agrees (flip y) ↔ σ.Agrees y := by
      constructor <;> intro h j c hjc
      · have hji : j ≠ i := fun heq => by subst heq; rw [hσi] at hjc; cases hjc
        simpa [flip, hji] using h j c hjc
      · have hji : j ≠ i := fun heq => by subst heq; rw [hσi] at hjc; cases hjc
        simpa [flip, hji] using h j c hjc
    have hflip_par (y : BitString n) :
        parity n (ρ.fill (flip y)) = !parity n (ρ.fill y) := by
      have hfill : ρ.fill (flip y) = Function.update (ρ.fill y) i (!(ρ.fill y i)) := by
        dsimp only [flip]
        rw [PartialAssignment.fill_update_of_eq_none hρi, PartialAssignment.fill_of_eq_none hρi]
      rw [hfill, parity, parityOn_update_not (Finset.mem_univ i)]
    have hbij :
        #{y : BitString n | σ.Agrees y ∧ b = parity n (ρ.fill y)} =
        #{y : BitString n | σ.Agrees y ∧ b ≠ parity n (ρ.fill y)} := by
      refine Finset.card_bij (fun y _ => flip y) (fun y hy => ?_)
        (fun y₁ _ y₂ _ h => by have := congrArg flip h; simpa [hflip_inv] using this)
        (fun y hy => ⟨flip y, ?_, hflip_inv y⟩)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        refine ⟨(hflip_agrees y).mpr hy.1, ?_⟩
        rw [hflip_par, ← hy.2]
        cases b <;> decide
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        refine ⟨(hflip_agrees y).mpr hy.1, ?_⟩
        rw [hflip_par]
        cases b <;> cases hpy : parity n (ρ.fill y) <;> simp_all
    have hpart :
        #{y : BitString n | σ.Agrees y ∧ b = parity n (ρ.fill y)} +
        #{y : BitString n | σ.Agrees y ∧ b ≠ parity n (ρ.fill y)} =
        #{y : BitString n | σ.Agrees y} := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext y
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      · rw [Finset.disjoint_left]
        intro y hy1 hy2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy2
        exact hy2.2 hy1.2
    simp only [DecisionTree.eval_leaf]
    rw [← hpart, ← hbij, two_mul]
    rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [DecisionTree.depth_node] at ht
    cases hσ : σ i with
    | some c =>
      cases c
      · have heq :
            (Finset.univ.filter fun y : BitString n =>
              σ.Agrees y ∧ (DecisionTree.node i t₀ t₁).eval y = parity n (ρ.fill y)) =
            (Finset.univ.filter fun y : BitString n =>
              σ.Agrees y ∧ t₀.eval y = parity n (ρ.fill y)) := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor <;> rintro ⟨hy, he⟩ <;> refine ⟨hy, ?_⟩
          · have hyi : y i = false := hy i false hσ
            simpa [DecisionTree.eval_node, hyi] using he
          · have hyi : y i = false := hy i false hσ
            simpa [DecisionTree.eval_node, hyi] using he
        rw [heq]
        exact ih₀ σ (by omega)
      · have heq :
            (Finset.univ.filter fun y : BitString n =>
              σ.Agrees y ∧ (DecisionTree.node i t₀ t₁).eval y = parity n (ρ.fill y)) =
            (Finset.univ.filter fun y : BitString n =>
              σ.Agrees y ∧ t₁.eval y = parity n (ρ.fill y)) := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor <;> rintro ⟨hy, he⟩ <;> refine ⟨hy, ?_⟩
          · have hyi : y i = true := hy i true hσ
            simpa [DecisionTree.eval_node, hyi] using he
          · have hyi : y i = true := hy i true hσ
            simpa [DecisionTree.eval_node, hyi] using he
        rw [heq]
        exact ih₁ σ (by omega)
    | none =>
      let upd (b : Bool) : PartialAssignment (Fin n) := Function.update σ i (some b)
      let σ₀ : PartialAssignment (Fin n) := upd false
      let σ₁ : PartialAssignment (Fin n) := upd true
      have hfree_eq (b : Bool) :
          ρ.free ∩ (upd b).free = (ρ.free ∩ σ.free).erase i := by
        ext j
        simp only [Finset.mem_inter, Finset.mem_erase, PartialAssignment.mem_free, upd,
          Function.update_apply]
        by_cases hji : j = i
        · subst hji; simp
        · simp [hji]
      have hcard_ge (b : Bool) : #(ρ.free ∩ σ.free) - 1 ≤
          #(ρ.free ∩ (upd b).free) := by
        rw [hfree_eq]
        exact Finset.pred_card_le_card_erase
      have h0 := ih₀ σ₀ (by have := hcard_ge false; dsimp [σ₀]; omega)
      have h1 := ih₁ σ₁ (by have := hcard_ge true; dsimp [σ₁]; omega)
      have hag_iff (y : BitString n) (b : Bool) :
          (upd b).Agrees y ↔ σ.Agrees y ∧ y i = b := by
        constructor
        · intro h
          refine ⟨fun j c hjc => ?_, h i b (by simp [upd])⟩
          have hji : j ≠ i := fun heq => by subst heq; rw [hσ] at hjc; cases hjc
          exact h j c (by simp [upd, hji, hjc])
        · rintro ⟨h, hyi⟩ j c hjc
          by_cases hji : j = i
          · subst hji
            simp only [upd, Function.update_self, Option.some.injEq] at hjc
            rw [hyi, hjc]
          · simp only [upd, Function.update_of_ne hji] at hjc
            exact h j c hjc
      have hsplit_tot :
          #{y : BitString n | σ.Agrees y} =
          #{y : BitString n | σ₀.Agrees y} + #{y : BitString n | σ₁.Agrees y} := by
        have h := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ.filter fun y : BitString n => σ.Agrees y)) (fun y => y i = false)
        have hf0 : (Finset.univ.filter fun y : BitString n => σ.Agrees y).filter
            (fun y => y i = false) = Finset.univ.filter fun y : BitString n => σ₀.Agrees y := by
          ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, σ₀, hag_iff]
        have hf1 : (Finset.univ.filter fun y : BitString n => σ.Agrees y).filter
            (fun y => ¬ y i = false) = Finset.univ.filter fun y : BitString n => σ₁.Agrees y := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, σ₁, hag_iff, Bool.not_eq_false]
        rw [hf0, hf1] at h
        omega
      have hsplit_ag :
          #{y : BitString n | σ.Agrees y ∧
            (DecisionTree.node i t₀ t₁).eval y = parity n (ρ.fill y)} =
          #{y : BitString n | σ₀.Agrees y ∧ t₀.eval y = parity n (ρ.fill y)} +
          #{y : BitString n | σ₁.Agrees y ∧ t₁.eval y = parity n (ρ.fill y)} := by
        have h := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ.filter fun y : BitString n =>
            σ.Agrees y ∧ (DecisionTree.node i t₀ t₁).eval y = parity n (ρ.fill y)))
          (fun y => y i = false)
        have hf0 : (Finset.univ.filter fun y : BitString n =>
            σ.Agrees y ∧ (DecisionTree.node i t₀ t₁).eval y = parity n (ρ.fill y)).filter
            (fun y => y i = false) =
            Finset.univ.filter fun y : BitString n =>
              σ₀.Agrees y ∧ t₀.eval y = parity n (ρ.fill y) := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, σ₀, hag_iff]
          constructor
          · rintro ⟨⟨hy, he⟩, hyi⟩
            exact ⟨⟨hy, hyi⟩, by simpa [DecisionTree.eval_node, hyi] using he⟩
          · rintro ⟨⟨hy, hyi⟩, he⟩
            exact ⟨⟨hy, by simpa [DecisionTree.eval_node, hyi] using he⟩, hyi⟩
        have hf1 : (Finset.univ.filter fun y : BitString n =>
            σ.Agrees y ∧ (DecisionTree.node i t₀ t₁).eval y = parity n (ρ.fill y)).filter
            (fun y => ¬ y i = false) =
            Finset.univ.filter fun y : BitString n =>
              σ₁.Agrees y ∧ t₁.eval y = parity n (ρ.fill y) := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, σ₁, hag_iff, Bool.not_eq_false]
          constructor
          · rintro ⟨⟨hy, he⟩, hyi⟩
            exact ⟨⟨hy, hyi⟩, by simpa [DecisionTree.eval_node, hyi] using he⟩
          · rintro ⟨⟨hy, hyi⟩, he⟩
            exact ⟨⟨hy, by simpa [DecisionTree.eval_node, hyi] using he⟩, hyi⟩
        rw [hf0, hf1] at h
        omega
      omega

/-- Double-counting lemma: for every `ℓ` and every `f : BitString n → ℝ`, drawing
`(ρ, y) ∈ withFree (Fin n) ℓ × BitString n` produces a uniform marginal `ρ.fill y`. -/
private theorem sum_withFree_fill {n ℓ : ℕ} (f : BitString n → ℝ) :
    ∑ ρ ∈ PartialAssignment.withFree (Fin n) ℓ, ∑ y : BitString n, f (ρ.fill y) =
      (#(PartialAssignment.withFree (Fin n) ℓ) : ℝ) * ∑ x : BitString n, f x := by
  let W := PartialAssignment.withFree (Fin n) ℓ
  have hfib (x : BitString n) :
      #{p ∈ W ×ˢ (Finset.univ : Finset (BitString n)) | p.1.fill p.2 = x} = #W := by
    refine Finset.card_bij
      (fun p _ => fun i : Fin n => if (p.1 i).isNone then none else some (p.2 i))
      (fun p hp => ?_) (fun p₁ hp₁ p₂ hp₂ h => ?_) (fun ρ' hρ' => ?_)
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, W,
        PartialAssignment.mem_withFree] at hp ⊢
      have hfr : (PartialAssignment.free fun i : Fin n =>
          if (p.1 i).isNone then none else some (p.2 i)) = p.1.free := by
        ext i
        cases hpi : p.1 i <;> simp [hpi]
      rw [hfr, hp.1]
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp₁ hp₂
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · have hi := congrFun h i
        cases h1 : p₁.1 i <;> cases h2 : p₂.1 i <;> simp_all
        · have hx1 : p₁.1.fill p₁.2 i = x i := congrFun hp₁.2 i
          have hx2 : p₂.1.fill p₂.2 i = x i := congrFun hp₂.2 i
          simpa [h1, h2] using hx1.trans hx2.symm
      · have hi := congrFun h i
        cases h1 : p₁.1 i <;> cases h2 : p₂.1 i <;> simp_all
        · have hx1 : p₁.1.fill p₁.2 i = x i := congrFun hp₁.2 i
          have hx2 : p₂.1.fill p₂.2 i = x i := congrFun hp₂.2 i
          simpa [h1, h2] using hx1.trans hx2.symm
    · let ρ : PartialAssignment (Fin n) := fun i => if (ρ' i).isNone then none else some (x i)
      let y : BitString n := fun i => match ρ' i with | none => x i | some b => b
      refine ⟨(ρ, y), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, W,
          PartialAssignment.mem_withFree] at hρ' ⊢
        refine ⟨?_, funext fun i => ?_⟩
        · have hfr : ρ.free = ρ'.free := by ext i; cases hi : ρ' i <;> simp [ρ, hi]
          rw [hfr, hρ']
        · cases hi : ρ' i <;> simp [ρ, y, hi]
      · funext i
        cases hi : ρ' i <;> simp [ρ, y, hi]
  calc ∑ ρ ∈ W, ∑ y : BitString n, f (ρ.fill y)
      = ∑ p ∈ W ×ˢ (Finset.univ : Finset (BitString n)), f (p.1.fill p.2) :=
        (Finset.sum_product W Finset.univ (fun p => f (p.1.fill p.2))).symm
    _ = ∑ x : BitString n, ∑ p ∈ W ×ˢ (Finset.univ : Finset (BitString n))
          with p.1.fill p.2 = x, f (p.1.fill p.2) :=
        (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _).symm
    _ = ∑ x : BitString n, (#W : ℝ) * f x := Finset.sum_congr rfl fun x _ => by
        have hcon : ∑ p ∈ W ×ˢ (Finset.univ : Finset (BitString n)) with p.1.fill p.2 = x,
            f (p.1.fill p.2) =
            ∑ p ∈ W ×ˢ (Finset.univ : Finset (BitString n)) with p.1.fill p.2 = x, f x :=
          Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]
        rw [hcon, Finset.sum_const, nsmul_eq_mul, hfib x]
    _ = (#W : ℝ) * ∑ x : BitString n, f x := (Finset.mul_sum _ _ _).symm

/-- **Average-case Håstad parity bound:** any unbounded fan-in circuit `C` of AND/OR depth at most
`e + 1` on `n` bits with `s ≥ 2` and `s * (16 * s + 1) ^ e ≤ n / 17` agrees with `parity n` on a
fraction of inputs within `C.size / 2 ^ (s + 1)` of `1 / 2`. -/
theorem abs_parity_agree_sub_half_le {n s e : ℕ} (C : Circuit Unbounded.signature n 1)
    (hs : 2 ≤ s) (hd : C.depthWith Unbounded.andOrCost ≤ e + 1)
    (hn : s * (16 * s + 1) ^ e ≤ n / 17) :
    |(#{x : BitString n | C.eval Unbounded.interpretation x 0 = parity n x} : ℝ) / (2 : ℝ) ^ n -
      1 / 2| ≤ (C.size : ℝ) / (2 : ℝ) ^ (s + 1) := by
  set ℓ := n / 17 / (16 * s + 1) ^ e
  set W := PartialAssignment.withFree (Fin n) ℓ
  set Bad := {ρ ∈ W | ∃ k, C.program.depthsWith andOrCost k ≤ e + 1 ∧
    ¬ Shallow s ρ fun x => C.program.eval Unbounded.interpretation x k}
  have hsℓ : s ≤ ℓ := (Nat.le_div_iff_mul_le (by positivity)).mpr hn
  have hℓn : ℓ ≤ n := (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)
  have hW_pos : 0 < #W := by
    rw [PartialAssignment.card_withFree, Fintype.card_fin]
    exact Nat.mul_pos (Nat.choose_pos hℓn) (by positivity)
  have hbad_bound : 2 ^ s * #Bad ≤ C.size * #W := by
    have h1 := two_pow_mul_card_filter_exists_not_shallow_le_depthWith (p := C.program)
      hs hn e le_rfl
    have h2 : #{k | (C.program.lines k).op ≠ .not ∧ C.program.depthsWith andOrCost k ≤ e + 1} ≤
        C.size := (Finset.card_filter_le _ _).trans_eq (by simp)
    exact h1.trans (Nat.mul_le_mul_right _ h2)
  let f (x : BitString n) : ℝ :=
    if C.eval Unbounded.interpretation x 0 = parity n x then 1 else -1
  have hcard_bs : Fintype.card (BitString n) = 2 ^ n := by
    simp [BitString]
  have hsum_good (ρ : PartialAssignment (Fin n)) (hρW : ρ ∈ W) (hρGood : ρ ∉ Bad) :
      ∑ y : BitString n, f (ρ.fill y) = 0 := by
    have hsh_out : Shallow s ρ fun x => C.eval Unbounded.interpretation x 0 := by
      have hout : (fun x => C.eval Unbounded.interpretation x 0) =
          fun x => C.program.trace Unbounded.interpretation x (C.outputs 0) := rfl
      rw [hout]
      refine shallow_trace_of_forall_ne_not hs (fun k _ hk => ?_) (C.outputs 0)
        ((C.wireDepthsWith_outputs_le_depthWith andOrCost 0).trans hd)
      by_contra hdeep
      exact hρGood (Finset.mem_filter.mpr ⟨hρW, k, hk, hdeep⟩)
    obtain ⟨t, ht_eval, ht_depth⟩ := hsh_out.exists_tree
    have hfree_eq : #(ρ.free ∩ PartialAssignment.empty.free) = ℓ := by
      rw [PartialAssignment.free_empty, Finset.inter_univ, PartialAssignment.mem_withFree.mp hρW]
    have htwo := two_mul_card_agree_parity_of_decisionTree ρ PartialAssignment.empty t
      (by omega)
    have hcard_ag : 2 * #{y : BitString n |
        C.eval Unbounded.interpretation (ρ.fill y) 0 = parity n (ρ.fill y)} = 2 ^ n := by
      have h1 : (Finset.univ.filter fun y : BitString n =>
          PartialAssignment.empty.Agrees y ∧ t.eval y = parity n (ρ.fill y)) =
          Finset.univ.filter fun y : BitString n =>
            C.eval Unbounded.interpretation (ρ.fill y) 0 = parity n (ρ.fill y) := by
        ext y; simp [ht_eval]
      have h2 : (Finset.univ.filter fun y : BitString n => PartialAssignment.empty.Agrees y) =
          Finset.univ := by ext y; simp
      rw [h1, h2, Finset.card_univ, hcard_bs] at htwo
      exact htwo
    have hsum_eq : ∑ y : BitString n, f (ρ.fill y) =
        2 * (#{y : BitString n |
          C.eval Unbounded.interpretation (ρ.fill y) 0 = parity n (ρ.fill y)} : ℝ) -
        (2 : ℝ) ^ n := by
      calc ∑ y : BitString n, f (ρ.fill y)
          = ∑ y : BitString n,
              ((if C.eval Unbounded.interpretation (ρ.fill y) 0 = parity n (ρ.fill y)
                then (2 : ℝ) else 0) - 1) :=
            Finset.sum_congr rfl fun y _ => by dsimp [f]; split_ifs <;> norm_num
        _ = (∑ y : BitString n,
              if C.eval Unbounded.interpretation (ρ.fill y) 0 = parity n (ρ.fill y)
              then (2 : ℝ) else 0) - (2 : ℝ) ^ n := by
            rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hcard_bs,
              nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
        _ = 2 * (#{y : BitString n |
              C.eval Unbounded.interpretation (ρ.fill y) 0 = parity n (ρ.fill y)} : ℝ) -
            (2 : ℝ) ^ n := by
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [hsum_eq]
    have hcard_r : 2 * (#{y : BitString n |
        C.eval Unbounded.interpretation (ρ.fill y) 0 = parity n (ρ.fill y)} : ℝ) =
        (2 : ℝ) ^ n := by exact_mod_cast hcard_ag
    linarith
  have hsum_abs_le : |∑ ρ ∈ W, ∑ y : BitString n, f (ρ.fill y)| ≤ (#Bad : ℝ) * (2 : ℝ) ^ n := by
    have hsplit : ∑ ρ ∈ W, ∑ y : BitString n, f (ρ.fill y) =
        ∑ ρ ∈ Bad, ∑ y : BitString n, f (ρ.fill y) := by
      have hsub : Bad ⊆ W := Finset.filter_subset _ W
      rw [← Finset.sum_subset hsub]
      intro ρ hρW hρNotBad
      exact hsum_good ρ hρW hρNotBad
    rw [hsplit]
    calc |∑ ρ ∈ Bad, ∑ y : BitString n, f (ρ.fill y)|
        ≤ ∑ ρ ∈ Bad, |∑ y : BitString n, f (ρ.fill y)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ρ ∈ Bad, (2 : ℝ) ^ n := Finset.sum_le_sum fun ρ _ => by
          calc |∑ y : BitString n, f (ρ.fill y)|
              ≤ ∑ y : BitString n, |f (ρ.fill y)| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ _y : BitString n, (1 : ℝ) := Finset.sum_congr rfl fun y _ => by
                dsimp [f]; split_ifs <;> norm_num
            _ = (2 : ℝ) ^ n := by
                rw [Finset.sum_const, Finset.card_univ, hcard_bs, nsmul_eq_mul, mul_one,
                  Nat.cast_pow, Nat.cast_ofNat]
      _ = (#Bad : ℝ) * (2 : ℝ) ^ n := by simp [nsmul_eq_mul]
  have hdouble := sum_withFree_fill (ℓ := ℓ) f
  have hsum_f : ∑ x : BitString n, f x =
      2 * (#{x : BitString n | C.eval Unbounded.interpretation x 0 = parity n x} : ℝ) -
      (2 : ℝ) ^ n := by
    calc ∑ x : BitString n, f x
        = ∑ x : BitString n,
            ((if C.eval Unbounded.interpretation x 0 = parity n x then (2 : ℝ) else 0) - 1) :=
          Finset.sum_congr rfl fun x _ => by dsimp [f]; split_ifs <;> norm_num
      _ = (∑ x : BitString n,
            if C.eval Unbounded.interpretation x 0 = parity n x then (2 : ℝ) else 0) -
          (2 : ℝ) ^ n := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hcard_bs,
            nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
      _ = 2 * (#{x : BitString n | C.eval Unbounded.interpretation x 0 = parity n x} : ℝ) -
          (2 : ℝ) ^ n := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hW_pos_r : (0 : ℝ) < (#W : ℝ) := by exact_mod_cast hW_pos
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hbad_r : (2 : ℝ) ^ s * (#Bad : ℝ) ≤ (C.size : ℝ) * (#W : ℝ) := by exact_mod_cast hbad_bound
  have h1 : (#W : ℝ) * |∑ x : BitString n, f x| ≤ (#Bad : ℝ) * (2 : ℝ) ^ n := by
    rw [← abs_of_pos hW_pos_r, ← abs_mul, ← hdouble]
    exact hsum_abs_le
  have h2 : |∑ x : BitString n, f x| / (2 : ℝ) ^ n ≤ (C.size : ℝ) / (2 : ℝ) ^ s := by
    rw [div_le_div_iff₀ h2n_pos (by positivity)]
    have hmul := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ (2 : ℝ) ^ s by positivity)
    have hmul2 := mul_le_mul_of_nonneg_right hbad_r h2n_pos.le
    have hcancel : (#W : ℝ) * (|∑ x : BitString n, f x| * (2 : ℝ) ^ s) ≤
        (#W : ℝ) * ((C.size : ℝ) * (2 : ℝ) ^ n) := by linarith
    exact le_of_mul_le_mul_left hcancel hW_pos_r
  have heq_diff :
      |(#{x : BitString n | C.eval Unbounded.interpretation x 0 = parity n x} : ℝ) / (2 : ℝ) ^ n -
        1 / 2| = (|∑ x : BitString n, f x| / (2 : ℝ) ^ n) / 2 := by
    rw [hsum_f]
    have hinner :
        (#{x : BitString n | C.eval Unbounded.interpretation x 0 = parity n x} : ℝ) / (2 : ℝ) ^ n -
          1 / 2 =
        (2 * (#{x : BitString n | C.eval Unbounded.interpretation x 0 = parity n x} : ℝ) -
          (2 : ℝ) ^ n) / (2 : ℝ) ^ n / 2 := by
      field_simp
    rw [hinner, abs_div, abs_div, abs_of_pos h2n_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [heq_diff, pow_succ, ← div_div]
  exact div_le_div_of_nonneg_right h2 (by norm_num)

/-! ### Part 2: NW Reconstruction for Unbounded Fan-In Circuits -/

/-- Any Boolean function `g : BitString q → Bool` depending only on a subset `S ⊆ Fin q` has an
unbounded fan-in DNF circuit of AND/OR depth at most `2` and size at most
`2^|S| * (|S| + 1) + 1`. -/
private theorem exists_unbounded_circuit_of_dependsOn {q : ℕ} (g : BitString q → Bool)
    (S : Finset (Fin q)) (hg : DependsOn g S) :
    ∃ C : Circuit Unbounded.signature q 1,
      C.Computes Unbounded.interpretation (single g) ∧
      C.depthWith Unbounded.andOrCost ≤ 2 ∧
      C.size ≤ 2 ^ #S * (#S + 1) + 1 := by
  classical
  let eS : Fin #S ≃ {i : Fin q // i ∈ S} := S.equivFin.symm
  let ext (v : {i : Fin q // i ∈ S} → Bool) : BitString q :=
    fun i => if hi : i ∈ S then v ⟨i, hi⟩ else false
  let T : Finset ({i : Fin q // i ∈ S} → Bool) :=
    Finset.univ.filter fun v => g (ext v) = true
  let eT : Fin #T ≃ {v : {i : Fin q // i ∈ S} → Bool // v ∈ T} := T.equivFin.symm
  let lit (i : Fin q) (b : Bool) : Circuit Unbounded.signature q 1 :=
    if b then Circuit.wiring Unbounded.signature (fun _ => i)
    else Circuit.oneGate (σ := Unbounded.signature) .not (fun _ => i)
  have hlit_eval (i : Fin q) (b : Bool) (x : BitString q) :
      (lit i b).eval Unbounded.interpretation x 0 = decide (x i = b) := by
    cases b <;> simp [lit]
  have hlit_dw (i : Fin q) (b : Bool) : (lit i b).depthWith andOrCost = 0 := by
    cases b
    · simp [lit]
    · simp [lit, Circuit.depthWith_wiring]
  have hlit_sz (i : Fin q) (b : Bool) : (lit i b).size ≤ 1 := by
    cases b <;> simp [lit]
  let term (v : {i : Fin q // i ∈ S} → Bool) : Circuit Unbounded.signature q 1 :=
    (Circuit.oneGate (σ := Unbounded.signature) (.and #S) id).comp
      (Circuit.pi fun idx : Fin #S => lit (eS idx).1 (v (eS idx)))
  have hterm_eval (v : {i : Fin q // i ∈ S} → Bool) (x : BitString q) :
      (term v).eval Unbounded.interpretation x 0 =
        decide (∀ i : {i : Fin q // i ∈ S}, x i.1 = v i) := by
    simp only [term, Circuit.eval_comp, Circuit.eval_pi, Circuit.eval_oneGate,
      interpretation_and, id_eq, hlit_eval, decide_eq_true_eq]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    exact Equiv.forall_congr eS fun _ => Iff.rfl
  have hterm_dw (v : {i : Fin q // i ∈ S} → Bool) : (term v).depthWith andOrCost ≤ 1 := by
    refine (Circuit.depthWith_comp_le (σ := Unbounded.signature) andOrCost _ _).trans ?_
    have hpi := Circuit.depthWith_pi_le (σ := Unbounded.signature) andOrCost
      (fun idx : Fin #S => lit (eS idx).1 (v (eS idx))) (fun idx => (hlit_dw _ _).le)
    simp only [Circuit.depthWith_oneGate, andOrCost_and]
    omega
  have hterm_sz (v : {i : Fin q // i ∈ S} → Bool) : (term v).size ≤ #S + 1 := by
    simp only [term, Circuit.size_comp, Circuit.size_pi, Circuit.size_oneGate]
    calc (∑ idx : Fin #S, (lit (eS idx).1 (v (eS idx))).size) + 1
        ≤ (∑ _idx : Fin #S, 1) + 1 :=
          Nat.add_le_add_right (Finset.sum_le_sum fun _ _ => hlit_sz _ _) 1
      _ = #S + 1 := by simp
  let C : Circuit Unbounded.signature q 1 :=
    (Circuit.oneGate (σ := Unbounded.signature) (.or #T) id).comp
      (Circuit.pi fun idx : Fin #T => term (eT idx).1)
  refine ⟨C, fun x => funext fun j => ?_, ?_, ?_⟩
  · fin_cases j
    simp only [C, Circuit.eval_comp, Circuit.eval_pi, Circuit.eval_oneGate,
      interpretation_or, id_eq, hterm_eval, decide_eq_true_eq, single_apply]
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    constructor
    · rintro ⟨idx, hidx⟩
      have hmem : (eT idx).1 ∈ T := (eT idx).2
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      have hgx : g x = g (ext (eT idx).1) := hg fun i hi => by
        simp only [ext, Finset.mem_coe.mp hi, ↓reduceDIte]
        exact hidx ⟨i, hi⟩
      rw [hgx, hmem]
    · intro hgx
      let v : {i : Fin q // i ∈ S} → Bool := fun i => x i.1
      have hv_mem : v ∈ T := by
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        have heq : g (ext v) = g x := hg fun i hi => by
          simp [ext, v, Finset.mem_coe.mp hi]
        rw [heq, hgx]
      refine ⟨eT.symm ⟨v, hv_mem⟩, fun i => ?_⟩
      simp [v]
  · refine (Circuit.depthWith_comp_le (σ := Unbounded.signature) andOrCost _ _).trans ?_
    have hpi := Circuit.depthWith_pi_le (σ := Unbounded.signature) andOrCost
      (fun idx : Fin #T => term (eT idx).1) (fun idx => hterm_dw _)
    simp only [Circuit.depthWith_oneGate, andOrCost_or]
    omega
  · simp only [C, Circuit.size_comp, Circuit.size_pi, Circuit.size_oneGate]
    have hT_le : #T ≤ 2 ^ #S := by
      calc #T ≤ Fintype.card ({i : Fin q // i ∈ S} → Bool) := Finset.card_le_univ T
        _ = 2 ^ #S := by simp
    calc (∑ idx : Fin #T, (term (eT idx).1).size) + 1
        ≤ (∑ _idx : Fin #T, (#S + 1)) + 1 :=
          Nat.add_le_add_right (Finset.sum_le_sum fun _ _ => hterm_sz _) 1
      _ = #T * (#S + 1) + 1 := by simp
      _ ≤ 2 ^ #S * (#S + 1) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_right _ hT_le) 1

/-- One-sided Nisan–Wigderson distinguishing bound for unbounded fan-in circuits. -/
private theorem nw_unbounded_one_sided_le {L q a M s d : ℕ} (D : Design L q a M) (hM : 0 < M)
    (G : Circuit Unbounded.signature M 1) (hs : 2 ≤ s)
    (hd : G.depthWith Unbounded.andOrCost ≤ d)
    (hq : s * (16 * s + 1) ^ (d + 1) ≤ q / 17) :
    ((generator D (parity q)).realExperiment
      (fun y => _root_.PMF.pure (G.eval Unbounded.interpretation y 0)) true).toReal -
    (Generator.idealExperiment
      (fun y => _root_.PMF.pure (G.eval Unbounded.interpretation y 0)) true).toReal ≤
      (M : ℝ) * ((G.size + M * (2 ^ a * (a + 1) + 1) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (s + 1) := by
  let test : BitString M → Bool := fun y => G.eval Unbounded.interpretation y 0
  set ε : ℝ :=
    ((generator D (parity q)).realExperiment (fun y => _root_.PMF.pure (test y)) true).toReal -
    (Generator.idealExperiment (fun y => _root_.PMF.pure (test y)) true).toReal
  by_cases hε : ε ≤ 0
  · exact hε.trans (by positivity)
  obtain ⟨i, S, bit, r, u, hS_card, hbit_dep, hagree⟩ :=
    exists_dependsOn_half_add_div_le_card_nextBitGuess_eq D (parity q) test hM le_rfl
  -- Build a circuit `Q j` for each input wire `j : Fin M` of `G`.
  have hQ_ex (j : Fin M) : ∃ Q : Circuit Unbounded.signature q 1,
      (∀ x, Q.eval Unbounded.interpretation x 0 =
        if h : (j : ℕ) < i then bit ⟨j, h⟩ x else if j = i then r else u j) ∧
      Q.depthWith Unbounded.andOrCost ≤ 2 ∧
      Q.size ≤ 2 ^ a * (a + 1) + 1 := by
    by_cases hji : (j : ℕ) < i
    · obtain ⟨Q, hQcomp, hQdw, hQsz⟩ :=
        exists_unbounded_circuit_of_dependsOn (bit ⟨j, hji⟩) (S ⟨j, hji⟩) (hbit_dep ⟨j, hji⟩)
      refine ⟨Q, fun x => by
        simp only [hji, ↓reduceDIte]
        exact congrFun (hQcomp x) 0, hQdw, hQsz.trans ?_⟩
      have hsc := hS_card ⟨j, hji⟩
      have h1 : 2 ^ #(S ⟨j, hji⟩) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hsc
      have h2 : #(S ⟨j, hji⟩) + 1 ≤ a + 1 := by omega
      exact Nat.add_le_add_right (Nat.mul_le_mul h1 h2) 1
    · refine ⟨constCircuit (.id _) (if j = i then r else u j),
        fun x => by simp [hji], ?_, ?_⟩
      · cases (if j = i then r else u j) <;> simp [constCircuit]
      · simp
  choose Q hQ_eval hQ_dw hQ_sz using hQ_ex
  let base : Circuit Unbounded.signature q 1 := G.comp (Circuit.pi Q)
  let H : Circuit Unbounded.signature q 1 := if r then base else notCircuit (.id _) base
  have hH_eval (x : BitString q) :
      H.eval Unbounded.interpretation x 0 =
        nextBitGuess test i r u (fun j => bit j x) := by
    have hbase : base.eval Unbounded.interpretation x 0 =
        test (fun j => if h : (j : ℕ) < i then bit ⟨j, h⟩ x else if j = i then r else u j) := by
      simp only [base, Circuit.eval_comp, Circuit.eval_pi, hQ_eval, test]
    cases r
    · simp only [H, Bool.false_eq_true, ↓reduceIte, eval_notCircuit, hbase, nextBitGuess]
      cases test _ <;> rfl
    · simp only [H, ↓reduceIte, hbase, nextBitGuess]
      cases test _ <;> rfl
  have hH_dw : H.depthWith Unbounded.andOrCost ≤ d + 2 := by
    have hbase_dw : base.depthWith Unbounded.andOrCost ≤ d + 2 := by
      refine (Circuit.depthWith_comp_le (σ := Unbounded.signature) andOrCost G (Circuit.pi Q)).trans
        ?_
      have hpi := Circuit.depthWith_pi_le (σ := Unbounded.signature) andOrCost Q hQ_dw
      omega
    cases r
    · simp only [H, Bool.false_eq_true, ↓reduceIte, notCircuit]
      refine (Circuit.depthWith_comp_le (σ := Unbounded.signature) andOrCost _ _).trans ?_
      simp only [Fin.isValue, Circuit.mapOp_id, Circuit.depthWith_oneGate, andOrCost_not, zero_add]
      exact hbase_dw
    · exact hbase_dw
  have hH_sz : H.size ≤ G.size + M * (2 ^ a * (a + 1) + 1) + 1 := by
    have hbase_sz : base.size ≤ G.size + M * (2 ^ a * (a + 1) + 1) := by
      simp only [base, Circuit.size_comp, Circuit.size_pi]
      have hsum : ∑ j : Fin M, (Q j).size ≤ M * (2 ^ a * (a + 1) + 1) := by
        calc ∑ j : Fin M, (Q j).size
            ≤ ∑ _j : Fin M, (2 ^ a * (a + 1) + 1) := Finset.sum_le_sum fun j _ => hQ_sz j
          _ = M * (2 ^ a * (a + 1) + 1) := by simp
      omega
    cases r <;> simp only [H, Bool.false_eq_true, ↓reduceIte, size_notCircuit] <;> omega
  have hhast := abs_parity_agree_sub_half_le H hs hH_dw hq
  have heq_set :
      #{x : BitString q | H.eval Unbounded.interpretation x 0 = parity q x} =
      #{x : BitString q | nextBitGuess test i r u (fun j => bit j x) = parity q x} := by
    congr 1; ext x; simp [hH_eval]
  rw [heq_set] at hhast
  have hdiff : ε / (M : ℝ) ≤ (H.size : ℝ) / (2 : ℝ) ^ (s + 1) := by
    have h1 := (abs_le.mp hhast).2
    linarith
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have h2 : ε ≤ (M : ℝ) * ((H.size : ℝ) / (2 : ℝ) ^ (s + 1)) := by
    rwa [div_le_iff₀ hM_pos, mul_comm] at hdiff
  calc ε ≤ (M : ℝ) * ((H.size : ℝ) / (2 : ℝ) ^ (s + 1)) := h2
    _ = (M : ℝ) * (H.size : ℝ) / (2 : ℝ) ^ (s + 1) := by ring
    _ ≤ (M : ℝ) * ((G.size + M * (2 ^ a * (a + 1) + 1) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (s + 1) := by
        gcongr

/-- Two-sided Nisan–Wigderson distinguishing bound for unbounded fan-in circuits. -/
theorem nw_unbounded_advantage_le {L q a M s d : ℕ} (D : Design L q a M) (hM : 0 < M)
    (G : Circuit Unbounded.signature M 1) (hs : 2 ≤ s)
    (hd : G.depthWith Unbounded.andOrCost ≤ d)
    (hq : s * (16 * s + 1) ^ (d + 1) ≤ q / 17) :
    |((generator D (parity q)).realExperiment
        (fun y => _root_.PMF.pure (G.eval Unbounded.interpretation y 0)) true).toReal -
      (Generator.idealExperiment
        (fun y => _root_.PMF.pure (G.eval Unbounded.interpretation y 0)) true).toReal| ≤
      (M : ℝ) * ((G.size + M * (2 ^ a * (a + 1) + 1) + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (s + 1) := by
  rw [abs_le]
  constructor
  · -- Apply one-sided bound to `notCircuit (.id _) G`.
    let G' : Circuit Unbounded.signature M 1 := notCircuit (.id _) G
    have hG'_dw : G'.depthWith Unbounded.andOrCost ≤ d := by
      dsimp [G', notCircuit]
      refine (Circuit.depthWith_comp_le (σ := Unbounded.signature) andOrCost _ _).trans ?_
      simp only [Fin.isValue, Circuit.mapOp_id, Circuit.depthWith_oneGate, andOrCost_not, zero_add]
      exact hd
    have h1 := nw_unbounded_one_sided_le D hM G' hs hG'_dw hq
    have hneg_real :
        ((generator D (parity q)).realExperiment
          (fun y => _root_.PMF.pure (G'.eval Unbounded.interpretation y 0)) true).toReal =
        1 - ((generator D (parity q)).realExperiment
          (fun y => _root_.PMF.pure (G.eval Unbounded.interpretation y 0)) true).toReal := by
      have hsum :
          ((generator D (parity q)).realExperiment
            (fun y => _root_.PMF.pure (G.eval Unbounded.interpretation y 0)) true).toReal +
          ((generator D (parity q)).realExperiment
            (fun y => _root_.PMF.pure (G.eval Unbounded.interpretation y 0)) false).toReal = 1 := by
        have h := apply_true_add_apply_false ((generator D (parity q)).realExperiment
          (fun y => _root_.PMF.pure (G.eval Unbounded.interpretation y 0)))
        have h' := congrArg ENNReal.toReal h
        rw [ENNReal.toReal_add (_root_.PMF.apply_ne_top _ _) (_root_.PMF.apply_ne_top _ _),
          ENNReal.toReal_one] at h'
        exact h'
      have hflip :
          ((generator D (parity q)).realExperiment
            (fun y => _root_.PMF.pure (G'.eval Unbounded.interpretation y 0)) true) =
          ((generator D (parity q)).realExperiment
            (fun y => _root_.PMF.pure (G.eval Unbounded.interpretation y 0)) false) := by
        simp only [Generator.realExperiment, _root_.PMF.bind_apply, _root_.PMF.pure_apply,
          G', eval_notCircuit]
        refine tsum_congr fun y => ?_
        cases G.eval Unbounded.interpretation y 0 <;> simp
      rw [hflip]; linarith
    have hneg_ideal :
        (Generator.idealExperiment
          (fun y => _root_.PMF.pure (G'.eval Unbounded.interpretation y 0)) true).toReal =
        1 - (Generator.idealExperiment
          (fun y => _root_.PMF.pure (G.eval Unbounded.interpretation y 0)) true).toReal := by
      have hsum :
          (Generator.idealExperiment
            (fun y => _root_.PMF.pure (G.eval Unbounded.interpretation y 0)) true).toReal +
          (Generator.idealExperiment
            (fun y => _root_.PMF.pure (G.eval Unbounded.interpretation y 0)) false).toReal = 1 := by
        have h := apply_true_add_apply_false (Generator.idealExperiment
          (fun y => _root_.PMF.pure (G.eval Unbounded.interpretation y 0)))
        have h' := congrArg ENNReal.toReal h
        rw [ENNReal.toReal_add (_root_.PMF.apply_ne_top _ _) (_root_.PMF.apply_ne_top _ _),
          ENNReal.toReal_one] at h'
        exact h'
      have hflip :
          (Generator.idealExperiment
            (fun y => _root_.PMF.pure (G'.eval Unbounded.interpretation y 0)) true) =
          (Generator.idealExperiment
            (fun y => _root_.PMF.pure (G.eval Unbounded.interpretation y 0)) false) := by
        simp only [Generator.idealExperiment, _root_.PMF.bind_apply, _root_.PMF.pure_apply,
          G', eval_notCircuit]
        refine tsum_congr fun y => ?_
        cases G.eval Unbounded.interpretation y 0 <;> simp
      rw [hflip]; linarith
    rw [hneg_real, hneg_ideal] at h1
    have hG'sz : G'.size = G.size + 1 := size_notCircuit (φ := .id _) G
    rw [hG'sz] at h1
    have hcast : ((G.size + 1 + M * (2 ^ a * (a + 1) + 1) + 1 : ℕ) : ℝ) =
        ((G.size + M * (2 ^ a * (a + 1) + 1) + 2 : ℕ) : ℝ) := by
      congr 1; omega
    rw [hcast] at h1
    linarith
  · refine (nw_unbounded_one_sided_le D hM G hs hd hq).trans ?_
    gcongr
    omega



end CslibFrontier.Computability.Circuit.Boolean.Hastad
