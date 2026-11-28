module


public import CslibFrontier.Computability.Circuit.Boolean.MachineSimulation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Circuit.Boolean.PippengerFischerStack
import CslibFrontier.Computability.Circuit.Boolean.Synthesis
import CslibFrontier.Computability.Circuit.Boolean.PolynomialTime
import CslibFrontier.Computability.Circuit.Boolean.Substitution
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
import Mathlib.Data.Nat.Log

/-!
# Pippenger–Fischer `O((T + 1) log (n + T + 2))` circuit simulation

Synthesizes the oblivious 5-slot block-buffer simulation from `PippengerFischerStack` as a De Morgan
circuit of size `O((T + 1) * (Nat.log 2 (n + T + 2) + 1))`. Each local TM transition modifies only
control state, the capped output prefix, head cells, and level `0` of each tape stack (`O(1)` gates
depending only on `k`, `m`, and `|State|`), while rebalancing level `j` against level `j + 1` costs
`O(2 ^ j)` gates and fires every `2 ^ j` steps, summing to `O(T * L)` across `T` steps.

## Main results

* `exists_synthesis_outCap_le_mul_log`: all bits and capped length of `OutCap m` after `T` steps
  are synthesizable in `C * (T + 1) * (Nat.log 2 (n + T + 2) + 1)` De Morgan gates.
* `complexity_slice_acceptedWithin_le_mul_log`: `O((T + 1) log(n + T + 2))` circuit complexity
  bound for `MachineSimulation.acceptedWithin`.
* `exists_complexity_pair_le_mul_log`: `O((T + 1) log(n + T + 2))` circuit complexity bound for
  both output bits of a `Bool × Bool`-valued function on pairs of `n`-bit strings.
-/

public section

namespace CslibFrontier.Computability.Circuit.Boolean

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Turing Turing.MultiTapeTM Finset
open PippengerFischer

section SynthesisPF

variable {n : ℕ}

/-- Any Boolean function of `k` available wires costs at most `2 ^ k * (2 * k + 2) + 1` gates. -/
private theorem synthesis_selected_set {s : Set (BooleanFunction n)} {k : ℕ}
    (w : Fin k → BooleanFunction n) (hw : ∀ i, w i ∈ s) (φ : BooleanFunction k) :
    Synthesis interpretation s {fun x => φ fun i => w i x} (2 ^ k * (2 * k + 2) + 1) := by
  classical
  let accepted := Finset.univ.filter fun q : BitString k => φ q = true
  have hmin (q : BitString k) :
      Synthesis interpretation s {fun x => decide ((fun i => w i x) = q)} (2 * k + 1) := by
    have hall := Synthesis.all_literal (s := s)
      (c := (List.finRange k).map fun i => (w i, q i))
      (by intro l hl; obtain ⟨i, _, rfl⟩ := List.mem_map.1 hl; exact hw i)
    refine (Synthesis.congr_iff hall fun x => ?_).mono Set.Subset.rfl Set.Subset.rfl (by simp)
    simp only [List.all_map, List.all_eq_true, List.mem_finRange, true_implies, Function.comp_def,
      decide_eq_true_eq]
    exact funext_iff.symm
  refine (Synthesis.congr_iff (Synthesis.exists_mem accepted
    (fun q x => decide ((fun i => w i x) = q)) (fun _ => 2 * k + 1)
    fun q _ => hmin q) fun x => by simp [accepted]).mono Set.Subset.rfl Set.Subset.rfl ?_
  rw [Finset.sum_const, smul_eq_mul, show 2 * k + 1 + 1 = 2 * k + 2 by omega]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _
    (by simpa [BitString, Fintype.card_fun] using Finset.card_le_univ accepted)) 1

/-- An `if-then-else` multiplexor over available wires costs 4 gates. -/
private theorem synthesis_ite_mem {s : Set (BooleanFunction n)} {c f g : BooleanFunction n}
    (hc : c ∈ s) (hf : f ∈ s) (hg : g ∈ s) :
    Synthesis interpretation s {fun x => if c x then f x else g x} 4 := by
  have h : Synthesis interpretation s {fun x => (c x && f x) || (!c x && g x)} 4 := by
    have h1 := (Synthesis.of_mem hc).and (Synthesis.of_mem hf)
    have h2 := (Synthesis.of_mem hc).not.and (Synthesis.of_mem hg)
    exact (h1.or h2).mono Set.Subset.rfl Set.Subset.rfl (by omega)
  refine Synthesis.congr_iff h fun x => ?_
  cases c x <;> cases f x <;> cases g x <;> simp

/-- A 2-way nested `if c₁ then f₁ else if c₂ then f₂ else f₃` over available wires costs 8 gates. -/
private theorem synthesis_ite2_mem {s : Set (BooleanFunction n)}
    {c₁ c₂ f₁ f₂ f₃ : BooleanFunction n}
    (hc₁ : c₁ ∈ s) (hc₂ : c₂ ∈ s) (hf₁ : f₁ ∈ s) (hf₂ : f₂ ∈ s) (hf₃ : f₃ ∈ s) :
    Synthesis interpretation s {fun x => if c₁ x then f₁ x else if c₂ x then f₂ x else f₃ x} 8 := by
  have hinner := synthesis_ite_mem hc₂ hf₂ hf₃
  have houter := synthesis_ite_mem (s := s ∪ {fun x => if c₂ x then f₂ x else f₃ x})
    (Set.mem_union_left _ hc₁) (Set.mem_union_left _ hf₁) (Set.mem_union_right _ rfl)
  exact (hinner.trans houter).mono Set.Subset.rfl Set.Subset.rfl (by omega)

/-- Bit `b ∈ Fin 3` of a `Fin 6` counter. -/
private def cntBit (c : Fin 6) (b : Fin 3) : Bool :=
  match b.val with
  | 0 => decide (c.val % 2 = 1)
  | 1 => decide ((c.val / 2) % 2 = 1)
  | _ => decide (4 ≤ c.val)

private def cntOfBits (v : BitString 3) : Fin 6 :=
  ⟨min 5 ((if v 0 then 1 else 0) + 2 * (if v 1 then 1 else 0) + 4 * (if v 2 then 1 else 0)),
    by omega⟩

private theorem cntOfBits_cntBit (c : Fin 6) : cntOfBits (cntBit c) = c := by
  fin_cases c <;> decide

private def cellBit (c : Cell) (b : Fin 2) : Bool :=
  if b.val = 0 then c.1 else c.2

/-- The wire set representing a `LevelData j`-valued function of `x : BitString n`. -/
private def levelWires {j : ℕ} (lv : BitString n → LevelData j) : Set (BooleanFunction n) :=
  (Set.range fun b : Fin 3 => fun x => cntBit (lv x).cnt b) ∪
  (Set.range fun p : Fin 5 × Fin (2 ^ j) × Fin 2 =>
    fun x => cellBit ((lv x).slots p.1 p.2.1) p.2.2)

private theorem cntBit_mem_levelWires {j : ℕ} (lv : BitString n → LevelData j) (b : Fin 3) :
    (fun x => cntBit (lv x).cnt b) ∈ levelWires lv :=
  Or.inl ⟨b, rfl⟩

private theorem slotBit_mem_levelWires {j : ℕ} (lv : BitString n → LevelData j)
    (r : Fin 5) (i : Fin (2 ^ j)) (b : Fin 2) :
    (fun x => cellBit ((lv x).slots r i) b) ∈ levelWires lv :=
  Or.inr ⟨(r, i, b), rfl⟩

private theorem levelWires_eqRec {a b : ℕ} (h : a = b) (lv : BitString n → LevelData a) :
    levelWires (fun x => (h ▸ lv x : LevelData b)) = levelWires lv := by
  subst h; rfl

/-- Synthesizing `rebalancePair` on two levels `(j, j + 1)` costs at most `3600 * 2 ^ j` gates. -/
private theorem synthesis_rebalancePair {j : ℕ} {s : Set (BooleanFunction n)}
    (lv : BitString n → LevelData j) (hi : BitString n → LevelData (j + 1))
    (hlv : levelWires lv ⊆ s) (hhi : levelWires hi ⊆ s) :
    Synthesis interpretation s
      (levelWires (fun x => (rebalancePair (lv x) (hi x)).1) ∪
        levelWires (fun x => (rebalancePair (lv x) (hi x)).2))
      (3600 * 2 ^ j) := by
  let cWires : Fin 3 → BooleanFunction n := fun b x => cntBit (lv x).cnt b
  have hcW : ∀ b, cWires b ∈ s := fun b => hlv (cntBit_mem_levelWires lv b)
  let isEq0 : BooleanFunction n := fun x => decide ((lv x).cnt.val = 0)
  let isEq1 : BooleanFunction n := fun x => decide ((lv x).cnt.val = 1)
  let isBorrow : BooleanFunction n := fun x => decide ((lv x).cnt.val ≤ 1)
  let isCarry : BooleanFunction n := fun x => decide (4 ≤ (lv x).cnt.val)
  let isEq4 : BooleanFunction n := fun x => decide ((lv x).cnt.val = 4)
  have hflag (φ : Fin 6 → Bool) :
      Synthesis interpretation s {fun x => φ (lv x).cnt} 65 := by
    have h := synthesis_selected_set cWires hcW (fun v => φ (cntOfBits v))
    exact Synthesis.congr_iff h fun x => by simp [cWires, cntOfBits_cntBit]
  have hflags : Synthesis interpretation s ({isEq0, isEq1, isBorrow, isCarry, isEq4}) 325 := by
    have h1 := hflag (fun c => decide (c.val = 0))
    have h2 := hflag (fun c => decide (c.val = 1))
    have h3 := hflag (fun c => decide (c.val ≤ 1))
    have h4 := hflag (fun c => decide (4 ≤ c.val))
    have h5 := hflag (fun c => decide (c.val = 4))
    exact ((((h1.union h2).union h3).union h4).union h5).mono Set.Subset.rfl
      (by intro f hf; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
          rcases hf with rfl | rfl | rfl | rfl | rfl <;>
            simp [isEq0, isEq1, isBorrow, isCarry, isEq4])
      (by omega)
  set s₁ := s ∪ {isEq0, isEq1, isBorrow, isCarry, isEq4}
  have hs_sub : s ⊆ s₁ := Set.subset_union_left
  have hisEq0 : isEq0 ∈ s₁ := Set.mem_union_right _ (by simp)
  have hisEq1 : isEq1 ∈ s₁ := Set.mem_union_right _ (by simp)
  have hisBorrow : isBorrow ∈ s₁ := Set.mem_union_right _ (by simp)
  have hisCarry : isCarry ∈ s₁ := Set.mem_union_right _ (by simp)
  have hisEq4 : isEq4 ∈ s₁ := Set.mem_union_right _ (by simp)
  have hlv_cnt : Synthesis interpretation s₁
      (Set.range fun b : Fin 3 => fun x => cntBit (rebalancePair (lv x) (hi x)).1.cnt b) 195 := by
    refine (Synthesis.iUnion (I := interpretation) (s := s₁)
      (fun b : Fin 3 => {fun x => cntBit (rebalancePair (lv x) (hi x)).1.cnt b})
      (fun _ => 65) fun b => ?_).mono Set.Subset.rfl
      (Set.range_subset_iff.2 fun b => Set.mem_iUnion.2 ⟨b, rfl⟩) (by simp)
    have h := synthesis_selected_set (s := s₁) cWires (fun i => hs_sub (hcW i))
      (fun v =>
        let c := cntOfBits v
        cntBit (if hc1 : c.val ≤ 1 then ⟨c.val + 2, by omega⟩
                else if hc4 : 4 ≤ c.val then ⟨c.val - 2, by omega⟩ else c) b)
    refine Synthesis.congr_iff h fun x => ?_
    simp only [cWires, cntOfBits_cntBit, rebalancePair]
    split_ifs <;> rfl
  have hhi_cnt : Synthesis interpretation s₁
      (Set.range fun b : Fin 3 => fun x => cntBit (rebalancePair (lv x) (hi x)).2.cnt b) 2691 := by
    let bothW : Fin 6 → BooleanFunction n := fun idx =>
      if h : idx.val < 3 then fun x => cntBit (lv x).cnt ⟨idx.val, h⟩
      else fun x => cntBit (hi x).cnt ⟨idx.val - 3, by omega⟩
    have hbothW : ∀ idx, bothW idx ∈ s₁ := fun idx => by
      dsimp only [bothW]
      split_ifs with h
      · exact hs_sub (hlv (cntBit_mem_levelWires lv _))
      · exact hs_sub (hhi (cntBit_mem_levelWires hi _))
    refine (Synthesis.iUnion (I := interpretation) (s := s₁)
      (fun b : Fin 3 => {fun x => cntBit (rebalancePair (lv x) (hi x)).2.cnt b})
      (fun _ => 897) fun b => ?_).mono Set.Subset.rfl
      (Set.range_subset_iff.2 fun b => Set.mem_iUnion.2 ⟨b, rfl⟩) (by simp)
    have h := synthesis_selected_set (s := s₁) bothW hbothW
      (fun v =>
        let c := cntOfBits fun i : Fin 3 => v ⟨i.val, by omega⟩
        let d := cntOfBits fun i : Fin 3 => v ⟨i.val + 3, by omega⟩
        cntBit (if hc1 : c.val ≤ 1 then ⟨d.val - 1, by omega⟩
                else if hc4 : 4 ≤ c.val then ⟨min 5 (d.val + 1), by omega⟩ else d) b)
    refine Synthesis.congr_iff h fun x => ?_
    have h1 : (fun i : Fin 3 => bothW ⟨i.val, by omega⟩ x) = cntBit (lv x).cnt := by
      funext i; simp [bothW, i.isLt]
    have h2 : (fun i : Fin 3 => bothW ⟨i.val + 3, by omega⟩ x) = cntBit (hi x).cnt := by
      funext i; simp [bothW]
    simp only [h1, h2, cntOfBits_cntBit, rebalancePair]
    split_ifs <;> rfl
  have hlv_slots : Synthesis interpretation s₁
      (Set.range fun p : Fin 5 × Fin (2 ^ j) × Fin 2 =>
        fun x => cellBit ((rebalancePair (lv x) (hi x)).1.slots p.1 p.2.1) p.2.2)
      (80 * 2 ^ j) := by
    refine (Synthesis.iUnion (I := interpretation) (s := s₁)
      (fun p : Fin 5 × Fin (2 ^ j) × Fin 2 =>
        {fun x => cellBit ((rebalancePair (lv x) (hi x)).1.slots p.1 p.2.1) p.2.2})
      (fun _ => 8) fun ⟨r, i, b⟩ => ?_).mono Set.Subset.rfl
      (Set.range_subset_iff.2 fun p => Set.mem_iUnion.2 ⟨p, rfl⟩) (by simp; ring_nf; omega)
    have hA : (fun x => cellBit ((splitBlock ((hi x).slots 0)).1 i) b) ∈ s₁ :=
      hs_sub (hhi (slotBit_mem_levelWires hi 0 ⟨i.val, by rw [pow_succ]; omega⟩ b))
    have hB : (fun x => cellBit ((splitBlock ((hi x).slots 0)).2 i) b) ∈ s₁ :=
      hs_sub (hhi (slotBit_mem_levelWires hi 0 ⟨2 ^ j + i.val, by rw [pow_succ]; omega⟩ b))
    have hcur : (fun x => cellBit ((lv x).slots r i) b) ∈ s₁ :=
      hs_sub (hlv (slotBit_mem_levelWires lv r i b))
    fin_cases r
    · exact (synthesis_ite_mem hisEq0 hA hcur).mono Set.Subset.rfl
        (Set.singleton_subset_iff.2 (funext fun x => by
          rcases hcx : (lv x).cnt with ⟨c, hc⟩
          have hc6 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
          rcases hc6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [rebalancePair, isEq0, hcx])) (by omega)
    · exact (synthesis_ite2_mem hisEq0 hisEq1 hB hA hcur).mono Set.Subset.rfl
        (Set.singleton_subset_iff.2 (funext fun x => by
          rcases hcx : (lv x).cnt with ⟨c, hc⟩
          have hc6 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
          rcases hc6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [rebalancePair, isEq0, isEq1, hcx])) le_rfl
    · exact (synthesis_ite_mem hisEq1 hB hcur).mono Set.Subset.rfl
        (Set.singleton_subset_iff.2 (funext fun x => by
          rcases hcx : (lv x).cnt with ⟨c, hc⟩
          have hc6 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
          rcases hc6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [rebalancePair, isEq1, hcx])) (by omega)
    · exact (Synthesis.of_mem hcur).mono Set.Subset.rfl
        (Set.singleton_subset_iff.2 (funext fun x => by
          unfold rebalancePair; split_ifs <;> rfl)) (by omega)
    · exact (Synthesis.of_mem hcur).mono Set.Subset.rfl
        (Set.singleton_subset_iff.2 (funext fun x => by
          unfold rebalancePair; split_ifs <;> rfl)) (by omega)
  have hhi_slots : Synthesis interpretation s₁
      (Set.range fun p : Fin 5 × Fin (2 ^ (j + 1)) × Fin 2 =>
        fun x => cellBit ((rebalancePair (lv x) (hi x)).2.slots p.1 p.2.1) p.2.2)
      (240 * 2 ^ j) := by
    refine (Synthesis.iUnion (I := interpretation) (s := s₁)
      (fun p : Fin 5 × Fin (2 ^ (j + 1)) × Fin 2 =>
        {fun x => cellBit ((rebalancePair (lv x) (hi x)).2.slots p.1 p.2.1) p.2.2})
      (fun _ => 12) fun ⟨r, idx, b⟩ => ?_).mono Set.Subset.rfl
      (Set.range_subset_iff.2 fun p => Set.mem_iUnion.2 ⟨p, rfl⟩)
      (by simp [pow_succ]; ring_nf; omega)
    have hhi_cur : (fun x => cellBit ((hi x).slots r idx) b) ∈ s₁ :=
      hs_sub (hhi (slotBit_mem_levelWires hi r idx b))
    by_cases hr0 : r.val = 0
    · have hr_eq : r = 0 := Fin.ext hr0
      subst hr_eq
      have hhi1 : (fun x => cellBit ((hi x).slots 1 idx) b) ∈ s₁ :=
        hs_sub (hhi (slotBit_mem_levelWires hi 1 idx b))
      by_cases hidx : idx.val < 2 ^ j
      · have hlv2 : (fun x => cellBit ((lv x).slots 2 ⟨idx.val, hidx⟩) b) ∈ s₁ :=
          hs_sub (hlv (slotBit_mem_levelWires lv 2 ⟨idx.val, hidx⟩ b))
        have hlv3 : (fun x => cellBit ((lv x).slots 3 ⟨idx.val, hidx⟩) b) ∈ s₁ :=
          hs_sub (hlv (slotBit_mem_levelWires lv 3 ⟨idx.val, hidx⟩ b))
        have hm := synthesis_ite_mem hisEq4 hlv2 hlv3
        have hout := synthesis_ite2_mem
          (s := s₁ ∪ {fun x => if isEq4 x then cellBit ((lv x).slots 2 ⟨idx.val, hidx⟩) b
                               else cellBit ((lv x).slots 3 ⟨idx.val, hidx⟩) b})
          (Set.mem_union_left _ hisBorrow) (Set.mem_union_left _ hisCarry)
          (Set.mem_union_left _ hhi1) (Set.mem_union_right _ rfl) (Set.mem_union_left _ hhi_cur)
        refine (hm.trans hout).mono Set.Subset.rfl
          (Set.singleton_subset_iff.2 (funext fun x => ?_)) (by omega)
        rw [rebalancePair_snd_slot0_lt (lv x) (hi x) idx hidx]
        by_cases h1 : (lv x).cnt.val ≤ 1
        · simp [isBorrow, h1]
        · by_cases h4 : 4 ≤ (lv x).cnt.val
          · by_cases heq4 : (lv x).cnt.val = 4 <;> simp [isBorrow, isCarry, isEq4, h1, h4, heq4]
          · simp [isBorrow, isCarry, h1, h4]
      · have hidx' : idx.val - 2 ^ j < 2 ^ j := by
          have hlt : idx.val < 2 ^ j * 2 := by simpa [pow_succ] using idx.isLt
          omega
        have hlv3 : (fun x => cellBit ((lv x).slots 3 ⟨idx.val - 2 ^ j, hidx'⟩) b) ∈ s₁ :=
          hs_sub (hlv (slotBit_mem_levelWires lv 3 ⟨idx.val - 2 ^ j, hidx'⟩ b))
        have hlv4 : (fun x => cellBit ((lv x).slots 4 ⟨idx.val - 2 ^ j, hidx'⟩) b) ∈ s₁ :=
          hs_sub (hlv (slotBit_mem_levelWires lv 4 ⟨idx.val - 2 ^ j, hidx'⟩ b))
        have hm := synthesis_ite_mem hisEq4 hlv3 hlv4
        have hout := synthesis_ite2_mem
          (s := s₁ ∪ {fun x => if isEq4 x then cellBit ((lv x).slots 3 ⟨idx.val - 2 ^ j, hidx'⟩) b
                               else cellBit ((lv x).slots 4 ⟨idx.val - 2 ^ j, hidx'⟩) b})
          (Set.mem_union_left _ hisBorrow) (Set.mem_union_left _ hisCarry)
          (Set.mem_union_left _ hhi1) (Set.mem_union_right _ rfl) (Set.mem_union_left _ hhi_cur)
        refine (hm.trans hout).mono Set.Subset.rfl
          (Set.singleton_subset_iff.2 (funext fun x => ?_)) (by omega)
        rw [rebalancePair_snd_slot0_ge (lv x) (hi x) idx hidx hidx']
        by_cases h1 : (lv x).cnt.val ≤ 1
        · simp [isBorrow, h1]
        · by_cases h4 : 4 ≤ (lv x).cnt.val
          · by_cases heq4 : (lv x).cnt.val = 4 <;> simp [isBorrow, isCarry, isEq4, h1, h4, heq4]
          · simp [isBorrow, isCarry, h1, h4]
    · have hrpos : 0 < r.val := by omega
      have hprev : (fun x => cellBit ((hi x).slots ⟨r.val - 1, by omega⟩ idx) b) ∈ s₁ :=
        hs_sub (hhi (slotBit_mem_levelWires hi ⟨r.val - 1, by omega⟩ idx b))
      by_cases hnext : r.val + 1 < 5
      · have hhiN : (fun x => cellBit ((hi x).slots ⟨r.val + 1, hnext⟩ idx) b) ∈ s₁ :=
          hs_sub (hhi (slotBit_mem_levelWires hi ⟨r.val + 1, hnext⟩ idx b))
        refine (synthesis_ite2_mem hisBorrow hisCarry hhiN hprev hhi_cur).mono Set.Subset.rfl
          (Set.singleton_subset_iff.2 (funext fun x => ?_)) (by omega)
        rw [rebalancePair_snd_slot_pos (lv x) (hi x) r hrpos idx]
        by_cases h1 : (lv x).cnt.val ≤ 1
        · simp [isBorrow, h1, hnext]
        · by_cases h4 : 4 ≤ (lv x).cnt.val <;> simp [isBorrow, isCarry, h1, h4]
      · have h0 : Synthesis interpretation s₁ {fun _ => false} 1 := Synthesis.const false
        have h2 := synthesis_ite2_mem (s := s₁ ∪ {fun _ => false})
          (Set.mem_union_left _ hisBorrow) (Set.mem_union_left _ hisCarry)
          (Set.mem_union_right _ rfl) (Set.mem_union_left _ hprev) (Set.mem_union_left _ hhi_cur)
        refine (h0.trans h2).mono Set.Subset.rfl
          (Set.singleton_subset_iff.2 (funext fun x => ?_)) (by omega)
        rw [rebalancePair_snd_slot_pos (lv x) (hi x) r hrpos idx]
        by_cases h1 : (lv x).cnt.val ≤ 1
        · simp [isBorrow, h1, hnext, cellBit, blankCell]
        · by_cases h4 : 4 ≤ (lv x).cnt.val <;> simp [isBorrow, isCarry, h1, h4]
  have hall := (hlv_cnt.union hlv_slots).union (hhi_cnt.union hhi_slots)
  have h2j : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  exact (hflags.trans hall).mono Set.Subset.rfl Set.Subset.rfl (by omega)

/-- Wires representing a `BlockStack L`. -/
private def stackWires {L : ℕ} (st : BitString n → BlockStack L) : Set (BooleanFunction n) :=
  ⋃ j : Fin L, levelWires (fun x => st x j)

/-- Wires representing a `ZipperTape L`. -/
private def zipperWires {L : ℕ} (z : BitString n → ZipperTape L) : Set (BooleanFunction n) :=
  stackWires (fun x => (z x).left) ∪
  (Set.range fun b : Fin 2 => fun x => cellBit (z x).center b) ∪
  stackWires (fun x => (z x).right)

/-- Wires representing an `ObliviousCfg k m State L`. -/
private def cfgWires {k m L : ℕ} {State : Type} [DecidableEq State]
    (oc : BitString n → ObliviousCfg k m State L) : Set (BooleanFunction n) :=
  (Set.range fun q : Option State => fun x => decide ((oc x).state = q)) ∪
  (Set.range fun l : Fin (m + 2) => fun x => decide ((oc x).out.len = l)) ∪
  (Set.range fun i : Fin m => fun x => (oc x).out.bits i) ∪
  zipperWires (fun x => (oc x).inTape) ∪
  (⋃ i : Fin k, zipperWires (fun x => (oc x).workTapes i))

private theorem synthesis_applyRebalance {L : ℕ} {s : Set (BooleanFunction n)}
    (st : BitString n → BlockStack L) (hst : stackWires st ⊆ s) (j : ℕ) (hj : j + 1 < L) :
    Synthesis interpretation s (stackWires fun x => (st x).applyRebalance j hj) (3600 * 2 ^ j) := by
  have h1 : levelWires (fun x => st x ⟨j, by omega⟩) ⊆ s :=
    (Set.subset_iUnion (fun i : Fin L => levelWires (fun x => st x i)) ⟨j, by omega⟩).trans hst
  have h2 : levelWires (fun x => st x ⟨j + 1, hj⟩) ⊆ s :=
    (Set.subset_iUnion (fun i : Fin L => levelWires (fun x => st x i)) ⟨j + 1, hj⟩).trans hst
  have hreb := synthesis_rebalancePair (fun x => st x ⟨j, by omega⟩)
    (fun x => st x ⟨j + 1, hj⟩) h1 h2
  have hfree : Synthesis interpretation s s 0 := Synthesis.of_subset Set.Subset.rfl
  refine (hfree.union hreb).mono Set.Subset.rfl ?_ (by omega)
  refine Set.iUnion_subset fun i => ?_
  by_cases hi1 : i.val = j
  · have heq : (fun x => (st x).applyRebalance j hj i) =
        fun x => hi1 ▸ (rebalancePair (st x ⟨j, by omega⟩) (st x ⟨j + 1, hj⟩)).1 := by
      funext x; simp [BlockStack.applyRebalance, dite_eq_left hi1]
    rw [heq, levelWires_eqRec]
    exact Set.subset_union_of_subset_right Set.subset_union_left _
  · by_cases hi2 : i.val = j + 1
    · have heq : (fun x => (st x).applyRebalance j hj i) =
          fun x => hi2 ▸ (rebalancePair (st x ⟨j, by omega⟩) (st x ⟨j + 1, hj⟩)).2 := by
        funext x; simp [BlockStack.applyRebalance, dite_eq_right hi1, dite_eq_left hi2]
      rw [heq, levelWires_eqRec]
      exact Set.subset_union_of_subset_right Set.subset_union_right _
    · have heq : (fun x => (st x).applyRebalance j hj i) = fun x => st x i := by
        funext x; simp [BlockStack.applyRebalance, dite_eq_right hi1, dite_eq_right hi2]
      rw [heq]
      exact Set.subset_union_of_subset_left
        ((Set.subset_iUnion (fun l : Fin L => levelWires (fun x => st x l)) i).trans hst) _

private def rebalanceLoopCost (L t : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => rebalanceLoopCost L t j + if j + 1 < L ∧ 2 ^ j ∣ t then 3600 * 2 ^ j else 0

private theorem synthesis_rebalanceLoop {L : ℕ} {s : Set (BooleanFunction n)} (t : ℕ)
    (st : BitString n → BlockStack L) (hst : stackWires st ⊆ s) :
    ∀ m, Synthesis interpretation s (stackWires fun x => (st x).rebalanceLoop t m)
      (rebalanceLoopCost L t m)
  | 0 => (Synthesis.of_subset hst).mono Set.Subset.rfl Set.Subset.rfl le_rfl
  | j + 1 => by
    have ih := synthesis_rebalanceLoop t st hst j
    simp only [BlockStack.rebalanceLoop, rebalanceLoopCost]
    split_ifs with h
    · have hstep := synthesis_applyRebalance (s := s ∪ stackWires fun x => (st x).rebalanceLoop t j)
        (fun x => (st x).rebalanceLoop t j) Set.subset_union_right j h.1
      exact ih.trans hstep
    · exact ih.mono Set.Subset.rfl Set.Subset.rfl (by omega)

/-- Extract level `0` of tape-stack `side < 2 * (k + 1)` from an `ObliviousCfg`. -/
private def sideLv0 {k m L : ℕ} {State : Type} (hL : 0 < L)
    (oc : ObliviousCfg k m State L) (side : ℕ) : LevelData 0 :=
  if side = 0 then oc.inTape.left ⟨0, hL⟩
  else if side = 1 then oc.inTape.right ⟨0, hL⟩
  else
    let ti := (side - 2) / 2
    if ht : ti < k then
      if (side - 2) % 2 = 0 then (oc.workTapes ⟨ti, ht⟩).left ⟨0, hL⟩
      else (oc.workTapes ⟨ti, ht⟩).right ⟨0, hL⟩
    else oc.inTape.left ⟨0, hL⟩

/-- Synthesizing one local TM transition (touching only `state`, `out`, `center`, and level `0`
of each stack) costs a constant `C_step` depending only on `k`, `m`, and `|State|`. -/
private theorem synthesis_localStep {k m : ℕ} {State : Type} [DecidableEq State] [Finite State]
    (tm : MultiTapeTM k Bool State) :
    ∃ C_step : ℕ, ∀ (n' L' : ℕ) (hL' : 0 < L')
      (oc' : BitString n' → ObliviousCfg k m State L') (s' : Set (BooleanFunction n')),
      cfgWires oc' ⊆ s' →
      Synthesis interpretation s' (cfgWires fun x => localStepOblivious tm hL' (oc' x)) C_step := by
  classical
  have := Fintype.ofFinite State
  let o1 := Fintype.card State + 1
  let o2 := o1 + (m + 2)
  let o3 := o2 + m
  let o4 := o3 + 2
  let o5 := o4 + 2 * k
  let W := o5 + 2 * (k + 1) * 13
  let wireCost := 2 ^ W * (2 * W + 2) + 1
  refine ⟨W * wireCost, fun n' L' hL' oc' s' hoc' => ?_⟩
  let stEquiv := Fintype.equivFin (Option State)
  let localWires : Fin W → BooleanFunction n' := fun idx =>
    let a := idx.val
    if h1 : a < o1 then
      fun x => decide ((oc' x).state = stEquiv.symm ⟨a, by simp [Fintype.card_option]; omega⟩)
    else if h2 : a < o2 then
      fun x => decide ((oc' x).out.len = ⟨a - o1, by omega⟩)
    else if h3 : a < o3 then
      fun x => (oc' x).out.bits ⟨a - o2, by omega⟩
    else if h4 : a < o4 then
      fun x => cellBit (oc' x).inTape.center ⟨a - o3, by omega⟩
    else if h5 : a < o5 then
      fun x => cellBit ((oc' x).workTapes ⟨(a - o4) / 2, by omega⟩).center ⟨(a - o4) % 2, by omega⟩
    else
      let side := (a - o5) / 13
      let pos := (a - o5) % 13
      if hp3 : pos < 3 then fun x => cntBit (sideLv0 hL' (oc' x) side).cnt ⟨pos, hp3⟩
      else if hr : (pos - 3) / 2 < 5 then
        fun x => cellBit ((sideLv0 hL' (oc' x) side).slots ⟨(pos - 3) / 2, hr⟩ ⟨0, by norm_num⟩)
          ⟨(pos - 3) % 2, by omega⟩
      else fun _ => false
  have hsideLv_mem (side : ℕ) : levelWires (fun x => sideLv0 hL' (oc' x) side) ⊆ s' := by
    by_cases hs0 : side = 0
    · simp only [sideLv0, hs0, ↓reduceIte]
      exact (Set.subset_iUnion _ ⟨0, hL'⟩).trans
        ((Set.subset_union_left.trans Set.subset_union_left).trans
          ((Set.subset_union_right.trans Set.subset_union_left).trans hoc'))
    · by_cases hs1 : side = 1
      · simp only [sideLv0, hs1, ↓reduceIte]
        exact (Set.subset_iUnion _ ⟨0, hL'⟩).trans
          (Set.subset_union_right.trans
            ((Set.subset_union_right.trans Set.subset_union_left).trans hoc'))
      · by_cases hti : (side - 2) / 2 < k
        · by_cases hpar : (side - 2) % 2 = 0
          · simp only [sideLv0, hs0, hs1, hti, hpar, ↓reduceIte, ↓reduceDIte]
            exact (Set.subset_iUnion _ ⟨0, hL'⟩).trans
              ((Set.subset_union_left.trans Set.subset_union_left).trans
                ((Set.subset_iUnion (fun i => zipperWires fun x => (oc' x).workTapes i) _).trans
                  (Set.subset_union_right.trans hoc')))
          · simp only [sideLv0, hs0, hs1, hti, hpar, ↓reduceIte, ↓reduceDIte]
            exact (Set.subset_iUnion _ ⟨0, hL'⟩).trans
              (Set.subset_union_right.trans
                ((Set.subset_iUnion (fun i => zipperWires fun x => (oc' x).workTapes i) _).trans
                  (Set.subset_union_right.trans hoc')))
        · simp only [sideLv0, hs0, hs1, hti, ↓reduceIte, ↓reduceDIte]
          exact (Set.subset_iUnion _ ⟨0, hL'⟩).trans
            ((Set.subset_union_left.trans Set.subset_union_left).trans
              ((Set.subset_union_right.trans Set.subset_union_left).trans hoc'))
  have hloc_mem : ∀ idx, localWires idx ∈ s' := fun idx => by
    dsimp only [localWires]
    split_ifs with h1 h2 h3 h4 h5 hp3 hr
    · exact hoc' (Or.inl (Or.inl (Or.inl (Or.inl ⟨_, rfl⟩))))
    · exact hoc' (Or.inl (Or.inl (Or.inl (Or.inr ⟨_, rfl⟩))))
    · exact hoc' (Or.inl (Or.inl (Or.inr ⟨_, rfl⟩)))
    · exact hoc' (Or.inl (Or.inr (Or.inl (Or.inr ⟨_, rfl⟩))))
    · exact hoc' (Or.inr (Set.mem_iUnion.2 ⟨_, Or.inl (Or.inr ⟨_, rfl⟩)⟩))
    · exact hsideLv_mem _ (cntBit_mem_levelWires _ _)
    · exact hsideLv_mem _ (slotBit_mem_levelWires _ _ _ _)
    · exfalso; omega
  let decState (v : BitString W) : Option State :=
    if h : ∃ i : Fin o1, v ⟨i.val, by omega⟩ = true then
      stEquiv.symm ⟨h.choose.val, by
        have := h.choose.isLt; simp [Fintype.card_option]; dsimp [o1] at this; omega⟩
    else none
  let decLen (v : BitString W) : Fin (m + 2) :=
    if h : ∃ i : Fin (m + 2), v ⟨o1 + i.val, by omega⟩ = true then h.choose else ⟨0, by omega⟩
  let decOut (v : BitString W) : OutCap m :=
    { len := decLen v, bits := fun i => v ⟨o2 + i.val, by omega⟩ }
  let decInC (v : BitString W) : Cell := (v ⟨o3, by omega⟩, v ⟨o3 + 1, by omega⟩)
  let decWC (v : BitString W) (i : Fin k) : Cell :=
    (v ⟨o4 + 2 * i.val, by omega⟩, v ⟨o4 + 2 * i.val + 1, by omega⟩)
  let decLv (v : BitString W) (side : ℕ) (hside : side < 2 * (k + 1)) : LevelData 0 :=
    { cnt := cntOfBits fun b => v ⟨o5 + side * 13 + b.val, by omega⟩
      slots := fun r _ => (v ⟨o5 + side * 13 + 3 + 2 * r.val, by omega⟩,
                           v ⟨o5 + side * 13 + 3 + 2 * r.val + 1, by omega⟩) }
  have hdecState (x : BitString n') : decState (fun idx => localWires idx x) = (oc' x).state := by
    let q0 : Fin o1 := ⟨(stEquiv (oc' x).state).val, by
      simpa [o1, Fintype.card_option] using (stEquiv (oc' x).state).isLt⟩
    have hex : ∃ i : Fin o1, localWires ⟨i.val, by omega⟩ x = true :=
      ⟨q0, by
        simp only [localWires, q0.isLt, ↓reduceDIte, decide_eq_true_eq]
        exact (stEquiv.symm_apply_apply _).symm⟩
    simp only [decState, dite_eq_left hex]
    have hc := hex.choose_spec
    simp only [localWires, hex.choose.isLt, ↓reduceDIte, decide_eq_true_eq] at hc
    exact hc.symm
  have hdecLen (x : BitString n') : decLen (fun idx => localWires idx x) = (oc' x).out.len := by
    have hex : ∃ i : Fin (m + 2), localWires ⟨o1 + i.val, by omega⟩ x = true :=
      ⟨(oc' x).out.len, by
        simp only [localWires, show ¬ (o1 + (oc' x).out.len.val < o1) by omega,
          show o1 + (oc' x).out.len.val < o2 by omega, ↓reduceDIte,
          Nat.add_sub_cancel_left, Fin.eta, decide_true]⟩
    simp only [decLen, dite_eq_left hex]
    set c := hex.choose
    have hc : localWires ⟨o1 + c.val, by omega⟩ x = true := hex.choose_spec
    dsimp only [localWires] at hc
    rw [dite_eq_right (by omega : ¬ o1 + c.val < o1),
      dite_eq_left (by omega : o1 + c.val < o2)] at hc
    simp only [Nat.add_sub_cancel_left, Fin.eta, decide_eq_true_eq] at hc
    exact hc.symm
  have hdecOut (x : BitString n') : decOut (fun idx => localWires idx x) = (oc' x).out := by
    ext
    · exact congrArg Fin.val (hdecLen x)
    · rename_i i
      simp only [decOut, localWires, show ¬ (o2 + i.val < o1) by omega,
        show ¬ (o2 + i.val < o2) by omega, show o2 + i.val < o3 by omega,
        ↓reduceDIte, Nat.add_sub_cancel_left, Fin.eta]
  have hdecInC (x : BitString n') :
      decInC (fun idx => localWires idx x) = (oc' x).inTape.center := by
    rcases hc : (oc' x).inTape.center with ⟨a, b⟩
    simp only [decInC, localWires,
      show ¬ (o3 < o1) by omega, show ¬ (o3 < o2) by omega, show ¬ (o3 < o3) by omega,
      show o3 < o4 by omega,
      show ¬ (o3 + 1 < o1) by omega, show ¬ (o3 + 1 < o2) by omega, show ¬ (o3 + 1 < o3) by omega,
      show o3 + 1 < o4 by omega, ↓reduceDIte,
      show o3 - o3 = 0 by omega, show o3 + 1 - o3 = 1 by omega,
      cellBit, hc, ↓reduceIte, show ¬ (1 = 0) by omega]
  have hdecWC (x : BitString n') (i : Fin k) :
      decWC (fun idx => localWires idx x) i = ((oc' x).workTapes i).center := by
    rcases hc : ((oc' x).workTapes i).center with ⟨a, b⟩
    simp only [decWC, localWires,
      show ¬ (o4 + 2 * i.val < o1) by omega, show ¬ (o4 + 2 * i.val < o2) by omega,
      show ¬ (o4 + 2 * i.val < o3) by omega, show ¬ (o4 + 2 * i.val < o4) by omega,
      show o4 + 2 * i.val < o5 by omega,
      show ¬ (o4 + 2 * i.val + 1 < o1) by omega, show ¬ (o4 + 2 * i.val + 1 < o2) by omega,
      show ¬ (o4 + 2 * i.val + 1 < o3) by omega, show ¬ (o4 + 2 * i.val + 1 < o4) by omega,
      show o4 + 2 * i.val + 1 < o5 by omega, ↓reduceDIte,
      show o4 + 2 * i.val - o4 = 2 * i.val by omega,
      show o4 + 2 * i.val + 1 - o4 = 2 * i.val + 1 by omega,
      show (2 * i.val) / 2 = i.val by omega, show (2 * i.val) % 2 = 0 by omega,
      show (2 * i.val + 1) / 2 = i.val by omega, show (2 * i.val + 1) % 2 = 1 by omega,
      Fin.eta, cellBit, hc, ↓reduceIte, show ¬ (1 = 0) by omega]
  have hdecLv (x : BitString n') (side : ℕ) (hside : side < 2 * (k + 1)) :
      decLv (fun idx => localWires idx x) side hside = sideLv0 hL' (oc' x) side := by
    rcases hlv : sideLv0 hL' (oc' x) side with ⟨tcnt, tslots⟩
    have hbase (off : ℕ) (hoff : off < 13) :
        localWires ⟨o5 + side * 13 + off, by omega⟩ x =
          if hp3 : off < 3 then cntBit tcnt ⟨off, hp3⟩
          else if hr : (off - 3) / 2 < 5 then
            cellBit (tslots ⟨(off - 3) / 2, hr⟩ ⟨0, by norm_num⟩) ⟨(off - 3) % 2, by omega⟩
          else false := by
      simp only [localWires, show ¬ (o5 + side * 13 + off < o1) by omega,
        show ¬ (o5 + side * 13 + off < o2) by omega, show ¬ (o5 + side * 13 + off < o3) by omega,
        show ¬ (o5 + side * 13 + off < o4) by omega, show ¬ (o5 + side * 13 + off < o5) by omega,
        ↓reduceDIte, show o5 + side * 13 + off - o5 = side * 13 + off by omega,
        show (side * 13 + off) / 13 = side by
          rw [mul_comm, Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt hoff, add_zero],
        show (side * 13 + off) % 13 = off by
          rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hoff]]
      by_cases hp3 : off < 3
      · simp only [hp3, ↓reduceDIte, hlv]
      · by_cases hr : (off - 3) / 2 < 5
        · simp only [hp3, hr, ↓reduceDIte, hlv]
        · simp only [hp3, hr, ↓reduceDIte]
    unfold decLv
    have hcnt_eq : (cntOfBits fun b : Fin 3 =>
        localWires ⟨o5 + side * 13 + b.val, by omega⟩ x) = tcnt := by
      have : (fun b : Fin 3 => localWires ⟨o5 + side * 13 + b.val, by omega⟩ x) = cntBit tcnt := by
        funext b; simpa [b.isLt] using hbase b.val (by omega)
      rw [this, cntOfBits_cntBit]
    have hslots_eq : (fun (r : Fin 5) (_ : Fin (2 ^ 0)) =>
        (localWires ⟨o5 + side * 13 + 3 + 2 * r.val, by omega⟩ x,
         localWires ⟨o5 + side * 13 + 3 + 2 * r.val + 1, by omega⟩ x)) = tslots := by
      funext r u
      have hu : u = ⟨0, by norm_num⟩ := Fin.ext (by have := u.isLt; norm_num at this; omega)
      subst hu
      have hb0 := hbase (3 + 2 * r.val) (by omega)
      have hb1 := hbase (3 + 2 * r.val + 1) (by omega)
      simp only [show ¬ (3 + 2 * r.val < 3) by omega,
        show ¬ (3 + 2 * r.val + 1 < 3) by omega, ↓reduceDIte,
        show (3 + 2 * r.val - 3) / 2 = r.val by omega, show (3 + 2 * r.val - 3) % 2 = 0 by omega,
        show (3 + 2 * r.val + 1 - 3) / 2 = r.val by omega,
        show (3 + 2 * r.val + 1 - 3) % 2 = 1 by omega, r.isLt, Fin.eta, cellBit,
        ↓reduceIte, show ¬ (1 = 0) by omega] at hb0 hb1
      rw [show (⟨o5 + side * 13 + 3 + 2 * r.val, by omega⟩ : Fin W) =
            ⟨o5 + side * 13 + (3 + 2 * r.val), by omega⟩ from Fin.ext (by dsimp; omega),
          show (⟨o5 + side * 13 + 3 + 2 * r.val + 1, by omega⟩ : Fin W) =
            ⟨o5 + side * 13 + (3 + 2 * r.val + 1), by omega⟩ from Fin.ext (by dsimp; omega),
          hb0, hb1]
    exact congrArg₂ LevelData.mk hcnt_eq hslots_eq
  let stepLv (v : BitString W) (side : ℕ) (hside : side < 2 * (k + 1)) : LevelData 0 :=
    match decState v with
    | none => decLv v side hside
    | some q =>
      let act := tm.tr q (cellDec (decInC v)) (fun i => cellDec (decWC v i))
      if side = 0 then
        match clampInMove (decInC v) act.inputTape with
        | .zero => decLv v 0 (by omega)
        | .pos => (decLv v 0 (by omega)).push0 (decInC v)
        | .neg => (decLv v 0 (by omega)).pop0
      else if side = 1 then
        match clampInMove (decInC v) act.inputTape with
        | .zero => decLv v 1 (by omega)
        | .pos => (decLv v 1 (by omega)).pop0
        | .neg => (decLv v 1 (by omega)).push0 (decInC v)
      else
        let ti := (side - 2) / 2
        if ht : ti < k then
          let wcell := match (act.workTapes ⟨ti, ht⟩).1 with
            | none => decWC v ⟨ti, ht⟩ | some sym => workEnc sym
          if (side - 2) % 2 = 0 then
            match (act.workTapes ⟨ti, ht⟩).2 with
            | .zero => decLv v side hside
            | .pos => (decLv v side hside).push0 wcell
            | .neg => (decLv v side hside).pop0
          else
            match (act.workTapes ⟨ti, ht⟩).2 with
            | .zero => decLv v side hside
            | .pos => (decLv v side hside).pop0
            | .neg => (decLv v side hside).push0 wcell
        else decLv v side hside
  let nextLocalPhi (idx : Fin W) (v : BitString W) : Bool :=
    let a := idx.val
    let nextSt : Option State := match decState v with
      | none => none
      | some q => (tm.tr q (cellDec (decInC v)) (fun i => cellDec (decWC v i))).state
    let nextOut : OutCap m := match decState v with
      | none => decOut v
      | some q => (decOut v).push (tm.tr q (cellDec (decInC v))
        (fun i => cellDec (decWC v i))).output
    let nextInC : Cell := match decState v with
      | none => decInC v
      | some q =>
        let act := tm.tr q (cellDec (decInC v)) (fun i => cellDec (decWC v i))
        match clampInMove (decInC v) act.inputTape with
        | .zero => decInC v
        | .pos => (decLv v 1 (by omega)).top0
        | .neg => (decLv v 0 (by omega)).top0
    let nextWC (i : Fin k) : Cell := match decState v with
      | none => decWC v i
      | some q =>
        let act := tm.tr q (cellDec (decInC v)) (fun j => cellDec (decWC v j))
        let wcell := match (act.workTapes i).1 with | none => decWC v i | some sym => workEnc sym
        match (act.workTapes i).2 with
        | .zero => wcell
        | .pos => (decLv v (2 + 2 * i.val + 1) (by omega)).top0
        | .neg => (decLv v (2 + 2 * i.val) (by omega)).top0
    if h1 : a < o1 then
      decide (nextSt = stEquiv.symm ⟨a, by simp [Fintype.card_option]; omega⟩)
    else if h2 : a < o2 then decide (nextOut.len = ⟨a - o1, by omega⟩)
    else if h3 : a < o3 then nextOut.bits ⟨a - o2, by omega⟩
    else if h4 : a < o4 then cellBit nextInC ⟨a - o3, by omega⟩
    else if h5 : a < o5 then cellBit (nextWC ⟨(a - o4) / 2, by omega⟩) ⟨(a - o4) % 2, by omega⟩
    else
      let side := (a - o5) / 13
      let pos := (a - o5) % 13
      if hside : side < 2 * (k + 1) then
        let lv := stepLv v side hside
        if hp3 : pos < 3 then cntBit lv.cnt ⟨pos, hp3⟩
        else if hr : (pos - 3) / 2 < 5 then
          cellBit (lv.slots ⟨(pos - 3) / 2, hr⟩ ⟨0, by norm_num⟩) ⟨(pos - 3) % 2, by omega⟩
        else false
      else false
  have hnextLoc : Synthesis interpretation s'
      (Set.range fun idx : Fin W => fun x => nextLocalPhi idx fun j => localWires j x)
      (W * wireCost) := by
    refine (Synthesis.iUnion (I := interpretation) (s := s')
      (fun idx : Fin W => {fun x => nextLocalPhi idx fun j => localWires j x})
      (fun _ => wireCost) fun idx =>
        synthesis_selected_set localWires hloc_mem (nextLocalPhi idx)).mono
      Set.Subset.rfl (Set.range_subset_iff.2 fun idx => Set.mem_iUnion.2 ⟨idx, rfl⟩) (by simp)
  have hkeep := Synthesis.of_subset (I := interpretation) (s := s') Set.Subset.rfl
  refine (hkeep.union hnextLoc).mono Set.Subset.rfl ?_ (by omega)
  have hstepLv_eq (x : BitString n') (side : ℕ) (hside : side < 2 * (k + 1)) :
      stepLv (fun idx => localWires idx x) side hside =
        sideLv0 hL' (localStepOblivious tm hL' (oc' x)) side := by
    simp only [stepLv, hdecState, hdecInC, hdecWC, hdecLv]
    unfold localStepOblivious sideLv0
    rcases (oc' x).state with _ | q
    · rfl
    · by_cases hs0 : side = 0
      · subst hs0
        simp only [↓reduceIte]
        cases clampInMove _ _ <;> simp [ZipperTape.step, BlockStack.update0]
      · by_cases hs1 : side = 1
        · subst hs1
          simp only [↓reduceIte, show ¬ (1 = 0) by omega]
          cases clampInMove _ _ <;> simp [ZipperTape.step, BlockStack.update0]
        · have hti : (side - 2) / 2 < k := by omega
          by_cases hpar : (side - 2) % 2 = 0
          · simp only [hs0, hs1, hti, hpar, ↓reduceIte, ↓reduceDIte]
            cases ((tm.tr q _ _).workTapes ⟨(side - 2) / 2, hti⟩).2 <;>
              simp [ZipperTape.step, BlockStack.update0]; rfl
          · simp only [hs0, hs1, hti, hpar, ↓reduceIte, ↓reduceDIte]
            cases ((tm.tr q _ _).workTapes ⟨(side - 2) / 2, hti⟩).2 <;>
              simp [ZipperTape.step, BlockStack.update0]; rfl
  -- Unified inclusion for level `0` of any stack `side < 2 * (k + 1)`
  have hside_in_range (side : ℕ) (hside : side < 2 * (k + 1)) :
      levelWires (fun x => sideLv0 hL' (localStepOblivious tm hL' (oc' x)) side) ⊆
        Set.range fun idx : Fin W => fun x => nextLocalPhi idx fun j => localWires j x := by
    rintro f (⟨b, rfl⟩ | ⟨⟨r, u, b⟩, rfl⟩)
    · refine ⟨⟨o5 + side * 13 + b.val, by omega⟩, funext fun x => ?_⟩
      simp only [nextLocalPhi, show ¬ (o5 + side * 13 + b.val < o1) by omega,
        show ¬ (o5 + side * 13 + b.val < o2) by omega,
        show ¬ (o5 + side * 13 + b.val < o3) by omega,
        show ¬ (o5 + side * 13 + b.val < o4) by omega,
        show ¬ (o5 + side * 13 + b.val < o5) by omega, ↓reduceDIte,
        show o5 + side * 13 + b.val - o5 = side * 13 + b.val by omega,
        show (side * 13 + b.val) / 13 = side by
          rw [mul_comm, Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt (by omega), add_zero],
        show (side * 13 + b.val) % 13 = b.val by
          rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)],
        hside, b.isLt, Fin.eta, hstepLv_eq]
    · have hu : u = ⟨0, by norm_num⟩ := Fin.ext (by have := u.isLt; norm_num at this; omega)
      subst hu
      refine ⟨⟨o5 + side * 13 + 3 + 2 * r.val + b.val, by omega⟩, funext fun x => ?_⟩
      simp only [nextLocalPhi, show ¬ (o5 + side * 13 + 3 + 2 * r.val + b.val < o1) by omega,
        show ¬ (o5 + side * 13 + 3 + 2 * r.val + b.val < o2) by omega,
        show ¬ (o5 + side * 13 + 3 + 2 * r.val + b.val < o3) by omega,
        show ¬ (o5 + side * 13 + 3 + 2 * r.val + b.val < o4) by omega,
        show ¬ (o5 + side * 13 + 3 + 2 * r.val + b.val < o5) by omega, ↓reduceDIte,
        show o5 + side * 13 + 3 + 2 * r.val + b.val - o5 = side * 13 + (3 + 2 * r.val + b.val) by
          omega,
        show (side * 13 + (3 + 2 * r.val + b.val)) / 13 = side by
          rw [mul_comm, Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt (by omega), add_zero],
        show (side * 13 + (3 + 2 * r.val + b.val)) % 13 = 3 + 2 * r.val + b.val by
          rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)],
        hside, show ¬ (3 + 2 * r.val + b.val < 3) by omega,
        show (3 + 2 * r.val + b.val - 3) / 2 = r.val by omega,
        show (3 + 2 * r.val + b.val - 3) % 2 = b.val by omega, r.isLt, Fin.eta, hstepLv_eq]
  rintro f ((((⟨q, rfl⟩ | ⟨l, rfl⟩) | ⟨i, rfl⟩) | ((hInL | ⟨b, rfl⟩) | hInR)) | hWork)
  · refine Or.inr ⟨⟨(stEquiv q).val, by
      have := (stEquiv q).isLt; simp [Fintype.card_option] at this; omega⟩, funext fun x => ?_⟩
    have hlt : (stEquiv q).val < o1 := by
      simpa [o1, Fintype.card_option] using (stEquiv q).isLt
    dsimp only [nextLocalPhi]
    rw [dite_eq_left hlt]
    simp only [Fin.eta, Equiv.symm_apply_apply, hdecState, hdecInC, hdecWC, localStepOblivious]
    rcases Option.eq_none_or_eq_some (oc' x).state with hst | ⟨q', hst⟩ <;> simp [hst]
  · refine Or.inr ⟨⟨o1 + l.val, by omega⟩, funext fun x => ?_⟩
    dsimp only [nextLocalPhi]
    rw [dite_eq_right (by omega : ¬ o1 + l.val < o1), dite_eq_left (by omega : o1 + l.val < o2)]
    simp only [Nat.add_sub_cancel_left, Fin.eta, hdecState, hdecOut, hdecInC, hdecWC,
      localStepOblivious]
    rcases Option.eq_none_or_eq_some (oc' x).state with hst | ⟨q', hst⟩ <;> simp [hst]
  · refine Or.inr ⟨⟨o2 + i.val, by omega⟩, funext fun x => ?_⟩
    dsimp only [nextLocalPhi]
    rw [dite_eq_right (by omega : ¬ o2 + i.val < o1),
      dite_eq_right (by omega : ¬ o2 + i.val < o2),
      dite_eq_left (by omega : o2 + i.val < o3)]
    simp only [Nat.add_sub_cancel_left, Fin.eta, hdecState, hdecOut, hdecInC, hdecWC,
      localStepOblivious]
    rcases Option.eq_none_or_eq_some (oc' x).state with hst | ⟨q', hst⟩ <;> simp [hst]
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hInL
    by_cases hj0 : j.val = 0
    · have hj_eq : j = ⟨0, hL'⟩ := Fin.ext hj0
      subst hj_eq
      exact Or.inr (hside_in_range 0 (by omega) (by simpa [sideLv0] using hj))
    · have heq : (fun x => (localStepOblivious tm hL' (oc' x)).inTape.left j) =
          fun x => (oc' x).inTape.left j := by
        funext x
        rcases hst : (oc' x).state with _ | q
        · simp [localStepOblivious, hst]
        · simp only [localStepOblivious, hst, ZipperTape.step]
          cases clampInMove (oc' x).inTape.center
              (tm.tr q (cellDec (oc' x).inTape.center)
                (fun i => cellDec ((oc' x).workTapes i).center)).inputTape <;>
            simp [BlockStack.update0, hj0]
      rw [heq] at hj
      exact Or.inl (hoc' (Or.inl (Or.inr (Or.inl (Or.inl (Set.mem_iUnion.2 ⟨j, hj⟩))))))
  · refine Or.inr ⟨⟨o3 + b.val, by omega⟩, funext fun x => ?_⟩
    dsimp only [nextLocalPhi]
    rw [dite_eq_right (by omega : ¬ o3 + b.val < o1),
      dite_eq_right (by omega : ¬ o3 + b.val < o2),
      dite_eq_right (by omega : ¬ o3 + b.val < o3),
      dite_eq_left (by omega : o3 + b.val < o4)]
    simp only [Nat.add_sub_cancel_left, Fin.eta,
      hdecState, hdecInC, hdecWC, hdecLv, sideLv0, ↓reduceIte, show ¬ (1 = 0) by omega,
      localStepOblivious]
    rcases hst : (oc' x).state with _ | q
    · rfl
    · simp only [ZipperTape.step]
      cases clampInMove (oc' x).inTape.center
          (tm.tr q (cellDec (oc' x).inTape.center)
            (fun i => cellDec ((oc' x).workTapes i).center)).inputTape <;> rfl
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hInR
    by_cases hj0 : j.val = 0
    · have hj_eq : j = ⟨0, hL'⟩ := Fin.ext hj0
      subst hj_eq
      exact Or.inr (hside_in_range 1 (by omega) (by simpa [sideLv0] using hj))
    · have heq : (fun x => (localStepOblivious tm hL' (oc' x)).inTape.right j) =
          fun x => (oc' x).inTape.right j := by
        funext x
        rcases hst : (oc' x).state with _ | q
        · simp [localStepOblivious, hst]
        · simp only [localStepOblivious, hst, ZipperTape.step]
          cases clampInMove (oc' x).inTape.center
              (tm.tr q (cellDec (oc' x).inTape.center)
                (fun i => cellDec ((oc' x).workTapes i).center)).inputTape <;>
            simp [BlockStack.update0, hj0]
      rw [heq] at hj
      exact Or.inl (hoc' (Or.inl (Or.inr (Or.inr (Set.mem_iUnion.2 ⟨j, hj⟩)))))
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hWork
    rcases hi with (hWL | ⟨b, rfl⟩) | hWR
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hWL
      by_cases hj0 : j.val = 0
      · have hj_eq : j = ⟨0, hL'⟩ := Fin.ext hj0
        subst hj_eq
        refine Or.inr (hside_in_range (2 + 2 * i.val) (by omega) ?_)
        have hlv_eq : (fun x => sideLv0 hL' (localStepOblivious tm hL' (oc' x)) (2 + 2 * i.val)) =
            fun x => ((localStepOblivious tm hL' (oc' x)).workTapes i).left ⟨0, hL'⟩ := by
          funext x
          simp only [sideLv0, show ¬ (2 + 2 * i.val = 0) by omega,
            show ¬ (2 + 2 * i.val = 1) by omega, show (2 + 2 * i.val - 2) / 2 = i.val by omega,
            i.isLt, show (2 + 2 * i.val - 2) % 2 = 0 by omega, ↓reduceIte, ↓reduceDIte, Fin.eta]
        rw [hlv_eq]; exact hj
      · have heq : (fun x => ((localStepOblivious tm hL' (oc' x)).workTapes i).left j) =
            fun x => ((oc' x).workTapes i).left j := by
          funext x
          rcases hst : (oc' x).state with _ | q
          · simp [localStepOblivious, hst]
          · simp only [localStepOblivious, hst, ZipperTape.step]
            cases ((tm.tr q (cellDec (oc' x).inTape.center)
                (fun j => cellDec ((oc' x).workTapes j).center)).workTapes i).2 <;>
              simp [BlockStack.update0, hj0]
        rw [heq] at hj
        exact Or.inl (hoc' (Or.inr (Set.mem_iUnion.2
          ⟨i, Or.inl (Or.inl (Set.mem_iUnion.2 ⟨j, hj⟩))⟩)))
    · refine Or.inr ⟨⟨o4 + 2 * i.val + b.val, by omega⟩, funext fun x => ?_⟩
      dsimp only [nextLocalPhi]
      rw [dite_eq_right (by omega : ¬ o4 + 2 * i.val + b.val < o1),
        dite_eq_right (by omega : ¬ o4 + 2 * i.val + b.val < o2),
        dite_eq_right (by omega : ¬ o4 + 2 * i.val + b.val < o3),
        dite_eq_right (by omega : ¬ o4 + 2 * i.val + b.val < o4),
        dite_eq_left (by omega : o4 + 2 * i.val + b.val < o5)]
      simp only [show o4 + 2 * i.val + b.val - o4 = 2 * i.val + b.val by omega,
        show (2 * i.val + b.val) / 2 = i.val by omega,
        show (2 * i.val + b.val) % 2 = b.val by omega, Fin.eta,
        hdecState, hdecInC, hdecWC, hdecLv, sideLv0,
        show ¬ (2 + 2 * i.val = 0) by omega, show ¬ (2 + 2 * i.val = 1) by omega,
        show ¬ (2 + 2 * i.val + 1 = 0) by omega, show ¬ (2 + 2 * i.val + 1 = 1) by omega,
        show (2 + 2 * i.val - 2) / 2 = i.val by omega,
        show (2 + 2 * i.val - 2) % 2 = 0 by omega,
        show (2 + 2 * i.val + 1 - 2) / 2 = i.val by omega,
        show ¬ ((2 + 2 * i.val + 1 - 2) % 2 = 0) by omega, i.isLt, ↓reduceIte, ↓reduceDIte,
        localStepOblivious]
      rcases hst : (oc' x).state with _ | q
      · rfl
      · simp only [ZipperTape.step]
        cases ((tm.tr q (cellDec (oc' x).inTape.center)
            (fun j => cellDec ((oc' x).workTapes j).center)).workTapes i).2 <;> rfl
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hWR
      by_cases hj0 : j.val = 0
      · have hj_eq : j = ⟨0, hL'⟩ := Fin.ext hj0
        subst hj_eq
        refine Or.inr (hside_in_range (2 + 2 * i.val + 1) (by omega) ?_)
        have hlv_eq :
            (fun x => sideLv0 hL' (localStepOblivious tm hL' (oc' x)) (2 + 2 * i.val + 1)) =
            fun x => ((localStepOblivious tm hL' (oc' x)).workTapes i).right ⟨0, hL'⟩ := by
          funext x
          simp only [sideLv0, show ¬ (2 + 2 * i.val + 1 = 0) by omega,
            show ¬ (2 + 2 * i.val + 1 = 1) by omega,
            show (2 + 2 * i.val + 1 - 2) / 2 = i.val by omega,
            i.isLt, show ¬ ((2 + 2 * i.val + 1 - 2) % 2 = 0) by omega, ↓reduceIte, ↓reduceDIte,
            Fin.eta]
        rw [hlv_eq]; exact hj
      · have heq : (fun x => ((localStepOblivious tm hL' (oc' x)).workTapes i).right j) =
            fun x => ((oc' x).workTapes i).right j := by
          funext x
          rcases hst : (oc' x).state with _ | q
          · simp [localStepOblivious, hst]
          · simp only [localStepOblivious, hst, ZipperTape.step]
            cases ((tm.tr q (cellDec (oc' x).inTape.center)
                (fun j => cellDec ((oc' x).workTapes j).center)).workTapes i).2 <;>
              simp [BlockStack.update0, hj0]
        rw [heq] at hj
        exact Or.inl (hoc' (Or.inr (Set.mem_iUnion.2 ⟨i, Or.inr (Set.mem_iUnion.2 ⟨j, hj⟩)⟩)))

/-- Initialization wires all belong to `inputs n ∪ {false, true}`, costing 2 gates total. -/
private theorem synthesis_initOblivious {k m L : ℕ} {State : Type} [DecidableEq State]
    (tm : MultiTapeTM k Bool State) :
    Synthesis interpretation (inputs n)
      (cfgWires fun x : BitString n => initObliviousCfg (m := m) tm L x) 2 := by
  have hconst : Synthesis interpretation (inputs n) ({fun _ => true} ∪ {fun _ => false}) 2 :=
    (Synthesis.const true).union (Synthesis.const false)
  have hmem_const (b : Bool) : (fun _ : BitString n => b) ∈
      inputs n ∪ ({fun _ => true} ∪ {fun _ => false}) := by
    cases b
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  have hmem_inCell (p : ℕ) (b : Fin 2) :
      (fun x : BitString n => cellBit (inCell x p) b) ∈
        inputs n ∪ ({fun _ => true} ∪ {fun _ => false}) := by
    by_cases hb : b.val = 0 <;> by_cases h0 : p = 0 <;> by_cases h1 : p - 1 < n <;>
      simp only [inCell, cellBit, hb, h0, h1, ↓reduceIte, ↓reduceDIte]
    · exact hmem_const false
    · exact hmem_const false
    · exact hmem_const true
    · exact hmem_const false
    · exact hmem_const false
    · exact hmem_const false
    · exact Or.inl ⟨⟨p - 1, h1⟩, rfl⟩
    · exact hmem_const true
  have hmem_initStack (f : ℕ → BitString n → Cell)
      (hf : ∀ u b, (fun x => cellBit (f u x) b) ∈ inputs n ∪ ({fun _ => true} ∪ {fun _ => false})) :
      stackWires (fun x => initStack L (fun u => f u x)) ⊆
        inputs n ∪ ({fun _ => true} ∪ {fun _ => false}) := by
    refine Set.iUnion_subset fun j => Set.union_subset ?_ ?_
    · rintro _ ⟨b, rfl⟩; exact hmem_const (cntBit ⟨2, by omega⟩ b)
    · rintro _ ⟨⟨r, i, b⟩, rfl⟩
      simp only [initStack]
      split_ifs with hr
      · exact hf _ b
      · exact hmem_const (cellBit blankCell b)
  have hsub : cfgWires (fun x : BitString n => initObliviousCfg (m := m) tm L x) ⊆
      inputs n ∪ ({fun _ => true} ∪ {fun _ => false}) := by
    rintro f ((((⟨q, rfl⟩ | ⟨l, rfl⟩) | ⟨i, rfl⟩) | ((hInL | ⟨b, rfl⟩) | hInR)) | hWork)
    · exact hmem_const (decide (some tm.q₀ = q))
    · exact hmem_const (decide ((OutCap.ofList m []).len = l))
    · exact hmem_const ((OutCap.ofList m []).bits i)
    · exact hmem_initStack (fun _ _ => (false, false)) (fun _ b => hmem_const _) hInL
    · exact hmem_inCell 1 b
    · exact hmem_initStack (fun r x => inCell x (r + 2)) (fun r b => hmem_inCell (r + 2) b) hInR
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hWork
      rcases hi with (hL | ⟨b, rfl⟩) | hR
      · exact hmem_initStack (fun _ _ => blankCell) (fun _ b => hmem_const _) hL
      · exact hmem_const (cellBit blankCell b)
      · exact hmem_initStack (fun _ _ => blankCell) (fun _ b => hmem_const _) hR
  exact (hconst.trans (Synthesis.of_subset hsub)).mono Set.Subset.rfl Set.Subset.rfl (by omega)

/-- Counting bound: `∑_{t=1}^T rebalanceLoopCost L t (L - 1) ≤ 3600 * T * (L - 1)`. -/
private theorem sum_rebalanceLoopCost_le (L : ℕ) :
    ∀ (m T : ℕ),
      (∑ t ∈ Finset.range T, rebalanceLoopCost L (t + 1) m) ≤ 3600 * T * m
  | 0, T => by simp [rebalanceLoopCost]
  | j + 1, T => by
    have ih := sum_rebalanceLoopCost_le L j T
    have hsplit : (∑ t ∈ Finset.range T, rebalanceLoopCost L (t + 1) (j + 1)) =
        (∑ t ∈ Finset.range T, rebalanceLoopCost L (t + 1) j) +
        ∑ t ∈ Finset.range T, (if j + 1 < L ∧ 2 ^ j ∣ (t + 1) then 3600 * 2 ^ j else 0) := by
      rw [← Finset.sum_add_distrib]
      rfl
    have hcnt : #{t ∈ Finset.range T | 2 ^ j ∣ (t + 1)} * 2 ^ j ≤ T := by
      let f : ℕ → ℕ := fun t => (t + 1) / 2 ^ j - 1
      have hinj : Set.InjOn f ↑((Finset.range T).filter fun t => 2 ^ j ∣ (t + 1)) := by
        intro a ha b hb hab
        have ha' := (Finset.mem_filter.1 ha).2
        have hb' := (Finset.mem_filter.1 hb).2
        have hpa : 1 ≤ (a + 1) / 2 ^ j := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos a) ha')
          (Nat.two_pow_pos j)
        have hpb : 1 ≤ (b + 1) / 2 ^ j := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos b) hb')
          (Nat.two_pow_pos j)
        have hq : (a + 1) / 2 ^ j = (b + 1) / 2 ^ j := by dsimp [f] at hab; omega
        have heqa := Nat.div_mul_cancel ha'
        have heqb := Nat.div_mul_cancel hb'
        have heq1 : a + 1 = b + 1 := by rw [← heqa, ← heqb, hq]
        omega
      have hmaps : Set.MapsTo f ↑((Finset.range T).filter fun t => 2 ^ j ∣ (t + 1))
          ↑(Finset.range (T / 2 ^ j)) := by
        intro t ht
        obtain ⟨htr, htd⟩ := Finset.mem_filter.1 ht
        have htlt := Finset.mem_range.1 htr
        have hpos : 1 ≤ (t + 1) / 2 ^ j := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos t) htd)
          (Nat.two_pow_pos j)
        have hle : (t + 1) / 2 ^ j ≤ T / 2 ^ j := Nat.div_le_div_right (by omega)
        exact Finset.mem_coe.2 (Finset.mem_range.2 (by dsimp [f]; omega))
      have hcard := Finset.card_le_card_of_injOn f hmaps hinj
      rw [Finset.card_range] at hcard
      exact (Nat.mul_le_mul_right (2 ^ j) hcard).trans (Nat.div_mul_le_self T (2 ^ j))
    have hterm : (∑ t ∈ Finset.range T,
        (if j + 1 < L ∧ 2 ^ j ∣ (t + 1) then 3600 * 2 ^ j else 0)) ≤ 3600 * T := by
      by_cases hltL : j + 1 < L
      · simp only [hltL, true_and, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
        calc #{t ∈ Finset.range T | 2 ^ j ∣ (t + 1)} * (3600 * 2 ^ j)
            = 3600 * (#{t ∈ Finset.range T | 2 ^ j ∣ (t + 1)} * 2 ^ j) := by ring
          _ ≤ 3600 * T := Nat.mul_le_mul_left 3600 hcnt
      · simp [hltL]
    rw [hsplit]
    calc (∑ t ∈ Finset.range T, rebalanceLoopCost L (t + 1) j) +
          ∑ t ∈ Finset.range T, (if j + 1 < L ∧ 2 ^ j ∣ (t + 1) then 3600 * 2 ^ j else 0)
        ≤ 3600 * T * j + 3600 * T := Nat.add_le_add ih hterm
      _ = 3600 * T * (j + 1) := by ring

end SynthesisPF

/-! ### Main Pippenger–Fischer circuit simulation theorems -/

/-- **Pippenger–Fischer simulation for `OutCap m`**. For any finite-state `MultiTapeTM k Bool State`
and fixed output prefix width `m`, there is a constant `C` such that for all `n` and `T`, all
features of `OutCap.ofList m (tm.runFrom (tm.initCfg x) T).output` can be synthesized from
`inputs n` within `C * (T + 1) * (Nat.log 2 (n + T + 2) + 1)` De Morgan gates. -/
theorem exists_synthesis_outCap_le_mul_log {k m : ℕ} {State : Type} [Finite State]
    (tm : MultiTapeTM k Bool State) :
    ∃ C : ℕ, ∀ (n T : ℕ),
      let outFn (x : BitString n) : OutCap m :=
        OutCap.ofList m (tm.runFrom (tm.initCfg (List.ofFn x)) T).output
      Synthesis interpretation (inputs n)
        ((Set.range fun l : Fin (m + 2) => fun x => decide ((outFn x).len = l)) ∪
         (Set.range fun i : Fin m => fun x => (outFn x).bits i))
        (C * (T + 1) * (Nat.log 2 (n + T + 2) + 1)) := by
  classical
  have := Fintype.ofFinite State
  obtain ⟨C_step, hStep⟩ := synthesis_localStep (m := m) tm
  refine ⟨C_step + 2 * (k + 1) * 3600 + 2, fun n T => ?_⟩
  set L := Nat.log 2 (n + T + 2) + 2 with hL_def
  have hL2 : 2 ≤ L := by omega
  have hSumLT : n + T + 2 < 2 ^ (L - 1) := by
    have : n + T + 2 < 2 ^ (Nat.log 2 (n + T + 2) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    have hL1 : L - 1 = Nat.log 2 (n + T + 2) + 1 := by omega
    rw [hL1]; exact this
  have hLT : T < 2 ^ (L - 1) := by omega
  have hnL : n + 2 ≤ 2 * (2 ^ L - 1) := by
    have : 2 ^ (L - 1) ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    omega
  have hrun : ∀ t : ℕ,
      Synthesis interpretation (inputs n)
        (cfgWires fun x : BitString n => runOblivious (m := m) (L := L) tm (by omega) x t)
        (2 + t * C_step +
          2 * (k + 1) * ∑ u ∈ Finset.range t, rebalanceLoopCost L (u + 1) (L - 1)) := by
    intro t
    induction t with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, Nat.zero_mul, Nat.mul_zero, add_zero]
      exact synthesis_initOblivious (n := n) (m := m) (L := L) tm
    | succ t ih =>
      set oc := fun x : BitString n => runOblivious (m := m) (L := L) tm (by omega) x t
      set mid : BitString n → ObliviousCfg k m State L :=
        fun x => localStepOblivious tm (by omega) (oc x)
      have h1 := hStep n L (by omega) oc (inputs n ∪ cfgWires oc) Set.subset_union_right
      set s_mid := inputs n ∪ cfgWires mid
      have hmid_sub : cfgWires mid ⊆ s_mid := Set.subset_union_right
      have hr_inL := synthesis_rebalanceLoop (s := s_mid) (t + 1) (fun x => (mid x).inTape.left)
        ((Set.subset_union_left.trans Set.subset_union_left).trans
          ((Set.subset_union_right.trans Set.subset_union_left).trans hmid_sub)) (L - 1)
      have hr_inR := synthesis_rebalanceLoop (s := s_mid) (t + 1) (fun x => (mid x).inTape.right)
        (Set.subset_union_right.trans
          ((Set.subset_union_right.trans Set.subset_union_left).trans hmid_sub)) (L - 1)
      have hr_wL (i : Fin k) := synthesis_rebalanceLoop (s := s_mid) (t + 1)
        (fun x => ((mid x).workTapes i).left)
        ((Set.subset_union_left.trans Set.subset_union_left).trans
          ((Set.subset_iUnion (fun i => zipperWires fun x => (mid x).workTapes i) i).trans
            (Set.subset_union_right.trans hmid_sub))) (L - 1)
      have hr_wR (i : Fin k) := synthesis_rebalanceLoop (s := s_mid) (t + 1)
        (fun x => ((mid x).workTapes i).right)
        (Set.subset_union_right.trans
          ((Set.subset_iUnion (fun i => zipperWires fun x => (mid x).workTapes i) i).trans
            (Set.subset_union_right.trans hmid_sub))) (L - 1)
      have hr_work := Synthesis.iUnion (I := interpretation) (s := s_mid)
        (fun i : Fin k =>
          stackWires (fun x => ((mid x).workTapes i).left.rebalanceLoop (t + 1) (L - 1)) ∪
          stackWires (fun x => ((mid x).workTapes i).right.rebalanceLoop (t + 1) (L - 1)))
        (fun _ => 2 * rebalanceLoopCost L (t + 1) (L - 1))
        fun i => ((hr_wL i).union (hr_wR i)).mono Set.Subset.rfl Set.Subset.rfl (by omega)
      have hkeep := Synthesis.of_subset (I := interpretation) (s := s_mid) hmid_sub
      have h2 : Synthesis interpretation s_mid
          (cfgWires fun x => runOblivious (m := m) (L := L) tm (by omega) x (t + 1))
          (2 * (k + 1) * rebalanceLoopCost L (t + 1) (L - 1)) :=
        ((hkeep.union (hr_inL.union hr_inR)).union hr_work).mono Set.Subset.rfl
          (by
            rintro f ((((⟨q, rfl⟩ | ⟨l, rfl⟩) | ⟨i, rfl⟩) | ((hL' | ⟨b, rfl⟩) | hR')) | hW')
            · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨q, rfl⟩)))))
            · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩)))))
            · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))
            · exact Or.inl (Or.inr (Or.inl hL'))
            · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨b, rfl⟩)))))
            · exact Or.inl (Or.inr (Or.inr hR'))
            · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hW'
              rcases hi with (hWL | ⟨b, rfl⟩) | hWR
              · exact Or.inr (Set.mem_iUnion.2 ⟨i, Or.inl hWL⟩)
              · exact Or.inl (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, Or.inl (Or.inr ⟨b, rfl⟩)⟩)))
              · exact Or.inr (Set.mem_iUnion.2 ⟨i, Or.inr hWR⟩))
          (by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
            ring_nf; omega)
      refine ((ih.trans h1).trans h2).mono Set.Subset.rfl Set.Subset.rfl ?_
      rw [Finset.sum_range_succ]
      ring_nf; omega
  have hmatch (x : BitString n) :
      (runOblivious (m := m) (L := L) tm (by omega) x T).out =
        OutCap.ofList m (tm.runFrom (tm.initCfg (List.ofFn x)) T).output :=
    (matchesCfg_runOblivious tm hL2 hnL x T hLT).2.1
  have hsum := sum_rebalanceLoopCost_le L (L - 1) T
  have hL1 : L - 1 = Nat.log 2 (n + T + 2) + 1 := by omega
  refine (hrun T).mono Set.Subset.rfl ?_ ?_
  · rintro f (⟨l, rfl⟩ | ⟨i, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨l, funext fun x => by dsimp only; rw [hmatch x]⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨i, funext fun x => by dsimp only; rw [hmatch x]⟩))
  · rw [hL1] at hsum
    set lg := Nat.log 2 (n + T + 2) + 1
    have hlg : 1 ≤ lg := by omega
    have hT1 : 1 ≤ T + 1 := by omega
    have hbound : 2 + T * C_step + 2 * (k + 1) * (3600 * T * lg) ≤
        (C_step + 2 * (k + 1) * 3600 + 2) * (T + 1) * lg := by
      have h1 : T * C_step ≤ C_step * (T + 1) * lg := by
        calc T * C_step = C_step * T := mul_comm _ _
          _ ≤ C_step * (T + 1) := Nat.mul_le_mul_left _ (by omega)
          _ ≤ C_step * (T + 1) * lg := Nat.le_mul_of_pos_right _ hlg
      have h2 : 2 ≤ 2 * (T + 1) * lg := by nlinarith
      have h3 : 2 * (k + 1) * (3600 * T * lg) ≤ (2 * (k + 1) * 3600) * (T + 1) * lg := by
        calc 2 * (k + 1) * (3600 * T * lg) = (2 * (k + 1) * 3600) * T * lg := by ring
          _ ≤ (2 * (k + 1) * 3600) * (T + 1) * lg :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      nlinarith
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ hsum) _).trans hbound

/-- **Pippenger–Fischer circuit simulation for single-bit output (`acceptedWithin`)**.
Upgrades `MachineSimulation.complexity_slice_acceptedWithin_le` from `O((n + T) ^ 2)` to
`O((T + 1) * (log₂(n + T + 2) + 1))`. -/
theorem complexity_slice_acceptedWithin_le_mul_log {k : ℕ} {State : Type} [DecidableEq State]
    [Finite State] (tm : MultiTapeTM k Bool State) :
    ∃ C : ℕ, ∀ (T : ℕ → ℕ) (n : ℕ),
      complexity interpretation (single ((MachineSimulation.acceptedWithin tm T).slice n)) ≤
        C * (T n + 1) * (Nat.log 2 (n + T n + 2) + 1) := by
  classical
  obtain ⟨C, hC⟩ := exists_synthesis_outCap_le_mul_log (m := 1) tm
  refine ⟨C + 1, fun T n => ?_⟩
  have hsyn := hC n (T n)
  let outFn (x : BitString n) : OutCap 1 :=
    OutCap.ofList 1 (tm.runFrom (tm.initCfg (List.ofFn x)) (T n)).output
  have hlen1 : (fun x => decide ((outFn x).len = ⟨1, by omega⟩)) ∈
      inputs n ∪ ((Set.range fun l : Fin 3 => fun x => decide ((outFn x).len = l)) ∪
        (Set.range fun i : Fin 1 => fun x => (outFn x).bits i)) :=
    Or.inr (Or.inl ⟨⟨1, by omega⟩, rfl⟩)
  have hbit0 : (fun x => (outFn x).bits ⟨0, by omega⟩) ∈
      inputs n ∪ ((Set.range fun l : Fin 3 => fun x => decide ((outFn x).len = l)) ∪
        (Set.range fun i : Fin 1 => fun x => (outFn x).bits i)) :=
    Or.inr (Or.inr ⟨⟨0, by omega⟩, rfl⟩)
  have hand := (Synthesis.of_mem hlen1).and (Synthesis.of_mem hbit0)
  have heq : (MachineSimulation.acceptedWithin tm T).slice n =
      fun x => decide ((outFn x).len = ⟨1, by omega⟩) && (outFn x).bits ⟨0, by omega⟩ := by
    funext x
    rw [MachineSimulation.acceptedWithin, Language.slice_ofSlices, Bool.eq_iff_iff,
      Bool.and_eq_true, decide_eq_true_eq]
    simp only [MachineSimulation.featureFn, MachineSimulation.cfgAt, decide_eq_true_eq,
      Feature.holds_out, OutView.ofList_eq_one_iff, outFn, OutCap.ofList_len, OutCap.ofList_bits]
    rcases (tm.runFrom (tm.initCfg (List.ofFn x)) (T n)).output with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp
    · cases a <;> simp
    · simp [Fin.ext_iff]
  rw [heq]
  have hcomb := (hsyn.trans hand).complexity_le
  have hpos : 1 ≤ (T n + 1) * (Nat.log 2 (n + T n + 2) + 1) :=
    Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  calc complexity interpretation (single fun x =>
        decide ((outFn x).len = ⟨1, by omega⟩) && (outFn x).bits ⟨0, by omega⟩)
      ≤ C * (T n + 1) * (Nat.log 2 (n + T n + 2) + 1) + 1 := hcomb
    _ ≤ (C + 1) * (T n + 1) * (Nat.log 2 (n + T n + 2) + 1) := by nlinarith

/-- **Pippenger–Fischer simulation for `Bool × Bool`-valued functions on pairs of `n`-bit strings**.
Given a `ComputableInTimeAndSpace` function `f : List Bool × List Bool → Bool × Bool` running in
time `tFn (x, y) ≤ T` for `|x| = |y| = n`, both coordinate Boolean functions on `BitString (n + n)`
have De Morgan circuit complexity at most `C * (T + 1) * (Nat.log 2 (n + T + 2) + 1)`. -/
theorem exists_complexity_pair_le_mul_log {f : List Bool × List Bool → Bool × Bool}
    {tFn sFn : List Bool × List Bool → ℕ}
    (hf : ComputableInTimeAndSpace f (encPair encBits encBits) (encPair encBool encBool) tFn sFn) :
    ∃ C : ℕ, ∀ (n T : ℕ),
      (∀ x y : List Bool, x.length = n → y.length = n → tFn (x, y) ≤ T) →
      complexity interpretation
        (single fun p : BitString (n + n) =>
          (f (List.ofFn fun i : Fin n => p (Fin.castAdd n i),
              List.ofFn fun i : Fin n => p (Fin.natAdd n i))).1) ≤
        C * (T + 1) * (Nat.log 2 (n + T + 2) + 1) ∧
      complexity interpretation
        (single fun p : BitString (n + n) =>
          (f (List.ofFn fun i : Fin n => p (Fin.castAdd n i),
              List.ofFn fun i : Fin n => p (Fin.natAdd n i))).2) ≤
        C * (T + 1) * (Nat.log 2 (n + T + 2) + 1) := by
  classical
  obtain ⟨k, State, hfin, tm, htm⟩ := hf
  obtain ⟨C, hC⟩ := exists_synthesis_outCap_le_mul_log (m := 4) tm
  refine ⟨4 * C + 4, fun n T hT => ?_⟩
  have hsyn := hC (2 * n + 1 + n) T
  let outFn (w : BitString (2 * n + 1 + n)) : OutCap 4 :=
    OutCap.ofList 4 (tm.runFrom (tm.initCfg (List.ofFn w)) T).output
  have hcomp1 : complexity interpretation (single fun w => (outFn w).bits ⟨1, by omega⟩) ≤
      C * (T + 1) * (Nat.log 2 (2 * n + 1 + n + T + 2) + 1) :=
    (hsyn.mono Set.Subset.rfl
      (Set.singleton_subset_iff.2 (Or.inr ⟨⟨1, by omega⟩, rfl⟩)) le_rfl).complexity_le
  have hcomp2 : complexity interpretation (single fun w => (outFn w).bits ⟨3, by omega⟩) ≤
      C * (T + 1) * (Nat.log 2 (2 * n + 1 + n + T + 2) + 1) :=
    (hsyn.mono Set.Subset.rfl
      (Set.singleton_subset_iff.2 (Or.inr ⟨⟨3, by omega⟩, rfl⟩)) le_rfl).complexity_le
  have hlog : Nat.log 2 (2 * n + 1 + n + T + 2) + 1 ≤ 3 * (Nat.log 2 (n + T + 2) + 1) := by
    have h1 : 2 * n + 1 + n + T + 2 ≤ 4 * (n + T + 2) := by omega
    have h2 : Nat.log 2 (2 * n + 1 + n + T + 2) ≤ Nat.log 2 (4 * (n + T + 2)) :=
      Nat.log_mono_right h1
    have h3 : Nat.log 2 (4 * (n + T + 2)) = Nat.log 2 (n + T + 2) + 2 := by
      rw [show 4 * (n + T + 2) = (n + T + 2) * 2 * 2 by ring,
        Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega)]
    omega
  have hout_eq (p : BitString (n + n)) :
      (tm.runFrom (tm.initCfg (List.ofFn (substitute (frameWiring n n) p))) T).output =
        [true, (f (List.ofFn fun i : Fin n => p (Fin.castAdd n i),
                   List.ofFn fun i : Fin n => p (Fin.natAdd n i))).1,
         false, (f (List.ofFn fun i : Fin n => p (Fin.castAdd n i),
                    List.ofFn fun i : Fin n => p (Fin.natAdd n i))).2] := by
    let x : BitString n := fun i => p (Fin.castAdd n i)
    let y : BitString n := fun i => p (Fin.natAdd n i)
    have hp : Fin.append x y = p := by
      funext j
      refine Fin.addCases (fun i => by simp [x]) (fun i => by rw [Fin.append_right]) j
    have hfw : List.ofFn (substitute (frameWiring n n) p) =
        encPair encBits encBits (List.ofFn x, List.ofFn y) := by
      rw [← hp, ofFn_substitute_frameWiring, encPair_apply, encBits_apply, encBits_apply]
    rw [hfw]
    have hrun := (htm (List.ofFn x, List.ofFn y)).runFrom_of_le
      (hT _ _ List.length_ofFn List.length_ofFn)
    rw [hrun.2]
    rfl
  have hf1 : (fun p : BitString (n + n) =>
      (f (List.ofFn fun i : Fin n => p (Fin.castAdd n i),
          List.ofFn fun i : Fin n => p (Fin.natAdd n i))).1) =
      fun p => (outFn (substitute (frameWiring n n) p)).bits ⟨1, by omega⟩ := by
    funext p; dsimp only [outFn]; rw [OutCap.ofList_bits, hout_eq p]; rfl
  have hf2 : (fun p : BitString (n + n) =>
      (f (List.ofFn fun i : Fin n => p (Fin.castAdd n i),
          List.ofFn fun i : Fin n => p (Fin.natAdd n i))).2) =
      fun p => (outFn (substitute (frameWiring n n) p)).bits ⟨3, by omega⟩ := by
    funext p; dsimp only [outFn]; rw [OutCap.ofList_bits, hout_eq p]; rfl
  have hpos : 1 ≤ (T + 1) * (Nat.log 2 (n + T + 2) + 1) :=
    Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  constructor
  · rw [hf1]
    have hsub := complexity_substitute_le (frameWiring n n) (fun w => (outFn w).bits ⟨1, by omega⟩)
    nlinarith
  · rw [hf2]
    have hsub := complexity_substitute_le (frameWiring n n) (fun w => (outFn w).bits ⟨3, by omega⟩)
    nlinarith

end CslibFrontier.Computability.Circuit.Boolean
