/-
Copyright (c) 2026 FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ExistsReal
public import CslibFrontier.Computability.Complexity.Problems.RealArithmetic
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.CircuitCompilation
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.Defs
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.Hardness
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.Membership
import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.CircuitPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Logics.RealArithmetic.FormulaTokenDecoding
import CslibFrontier.Logics.RealArithmetic.FormulaWordValidation
import CslibFrontier.Logics.RealArithmetic.TermTokenDecoding
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Polynomial-Time Reduction `ETR ≤ₚ ARM(3)` and `∃ℝ`-Completeness

Polynomial-time certificate for `etrWordToARM3`, establishing the many-one reduction
`ETR ≤ₚ ARM(3)`, `∃ℝ`-hardness, and `∃ℝ`-completeness of `ARM(3)`.
-/

public section

namespace Cslib.Complexity

open Matrix Cslib.Logic.RealArithmetic Cslib.Complexity Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

/-! ### Helper Constructors for `encArithGateUnary` -/

private abbrev encGateTail4 : (ℕ × ℕ) ⊕ ℕ ↪ List Bool :=
  encSum (encPair encUnary encUnary) encUnary

private abbrev encGateTail3 : (ℕ × ℕ) ⊕ (ℕ × ℕ) ⊕ ℕ ↪ List Bool :=
  encSum (encPair encUnary encUnary) encGateTail4

private abbrev encGateTail2 : ℚ ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ) ⊕ ℕ ↪ List Bool :=
  encSum encRat encGateTail3

private theorem mkInput_polyTime {γ : Type} {enc : γ ↪ List Bool} {f : γ → ℕ}
    (hf : ComputableInPolyTime f enc encUnary) :
    ComputableInPolyTime (fun x ↦ ArithGate.input (f x)) enc encArithGateUnary :=
  ((sumInl encUnary encGateTail2).comp hf).of_enc_eq fun _ ↦ rfl

private theorem mkConst_polyTime {γ : Type} {enc : γ ↪ List Bool} {f : γ → ℚ}
    (hf : ComputableInPolyTime f enc encRat) :
    ComputableInPolyTime (fun x ↦ ArithGate.const (f x)) enc encArithGateUnary :=
  ((sumInr encUnary encGateTail2).comp ((sumInl encRat encGateTail3).comp hf)).of_enc_eq
    fun _ ↦ rfl

private theorem mkAdd_polyTime {γ : Type} {enc : γ ↪ List Bool} {f g : γ → ℕ}
    (hf : ComputableInPolyTime f enc encUnary) (hg : ComputableInPolyTime g enc encUnary) :
    ComputableInPolyTime (fun x ↦ ArithGate.add (f x) (g x)) enc encArithGateUnary :=
  ((sumInr encUnary encGateTail2).comp ((sumInr encRat encGateTail3).comp
    ((sumInl (encPair encUnary encUnary) encGateTail4).comp (hf.prod hg)))).of_enc_eq fun _ ↦ rfl

private theorem mkMul_polyTime {γ : Type} {enc : γ ↪ List Bool} {f g : γ → ℕ}
    (hf : ComputableInPolyTime f enc encUnary) (hg : ComputableInPolyTime g enc encUnary) :
    ComputableInPolyTime (fun x ↦ ArithGate.mul (f x) (g x)) enc encArithGateUnary :=
  ((sumInr encUnary encGateTail2).comp ((sumInr encRat encGateTail3).comp
    ((sumInr (encPair encUnary encUnary) encGateTail4).comp
      ((sumInl (encPair encUnary encUnary) encUnary).comp (hf.prod hg))))).of_enc_eq fun _ ↦ rfl

private theorem mkNeg_polyTime {γ : Type} {enc : γ ↪ List Bool} {f : γ → ℕ}
    (hf : ComputableInPolyTime f enc encUnary) :
    ComputableInPolyTime (fun x ↦ ArithGate.neg (f x)) enc encArithGateUnary :=
  ((sumInr encUnary encGateTail2).comp ((sumInr encRat encGateTail3).comp
    ((sumInr (encPair encUnary encUnary) encGateTail4).comp
      ((sumInr (encPair encUnary encUnary) encUnary).comp hf)))).of_enc_eq fun _ ↦ rfl

private theorem sumElimSnd' {γ α β δ : Type} {ea : α ↪ List Bool} {eb : β ↪ List Bool}
    {eg : γ ↪ List Bool} {ed : δ ↪ List Bool}
    {f : γ × α → δ} {g : γ × β → δ}
    (hf : ComputableInPolyTime f (encPair eg ea) ed)
    (hg : ComputableInPolyTime g (encPair eg eb) ed) :
    ComputableInPolyTime
      (fun p : γ × (α ⊕ β) ↦ p.2.elim (fun a ↦ f (p.1, a)) (fun b ↦ g (p.1, b)))
      (encPair eg (encSum ea eb)) ed :=
  sumElimSnd (left := fun x a ↦ f (x, a)) (right := fun x b ↦ g (x, b)) hf hg

private theorem length_encArithGateUnary_input (i : ℕ) :
    (encArithGateUnary (.input i)).length ≤ 6 * i + 12 := by
  have := length_encArithGateUnary_le (.input i) (B := i) (C := 0)
    (fun _ h ↦ by cases h; omega) (by simp) (by simp) (by simp)
  omega

private theorem length_encArithGateUnary_const (c : ℚ) :
    (encArithGateUnary (.const c)).length ≤ (encRat c).length + 12 := by
  have := length_encArithGateUnary_le (.const c) (B := 0) (C := (encRat c).length)
    (by simp) (by simp) (by simp) (fun _ h ↦ by cases h; omega)
  omega

private theorem length_encArithGateUnary_neg (a : ℕ) :
    (encArithGateUnary (.neg a)).length ≤ 6 * a + 24 := by
  have := length_encArithGateUnary_le (.neg a) (B := a) (C := 0)
    (by simp) (fun _ h ↦ by cases h; omega) (by simp) (by simp)
  omega

private theorem length_encArithGateUnary_add (l r : ℕ) :
    (encArithGateUnary (.add l r)).length ≤ 6 * max l r + 24 := by
  have := length_encArithGateUnary_le (.add l r) (B := max l r) (C := 0)
    (by simp) (by simp)
    (fun _ _ h ↦ by rcases h with h | h <;> cases h; exact ⟨le_max_left _ _, le_max_right _ _⟩)
    (by simp)
  omega

private theorem length_encArithGateUnary_mul (l r : ℕ) :
    (encArithGateUnary (.mul l r)).length ≤ 6 * max l r + 24 := by
  have := length_encArithGateUnary_le (.mul l r) (B := max l r) (C := 0)
    (by simp) (by simp)
    (fun _ _ h ↦ by rcases h with h | h <;> cases h; exact ⟨le_max_left _ _, le_max_right _ _⟩)
    (by simp)
  omega

private theorem compileTermTokens_length_ge (tts : List TermToken) (s : List ℕ)
    (gs : List ArithGate) : gs.length ≤ (tts.foldl compileTermTokenStep (s, gs)).2.length := by
  induction tts generalizing s gs with
  | nil => simp
  | cons t rt ih =>
    simp only [List.foldl_cons]
    have h1 : gs.length ≤ (compileTermTokenStep (s, gs) t).2.length := by
      have := (compileTermTokenStep_length (s, gs) t).1; dsimp at this ⊢; omega
    exact h1.trans (ih _ _)

/-! ### Stage 1: `compileTermTokens` in Polynomial Time -/

private theorem compileTermTokens_polyTime :
    ComputableInPolyTime (fun p : List TermToken × List ArithGate ↦ compileTermTokens p.1 p.2)
      (encPair (encList encTermToken) (encList encArithGateUnary))
      (encPair (encList encUnary) (encList encArithGateUnary)) := by
  let encS := encPair (encList encUnary) (encList encArithGateUnary)
  have hstep : ComputableInPolyTime
      (fun p : (List ℕ × List ArithGate) × TermToken ↦ compileTermTokenStep p.1 p.2)
      (encPair encS encTermToken) encS := by
    have hconst : ComputableInPolyTime
        (fun p : (List ℕ × List ArithGate) × ℤ ↦
          ((p.1.2.length :: p.1.1), p.1.2 ++ [ArithGate.const (p.2 : ℚ)]))
        (encPair encS encIntBin) encS := by
      have hg := (snd (encList encUnary) (encList encArithGateUnary)).comp (fst encS encIntBin)
      have hs := (fst (encList encUnary) (encList encArithGateUnary)).comp (fst encS encIntBin)
      have hlen := (length_list encArithGateUnary).comp hg
      exact ((cons encUnary).comp (hlen.prod hs)).prod
        ((snoc encArithGateUnary).comp (hg.prod (mkConst_polyTime (rat_intCast.comp (snd encS _)))))
    have hvar : ComputableInPolyTime
        (fun p : (List ℕ × List ArithGate) × ℕ ↦
          ((p.1.2.length :: p.1.1), p.1.2 ++ [ArithGate.input p.2]))
        (encPair encS encUnary) encS := by
      have hg := (snd (encList encUnary) (encList encArithGateUnary)).comp (fst encS encUnary)
      have hs := (fst (encList encUnary) (encList encArithGateUnary)).comp (fst encS encUnary)
      have hlen := (length_list encArithGateUnary).comp hg
      exact ((cons encUnary).comp (hlen.prod hs)).prod
        ((snoc encArithGateUnary).comp (hg.prod (mkInput_polyTime (snd encS _))))
    have hadd : ComputableInPolyTime
        (fun p : (List ℕ × List ArithGate) × Unit ↦
          ((p.1.2.length :: p.1.1.tail.tail),
            p.1.2 ++ [ArithGate.add (p.1.1.headD 0) (p.1.1.tail.headD 0)]))
        (encPair encS encUnit) encS := by
      have hg := (snd (encList encUnary) (encList encArithGateUnary)).comp (fst encS encUnit)
      have hs := (fst (encList encUnary) (encList encArithGateUnary)).comp (fst encS encUnit)
      have hlen := (length_list encArithGateUnary).comp hg
      have htl := (listTail encUnary).comp hs
      exact ((cons encUnary).comp (hlen.prod ((listTail encUnary).comp htl))).prod
        ((snoc encArithGateUnary).comp
          (hg.prod (mkAdd_polyTime ((headD 0).comp hs) ((headD 0).comp htl))))
    have hmul : ComputableInPolyTime
        (fun p : (List ℕ × List ArithGate) × Unit ↦
          ((p.1.2.length :: p.1.1.tail.tail),
            p.1.2 ++ [ArithGate.mul (p.1.1.headD 0) (p.1.1.tail.headD 0)]))
        (encPair encS encUnit) encS := by
      have hg := (snd (encList encUnary) (encList encArithGateUnary)).comp (fst encS encUnit)
      have hs := (fst (encList encUnary) (encList encArithGateUnary)).comp (fst encS encUnit)
      have hlen := (length_list encArithGateUnary).comp hg
      have htl := (listTail encUnary).comp hs
      exact ((cons encUnary).comp (hlen.prod ((listTail encUnary).comp htl))).prod
        ((snoc encArithGateUnary).comp
          (hg.prod (mkMul_polyTime ((headD 0).comp hs) ((headD 0).comp htl))))
    exact (sumElimSnd' hconst (sumElimSnd' hvar (sumElimSnd' hadd hmul))).of_enc_eq fun p ↦ by
      rcases p with ⟨⟨s, g⟩, z | i | ⟨⟩ | ⟨⟩⟩ <;> rfl
  let encIn := encPair (encList encTermToken) (encList encArithGateUnary)
  have hrev := (listReverse encTermToken).comp
    (fst (encList encTermToken) (encList encArithGateUnary))
  have hinit : ComputableInPolyTime (fun p : List TermToken × List ArithGate ↦ ([], p.2))
      encIn encS := (const []).prod (snd _ _)
  let B : List TermToken × List ArithGate → ℕ := fun p ↦
    100 * ((encIn p).length + 1) ^ 2
  have hB : PolyBounded (fun p ↦ (encIn p).length) B :=
    PolyBounded.of_forall_le 100 2 fun _ ↦ le_rfl
  refine foldl' hrev hinit hstep hB fun p i hi ↦ ?_
  set L := (encIn p).length
  have hp1_le : (encList encTermToken p.1).length ≤ L := length_le_encPair_left _ _ p
  have hp2_le : (encList encArithGateUnary p.2).length ≤ L := length_le_encPair_right _ _ p
  have hlen1 : p.1.length ≤ L :=
    (SizedListEncoding.length_le encTermToken (encL := encList encTermToken) p.1).trans hp1_le
  have hlen2 : p.2.length ≤ L :=
    (SizedListEncoding.length_le encArithGateUnary (encL := encList encArithGateUnary) p.2).trans
      hp2_le
  have hgen : ∀ (ts : List TermToken), (∀ tok ∈ ts, tok ∈ p.1) →
      let st := ts.foldl compileTermTokenStep ([], p.2)
      st.2.length ≤ p.2.length + ts.length ∧
      st.1.length ≤ ts.length ∧
      (∀ g ∈ st.1, g ≤ p.2.length + ts.length) ∧
      (∀ g ∈ st.2, g ∈ p.2 ∨
        (encArithGateUnary g).length ≤ 6 * (p.2.length + ts.length) + 2 * L + 24) := by
    intro ts
    induction ts using List.reverseRecOn with
    | nil => intro _; exact ⟨by simp, by simp, fun _ h ↦ by simp at h, fun g hg ↦ Or.inl hg⟩
    | append_singleton ts tok ih =>
      intro hmem
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      obtain ⟨hg, hs, hsmem, hgmem⟩ := ih fun t ht ↦ hmem t (List.mem_append_left _ ht)
      set st := ts.foldl compileTermTokenStep ([], p.2)
      have htok_mem : tok ∈ p.1 := hmem tok (List.mem_append_right _ (List.mem_singleton.mpr rfl))
      have htok_enc : (encTermToken tok).length ≤ L :=
        (SizedListEncoding.length_elem_le (encA := encTermToken) (encL := encList encTermToken)
          p.1 tok htok_mem).trans hp1_le
      refine ⟨by rcases tok with z | idx | ⟨⟩ | ⟨⟩ <;> simp <;> omega,
        by rcases tok with z | idx | ⟨⟩ | ⟨⟩ <;>
          simp [List.length_tail] <;> omega, ?_, ?_⟩
      · intro g hgm
        rcases tok with z | idx | ⟨⟩ | ⟨⟩ <;>
          simp only [compileTermTokenStep_inl, compileTermTokenStep_var_raw,
            compileTermTokenStep_add_raw, compileTermTokenStep_mul_raw, List.mem_cons] at hgm
        · rcases hgm with rfl | hgm
          · simp; omega
          · exact (hsmem g hgm).trans (by simp)
        · rcases hgm with rfl | hgm
          · simp; omega
          · exact (hsmem g hgm).trans (by simp)
        · rcases hgm with rfl | hgm
          · simp; omega
          · exact (hsmem g (List.mem_of_mem_tail (List.mem_of_mem_tail hgm))).trans (by simp)
        · rcases hgm with rfl | hgm
          · simp; omega
          · exact (hsmem g (List.mem_of_mem_tail (List.mem_of_mem_tail hgm))).trans (by simp)
      · intro g hgm
        have hmem_new : g ∈ st.2 ∨
            (encArithGateUnary g).length ≤
              6 * (p.2.length + (ts ++ [tok]).length) + 2 * L + 24 := by
          rcases tok with z | idx | ⟨⟩ | ⟨⟩ <;>
            simp only [compileTermTokenStep_inl, compileTermTokenStep_var_raw,
              compileTermTokenStep_add_raw, compileTermTokenStep_mul_raw, List.mem_append,
                List.mem_singleton] at hgm
          · rcases hgm with hgm | rfl
            · exact Or.inl hgm
            · right
              have hz : (encRat (z : ℚ)).length ≤ 2 * L + 10 := by
                have hz' : (encIntBin z).length ≤ L := by
                  have h1 : (encIntBin z).length ≤ (encTermToken (.inl z)).length := by
                    simp [encTermToken]
                  exact h1.trans htok_enc
                rw [length_encRat, length_encIntBin] at *
                simp only [Rat.num_intCast, Rat.den_intCast, Nat.size_one]
                omega
              have := length_encArithGateUnary_le (.const (z : ℚ))
                (B := p.2.length + (ts.length + 1)) (C := 2 * L + 10)
                (by simp) (by simp) (by simp) (fun c hc ↦ by cases hc; exact hz)
              simp only [List.length_append, List.length_singleton]; omega
          · rcases hgm with hgm | rfl
            · exact Or.inl hgm
            · right
              have hidx : idx ≤ L := by
                have h1 : idx ≤ (encTermToken (.inr (.inl idx))).length := by
                  simp [encTermToken]; omega
                exact h1.trans htok_enc
              have hle : (encArithGateUnary (.input idx)).length ≤ idx + 1 := by
                rw [encArithGateUnary_length_input]
              omega
          · rcases hgm with hgm | rfl
            · exact Or.inl hgm
            · right
              have h1 : st.1.headD 0 ≤ p.2.length + ts.length := by
                cases hs_eq : st.1 with
                | nil => simp
                | cons a _ => exact hsmem a (by simp [hs_eq])
              have h2 : st.1.tail.headD 0 ≤ p.2.length + ts.length := by
                cases hs_eq : st.1 with
                | nil => simp
                | cons _ t =>
                  cases ht_eq : t with
                  | nil => simp
                  | cons b _ => exact hsmem b (by simp [hs_eq, ht_eq])
              have := length_encArithGateUnary_le (.add (st.1.headD 0) (st.1.tail.headD 0))
                (B := p.2.length + (ts.length + 1)) (C := 2 * L)
                (by simp) (by simp)
                (fun l r h ↦ by rcases h with h | h <;> cases h; constructor <;> omega) (by simp)
              simp only [List.length_append, List.length_singleton]; omega
          · rcases hgm with hgm | rfl
            · exact Or.inl hgm
            · right
              have h1 : st.1.headD 0 ≤ p.2.length + ts.length := by
                cases hs_eq : st.1 with
                | nil => simp
                | cons a _ => exact hsmem a (by simp [hs_eq])
              have h2 : st.1.tail.headD 0 ≤ p.2.length + ts.length := by
                cases hs_eq : st.1 with
                | nil => simp
                | cons _ t =>
                  cases ht_eq : t with
                  | nil => simp
                  | cons b _ => exact hsmem b (by simp [hs_eq, ht_eq])
              have := length_encArithGateUnary_le (.mul (st.1.headD 0) (st.1.tail.headD 0))
                (B := p.2.length + (ts.length + 1)) (C := 2 * L)
                (by simp) (by simp)
                (fun l r h ↦ by rcases h with h | h <;> cases h; constructor <;> omega) (by simp)
              simp only [List.length_append, List.length_singleton]; omega
        rcases hmem_new with hgm | hle
        · rcases hgmem g hgm with hgp2 | hle
          · exact Or.inl hgp2
          · exact Or.inr (hle.trans (by simp))
        · exact Or.inr hle
  obtain ⟨hg_len, hs_len, hs_val, hg_enc⟩ :=
    hgen (p.1.reverse.take i) (fun tok htok ↦ List.mem_reverse.mp (List.mem_of_mem_take htok))
  have hilen : (p.1.reverse.take i).length ≤ L := by
    simp only [List.length_take, List.length_reverse]
    exact (Nat.min_le_right _ _).trans hlen1
  rw [length_encPair]
  have h1 : (encList encUnary ((p.1.reverse.take i).foldl compileTermTokenStep ([],
    p.2)).1).length ≤
      L * (2 * (2 * L) + 1) := by
    have hle := length_encList_le encUnary
      ((p.1.reverse.take i).foldl compileTermTokenStep ([], p.2)).1 (b := 2 * L) fun g hg ↦ by
        simp only [encUnary_apply, List.length_replicate]
        have := hs_val g hg; omega
    exact hle.trans (Nat.mul_le_mul_right _ (by omega))
  have h2 : (encList encArithGateUnary
      ((p.1.reverse.take i).foldl compileTermTokenStep ([], p.2)).2).length ≤
      2 * L * (2 * (14 * L + 24) + 1) := by
    have hle := length_encList_le encArithGateUnary
      ((p.1.reverse.take i).foldl compileTermTokenStep ([], p.2)).2 (b := 14 * L + 24) fun g hg ↦ by
        rcases hg_enc g hg with hgp2 | hle
        · have := (SizedListEncoding.length_elem_le (encA := encArithGateUnary)
            (encL := encList encArithGateUnary) p.2 g hgp2).trans hp2_le
          omega
        · omega
    exact hle.trans (Nat.mul_le_mul_right _ (by omega))
  dsimp [B]
  nlinarith

/-! ### Stage 2: `compileFormulaTokenStep` and `etrWordToRawCircuit` in Polynomial Time -/

private abbrev encFormulaState : FormulaCompileState ↪ List Bool :=
  encPair (encList encUnary)
    (encPair (encList encUnary) (encPair (encList encArithGateUnary) encUnary))

private theorem eqZeroGateBlock_polyTime :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ ↦ eqZeroGateBlock p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encUnary) (encList encArithGateUnary) := by
  let encIn := encPair (encPair encUnary encUnary) encUnary
  have hk := (fst encUnary encUnary).comp (fst (encPair encUnary encUnary) encUnary)
  have hgt := (snd encUnary encUnary).comp (fst (encPair encUnary encUnary) encUnary)
  have hsl := snd (encPair encUnary encUnary) encUnary
  have haddK (c : ℕ) := unary_add.comp (hk.prod (const c))
  have c0 := mkInput_polyTime hsl
  have c1 := mkInput_polyTime (unary_add.comp (hsl.prod (const 1)))
  have c2 := mkConst_polyTime (enc := encIn) (const (α := (ℕ × ℕ) × ℕ) (1 : ℚ))
  have c3 := mkNeg_polyTime hk
  have c4 := mkAdd_polyTime (haddK 2) (haddK 3)
  have c5 := mkMul_polyTime hk (haddK 4)
  have c6 := mkMul_polyTime hk hgt
  have c7 := mkMul_polyTime hgt (haddK 1)
  have c8 := mkNeg_polyTime (haddK 2)
  have c9 := mkAdd_polyTime (haddK 7) (haddK 8)
  have c10 := mkMul_polyTime (haddK 4) (haddK 9)
  have h10 : ComputableInPolyTime _ encIn (encList encArithGateUnary) :=
    (cons encArithGateUnary).comp (c10.prod (const (α := (ℕ × ℕ) × ℕ) ([] : List ArithGate)))
  have h9 := (cons encArithGateUnary).comp (c9.prod h10)
  have h8 := (cons encArithGateUnary).comp (c8.prod h9)
  have h7 := (cons encArithGateUnary).comp (c7.prod h8)
  have h6 := (cons encArithGateUnary).comp (c6.prod h7)
  have h5 := (cons encArithGateUnary).comp (c5.prod h6)
  have h4 := (cons encArithGateUnary).comp (c4.prod h5)
  have h3 := (cons encArithGateUnary).comp (c3.prod h4)
  have h2 := (cons encArithGateUnary).comp (c2.prod h3)
  have h1 := (cons encArithGateUnary).comp (c1.prod h2)
  exact (cons encArithGateUnary).comp (c0.prod h1)

private theorem ltZeroGateBlock_polyTime :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ ↦ ltZeroGateBlock p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encUnary) (encList encArithGateUnary) := by
  let encIn := encPair (encPair encUnary encUnary) encUnary
  have hk := (fst encUnary encUnary).comp (fst (encPair encUnary encUnary) encUnary)
  have hgt := (snd encUnary encUnary).comp (fst (encPair encUnary encUnary) encUnary)
  have hsl := snd (encPair encUnary encUnary) encUnary
  have haddK (c : ℕ) := unary_add.comp (hk.prod (const c))
  have haddS (c : ℕ) := unary_add.comp (hsl.prod (const c))
  have c0 := mkInput_polyTime hsl
  have c1 := mkInput_polyTime (haddS 1)
  have c2 := mkInput_polyTime (haddS 2)
  have c3 := mkInput_polyTime (haddS 3)
  have c4 := mkConst_polyTime (enc := encIn) (const (α := (ℕ × ℕ) × ℕ) (1 : ℚ))
  have c5 := mkNeg_polyTime hk
  have c6 := mkAdd_polyTime (haddK 4) (haddK 5)
  have c7 := mkMul_polyTime hk (haddK 6)
  have c8 := mkMul_polyTime (haddK 1) (haddK 1)
  have c9 := mkAdd_polyTime hgt (haddK 8)
  have c10 := mkMul_polyTime hk (haddK 9)
  have c11 := mkMul_polyTime (haddK 1) (haddK 2)
  have c12 := mkNeg_polyTime (haddK 4)
  have c13 := mkAdd_polyTime (haddK 11) (haddK 12)
  have c14 := mkMul_polyTime hk (haddK 13)
  have c15 := mkMul_polyTime (haddK 3) (haddK 3)
  have c16 := mkNeg_polyTime (haddK 15)
  have c17 := mkAdd_polyTime hgt (haddK 16)
  have c18 := mkMul_polyTime (haddK 6) (haddK 17)
  have h18 : ComputableInPolyTime _ encIn (encList encArithGateUnary) :=
    (cons encArithGateUnary).comp (c18.prod (const (α := (ℕ × ℕ) × ℕ) ([] : List ArithGate)))
  have h17 := (cons encArithGateUnary).comp (c17.prod h18)
  have h16 := (cons encArithGateUnary).comp (c16.prod h17)
  have h15 := (cons encArithGateUnary).comp (c15.prod h16)
  have h14 := (cons encArithGateUnary).comp (c14.prod h15)
  have h13 := (cons encArithGateUnary).comp (c13.prod h14)
  have h12 := (cons encArithGateUnary).comp (c12.prod h13)
  have h11 := (cons encArithGateUnary).comp (c11.prod h12)
  have h10 := (cons encArithGateUnary).comp (c10.prod h11)
  have h9 := (cons encArithGateUnary).comp (c9.prod h10)
  have h8 := (cons encArithGateUnary).comp (c8.prod h9)
  have h7 := (cons encArithGateUnary).comp (c7.prod h8)
  have h6 := (cons encArithGateUnary).comp (c6.prod h7)
  have h5 := (cons encArithGateUnary).comp (c5.prod h6)
  have h4 := (cons encArithGateUnary).comp (c4.prod h5)
  have h3 := (cons encArithGateUnary).comp (c3.prod h4)
  have h2 := (cons encArithGateUnary).comp (c2.prod h3)
  have h1 := (cons encArithGateUnary).comp (c1.prod h2)
  exact (cons encArithGateUnary).comp (c0.prod h1)

private theorem compileFormulaTokenStep_polyTime :
    ComputableInPolyTime (fun p : FormulaCompileState × FormulaToken ↦
      compileFormulaTokenStep p.1 p.2)
      (encPair encFormulaState encFormulaToken) encFormulaState := by
  let encSt := encFormulaState
  have hFalse : ComputableInPolyTime
      (fun p : FormulaCompileState × Unit ↦
        (p.1.2.2.1.length :: p.1.1, p.1.2.1, p.1.2.2.1 ++ [.const 0], p.1.2.2.2))
      (encPair encSt encUnit) encSt := by
    have hst := fst encSt encUnit
    have hstk := (fst _ _).comp hst
    have hzs := (fst _ _).comp ((snd _ _).comp hst)
    have hgs := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp hst))
    have hsl := (snd _ _).comp ((snd _ _).comp ((snd _ _).comp hst))
    have hlen := (length_list encArithGateUnary).comp hgs
    exact ((cons encUnary).comp (hlen.prod hstk)).prod
      (hzs.prod (((snoc encArithGateUnary).comp
        (hgs.prod (const (α := FormulaCompileState × Unit) (ArithGate.const 0)))).prod hsl))
  have hEqZero : ComputableInPolyTime
      (fun p : FormulaCompileState × List Bool ↦
        let ts := (termTokensDecoder.decode p.2).getD []
        let res := compileTermTokens ts p.1.2.2.1
        let gt := res.1.headD 0
        let gates₁ := res.2
        let k := gates₁.length
        (k :: p.1.1, (k + 5) :: (k + 6) :: (k + 10) :: p.1.2.1,
          gates₁ ++ eqZeroGateBlock k gt p.1.2.2.2, p.1.2.2.2 + 2))
      (encPair encSt encBits) encSt := by
    have hst := fst encSt encBits
    have hstk := (fst _ _).comp hst
    have hzs := (fst _ _).comp ((snd _ _).comp hst)
    have hgs := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp hst))
    have hsl := (snd _ _).comp ((snd _ _).comp ((snd _ _).comp hst))
    have hts := optionGetDWithInput (termTokensDecoder.computable.comp (snd encSt encBits))
      (const [])
    have hres := compileTermTokens_polyTime.comp (hts.prod hgs)
    have hgt := (headD (encA := encUnary) 0).comp ((fst _ _).comp hres)
    have hg1 := (snd _ _).comp hres
    have hk := (length_list encArithGateUnary).comp hg1
    have haddK (c : ℕ) := unary_add.comp (hk.prod (const c))
    have hnew := eqZeroGateBlock_polyTime.comp ((hk.prod hgt).prod hsl)
    exact ((cons encUnary).comp (hk.prod hstk)).prod
      ((((cons encUnary).comp ((haddK 5).prod
        ((cons encUnary).comp ((haddK 6).prod
          ((cons encUnary).comp ((haddK 10).prod hzs)))))).prod
        (((listAppend encArithGateUnary).comp (hg1.prod hnew)).prod
          (unary_add.comp (hsl.prod (const 2))))))
  have hLtZero : ComputableInPolyTime
      (fun p : FormulaCompileState × List Bool ↦
        let ts := (termTokensDecoder.decode p.2).getD []
        let res := compileTermTokens ts p.1.2.2.1
        let gt := res.1.headD 0
        let gates₁ := res.2
        let k := gates₁.length
        (k :: p.1.1, (k + 7) :: (k + 10) :: (k + 14) :: (k + 18) :: p.1.2.1,
          gates₁ ++ ltZeroGateBlock k gt p.1.2.2.2, p.1.2.2.2 + 4))
      (encPair encSt encBits) encSt := by
    have hst := fst encSt encBits
    have hstk := (fst _ _).comp hst
    have hzs := (fst _ _).comp ((snd _ _).comp hst)
    have hgs := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp hst))
    have hsl := (snd _ _).comp ((snd _ _).comp ((snd _ _).comp hst))
    have hts := optionGetDWithInput (termTokensDecoder.computable.comp (snd encSt encBits))
      (const [])
    have hres := compileTermTokens_polyTime.comp (hts.prod hgs)
    have hgt := (headD (encA := encUnary) 0).comp ((fst _ _).comp hres)
    have hg1 := (snd _ _).comp hres
    have hk := (length_list encArithGateUnary).comp hg1
    have haddK (c : ℕ) := unary_add.comp (hk.prod (const c))
    have hnew := ltZeroGateBlock_polyTime.comp ((hk.prod hgt).prod hsl)
    exact ((cons encUnary).comp (hk.prod hstk)).prod
      ((((cons encUnary).comp ((haddK 7).prod
        ((cons encUnary).comp ((haddK 10).prod
          ((cons encUnary).comp ((haddK 14).prod
            ((cons encUnary).comp ((haddK 18).prod hzs)))))))).prod
        (((listAppend encArithGateUnary).comp (hg1.prod hnew)).prod
          (unary_add.comp (hsl.prod (const 4))))))
  have hNot : ComputableInPolyTime
      (fun p : FormulaCompileState × Unit ↦
        let bp := p.1.1.headD 0
        let k := p.1.2.2.1.length
        ((k + 2) :: p.1.1.tail, p.1.2.1, p.1.2.2.1 ++ [.const 1, .neg bp, .add k (k + 1)],
          p.1.2.2.2))
      (encPair encSt encUnit) encSt := by
    have hst := fst encSt encUnit
    have hstk := (fst _ _).comp hst
    have hzs := (fst _ _).comp ((snd _ _).comp hst)
    have hgs := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp hst))
    have hsl := (snd _ _).comp ((snd _ _).comp ((snd _ _).comp hst))
    have hk := (length_list encArithGateUnary).comp hgs
    have hbp := (headD (encA := encUnary) 0).comp hstk
    have hnew := (cons encArithGateUnary).comp
      ((mkConst_polyTime (const (α := FormulaCompileState × Unit) (1 : ℚ))).prod
        ((cons encArithGateUnary).comp ((mkNeg_polyTime hbp).prod
          ((cons encArithGateUnary).comp
            ((mkAdd_polyTime hk (unary_add.comp (hk.prod (const 1)))).prod (const []))))))
    exact ((cons encUnary).comp ((unary_add.comp (hk.prod (const 2))).prod
      ((listTail encUnary).comp hstk))).prod
      (hzs.prod (((listAppend encArithGateUnary).comp (hgs.prod hnew)).prod hsl))
  have hAnd : ComputableInPolyTime
      (fun p : FormulaCompileState × Unit ↦
        let bp := p.1.1.headD 0
        let bq := p.1.1.tail.headD 0
        let k := p.1.2.2.1.length
        (k :: p.1.1.tail.tail, p.1.2.1, p.1.2.2.1 ++ [.mul bp bq], p.1.2.2.2))
      (encPair encSt encUnit) encSt := by
    have hst := fst encSt encUnit
    have hstk := (fst _ _).comp hst
    have hzs := (fst _ _).comp ((snd _ _).comp hst)
    have hgs := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp hst))
    have hsl := (snd _ _).comp ((snd _ _).comp ((snd _ _).comp hst))
    have hk := (length_list encArithGateUnary).comp hgs
    have htl := (listTail encUnary).comp hstk
    exact ((cons encUnary).comp (hk.prod ((listTail encUnary).comp htl))).prod
      (hzs.prod (((snoc encArithGateUnary).comp
        (hgs.prod (mkMul_polyTime ((headD (encA := encUnary) 0).comp hstk)
          ((headD (encA := encUnary) 0).comp htl)))).prod hsl))
  have hOr : ComputableInPolyTime
      (fun p : FormulaCompileState × Unit ↦
        let bp := p.1.1.headD 0
        let bq := p.1.1.tail.headD 0
        let k := p.1.2.2.1.length
        ((k + 3) :: p.1.1.tail.tail, p.1.2.1,
          p.1.2.2.1 ++ [.add bp bq, .mul bp bq, .neg (k + 1), .add k (k + 2)], p.1.2.2.2))
      (encPair encSt encUnit) encSt := by
    have hst := fst encSt encUnit
    have hstk := (fst _ _).comp hst
    have hzs := (fst _ _).comp ((snd _ _).comp hst)
    have hgs := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp hst))
    have hsl := (snd _ _).comp ((snd _ _).comp ((snd _ _).comp hst))
    have hk := (length_list encArithGateUnary).comp hgs
    have htl := (listTail encUnary).comp hstk
    have hbp := (headD (encA := encUnary) 0).comp hstk
    have hbq := (headD (encA := encUnary) 0).comp htl
    have hnew := (cons encArithGateUnary).comp ((mkAdd_polyTime hbp hbq).prod
      ((cons encArithGateUnary).comp ((mkMul_polyTime hbp hbq).prod
        ((cons encArithGateUnary).comp
          ((mkNeg_polyTime (unary_add.comp (hk.prod (const 1)))).prod
            ((cons encArithGateUnary).comp
              ((mkAdd_polyTime hk (unary_add.comp (hk.prod (const 2)))).prod (const []))))))))
    exact ((cons encUnary).comp ((unary_add.comp (hk.prod (const 3))).prod
      ((listTail encUnary).comp htl))).prod
      (hzs.prod (((listAppend encArithGateUnary).comp (hgs.prod hnew)).prod hsl))
  exact (sumElimSnd' hFalse (sumElimSnd' hEqZero (sumElimSnd' hLtZero
    (sumElimSnd' hNot (sumElimSnd' hAnd hOr))))).of_enc_eq fun p ↦ by
      rcases p with ⟨st, ⟨⟩ | w | w | ⟨⟩ | ⟨⟩ | ⟨⟩⟩ <;> rfl

/-- Structural invariants of `compileFormulaTokenStep` folds for `formulaFold_size_bound`. -/
private theorem formulaFold_invariants (word : List Bool) (ts : List FormulaToken)
    (hmem : ∀ tok ∈ ts, tok ∈ formulaWordTokens word) :
    let L := word.length + 1
    let st := ts.foldl compileFormulaTokenStep ([], [], [], word.length)
    st.1.length ≤ ts.length ∧
    st.2.1.length ≤ 4 * ts.length ∧
    st.2.2.1.length ≤ ts.length * (L + 20) ∧
    st.2.2.2 ≤ word.length + 4 * ts.length ∧
    (∀ g ∈ st.1, g ≤ st.2.2.1.length) ∧
    (∀ g ∈ st.2.1, g ≤ st.2.2.1.length) ∧
    (∀ g ∈ st.2.2.1, (encArithGateUnary g).length ≤
      6 * (st.2.2.1.length + st.2.2.2) + 2 * L + 24) := by
  intro L
  have htok_term_le : ∀ tok ∈ formulaWordTokens word, ∀ tw,
      (tok = .inr (.inl tw) ∨ tok = .inr (.inr (.inl tw))) → tw.length ≤ word.length := by
    intro tok htok tw htw
    by_cases hv : validFormulaWord word = true
    · have hdec := formulaTokensDecoder_decode_encFormula (Formula.ofWord word)
      rw [encFormula_ofWord, normalizeFormulaWord, ite_eq_left hv, ← formulaWordTokens_eq] at hdec
      rcases htw with rfl | rfl
      · exact (formulaTermWord_length_lt_of_decode hdec (Or.inl htok)).le
      · exact (formulaTermWord_length_lt_of_decode hdec (Or.inr htok)).le
    · rw [formulaWordTokens_eq, Formula.ofWord_of_not_valid hv] at htok
      simp only [encFormula_tokens, List.map_singleton, List.mem_singleton,
        FormulaToken.encodeTerms, Sum.map_inl, id_eq] at htok
      subst htok
      rcases htw with h | h <;> cases h
  revert hmem
  induction ts using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨by simp, by simp, by simp, by simp, fun _ h ↦ by simp at h,
      fun _ h ↦ by simp at h, fun _ h ↦ by simp at h⟩
  | append_singleton ts tok ih =>
    intro hmem
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs, hz, hg, hsl, hsm, hzm, hgenc⟩ := ih fun t ht ↦ hmem t (List.mem_append_left _ ht)
    set st := ts.foldl compileFormulaTokenStep ([], [], [], word.length)
    have htok_mem := hmem tok (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    have hterm_inv : ∀ (tw : List Bool),
        (tok = .inr (.inl tw) ∨ tok = .inr (.inr (.inl tw))) →
        let tts := (termTokensDecoder.decode tw).getD []
        let res := compileTermTokens tts st.2.2.1
        res.2.length ≤ st.2.2.1.length + word.length ∧
        (res.1.headD 0) ≤ res.2.length ∧
        (∀ g ∈ res.2, g ∈ st.2.2.1 ∨
          (encArithGateUnary g).length ≤ 6 * res.2.length + 2 * L + 24) := by
        intro tw htw
        have htw_le : tw.length ≤ word.length := htok_term_le tok htok_mem tw htw
        have htts_le : ((termTokensDecoder.decode tw).getD []).length ≤ word.length := by
          cases hd : termTokensDecoder.decode tw with
          | none => simp
          | some tts =>
            have h1 := SizedListEncoding.length_le encTermToken (encL := encList encTermToken) tts
            rw [(termTokensDecoder.decode_eq_some_iff _ _).mp hd] at h1
            exact h1.trans htw_le
        have hfold_gen : ∀ (r : List TermToken),
            (∀ tt ∈ r, tt ∈ (termTokensDecoder.decode tw).getD []) →
            let res := r.foldl compileTermTokenStep ([], st.2.2.1)
            res.2.length = st.2.2.1.length + r.length ∧
            (∀ a ∈ res.1, a ≤ res.2.length) ∧
            (∀ g ∈ res.2, g ∈ st.2.2.1 ∨
              (encArithGateUnary g).length ≤ 6 * res.2.length + 2 * L + 24) := by
          intro r
          induction r using List.reverseRecOn with
          | nil => intro _; exact ⟨by simp, fun _ h ↦ by simp at h, fun g hg ↦ Or.inl hg⟩
          | append_singleton r tt ih' =>
            intro hr
            rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
            obtain ⟨hlen', hs', hg'⟩ := ih' fun x hx ↦ hr x (List.mem_append_left _ hx)
            set res' := r.foldl compileTermTokenStep ([], st.2.2.1)
            have htt_mem := hr tt (List.mem_append_right _ (List.mem_singleton.mpr rfl))
            have htt_enc : (encTermToken tt).length ≤ word.length := by
              cases hd : termTokensDecoder.decode tw with
              | none => simp [hd] at htt_mem
              | some tts =>
                simp only [hd, Option.getD_some] at htt_mem
                have h1 := SizedListEncoding.length_elem_le (encA := encTermToken)
                  (encL := encList encTermToken) tts tt htt_mem
                rw [(termTokensDecoder.decode_eq_some_iff _ _).mp hd] at h1
                exact h1.trans htw_le
            have hnewlen : (compileTermTokenStep res' tt).2.length = res'.2.length + 1 :=
              (compileTermTokenStep_length res' tt).1
            refine ⟨by simp [hnewlen, hlen']; omega, ?_, ?_⟩
            · intro a ha
              rw [hnewlen]
              rcases tt with z | idx | ⟨⟩ | ⟨⟩ <;>
                simp only [compileTermTokenStep_inl, compileTermTokenStep_var_raw,
                  compileTermTokenStep_add_raw, compileTermTokenStep_mul_raw, List.mem_cons] at ha
              · rcases ha with rfl | ha
                · omega
                · exact (hs' a ha).trans (by omega)
              · rcases ha with rfl | ha
                · omega
                · exact (hs' a ha).trans (by omega)
              · rcases ha with rfl | ha
                · omega
                · exact (hs' a (List.mem_of_mem_tail (List.mem_of_mem_tail ha))).trans (by omega)
              · rcases ha with rfl | ha
                · omega
                · exact (hs' a (List.mem_of_mem_tail (List.mem_of_mem_tail ha))).trans (by omega)
            · intro g hgm
              rw [hnewlen]
              have hcase : g ∈ res'.2 ∨
                  (encArithGateUnary g).length ≤ 6 * (res'.2.length + 1) + 2 * L + 24 := by
                rcases tt with z | idx | ⟨⟩ | ⟨⟩ <;>
                  simp only [compileTermTokenStep_inl, compileTermTokenStep_var_raw,
                    compileTermTokenStep_add_raw, compileTermTokenStep_mul_raw, List.mem_append,
                      List.mem_singleton] at hgm
                · rcases hgm with hgm | rfl
                  · exact Or.inl hgm
                  · right
                    have hz' : (encRat (z : ℚ)).length ≤ 2 * L + 10 := by
                      have h1 : (encIntBin z).length ≤ word.length :=
                        (by simp [encTermToken] : (encIntBin z).length ≤
                          (encTermToken (.inl z)).length).trans htt_enc
                      rw [length_encRat, length_encIntBin] at *
                      simp only [Rat.num_intCast, Rat.den_intCast, Nat.size_one]; omega
                    have := length_encArithGateUnary_le (.const (z : ℚ))
                      (B := res'.2.length + 1) (C := 2 * L + 10) (by simp) (by simp) (by simp)
                      (fun c hc ↦ by cases hc; exact hz')
                    omega
                · rcases hgm with hgm | rfl
                  · exact Or.inl hgm
                  · right
                    have hidx : idx ≤ word.length :=
                      (by simp [encTermToken]; omega : idx ≤
                        (encTermToken (.inr (.inl idx))).length).trans htt_enc
                    have : (encArithGateUnary (.input idx)).length ≤ idx + 1 := by
                      rw [encArithGateUnary_length_input]
                    omega
                · rcases hgm with hgm | rfl
                  · exact Or.inl hgm
                  · right
                    have h1 : res'.1.headD 0 ≤ res'.2.length := by
                      cases h : res'.1 with | nil => simp | cons a _ => exact hs' a (by simp [h])
                    have h2 : res'.1.tail.headD 0 ≤ res'.2.length := by
                      cases h : res'.1 with
                      | nil => simp
                      | cons _ t =>
                        cases ht : t with
                        | nil => simp
                        | cons b _ => exact hs' b (by simp [h, ht])
                    have := length_encArithGateUnary_le
                      (.add (res'.1.headD 0) (res'.1.tail.headD 0))
                      (B := res'.2.length + 1) (C := 2 * L) (by simp) (by simp)
                      (fun l r h ↦ by rcases h with h | h <;> cases h; constructor <;> omega)
                      (by simp)
                    omega
                · rcases hgm with hgm | rfl
                  · exact Or.inl hgm
                  · right
                    have h1 : res'.1.headD 0 ≤ res'.2.length := by
                      cases h : res'.1 with | nil => simp | cons a _ => exact hs' a (by simp [h])
                    have h2 : res'.1.tail.headD 0 ≤ res'.2.length := by
                      cases h : res'.1 with
                      | nil => simp
                      | cons _ t =>
                        cases ht : t with
                        | nil => simp
                        | cons b _ => exact hs' b (by simp [h, ht])
                    have := length_encArithGateUnary_le
                      (.mul (res'.1.headD 0) (res'.1.tail.headD 0))
                      (B := res'.2.length + 1) (C := 2 * L) (by simp) (by simp)
                      (fun l r h ↦ by rcases h with h | h <;> cases h; constructor <;> omega)
                      (by simp)
                    omega
              rcases hcase with hgm | hle
              · rcases hg' g hgm with hgs | hle
                · exact Or.inl hgs
                · exact Or.inr (hle.trans (by omega))
              · exact Or.inr hle
        obtain ⟨hlen', hs', hg'⟩ := hfold_gen ((termTokensDecoder.decode tw).getD []).reverse
          (fun tt htt ↦ List.mem_reverse.mp htt)
        refine ⟨by rw [compileTermTokens_eq_foldl]; rw [hlen', List.length_reverse]; omega, ?_, hg'⟩
        cases h : (compileTermTokens ((termTokensDecoder.decode tw).getD []) st.2.2.1).1 with
        | nil => simp
        | cons a _ =>
          rw [compileTermTokens_eq_foldl] at h ⊢
          exact hs' a (by rw [h]; simp)
    have hconst1_len : (encRat (1 : ℚ)).length ≤ 10 := by
      rw [length_encRat]; simp [Nat.size]
    have hconst0_len : (encRat (0 : ℚ)).length ≤ 10 := by
      rw [length_encRat]; simp [Nat.size]
    rcases tok with ⟨⟩ | tw | tw | ⟨⟩ | ⟨⟩ | ⟨⟩
    · -- false
      refine ⟨by simp; omega,
        by simp; omega,
        by simp; nlinarith,
        by simp; omega, ?_, ?_, ?_⟩
      · intro g hgm
        simp only [compileFormulaTokenStep_inl,
            List.mem_cons,
              List.length_append,
          List.length_singleton] at hgm ⊢
        rcases hgm with rfl | hgm
        · omega
        · exact (hsm g hgm).trans (by omega)
      · intro g hgm; simp only [compileFormulaTokenStep_inl,
          List.length_append,
        List.length_singleton]
        exact (hzm g hgm).trans (by omega)
      · intro g hgm
        simp only [compileFormulaTokenStep_inl,
            List.mem_append,
              List.mem_singleton,
          List.length_append, List.length_singleton] at hgm ⊢
        rcases hgm with hgm | rfl
        · exact (hgenc g hgm).trans (by omega)
        · have := length_encArithGateUnary_le (.const 0) (B := st.2.2.1.length + 1 + st.2.2.2)
            (C := 10) (by simp) (by simp) (by simp) (fun c hc ↦ by cases hc; exact hconst0_len)
          omega
    · -- eqZero tw
      obtain ⟨hr_len, hgt_le, hr_enc⟩ := hterm_inv tw (Or.inl rfl)
      set res := compileTermTokens ((termTokensDecoder.decode tw).getD []) st.2.2.1
      have hpref : st.2.2.1.length ≤ res.2.length := compileTermTokens_length_ge _ _ _
      refine ⟨by simp; omega,
        by simp; omega,
        by simp only [compileFormulaTokenStep_eqZero_raw, eqZeroGateBlock_length,
          List.length_append,
            List.length_cons, List.length_nil]
           dsimp only [res] at hr_len
           have hwl : word.length ≤ L := by omega
           nlinarith,
        by simp; omega, ?_, ?_, ?_⟩
      · intro g hgm
        simp only [compileFormulaTokenStep_eqZero_raw,
            List.mem_cons,
              List.length_append] at hgm ⊢
        rcases hgm with rfl | hgm
        · omega
        · exact (hsm g hgm).trans (by dsimp only [res] at hpref; omega)
      · intro g hgm
        simp only [compileFormulaTokenStep_eqZero_raw,
            List.mem_cons,
              List.length_append] at hgm ⊢
        have hblen : (eqZeroGateBlock res.2.length (res.1.headD 0) st.2.2.2).length = 11 := rfl
        rcases hgm with rfl | rfl | rfl | hgm <;> try (dsimp only [res] at hblen ⊢; omega)
        exact (hzm g hgm).trans (by dsimp only [res] at hpref; omega)
      · intro g hgm
        simp only [compileFormulaTokenStep_eqZero_raw, eqZeroGateBlock_length,
          mem_eqZeroGateBlock_iff, List.mem_append,
          List.length_append] at hgm ⊢
        rcases hgm with hgm | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
        · rcases hr_enc g hgm with hgs | hle
          · exact (hgenc g hgs).trans (by dsimp only [res] at hpref; omega)
          · dsimp only [res] at hle; omega
        · have := length_encArithGateUnary_input st.2.2.2; omega
        · have := length_encArithGateUnary_input (st.2.2.2 + 1); omega
        · have := length_encArithGateUnary_const 1; omega
        · have := length_encArithGateUnary_neg res.2.length; dsimp only [res] at this; omega
        · have := length_encArithGateUnary_add (res.2.length + 2) (res.2.length + 3)
          dsimp only [res] at this; omega
        · have := length_encArithGateUnary_mul res.2.length (res.2.length + 4)
          dsimp only [res] at this; omega
        · have := length_encArithGateUnary_mul res.2.length (res.1.headD 0)
          dsimp only [res] at this hgt_le; omega
        · have := length_encArithGateUnary_mul (res.1.headD 0) (res.2.length + 1)
          dsimp only [res] at this hgt_le; omega
        · have := length_encArithGateUnary_neg (res.2.length + 2); dsimp only [res] at this; omega
        · have := length_encArithGateUnary_add (res.2.length + 7) (res.2.length + 8)
          dsimp only [res] at this; omega
        · have := length_encArithGateUnary_mul (res.2.length + 4) (res.2.length + 9)
          dsimp only [res] at this; omega
    · -- ltZero tw
      obtain ⟨hr_len, hgt_le, hr_enc⟩ := hterm_inv tw (Or.inr rfl)
      set res := compileTermTokens ((termTokensDecoder.decode tw).getD []) st.2.2.1
      have hpref : st.2.2.1.length ≤ res.2.length := compileTermTokens_length_ge _ _ _
      refine ⟨by simp; omega,
        by simp; omega,
        by simp only [compileFormulaTokenStep_ltZero_raw, ltZeroGateBlock_length,
          List.length_append,
            List.length_cons, List.length_nil]
           dsimp only [res] at hr_len
           have hwl : word.length ≤ L := by omega
           nlinarith,
        by simp; omega, ?_, ?_, ?_⟩
      · intro g hgm
        simp only [
          compileFormulaTokenStep_ltZero_raw,
            List.mem_cons,
              List.length_append] at hgm ⊢
        rcases hgm with rfl | hgm
        · omega
        · exact (hsm g hgm).trans (by dsimp only [res] at hpref; omega)
      · intro g hgm
        simp only [
          compileFormulaTokenStep_ltZero_raw,
            List.mem_cons,
              List.length_append] at hgm ⊢
        have hblen : (ltZeroGateBlock res.2.length (res.1.headD 0) st.2.2.2).length = 19 := rfl
        rcases hgm with rfl | rfl | rfl | rfl | hgm <;>
          try (dsimp only [res] at hblen ⊢; omega)
        exact (hzm g hgm).trans (by dsimp only [res] at hpref; omega)
      · intro g hgm
        simp only [compileFormulaTokenStep_ltZero_raw, ltZeroGateBlock_length,
          mem_ltZeroGateBlock_iff, List.mem_append,
          List.length_append] at hgm ⊢
        rcases hgm with hgm | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
        · rcases hr_enc g hgm with hgs | hle
          · exact (hgenc g hgs).trans (by dsimp only [res] at hpref; omega)
          · dsimp only [res] at hle; omega
        · have := length_encArithGateUnary_input st.2.2.2; omega
        · have := length_encArithGateUnary_input (st.2.2.2 + 1); omega
        · have := length_encArithGateUnary_input (st.2.2.2 + 2); omega
        · have := length_encArithGateUnary_input (st.2.2.2 + 3); omega
        · have := length_encArithGateUnary_const 1; omega
        · have := length_encArithGateUnary_neg res.2.length; dsimp only [res] at this; omega
        · have := length_encArithGateUnary_add (res.2.length + 4) (res.2.length + 5)
          dsimp only [res] at this; omega
        · have := length_encArithGateUnary_mul res.2.length (res.2.length + 6)
          dsimp only [res] at this; omega
        · have := length_encArithGateUnary_mul (res.2.length + 1) (res.2.length + 1)
          dsimp only [res] at this; omega
        · have := length_encArithGateUnary_add (res.1.headD 0) (res.2.length + 8)
          dsimp only [res] at this hgt_le; omega
        · have := length_encArithGateUnary_mul res.2.length (res.2.length + 9)
          dsimp only [res] at this; omega
        · have := length_encArithGateUnary_mul (res.2.length + 1) (res.2.length + 2)
          dsimp only [res] at this; omega
        · have := length_encArithGateUnary_neg (res.2.length + 4); dsimp only [res] at this; omega
        · have := length_encArithGateUnary_add (res.2.length + 11) (res.2.length + 12)
          dsimp only [res] at this; omega
        · have := length_encArithGateUnary_mul res.2.length (res.2.length + 13)
          dsimp only [res] at this; omega
        · have := length_encArithGateUnary_mul (res.2.length + 3) (res.2.length + 3)
          dsimp only [res] at this; omega
        · have := length_encArithGateUnary_neg (res.2.length + 15)
          dsimp only [res] at this; omega
        · have := length_encArithGateUnary_add (res.1.headD 0) (res.2.length + 16)
          dsimp only [res] at this hgt_le; omega
        · have := length_encArithGateUnary_mul (res.2.length + 6) (res.2.length + 17)
          dsimp only [res] at this; omega
    · -- not
      have hbp : st.1.headD 0 ≤ st.2.2.1.length := by
        cases h : st.1 with | nil => simp | cons a _ => exact hsm a (by simp [h])
      refine ⟨by simp [List.length_tail]; omega,
        by simp; omega,
        by simp; nlinarith,
        by simp; omega, ?_, ?_, ?_⟩
      · intro g hgm
        simp only [
          compileFormulaTokenStep_not_raw,
            List.mem_cons,
              List.length_append,
          List.length_cons, List.length_nil] at hgm ⊢
        rcases hgm with rfl | hgm
        · omega
        · exact (hsm g (List.mem_of_mem_tail hgm)).trans (by omega)
      · intro g hgm; simp only [
        compileFormulaTokenStep_not_raw,
          List.length_append,
            List.length_cons,
          List.length_nil]
        exact (hzm g hgm).trans (by omega)
      · intro g hgm
        simp only [
          compileFormulaTokenStep_not_raw,
            List.mem_append,
              List.mem_cons, List.not_mem_nil,
          or_false, List.length_append, List.length_cons, List.length_nil] at hgm ⊢
        rcases hgm with hgm | (rfl | rfl | rfl)
        · exact (hgenc g hgm).trans (by omega)
        · have := length_encArithGateUnary_const 1; omega
        · have := length_encArithGateUnary_neg (st.1.headD 0); omega
        · have := length_encArithGateUnary_add st.2.2.1.length (st.2.2.1.length + 1); omega
    · -- and
      have hbp : st.1.headD 0 ≤ st.2.2.1.length := by
        cases h : st.1 with | nil => simp | cons a _ => exact hsm a (by simp [h])
      have hbq : st.1.tail.headD 0 ≤ st.2.2.1.length := by
        cases h : st.1 with
        | nil => simp
        | cons _ t => cases ht : t with | nil => simp | cons b _ => exact hsm b (by simp [h, ht])
      refine ⟨by simp [List.length_tail]; omega,
        by simp; omega,
        by simp; nlinarith,
        by simp; omega, ?_, ?_, ?_⟩
      · intro g hgm
        simp only [
            compileFormulaTokenStep_and_raw, List.mem_cons,
              List.length_append,
          List.length_singleton] at hgm ⊢
        rcases hgm with rfl | hgm
        · omega
        · exact (hsm g (List.mem_of_mem_tail (List.mem_of_mem_tail hgm))).trans (by omega)
      · intro g hgm; simp only [
          compileFormulaTokenStep_and_raw, List.length_append,
        List.length_singleton]
        exact (hzm g hgm).trans (by omega)
      · intro g hgm
        simp only [
            compileFormulaTokenStep_and_raw, List.mem_append,
              List.mem_singleton,
          List.length_append, List.length_singleton] at hgm ⊢
        rcases hgm with hgm | rfl
        · exact (hgenc g hgm).trans (by omega)
        · have := length_encArithGateUnary_mul (st.1.headD 0) (st.1.tail.headD 0); omega
    · -- or
      have hbp : st.1.headD 0 ≤ st.2.2.1.length := by
        cases h : st.1 with | nil => simp | cons a _ => exact hsm a (by simp [h])
      have hbq : st.1.tail.headD 0 ≤ st.2.2.1.length := by
        cases h : st.1 with
        | nil => simp
        | cons _ t => cases ht : t with | nil => simp | cons b _ => exact hsm b (by simp [h, ht])
      refine ⟨by simp [List.length_tail]; omega,
        by simp; omega,
        by simp; nlinarith,
        by simp; omega, ?_, ?_, ?_⟩
      · intro g hgm
        simp only [
            compileFormulaTokenStep_or_raw, List.mem_cons,
              List.length_append,
          List.length_cons, List.length_nil] at hgm ⊢
        rcases hgm with rfl | hgm
        · omega
        · exact (hsm g (List.mem_of_mem_tail (List.mem_of_mem_tail hgm))).trans (by omega)
      · intro g hgm; simp only [
          compileFormulaTokenStep_or_raw, List.length_append,
            List.length_cons,
          List.length_nil]
        exact (hzm g hgm).trans (by omega)
      · intro g hgm
        simp only [
            compileFormulaTokenStep_or_raw, List.mem_append,
              List.mem_cons, List.not_mem_nil,
          or_false, List.length_append, List.length_cons, List.length_nil] at hgm ⊢
        rcases hgm with hgm | (rfl | rfl | rfl | rfl)
        · exact (hgenc g hgm).trans (by omega)
        · have := length_encArithGateUnary_add (st.1.headD 0) (st.1.tail.headD 0); omega
        · have := length_encArithGateUnary_mul (st.1.headD 0) (st.1.tail.headD 0); omega
        · have := length_encArithGateUnary_neg (st.2.2.1.length + 1); omega
        · have := length_encArithGateUnary_add st.2.2.1.length (st.2.2.1.length + 2); omega
/-- Size bound on intermediate states of the formula-token fold for `formulaFold_polyTime`. -/
private theorem formulaFold_size_bound (word : List Bool) (i : ℕ)
    (_hi : i ≤ (formulaWordTokens word).reverse.length) :
    (encFormulaState (((formulaWordTokens word).reverse.take i).foldl compileFormulaTokenStep
      ([], [], [], word.length))).length ≤ 1000000 * (word.length + 1) ^ 4 := by
  set L := word.length + 1
  have htoks_len : (formulaWordTokens word).length ≤ L := by
    have := formulaWordTokens_length_le word; omega
  obtain ⟨hs, hz, hg, hsl, hsm, hzm, hgenc⟩ :=
    formulaFold_invariants word ((formulaWordTokens word).reverse.take i)
      (fun tok htok ↦ List.mem_reverse.mp (List.mem_of_mem_take htok))
  have hilen : ((formulaWordTokens word).reverse.take i).length ≤ L := by
    simp only [List.length_take, List.length_reverse]
    exact (Nat.min_le_right _ _).trans htoks_len
  set st := ((formulaWordTokens word).reverse.take i).foldl compileFormulaTokenStep
    ([], [], [], word.length)
  set G := L * (L + 20)
  set M := 10 * L + 2 * G + 20
  have hst_g : st.2.2.1.length ≤ G := hg.trans (Nat.mul_le_mul_right _ hilen)
  have hst_sl : st.2.2.2 ≤ M := by omega
  have hst_s : st.1.length ≤ L := hs.trans hilen
  have hst_z : st.2.1.length ≤ 4 * L := hz.trans (by omega)
  have h1 : (encList encUnary st.1).length ≤ L * (2 * M + 1) :=
    (length_encList_le encUnary st.1 (b := M) fun g hg' ↦ by
      simp only [encUnary_apply, List.length_replicate]; have := hsm g hg'; omega).trans
      (Nat.mul_le_mul_right _ hst_s)
  have h2 : (encList encUnary st.2.1).length ≤ 4 * L * (2 * M + 1) :=
    (length_encList_le encUnary st.2.1 (b := M) fun g hg' ↦ by
      simp only [encUnary_apply, List.length_replicate]; have := hzm g hg'; omega).trans
      (Nat.mul_le_mul_right _ hst_z)
  have h3 : (encList encArithGateUnary st.2.2.1).length ≤
      G * (2 * (6 * M + 2 * L + 24) + 1) :=
    (length_encList_le encArithGateUnary st.2.2.1 (b := 6 * M + 2 * L + 24) fun g hg' ↦ by
      have := hgenc g hg'; omega).trans (Nat.mul_le_mul_right _ hst_g)
  have h4 : (encUnary st.2.2.2).length ≤ M := by
    simp only [encUnary_apply, List.length_replicate]; exact hst_sl
  change (encPair (encList encUnary)
    (encPair (encList encUnary) (encPair (encList encArithGateUnary) encUnary)) st).length ≤ _
  rw [length_encPair, length_encPair, length_encPair]
  clear_value st
  have hL : 1 ≤ L := by omega
  have hL2 : L ≤ L ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_right L hL
  have hL3 : L ^ 2 ≤ L ^ 3 := by rw [pow_succ]; exact Nat.le_mul_of_pos_right _ hL
  have hL4 : L ^ 3 ≤ L ^ 4 := by rw [pow_succ]; exact Nat.le_mul_of_pos_right _ hL
  have hG : G ≤ 21 * L ^ 2 := by
    calc G = L * (L + 20) := rfl
      _ ≤ L * (L + 20 * L) := Nat.mul_le_mul_left L (by omega)
      _ = 21 * (L * L) := by ring
      _ = 21 * L ^ 2 := by rw [sq]
  have hM : M ≤ 72 * L ^ 2 := by omega
  clear_value G M
  have h1' : L * (2 * M + 1) ≤ 145 * L ^ 3 := by
    calc L * (2 * M + 1) ≤ L * (145 * L ^ 2) := Nat.mul_le_mul_left L (by omega)
      _ = 145 * L ^ 3 := by ring
  have h2' : 4 * L * (2 * M + 1) ≤ 580 * L ^ 3 := by
    calc 4 * L * (2 * M + 1) = 4 * (L * (2 * M + 1)) := by ring
      _ ≤ 4 * (145 * L ^ 3) := Nat.mul_le_mul_left 4 h1'
      _ = 580 * L ^ 3 := by ring
  have h3' : G * (2 * (6 * M + 2 * L + 24) + 1) ≤ 20000 * L ^ 4 := by
    have hinner : 2 * (6 * M + 2 * L + 24) + 1 ≤ 917 * L ^ 2 := by omega
    calc G * (2 * (6 * M + 2 * L + 24) + 1)
        ≤ (21 * L ^ 2) * (917 * L ^ 2) := Nat.mul_le_mul hG hinner
      _ = 19257 * L ^ 4 := by ring
      _ ≤ 20000 * L ^ 4 := Nat.mul_le_mul_right _ (by decide)
  omega

/-- Polynomial-time certificate for the formula-token fold of `etrWordToRawCircuit`. -/
private theorem formulaFold_polyTime :
    ComputableInPolyTime
      (fun word : List Bool ↦
        (formulaWordTokens word).reverse.foldl compileFormulaTokenStep
          ([], [], [], word.length))
      encBits encFormulaState := by
  have hlist := (listReverse encFormulaToken).comp formulaWordTokens_polyTime
  have hinit : ComputableInPolyTime (fun word : List Bool ↦ ([], [], [], word.length))
      encBits encFormulaState :=
    (const []).prod ((const []).prod ((const []).prod (length_bits)))
  let B : List Bool → ℕ := fun word ↦ 1000000 * (word.length + 1) ^ 4
  have hB : PolyBounded (fun word : List Bool ↦ (encBits word).length) B :=
    PolyBounded.of_forall_le 1000000 4 fun _ ↦ le_rfl
  exact foldl' hlist hinit compileFormulaTokenStep_polyTime hB formulaFold_size_bound

/-- Stage 3: `sumOfSquaresStep` fold runs in polynomial time. -/
private theorem sumOfSquares_polyTime :
    ComputableInPolyTime
      (fun p : List ℕ × (ℕ × List ArithGate) ↦ p.1.foldl sumOfSquaresStep p.2)
      (encPair (encList encUnary) (encPair encUnary (encList encArithGateUnary)))
      (encPair encUnary (encList encArithGateUnary)) := by
  let encS := encPair encUnary (encList encArithGateUnary)
  let encIn := encPair (encList encUnary) encS
  have hstep : ComputableInPolyTime
      (fun p : (ℕ × List ArithGate) × ℕ ↦ sumOfSquaresStep p.1 p.2)
      (encPair encS encUnary) encS := by
    have hacc := (fst _ _).comp (fst encS encUnary)
    have hgs := (snd _ _).comp (fst encS encUnary)
    have hg := snd encS encUnary
    have hj := (length_list encArithGateUnary).comp hgs
    have hnew := (cons _).comp ((mkMul_polyTime hg hg).prod
      ((cons _).comp ((mkAdd_polyTime hacc hj).prod (const []))))
    exact (unary_add.comp (hj.prod (const 1))).prod
      ((listAppend encArithGateUnary).comp (hgs.prod hnew))
  let B : List ℕ × (ℕ × List ArithGate) → ℕ := fun p ↦
    200 * ((encIn p).length + 1) ^ 2
  have hB : PolyBounded (fun p ↦ (encIn p).length) B :=
    PolyBounded.of_forall_le 200 2 fun _ ↦ le_rfl
  refine foldl' (fst _ _) (snd _ _) hstep hB fun p i hi ↦ ?_
  set L := (encIn p).length
  have hp1_le : (encList encUnary p.1).length ≤ L := length_le_encPair_left _ _ p
  have hp2_le : (encS p.2).length ≤ L := length_le_encPair_right _ _ p
  have ha_le : p.2.1 ≤ L := by
    have := (length_le_encPair_left encUnary (encList encArithGateUnary) p.2).trans hp2_le
    simpa [encUnary_apply] using this
  have hgs_le : (encList encArithGateUnary p.2.2).length ≤ L :=
    (length_le_encPair_right encUnary (encList encArithGateUnary) p.2).trans hp2_le
  have hlen1 : p.1.length ≤ L :=
    (SizedListEncoding.length_le encUnary (encL := encList encUnary) p.1).trans hp1_le
  have hlen2 : p.2.2.length ≤ L :=
    (SizedListEncoding.length_le encArithGateUnary (encL := encList encArithGateUnary) p.2.2).trans
      hgs_le
  have hgen : ∀ (zs : List ℕ), (∀ z ∈ zs, z ≤ L) →
      let st := zs.foldl sumOfSquaresStep p.2
      st.2.length = p.2.2.length + 2 * zs.length ∧
      st.1 ≤ p.2.1 + p.2.2.length + 2 * zs.length ∧
      (∀ g ∈ st.2, g ∈ p.2.2 ∨
        (encArithGateUnary g).length ≤ 6 * (p.2.1 + p.2.2.length + 2 * zs.length + L) + 12) := by
    intro zs
    induction zs using List.reverseRecOn with
    | nil => intro _; exact ⟨by simp, by simp, fun g hg ↦ Or.inl hg⟩
    | append_singleton zs z ih =>
      intro hmem
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      obtain ⟨hlen', hacc', hgm⟩ := ih fun a ha ↦ hmem a (List.mem_append_left _ ha)
      set st := zs.foldl sumOfSquaresStep p.2
      have hz := hmem z (List.mem_append_right _ (List.mem_singleton.mpr rfl))
      refine ⟨by simp [hlen']; omega,
        by simp only [sumOfSquaresStep_fst, List.length_append,
          List.length_singleton]; omega, ?_⟩
      intro g hg
      simp only [sumOfSquaresStep_snd, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hg
      rcases hg with hg | (rfl | rfl)
      · rcases hgm g hg with hp2 | hle
        · exact Or.inl hp2
        · exact Or.inr (hle.trans (by simp))
      · right
        have := length_encArithGateUnary_mul z z
        simp only [List.length_append, List.length_singleton]; omega
      · right
        have := length_encArithGateUnary_add st.1 st.2.length
        simp only [List.length_append, List.length_singleton]; omega
  obtain ⟨hlen', hacc', hgm⟩ := hgen (p.1.take i) fun z hz ↦ by
    have hz' := List.mem_of_mem_take hz
    have h1 := (SizedListEncoding.length_elem_le (encA := encUnary) (encL :=
      encList encUnary) p.1 z hz').trans
      hp1_le
    simpa [encUnary_apply] using h1
  have hilen : (p.1.take i).length ≤ L := by
    simp only [List.length_take]
    exact (Nat.min_le_right _ _).trans hlen1
  rw [length_encPair]
  have h1 : (encUnary ((p.1.take i).foldl sumOfSquaresStep p.2).1).length ≤ 4 * L := by
    simp only [encUnary_apply, List.length_replicate]; omega
  have h2 : (encList encArithGateUnary ((p.1.take i).foldl sumOfSquaresStep p.2).2).length ≤
      3 * L * (2 * (30 * L + 12) + 1) := by
    have hle := length_encList_le encArithGateUnary
      ((p.1.take i).foldl sumOfSquaresStep p.2).2 (b := 30 * L + 12) fun g hg ↦ by
        rcases hgm g hg with hp2 | hle
        · have := (SizedListEncoding.length_elem_le (encA := encArithGateUnary)
            (encL := encList encArithGateUnary) p.2.2 g hp2).trans hgs_le
          omega
        · omega
    exact hle.trans (Nat.mul_le_mul_right _ (by omega))
  simp only [encUnary_apply, List.length_replicate] at h1 ⊢
  dsimp only [B]
  nlinarith

/-- Stage 4: `etrWordToRawCircuit` runs in polynomial time. -/
private theorem etrWordToRawCircuit_polyTime :
    ComputableInPolyTime etrWordToRawCircuit encBits
      (encPair encUnary (encPair (encList encArithGateUnary) encUnary)) := by
  have hst := formulaFold_polyTime
  have hstk := (fst _ _).comp hst
  have hzs := (fst _ _).comp ((snd _ _).comp hst)
  have hgs := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp hst))
  have hsl := (snd _ _).comp ((snd _ _).comp ((snd _ _).comp hst))
  have hk := (length_list encArithGateUnary).comp hgs
  have hbRoot := (headD (encA := encUnary) 0).comp hstk
  have hnew1 := (cons encArithGateUnary).comp
    ((mkConst_polyTime (const (α := List Bool) (1 : ℚ))).prod
      ((cons encArithGateUnary).comp ((mkNeg_polyTime hk).prod
        ((cons encArithGateUnary).comp
          ((mkAdd_polyTime hbRoot (unary_add.comp (hk.prod (const 1)))).prod (const []))))))
  have hg1 := (listAppend encArithGateUnary).comp (hgs.prod hnew1)
  have hallZ := (cons encUnary).comp ((unary_add.comp (hk.prod (const 2))).prod hzs)
  have hinitIdx := (length_list encArithGateUnary).comp hg1
  have hg2 := (snoc encArithGateUnary).comp
    (hg1.prod (const (α := List Bool) (ArithGate.const 0)))
  have hfinal := sumOfSquares_polyTime.comp (hallZ.prod (hinitIdx.prod hg2))
  exact hsl.prod (((snd _ _).comp hfinal).prod ((fst _ _).comp hfinal))

/-! ### Polynomial-Time Certificate for `etrWordToARM3` -/

/-- **Polynomial-time certificate**: `etrWordToARM3` is computable in polynomial time. -/
theorem etrWordToARM3_polyTime :
    ComputableInPolyTime etrWordToARM3 encBits encARMInstance := by
  have hraw := etrWordToRawCircuit_polyTime
  have hN := (fst _ _).comp hraw
  have hgs := (fst _ _).comp ((snd _ _).comp hraw)
  have hS := (length_list encArithGateUnary).comp hgs
  have hd := unary_add.comp ((unary_add.comp ((const 3).prod hN)).prod
    (unary_mul.comp ((const 3).prod hS)))
  have hdBin := unary_to_binary.comp hd
  have hcs := compileCircuitConstraints_polyTime.comp hraw
  exact (hdBin.prod (hdBin.prod hcs)).of_enc_eq fun _ ↦ rfl

/-! ### Main Complexity Theorems (, ) -/

/-- **Polynomial-time many-one reduction `ETR ≤ₚ ARM(3)`**. -/
theorem polyTimeReducible_ETR_ARM3 :
    PolyTimeReducible encBits encARMInstance ETR (ARM 3) :=
  ⟨etrWordToARM3, etrWordToARM3_polyTime, etrWordToARM3_mem_iff⟩

/-- `ETR` is `∃ℝ`-hard under polynomial-time many-one reductions. -/
theorem etr_existsRealHard : PolyTimeHard @ExistsReal encBits ETR :=
  fun _ _ _ h ↦ h

/-- `ETR` is `∃ℝ`-complete under polynomial-time many-one reductions. -/
theorem etr_existsRealComplete : PolyTimeComplete @ExistsReal encBits ETR :=
  ⟨PolyTimeReducible.refl encBits ETR, etr_existsRealHard⟩

/-- `ARM(3)` is `∃ℝ`-hard under polynomial-time
many-one reductions. -/
theorem arm3_existsRealHard : PolyTimeHard @ExistsReal encARMInstance (ARM 3) :=
  etr_existsRealHard.trans polyTimeReducible_ETR_ARM3

/-- `ARM(3)` is `∃ℝ`-complete. -/
theorem arm3_existsRealComplete : PolyTimeComplete @ExistsReal encARMInstance (ARM 3) :=
  ⟨arm_mem_existsReal 3, arm3_existsRealHard⟩

/-! ### Non-Degenerate Joint-Hypothesis Witness (Anti-Vacuity) -/

/-- Non-degenerate intended-domain witness: the arithmetic circuit `C` computing `x * y - 6` has a
real root `(x = 2, y = 3)`, its compiled `ARM(3)` instance is feasible with a non-degenerate
rank-3 matrix, and `ARM(3)` also admits a concrete infeasible instance. -/
theorem arm3_nondegenerate_witness :
    ∃ (C : ArithCircuit) (inst_no : ARMInstance),
      C.numInputs = 2 ∧
      C.size = 5 ∧
      C.Satisfiable ∧
      compileCircuit C ∈ ARM 3 ∧
      inst_no ∉ ARM 3 := by
  let C : ArithCircuit :=
    { numInputs := 2
      gates := [.input 0, .input 1, .mul 0 1, .const (-6), .add 2 3]
      output := 4
      gates_wf := by
        intro k hk
        simp only [List.length_cons, List.length_nil] at hk
        interval_cases k <;> simp [ArithGate.wellFormed_add, ArithGate.wellFormed_mul]
      output_lt := by decide }
  have hCsat : C.Satisfiable := by
    refine ⟨![2, 3], ?_⟩
    simp [C, ArithCircuit.eval_eq, ArithCircuit.evalGate_eq, evalGatesList_eq_foldl]
    norm_num
  let cs_no : List (Matrix (Fin 1) (Fin 1) ℚ × ℚ) :=
    [(entryMatrix 1 1 0 0, 0), (entryMatrix 1 1 0 0, 1)]
  let inst_no : ARMInstance := ARMInstance.ofMatrices cs_no
  have hno : inst_no ∉ ARM 3 := by
    rintro ⟨X, hsat, _⟩
    have hsat' := (ARMInstance.satisfies_ofMatrices_iff cs_no X).mp hsat
    have h0 := hsat' (entryMatrix 1 1 0 0, 0) (by simp [cs_no])
    have h1 := hsat' (entryMatrix 1 1 0 0, 1) (by simp [cs_no])
    norm_num at h0 h1
    linarith
  exact ⟨C, inst_no, rfl, rfl, hCsat, (circuit_iff_arm3 C).mp hCsat, hno⟩

end Cslib.Complexity
