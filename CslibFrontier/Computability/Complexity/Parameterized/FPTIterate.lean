module

public import CslibFrontier.Computability.Complexity.Parameterized
public import CslibFrontier.Computability.Complexity.Parameterized.VertexCover
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.IterateWhile
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option

import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size

/-!
# FPT-Time Iteration and Constructive Minimum Vertex Cover

Provides general fixed-parameter-tractable (FPT) bounded and unbounded search combinators built
directly on `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.iterateWhile`, together with a
constructive FPT-time algorithm `minVertexCover` that returns a minimum-cardinality vertex cover
of a finite graph parameterized by its vertex cover number.

## Main definitions

- `CslibFrontier.Complexity.searchUnbounded`: unbounded linear search returning the first `y` with
  `step (a, i) = some y`.
- `CslibFrontier.Complexity.searchFirst`: bounded linear search returning the first `some y` for
  `i < bound a`.
- `CslibFrontier.Complexity.minVertexCoverSize`: minimum cardinality of a vertex cover of `G`.
- `CslibFrontier.Complexity.minVertexCover`: constructive FPT-time minimum vertex cover finder built
  on `Cslib.Complexity.VertexCover.foldBranch`.

## Main results

- `CslibFrontier.Complexity.computableInFPTTime_prod`: pairing two FPT-time computable functions
  under the same parameter is computable in FPT time.
- `CslibFrontier.Complexity.computableInFPTTime_iterateWhile_fpt_on`: iterating an FPT-time step
  function on an invariant subtype for at most `Fr (κ x)` rounds with FPT-bounded intermediate
  encoding lengths and step parameters is computable in FPT time.
- `CslibFrontier.Complexity.computableInFPTTime_iterateWhile_on`: iterating a polynomial-time step
  function on an invariant subtype for at most `Fr (κ x)` rounds with FPT-bounded intermediate
  encoding lengths is computable in FPT time.
- `CslibFrontier.Complexity.computableInFPTTime_searchUnbounded`: `searchUnbounded` is computable in
  FPT time.
- `CslibFrontier.Complexity.computableInFPTTime_searchFirst`: `searchFirst` is computable in FPT
  time.
- `CslibFrontier.Complexity.computableInFPTTime_anyRange`: bounded existential search over
  `i < bound a` with an FPT-time predicate is computable in FPT time.
- `CslibFrontier.Complexity.minVertexCover_spec`: `minVertexCover G` is a duplicate-free vertex
  cover of `G` of minimum cardinality `minVertexCoverSize G`.
- `CslibFrontier.Complexity.computableInFPTTime_minVertexCover`: `minVertexCover` is computable in
  FPT time parameterized by `minVertexCoverSize`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-! ### 1. General FPT Iteration and Search Combinators -/

/-- Congruence helper for `ComputableInFPTTime`. -/
theorem computableInFPTTime_congr {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {κ : α → ℕ} {f g : α → β} (hf : ComputableInFPTTime f encA encB κ) (h : ∀ a, f a = g a) :
    ComputableInFPTTime g encA encB κ := by
  have heq : f = g := funext h
  exact heq ▸ hf

/-- Pairing two FPT-time computable functions under the same parameter is computable in FPT time. -/
theorem computableInFPTTime_prod {α β₁ β₂ : Type} {encA : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool} {κ : α → ℕ}
    {f : α → β₁} {g : α → β₂}
    (hf : ComputableInFPTTime f encA enc₁ κ) (hg : ComputableInFPTTime g encA enc₂ κ) :
    ComputableInFPTTime (fun a ↦ (f a, g a)) encA (encPair enc₁ enc₂) κ := by
  obtain ⟨F₁, c₁, h₁⟩ := hf
  obtain ⟨F₂, c₂, h₂⟩ := hg
  have hO₁ : ComputableInO f encA enc₁ (fun a ↦ F₁ (κ a) * ((encA a).length + 1) ^ c₁)
      (fun a ↦ F₁ (κ a) * ((encA a).length + 1) ^ c₁) :=
    .of_bounds h₁ 1 (fun _ ↦ by omega) (fun _ ↦ by omega)
      fun a ↦ (h₁.length_le a).trans (by omega)
  have hO₂ : ComputableInO g encA enc₂ (fun a ↦ F₂ (κ a) * ((encA a).length + 1) ^ c₂)
      (fun a ↦ F₂ (κ a) * ((encA a).length + 1) ^ c₂) :=
    .of_bounds h₂ 1 (fun _ ↦ by omega) (fun _ ↦ by omega)
      fun a ↦ (h₂.length_le a).trans (by omega)
  have hO : ComputableInO (fun a ↦ (f a, g a)) encA (encPair enc₁ enc₂)
      (fun a ↦ (F₁ (κ a) + F₂ (κ a)) * ((encA a).length + 1) ^ (c₁ + c₂))
      (fun a ↦ (F₁ (κ a) + F₂ (κ a)) * ((encA a).length + 1) ^ (c₁ + c₂)) := by
    refine (hO₁.prod hO₂).mono_le (fun a ↦ ?_) (fun a ↦ ?_)
    · have hpos : 0 < (encA a).length + 1 := Nat.add_pos_right _ one_pos
      have h1 := Nat.mul_le_mul_left (F₁ (κ a)) (Nat.pow_le_pow_right hpos (Nat.le_add_right c₁ c₂))
      have h2 := Nat.mul_le_mul_left (F₂ (κ a)) (Nat.pow_le_pow_right hpos (Nat.le_add_left c₂ c₁))
      rw [Nat.add_mul]; omega
    · have hpos : 0 < (encA a).length + 1 := Nat.add_pos_right _ one_pos
      have h1 := Nat.mul_le_mul_left (F₁ (κ a)) (Nat.pow_le_pow_right hpos (Nat.le_add_right c₁ c₂))
      have h2 := Nat.mul_le_mul_left (F₂ (κ a)) (Nat.pow_le_pow_right hpos (Nat.le_add_left c₂ c₁))
      rw [Nat.add_mul]; omega
  exact hO.computableInFPTTime (F := fun k ↦ F₁ k + F₂ k) (c := c₁ + c₂)

/-- Iterating an FPT-time function `f : α → α` on an `f`-invariant subtype `Subtype P` until
`enc (f^[n + 1] x) = []` runs in FPT time whenever the iteration count, intermediate encoding
lengths, and step parameters along the orbit are bounded by functions of `κ x`. -/
theorem computableInFPTTime_iterateWhile_fpt_on {α : Type} {f : α → α} {enc : α ↪ List Bool}
    {κf : α → ℕ} (hf : ComputableInFPTTime f enc enc κf)
    {P : α → Prop} (hP : ∀ a, P a → P (f a))
    {κ : Subtype P → ℕ} {r : Subtype P → ℕ}
    (hr : ∀ x : Subtype P, IsLeast {n | enc (f^[n + 1] x.1) = []} (r x))
    {Fr Fl h : ℕ → ℕ} {cl : ℕ}
    (hFr : ∀ x, r x ≤ Fr (κ x))
    (hFl : ∀ x, ∀ n ≤ r x, (enc (f^[n] x.1)).length ≤ Fl (κ x) * ((enc x.1).length + 1) ^ cl)
    (hκf : ∀ x, ∀ n ≤ r x, κf (f^[n] x.1) ≤ h (κ x)) :
    ComputableInFPTTime (fun x : Subtype P ↦ (⟨f^[r x] x.1, by
      have : ∀ m, P (f^[m] x.1) := fun m ↦ by
        induction m with
        | zero => exact x.2
        | succ m ih => rw [Function.iterate_succ_apply']; exact hP _ ih
      exact this (r x)⟩ : Subtype P))
      ((Function.Embedding.subtype P).trans enc)
      ((Function.Embedding.subtype P).trans enc) κ := by
  let encP : Subtype P ↪ List Bool := (Function.Embedding.subtype P).trans enc
  let fP : Subtype P → Subtype P := fun x ↦ ⟨f x.1, hP x.1 x.2⟩
  have hfP_iter : ∀ (m : ℕ) (x : Subtype P), (fP^[m] x).1 = f^[m] x.1 := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      dsimp only [fP]
      rw [ih x]
  obtain ⟨Ff, cf, hts⟩ := hf
  obtain ⟨c0, htidy0⟩ := hts.exists_computableTidilyInTimeAndSpace
  let Fmono : ℕ → ℕ := fun k ↦ ∑ j ∈ Finset.range (k + 1), Ff j
  have hle_Fmono : ∀ {a b : ℕ}, a ≤ b → Ff a ≤ Fmono b := fun {a b} hab ↦
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have htidy : ComputableTidilyInTimeAndSpace f enc enc
      (fun a ↦ (5 * Ff (κf a) + c0) * ((enc a).length + 1) ^ cf)
      (fun a ↦ c0 * (Ff (κf a) * ((enc a).length + 1) ^ cf + 1)) := by
    refine htidy0.mono (fun a ↦ ?_) (fun _ ↦ le_rfl)
    have h1 : c0 ≤ c0 * ((enc a).length + 1) ^ cf :=
      Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (Nat.succ_pos _))
    nlinarith
  have htidyP : ComputableTidilyInTimeAndSpace fP encP encP
      (fun x ↦ (5 * Ff (κf x.1) + c0) * ((encP x).length + 1) ^ cf)
      (fun x ↦ c0 * (Ff (κf x.1) * ((encP x).length + 1) ^ cf + 1)) := by
    obtain ⟨k, State, hFin, tm, htm⟩ := htidy
    exact ⟨k, State, hFin, tm, fun x ↦ htm x.1⟩
  have hrP : ∀ x : Subtype P, IsLeast {n | encP (fP^[n + 1] x) = []} (r x) := by
    intro x
    simpa only [encP, Function.Embedding.trans_apply, Function.Embedding.coe_subtype,
      hfP_iter] using hr x
  obtain ⟨c, hiter⟩ := ComputableTidilyInTimeAndSpace.iterateWhile htidyP hrP
  let F : ℕ → ℕ := fun k ↦ (Fr k + 1) * ((5 * Fmono (h k) + c0) * (Fl k + 1) ^ cf + c * (Fl k + 1))
  let C : ℕ := cl * cf + cl
  have hFPT : ComputableInFPTTime (fun x : Subtype P ↦ fP^[r x] x) encP encP κ := by
    refine (ComputableInTimeAndSpace.mono
      (ComputableTidilyInTimeAndSpace.computableInTimeAndSpace hiter)
      (t' := fun x ↦ F (κ x) * ((encP x).length + 1) ^ C)
      (fun x ↦ ?_) (fun _ ↦ le_rfl)).computableInFPTTime
    have hP1 : 1 ≤ ((encP x).length + 1) ^ cl := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have hsup_len : (Finset.Iic (r x)).sup (fun n ↦ (encP (fP^[n] x)).length) ≤
        Fl (κ x) * ((encP x).length + 1) ^ cl := by
      refine Finset.sup_le fun n hn ↦ ?_
      have := hFl x n (Finset.mem_Iic.mp hn)
      simpa only [encP, Function.Embedding.trans_apply, Function.Embedding.coe_subtype,
        hfP_iter] using this
    have hsup_t : (Finset.Iic (r x)).sup
        (fun n ↦ (5 * Ff (κf (fP^[n] x).1) + c0) * ((encP (fP^[n] x)).length + 1) ^ cf) ≤
        (5 * Fmono (h (κ x)) + c0) * (Fl (κ x) + 1) ^ cf * (((encP x).length + 1) ^ cl) ^ cf := by
      refine Finset.sup_le fun n hn ↦ ?_
      have hn' := Finset.mem_Iic.mp hn
      have hl : (encP (fP^[n] x)).length ≤ Fl (κ x) * ((encP x).length + 1) ^ cl := by
        have := hFl x n hn'
        simpa only [encP, Function.Embedding.trans_apply, Function.Embedding.coe_subtype,
          hfP_iter] using this
      have hfm : Ff (κf (fP^[n] x).1) ≤ Fmono (h (κ x)) := by
        rw [hfP_iter]; exact hle_Fmono (hκf x n hn')
      have h1 : (encP (fP^[n] x)).length + 1 ≤ (Fl (κ x) + 1) * ((encP x).length + 1) ^ cl := by
        nlinarith
      calc (5 * Ff (κf (fP^[n] x).1) + c0) * ((encP (fP^[n] x)).length + 1) ^ cf
          ≤ (5 * Fmono (h (κ x)) + c0) * ((Fl (κ x) + 1) * ((encP x).length + 1) ^ cl) ^ cf :=
            Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left h1 cf)
        _ = (5 * Fmono (h (κ x)) + c0) * (Fl (κ x) + 1) ^ cf *
              (((encP x).length + 1) ^ cl) ^ cf := by
            rw [Nat.mul_pow, Nat.mul_assoc]
    have hlen1 : (Finset.Iic (r x)).sup (fun n ↦ (encP (fP^[n] x)).length) + 1 ≤
        (Fl (κ x) + 1) * ((encP x).length + 1) ^ cl := by nlinarith
    have hpow : (((encP x).length + 1) ^ cl) ^ cf * ((encP x).length + 1) ^ cl =
        ((encP x).length + 1) ^ C := by
      dsimp only [C]; rw [← Nat.pow_mul, ← Nat.pow_add]
    have hterm1 : (5 * Fmono (h (κ x)) + c0) * (Fl (κ x) + 1) ^ cf *
          (((encP x).length + 1) ^ cl) ^ cf ≤
        (5 * Fmono (h (κ x)) + c0) * (Fl (κ x) + 1) ^ cf * ((encP x).length + 1) ^ C := by
      rw [← hpow, ← Nat.mul_assoc]
      exact Nat.le_mul_of_pos_right _ hP1
    have hterm2 : c * ((Fl (κ x) + 1) * ((encP x).length + 1) ^ cl) ≤
        c * (Fl (κ x) + 1) * ((encP x).length + 1) ^ C := by
      rw [← hpow]
      have hsub : ((encP x).length + 1) ^ cl ≤
          (((encP x).length + 1) ^ cl) ^ cf * ((encP x).length + 1) ^ cl := by
        have : 1 ≤ (((encP x).length + 1) ^ cl) ^ cf := Nat.one_le_pow _ _ hP1
        nlinarith
      have hmul := Nat.mul_le_mul_left (c * (Fl (κ x) + 1)) hsub
      simpa [Nat.mul_assoc] using hmul
    have hr1 : r x + 1 ≤ Fr (κ x) + 1 := Nat.add_le_add_right (hFr x) 1
    have hinner : (Finset.Iic (r x)).sup
          (fun n ↦ (5 * Ff (κf (fP^[n] x).1) + c0) * ((encP (fP^[n] x)).length + 1) ^ cf) +
        c * ((Finset.Iic (r x)).sup (fun n ↦ (encP (fP^[n] x)).length) + 1) ≤
        ((5 * Fmono (h (κ x)) + c0) * (Fl (κ x) + 1) ^ cf + c * (Fl (κ x) + 1)) *
          ((encP x).length + 1) ^ C := by
      have h2 : c * ((Finset.Iic (r x)).sup (fun n ↦ (encP (fP^[n] x)).length) + 1) ≤
          c * (Fl (κ x) + 1) * ((encP x).length + 1) ^ C :=
        (Nat.mul_le_mul_left c hlen1).trans hterm2
      have h1 := hsup_t.trans hterm1
      rw [Nat.add_mul]; omega
    calc (r x + 1) * ((Finset.Iic (r x)).sup
            (fun n ↦ (5 * Ff (κf (fP^[n] x).1) + c0) * ((encP (fP^[n] x)).length + 1) ^ cf) +
            c * ((Finset.Iic (r x)).sup (fun n ↦ (encP (fP^[n] x)).length) + 1))
        ≤ (Fr (κ x) + 1) * (((5 * Fmono (h (κ x)) + c0) * (Fl (κ x) + 1) ^ cf +
            c * (Fl (κ x) + 1)) * ((encP x).length + 1) ^ C) := Nat.mul_le_mul hr1 hinner
      _ = F (κ x) * ((encP x).length + 1) ^ C := by dsimp only [F]; ring
  exact computableInFPTTime_congr hFPT fun x ↦ Subtype.ext (hfP_iter (r x) x)

private theorem computableInPolyTime_congr {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {f g : α → β} (hf : ComputableInPolyTime f encA encB)
    (h : ∀ a, f a = g a) : ComputableInPolyTime g encA encB := by
  have heq : f = g := funext h
  exact heq ▸ hf

private theorem encOption_none_eq {α : Type} (enc : α ↪ List Bool) :
    encOption enc none = [] := rfl

private theorem encOption_some_eq {α : Type} (enc : α ↪ List Bool) (a : α) :
    encOption enc (some a) = true :: enc a := rfl

private theorem testBit_add_two_pow_of_lt {i d j : ℕ} (hj : j < d) :
    (i + 2 ^ d).testBit j = i.testBit j := by
  rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have hd : 2 ^ d = 2 ^ (d - j) * 2 ^ j := by rw [← Nat.pow_add, Nat.sub_add_cancel hj.le]
  have hd2 : 2 ^ (d - j) = 2 * 2 ^ (d - j - 1) := by
    conv_lhs => rw [show d - j = (d - j - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  rw [hd, Nat.add_mul_div_right _ _ (Nat.two_pow_pos j), hd2]
  have : (i / 2 ^ j + 2 * 2 ^ (d - j - 1)) % 2 = (i / 2 ^ j) % 2 := by omega
  simp [this]

private theorem nodup_of_toFinset_card_eq {l : List ℕ} (h : l.toFinset.card = l.length) :
    l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    by_cases ha : a ∈ t
    · have h1 : (a :: t).toFinset = t.toFinset := by
        ext x; simp only [List.mem_toFinset, List.mem_cons]
        exact ⟨fun hx ↦ hx.elim (· ▸ ha) id, Or.inr⟩
      rw [h1, List.length_cons] at h
      have h2 := List.toFinset_card_le t
      omega
    · rw [List.toFinset_cons, Finset.card_insert_of_notMem (by simpa using ha),
        List.length_cons] at h
      exact List.nodup_cons.mpr ⟨ha, ih (by omega)⟩

/-- Iterating a polynomial-time function `f : α → α` on an `f`-invariant subtype `Subtype P` until
`enc (f^[n + 1] x) = []` runs in FPT time whenever the iteration count `r x` and all intermediate
encoding lengths are bounded by `F (κ x) * (|enc x| + 1) ^ c`. -/
theorem computableInFPTTime_iterateWhile_on {α : Type} {f : α → α} {enc : α ↪ List Bool}
    (hf : ComputableInPolyTime f enc enc) {P : α → Prop} (hP : ∀ a, P a → P (f a))
    {κ : Subtype P → ℕ} {r : Subtype P → ℕ}
    (hr : ∀ x : Subtype P, IsLeast {n | enc (f^[n + 1] x.1) = []} (r x))
    {Fr Fl : ℕ → ℕ} {cl : ℕ}
    (hFr : ∀ x, r x ≤ Fr (κ x))
    (hFl : ∀ x, ∀ n ≤ r x, (enc (f^[n] x.1)).length ≤ Fl (κ x) * ((enc x.1).length + 1) ^ cl) :
    ComputableInFPTTime (fun x : Subtype P ↦ (⟨f^[r x] x.1, by
      have : ∀ m, P (f^[m] x.1) := fun m ↦ by
        induction m with
        | zero => exact x.2
        | succ m ih => rw [Function.iterate_succ_apply']; exact hP _ ih
      exact this (r x)⟩ : Subtype P))
      ((Function.Embedding.subtype P).trans enc)
      ((Function.Embedding.subtype P).trans enc) κ := by
  let encP : Subtype P ↪ List Bool := (Function.Embedding.subtype P).trans enc
  let fP : Subtype P → Subtype P := fun x ↦ ⟨f x.1, hP x.1 x.2⟩
  have hfP_iter : ∀ (m : ℕ) (x : Subtype P), (fP^[m] x).1 = f^[m] x.1 := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      dsimp only [fP]
      rw [ih x]
  obtain ⟨t, s, ht, hs, hts⟩ := hf
  obtain ⟨ct, dt, ht_le⟩ := Cslib.polynomiallyBounded_iff_le.mp ht
  obtain ⟨cs, ds, hs_le⟩ := Cslib.polynomiallyBounded_iff_le.mp hs
  obtain ⟨c0, htidy0⟩ := hts.exists_computableTidilyInTimeAndSpace
  let D : ℕ := max dt ds
  let C0 : ℕ := 2 * ct + 3 * cs + c0
  have htidy : ComputableTidilyInTimeAndSpace f enc enc
      (fun a ↦ C0 * ((enc a).length + 1) ^ D)
      (fun a ↦ c0 * (s (enc a).length + 1)) := by
    refine htidy0.mono (fun a ↦ ?_) (fun _ ↦ le_rfl)
    have h1 : t (enc a).length ≤ ct * ((enc a).length + 1) ^ D :=
      (ht_le _).trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)))
    have h2 : s (enc a).length ≤ cs * ((enc a).length + 1) ^ D :=
      (hs_le _).trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right _ _)))
    have h3 : c0 ≤ c0 * ((enc a).length + 1) ^ D :=
      Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (Nat.succ_pos _))
    dsimp only [C0]
    nlinarith
  have htidyP : ComputableTidilyInTimeAndSpace fP encP encP
      (fun x ↦ C0 * ((encP x).length + 1) ^ D)
      (fun x ↦ c0 * (s (encP x).length + 1)) := by
    obtain ⟨k, State, hFin, tm, htm⟩ := htidy
    exact ⟨k, State, hFin, tm, fun x ↦ htm x.1⟩
  have hrP : ∀ x : Subtype P, IsLeast {n | encP (fP^[n + 1] x) = []} (r x) := by
    intro x
    simpa only [encP, Function.Embedding.trans_apply, Function.Embedding.coe_subtype,
      hfP_iter] using hr x
  obtain ⟨c, hiter⟩ := ComputableTidilyInTimeAndSpace.iterateWhile htidyP hrP
  let F : ℕ → ℕ := fun k ↦ (Fr k + 1) * (C0 * (Fl k + 1) ^ D + c * (Fl k + 1))
  let C : ℕ := cl * D + cl
  have hFPT : ComputableInFPTTime (fun x : Subtype P ↦ fP^[r x] x) encP encP κ := by
    refine (ComputableInTimeAndSpace.mono
      (ComputableTidilyInTimeAndSpace.computableInTimeAndSpace hiter)
      (t' := fun x ↦ F (κ x) * ((encP x).length + 1) ^ C)
      (fun x ↦ ?_) (fun _ ↦ le_rfl)).computableInFPTTime
    have hP1 : 1 ≤ ((encP x).length + 1) ^ cl := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have hsup_len : (Finset.Iic (r x)).sup (fun n ↦ (encP (fP^[n] x)).length) ≤
        Fl (κ x) * ((encP x).length + 1) ^ cl := by
      refine Finset.sup_le fun n hn ↦ ?_
      have := hFl x n (Finset.mem_Iic.mp hn)
      simpa only [encP, Function.Embedding.trans_apply, Function.Embedding.coe_subtype,
        hfP_iter] using this
    have hsup_t : (Finset.Iic (r x)).sup
        (fun n ↦ C0 * ((encP (fP^[n] x)).length + 1) ^ D) ≤
        C0 * (Fl (κ x) + 1) ^ D * (((encP x).length + 1) ^ cl) ^ D := by
      refine Finset.sup_le fun n hn ↦ ?_
      have hl : (encP (fP^[n] x)).length ≤ Fl (κ x) * ((encP x).length + 1) ^ cl := by
        have := hFl x n (Finset.mem_Iic.mp hn)
        simpa only [encP, Function.Embedding.trans_apply, Function.Embedding.coe_subtype,
          hfP_iter] using this
      have h1 : (encP (fP^[n] x)).length + 1 ≤ (Fl (κ x) + 1) * ((encP x).length + 1) ^ cl := by
        nlinarith
      calc C0 * ((encP (fP^[n] x)).length + 1) ^ D
          ≤ C0 * ((Fl (κ x) + 1) * ((encP x).length + 1) ^ cl) ^ D :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 D)
        _ = C0 * (Fl (κ x) + 1) ^ D * (((encP x).length + 1) ^ cl) ^ D := by
            rw [Nat.mul_pow, Nat.mul_assoc]
    have hlen1 : (Finset.Iic (r x)).sup (fun n ↦ (encP (fP^[n] x)).length) + 1 ≤
        (Fl (κ x) + 1) * ((encP x).length + 1) ^ cl := by nlinarith
    have hpow : (((encP x).length + 1) ^ cl) ^ D * ((encP x).length + 1) ^ cl =
        ((encP x).length + 1) ^ C := by
      dsimp only [C]; rw [← Nat.pow_mul, ← Nat.pow_add]
    have hterm1 : C0 * (Fl (κ x) + 1) ^ D * (((encP x).length + 1) ^ cl) ^ D ≤
        C0 * (Fl (κ x) + 1) ^ D * ((encP x).length + 1) ^ C := by
      rw [← hpow, ← Nat.mul_assoc]
      exact Nat.le_mul_of_pos_right _ hP1
    have hterm2 : c * ((Fl (κ x) + 1) * ((encP x).length + 1) ^ cl) ≤
        c * (Fl (κ x) + 1) * ((encP x).length + 1) ^ C := by
      rw [← hpow]
      have hsub : ((encP x).length + 1) ^ cl ≤
          (((encP x).length + 1) ^ cl) ^ D * ((encP x).length + 1) ^ cl := by
        have : 1 ≤ (((encP x).length + 1) ^ cl) ^ D := Nat.one_le_pow _ _ hP1
        nlinarith
      have hmul := Nat.mul_le_mul_left (c * (Fl (κ x) + 1)) hsub
      simpa [Nat.mul_assoc] using hmul
    have hr1 : r x + 1 ≤ Fr (κ x) + 1 := Nat.add_le_add_right (hFr x) 1
    have hinner : (Finset.Iic (r x)).sup (fun n ↦ C0 * ((encP (fP^[n] x)).length + 1) ^ D) +
        c * ((Finset.Iic (r x)).sup (fun n ↦ (encP (fP^[n] x)).length) + 1) ≤
        (C0 * (Fl (κ x) + 1) ^ D + c * (Fl (κ x) + 1)) * ((encP x).length + 1) ^ C := by
      have h2 : c * ((Finset.Iic (r x)).sup (fun n ↦ (encP (fP^[n] x)).length) + 1) ≤
          c * (Fl (κ x) + 1) * ((encP x).length + 1) ^ C :=
        (Nat.mul_le_mul_left c hlen1).trans hterm2
      have h1 : (Finset.Iic (r x)).sup (fun n ↦ C0 * ((encP (fP^[n] x)).length + 1) ^ D) ≤
          C0 * (Fl (κ x) + 1) ^ D * ((encP x).length + 1) ^ C := hsup_t.trans hterm1
      rw [Nat.add_mul]; omega
    calc (r x + 1) * ((Finset.Iic (r x)).sup
            (fun n ↦ C0 * ((encP (fP^[n] x)).length + 1) ^ D) +
            c * ((Finset.Iic (r x)).sup (fun n ↦ (encP (fP^[n] x)).length) + 1))
        ≤ (Fr (κ x) + 1) * ((C0 * (Fl (κ x) + 1) ^ D + c * (Fl (κ x) + 1)) *
            ((encP x).length + 1) ^ C) := Nat.mul_le_mul hr1 hinner
      _ = F (κ x) * ((encP x).length + 1) ^ C := by dsimp only [F]; ring
  exact computableInFPTTime_congr hFPT fun x ↦ Subtype.ext (hfP_iter (r x) x)

/-- Unbounded linear search returning the first `y` with `step (a, i) = some y`. -/
noncomputable def searchUnbounded {α β : Type} (step : α × ℕ → Option β)
    (hex : ∀ a, ∃ i, (step (a, i)).isSome) (a : α) : β :=
  (step (a, Nat.find (hex a))).get (Nat.find_spec (hex a))

/-- Unbounded linear search is computable in FPT time whenever the witness index `Nat.find` is
bounded by `F (κ a)`. -/
theorem computableInFPTTime_searchUnbounded {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {κ : α → ℕ} {step : α × ℕ → Option β}
    (hstep : ComputableInPolyTime step (encPair encA encNat) (encOption encB))
    (hex : ∀ a, ∃ i, (step (a, i)).isSome)
    {F : ℕ → ℕ} (hF : ∀ a, Nat.find (hex a) ≤ F (κ a)) :
    ComputableInFPTTime (searchUnbounded step hex) encA encB κ := by
  classical
  rcases isEmpty_or_nonempty α with hempty | hne_a
  · have : Fintype α := Fintype.ofIsEmpty
    exact (ComputableInPolyTime.of_finite (searchUnbounded step hex)).computableInFPTTime κ
  let a₀ : α := Classical.choice hne_a
  let b₀ : β := searchUnbounded step hex a₀
  let S := Option ((α × ℕ) × Option β)
  let encS : S ↪ List Bool := encOption (encPair (encPair encA encNat) (encOption encB))
  let nextS : S → S := fun s ↦
    s.elim none fun p ↦ p.2.elim (some ((p.1.1, p.1.2 + 1), step p.1)) fun _ ↦ none
  have hnext : ComputableInPolyTime nextS encS encS := by
    have hbody : ComputableInPolyTime
        (fun q : S × ((α × ℕ) × Option β) ↦
          q.2.2.elim (some ((q.2.1.1, q.2.1.2 + 1), step q.2.1)) fun _ ↦ none)
        (encPair encS (encPair (encPair encA encNat) (encOption encB))) encS := by
      have hp := snd encS (encPair (encPair encA encNat) (encOption encB))
      have hp1 := (fst (encPair encA encNat) (encOption encB)).comp hp
      have hp2 := (snd (encPair encA encNat) (encOption encB)).comp hp
      have ha := (fst encA encNat).comp hp1
      have hi := (snd encA encNat).comp hp1
      have hnone : ComputableInPolyTime
          (fun q : S × ((α × ℕ) × Option β) ↦ some ((q.2.1.1, q.2.1.2 + 1), step q.2.1))
          (encPair encS (encPair (encPair encA encNat) (encOption encB))) encS :=
        (optionSome _).comp ((ha.prod (binary_add' hi (const 1))).prod (hstep.comp hp1))
      exact optionElimWithInput (body := fun _ (_ : β) ↦ (none : S)) hp2 hnone (const none)
    have hres := optionElimWithInput (value := id) (fallback := fun _ ↦ (none : S))
      (body := fun (_ : S) (p : (α × ℕ) × Option β) ↦
        p.2.elim (some ((p.1.1, p.1.2 + 1), step p.1)) fun _ ↦ none)
      id' (const none) hbody
    simpa [nextS] using hres
  have hiter_eq : ∀ a n, n ≤ Nat.find (hex a) →
      nextS^[n] (some ((a, 0), none)) = some ((a, n), none) := by
    intro a n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [Function.iterate_succ_apply', ih (by omega)]
      have hne : step (a, n) = none := by
        have hlt := Nat.find_min (hex a) (m := n) (by omega)
        cases h : step (a, n) with
        | none => rfl
        | some y => simp [h] at hlt
      simp [nextS, hne]
  have hiter_last : ∀ a,
      nextS^[Nat.find (hex a) + 1] (some ((a, 0), none)) =
        some ((a, Nat.find (hex a) + 1), step (a, Nat.find (hex a))) := by
    intro a
    rw [Function.iterate_succ_apply', hiter_eq a _ le_rfl]
    rfl
  have hiter_done : ∀ a, nextS^[Nat.find (hex a) + 2] (some ((a, 0), none)) = none := by
    intro a
    rw [show Nat.find (hex a) + 2 = (Nat.find (hex a) + 1) + 1 by omega,
      Function.iterate_succ_apply', hiter_last a]
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (Nat.find_spec (hex a))
    simp [nextS, hy]
  let P : S → Prop := fun s ↦
    (∃ a, ∃ n ≤ Nat.find (hex a) + 1, s = nextS^[n] (some ((a, 0), none))) ∨ s = none
  have hP : ∀ s, P s → P (nextS s) := by
    intro s hs
    rcases hs with ⟨a, n, hn, rfl⟩ | rfl
    · rcases Nat.eq_or_lt_of_le hn with rfl | hlt
      · right; simpa [← Function.iterate_succ_apply'] using hiter_done a
      · left; exact ⟨a, n + 1, by omega, (Function.iterate_succ_apply' nextS n _).symm⟩
    · right; rfl
  let rP : Subtype P → ℕ := fun x ↦
    match x.1 with
    | none => 0
    | some p => Nat.find (hex p.1.1) + 1 - p.1.2
  let κP : Subtype P → ℕ := fun x ↦
    match x.1 with
    | none => 0
    | some p => κ p.1.1
  have hrP_spec : ∀ a n (hn : n ≤ Nat.find (hex a) + 1),
      rP ⟨nextS^[n] (some ((a, 0), none)), Or.inl ⟨a, n, hn, rfl⟩⟩ =
        Nat.find (hex a) + 1 - n := by
    intro a n hn
    dsimp only [rP]
    rcases Nat.eq_or_lt_of_le hn with rfl | hlt
    · rw [hiter_last]
    · rw [hiter_eq a n (by omega)]
  have hκP_spec : ∀ a n (hn : n ≤ Nat.find (hex a) + 1),
      κP ⟨nextS^[n] (some ((a, 0), none)), Or.inl ⟨a, n, hn, rfl⟩⟩ = κ a := by
    intro a n hn
    dsimp only [κP]
    rcases Nat.eq_or_lt_of_le hn with rfl | hlt
    · rw [hiter_last]
    · rw [hiter_eq a n (by omega)]
  have hr : ∀ x : Subtype P, IsLeast {m | encS (nextS^[m + 1] x.1) = []} (rP x) := by
    intro x
    rcases x with ⟨s, hs⟩
    rcases hs with ⟨a, n, hn, rfl⟩ | rfl
    · rw [hrP_spec a n hn]
      refine ⟨?_, ?_⟩
      · change encS (nextS^[Nat.find (hex a) + 1 - n + 1] (nextS^[n] (some ((a, 0), none)))) = []
        rw [← Function.iterate_add_apply,
          show Nat.find (hex a) + 1 - n + 1 + n = Nat.find (hex a) + 2 by omega, hiter_done]
        rfl
      · intro m hm
        change encS (nextS^[m + 1] (nextS^[n] (some ((a, 0), none)))) = [] at hm
        rw [← Function.iterate_add_apply] at hm
        by_contra hlt; push Not at hlt
        have hle : m + 1 + n ≤ Nat.find (hex a) + 1 := by omega
        rcases Nat.eq_or_lt_of_le hle with heq | hlt'
        · rw [heq, hiter_last] at hm
          have : encS (some ((a, Nat.find (hex a) + 1), step (a, Nat.find (hex a)))) =
              true :: _ := encOption_some_eq _ _
          rw [this] at hm; simp at hm
        · rw [hiter_eq a _ (by omega)] at hm
          have : encS (some ((a, m + 1 + n), none)) = true :: _ := encOption_some_eq _ _
          rw [this] at hm; simp at hm
    · have hr0 : rP ⟨none, Or.inr rfl⟩ = 0 := by simp [rP]
      rw [hr0]
      exact ⟨by change encS none = []; rfl, fun m _ ↦ Nat.zero_le m⟩
  obtain ⟨c_step, d_step, hstep_len⟩ := hstep.polyBounded_length.exists_le
  let Fl : ℕ → ℕ := fun k ↦ 10 * (F k + c_step * (3 * (F k + 2)) ^ d_step + 10)
  have hFl : ∀ x : Subtype P, ∀ m ≤ rP x,
      (encS (nextS^[m] x.1)).length ≤ Fl (κP x) * ((encS x.1).length + 1) ^ (d_step + 1) := by
    intro x m hm
    rcases x with ⟨s, hs⟩
    rcases hs with ⟨a, n, hn, rfl⟩ | rfl
    · rw [hκP_spec a n hn]
      rw [hrP_spec a n hn] at hm
      rw [← Function.iterate_add_apply]
      have hmn : m + n ≤ Nat.find (hex a) + 1 := by omega
      have hnat_len : ∀ j : ℕ, (encNat j).length ≤ j + 1 := fun j ↦ by
        rw [encNat_apply, Nat.size_eq_bits_len]
        have := Nat.size_le_self j; omega
      have hlen_a : (encA a).length ≤ (encS (nextS^[n] (some ((a, 0), none)))).length := by
        rcases Nat.eq_or_lt_of_le hn with rfl | hlt
        · rw [hiter_last]
          dsimp only [encS]
          rw [encOption_some_eq, List.length_cons]
          calc (encA a).length
              ≤ (encPair encA encNat (a, Nat.find (hex a) + 1)).length :=
                length_le_encPair_left encA encNat (a, Nat.find (hex a) + 1)
            _ ≤ (encPair (encPair encA encNat) (encOption encB)
                  ((a, Nat.find (hex a) + 1), step (a, Nat.find (hex a)))).length :=
                length_le_encPair_left (encPair encA encNat) (encOption encB)
                  ((a, Nat.find (hex a) + 1), step (a, Nat.find (hex a)))
            _ ≤ _ := Nat.le_succ _
        · rw [hiter_eq a n (by omega)]
          dsimp only [encS]
          rw [encOption_some_eq, List.length_cons]
          calc (encA a).length
              ≤ (encPair encA encNat (a, n)).length := length_le_encPair_left encA encNat (a, n)
            _ ≤ (encPair (encPair encA encNat) (encOption encB) ((a, n), none)).length :=
                length_le_encPair_left (encPair encA encNat) (encOption encB) ((a, n), none)
            _ ≤ _ := Nat.le_succ _
      have hpair_a : ∀ j ≤ F (κ a) + 1,
          (encPair encA encNat (a, j)).length ≤
            (2 * (F (κ a) + 2)) * ((encA a).length + 1) := by
        intro j hj
        rw [length_encPair]
        have := hnat_len j
        nlinarith
      have hpow1 : (encA a).length + 1 ≤
          ((encS (nextS^[n] (some ((a, 0), none)))).length + 1) ^ (d_step + 1) := by
        have hle1 : (encA a).length + 1 ≤
            (encS (nextS^[n] (some ((a, 0), none)))).length + 1 := by omega
        exact hle1.trans (by
          simpa using Nat.pow_le_pow_right (Nat.succ_pos _) (show 1 ≤ d_step + 1 by omega))
      have hpowd : ((encA a).length + 1) ^ d_step ≤
          ((encS (nextS^[n] (some ((a, 0), none)))).length + 1) ^ (d_step + 1) := by
        have hle1 : (encA a).length + 1 ≤
            (encS (nextS^[n] (some ((a, 0), none)))).length + 1 := by omega
        exact (Nat.pow_le_pow_left hle1 d_step).trans
          (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
      have hpow0 : 1 ≤ ((encS (nextS^[n] (some ((a, 0), none)))).length + 1) ^ (d_step + 1) :=
        Nat.one_le_pow _ _ (Nat.succ_pos _)
      rcases Nat.eq_or_lt_of_le hmn with heq | hlt
      · rw [heq, hiter_last]
        have hlen_step : (encOption encB (step (a, Nat.find (hex a)))).length ≤
            c_step * ((encPair encA encNat (a, Nat.find (hex a))).length + 1) ^ d_step :=
          hstep_len (a, Nat.find (hex a))
        have hlen_p : (encPair encA encNat (a, Nat.find (hex a))).length + 1 ≤
            (3 * (F (κ a) + 2)) * ((encA a).length + 1) := by
          have := hpair_a (Nat.find (hex a)) (by have := hF a; omega)
          have hpos := Nat.succ_pos (encA a).length
          nlinarith
        have hstep_b : (encOption encB (step (a, Nat.find (hex a)))).length ≤
            c_step * (3 * (F (κ a) + 2)) ^ d_step * ((encA a).length + 1) ^ d_step := by
          calc (encOption encB (step (a, Nat.find (hex a)))).length
              ≤ c_step * ((encPair encA encNat (a, Nat.find (hex a))).length + 1) ^ d_step :=
                hlen_step
            _ ≤ c_step * ((3 * (F (κ a) + 2)) * ((encA a).length + 1)) ^ d_step :=
                Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlen_p _)
            _ = c_step * (3 * (F (κ a) + 2)) ^ d_step * ((encA a).length + 1) ^ d_step := by
                rw [Nat.mul_pow, Nat.mul_assoc]
        have hlen_eq :
            (encS (some ((a, Nat.find (hex a) + 1), step (a, Nat.find (hex a))))).length =
            1 + (2 * (encPair encA encNat (a, Nat.find (hex a) + 1)).length + 1 +
              (encOption encB (step (a, Nat.find (hex a)))).length) := by
          dsimp only [encS]
          rw [encOption_some_eq, List.length_cons, length_encPair]; dsimp only; omega
        rw [hlen_eq]
        have hp1 := hpair_a (Nat.find (hex a) + 1) (by have := hF a; omega)
        have hm1 : (encPair encA encNat (a, Nat.find (hex a) + 1)).length ≤
            2 * (F (κ a) + 2) *
              ((encS (nextS^[n] (some ((a, 0), none)))).length + 1) ^ (d_step + 1) :=
          hp1.trans (Nat.mul_le_mul_left _ hpow1)
        have hm2 : (encOption encB (step (a, Nat.find (hex a)))).length ≤
            c_step * (3 * (F (κ a) + 2)) ^ d_step *
              ((encS (nextS^[n] (some ((a, 0), none)))).length + 1) ^ (d_step + 1) :=
          hstep_b.trans (Nat.mul_le_mul_left _ hpowd)
        dsimp only [Fl]
        nlinarith
      · rw [hiter_eq a (m + n) (by omega)]
        have hlen_eq : (encS (some ((a, m + n), none))).length =
            1 + (2 * (encPair encA encNat (a, m + n)).length + 1) := by
          dsimp only [encS]
          rw [encOption_some_eq, List.length_cons, length_encPair, encOption_none_eq,
            List.length_nil]
          dsimp only; omega
        rw [hlen_eq]
        have hp1 := hpair_a (m + n) (by have := hF a; omega)
        have hm1 : (encPair encA encNat (a, m + n)).length ≤
            2 * (F (κ a) + 2) *
              ((encS (nextS^[n] (some ((a, 0), none)))).length + 1) ^ (d_step + 1) :=
          hp1.trans (Nat.mul_le_mul_left _ hpow1)
        have hFl_ge : 10 * (F (κ a) + 10) ≤ Fl (κ a) := by dsimp only [Fl]; omega
        have hFl_mul :
            10 * (F (κ a) + 10) *
              ((encS (nextS^[n] (some ((a, 0), none)))).length + 1) ^ (d_step + 1) ≤
            Fl (κ a) *
              ((encS (nextS^[n] (some ((a, 0), none)))).length + 1) ^ (d_step + 1) :=
          Nat.mul_le_mul_right _ hFl_ge
        nlinarith
    · have hr0 : rP ⟨none, Or.inr rfl⟩ = 0 := by simp [rP]
      rw [hr0] at hm
      have hm0 : m = 0 := by omega
      subst hm0
      have h0 : (encS none).length = 0 := by
        dsimp only [encS]; rw [encOption_none_eq, List.length_nil]
      simp [h0]
  have hiter := computableInFPTTime_iterateWhile_on hnext hP hr
    (Fr := fun k ↦ F k + 1) (Fl := Fl) (cl := d_step + 1)
    (fun x ↦ by
      rcases x with ⟨s, hs⟩
      rcases hs with ⟨a, n, hn, rfl⟩ | rfl
      · rw [hrP_spec a n hn, hκP_spec a n hn]; have := hF a; omega
      · simp [rP])
    hFl
  let encP : Subtype P ↪ List Bool := (Function.Embedding.subtype P).trans encS
  let init : α → Subtype P := fun a ↦ ⟨some ((a, 0), none), Or.inl ⟨a, 0, Nat.zero_le _, rfl⟩⟩
  have hinit : ComputableInPolyTime init encA encP := by
    have h1 : ComputableInPolyTime (fun a : α ↦ (some ((a, 0), none) : S)) encA encS :=
      (optionSome _).comp ((id'.prod (const 0)).prod (const none))
    obtain ⟨t, s, ht, hs, k, State, hFin, tm, htm⟩ := h1
    exact ⟨t, s, ht, hs, k, State, hFin, tm, fun a ↦ htm a⟩
  let extract : Subtype P → β := fun x ↦
    x.1.elim b₀ fun p ↦ p.2.getD b₀
  have hextract : ComputableInPolyTime extract encP encB := by
    have h1 : ComputableInPolyTime (fun s : S ↦ s.elim b₀ fun p ↦ p.2.getD b₀) encS encB := by
      have hbody : ComputableInPolyTime
          (fun q : S × ((α × ℕ) × Option β) ↦ q.2.2.getD b₀)
          (encPair encS (encPair (encPair encA encNat) (encOption encB))) encB :=
        optionGetDWithInput
          ((snd (encPair encA encNat) (encOption encB)).comp (snd encS _)) (const b₀)
      exact optionElimWithInput id' (const b₀) hbody
    obtain ⟨t, s, ht, hs, k, State, hFin, tm, htm⟩ := h1
    exact ⟨t, s, ht, hs, k, State, hFin, tm, fun x ↦ htm x.1⟩
  have hcomp : ComputableInFPTTime
      (fun a ↦ extract ((fun x : Subtype P ↦ (⟨nextS^[rP x] x.1, by
        have : ∀ m, P (nextS^[m] x.1) := fun m ↦ by
          induction m with
          | zero => exact x.2
          | succ m ih => rw [Function.iterate_succ_apply']; exact hP _ ih
        exact this (rP x)⟩ : Subtype P)) (init a))) encA encB κ := by
    have hstep1 : ComputableInFPTTime
        (fun a ↦ (⟨nextS^[rP (init a)] (init a).1, _⟩ : Subtype P)) encA encP κ :=
      hiter.comp (hinit.computableInFPTTime κ) (h := id) (fun a ↦ by
        have := hκP_spec a 0 (Nat.zero_le _)
        exact this.le)
    exact (hextract.computableInFPTTime κP).comp hstep1 (h := id) fun a ↦ by
      have hr0 : rP (init a) = Nat.find (hex a) + 1 := by
        simpa [init] using hrP_spec a 0 (Nat.zero_le _)
      change κP ⟨nextS^[rP (init a)] (some ((a, 0), none)), _⟩ ≤ κ a
      rw [hr0]
      exact (hκP_spec a _ le_rfl).le
  refine computableInFPTTime_congr hcomp fun a ↦ ?_
  have hr0 : rP (init a) = Nat.find (hex a) + 1 := by
    simpa [init] using hrP_spec a 0 (Nat.zero_le _)
  dsimp only [extract]
  change (nextS^[rP (init a)] (some ((a, 0), none))).elim b₀ (fun p ↦ p.2.getD b₀) = _
  rw [hr0, hiter_last a]
  simp only [Option.elim_some, searchUnbounded]
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (Nat.find_spec (hex a))
  simp [hy]

/-- Bounded linear search returning the first `y` with `step (a, i) = some y` and `i < bound a`,
or `none` if no such `i` exists. -/
def searchFirst {α β : Type} (step : α × ℕ → Option β) (bound : α → ℕ) (a : α) : Option β :=
  (List.range (bound a)).findSome? fun i ↦ step (a, i)

/-- Bounded linear search with bound `0` returns `none`. -/
@[simp]
theorem searchFirst_zero {α β : Type} (step : α × ℕ → Option β) (a : α) :
    searchFirst step (fun _ ↦ 0) a = none := by
  unfold searchFirst
  rw [List.range_zero, List.findSome?_nil]

theorem searchFirst_eq_some_iff {α β : Type} {step : α × ℕ → Option β} {bound : α → ℕ}
    {a : α} {y : β} :
    searchFirst step bound a = some y ↔
      ∃ i < bound a, step (a, i) = some y ∧ ∀ j < i, step (a, j) = none := by
  unfold searchFirst
  constructor
  · intro h
    have hex : ∃ i ∈ List.range (bound a), (step (a, i)).isSome := by
      have hne : ((List.range (bound a)).findSome? fun i ↦ step (a, i)).isSome := by simp [h]
      rw [List.isSome_findSome?] at hne
      simpa using hne
    classical
    let i₀ := Nat.find hex
    obtain ⟨hi₀_mem, hi₀_some⟩ := Nat.find_spec hex
    have hi₀_lt : i₀ < bound a := List.mem_range.mp hi₀_mem
    have hnone_before : ∀ j < i₀, step (a, j) = none := by
      intro j hj
      have hmin := Nat.find_min hex hj
      push Not at hmin
      have := hmin (List.mem_range.mpr (hj.trans hi₀_lt))
      cases hstep : step (a, j) with
      | none => rfl
      | some z => simp [hstep] at this
    have hfind_eq : (List.range (bound a)).findSome? (fun i ↦ step (a, i)) = step (a, i₀) := by
      have hsplit : List.range (bound a) =
          List.range i₀ ++ i₀ :: (List.range (bound a)).drop (i₀ + 1) := by
        have hlen : i₀ < (List.range (bound a)).length := by simp [hi₀_lt]
        have h1 : (List.range (bound a)).take i₀ = List.range i₀ := by
          rw [List.take_range]; exact congrArg List.range (Nat.min_eq_left hi₀_lt.le)
        have h2 : (List.range (bound a))[i₀] = i₀ := List.getElem_range hlen
        conv_lhs => rw [← List.take_append_drop i₀ (List.range (bound a))]
        rw [h1, List.drop_eq_getElem_cons hlen, h2]
      rw [hsplit, List.findSome?_append]
      have hpre : (List.range i₀).findSome? (fun i ↦ step (a, i)) = none := by
        rw [List.findSome?_eq_none_iff]
        intro j hj
        exact hnone_before j (List.mem_range.mp hj)
      rw [hpre, Option.none_or, List.findSome?_cons]
      have hi₀_some' : (step (a, i₀)).isSome = true := hi₀_some
      cases hs : step (a, i₀) with
      | none => simp [hs] at hi₀_some'
      | some z => rfl
    rw [hfind_eq] at h
    exact ⟨i₀, hi₀_lt, h, hnone_before⟩
  · rintro ⟨i, hi, hstep_i, hnone⟩
    have hsplit : List.range (bound a) =
        List.range i ++ i :: (List.range (bound a)).drop (i + 1) := by
      have hlen : i < (List.range (bound a)).length := by simp [hi]
      have h1 : (List.range (bound a)).take i = List.range i := by
        rw [List.take_range]; exact congrArg List.range (Nat.min_eq_left hi.le)
      have h2 : (List.range (bound a))[i] = i := List.getElem_range hlen
      conv_lhs => rw [← List.take_append_drop i (List.range (bound a))]
      rw [h1, List.drop_eq_getElem_cons hlen, h2]
    rw [hsplit, List.findSome?_append]
    have hpre : (List.range i).findSome? (fun j ↦ step (a, j)) = none := by
      rw [List.findSome?_eq_none_iff]
      intro j hj
      exact hnone j (List.mem_range.mp hj)
    rw [hpre, Option.none_or, List.findSome?_cons, hstep_i]

theorem searchFirst_isSome_iff {α β : Type} {step : α × ℕ → Option β} {bound : α → ℕ} {a : α} :
    (searchFirst step bound a).isSome ↔ ∃ i < bound a, (step (a, i)).isSome := by
  unfold searchFirst
  rw [List.isSome_findSome?]
  simp [List.mem_range]

/-- Bounded linear search `searchFirst` is computable in FPT time whenever `bound a ≤ F (κ a)`. -/
theorem computableInFPTTime_searchFirst {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {κ : α → ℕ} {step : α × ℕ → Option β} {bound : α → ℕ}
    (hstep : ComputableInPolyTime step (encPair encA encNat) (encOption encB))
    (hbound : ComputableInPolyTime bound encA encNat)
    {F : ℕ → ℕ} (hF : ∀ a, bound a ≤ F (κ a)) :
    ComputableInFPTTime (searchFirst step bound) encA (encOption encB) κ := by
  let step' : α × ℕ → Option (Option β) := fun p ↦
    if p.2 < bound p.1 then (step p).map some else some none
  have hstep' : ComputableInPolyTime step' (encPair encA encNat)
      (encOption (encOption encB)) := by
    have hcond : ComputableInPolyTime (fun p : α × ℕ ↦ decide (p.2 < bound p.1))
        (encPair encA encNat) encBool :=
      binary_lt' (snd encA encNat) (hbound.comp (fst encA encNat))
    have hthen : ComputableInPolyTime (fun p : α × ℕ ↦ (step p).map some)
        (encPair encA encNat) (encOption (encOption encB)) :=
      optionMapWithInput hstep ((optionSome encB).comp (snd (encPair encA encNat) encB))
    exact computableInPolyTime_congr (ComputableInPolyTime.ite hcond hthen (const (some none)))
      fun p ↦ by simp [step']
  have hex' : ∀ a, ∃ i, (step' (a, i)).isSome := fun a ↦
    ⟨bound a, by simp [step']⟩
  have hF' : ∀ a, Nat.find (hex' a) ≤ F (κ a) := fun a ↦
    (Nat.find_min' (hex' a) (by simp [step'])).trans (hF a)
  refine computableInFPTTime_congr (computableInFPTTime_searchUnbounded hstep' hex' hF') fun a ↦ ?_
  have hfind_le : Nat.find (hex' a) ≤ bound a := Nat.find_min' (hex' a) (by simp [step'])
  rcases Nat.eq_or_lt_of_le hfind_le with heq | hlt
  · have hnone : ∀ j < bound a, step (a, j) = none := by
      intro j hj
      have hmin := Nat.find_min (hex' a) (heq.symm ▸ hj)
      simp only [step', hj, ↓reduceIte, Option.isSome_map] at hmin
      cases hs : step (a, j) with
      | none => rfl
      | some y => simp [hs] at hmin
    have hsf : searchFirst step bound a = none := by
      unfold searchFirst
      rw [List.findSome?_eq_none_iff]
      intro j hj
      exact hnone j (List.mem_range.mp hj)
    rw [hsf]
    simp [searchUnbounded, step', heq]
  · have hspec := Nat.find_spec (hex' a)
    simp only [step', hlt, ↓reduceIte, Option.isSome_map] at hspec
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hspec
    have hnone : ∀ j < Nat.find (hex' a), step (a, j) = none := by
      intro j hj
      have hmin := Nat.find_min (hex' a) hj
      have hj' : j < bound a := hj.trans hlt
      simp only [step', hj', ↓reduceIte, Option.isSome_map] at hmin
      cases hs : step (a, j) with
      | none => rfl
      | some z => simp [hs] at hmin
    have hsf : searchFirst step bound a = some y :=
      searchFirst_eq_some_iff.mpr ⟨Nat.find (hex' a), hlt, hy, hnone⟩
    rw [hsf]
    simp [searchUnbounded, step', hlt, hy]

/-- Bounded existential search over `i < bound a` with an FPT-time predicate `pred` runs in FPT
time whenever `bound a ≤ F (κ a)` and `κP (a, i) ≤ h (κ a)` for all `i ≤ bound a`. -/
theorem computableInFPTTime_anyRange {α : Type} {encA : α ↪ List Bool} {κ : α → ℕ}
    {pred : α × ℕ → Bool} {κP : α × ℕ → ℕ} {bound : α → ℕ}
    (hpred : ComputableInFPTTime pred (encPair encA encNat) encBool κP)
    (hbound : ComputableInPolyTime bound encA encNat)
    {F h : ℕ → ℕ} (hF : ∀ a, bound a ≤ F (κ a))
    (hκ : ∀ a i, i ≤ bound a → κP (a, i) ≤ h (κ a)) :
    ComputableInFPTTime (fun a ↦ (List.range (bound a)).any fun i ↦ pred (a, i))
      encA encBool κ := by
  classical
  rcases isEmpty_or_nonempty α with hempty | hne_a
  · have : Fintype α := Fintype.ofIsEmpty
    exact (ComputableInPolyTime.of_finite _).computableInFPTTime κ
  let a₀ : α := Classical.choice hne_a
  let S := Option ((α × ℕ) × Bool)
  let encS : S ↪ List Bool := encOption (encPair (encPair encA encNat) encBool)
  let extractP : S → α × ℕ := fun s ↦ s.elim (a₀, 0) Prod.fst
  let cond : S → Bool := fun s ↦ s.elim false fun p ↦ !p.2 && decide (p.1.2 < bound p.1.1)
  let nextS : S → S := fun s ↦
    if cond s then some (((extractP s).1, (extractP s).2 + 1), pred (extractP s)) else none
  let κS : S → ℕ := fun s ↦ κP (extractP s)
  have hextractP : ComputableInPolyTime extractP encS (encPair encA encNat) :=
    optionElimWithInput id' (const (a₀, 0)) ((fst _ _).comp (snd _ _))
  have hcond : ComputableInPolyTime cond encS encBool :=
    optionElimWithInput id' (const false)
      (bool_and' (bool_not.comp ((snd _ _).comp (snd _ _)))
        (binary_lt' ((snd _ _).comp ((fst _ _).comp (snd _ _)))
          (hbound.comp ((fst _ _).comp ((fst _ _).comp (snd _ _))))))
  have hnext : ComputableInFPTTime nextS encS encS κS := by
    have h1 : ComputableInPolyTime (fun s : S ↦ ((extractP s).1, (extractP s).2 + 1))
        encS (encPair encA encNat) :=
      ((fst _ _).comp hextractP).prod (binary_add' ((snd _ _).comp hextractP) (const 1))
    have h2 : ComputableInFPTTime (fun s : S ↦ pred (extractP s)) encS encBool κS :=
      hpred.comp (hextractP.computableInFPTTime κS) (h := id) fun _ ↦ le_rfl
    have hadv : ComputableInFPTTime
        (fun s : S ↦ (some (((extractP s).1, (extractP s).2 + 1), pred (extractP s)) : S))
        encS encS κS :=
      ((optionSome _).computableInFPTTime (fun _ ↦ 0)).comp
        (computableInFPTTime_prod (h1.computableInFPTTime κS) h2) (h := fun _ ↦ 0)
        fun _ ↦ Nat.zero_le _
    exact ComputableInFPTTime.ite (hcond.computableInFPTTime κS) hadv
      ((const (none : S)).computableInFPTTime κS)
  -- Track orbit `nextS^[n] (some ((a, 0), false))` up to first hit or `bound a`:
  let stopIdx (a : α) : ℕ :=
    if h : ∃ i < bound a, pred (a, i) = true then Nat.find h + 1 else bound a
  have hstop_le : ∀ a, stopIdx a ≤ bound a := fun a ↦ by
    dsimp only [stopIdx]
    split_ifs with h
    · have := (Nat.find_spec h).1; omega
    · exact le_rfl
  have hiter_pre : ∀ a n, n < stopIdx a →
      nextS^[n] (some ((a, 0), false)) = some ((a, n), false) := by
    intro a n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [Function.iterate_succ_apply', ih (by omega)]
      have hlt_b : n < bound a := lt_of_lt_of_le (Nat.lt_of_succ_lt hn) (hstop_le a)
      have hfalse : pred (a, n) = false := by
        dsimp only [stopIdx] at hn
        split_ifs at hn with hex
        · have hmin := Nat.find_min hex (by omega : n < Nat.find hex)
          cases hp : pred (a, n) with
          | false => rfl
          | true => exact absurd ⟨hlt_b, hp⟩ hmin
        · cases hp : pred (a, n) with
          | false => rfl
          | true => exact absurd ⟨n, hlt_b, hp⟩ hex
      simp [nextS, cond, extractP, hlt_b, hfalse]
  have hiter_stop : ∀ a,
      nextS^[stopIdx a] (some ((a, 0), false)) =
        some ((a, stopIdx a), (List.range (bound a)).any fun i ↦ pred (a, i)) := by
    intro a
    dsimp only [stopIdx]
    split_ifs with hex
    · have hspec := Nat.find_spec hex
      have hpre := hiter_pre a (Nat.find hex) (by simp [stopIdx, hex])
      rw [Function.iterate_succ_apply', hpre]
      have hany : ((List.range (bound a)).any fun i ↦ pred (a, i)) = true :=
        List.any_eq_true.mpr ⟨Nat.find hex, List.mem_range.mpr hspec.1, hspec.2⟩
      simp [nextS, cond, extractP, hspec.1, hspec.2, hany]
    · have hany : ((List.range (bound a)).any fun i ↦ pred (a, i)) = false := by
        cases h : (List.range (bound a)).any fun i ↦ pred (a, i) with
        | false => rfl
        | true =>
          obtain ⟨i, hi, hp⟩ := List.any_eq_true.mp h
          exact absurd ⟨i, List.mem_range.mp hi, hp⟩ hex
      cases hb : bound a with
      | zero => simp
      | succ m =>
        have hlt_stop : m < stopIdx a := by dsimp only [stopIdx]; rw [dite_eq_right hex, hb]; omega
        have hpre := hiter_pre a m hlt_stop
        rw [Function.iterate_succ_apply', hpre]
        have hm_lt : m < bound a := by omega
        have hm_f : pred (a, m) = false := by
          cases hp : pred (a, m) with
          | false => rfl
          | true => exact absurd ⟨m, hm_lt, hp⟩ hex
        rw [hb] at hany
        simp [nextS, cond, extractP, hm_lt, hm_f, hany]
  have hiter_done : ∀ a, nextS^[stopIdx a + 1] (some ((a, 0), false)) = none := by
    intro a
    rw [Function.iterate_succ_apply', hiter_stop a]
    dsimp only [stopIdx]
    split_ifs with hex
    · have hany : ((List.range (bound a)).any fun i ↦ pred (a, i)) = true :=
        List.any_eq_true.mpr ⟨Nat.find hex, List.mem_range.mpr (Nat.find_spec hex).1,
          (Nat.find_spec hex).2⟩
      simp [nextS, cond, hany]
    · simp [nextS, cond]
  let P : S → Prop := fun s ↦
    (∃ a, ∃ n ≤ stopIdx a, s = nextS^[n] (some ((a, 0), false))) ∨ s = none
  have hP : ∀ s, P s → P (nextS s) := by
    intro s hs
    rcases hs with ⟨a, n, hn, rfl⟩ | rfl
    · rcases Nat.eq_or_lt_of_le hn with rfl | hlt
      · right; simpa [← Function.iterate_succ_apply'] using hiter_done a
      · left; exact ⟨a, n + 1, by omega, (Function.iterate_succ_apply' nextS n _).symm⟩
    · right; simp [nextS, cond]
  have hstate_eq : ∀ a n, n ≤ stopIdx a →
      ∃ b : Bool, nextS^[n] (some ((a, 0), false)) = some ((a, n), b) := fun a n hn ↦ by
    rcases Nat.eq_or_lt_of_le hn with rfl | hlt
    · exact ⟨_, hiter_stop a⟩
    · exact ⟨false, hiter_pre a n hlt⟩
  let rP : Subtype P → ℕ := fun x ↦
    match x.1 with
    | none => 0
    | some p => stopIdx p.1.1 - p.1.2
  let κSub : Subtype P → ℕ := fun x ↦
    match x.1 with
    | none => 0
    | some p => κ p.1.1
  have hrP_spec : ∀ a n (hn : n ≤ stopIdx a),
      rP ⟨nextS^[n] (some ((a, 0), false)), Or.inl ⟨a, n, hn, rfl⟩⟩ = stopIdx a - n := by
    intro a n hn
    obtain ⟨b, hb⟩ := hstate_eq a n hn
    dsimp only [rP]; rw [hb]
  have hκSub_spec : ∀ a n (hn : n ≤ stopIdx a),
      κSub ⟨nextS^[n] (some ((a, 0), false)), Or.inl ⟨a, n, hn, rfl⟩⟩ = κ a := by
    intro a n hn
    obtain ⟨b, hb⟩ := hstate_eq a n hn
    dsimp only [κSub]; rw [hb]
  have hr : ∀ x : Subtype P, IsLeast {m | encS (nextS^[m + 1] x.1) = []} (rP x) := by
    intro x
    rcases x with ⟨s, hs⟩
    rcases hs with ⟨a, n, hn, rfl⟩ | rfl
    · rw [hrP_spec a n hn]
      refine ⟨?_, ?_⟩
      · change encS (nextS^[stopIdx a - n + 1] (nextS^[n] (some ((a, 0), false)))) = []
        rw [← Function.iterate_add_apply, show stopIdx a - n + 1 + n = stopIdx a + 1 by omega,
          hiter_done]
        rfl
      · intro m hm
        change encS (nextS^[m + 1] (nextS^[n] (some ((a, 0), false)))) = [] at hm
        rw [← Function.iterate_add_apply] at hm
        by_contra hlt; push Not at hlt
        obtain ⟨b, hb⟩ := hstate_eq a (m + 1 + n) (by omega)
        rw [hb] at hm
        have : encS (some ((a, m + 1 + n), b)) = true :: _ := encOption_some_eq _ _
        rw [this] at hm; simp at hm
    · exact ⟨by
          change encS (nextS none) = []
          rw [show nextS none = none by simp [nextS, cond]]
          rfl,
        fun m _ ↦ Nat.zero_le m⟩
  let Fl : ℕ → ℕ := fun k ↦ 10 * (F k + 10)
  have hFl : ∀ x : Subtype P, ∀ m ≤ rP x,
      (encS (nextS^[m] x.1)).length ≤ Fl (κSub x) * ((encS x.1).length + 1) ^ 1 := by
    intro x m hm
    rcases x with ⟨s, hs⟩
    rcases hs with ⟨a, n, hn, rfl⟩ | rfl
    · rw [hκSub_spec a n hn]; rw [hrP_spec a n hn] at hm
      rw [← Function.iterate_add_apply]
      obtain ⟨b, hb⟩ := hstate_eq a (m + n) (by omega)
      obtain ⟨bn, hbn⟩ := hstate_eq a n hn
      rw [hb]
      have hlen_a : (encA a).length ≤ (encS (nextS^[n] (some ((a, 0), false)))).length := by
        rw [hbn]; dsimp only [encS]; rw [encOption_some_eq, List.length_cons]
        calc (encA a).length ≤ (encPair encA encNat (a, n)).length :=
              length_le_encPair_left encA encNat (a, n)
          _ ≤ (encPair (encPair encA encNat) encBool ((a, n), bn)).length :=
              length_le_encPair_left (encPair encA encNat) encBool ((a, n), bn)
          _ ≤ _ := Nat.le_succ _
      have hnat_len : (encNat (m + n)).length ≤ F (κ a) + 1 := by
        rw [encNat_apply, Nat.size_eq_bits_len]
        have := Nat.size_le_self (m + n)
        have := hstop_le a; have := hF a; omega
      have hlen_s : (encS (some ((a, m + n), b))).length =
          1 + (2 * (2 * (encA a).length + 1 + (encNat (m + n)).length) + 1 +
            (encBool b).length) := by
        dsimp only [encS]
        rw [encOption_some_eq, List.length_cons, length_encPair, length_encPair]; dsimp only; omega
      have hb_len : (encBool b).length = 1 := rfl
      rw [hlen_s, hb_len]
      dsimp only [Fl]; rw [pow_one]; nlinarith
    · have hm0 : m = 0 := by simpa [rP] using hm
      subst hm0
      have h0 : (encS none).length = 0 := rfl
      change (encS none).length ≤ _
      rw [h0]; exact Nat.zero_le _
  have hκf : ∀ x : Subtype P, ∀ m ≤ rP x,
      κS (nextS^[m] x.1) ≤ max (h (κSub x)) (κP (a₀, 0)) := by
    intro x m hm
    rcases x with ⟨s, hs⟩
    rcases hs with ⟨a, n, hn, rfl⟩ | rfl
    · rw [hκSub_spec a n hn]; rw [hrP_spec a n hn] at hm
      rw [← Function.iterate_add_apply]
      obtain ⟨b, hb⟩ := hstate_eq a (m + n) (by omega)
      dsimp only [κS, extractP]; rw [hb, Option.elim_some]
      exact (hκ a (m + n) ((by omega : m + n ≤ stopIdx a).trans (hstop_le a))).trans
        (le_max_left _ _)
    · have hm0 : m = 0 := by simpa [rP] using hm
      subst hm0
      change κS none ≤ _
      exact le_max_right _ _
  have hiter := computableInFPTTime_iterateWhile_fpt_on hnext hP hr
    (Fr := F) (Fl := Fl) (h := fun k ↦ max (h k) (κP (a₀, 0))) (cl := 1)
    (fun x ↦ by
      rcases x with ⟨s, hs⟩
      rcases hs with ⟨a, n, hn, rfl⟩ | rfl
      · rw [hrP_spec a n hn, hκSub_spec a n hn]; have := hstop_le a; have := hF a; omega
      · exact Nat.zero_le _)
    hFl hκf
  let encP : Subtype P ↪ List Bool := (Function.Embedding.subtype P).trans encS
  let init : α → Subtype P := fun a ↦ ⟨some ((a, 0), false), Or.inl ⟨a, 0, Nat.zero_le _, rfl⟩⟩
  have hinit : ComputableInPolyTime init encA encP := by
    have h1 : ComputableInPolyTime (fun a : α ↦ (some ((a, 0), false) : S)) encA encS :=
      (optionSome _).comp ((id'.prod (const 0)).prod (const false))
    obtain ⟨t, s, ht, hs, k, State, hFin, tm, htm⟩ := h1
    exact ⟨t, s, ht, hs, k, State, hFin, tm, fun a ↦ htm a⟩
  let extract : Subtype P → Bool := fun x ↦ x.1.elim false Prod.snd
  have hextract : ComputableInPolyTime extract encP encBool := by
    have h1 : ComputableInPolyTime (fun s : S ↦ s.elim false Prod.snd) encS encBool :=
      optionElimWithInput id' (const false) ((snd _ _).comp (snd _ _))
    obtain ⟨t, s, ht, hs, k, State, hFin, tm, htm⟩ := h1
    exact ⟨t, s, ht, hs, k, State, hFin, tm, fun x ↦ htm x.1⟩
  have hcomp : ComputableInFPTTime
      (fun a ↦ extract ((fun x : Subtype P ↦ (⟨nextS^[rP x] x.1, by
        have : ∀ m, P (nextS^[m] x.1) := fun m ↦ by
          induction m with
          | zero => exact x.2
          | succ m ih => rw [Function.iterate_succ_apply']; exact hP _ ih
        exact this (rP x)⟩ : Subtype P)) (init a))) encA encBool κ := by
    have hstep1 := hiter.comp (hinit.computableInFPTTime κ) (h := id) fun a ↦
      (hκSub_spec a 0 (Nat.zero_le _)).le
    refine (hextract.computableInFPTTime κSub).comp hstep1 (h := id) fun a ↦ ?_
    have hr0 : rP (init a) = stopIdx a := by simpa [init] using hrP_spec a 0 (Nat.zero_le _)
    change κSub ⟨nextS^[rP (init a)] (some ((a, 0), false)), _⟩ ≤ κ a
    rw [hr0]; exact (hκSub_spec a _ le_rfl).le
  refine computableInFPTTime_congr hcomp fun a ↦ ?_
  have hr0 : rP (init a) = stopIdx a := by simpa [init] using hrP_spec a 0 (Nat.zero_le _)
  dsimp only [extract]
  change (nextS^[rP (init a)] (some ((a, 0), false))).elim false Prod.snd = _
  rw [hr0, hiter_stop a]; rfl

/-! ### 2. Constructive FPT-Time Minimum Vertex Cover -/

private theorem exists_vertexCover_bound (G : Graph) :
    ∃ m, ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.vertices) ∧
      (∀ u ∈ G.vertices, ∀ v ∈ G.vertices, G.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) ∧
      S.card ≤ m :=
  ⟨G.vertices.length, G.vertices.toFinset,
    fun _ hv ↦ List.mem_toFinset.mp hv,
    fun _ hu _ _ _ ↦ Or.inl (List.mem_toFinset.mpr hu),
    List.toFinset_card_le G.vertices⟩

/-- The minimum cardinality of a vertex cover of `G` contained in `G.vertices`. -/
noncomputable def minVertexCoverSize (G : Graph) : ℕ := by
  classical
  exact Nat.find (exists_vertexCover_bound G)

theorem minVertexCoverSize_spec (G : Graph) :
    ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.vertices) ∧
      (∀ u ∈ G.vertices, ∀ v ∈ G.vertices, G.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) ∧
      S.card = minVertexCoverSize G := by
  classical
  unfold minVertexCoverSize
  obtain ⟨S, hSV, hScov, hScard⟩ := Nat.find_spec (exists_vertexCover_bound G)
  refine ⟨S, hSV, hScov, le_antisymm hScard ?_⟩
  exact Nat.find_min' (exists_vertexCover_bound G) ⟨S, hSV, hScov, le_rfl⟩

theorem minVertexCoverSize_le {G : Graph} {S : Finset ℕ} (hSV : ∀ v ∈ S, v ∈ G.vertices)
    (hScov : ∀ u ∈ G.vertices, ∀ v ∈ G.vertices, G.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) :
    minVertexCoverSize G ≤ S.card := by
  classical
  unfold minVertexCoverSize
  exact Nat.find_min' (exists_vertexCover_bound G) ⟨S, hSV, hScov, le_rfl⟩

/-- Branching-path vertex-cover candidate extracted from `(G, idx)`. -/
def minVertexCoverFold (p : Graph × ℕ) : List ℕ :=
  VertexCover.foldBranch p.1 ((List.range ((encNat (p.2 + 1)).length - 1)).map (p.2 + 1).testBit)

/-- Return `some C` if `C` is a vertex cover of `G`, otherwise `none`. -/
def minVertexCoverSelect (p : Graph × List ℕ) : Option (List ℕ) :=
  if VertexCover.isCover p.1 p.2 then some p.2 else none

/-- One step of the constructive minimum vertex cover search: decode depth
`d = (encNat (idx + 1)).length - 1` and follow the branching path of length `d` determined by
the lowest `d` bits of `idx + 1`. -/
def minVertexCoverStep (p : Graph × ℕ) : Option (List ℕ) :=
  minVertexCoverSelect (p.1, minVertexCoverFold p)

private theorem mem_of_mem_foldBranch_aux (G : Graph) (bs : List Bool) :
    ∀ v ∈ VertexCover.foldBranch G bs, v ∈ G.vertices := by
  induction bs using List.reverseRecOn with
  | nil => simp [VertexCover.foldBranch]
  | append_singleton bs b ih =>
    have hfb : VertexCover.foldBranch G (bs ++ [b]) =
        VertexCover.branchStep G (VertexCover.foldBranch G bs) b := by
      simp [VertexCover.foldBranch]
    rw [hfb]
    intro v hv
    set C := VertexCover.foldBranch G bs
    cases hcov : VertexCover.isCover G C with
    | true =>
      simp only [VertexCover.branchStep, hcov, ↓reduceIte] at hv
      exact ih v hv
    | false =>
      simp only [VertexCover.branchStep, hcov, Bool.false_eq_true, ↓reduceIte] at hv
      rcases List.mem_cons.mp hv with rfl | hv'
      · have hne : VertexCover.uncoveredEdges G C ≠ [] := by
          intro hnil; simp [VertexCover.isCover, hnil] at hcov
        have hhead : (VertexCover.uncoveredEdges G C).headD (0, 0) ∈
            VertexCover.uncoveredEdges G C := by
          cases h : VertexCover.uncoveredEdges G C with
          | nil => exact absurd h hne
          | cons e es => simp
        obtain ⟨_, he1, he2, _, _, _⟩ := VertexCover.mem_uncoveredEdges_iff.mp hhead
        cases b <;> assumption
      · exact ih v hv'

private theorem length_foldBranch_le_aux (G : Graph) (bs : List Bool) :
    (VertexCover.foldBranch G bs).length ≤ bs.length := by
  induction bs using List.reverseRecOn with
  | nil => simp [VertexCover.foldBranch]
  | append_singleton bs b ih =>
    have hfb : VertexCover.foldBranch G (bs ++ [b]) =
        VertexCover.branchStep G (VertexCover.foldBranch G bs) b := by
      simp [VertexCover.foldBranch]
    rw [hfb, List.length_append, List.length_singleton]
    have hstep : (VertexCover.branchStep G (VertexCover.foldBranch G bs) b).length ≤
        (VertexCover.foldBranch G bs).length + 1 := by
      unfold VertexCover.branchStep; split_ifs <;> simp
    omega

private theorem length_encList_branchStep_le_aux (G : Graph) (C : List ℕ) (b : Bool) :
    (encList encNat (VertexCover.branchStep G C b)).length ≤
      (encList encNat C).length + (2 * (encGraph G).length + 2) := by
  cases h : VertexCover.isCover G C with
  | false =>
    have hne : VertexCover.uncoveredEdges G C ≠ [] := by
      intro hnil; simp [VertexCover.isCover, hnil] at h
    have hhead : (VertexCover.uncoveredEdges G C).headD (0, 0) ∈
        VertexCover.uncoveredEdges G C := by
      cases hu : VertexCover.uncoveredEdges G C with
      | nil => exact absurd hu hne
      | cons e es => simp
    obtain ⟨_, he1, he2, _, _, _⟩ := VertexCover.mem_uncoveredEdges_iff.mp hhead
    have hw : (if b then ((VertexCover.uncoveredEdges G C).headD (0, 0)).2
        else ((VertexCover.uncoveredEdges G C).headD (0, 0)).1) ∈ G.vertices := by
      cases b <;> assumption
    have hlen : (encNat (if b then ((VertexCover.uncoveredEdges G C).headD (0, 0)).2
        else ((VertexCover.uncoveredEdges G C).headD (0, 0)).1)).length ≤ (encGraph G).length := by
      calc (encNat _).length
          ≤ (encList encNat G.vertices).length := length_le_encList_of_mem encNat hw
        _ ≤ (encGraph G).length := by rw [encGraph_apply, length_encPair]; dsimp only; omega
    simp only [VertexCover.branchStep, h, Bool.false_eq_true, ↓reduceIte, encList_cons,
      List.length_append, length_frame]
    omega
  | true =>
    simp only [VertexCover.branchStep, h, ↓reduceIte]; omega

private theorem exists_minVertexCoverStep_isSome (G : Graph) :
    ∃ idx, (minVertexCoverStep (G, idx)).isSome := by
  let d := minVertexCoverSize G
  obtain ⟨S, hSV, hScov, hScard⟩ := minVertexCoverSize_spec G
  obtain ⟨i, hi, hcov⟩ := (VertexCover.exists_lt_two_pow_isCover_foldBranch G d).mp
    ⟨S, hSV, hScov, hScard.le⟩
  let m := 2 ^ d + i
  have hm_pos : 1 ≤ m := by have := Nat.one_le_two_pow (n := d); omega
  have hm_size : (encNat m).length = d + 1 := by
    rw [encNat_apply, Nat.size_eq_bits_len]
    apply le_antisymm
    · exact Nat.size_le.mpr (by rw [Nat.pow_succ]; omega)
    · by_contra hlt; push Not at hlt
      have h1 : m < 2 ^ d := (Nat.lt_size_self m).trans_le
        (Nat.pow_le_pow_right (by omega) (by omega))
      omega
  have hbits : (List.range d).map m.testBit = (List.range d).map i.testBit := by
    apply List.map_congr_left
    intro j hj
    have hjlt : j < d := List.mem_range.mp hj
    have hshift : m = i + 2 ^ d := by omega
    rw [hshift, testBit_add_two_pow_of_lt hjlt]
  refine ⟨m - 1, ?_⟩
  simp only [minVertexCoverStep, minVertexCoverSelect, minVertexCoverFold,
    show m - 1 + 1 = m by omega, hm_size, Nat.add_sub_cancel, hbits, hcov, ↓reduceIte,
    Option.isSome_some]

private theorem find_minVertexCoverStep_succ_lt (G : Graph) :
    Nat.find (exists_minVertexCoverStep_isSome G) + 1 < 2 ^ (minVertexCoverSize G + 1) := by
  let d := minVertexCoverSize G
  obtain ⟨S, hSV, hScov, hScard⟩ := minVertexCoverSize_spec G
  obtain ⟨i, hi, hcov⟩ := (VertexCover.exists_lt_two_pow_isCover_foldBranch G d).mp
    ⟨S, hSV, hScov, hScard.le⟩
  let m := 2 ^ d + i
  have hm_pos : 1 ≤ m := by have := Nat.one_le_two_pow (n := d); omega
  have hm_size : (encNat m).length = d + 1 := by
    rw [encNat_apply, Nat.size_eq_bits_len]
    apply le_antisymm
    · exact Nat.size_le.mpr (by rw [Nat.pow_succ]; omega)
    · by_contra hlt; push Not at hlt
      have h1 : m < 2 ^ d := (Nat.lt_size_self m).trans_le
        (Nat.pow_le_pow_right (by omega) (by omega))
      omega
  have hbits : (List.range d).map m.testBit = (List.range d).map i.testBit := by
    apply List.map_congr_left
    intro j hj
    have hjlt : j < d := List.mem_range.mp hj
    have hshift : m = i + 2 ^ d := by omega
    rw [hshift, testBit_add_two_pow_of_lt hjlt]
  have hok : (minVertexCoverStep (G, m - 1)).isSome := by
    simp only [minVertexCoverStep, minVertexCoverSelect, minVertexCoverFold,
      show m - 1 + 1 = m by omega, hm_size, Nat.add_sub_cancel, hbits, hcov, ↓reduceIte,
      Option.isSome_some]
  have hle := Nat.find_min' (exists_minVertexCoverStep_isSome G) hok
  have hpow : m < 2 ^ (d + 1) := by rw [Nat.pow_succ]; omega
  dsimp only [d, m] at hle hpow hm_pos
  omega

/-- Constructive FPT-time minimum vertex cover algorithm returning a duplicate-free vertex cover
of `G` of minimum cardinality. -/
noncomputable def minVertexCover (G : Graph) : List ℕ :=
  searchUnbounded minVertexCoverStep exists_minVertexCoverStep_isSome G

theorem minVertexCover_spec (G : Graph) :
    (minVertexCover G).Nodup ∧
      (∀ v ∈ minVertexCover G, v ∈ G.vertices) ∧
      (∀ u ∈ G.vertices, ∀ v ∈ G.vertices, G.toSimpleGraph.Adj u v →
        u ∈ minVertexCover G ∨ v ∈ minVertexCover G) ∧
      (minVertexCover G).length = minVertexCoverSize G := by
  let idx := Nat.find (exists_minVertexCoverStep_isSome G)
  have hspec := Nat.find_spec (exists_minVertexCoverStep_isSome G)
  have hlt := find_minVertexCoverStep_succ_lt G
  let m := idx + 1
  let d := (encNat m).length - 1
  have hcov : VertexCover.isCover G
      (VertexCover.foldBranch G ((List.range d).map m.testBit)) = true := by
    change (if VertexCover.isCover G (VertexCover.foldBranch G ((List.range d).map m.testBit))
        then some (VertexCover.foldBranch G ((List.range d).map m.testBit)) else none).isSome = true
      at hspec
    split_ifs at hspec with h
    · exact h
    · simp at hspec
  have hEq : minVertexCover G = VertexCover.foldBranch G ((List.range d).map m.testBit) := by
    change (if VertexCover.isCover G (VertexCover.foldBranch G ((List.range d).map m.testBit))
        then some (VertexCover.foldBranch G ((List.range d).map m.testBit)) else none).get _ = _
    simp [hcov]
  rw [hEq]
  set C := VertexCover.foldBranch G ((List.range d).map m.testBit)
  have hmem : ∀ v ∈ C, v ∈ G.vertices := mem_of_mem_foldBranch_aux G _
  have hcov_prop : ∀ u ∈ G.vertices, ∀ v ∈ G.vertices, G.toSimpleGraph.Adj u v →
      u ∈ C ∨ v ∈ C := by
    intro u hu v hv hadj
    exact VertexCover.isCover_eq_true_iff.mp hcov u hu v hv hadj
  have hd_le : d ≤ minVertexCoverSize G := by
    have hm_lt : m < 2 ^ (minVertexCoverSize G + 1) := hlt
    have hsz : m.size ≤ minVertexCoverSize G + 1 := Nat.size_le.mpr hm_lt
    have hlen : (encNat m).length = m.size := by rw [encNat_apply, Nat.size_eq_bits_len]
    dsimp only [d]; omega
  have hC_len : C.length ≤ minVertexCoverSize G :=
    (length_foldBranch_le_aux G _).trans (by simp [hd_le])
  have hvc_le : minVertexCoverSize G ≤ C.toFinset.card :=
    minVertexCoverSize_le (fun v hv ↦ hmem v (List.mem_toFinset.mp hv))
      (fun u hu v hv hadj ↦ by simpa only [List.mem_toFinset] using hcov_prop u hu v hv hadj)
  have hcard_le : C.toFinset.card ≤ C.length := List.toFinset_card_le C
  have hlen_eq : C.length = minVertexCoverSize G := by omega
  have hcard_eq : C.toFinset.card = C.length := by omega
  exact ⟨nodup_of_toFinset_card_eq hcard_eq, hmem, hcov_prop, hlen_eq⟩

private theorem computableInPolyTime_minVertexCoverBits :
    ComputableInPolyTime
      (fun p : Graph × ℕ ↦ (List.range ((encNat (p.2 + 1)).length - 1)).map (p.2 + 1).testBit)
      (encPair encGraph encNat) (encList encBool) := by
  let encIn := encPair encGraph encNat
  have hm : ComputableInPolyTime (fun p : Graph × ℕ ↦ p.2 + 1) encIn encNat :=
    binary_add' (snd _ _) (const 1)
  have hd : ComputableInPolyTime (fun p : Graph × ℕ ↦ (encNat (p.2 + 1)).length - 1)
      encIn encUnary :=
    unary_sub.comp (((encoding_length encNat).comp hm).prod (const 1))
  have heq : (fun p : Graph × ℕ ↦
        (List.range ((encNat (p.2 + 1)).length - 1)).map (p.2 + 1).testBit) =
      fun p ↦ (List.range ((encNat (p.2 + 1)).length - 1)).map
        fun j ↦ (encNat (p.2 + 1)).getD j false := by
    funext p; congr 1 with j; rw [Nat.testBit_eq_inth]; rfl
  rw [heq]
  exact mapWithInput (range.comp hd)
    (bitsGetDWithInput
      ((of_eq (f := encNat) (encIn := encNat) (encOut := encBits) fun _ ↦ rfl).comp
        (hm.comp (fst encIn encUnary)))
      (snd encIn encUnary) false)

private theorem computableInPolyTime_minVertexCoverFold :
    ComputableInPolyTime minVertexCoverFold (encPair encGraph encNat) (encList encNat) := by
  let encIn := encPair encGraph encNat
  have hG : ComputableInPolyTime (fun p : Graph × ℕ ↦ p.1) encIn encGraph := fst _ _
  have hgrowth : PolyBounded (fun p : Graph × ℕ ↦ (encIn p).length)
      (fun p : Graph × ℕ ↦ 2 * (encGraph p.1).length + 2) :=
    ((PolyBounded.const 2).mul hG.polyBounded_length).add (.const 2)
  exact foldlWith_of_bounded_growth hG computableInPolyTime_minVertexCoverBits (const [])
    VertexCover.computableInPolyTime_branchStep hgrowth
    (fun p C b _ ↦ length_encList_branchStep_le_aux p.1 C b)

private theorem computableInPolyTime_minVertexCoverSelect :
    ComputableInPolyTime minVertexCoverSelect
      (encPair encGraph (encList encNat)) (encOption (encList encNat)) := by
  have hthen : ComputableInPolyTime (fun p : Graph × List ℕ ↦ some p.2)
      (encPair encGraph (encList encNat)) (encOption (encList encNat)) :=
    (optionSome (encList encNat)).comp (snd encGraph (encList encNat))
  have helse : ComputableInPolyTime (fun _ : Graph × List ℕ ↦ (none : Option (List ℕ)))
      (encPair encGraph (encList encNat)) (encOption (encList encNat)) :=
    const none
  exact ComputableInPolyTime.ite VertexCover.computableInPolyTime_isCover hthen helse

private theorem computableInPolyTime_minVertexCoverStep :
    ComputableInPolyTime minVertexCoverStep
      (encPair encGraph encNat) (encOption (encList encNat)) :=
  computableInPolyTime_minVertexCoverSelect.comp
    ((fst encGraph encNat).prod computableInPolyTime_minVertexCoverFold)

/-- `minVertexCover` is computable in FPT time parameterized by `minVertexCoverSize`. -/
theorem computableInFPTTime_minVertexCover :
    ComputableInFPTTime minVertexCover encGraph (encList encNat) minVertexCoverSize :=
  computableInFPTTime_searchUnbounded (F := fun k ↦ 2 ^ (k + 1))
    computableInPolyTime_minVertexCoverStep exists_minVertexCoverStep_isSome
    fun G ↦ by have := find_minVertexCoverStep_succ_lt G; omega

end CslibFrontier.Complexity
