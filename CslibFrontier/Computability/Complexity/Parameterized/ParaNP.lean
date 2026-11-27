module

public import CslibFrontier.Computability.Complexity.Parameterized
public import CslibFrontier.Computability.Complexity.Parameterized.Hardness
public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Parameterized Complexity Class `para-NP` and FPT-Time Combinators

This module defines the parameterized complexity class `para-NP` and `para-NP`-hardness, and proves
foundational closure, slice-hardness, and collapse results under
standard Lean axioms. It also provides reusable fixed-parameter-tractable (FPT) time combinators
for pairing, parameter-bounded unary conversion, and parameter-bounded iteration on multi-tape
Turing machines.

## Main definitions

* `Cslib.Complexity.ParaNP`: the parameterized class `para-NP` of problems admitting an fpt-time
  reduction to a problem in `NP`.
* `Cslib.Complexity.ParaNPHard`: `para-NP`-hardness under fpt-reductions (`FPTHard ParaNP`).

## Main results

* `Cslib.Complexity.FPT_subset_ParaNP`, `Cslib.Complexity.NP_subset_ParaNP`:
  `FPT ⊆ para-NP` and `NP ⊆ para-NP` for every parameter.
* `Cslib.Complexity.FPTReducible.mem_ParaNP`: `para-NP` is closed under fpt-reductions.
* `Cslib.Complexity.ParaNP_eq_NP_of_le`: for a bounded parameter, `para-NP = NP`.
* `Cslib.Complexity.mem_ParaNP_iff_fptReducible_SAT`: a problem lies in `para-NP` iff it
  fpt-reduces to `SAT` with constant parameter `0`.
* `Cslib.Complexity.ParaNPHard.of_slice_npHard`: slice-hardness criterion
: a parameterized problem with an `NP`-hard parameter-bounded slice is
  `para-NP`-hard.
* `Cslib.Complexity.ParaNPHard.P_eq_NP_of_mem_FPT`: any `para-NP`-hard problem in `FPT` implies
  `P = NP`.
* `Cslib.Complexity.ComputableInFPTTime.prod`,
  `Cslib.Complexity.ComputableInFPTTime.toUnary_of_le`,
  `Cslib.Complexity.ComputableInFPTTime.iterate_of_poly`: FPT-time combinators for pairing,
  parameter-bounded binary-to-unary conversion, and parameter-bounded iteration.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### FPT-time combinators -/

section FPTCombinators

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {κ : α → ℕ}

private theorem fpt_exists_computableInO {f : α → β} (hf : ComputableInFPTTime f encA encB κ) :
    ∃ (F : ℕ → ℕ) (c : ℕ), ComputableInO f encA encB
      (fun a => F (κ a) * ((encA a).length + 1) ^ c)
      (fun a => F (κ a) * ((encA a).length + 1) ^ c) := by
  obtain ⟨F, c, hc⟩ := hf
  exact ⟨F, c, .of_bounds hc 1 (fun _ => by omega) (fun _ => by omega)
    fun a => (hc.length_le a).trans (by omega)⟩

/-- Pairing two fpt-time computable functions is computable in fpt time. -/
theorem ComputableInFPTTime.prod {f : α → β} {g : α → γ}
    (hf : ComputableInFPTTime f encA encB κ) (hg : ComputableInFPTTime g encA encC κ) :
    ComputableInFPTTime (fun a => (f a, g a)) encA (encPair encB encC) κ := by
  obtain ⟨F₁, c₁, hfO⟩ := fpt_exists_computableInO hf
  obtain ⟨F₂, c₂, hgO⟩ := fpt_exists_computableInO hg
  have key (a : α) :
      F₁ (κ a) * ((encA a).length + 1) ^ c₁ + F₂ (κ a) * ((encA a).length + 1) ^ c₂ ≤
        (F₁ (κ a) + F₂ (κ a)) * ((encA a).length + 1) ^ (c₁ + c₂) := by
    have h₁ : ((encA a).length + 1) ^ c₁ ≤ ((encA a).length + 1) ^ (c₁ + c₂) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_right _ _)
    have h₂ : ((encA a).length + 1) ^ c₂ ≤ ((encA a).length + 1) ^ (c₁ + c₂) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_left _ _)
    have hm₁ := Nat.mul_le_mul_left (F₁ (κ a)) h₁
    have hm₂ := Nat.mul_le_mul_left (F₂ (κ a)) h₂
    rw [Nat.add_mul]
    omega
  exact ComputableInO.computableInFPTTime
    (F := fun k => F₁ k + F₂ k) (c := c₁ + c₂) ((hfO.prod hgO).mono_le key key)

/-- Iterating a polynomial-time step function a parameter-bounded number of times (with binary
count and FPT-bounded intermediate encoded state lengths) runs in fpt time. -/
theorem ComputableInFPTTime.iterate_of_poly [Inhabited β]
    {n : α → ℕ} {init : α → β} {step : β → β}
    (hn : ComputableInFPTTime n encA encNat κ)
    (hinit : ComputableInFPTTime init encA encB κ)
    (hstep : ComputableInPolyTime step encB encB)
    {hn_le : ℕ → ℕ} (hnb : ∀ a, n a ≤ hn_le (κ a))
    {G : ℕ → ℕ} {e : ℕ}
    (hstate : ∀ a, ∀ k ≤ n a, (encB (step^[k] (init a))).length ≤
      G (κ a) * ((encA a).length + 1) ^ e) :
    ComputableInFPTTime (fun a => step^[n a] (init a)) encA encB κ := by
  obtain ⟨Fn, cn, hnO⟩ := fpt_exists_computableInO hn
  obtain ⟨Fi, ci, hiO⟩ := fpt_exists_computableInO hinit
  obtain ⟨ds, _, hstepD⟩ := hstep.exists_degree
  let R : α → ℕ := fun a => (G (κ a) * ((encA a).length + 1) ^ e + 1) ^ ds
  let B : α → ℕ := fun a => G (κ a) * ((encA a).length + 1) ^ e
  have hround : ∀ a, ∀ k ≤ n a, ((encB (step^[k] (init a))).length + 1) ^ ds ≤ R a :=
    fun a k hk => Nat.pow_le_pow_left (Nat.add_le_add_right (hstate a k hk) 1) ds
  have hiter := ComputableInO.iterate hnO hiO (ComputableInDegree.inO hstepD) hround hround hstate
  let F : ℕ → ℕ := fun k =>
    Fn k + Fi k + (hn_le k + 1) * ((G k + 1) ^ ds + G k + (hn_le k + 1) ^ 2)
  let c : ℕ := cn + ci + e * ds + e
  have hle_time (a : α) :
      Fn (κ a) * ((encA a).length + 1) ^ cn + Fi (κ a) * ((encA a).length + 1) ^ ci +
        (n a + 1) * (R a + B a + ((encNat (n a)).length + 1) ^ 2) ≤
      F (κ a) * ((encA a).length + 1) ^ c := by
    set L := (encA a).length + 1
    have hLpos : 1 ≤ L := Nat.succ_pos _
    have hLpow (m : ℕ) (hm : m ≤ c) : L ^ m ≤ L ^ c := Nat.pow_le_pow_right hLpos hm
    have hLc : 1 ≤ L ^ c := Nat.one_le_pow c L hLpos
    have hR : R a ≤ (G (κ a) + 1) ^ ds * L ^ (e * ds) := by
      dsimp only [R]
      have h1 : G (κ a) * L ^ e + 1 ≤ (G (κ a) + 1) * L ^ e := by
        have := Nat.one_le_pow e L hLpos
        nlinarith
      calc (G (κ a) * L ^ e + 1) ^ ds
          ≤ ((G (κ a) + 1) * L ^ e) ^ ds := Nat.pow_le_pow_left h1 ds
        _ = (G (κ a) + 1) ^ ds * (L ^ e) ^ ds := Nat.mul_pow _ _ _
        _ = (G (κ a) + 1) ^ ds * L ^ (e * ds) := by rw [← Nat.pow_mul]
    have hR' : R a ≤ (G (κ a) + 1) ^ ds * L ^ c :=
      hR.trans (Nat.mul_le_mul_left _ (hLpow (e * ds) (by omega)))
    have hB' : B a ≤ G (κ a) * L ^ c :=
      Nat.mul_le_mul_left _ (hLpow e (by omega))
    have hlen : ((encNat (n a)).length + 1) ^ 2 ≤ (hn_le (κ a) + 1) ^ 2 * L ^ c := by
      have hl : (encNat (n a)).length ≤ hn_le (κ a) :=
        (length_encNat_le_self (n a)).trans (hnb a)
      have hsq : ((encNat (n a)).length + 1) ^ 2 ≤ (hn_le (κ a) + 1) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      exact hsq.trans (Nat.le_mul_of_pos_right _ hLc)
    have hsum : R a + B a + ((encNat (n a)).length + 1) ^ 2 ≤
        ((G (κ a) + 1) ^ ds + G (κ a) + (hn_le (κ a) + 1) ^ 2) * L ^ c := by
      rw [Nat.add_mul, Nat.add_mul]
      omega
    have hmul : (n a + 1) * (R a + B a + ((encNat (n a)).length + 1) ^ 2) ≤
        (hn_le (κ a) + 1) * ((G (κ a) + 1) ^ ds + G (κ a) + (hn_le (κ a) + 1) ^ 2) * L ^ c := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul (Nat.add_le_add_right (hnb a) 1) hsum
    have hfn : Fn (κ a) * L ^ cn ≤ Fn (κ a) * L ^ c :=
      Nat.mul_le_mul_left _ (hLpow cn (by omega))
    have hfi : Fi (κ a) * L ^ ci ≤ Fi (κ a) * L ^ c :=
      Nat.mul_le_mul_left _ (hLpow ci (by omega))
    dsimp only [F]
    rw [Nat.add_mul, Nat.add_mul]
    linarith
  have hle_space (a : α) :
      Fn (κ a) * ((encA a).length + 1) ^ cn + Fi (κ a) * ((encA a).length + 1) ^ ci +
        R a + B a + (encNat (n a)).length ≤
      F (κ a) * ((encA a).length + 1) ^ c := by
    have h1 : (encNat (n a)).length ≤ ((encNat (n a)).length + 1) ^ 2 :=
      (Nat.le_succ _).trans (Nat.le_self_pow two_ne_zero _)
    have h2 : R a + B a + ((encNat (n a)).length + 1) ^ 2 ≤
        (n a + 1) * (R a + B a + ((encNat (n a)).length + 1) ^ 2) :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    exact (by omega : _ ≤ _).trans (hle_time a)
  exact ComputableInO.computableInFPTTime (F := F) (c := c) (hiter.mono_le hle_time hle_space)

/-- Converting a parameter-bounded binary natural number to unary runs in fpt time. -/
theorem ComputableInFPTTime.toUnary_of_le {f : α → ℕ}
    (hf : ComputableInFPTTime f encA encNat κ) {h : ℕ → ℕ} (hb : ∀ a, f a ≤ h (κ a)) :
    ComputableInFPTTime f encA encUnary κ := by
  have hsucc : ComputableInPolyTime (fun u : ℕ => u + 1) encUnary encUnary := by
    have : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + p.2) (encPair encUnary encUnary)
        encUnary := ComputableInPolyTime.unary_add
    exact this.comp (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const 1))
  have hiter := ComputableInFPTTime.iterate_of_poly (encB := encUnary) (init := fun _ => 0)
    (step := fun u => u + 1) hf ((ComputableInPolyTime.const 0).computableInFPTTime κ) hsucc
    (hn_le := h) hb (G := h) (e := 0) (fun a k hk => by
      have heq : ∀ m : ℕ, (fun u : ℕ => u + 1)^[m] 0 = m := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih => rw [Function.iterate_succ_apply', ih]
      rw [heq k, encUnary_apply, List.length_replicate, pow_zero, mul_one]
      exact hk.trans (hb a))
  have heq : (fun a => (fun u : ℕ => u + 1)^[f a] 0) = f := by
    funext a
    induction f a with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih]
  rwa [heq] at hiter

end FPTCombinators

/-! ### The class `para-NP` and `para-NP`-hardness -/

section ParaNP

/-- **The class `para-NP`**:
a parameterized problem `(A, κ)` lies in `para-NP` when it admits an fpt-time reduction to some
problem `B ∈ NP`.
-/
def ParaNP {α : Type} (enc : α ↪ List Bool) (κ : α → ℕ) : Set (Set α) :=
  {A | ∃ (γ : Type) (encB : γ ↪ List Bool) (B : Set γ), B ∈ NP encB ∧
    ∃ f : α → γ, ComputableInFPTTime f enc encB κ ∧ ∀ a, a ∈ A ↔ f a ∈ B}

/-- **`para-NP`-hardness**: every problem in `para-NP` fpt-reduces to `B`. -/
abbrev ParaNPHard {β : Type} (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  FPTHard (@ParaNP) enc κ B

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {κA : α → ℕ} {κB : β → ℕ}
  {A : Set α} {B : Set β}

/-- Membership in `ParaNP`. -/
theorem mem_ParaNP :
    A ∈ ParaNP encA κA ↔ ∃ (γ : Type) (encC : γ ↪ List Bool) (C : Set γ), C ∈ NP encC ∧
      ∃ f : α → γ, ComputableInFPTTime f encA encC κA ∧ ∀ a, a ∈ A ↔ f a ∈ C :=
  Iff.rfl

/-- **`NP ⊆ para-NP`** for every parameter. -/
theorem NP_subset_ParaNP : NP encA ⊆ ParaNP encA κA := fun A hA =>
  ⟨α, encA, A, hA, id, ComputableInPolyTime.id'.computableInFPTTime κA, fun _ => Iff.rfl⟩

/-- **`FPT ⊆ para-NP`** for every parameter. -/
theorem FPT_subset_ParaNP : FPT encA κA ⊆ ParaNP encA κA := by
  intro A hA
  obtain ⟨g, hg, hAg⟩ := mem_FPT_iff_computableInFPTTime.mp hA
  have htrue : ({true} : Set Bool) ∈ NP encBool :=
    P_subset_NP ⟨id, ComputableInPolyTime.id', fun _ => Iff.rfl⟩
  exact ⟨Bool, encBool, {true}, htrue, g, hg, hAg⟩

/-- **`para-NP` is closed under fpt-reductions.** -/
theorem FPTReducible.mem_ParaNP (hAB : FPTReducible encA encB κA κB A B)
    (hB : B ∈ ParaNP encB κB) : A ∈ ParaNP encA κA := by
  obtain ⟨f, ⟨hf, h, hκ⟩, hred⟩ := hAB
  obtain ⟨γ, encC, C, hC, g, hg, hgB⟩ := hB
  exact ⟨γ, encC, C, hC, g ∘ f, hg.comp hf hκ, fun a => (hred a).trans (hgB (f a))⟩

/-- Changing the parameter monotonically preserves `para-NP`. -/
theorem ParaNP_subset_ParaNP_of_le_comp {κ' : α → ℕ} {h : ℕ → ℕ} (hκ : ∀ a, κA a ≤ h (κ' a)) :
    ParaNP encA κA ⊆ ParaNP encA κ' := fun _ hA =>
  FPTReducible.mem_ParaNP
    (FPTReducible.of_computableInPolyTime ComputableInPolyTime.id' hκ fun _ => Iff.rfl) hA

/-- **Characterization via `SAT`**: a parameterized problem belongs to `para-NP` iff it
fpt-reduces to `SAT` with constant parameter `0`. -/
theorem mem_ParaNP_iff_fptReducible_SAT :
    A ∈ ParaNP encA κA ↔ FPTReducible encA encCNF κA (fun _ => 0) A SAT := by
  constructor
  · rintro ⟨γ, encC, C, hC, f, hf, hred⟩
    obtain ⟨g, hg, hgC⟩ := CookLevin.SAT_npHard encC C hC
    exact ⟨g ∘ f, ⟨(hg.computableInFPTTime (fun _ => 0)).comp hf (h := fun _ => 0)
        (fun _ => le_rfl),
      fun _ => 0, fun _ => le_rfl⟩, fun a => (hred a).trans (hgC (f a))⟩
  · rintro ⟨f, ⟨hf, -, -⟩, hred⟩
    exact ⟨CNF ℕ, encCNF, SAT, SAT.mem_NP, f, hf, hred⟩

/-- **Bounded parameters**: for a parameter bounded by a constant, `para-NP = NP`. -/
theorem ParaNP_eq_NP_of_le {K : ℕ} (hκ : ∀ a, κA a ≤ K) : ParaNP encA κA = NP encA := by
  refine Set.Subset.antisymm (fun A hA => ?_) NP_subset_ParaNP
  obtain ⟨γ, encC, C, hC, f, hf, hred⟩ := hA
  have hf0 : ComputableInFPTTime f encA encC (fun _ => 0) := by
    have hcomp := hf.comp (ComputableInPolyTime.id'.computableInFPTTime (fun _ => 0))
      (h := fun _ => K) hκ
    simpa [Function.comp_def] using hcomp
  obtain ⟨F, c, hO⟩ := fpt_exists_computableInO hf0
  have hpoly : ComputableInPolyTime f encA encC :=
    hO.computableInPolyTime (.of_forall_le (F 0) c fun _ => le_rfl)
      (.of_forall_le (F 0) c fun _ => le_rfl)
  exact PolyTimeReducible.mem_NP ⟨f, hpoly, hred⟩ hC

/-- **Slice-hardness criterion**: if an `NP`-hard problem
polynomial-time reduces to `B` with output parameter bounded by a constant `k₀`, then `B` is
`para-NP`-hard.
-/
theorem ParaNPHard.of_polyTimeReducible_bounded {γ : Type} {encC : γ ↪ List Bool} {C : Set γ}
    (hC : NPHard encC C) {r : γ → β} (hr : ComputableInPolyTime r encC encB)
    {k₀ : ℕ} (hκ : ∀ c, κB (r c) ≤ k₀) (hred : ∀ c, c ∈ C ↔ r c ∈ B) :
    ParaNPHard encB κB B := by
  intro α encA κA A hA
  obtain ⟨f, ⟨hf, -, -⟩, hfA⟩ := mem_ParaNP_iff_fptReducible_SAT.mp hA
  obtain ⟨g, hg, hgC⟩ := hC encCNF SAT SAT.mem_NP
  refine ⟨r ∘ g ∘ f,
    ⟨((hr.comp hg).computableInFPTTime (fun _ => 0)).comp hf (h := fun _ => 0)
        (fun _ => le_rfl),
      fun _ => k₀, fun a => hκ _⟩,
    fun a => (hfA a).trans ((hgC (f a)).trans (hred (g (f a))))⟩

/-- **Slice-hardness criterion (slice form)**: if `κB` is
computable in polynomial time, `B` has at least one no-instance, and some bounded-parameter slice
`B ∩ {b | κB b ≤ k₀}` is `NP`-hard, then `B` is `para-NP`-hard.
-/
theorem ParaNPHard.of_slice_npHard {k₀ : ℕ}
    (hκ_poly : ComputableInPolyTime κB encB encNat)
    (hno : ∃ b₀ : β, b₀ ∉ B)
    (hslice : NPHard encB (B ∩ {b | κB b ≤ k₀})) :
    ParaNPHard encB κB B := by
  obtain ⟨b₀, hb₀⟩ := hno
  obtain ⟨g, hg, hgS⟩ := hslice encCNF SAT SAT.mem_NP
  let r : CNF ℕ → β := fun φ => if decide (κB (g φ) ≤ k₀) then g φ else b₀
  have hr : ComputableInPolyTime r encCNF encB := by
    have htest : ComputableInPolyTime (fun φ : CNF ℕ => decide (κB (g φ) ≤ k₀)) encCNF encBool :=
      ComputableInPolyTime.binary_le' (hκ_poly.comp hg) (ComputableInPolyTime.const k₀)
    exact htest.ite hg (ComputableInPolyTime.const b₀)
  refine ParaNPHard.of_polyTimeReducible_bounded CookLevin.SAT_npHard hr
    (k₀ := max k₀ (κB b₀)) (fun φ => ?_) (fun φ => ?_)
  · dsimp only [r]
    split_ifs with h
    · exact (decide_eq_true_eq.mp h).trans (le_max_left _ _)
    · exact le_max_right _ _
  · dsimp only [r]
    rw [hgS φ]
    split_ifs with h
    · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, decide_eq_true_eq.mp h, and_true]
    · have hnot : ¬κB (g φ) ≤ k₀ := by simpa using h
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hnot, and_false, hb₀]

/-- **Collapse from `para-NP`-hardness**: if a `para-NP`-hard problem belongs to `FPT`, then
`P = NP` for every encoding. -/
theorem ParaNPHard.P_eq_NP_of_mem_FPT (hB : ParaNPHard encB κB B) (hFPT : B ∈ FPT encB κB)
    {γ : Type} (encC : γ ↪ List Bool) : P encC = NP encC := by
  refine Set.Subset.antisymm P_subset_NP (fun A hA => ?_)
  have hpara : A ∈ ParaNP encC (fun _ => 0) := NP_subset_ParaNP hA
  have hfpt : A ∈ FPT encC (fun _ => 0) := (hB _ _ _ hpara).mem_FPT hFPT
  rwa [FPT_eq_P_of_le (K := 0) (fun _ => le_rfl)] at hfpt

end ParaNP

end Cslib.Complexity
