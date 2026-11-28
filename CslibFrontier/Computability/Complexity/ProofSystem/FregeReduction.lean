module

public import CslibFrontier.Computability.Complexity.ProofSystem.TauFormula

import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial-Size Frege Circuit Specialization and Disjunction Flattening

This module develops explicit line-count and formula-length bounded Hilbert-style Frege proof
combinators (`BoundedFrege`) and proves two uniform polynomial-size Extended Frege reduction
theorems (using pure Frege rules with zero extension axioms or extra axioms):

1. `exists_frege_bigOr_flatten`: flattening nested right-associated disjunctions
   `bigOr (groups.map bigOr) → bigOr groups.flatten` in polynomial encoded proof size.
2. `exists_frege_reduce_tauFormula`: specializing a circuit range-avoidance formula
   `tauFormula 0 c' b` to `tauFormula 0 c a` along any wire map `Wire n' c'.size → WireSim n c.size`
   carrying each gate of `c'` either to a faithful copy of a gate of `c` or to a one-variable
   propositional tautology, and each output wire of `c'` to a matching constant or signed output
   wire of `c`.

## Main definitions

* `CslibFrontier.ProofComplexity.WireSim`: constant or signed-wire target of a circuit
  specialization.
* `CslibFrontier.ProofComplexity.wireSimFormula`: propositional formula realizing a `WireSim`.
* `CslibFrontier.ProofComplexity.OneVarSim`: one-variable symbolic constant or signed atom.
* `CslibFrontier.ProofComplexity.oneVarGateTemplate`: one-variable gate-equation formula schema.
* `CslibFrontier.ProofComplexity.IsGateSim`: per-gate soundness of a circuit specialization.
* `CslibFrontier.ProofComplexity.IsOutputSim`: per-output soundness of a circuit specialization.
* `CslibFrontier.ProofComplexity.wireSimPairs`: finite substitution association list for a `WireSim`
  map.

## Main results

* `CslibFrontier.ProofComplexity.exists_frege_bigOr_flatten`: polynomial-size verified Frege proof
  of `bigOr (groups.map bigOr) → bigOr groups.flatten`.
* `CslibFrontier.ProofComplexity.listSubst_wireSimPairs`: lookup equation for `wireSimPairs`.
* `CslibFrontier.ProofComplexity.length_wireSimPairs_le`: quadratic encoded-length bound on
  `wireSimPairs`.
* `CslibFrontier.ProofComplexity.exists_frege_reduce_tauFormula`: polynomial-size verified Frege
  proof of `((tauFormula 0 c' b).subst (listSubst (wireSimPairs sim))) → tauFormula 0 c a`.


-/

public section

namespace CslibFrontier.ProofComplexity

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Logic.PL Cslib.Complexity
open Turing.MultiTapeTM
open Finset

/-! ### Bounded-size Frege proof combinators and circuit specialization -/

/-- A hypothesis-free Frege proof containing `φ` with at most `S` lines, every one of which has
encoded bit length at most `M`. -/
private def BoundedFrege (φ : Formula) (S M : ℕ) : Prop :=
  ∃ L : List Formula, Frege.IsProof [] L ∧ φ ∈ L ∧ L.length ≤ S ∧
    ∀ θ ∈ L, (encFormula θ).length ≤ M

private theorem BoundedFrege.mono {φ : Formula} {S S' M M' : ℕ} (h : BoundedFrege φ S M)
    (hS : S ≤ S') (hM : M ≤ M') : BoundedFrege φ S' M' :=
  let ⟨L, hL, hφ, hl, hm⟩ := h
  ⟨L, hL, hφ, hl.trans hS, fun θ hθ => (hm θ hθ).trans hM⟩

private theorem fregeIsProof_append {L₁ L₂ : List Formula} (h₁ : Frege.IsProof [] L₁)
    (h₂ : Frege.IsProof [] L₂) : Frege.IsProof [] (L₂ ++ L₁) := by
  induction h₂ with
  | nil => exact h₁
  | hyp _ hm => cases hm
  | ax _ hax ih => exact ih.ax hax
  | mp _ hA hAB ih => exact ih.mp (List.mem_append_left _ hA) (List.mem_append_left _ hAB)

private theorem BoundedFrege.ax {φ : Formula} (h : Frege.IsAxiom φ) :
    BoundedFrege φ 1 (encFormula φ).length :=
  ⟨[φ], Frege.IsProof.nil.ax h, List.mem_cons_self, le_rfl,
    fun _ hθ => by simp only [List.mem_singleton] at hθ; subst hθ; exact le_rfl⟩

private theorem BoundedFrege.mp {A B : Formula} {S₁ S₂ M₁ M₂ : ℕ}
    (hAB : BoundedFrege (.imp A B) S₁ M₁) (hA : BoundedFrege A S₂ M₂) :
    BoundedFrege B (S₁ + S₂ + 1) (max M₁ M₂) := by
  obtain ⟨L₁, hL₁, hm₁, hs₁, hb₁⟩ := hAB
  obtain ⟨L₂, hL₂, hm₂, hs₂, hb₂⟩ := hA
  have hB : (encFormula B).length ≤ M₁ := by
    have := hb₁ _ hm₁; simp only [encFormula_imp, List.length_append] at this; omega
  refine ⟨B :: (L₂ ++ L₁), (fregeIsProof_append hL₁ hL₂).mp
    (List.mem_append_left _ hm₂) (List.mem_append_right _ hm₁),
    List.mem_cons_self, by simp; omega, fun θ hθ => ?_⟩
  rcases List.mem_cons.1 hθ with rfl | hθ
  · exact le_max_of_le_left hB
  · rcases List.mem_append.1 hθ with h | h
    · exact le_max_of_le_right (hb₂ θ h)
    · exact le_max_of_le_left (hb₁ θ h)

/-- Canonical `5`-line bounded Frege proof of `φ → φ`. -/
private theorem BoundedFrege.id (φ : Formula) :
    BoundedFrege (.imp φ φ) 5 (9 * (encFormula φ).length + 100) := by
  have hop3 : (frame (encFormTok (.inr 3))).length ≤ 10 := by decide
  have p1 := BoundedFrege.ax (Frege.IsAxiom.s φ (.imp φ φ) φ)
  have p2 := BoundedFrege.ax (Frege.IsAxiom.k φ (.imp φ φ))
  have p3 := BoundedFrege.ax (Frege.IsAxiom.k φ φ)
  refine ((p1.mp p2).mp p3).mono (by omega) ?_
  simp only [encFormula_imp, List.length_append, max_le_iff]; constructor <;> [constructor; skip]
    <;> omega

/-- Prepend a context `Γ` onto a bounded Frege theorem `φ` using `|Γ|` applications of axiom `K`. -/
private theorem BoundedFrege.weaken_imps (Γ : List Formula) {φ : Formula} {S M : ℕ}
    (h : BoundedFrege φ S M) {G : ℕ} (hG : ∀ γ ∈ Γ, (encFormula γ).length ≤ G) :
    BoundedFrege (Frege.Formula.imps Γ φ) (S + 2 * Γ.length)
      (max M (3 * ((Γ.length + 1) * (G + 10) + (encFormula φ).length))) := by
  have hop3 : (frame (encFormTok (.inr 3))).length ≤ 10 := by decide
  induction Γ with
  | nil => exact h.mono (by omega) (le_max_left _ _)
  | cons γ Γ ih =>
    have hγ := hG γ List.mem_cons_self
    have ihΓ := ih fun x hx => hG x (List.mem_cons_of_mem _ hx)
    have hlen_imps := length_encFormula_imps_le (B := G) φ
      (fun x hx => hG x (List.mem_cons_of_mem _ hx))
    have hk := BoundedFrege.ax (Frege.IsAxiom.k (Frege.Formula.imps Γ φ) γ)
    refine (hk.mp ihΓ).mono (by simp; omega) ?_
    have hR : 3 * ((Γ.length + 1) * (G + 10) + (encFormula φ).length) ≤
        3 * (((γ :: Γ).length + 1) * (G + 10) + (encFormula φ).length) := by
      simp only [List.length_cons]; nlinarith
    refine max_le (le_max_of_le_right ?_) (max_le (le_max_left _ _) (le_max_of_le_right hR))
    simp only [encFormula_imp, List.length_append, List.length_cons]; nlinarith

/-- Extract `imps Γ α` for any hypothesis `α ∈ Γ` in `O(|Γ|)` lines. -/
private theorem BoundedFrege.imps_mem {Γ : List Formula} {α : Formula} (hα : α ∈ Γ) {G : ℕ}
    (hG : ∀ γ ∈ Γ, (encFormula γ).length ≤ G) :
    BoundedFrege (Frege.Formula.imps Γ α) (8 * Γ.length + 5)
      (16 * (Γ.length + 1) * (G + 20)) := by
  have hop3 : (frame (encFormTok (.inr 3))).length ≤ 10 := by decide
  induction Γ with
  | nil => cases hα
  | cons γ Γ ih =>
    have hγ := hG γ List.mem_cons_self
    have hαG := hG α hα
    rcases List.mem_cons.1 hα with rfl | hmem
    · clear ih
      have hG' : ∀ x ∈ Γ, (encFormula x).length ≤ G := fun x hx => hG x (List.mem_cons_of_mem _ hx)
      suffices ∀ Δ : List Formula, (∀ x ∈ Δ, (encFormula x).length ≤ G) →
          BoundedFrege (.imp α (Frege.Formula.imps Δ α)) (7 * Δ.length + 5)
            (16 * (Δ.length + 1) * (G + 20)) from
        (this Γ hG').mono (by simp; omega) (by simp only [List.length_cons]; nlinarith)
      intro Δ
      induction Δ with
      | nil => exact fun _ => (BoundedFrege.id α).mono (by omega) (by simp; nlinarith)
      | cons δ Δ ihΔ =>
        intro hΔ
        have hδ := hΔ δ List.mem_cons_self
        have prev := ihΔ fun x hx => hΔ x (List.mem_cons_of_mem _ hx)
        set B := Frege.Formula.imps Δ α
        have hB := length_encFormula_imps_le (B := G) α
          (fun x hx => hΔ x (List.mem_cons_of_mem _ hx))
        have pk1 := BoundedFrege.ax (Frege.IsAxiom.k (.imp B (.imp δ B)) α)
        have pk2 := BoundedFrege.ax (Frege.IsAxiom.k B δ)
        have ps := BoundedFrege.ax (Frege.IsAxiom.s α B (.imp δ B))
        refine ((ps.mp (pk1.mp pk2)).mp prev).mono (by simp; omega) ?_
        simp only [encFormula_imp, List.length_append, List.length_cons, max_le_iff]
        exact ⟨⟨by nlinarith, by nlinarith, by nlinarith⟩, by nlinarith⟩
    · have ihΓ := ih hmem fun x hx => hG x (List.mem_cons_of_mem _ hx)
      have hlen_imps := length_encFormula_imps_le (B := G) α
        (fun x hx => hG x (List.mem_cons_of_mem _ hx))
      have hk := BoundedFrege.ax (Frege.IsAxiom.k (Frege.Formula.imps Γ α) γ)
      refine (hk.mp ihΓ).mono (by simp; omega) ?_
      simp only [encFormula_imp, List.length_append, List.length_cons, max_le_iff]
      exact ⟨by nlinarith, by nlinarith⟩

/-- Distributive law `imps Γ (A → B) → imps Γ A → imps Γ B` in `O(|Γ|)` lines. -/
private theorem BoundedFrege.imps_dist (Γ : List Formula) (A B : Formula) {G : ℕ}
    (hG : ∀ γ ∈ Γ, (encFormula γ).length ≤ G) :
    BoundedFrege (.imp (Frege.Formula.imps Γ (.imp A B))
      (.imp (Frege.Formula.imps Γ A) (Frege.Formula.imps Γ B)))
      (10 * Γ.length + 5)
      (20 * ((Γ.length + 1) * (G + 20) + (encFormula A).length + (encFormula B).length)) := by
  have hop3 : (frame (encFormTok (.inr 3))).length ≤ 10 := by decide
  induction Γ with
  | nil =>
    exact (BoundedFrege.id (.imp A B)).mono (by omega)
      (by simp only [encFormula_imp, List.length_append, List.length_nil]; nlinarith)
  | cons γ Γ ih =>
    have hγ := hG γ List.mem_cons_self
    have hG' : ∀ x ∈ Γ, (encFormula x).length ≤ G := fun x hx => hG x (List.mem_cons_of_mem _ hx)
    have ihΓ := ih hG'
    set X := Frege.Formula.imps Γ (.imp A B)
    set Y := Frege.Formula.imps Γ A
    set Z := Frege.Formula.imps Γ B
    have hX : (encFormula X).length ≤
        Γ.length * (G + 10) + (encFormula A).length + (encFormula B).length + 10 := by
      have h0 := length_encFormula_imps_le (B := G) (Proposition.imp A B) hG'
      rw [encFormula_imp, List.length_append, List.length_append] at h0; linarith
    have hY := length_encFormula_imps_le (B := G) A hG'
    have hZ := length_encFormula_imps_le (B := G) B hG'
    have d1 := (BoundedFrege.ax (Frege.IsAxiom.k (.imp X (.imp Y Z)) γ)).mp ihΓ
    have d2 := (BoundedFrege.ax (Frege.IsAxiom.s γ X (.imp Y Z))).mp d1
    let sYZ : Formula := .imp (.imp γ (.imp Y Z)) (.imp (.imp γ Y) (.imp γ Z))
    have d3 := (BoundedFrege.ax (Frege.IsAxiom.k sYZ (.imp γ X))).mp
      (BoundedFrege.ax (Frege.IsAxiom.s γ Y Z))
    have d4 := (BoundedFrege.ax
      (Frege.IsAxiom.s (.imp γ X) (.imp γ (.imp Y Z)) (.imp (.imp γ Y) (.imp γ Z)))).mp d3
    refine (d4.mp d2).mono (by simp; omega) ?_
    simp only [sYZ, encFormula_imp, List.length_append, List.length_cons, max_le_iff]
    exact ⟨⟨by nlinarith, by nlinarith, by nlinarith⟩,
      by nlinarith, by nlinarith, by nlinarith⟩

/-- Modus ponens under an antecedent context `Γ`. -/
private theorem BoundedFrege.imps_mp (Γ : List Formula) {A B : Formula} {S₁ S₂ M₁ M₂ G : ℕ}
    (hAB : BoundedFrege (Frege.Formula.imps Γ (.imp A B)) S₁ M₁)
    (hA : BoundedFrege (Frege.Formula.imps Γ A) S₂ M₂)
    (hG : ∀ γ ∈ Γ, (encFormula γ).length ≤ G) :
    BoundedFrege (Frege.Formula.imps Γ B) (S₁ + S₂ + 10 * Γ.length + 7)
      (max (max M₁ M₂)
        (20 * ((Γ.length + 1) * (G + 20) + (encFormula A).length + (encFormula B).length))) := by
  refine (((BoundedFrege.imps_dist Γ A B hG).mp hAB).mp hA).mono (by omega) ?_
  simp only [max_le_iff]
  exact ⟨⟨le_max_right _ _, le_max_of_le_left (le_max_left _ _)⟩,
    le_max_of_le_left (le_max_right _ _)⟩

/-- Instantiate a fixed schema tautology `ψ ∈ TAUT` with bounded line count and encoded size. -/
private theorem BoundedFrege.of_schema {ψ : Formula} {L₀ : List Formula}
    (hL₀ : Frege.IsProof [] L₀) (hψ : ψ ∈ L₀) (f : ℕ → Formula) {K : ℕ}
    (hK : ∀ v, (encFormula (f v)).length ≤ K) :
    let T := L₀.foldr (fun θ acc => max (encFormula θ).length acc) 0
    BoundedFrege (ψ.subst f) L₀.length (T * (K + 1)) := by
  intro T
  have hθ_le : ∀ θ ∈ L₀, (encFormula (θ.subst f)).length ≤ T * (K + 1) := by
    intro θ hθ
    have hT : (encFormula θ).length ≤ T := by
      suffices ∀ ls : List Formula, θ ∈ ls →
          (encFormula θ).length ≤ ls.foldr (fun ψ acc => max (encFormula ψ).length acc) 0 from
        this L₀ hθ
      intro ls; induction ls with
      | nil => intro h; cases h
      | cons x xs ih =>
        intro h; rcases List.mem_cons.1 h with rfl | h'
        · exact le_max_left _ _
        · exact (ih h').trans (le_max_right _ _)
    rw [encFormula_apply, toPostfix_subst]
    rw [encFormula_apply] at hT
    suffices ∀ ts : List FormTok,
        (encList encFormTok (ts.flatMap fun
          | .inl v => toPostfix (f v) | .inr op => [.inr op])).length ≤
          (encList encFormTok ts).length * (K + 1) from
      (this (toPostfix θ)).trans (Nat.mul_le_mul_right _ hT)
    intro ts
    induction ts with
    | nil => simp
    | cons t ts ih =>
      cases t with
      | inl v =>
        have hv := hK v; rw [encFormula_apply] at hv
        simp only [List.flatMap_cons, encList_append, encList_cons, List.length_append,
          length_frame]
        nlinarith
      | inr op =>
        simp only [List.flatMap_cons, encList_append, encList_cons, encList_nil, List.append_nil,
          List.length_append, length_frame]
        nlinarith
  exact ⟨L₀.map (Proposition.subst f), fregeIsProof_subst f hL₀, List.mem_map_of_mem hψ,
    by simp, fun _ h => by obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 h; exact hθ_le θ hθ⟩

/-- Binary disjunction monotonicity schema `(A → A') → (B → B') → (A ∨ B → A' ∨ B')`. -/
private def orMonoSchema : Formula :=
  .imp (.imp (.atom 0) (.atom 1))
    (.imp (.imp (.atom 2) (.atom 3))
      (.imp (.or (.atom 0) (.atom 2)) (.or (.atom 1) (.atom 3))))

private theorem orMonoSchema_mem_taut : orMonoSchema ∈ TAUT := by
  intro σ
  simp only [orMonoSchema, Proposition.eval_imp_bool, Proposition.eval_or_bool,
    Proposition.eval_atom_bool]
  cases σ 0 <;> cases σ 1 <;> cases σ 2 <;> cases σ 3 <;> rfl

/-- Bounded Frege proof of `bigOr αs → bigOr βs` from pointwise bounded proofs of `αᵢ → βᵢ`. -/
private theorem BoundedFrege.bigOr_imp_bigOr :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ {αs βs : List Formula} {S M : ℕ},
      αs.length = βs.length →
      (∀ i (h₁ : i < αs.length) (h₂ : i < βs.length),
        BoundedFrege (.imp αs[i] βs[i]) S M) →
      (∀ α ∈ αs, (encFormula α).length ≤ M) →
      (∀ β ∈ βs, (encFormula β).length ≤ M) →
      BoundedFrege (.imp (bigOr αs) (bigOr βs))
        ((αs.length + 1) * (S + C)) (C * (αs.length + 1) * (M + 20)) := by
  obtain ⟨L₀, hL₀, hmem⟩ := frege_complete orMonoSchema_mem_taut
  let T := L₀.foldr (fun θ acc => max (encFormula θ).length acc) 0
  set C := L₀.length + T + 30
  have hLC : L₀.length + 10 ≤ C := by dsimp only [C]; omega
  have hTC : T + 20 ≤ C := by dsimp only [C]; omega
  refine ⟨C, by omega, ?_⟩
  intro αs
  induction αs with
  | nil =>
    intro βs S M hlen _ _ _
    cases βs with
    | nil =>
      refine (BoundedFrege.id .falsum).mono (by simp only [List.length_nil]; nlinarith) ?_
      have : (encFormula .falsum).length ≤ 10 := by decide
      simp only [List.length_nil, zero_add]; nlinarith
    | cons _ _ => simp at hlen
  | cons α rest ih =>
    intro βs S M hlen hpt hαs hβs
    cases βs with
    | nil => simp at hlen
    | cons β brest =>
      have h0 := hpt 0 (by simp) (by simp)
      cases rest with
      | nil =>
        cases brest with
        | nil =>
          exact h0.mono (by simp only [List.length_cons, List.length_nil]; nlinarith)
            (by simp only [List.length_cons, List.length_nil]; nlinarith)
        | cons _ _ => simp at hlen
      | cons α₂ atail =>
        cases brest with
        | nil => simp at hlen
        | cons β₂ btail =>
          have htl : atail.length = btail.length := by
            simp only [List.length_cons] at hlen; omega
          have htail := ih (βs := β₂ :: btail) (by simp [htl])
            (fun i h₁ h₂ => hpt (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂))
            (fun x hx => hαs x (List.mem_cons_of_mem _ hx))
            (fun x hx => hβs x (List.mem_cons_of_mem _ hx))
          set rA := bigOr (α₂ :: atail)
          set rB := bigOr (β₂ :: btail)
          let K := (atail.length + 2) * (M + 10)
          have hrA : (encFormula rA).length ≤ K := by
            simpa [K] using length_encFormula_bigOr_le
              (fun x hx => hαs x (List.mem_cons_of_mem _ hx))
          have hrB : (encFormula rB).length ≤ K := by
            simpa [K, htl.symm] using length_encFormula_bigOr_le
              (fun x hx => hβs x (List.mem_cons_of_mem _ hx))
          let sub : ℕ → Formula
            | 0 => α | 1 => β | 2 => rA | 3 => rB | _ => .falsum
          have hsub (v : ℕ) : (encFormula (sub v)).length ≤ K := by
            have hbot : (encFormula .falsum).length ≤ 10 := by decide
            have hαM := hαs α List.mem_cons_self
            have hβM := hβs β List.mem_cons_self
            match v with
            | 0 => exact hαM.trans (by dsimp only [K]; nlinarith)
            | 1 => exact hβM.trans (by dsimp only [K]; nlinarith)
            | 2 => exact hrA
            | 3 => exact hrB
            | _ + 4 => exact hbot.trans (by dsimp only [K]; nlinarith)
          have hsc := BoundedFrege.of_schema hL₀ hmem sub hsub
          have hcomb := (hsc.mp h0).mp htail
          refine hcomb.mono (by simp only [List.length_cons]; nlinarith) ?_
          simp only [List.length_cons, max_le_iff]
          have h1 : T * (K + 1) ≤ C * (atail.length + 3) * (M + 20) := by
            have : K + 1 ≤ (atail.length + 3) * (M + 20) := by dsimp only [K]; nlinarith
            calc T * (K + 1) ≤ C * ((atail.length + 3) * (M + 20)) := Nat.mul_le_mul (by omega) this
              _ = C * (atail.length + 3) * (M + 20) := by ring
          have h2 : C * (atail.length + 2) * (M + 20) ≤ C * (atail.length + 3) * (M + 20) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left C (by omega))
          exact ⟨⟨h1, by nlinarith⟩, h2⟩

/-- Bounded Frege proof of `(bigOr l₁ ∨ bigOr l₂) → bigOr (l₁ ++ l₂)`. -/
private theorem frege_bigOr_append :
    ∃ D : ℕ, 20 ≤ D ∧ ∀ (l₁ l₂ : List Formula) (B : ℕ),
      (∀ α ∈ l₁, (encFormula α).length ≤ B) → (∀ α ∈ l₂, (encFormula α).length ≤ B) →
      BoundedFrege (.imp (.or (bigOr l₁) (bigOr l₂)) (bigOr (l₁ ++ l₂)))
        ((l₁.length + 1) * D) (D * (l₁.length + l₂.length + 2) * (B + 20)) := by
  let scBotOr : Formula := .imp (.or .falsum (.atom 0)) (.atom 0)
  let scOrBot : Formula := .imp (.or (.atom 0) .falsum) (.atom 0)
  let scAssoc : Formula :=
    .imp (.imp (.or (.atom 1) (.atom 2)) (.atom 3))
      (.imp (.or (.or (.atom 0) (.atom 1)) (.atom 2)) (.or (.atom 0) (.atom 3)))
  obtain ⟨L2, hL2, hm2⟩ := frege_complete (show scBotOr ∈ TAUT from fun _ => by simp [scBotOr])
  obtain ⟨L3, hL3, hm3⟩ := frege_complete (show scOrBot ∈ TAUT from fun _ => by simp [scOrBot])
  obtain ⟨L4, hL4, hm4⟩ := frege_complete (show scAssoc ∈ TAUT from fun σ => by
    simp only [scAssoc, Proposition.eval_imp_bool, Proposition.eval_or_bool,
      Proposition.eval_atom_bool]
    cases σ 0 <;> cases σ 1 <;> cases σ 2 <;> cases σ 3 <;> rfl)
  let mxL (L : List Formula) := L.foldr (fun θ acc => max (encFormula θ).length acc) 0
  let D : ℕ := L2.length + L3.length + L4.length + mxL L2 + mxL L3 + mxL L4 + 30
  refine ⟨D, by dsimp only [D]; omega, ?_⟩
  intro l₁; induction l₁ with
  | nil =>
    intro l₂ B _ hl₂
    have hK := length_encFormula_bigOr_le hl₂
    refine (BoundedFrege.of_schema hL2 hm2 (fun _ => bigOr l₂) (fun _ => hK)).mono
      (by simp [D]; omega) ?_
    have h1 : (l₂.length + 1) * (B + 10) + 1 ≤ (l₂.length + 2) * (B + 20) := by nlinarith
    simpa only [List.length_nil, zero_add, Nat.mul_assoc] using
      Nat.mul_le_mul (show mxL L2 ≤ D by dsimp only [D]; omega) h1
  | cons α rest ih =>
    intro l₂ B hl₁ hl₂
    have hα := hl₁ α List.mem_cons_self
    cases rest with
    | nil =>
      cases l₂ with
      | nil =>
        refine (BoundedFrege.of_schema hL3 hm3 (fun _ => α) (fun _ => hα)).mono
          (by simp [D]; omega) ?_
        simpa only [List.length_cons, List.length_nil, Nat.mul_assoc] using
          Nat.mul_le_mul (show mxL L3 ≤ D by dsimp only [D]; omega) (by omega : B + 1 ≤
            3 * (B + 20))
      | cons β btail =>
        have hK := length_encFormula_bigOr_le (αs := α :: β :: btail) (B := B)
          (fun x hx => by rcases List.mem_cons.1 hx with rfl | h; exacts [hα, hl₂ x h])
        refine (BoundedFrege.id (bigOr (α :: β :: btail))).mono (by simp [D]; omega) ?_
        simp only [List.length_cons, List.length_nil] at hK ⊢
        calc 9 * (encFormula (bigOr (α :: β :: btail))).length + 100
            ≤ 20 * ((btail.length + 4) * (B + 20)) := by nlinarith
          _ ≤ D * ((btail.length + 4) * (B + 20)) :=
              Nat.mul_le_mul_right _ (by dsimp only [D]; omega)
          _ = D * (0 + 1 + (btail.length + 1) + 2) * (B + 20) := by ring
    | cons α₂ atail =>
      have ihr := ih l₂ B (fun x hx => hl₁ x (List.mem_cons_of_mem _ hx)) hl₂
      let K := (atail.length + l₂.length + 3) * (B + 10)
      let sub : ℕ → Formula
        | 0 => α | 1 => bigOr (α₂ :: atail) | 2 => bigOr l₂
        | 3 => bigOr ((α₂ :: atail) ++ l₂) | _ => .falsum
      have hsub (v : ℕ) : (encFormula (sub v)).length ≤ K := by
        have hbot : (encFormula .falsum).length ≤ 10 := by decide
        have h1 := length_encFormula_bigOr_le (αs := α₂ :: atail) (B := B)
          (fun x hx => hl₁ x (List.mem_cons_of_mem _ hx))
        have h2 := length_encFormula_bigOr_le hl₂
        have h3 := length_encFormula_bigOr_le (αs := (α₂ :: atail) ++ l₂) (B := B)
          (fun x hx => (List.mem_append.1 hx).elim
            (fun h => hl₁ x (List.mem_cons_of_mem _ h)) (hl₂ x))
        simp only [List.length_append, List.length_cons] at h1 h3
        match v with
        | 0 => exact hα.trans (by dsimp only [K]; nlinarith)
        | 1 => exact h1.trans (by dsimp only [K]; nlinarith)
        | 2 => exact h2.trans (by dsimp only [K]; nlinarith)
        | 3 => exact h3.trans (by dsimp only [K]; nlinarith)
        | _ + 4 => exact hbot.trans (by dsimp only [K]; nlinarith)
      refine ((BoundedFrege.of_schema hL4 hm4 sub hsub).mp ihr).mono
        (by simp only [List.length_cons]; have : L4.length + 1 ≤ D := by dsimp only [D]; omega
            nlinarith)
        (max_le ?_ (by simp only [List.length_cons]
                       exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left D (by omega))))
      have hK1 : K + 1 ≤ ((α :: α₂ :: atail).length + l₂.length + 2) * (B + 20) := by
        dsimp only [K]; simp only [List.length_cons]; nlinarith
      simpa only [Nat.mul_assoc] using
        Nat.mul_le_mul (show mxL L4 ≤ D by dsimp only [D]; omega) hK1

/-- **Polynomial-size verified Frege flattening of nested disjunctions.** For every list of formula
lists `groups : List (List Formula)`, there exists a verified `EF` derivation of
`bigOr (groups.map bigOr) → bigOr groups.flatten` of polynomial encoded length. -/
theorem exists_frege_bigOr_flatten :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (groups : List (List Formula)) (B : ℕ),
      (∀ g ∈ groups, ∀ α ∈ g, (encFormula α).length ≤ B) →
      ∃ steps : List EFStep,
        runEFProof (fun _ => false) steps =
          .imp (bigOr (groups.map bigOr)) (bigOr groups.flatten) ∧
        (encList encEFStep steps).length ≤
          C * (groups.length + groups.flatten.length + 2) ^ 4 * (B + 20) := by
  obtain ⟨Da, hDa20, happ⟩ := frege_bigOr_append
  let scStep : Formula :=
    .imp (.imp (.atom 1) (.atom 2))
      (.imp (.imp (.or (.atom 0) (.atom 2)) (.atom 3))
        (.imp (.or (.atom 0) (.atom 1)) (.atom 3)))
  obtain ⟨L5, hL5, hm5⟩ := frege_complete (show scStep ∈ TAUT from fun σ => by
    simp only [scStep, Proposition.eval_imp_bool, Proposition.eval_or_bool,
      Proposition.eval_atom_bool]
    cases σ 0 <;> cases σ 1 <;> cases σ 2 <;> cases σ 3 <;> rfl)
  let mx5 := L5.foldr (fun θ acc => max (encFormula θ).length acc) 0
  let D : ℕ := Da + L5.length + mx5 + 30
  have hD20 : 20 ≤ D := by dsimp only [D]; omega
  have hmap_bd : ∀ (ls : List (List Formula)) (B : ℕ),
      (∀ x ∈ ls, ∀ α ∈ x, (encFormula α).length ≤ B) →
      (encFormula (bigOr (ls.map bigOr))).length ≤
        (ls.length + ls.flatten.length + 1) * (B + 20) := by
    have hop2 : (frame (encFormTok (.inr 2))).length ≤ 10 := by decide
    have hbot : (encFormula .falsum).length ≤ 10 := by decide
    intro ls B; induction ls with
    | nil => intro _; simp; omega
    | cons x xs ihx =>
      intro hls
      have hx := length_encFormula_bigOr_le (hls x List.mem_cons_self)
      cases xs with
      | nil =>
        simp only [List.map_cons, List.map_nil, bigOr_singleton, List.length_cons,
          List.length_nil, List.flatten_cons, List.flatten_nil, List.append_nil]; nlinarith
      | cons y ys =>
        have ihs := ihx fun z hz => hls z (List.mem_cons_of_mem _ hz)
        simp only [List.map_cons, bigOr_cons_cons, encFormula_or, List.length_append,
          List.length_cons, List.flatten_cons] at ihs ⊢; nlinarith
  have hflat : ∀ (gs : List (List Formula)) (B : ℕ),
      (∀ g ∈ gs, ∀ α ∈ g, (encFormula α).length ≤ B) →
      BoundedFrege (.imp (bigOr (gs.map bigOr)) (bigOr gs.flatten))
        ((gs.length + gs.flatten.length + 1) ^ 2 * D)
        (D * (gs.length + gs.flatten.length + 2) * (B + 25)) := by
    intro gs B; induction gs with
    | nil =>
      intro _
      have hbot : (encFormula .falsum).length ≤ 10 := by decide
      exact (BoundedFrege.id .falsum).mono (by simp; omega) (by simp; nlinarith)
    | cons g rest ih =>
      intro hgs
      have hg := hgs g List.mem_cons_self
      cases rest with
      | nil =>
        have hK := length_encFormula_bigOr_le hg
        simp only [List.map_cons, List.map_nil, bigOr_singleton, List.flatten_cons,
          List.flatten_nil, List.append_nil, List.length_cons, List.length_nil, zero_add]
        refine (BoundedFrege.id (bigOr g)).mono (by nlinarith) ?_
        calc 9 * (encFormula (bigOr g)).length + 100
            ≤ 20 * ((g.length + 3) * (B + 25)) := by nlinarith
          _ ≤ D * ((g.length + 3) * (B + 25)) := Nat.mul_le_mul_right _ hD20
          _ = D * (1 + g.length + 2) * (B + 25) := by ring
      | cons g₂ gtail =>
        have hrest : ∀ x ∈ g₂ :: gtail, ∀ α ∈ x, (encFormula α).length ≤ B :=
          fun x hx => hgs x (List.mem_cons_of_mem _ hx)
        have ihr := ih hrest
        have hap := happ g (g₂ :: gtail).flatten B hg fun α hα => by
          obtain ⟨x, hx, hαx⟩ := List.mem_flatten.1 hα; exact hrest x hx α hαx
        set N := (g :: g₂ :: gtail).length + (g :: g₂ :: gtail).flatten.length
        let K := (N + 1) * (B + 20)
        have hNr : (g₂ :: gtail).length + (g₂ :: gtail).flatten.length + 1 ≤ N := by
          dsimp only [N]; simp only [List.length_cons, List.flatten_cons, List.length_append]; omega
        have hNa : g.length + (g₂ :: gtail).flatten.length + 2 ≤ N := by
          dsimp only [N]; simp only [List.length_cons, List.flatten_cons, List.length_append]; omega
        let sub : ℕ → Formula
          | 0 => bigOr g | 1 => bigOr ((g₂ :: gtail).map bigOr)
          | 2 => bigOr (g₂ :: gtail).flatten | 3 => bigOr (g ++ (g₂ :: gtail).flatten)
          | _ => .falsum
        have hsub (v : ℕ) : (encFormula (sub v)).length ≤ K := by
          have hbot : (encFormula .falsum).length ≤ 10 := by decide
          have hflt : ∀ α ∈ (g₂ :: gtail).flatten, (encFormula α).length ≤ B := fun α hα => by
            obtain ⟨x, hx, hαx⟩ := List.mem_flatten.1 hα; exact hrest x hx α hαx
          have happB : ∀ α ∈ g ++ (g₂ :: gtail).flatten, (encFormula α).length ≤ B :=
            fun α hα => (List.mem_append.1 hα).elim (hg α) (hflt α)
          match v with
          | 0 =>
            exact (length_encFormula_bigOr_le hg).trans (Nat.mul_le_mul (by omega) (by omega))
          | 1 =>
            exact (hmap_bd _ B hrest).trans (Nat.mul_le_mul_right _ (by omega))
          | 2 =>
            exact (length_encFormula_bigOr_le hflt).trans (Nat.mul_le_mul (by omega) (by omega))
          | 3 =>
            have h3 := length_encFormula_bigOr_le happB
            rw [List.length_append] at h3
            exact h3.trans (Nat.mul_le_mul (by omega) (by omega))
          | _ + 4 =>
            exact hbot.trans (by dsimp only [K]; nlinarith)
        refine (((BoundedFrege.of_schema hL5 hm5 sub hsub).mp ihr).mp hap).mono ?_
          (max_le (max_le ?_ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left D (by omega))))
            (Nat.mul_le_mul (Nat.mul_le_mul (by dsimp only [D]; omega) (by omega)) (by omega)))
        · have hL5D : L5.length + 2 ≤ D := by dsimp only [D]; omega
          have hDaD : Da ≤ D := by dsimp only [D]; omega
          set r := (g₂ :: gtail).length + (g₂ :: gtail).flatten.length
          have hNr_eq : N = g.length + r + 1 := by
            dsimp only [N, r]; simp only [List.length_cons, List.flatten_cons, List.length_append]
            omega
          have hsq : 1 + (r + 1) ^ 2 + (g.length + 1) ≤ (N + 1) ^ 2 := by rw [hNr_eq]; nlinarith
          calc L5.length + (r + 1) ^ 2 * D + 1 + (g.length + 1) * Da + 1
              ≤ D + (r + 1) ^ 2 * D + (g.length + 1) * D := by
                have := Nat.mul_le_mul_left (g.length + 1) hDaD; omega
            _ = (1 + (r + 1) ^ 2 + (g.length + 1)) * D := by ring
            _ ≤ (N + 1) ^ 2 * D := Nat.mul_le_mul_right D hsq
        · have hK1 : K + 1 ≤ (N + 2) * (B + 25) := by dsimp only [K]; nlinarith
          simpa only [Nat.mul_assoc] using
            Nat.mul_le_mul (show mx5 ≤ D by dsimp only [D]; omega) hK1
  refine ⟨640 * (D + 20) ^ 2, Nat.succ_le_of_lt (by positivity), fun groups B hB => ?_⟩
  obtain ⟨L, hL, hmem, hS, hM⟩ := hflat groups B hB
  obtain ⟨steps, hrun, hlen⟩ := exists_runEFProof_of_fregeIsProof hL hmem (fun _ => false) hM
  refine ⟨steps, hrun, hlen.trans ?_⟩
  set N := groups.length + groups.flatten.length
  have h1 : L.length + 6 ≤ (N + 2) ^ 2 * (D + 6) :=
    calc L.length + 6 ≤ (N + 1) ^ 2 * D + 6 := Nat.add_le_add_right hS 6
      _ ≤ (N + 2) ^ 2 * D + (N + 2) ^ 2 * 6 :=
          Nat.add_le_add (Nat.mul_le_mul_right D (by nlinarith)) (by nlinarith)
      _ = (N + 2) ^ 2 * (D + 6) := by ring
  have h2 : 9 * (D * (N + 2) * (B + 25)) + L.length + 160 ≤
      20 * (D + 20) * (N + 2) ^ 2 * (B + 20) := by
    have h9 : 9 * (D * (N + 2) * (B + 25)) ≤ 12 * (D + 20) * ((N + 2) ^ 2 * (B + 20)) :=
      calc 9 * (D * (N + 2) * (B + 25)) = 3 * D * (N + 2) * (3 * (B + 25)) := by ring
        _ ≤ 3 * (D + 20) * (N + 2) ^ 2 * (4 * (B + 20)) :=
            Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by nlinarith)) (by omega)
        _ = 12 * (D + 20) * ((N + 2) ^ 2 * (B + 20)) := by ring
    have hL2 : L.length + 160 ≤ 8 * (D + 20) * ((N + 2) ^ 2 * (B + 20)) :=
      calc L.length + 160 ≤ (N + 2) ^ 2 * (D + 6) + 40 * (N + 2) ^ 2 := by
            have h160 : 160 ≤ 40 * (N + 2) ^ 2 := by nlinarith
            omega
        _ = (D + 46) * (N + 2) ^ 2 := by ring
        _ ≤ 8 * (D + 20) * (N + 2) ^ 2 := Nat.mul_le_mul_right _ (by omega)
        _ ≤ 8 * (D + 20) * (N + 2) ^ 2 * (B + 20) := Nat.le_mul_of_pos_right _ (by omega)
        _ = 8 * (D + 20) * ((N + 2) ^ 2 * (B + 20)) := by ring
    linarith
  calc 32 * (L.length + 6) * (9 * (D * (N + 2) * (B + 25)) + L.length + 160)
      ≤ 32 * ((N + 2) ^ 2 * (D + 6)) * (20 * (D + 20) * (N + 2) ^ 2 * (B + 20)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 32 h1) h2
    _ = 640 * ((D + 6) * (D + 20)) * ((N + 2) ^ 4 * (B + 20)) := by ring
    _ ≤ 640 * (D + 20) ^ 2 * ((N + 2) ^ 4 * (B + 20)) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 640 (by nlinarith))
    _ = 640 * (D + 20) ^ 2 * (N + 2) ^ 4 * (B + 20) := by ring

/-! ### Polynomial-size Frege circuit-specialization theorem -/

/-- Target of a wire under a Boolean circuit specialization: either a fixed Boolean constant
`.inl val`, a positive target wire `.inr (false, w)`, or a negated target wire `.inr (true, w)`. -/
abbrev WireSim (n g : ℕ) : Type := Bool ⊕ (Bool × Wire n g)

/-- Convert a `WireSim n g` into its substituting propositional formula over standard atoms
`stdWireAtom 0 n`. -/
@[expose]
def wireSimFormula {n g : ℕ} : WireSim n g → Formula
  | .inl false => .falsum
  | .inl true => .imp .falsum .falsum
  | .inr (false, w) => .atom (stdWireAtom 0 n w)
  | .inr (true, w) => .imp (.atom (stdWireAtom 0 n w)) .falsum

/-- Evaluate a `WireSim n g` semantically given wire values `wv : Wire n g → Bool`. -/
def wireSimEval {n g : ℕ} (wv : Wire n g → Bool) : WireSim n g → Bool
  | .inl b => b
  | .inr (neg, w) => if neg then !wv w else wv w

/-- Boolean evaluation of `wireSimFormula` agrees with `wireSimEval`. -/
@[simp]
theorem eval_wireSimFormula {n g : ℕ} (s : WireSim n g) (σ : ℕ → Bool) :
    (wireSimFormula s).eval σ = wireSimEval (fun w => σ (stdWireAtom 0 n w)) s := by
  rcases s with (_ | _) | ⟨_ | _, w⟩ <;> simp [wireSimFormula, wireSimEval]

/-- One-variable symbolic value: either `.inl b` (constant `b`) or `.inr neg` (atom `0` if
`neg = false`, `¬ atom 0` if `neg = true`). -/
abbrev OneVarSim : Type := Bool ⊕ Bool

/-- Convert a `OneVarSim` into a `Formula` over the single atom `0`. -/
@[expose]
def oneVarFormula : OneVarSim → Formula
  | .inl false => .falsum
  | .inl true => .imp .falsum .falsum
  | .inr false => .atom 0
  | .inr true => .imp (.atom 0) .falsum

/-- Lift a `OneVarSim` to a `WireSim n g` anchored at target wire `w`. -/
@[expose]
def liftOneVar {n g : ℕ} (w : Wire n g) : OneVarSim → WireSim n g
  | .inl b => .inl b
  | .inr neg => .inr (neg, w)

/-- Lifting a constant `OneVarSim` yields `.inl b`. -/
@[simp] theorem liftOneVar_inl {n g : ℕ} (w : Wire n g) (b : Bool) :
    liftOneVar w (.inl b) = .inl b := rfl

/-- Lifting a literal `OneVarSim` anchors it at target wire `w`. -/
@[simp] theorem liftOneVar_inr {n g : ℕ} (w : Wire n g) (neg : Bool) :
    liftOneVar w (.inr neg) = .inr (neg, w) := rfl

/-- Substituting `stdWireAtom 0 n w` into `oneVarFormula e` produces
`wireSimFormula (liftOneVar w e)`. -/
@[simp]
theorem subst_oneVarFormula {n g : ℕ} (w : Wire n g) (e : OneVarSim) :
    (oneVarFormula e).subst (fun _ => .atom (stdWireAtom 0 n w)) =
      wireSimFormula (liftOneVar w e) := by
  rcases e with (_ | _) | (_ | _) <;> rfl

/-- Boolean evaluation of a `OneVarSim` on a single Boolean variable `v`. -/
@[expose] def evalOneVar (v : Bool) : OneVarSim → Bool
  | .inl b => b
  | .inr neg => if neg then !v else v

/-- Evaluating a constant `OneVarSim` returns that constant. -/
@[simp] theorem evalOneVar_inl (v b : Bool) : evalOneVar v (.inl b) = b := rfl
/-- Evaluating a literal `OneVarSim` returns `v` or `!v`. -/
@[simp] theorem evalOneVar_inr (v neg : Bool) :
    evalOneVar v (.inr neg) = if neg then !v else v := rfl

/-- One-variable gate-equation template over atom `0` for gate opcode `op`, output `eOut`, and
operands `e0, e1`. -/
@[expose]
def oneVarGateTemplate (op : Boolean.Op) (eOut e0 e1 : OneVarSim) : Formula :=
  let rhs : Formula := match op with
    | .const false => .falsum
    | .const true => .imp .falsum .falsum
    | .not => .imp (oneVarFormula e0) .falsum
    | .and => .and (oneVarFormula e0) (oneVarFormula e1)
    | .or => .or (oneVarFormula e0) (oneVarFormula e1)
  formulaIff (oneVarFormula eOut) rhs

/-- Semantic criterion for `oneVarGateTemplate op eOut e0 e1 ∈ TAUT` via Boolean evaluation on the
single variable `v : Bool`. -/
theorem oneVarGateTemplate_mem_taut_of_eq (op : Boolean.Op) (eOut e0 e1 : OneVarSim)
    (h : ∀ v : Bool, evalOneVar v eOut = match op with
      | .const b => b
      | .not => !evalOneVar v e0
      | .and => evalOneVar v e0 && evalOneVar v e1
      | .or => evalOneVar v e0 || evalOneVar v e1) :
    oneVarGateTemplate op eOut e0 e1 ∈ TAUT := by
  have hev (e : OneVarSim) (σ : ℕ → Bool) : (oneVarFormula e).eval σ = evalOneVar (σ 0) e := by
    rcases e with (_ | _) | (_ | _) <;> simp [oneVarFormula, evalOneVar]
  intro σ
  dsimp only [oneVarGateTemplate]
  rw [eval_formulaIff_eq_true, hev]
  cases op with
  | const b => cases b <;> simpa using h (σ 0)
  | not => simpa [hev] using h (σ 0)
  | and => simpa [hev] using h (σ 0)
  | or => simpa [hev] using h (σ 0)

/-- Per-gate validity of a circuit specialization `sim : Wire n' c'.size → WireSim n c.size`:
gate `k'` of `c'` is EITHER a faithful copy of some gate `k` of `c`, OR collapses to a `1`-variable
propositional tautology anchored at some target wire `w` (or constant `0`). -/
@[expose]
def IsGateSim {n' m' n m : ℕ} (c' : Circuit signature n' m') (c : Circuit signature n m)
    (sim : Wire n' c'.size → WireSim n c.size) (k' : Fin c'.size) : Prop :=
  let l' := c'.program.lines k'
  (∃ (k : Fin c.size) (hop : l'.op = (c.program.lines k).op),
    sim (.gate k') = .inr (false, .gate k) ∧
    ∀ a : Fin (signature.Arity l'.op),
      sim (l'.wires a) =
        .inr (false, (c.program.lines k).wires (a.cast (congrArg signature.Arity hop)))) ∨
  (∃ (eOut e0 e1 : OneVarSim),
    oneVarGateTemplate l'.op eOut e0 e1 ∈ TAUT ∧
    ((n + c.size = 0 ∧ ∃ bOut b0 b1,
      eOut = .inl bOut ∧ e0 = .inl b0 ∧ e1 = .inl b1 ∧
      sim (.gate k') = .inl bOut ∧
      (∀ a : Fin (signature.Arity l'.op),
        sim (l'.wires a) = .inl (if a.val = 0 then b0 else b1))) ∨
     (∃ w : Wire n c.size,
      sim (.gate k') = liftOneVar w eOut ∧
      ∀ a : Fin (signature.Arity l'.op),
        sim (l'.wires a) = liftOneVar w (if a.val = 0 then e0 else e1))))

/-- Direct gate-copy constructor for `IsGateSim`. -/
theorem isGateSim_of_preserve {n' m' n m : ℕ} {c' : Circuit signature n' m'}
    {c : Circuit signature n m} {sim : Wire n' c'.size → WireSim n c.size} {k' : Fin c'.size}
    (k : Fin c.size) (hop : (c'.program.lines k').op = (c.program.lines k).op)
    (hout : sim (.gate k') = .inr (false, .gate k))
    (hw : ∀ a : Fin (signature.Arity (c'.program.lines k').op),
      sim ((c'.program.lines k').wires a) =
        .inr (false, (c.program.lines k).wires (a.cast (congrArg signature.Arity hop)))) :
    IsGateSim c' c sim k' :=
  Or.inl ⟨k, hop, hout, hw⟩

/-- Helper: any single-variable gate where every operand is either a constant `.inl _` or shares a
single target wire `w`, and whose semantic gate relation holds for both values of `w`, satisfies
`IsGateSim`. -/
theorem isGateSim_of_oneVar {n' m' n m : ℕ} {c' : Circuit signature n' m'}
    {c : Circuit signature n m} {sim : Wire n' c'.size → WireSim n c.size} {k' : Fin c'.size}
    (w : Wire n c.size) (eOut e0 e1 : OneVarSim)
    (hout : sim (.gate k') = liftOneVar w eOut)
    (hargs : ∀ a : Fin (signature.Arity (c'.program.lines k').op),
      sim ((c'.program.lines k').wires a) = liftOneVar w (if a.val = 0 then e0 else e1))
    (htaut : oneVarGateTemplate (c'.program.lines k').op eOut e0 e1 ∈ TAUT) :
    IsGateSim c' c sim k' :=
  Or.inr ⟨eOut, e0, e1, htaut, Or.inr ⟨w, hout, hargs⟩⟩

/-- Per-output validity of a specialization `sim` carrying target `b` of `c'` to target `a` of `c`:
for each output `j : Fin m`, `sim (c'.outputs j)` is either constant `b j` (impossible mismatch),
positive `c.outputs j` with `b j = a j`, or negated `c.outputs j` with `b j = !a j`. -/
@[expose]
def IsOutputSim {n' n m : ℕ} (c' : Circuit signature n' m) (c : Circuit signature n m)
    (sim : Wire n' c'.size → WireSim n c.size) (b a : BitString m) : Prop :=
  ∀ j : Fin m,
    sim (c'.outputs j) = .inl (b j) ∨
    (sim (c'.outputs j) = .inr (false, c.outputs j) ∧ b j = a j) ∨
    (sim (c'.outputs j) = .inr (true, c.outputs j) ∧ b j = !a j)

/-- Canonical association list realizing a circuit specialization `sim` on all standard atoms of
`c'` starting at `0`. -/
@[expose]
def wireSimPairs {n' g' n g : ℕ} (sim : Wire n' g' → WireSim n g) : List (ℕ × Formula) :=
  ((List.finRange n').map fun i => (i.val, wireSimFormula (sim (.input i)))) ++
  ((List.finRange g').map fun k => (n' + k.val, wireSimFormula (sim (.gate k))))

/-- Splitting `wireSimPairs sim` at an input prefix length `ℓ ≤ n'`. -/
theorem wireSimPairs_drop_of_le {n' g' n g ℓ : ℕ} (hℓ : ℓ ≤ n')
    (sim : Wire n' g' → WireSim n g) :
    wireSimPairs sim =
      ((List.finRange n').take ℓ).map (fun i => (i.val, wireSimFormula (sim (.input i)))) ++
        (wireSimPairs sim).drop ℓ := by
  dsimp only [wireSimPairs]
  rw [List.drop_append_of_le_length (by rw [List.length_map, List.length_finRange]; exact hℓ),
    List.map_take, ← List.append_assoc, List.take_append_drop]

/-- Looking up a standard wire atom of `c'` in `wireSimPairs sim` gives `wireSimFormula (sim w)`. -/
@[simp]
theorem listSubst_wireSimPairs {n' g' n g : ℕ} (sim : Wire n' g' → WireSim n g)
    (w : Wire n' g') :
    listSubst (wireSimPairs sim) (stdWireAtom 0 n' w) = wireSimFormula (sim w) := by
  have hfind_map : ∀ {α : Type} (l : List α) (key : α → ℕ) (val : α → Formula) (a : α),
      a ∈ l → (∀ x ∈ l, key x = key a → x = a) →
      (l.map fun x => (key x, val x)).find? (fun kv => kv.1 == key a) = some (key a, val a) := by
    intro α l key val a
    induction l with
    | nil => intro h; cases h
    | cons x xs ih =>
      intro hm hinj
      simp only [List.map_cons, List.find?_cons]
      by_cases hkx : (key x == key a) = true
      · rw [hinj x List.mem_cons_self (beq_iff_eq.1 hkx)]; simp
      · simp only [hkx]
        rcases List.mem_cons.1 hm with rfl | hm'
        · simp at hkx
        · exact ih hm' fun y hy => hinj y (List.mem_cons_of_mem _ hy)
  cases w with
  | input i =>
    have hf := hfind_map (List.finRange n') Fin.val
      (fun j => wireSimFormula (sim (.input j))) i (List.mem_finRange i)
      (fun x _ h => Fin.ext h)
    rw [stdWireAtom_input, zero_add]
    have hfind : (wireSimPairs sim).find? (fun kv => kv.1 == i.val) =
        some (i.val, wireSimFormula (sim (.input i))) := by
      dsimp only [wireSimPairs]; rw [List.find?_append, hf]; rfl
    exact listSubst_of_find?_eq_some hfind
  | gate k =>
    have hnone : ((List.finRange n').map fun i : Fin n' =>
        (i.val, wireSimFormula (sim (.input i)))).find?
          (fun kv => kv.1 == n' + k.val) = none := by
      rw [List.find?_eq_none]
      rintro _ hmem
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hmem
      have : i.val ≠ n' + k.val := by omega
      simp [this]
    have hf := hfind_map (List.finRange g') (fun j : Fin g' => n' + j.val)
      (fun j => wireSimFormula (sim (.gate j))) k (List.mem_finRange k)
      (fun x _ h => Fin.ext (by omega))
    rw [stdWireAtom_gate, zero_add]
    have hfind : (wireSimPairs sim).find? (fun kv => kv.1 == n' + k.val) =
        some (n' + k.val, wireSimFormula (sim (.gate k))) := by
      dsimp only [wireSimPairs]; rw [List.find?_append, hnone, Option.none_or, hf]
    exact listSubst_of_find?_eq_some hfind

/-- Encoded bit length of `wireSimPairs sim` is at most quadratic in `n' + g' + n + g`. -/
theorem length_wireSimPairs_le {n' g' n g : ℕ} (sim : Wire n' g' → WireSim n g) :
    (encList (encPair encNat encFormula) (wireSimPairs sim)).length ≤
      40 * (n' + g' + 1) * (n + g + n' + g' + 20) := by
  have hwf (s : WireSim n g) : (encFormula (wireSimFormula s)).length ≤ 2 * (n + g) + 30 := by
    have hbot : (encFormula .falsum).length ≤ 10 := by decide
    have hop3 : (frame (encFormTok (.inr 3))).length ≤ 10 := by decide
    rcases s with (_ | _) | ⟨_ | _, w⟩
    · exact hbot.trans (by omega)
    · simp only [wireSimFormula, encFormula_imp, List.length_append]; omega
    · have hw : stdWireAtom 0 n w ≤ n + g := by
        have := (mem_Ico.1 (stdWireAtom_mem_Ico 0 n w)).2; omega
      have h1 := (length_encNat_mono hw).trans (length_encNat_le_self (n + g))
      have h2 := length_encFormula_atom_le (stdWireAtom 0 n w)
      simp only [wireSimFormula]; omega
    · have hw : stdWireAtom 0 n w ≤ n + g := by
        have := (mem_Ico.1 (stdWireAtom_mem_Ico 0 n w)).2; omega
      have h1 := (length_encNat_mono hw).trans (length_encNat_le_self (n + g))
      have h2 := length_encFormula_atom_le (stdWireAtom 0 n w)
      simp only [wireSimFormula, encFormula_imp, List.length_append]; omega
  have hlist : ∀ l : List (ℕ × Formula),
      (∀ kv ∈ l, kv.1 ≤ n' + g' ∧ (encFormula kv.2).length ≤ 2 * (n + g) + 30) →
      (encList (encPair encNat encFormula) l).length ≤
        l.length * (12 * (n + g + n' + g') + 140) := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons kv rest ih =>
      intro hl
      obtain ⟨hk1, hk2⟩ := hl kv List.mem_cons_self
      have hkn := (length_encNat_mono hk1).trans (length_encNat_le_self (n' + g'))
      have ihr := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
      simp only [encList_cons, List.length_append, length_frame, length_encPair, List.length_cons]
      nlinarith
  have hle := hlist (wireSimPairs sim) fun kv hkv => by
    simp only [wireSimPairs, List.mem_append, List.mem_map] at hkv
    rcases hkv with ⟨i, -, rfl⟩ | ⟨k, -, rfl⟩
    · exact ⟨by omega, hwf _⟩
    · exact ⟨by omega, hwf _⟩
  have hlen : (wireSimPairs sim).length = n' + g' := by simp [wireSimPairs]
  rw [hlen] at hle
  nlinarith

/-- Uniform bounded Frege proofs for all valid `1`-variable gate-equation templates. -/
private theorem exists_uniform_oneVarGate_proof :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (op : Boolean.Op) (eOut e0 e1 : OneVarSim),
      oneVarGateTemplate op eOut e0 e1 ∈ TAUT →
      ∀ (sub : ℕ → Formula) {K : ℕ}, (∀ v, (encFormula (sub v)).length ≤ K) →
        BoundedFrege ((oneVarGateTemplate op eOut e0 e1).subst sub) C (C * (K + 1)) := by
  classical
  let Idx := Boolean.Op × OneVarSim × OneVarSim × OneVarSim
  let cost (x : Idx) : ℕ :=
    if h : oneVarGateTemplate x.1 x.2.1 x.2.2.1 x.2.2.2 ∈ TAUT then
      let L₀ := Classical.choose (frege_complete h)
      L₀.length + L₀.foldr (fun θ acc => max (encFormula θ).length acc) 0 + 1
    else 1
  let C := (univ : Finset Idx).sup cost + 1
  refine ⟨C, by omega, fun op eOut e0 e1 ht sub K hK => ?_⟩
  let x : Idx := (op, eOut, e0, e1)
  have hx : cost x ≤ C := (le_sup (mem_univ x)).trans (Nat.le_succ _)
  simp only [cost, x, ht, dite_true] at hx
  have hspec := Classical.choose_spec (frege_complete ht)
  exact (BoundedFrege.of_schema hspec.1 hspec.2 sub hK).mono
    (by omega) (Nat.mul_le_mul_right _ (by omega))

/-- Uniform bounded Frege proofs for all valid `1`-variable output-mismatch implications. -/
private theorem exists_uniform_outSim_proof :
    ∃ C : ℕ, 40 ≤ C ∧ ∀ {n' n m : ℕ} (c' : Circuit signature n' m) (c : Circuit signature n m)
      (sim : Wire n' c'.size → WireSim n c.size) (b a : BitString m),
      IsOutputSim c' c sim b a →
      ∀ j : Fin m, BoundedFrege
        (.imp ((litNe (stdWireAtom 0 n' (c'.outputs j)) (b j)).subst
            (listSubst (wireSimPairs sim)))
          (litNe (stdWireAtom 0 n (c.outputs j)) (a j)))
        C (C * (n + c.size + 20)) := by
  let s1 : Formula := .imp (.or (.imp (.imp .falsum .falsum) .falsum) (.and .falsum .falsum))
    (.atom 0)
  let s2 : Formula := .imp (.and (.or .falsum .falsum) (.imp .falsum .falsum)) (.atom 0)
  let s3 : Formula := .imp (.or (.imp (.imp (.atom 0) .falsum) .falsum) (.and .falsum .falsum))
    (.and (.or (.atom 0) .falsum) (.imp .falsum .falsum))
  let s4 : Formula := .imp (.and (.or (.imp (.atom 0) .falsum) .falsum) (.imp .falsum .falsum))
    (.or (.imp (.atom 0) .falsum) (.and .falsum .falsum))
  obtain ⟨L1, hL1, hm1⟩ := frege_complete (show s1 ∈ TAUT from fun _ => by simp [s1])
  obtain ⟨L2, hL2, hm2⟩ := frege_complete (show s2 ∈ TAUT from fun _ => by simp [s2])
  obtain ⟨L3, hL3, hm3⟩ := frege_complete (show s3 ∈ TAUT from fun σ => by
    simp only [s3, Proposition.eval_imp_bool, Proposition.eval_or_bool, Proposition.eval_and_bool,
      Proposition.eval_atom_bool, Proposition.eval_falsum_bool]; cases σ 0 <;> rfl)
  obtain ⟨L4, hL4, hm4⟩ := frege_complete (show s4 ∈ TAUT from fun σ => by
    simp only [s4, Proposition.eval_imp_bool, Proposition.eval_or_bool, Proposition.eval_and_bool,
      Proposition.eval_atom_bool, Proposition.eval_falsum_bool]; cases σ 0 <;> rfl)
  let mxL (L : List Formula) := L.foldr (fun θ acc => max (encFormula θ).length acc) 0
  let D0 := L1.length + L2.length + L3.length + L4.length +
    mxL L1 + mxL L2 + mxL L3 + mxL L4 + 60
  refine ⟨D0 * 60, by dsimp only [D0]; omega, fun {n' n m} c' c sim b a hout j => ?_⟩
  rw [subst_litNe, listSubst_wireSimPairs]
  set v := stdWireAtom 0 n (c.outputs j)
  have hv_le : (encFormula (.atom v)).length ≤ 2 * (n + c.size) + 4 := by
    have hw : v ≤ n + c.size := by
      have h0 := (mem_Ico.1 (stdWireAtom_mem_Ico 0 n (c.outputs j))).2
      rw [Nat.zero_add] at h0; omega
    have h1 := (length_encNat_mono hw).trans (length_encNat_le_self (n + c.size))
    have h2 := length_encFormula_atom_le v; omega
  have hlit_le (bv : Bool) : (encFormula (litNe v bv)).length ≤ 2 * (n + c.size) + 40 := by
    rw [encFormula_litNe, List.length_append, length_litNeSuffix]; omega
  have hlen_bd {l0 : ℕ} (hl0 : l0 ≤ D0) : l0 ≤ D0 * 60 := hl0.trans (by omega)
  have hsc_bd {m0 : ℕ} (hm0 : m0 ≤ D0) {K : ℕ} (hK : K + 1 ≤ 60 * (n + c.size + 20)) :
      m0 * (K + 1) ≤ D0 * 60 * (n + c.size + 20) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul hm0 hK
  have hK1 : 2 * (n + c.size) + 40 + 1 ≤ 60 * (n + c.size + 20) := by omega
  have hK2 : 2 * (n + c.size) + 4 + 1 ≤ 60 * (n + c.size + 20) := by omega
  rcases hout j with hconst | ⟨hpos, hba⟩ | ⟨hneg, hba⟩
  · rw [hconst]
    cases b j
    · exact (BoundedFrege.of_schema hL2 hm2 (fun _ => litNe v (a j))
        (fun _ => hlit_le (a j))).mono (hlen_bd (by dsimp only [D0]; omega))
        (hsc_bd (by dsimp only [D0, mxL]; omega) hK1)
    · exact (BoundedFrege.of_schema hL1 hm1 (fun _ => litNe v (a j))
        (fun _ => hlit_le (a j))).mono (hlen_bd (by dsimp only [D0]; omega))
        (hsc_bd (by dsimp only [D0, mxL]; omega) hK1)
  · rw [hpos, hba]
    have hl := hlit_le (a j)
    have hid (bv : Bool) (h : (encFormula (litNe v bv)).length ≤ 2 * (n + c.size) + 40) :
        9 * (encFormula (litNe v bv)).length + 100 ≤ D0 * 60 * (n + c.size + 20) := by
      have hD1 : 1 ≤ D0 := by dsimp only [D0]; omega
      calc 9 * (encFormula (litNe v bv)).length + 100
          ≤ 1 * (60 * (n + c.size + 20)) := by omega
        _ ≤ D0 * (60 * (n + c.size + 20)) := Nat.mul_le_mul_right _ hD1
        _ = D0 * 60 * (n + c.size + 20) := by ring
    cases ha : a j
    · exact (BoundedFrege.id (litNe v false)).mono (hlen_bd (by dsimp only [D0]; omega))
        (hid false (ha ▸ hl))
    · exact (BoundedFrege.id (litNe v true)).mono (hlen_bd (by dsimp only [D0]; omega))
        (hid true (ha ▸ hl))
  · rw [hneg, hba]
    cases a j
    · exact (BoundedFrege.of_schema hL3 hm3 (fun _ => .atom v) (fun _ => hv_le)).mono
        (hlen_bd (by dsimp only [D0]; omega)) (hsc_bd (by dsimp only [D0, mxL]; omega) hK2)
    · exact (BoundedFrege.of_schema hL4 hm4 (fun _ => .atom v) (fun _ => hv_le)).mono
        (hlen_bd (by dsimp only [D0]; omega)) (hsc_bd (by dsimp only [D0, mxL]; omega) hK2)

/-- Syntactic identity connecting a specialized gate equation of `c'` either to a copied gate
equation of `c` or to a `1`-variable substitution instance of `oneVarGateTemplate`. -/
private theorem gateSim_subst_eq {n' n m : ℕ} (c' : Circuit signature n' m)
    (c : Circuit signature n m) (sim : Wire n' c'.size → WireSim n c.size) (k' : Fin c'.size)
    (hgate : IsGateSim c' c sim k') :
    let N := n' + c'.size + n + c.size + m + 2
    (∃ k : Fin c.size,
      (gateEqFormula (stdWireAtom 0 n') k' (c'.program.lines k')).subst
        (listSubst (wireSimPairs sim)) =
      gateEqFormula (stdWireAtom 0 n) k (c.program.lines k)) ∨
    ∃ (eOut e0 e1 : OneVarSim) (sub : ℕ → Formula),
      oneVarGateTemplate (c'.program.lines k').op eOut e0 e1 ∈ TAUT ∧
      (∀ v, (encFormula (sub v)).length ≤ 4 * N) ∧
      (gateEqFormula (stdWireAtom 0 n') k' (c'.program.lines k')).subst
        (listSubst (wireSimPairs sim)) =
        (oneVarGateTemplate (c'.program.lines k').op eOut e0 e1).subst sub := by
  intro N
  have hN2 : 2 ≤ N := by dsimp only [N]; omega
  rcases hgate with ⟨k, hop, hout, hargs⟩ | ⟨eOut, e0, e1, htaut, hkind⟩
  · refine Or.inl ⟨k, ?_⟩
    have hspec_gen : ∀ (l' : Line signature n' c'.size) (l : Line signature n c.size)
        (ho : l'.op = l.op),
        (∀ i : Fin (signature.Arity l'.op),
          sim (l'.wires i) = .inr (false, l.wires (i.cast (by rw [ho])))) →
        (lineSpecFormula (stdWireAtom 0 n') l').subst (listSubst (wireSimPairs sim)) =
          lineSpecFormula (stdWireAtom 0 n) l := by
      rintro ⟨op', ws'⟩ ⟨op, ws⟩ ho ha; dsimp only at ho ha; subst ho
      cases op' with
      | const bv => cases bv <;> rfl
      | not =>
        change Proposition.imp (listSubst (wireSimPairs sim) _) .falsum = _
        rw [listSubst_wireSimPairs, ha 0]; rfl
      | and =>
        change Proposition.and (listSubst (wireSimPairs sim) _)
          (listSubst (wireSimPairs sim) _) = _
        rw [listSubst_wireSimPairs, ha 0, listSubst_wireSimPairs, ha 1]; rfl
      | or =>
        change Proposition.or (listSubst (wireSimPairs sim) _)
          (listSubst (wireSimPairs sim) _) = _
        rw [listSubst_wireSimPairs, ha 0, listSubst_wireSimPairs, ha 1]; rfl
    have hspec := hspec_gen _ _ hop hargs
    have hk : listSubst (wireSimPairs sim) (stdWireAtom 0 n' (.gate k')) =
        .atom (stdWireAtom 0 n (.gate k)) := by
      rw [listSubst_wireSimPairs, hout]; rfl
    change formulaIff (listSubst (wireSimPairs sim) (stdWireAtom 0 n' (.gate k')))
      ((lineSpecFormula (stdWireAtom 0 n') (c'.program.lines k')).subst
        (listSubst (wireSimPairs sim))) = _
    rw [hk, hspec]; rfl
  · refine Or.inr ⟨eOut, e0, e1, ?_⟩
    rcases hkind with ⟨_, bOut, b0, b1, rfl, rfl, rfl, hout, hargs⟩ | ⟨w, hout, hargs⟩
    · refine ⟨fun _ => .falsum, htaut, fun _ => by
        have hb : (encFormula .falsum).length = 3 := by decide
        rw [hb]; omega, ?_⟩
      have hof (b : Bool) : (oneVarFormula (.inl b)).subst (fun _ => .falsum) =
          wireSimFormula (n := n) (g := c.size) (.inl b) := by cases b <;> rfl
      rcases hl' : c'.program.lines k' with ⟨op', ws'⟩
      have hargs' := hl' ▸ hargs
      have hsp : (lineSpecFormula (stdWireAtom 0 n') ⟨op', ws'⟩).subst
          (listSubst (wireSimPairs sim)) =
          (match op' with
           | .const false => (Proposition.falsum : Formula)
           | .const true => .imp .falsum .falsum
           | .not => .imp (oneVarFormula (.inl b0)) .falsum
           | .and => .and (oneVarFormula (.inl b0)) (oneVarFormula (.inl b1))
           | .or => .or (oneVarFormula (.inl b0)) (oneVarFormula (.inl b1))).subst
            (fun _ => .falsum) := by
        cases op' with
        | const bv => cases bv <;> rfl
        | not =>
          change Proposition.imp (listSubst (wireSimPairs sim) _) .falsum =
            Proposition.imp ((oneVarFormula (.inl b0)).subst _) .falsum
          rw [listSubst_wireSimPairs, hargs' 0, hof]; rfl
        | and =>
          change Proposition.and (listSubst (wireSimPairs sim) _)
            (listSubst (wireSimPairs sim) _) =
            Proposition.and ((oneVarFormula (.inl b0)).subst _)
              ((oneVarFormula (.inl b1)).subst _)
          rw [listSubst_wireSimPairs, hargs' 0, listSubst_wireSimPairs, hargs' 1, hof, hof]; rfl
        | or =>
          change Proposition.or (listSubst (wireSimPairs sim) _)
            (listSubst (wireSimPairs sim) _) =
            Proposition.or ((oneVarFormula (.inl b0)).subst _)
              ((oneVarFormula (.inl b1)).subst _)
          rw [listSubst_wireSimPairs, hargs' 0, listSubst_wireSimPairs, hargs' 1, hof, hof]; rfl
      change formulaIff (listSubst (wireSimPairs sim) (stdWireAtom 0 n' (.gate k'))) _ =
        formulaIff ((oneVarFormula (.inl bOut)).subst (fun _ => .falsum)) _
      rw [listSubst_wireSimPairs, hout, hof, hsp]; rfl
    · refine ⟨fun _ => .atom (stdWireAtom 0 n w), htaut, fun _ => ?_, ?_⟩
      · have hw : stdWireAtom 0 n w ≤ N := by
          have h0 := (mem_Ico.1 (stdWireAtom_mem_Ico 0 n w)).2
          rw [Nat.zero_add] at h0; dsimp only [N]; omega
        have h1 : (encNat (stdWireAtom 0 n w)).length ≤ N :=
          (length_encNat_mono hw).trans (length_encNat_le_self N)
        exact (length_encFormula_atom_le (stdWireAtom 0 n w)).trans (by omega)
      · generalize hlk : c'.program.lines k' = lk at hargs ⊢
        rcases lk with ⟨op', ws'⟩
        have hsp : (lineSpecFormula (stdWireAtom 0 n') ⟨op', ws'⟩).subst
            (listSubst (wireSimPairs sim)) =
            (match op' with
             | .const false => (Proposition.falsum : Formula)
             | .const true => .imp .falsum .falsum
             | .not => .imp (oneVarFormula e0) .falsum
             | .and => .and (oneVarFormula e0) (oneVarFormula e1)
             | .or => .or (oneVarFormula e0) (oneVarFormula e1)).subst
              (fun _ => .atom (stdWireAtom 0 n w)) := by
          cases op' with
          | const bv => cases bv <;> rfl
          | not =>
            have h0 : sim (ws' 0) = liftOneVar w e0 := hargs ⟨0, Nat.zero_lt_one⟩
            change Proposition.imp (listSubst (wireSimPairs sim) _) .falsum =
              Proposition.imp ((oneVarFormula e0).subst _) .falsum
            rw [listSubst_wireSimPairs, h0, subst_oneVarFormula]
          | and =>
            have h0 : sim (ws' 0) = liftOneVar w e0 := hargs ⟨0, Nat.zero_lt_succ 1⟩
            have h1 : sim (ws' 1) = liftOneVar w e1 := hargs ⟨1, Nat.one_lt_succ_succ 0⟩
            change Proposition.and (listSubst (wireSimPairs sim) _)
              (listSubst (wireSimPairs sim) _) =
              Proposition.and ((oneVarFormula e0).subst _) ((oneVarFormula e1).subst _)
            rw [listSubst_wireSimPairs, h0, listSubst_wireSimPairs, h1,
              subst_oneVarFormula, subst_oneVarFormula]
          | or =>
            have h0 : sim (ws' 0) = liftOneVar w e0 := hargs ⟨0, Nat.zero_lt_succ 1⟩
            have h1 : sim (ws' 1) = liftOneVar w e1 := hargs ⟨1, Nat.one_lt_succ_succ 0⟩
            change Proposition.or (listSubst (wireSimPairs sim) _)
              (listSubst (wireSimPairs sim) _) =
              Proposition.or ((oneVarFormula e0).subst _) ((oneVarFormula e1).subst _)
            rw [listSubst_wireSimPairs, h0, listSubst_wireSimPairs, h1,
              subst_oneVarFormula, subst_oneVarFormula]
        change formulaIff (listSubst (wireSimPairs sim) (stdWireAtom 0 n' (.gate k'))) _ =
          formulaIff ((oneVarFormula eOut).subst (fun _ => .atom (stdWireAtom 0 n w))) _
        rw [listSubst_wireSimPairs, hout, subst_oneVarFormula, hsp]; rfl

/-- Encoded-length bounds for all formulas occurring in a circuit-specialization Frege proof. -/
private theorem frege_reduce_length_bounds {n' n m : ℕ} (c' : Circuit signature n' m)
    (c : Circuit signature n m) (sim : Wire n' c'.size → WireSim n c.size) (b a : BitString m) :
    let σ := listSubst (wireSimPairs sim)
    let N := n' + c'.size + n + c.size + m + 2
    (∀ k' : Fin c'.size,
      (encFormula ((gateEqFormula (stdWireAtom 0 n') k' (c'.program.lines k')).subst σ)).length ≤
        130 * N) ∧
    (∀ j : Fin m,
      (encFormula ((litNe (stdWireAtom 0 n' (c'.outputs j)) (b j)).subst σ)).length ≤ 50 * N) ∧
    (∀ j : Fin m,
      (encFormula (litNe (stdWireAtom 0 n (c.outputs j)) (a j))).length ≤ 50 * N) ∧
    (encFormula ((outMismatchWith c' (stdWireAtom 0 n') b).subst σ)).length ≤ 60 * N ^ 2 ∧
    (encFormula (outMismatchWith c (stdWireAtom 0 n) a)).length ≤ 60 * N ^ 2 ∧
    (∀ γ ∈ (tauFormula 0 c' b).subst σ :: gateDefsWith c (stdWireAtom 0 n),
      (encFormula γ).length ≤ 200 * N ^ 2) := by
  intro σ N
  have hN2 : 2 ≤ N := by dsimp only [N]; omega
  have hop (i : Fin 4) : (frame (encFormTok (.inr i))).length ≤ 10 := by fin_cases i <;> decide
  have hbot : (encFormula .falsum).length ≤ 10 := by decide
  have hwaN (w : Wire n c.size) : stdWireAtom 0 n w ≤ N := by
    have h0 := (mem_Ico.1 (stdWireAtom_mem_Ico 0 n w)).2
    rw [Nat.zero_add] at h0; dsimp only [N]; omega
  have hwf_le (s : WireSim n c.size) : (encFormula (wireSimFormula s)).length ≤ 2 * N + 30 := by
    have h3 := hop 3
    rcases s with (_ | _) | ⟨_ | _, w⟩
    · exact hbot.trans (by omega)
    · simp only [wireSimFormula, encFormula_imp, List.length_append]; omega
    · have h1 : (encNat (stdWireAtom 0 n w)).length ≤ N :=
        (length_encNat_mono (hwaN w)).trans (length_encNat_le_self N)
      exact (length_encFormula_atom_le (stdWireAtom 0 n w)).trans (by omega)
    · have h1 : (encNat (stdWireAtom 0 n w)).length ≤ N :=
        (length_encNat_mono (hwaN w)).trans (length_encNat_le_self N)
      have h2 := length_encFormula_atom_le (stdWireAtom 0 n w)
      simp only [wireSimFormula, encFormula_imp, List.length_append]; omega
  have hgate (k' : Fin c'.size) :
      (encFormula ((gateEqFormula (stdWireAtom 0 n') k' (c'.program.lines k')).subst σ)).length ≤
        130 * N := by
    have hspec : (encFormula ((lineSpecFormula (stdWireAtom 0 n') (c'.program.lines k')).subst
        σ)).length ≤ 5 * N + 70 := by
      rcases c'.program.lines k' with ⟨op, ws⟩
      cases op with
      | const bv =>
        cases bv
        · exact hbot.trans (by omega)
        · have := hop 3
          change (encFormula (Proposition.imp .falsum .falsum)).length ≤ _
          simp only [encFormula_imp, List.length_append]; omega
      | not =>
        have := hwf_le (sim (ws 0)); have := hop 3
        change (encFormula (Proposition.imp (listSubst (wireSimPairs sim) _) .falsum)).length ≤ _
        rw [listSubst_wireSimPairs]; simp only [encFormula_imp, List.length_append]; omega
      | and =>
        have := hwf_le (sim (ws 0)); have := hwf_le (sim (ws 1)); have := hop 1
        change (encFormula (Proposition.and (listSubst (wireSimPairs sim) _)
          (listSubst (wireSimPairs sim) _))).length ≤ _
        rw [listSubst_wireSimPairs, listSubst_wireSimPairs]
        simp only [encFormula_and, List.length_append]; omega
      | or =>
        have := hwf_le (sim (ws 0)); have := hwf_le (sim (ws 1)); have := hop 2
        change (encFormula (Proposition.or (listSubst (wireSimPairs sim) _)
          (listSubst (wireSimPairs sim) _))).length ≤ _
        rw [listSubst_wireSimPairs, listSubst_wireSimPairs]
        simp only [encFormula_or, List.length_append]; omega
    have hk := hwf_le (sim (.gate k')); have h1 := hop 1; have h3 := hop 3
    change (encFormula (formulaIff (listSubst (wireSimPairs sim) (stdWireAtom 0 n' (.gate k')))
      ((lineSpecFormula (stdWireAtom 0 n') (c'.program.lines k')).subst σ))).length ≤ _
    rw [listSubst_wireSimPairs, length_encFormula_formulaIff]; omega
  have hlit' (j : Fin m) :
      (encFormula ((litNe (stdWireAtom 0 n' (c'.outputs j)) (b j)).subst σ)).length ≤ 50 * N := by
    have := hwf_le (sim (c'.outputs j))
    have h1 := hop 1; have h2 := hop 2; have h3 := hop 3
    have heq (ψ : Formula) (bv : Bool) :
        (encFormula (if bv then Proposition.or (.imp ψ .falsum) (.and .falsum .falsum)
          else .and (.or ψ .falsum) (.imp .falsum .falsum))).length ≤
          (encFormula ψ).length + 60 := by
      cases bv <;> (simp only [↓reduceIte, Bool.false_eq_true, encFormula_or,
        encFormula_and, encFormula_imp, List.length_append]; omega)
    dsimp only [σ]; rw [subst_litNe, listSubst_wireSimPairs]
    exact (heq _ _).trans (by omega)
  have hlit_a (j : Fin m) :
      (encFormula (litNe (stdWireAtom 0 n (c.outputs j)) (a j))).length ≤ 50 * N := by
    have h1 : (encNat (stdWireAtom 0 n (c.outputs j))).length ≤ N :=
      (length_encNat_mono (hwaN (c.outputs j))).trans (length_encNat_le_self N)
    have h2 := length_encFormula_atom_le (stdWireAtom 0 n (c.outputs j))
    rw [encFormula_litNe, List.length_append, length_litNeSuffix]; omega
  have hmN : m + 1 ≤ N := by dsimp only [N]; omega
  have h55 : (m + 1) * (50 * N + 10) ≤ 60 * N ^ 2 :=
    calc (m + 1) * (50 * N + 10) ≤ N * (60 * N) := Nat.mul_le_mul hmN (by omega)
      _ = 60 * N ^ 2 := by rw [Nat.mul_left_comm, sq]
  have hB' : (encFormula ((outMismatchWith c' (stdWireAtom 0 n') b).subst σ)).length ≤
      60 * N ^ 2 := by
    have hb := length_encFormula_bigOr_le (B := 50 * N)
      (αs := List.ofFn fun j : Fin m => (litNe (stdWireAtom 0 n' (c'.outputs j)) (b j)).subst σ)
      fun α hα => by simp only [List.mem_ofFn] at hα; obtain ⟨j, rfl⟩ := hα; exact hlit' j
    rw [subst_outMismatchWith]
    rw [List.length_ofFn] at hb; exact hb.trans h55
  have hB : (encFormula (outMismatchWith c (stdWireAtom 0 n) a)).length ≤ 60 * N ^ 2 := by
    have hb := length_encFormula_bigOr_le (B := 50 * N)
      (αs := List.ofFn fun j : Fin m => litNe (stdWireAtom 0 n (c.outputs j)) (a j))
      fun α hα => by simp only [List.mem_ofFn] at hα; obtain ⟨j, rfl⟩ := hα; exact hlit_a j
    rw [List.length_ofFn] at hb; exact hb.trans h55
  refine ⟨hgate, hlit', hlit_a, hB', hB, fun γ hγ => ?_⟩
  rcases List.mem_cons.1 hγ with rfl | hγ
  · change (encFormula ((Frege.Formula.imps _ _).subst σ)).length ≤ _
    rw [subst_imps]
    have hi := length_encFormula_imps_le (B := 130 * N)
      ((outMismatchWith c' (stdWireAtom 0 n') b).subst σ) fun δ hδ => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hδ
        obtain ⟨k', rfl⟩ := List.mem_ofFn.1 hd; exact hgate k'
    have hml : ((gateDefsWith c' (stdWireAtom 0 n')).map (Proposition.subst σ)).length ≤ N := by
      rw [List.length_map, length_gateDefsWith]; dsimp only [N]; omega
    calc _ ≤ N * (140 * N) + 60 * N ^ 2 :=
          hi.trans (Nat.add_le_add (Nat.mul_le_mul hml (by omega)) hB')
      _ = 200 * N ^ 2 := by rw [Nat.mul_left_comm, ← sq]; omega
  · obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hγ
    have h1 := length_encFormula_gateEqFormula_le (V := N) hwaN k (c.program.lines k)
    have h2 : (encNat N).length ≤ N := length_encNat_le_self N
    calc (encFormula (gateEqFormula (stdWireAtom 0 n) k (c.program.lines k))).length
        ≤ 16 * (6 * N) := h1.trans (Nat.mul_le_mul_left 16 (by omega))
      _ ≤ 200 * (N * N) := by have := Nat.mul_le_mul_left N hN2; omega
      _ = 200 * N ^ 2 := by rw [sq]

/-- **General polynomial-size Frege circuit-specialization theorem.** There exists an absolute
constant `C ≥ 1` such that for any Boolean circuits `c' : Circuit signature n' m` and
`c : Circuit signature n m`, any target strings `b, a : BitString m`, and any wire specialization
`sim : Wire n' c'.size → WireSim n c.size` satisfying `IsGateSim c' c sim k'` for all `k'` and
`IsOutputSim c' c sim b a`, there is a verified Extended Frege proof `steps : List EFStep` (using
pure Frege rules with zero extension or extra axioms) of
`((tauFormula 0 c' b).subst (listSubst (wireSimPairs sim))) → tauFormula 0 c a`
whose encoded bit length is at most `C * (n' + c'.size + n + c.size + m + 2) ^ 6`. -/
theorem exists_frege_reduce_tauFormula :
    ∃ C : ℕ, 1 ≤ C ∧
      ∀ {n' n m : ℕ} (c' : Circuit signature n' m) (c : Circuit signature n m)
        (sim : Wire n' c'.size → WireSim n c.size) (b a : BitString m),
        (∀ k' : Fin c'.size, IsGateSim c' c sim k') →
        IsOutputSim c' c sim b a →
        ∃ steps : List EFStep,
          runEFProof (fun _ => false) steps =
            .imp ((tauFormula 0 c' b).subst (listSubst (wireSimPairs sim))) (tauFormula 0 c a) ∧
          (encList encEFStep steps).length ≤
            C * (n' + c'.size + n + c.size + m + 2) ^ 6 := by
  obtain ⟨Cg, hCg1, hCg⟩ := exists_uniform_oneVarGate_proof
  obtain ⟨Co, hCo40, hCo⟩ := exists_uniform_outSim_proof
  obtain ⟨Cb, hCb1, hCb⟩ := BoundedFrege.bigOr_imp_bigOr
  generalize hD_def : Cg + Co + Cb + 4000 = D
  have hD0 : 4000 ≤ D := by omega
  refine ⟨80000 * D ^ 3, Nat.succ_le_of_lt (by positivity),
    fun {n' n m} c' c sim b a hgates houts => ?_⟩
  obtain ⟨hgate_le, hlit'_le, hlit_a_le, hB'_le, hB_le, hG⟩ :=
    frege_reduce_length_bounds c' c sim b a
  have hgs_eq := fun k' => gateSim_subst_eq c' c sim k' (hgates k')
  generalize hN_def : n' + c'.size + n + c.size + m + 2 = N at *
  set σ := listSubst (wireSimPairs sim)
  set H := (tauFormula 0 c' b).subst σ
  set Γ := H :: gateDefsWith c (stdWireAtom 0 n)
  set B' := (outMismatchWith c' (stdWireAtom 0 n') b).subst σ
  set B := outMismatchWith c (stdWireAtom 0 n) a
  have hN2 : 2 ≤ N := by omega
  have hN2_ge : 4 ≤ N ^ 2 := by nlinarith only [hN2]
  have hN_cu : N ≤ N ^ 3 := by calc N = N * 1 := (Nat.mul_one N).symm
    _ ≤ N * N ^ 2 := Nat.mul_le_mul_left N (by omega)
    _ = N ^ 3 := by ring
  have hN2_cu : N ^ 2 ≤ N ^ 3 := by calc N ^ 2 = 1 * N ^ 2 := (Nat.one_mul _).symm
    _ ≤ N * N ^ 2 := Nat.mul_le_mul_right _ (by omega)
    _ = N ^ 3 := by ring
  have hDD : D ≤ D ^ 2 := by nlinarith only [hD0]
  have hΓN : Γ.length + 1 ≤ N := by
    have : Γ.length = c.size + 1 := congrArg Nat.succ List.length_ofFn; omega
  have hcN : c'.size + 1 ≤ N := by omega
  have hmN : m + 1 ≤ N := by omega
  have hcsN : n + c.size + 20 ≤ 11 * N := by omega
  have hΓG : (Γ.length + 1) * (200 * N ^ 2 + 20) ≤ 205 * N ^ 3 :=
    calc (Γ.length + 1) * (200 * N ^ 2 + 20) ≤ N * (205 * N ^ 2) :=
          Nat.mul_le_mul hΓN (by omega)
      _ = 205 * N ^ 3 := by ring
  have hΓG10 : (Γ.length + 1) * (200 * N ^ 2 + 10) ≤ 205 * N ^ 3 :=
    (Nat.mul_le_mul_left _ (by omega)).trans hΓG
  have h4kN3 : 4000 * N ^ 3 ≤ D * N ^ 3 := Nat.mul_le_mul_right _ hD0
  have hδ_prov (k' : Fin c'.size) :
      BoundedFrege (Frege.Formula.imps Γ
          ((gateEqFormula (stdWireAtom 0 n') k' (c'.program.lines k')).subst σ))
        (D * N) (2 * D * N ^ 3) := by
    rcases hgs_eq k' with ⟨k, heq⟩ | ⟨eOut, e0, e1, sub, ht, hK, heq⟩
    · rw [heq]
      have hmem : gateEqFormula (stdWireAtom 0 n) k (c.program.lines k) ∈ Γ :=
        List.mem_cons_of_mem _ (List.mem_ofFn.2 ⟨k, rfl⟩)
      refine (BoundedFrege.imps_mem hmem hG).mono (by nlinarith only [hΓN, hD0]) ?_
      rw [Nat.mul_assoc 16, Nat.mul_assoc 2]; omega
    · have hd0 := hCg (c'.program.lines k').op eOut e0 e1 ht sub hK
      rw [← heq] at hd0
      have hkl := hgate_le k'
      refine (hd0.weaken_imps Γ hG).mono (by nlinarith only [hΓN, hD_def, hN2]) (max_le ?_ ?_)
      · calc Cg * (4 * N + 1) ≤ D * (2 * (4 * N)) := Nat.mul_le_mul (by omega) (by omega)
          _ ≤ D * (2 * (N ^ 2 * N)) :=
            Nat.mul_le_mul_left D (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right N hN2_ge))
          _ = 2 * D * N ^ 3 := by ring
      · rw [Nat.mul_assoc 2]; linarith only [hΓG10, hkl, hN_cu, h4kN3]
  have hpeel : ∀ (ks : List (Fin c'.size)) (S₀ : ℕ), ks.length ≤ N →
      BoundedFrege (Frege.Formula.imps Γ (Frege.Formula.imps
          (ks.map fun k' => (gateEqFormula (stdWireAtom 0 n') k' (c'.program.lines k')).subst σ)
          B')) S₀ (30 * D * N ^ 3) →
      BoundedFrege (Frege.Formula.imps Γ B')
        (S₀ + ks.length * (2 * D * N)) (30 * D * N ^ 3) := by
    intro ks; induction ks with
    | nil => intro S₀ _ h; simpa using h
    | cons k' rest ih =>
      intro S₀ hks h
      have hrl : rest.length ≤ N := by simp only [List.length_cons] at hks; omega
      let gfn := fun r : Fin c'.size =>
        (gateEqFormula (stdWireAtom 0 n') r (c'.program.lines r)).subst σ
      have hrem : (encFormula (Frege.Formula.imps (rest.map gfn) B')).length ≤ 200 * N ^ 2 := by
        have hi := length_encFormula_imps_le (Δ := rest.map gfn) (B := 130 * N) B' fun δ hδ => by
          obtain ⟨r, -, rfl⟩ := List.mem_map.1 hδ; exact hgate_le r
        rw [List.length_map] at hi; nlinarith only [hi, hrl, hB'_le, hN2]
      have hkl : (encFormula (gfn k')).length ≤ 130 * N := hgate_le k'
      have hst : BoundedFrege _ (S₀ + 2 * D * N) (30 * D * N ^ 3) :=
        (BoundedFrege.imps_mp Γ h (hδ_prov k') hG).mono (by nlinarith only [hΓN, hD0])
          (max_le (max_le le_rfl (by rw [Nat.mul_assoc 2, Nat.mul_assoc 30]; omega))
            (by rw [Nat.mul_assoc 30]
                change 20 * (_ + (encFormula (gfn k')).length +
                  (encFormula (Frege.Formula.imps (rest.map gfn) B')).length) ≤ _
                omega))
      refine (ih (S₀ + 2 * D * N) hrl hst).mono ?_ le_rfl
      rw [List.length_cons]; exact le_of_eq (by ring)
  have hinit : BoundedFrege (Frege.Formula.imps Γ H) (2 * D * N) (30 * D * N ^ 3) :=
    (BoundedFrege.imps_mem (Γ := Γ) List.mem_cons_self hG).mono
      (by nlinarith only [hΓN, hD0]) (by rw [Nat.mul_assoc 16, Nat.mul_assoc 30]; omega)
  have hH_map : H = Frege.Formula.imps
      ((List.finRange c'.size).map fun k' =>
        (gateEqFormula (stdWireAtom 0 n') k' (c'.program.lines k')).subst σ) B' := by
    change (Frege.Formula.imps _ _).subst σ = _
    rw [subst_imps, gateDefsWith_eq_map_finRange, List.map_map]; rfl
  rw [hH_map] at hinit
  have hB'_prov : BoundedFrege (Frege.Formula.imps Γ B') (3 * D * N ^ 2) (30 * D * N ^ 3) :=
    (hpeel (List.finRange c'.size) (2 * D * N) (by rw [List.length_finRange]; omega) hinit).mono
      (by rw [List.length_finRange]
          calc 2 * D * N + c'.size * (2 * D * N) = (c'.size + 1) * (2 * D * N) := by ring
            _ ≤ N * (2 * D * N) := Nat.mul_le_mul_right _ hcN
            _ = 2 * (D * N ^ 2) := by ring
            _ ≤ 3 * D * N ^ 2 := by rw [Nat.mul_assoc]; omega) le_rfl
  let αs := List.ofFn fun j : Fin m => (litNe (stdWireAtom 0 n' (c'.outputs j)) (b j)).subst σ
  let βs := List.ofFn fun j : Fin m => litNe (stdWireAtom 0 n (c.outputs j)) (a j)
  have hαlen : αs.length = m := List.length_ofFn
  have hβlen : βs.length = m := List.length_ofFn
  have hBB' : BoundedFrege (.imp B' B) (2 * D * N) (12 * D ^ 2 * N ^ 2) := by
    have h1 : B' = bigOr αs := subst_outMismatchWith σ c' (stdWireAtom 0 n') b
    rw [h1, show B = bigOr βs from rfl]
    let Mlit := Co * (11 * N)
    have hNM : 50 * N ≤ Mlit := by dsimp only [Mlit]; nlinarith only [hCo40]
    have hpt := hCb (αs := αs) (βs := βs) (S := Co) (M := Mlit) (hαlen.trans hβlen.symm)
      (fun i h₁ _ => by
        have him : i < m := hαlen ▸ h₁
        simpa only [αs, βs, List.getElem_ofFn] using
          (hCo c' c sim b a houts ⟨i, him⟩).mono le_rfl (Nat.mul_le_mul_left Co hcsN))
      (fun α hα => by obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hα; exact (hlit'_le j).trans hNM)
      (fun β hβ => by obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hβ; exact (hlit_a_le j).trans hNM)
    rw [hαlen] at hpt
    refine hpt.mono (by nlinarith only [hmN, hD_def]) ?_
    have hM20 : Mlit + 20 ≤ 12 * D * N := by dsimp only [Mlit]; nlinarith only [hD_def, hN2]
    calc Cb * (m + 1) * (Mlit + 20)
        ≤ D * N * (12 * D * N) := Nat.mul_le_mul (Nat.mul_le_mul (by omega) hmN) hM20
      _ = 12 * D ^ 2 * N ^ 2 := by ring
  have hop3 : (frame (encFormTok (.inr 3))).length ≤ 10 := by decide
  have hBB'len : (encFormula (Proposition.imp B' B)).length ≤ 130 * N ^ 2 := by
    rw [encFormula_imp, List.length_append, List.length_append]; omega
  have hgoal := BoundedFrege.imps_mp Γ (hBB'.weaken_imps Γ hG) hB'_prov hG
  have hD2N3 : D * N ^ 3 ≤ D ^ 2 * N ^ 3 := Nat.mul_le_mul_right _ hDD
  have hD2N23 : D ^ 2 * N ^ 2 ≤ D ^ 2 * N ^ 3 := Nat.mul_le_mul_left _ hN2_cu
  have h4kD2N3 : 4000 * N ^ 3 ≤ D ^ 2 * N ^ 3 := h4kN3.trans hD2N3
  have h30_eq : 30 * D ^ 2 * N ^ 3 = 30 * (D ^ 2 * N ^ 3) := Nat.mul_assoc _ _ _
  obtain ⟨L, hL, hmem, hLS, hLM⟩ := hgoal.mono (S' := 5 * D * N ^ 2) (M' := 30 * D ^ 2 * N ^ 3)
    (by have h1 : 2 * D * N + 12 * Γ.length + 7 ≤ 3 * (D * N) := by nlinarith only [hΓN, hD0]
        have h2 : 3 * (D * N) ≤ 2 * (D * N ^ 2) :=
          calc 3 * (D * N) ≤ 4 * (D * N) := by omega
            _ = D * (2 * (2 * N)) := by ring
            _ ≤ D * (2 * (N * N)) :=
              Nat.mul_le_mul_left D (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right N hN2))
            _ = 2 * (D * N ^ 2) := by ring
        rw [Nat.mul_assoc 2 D] at h1 ⊢; rw [Nat.mul_assoc 3, Nat.mul_assoc 5]; omega)
    (max_le (max_le (max_le
      (by rw [Nat.mul_assoc 12, h30_eq]; omega)
      (by rw [h30_eq]; omega))
      (by rw [Nat.mul_assoc 30, h30_eq]; omega))
      (by rw [h30_eq]; omega))
  obtain ⟨steps, hrun, hlen⟩ := exists_runEFProof_of_fregeIsProof hL hmem (fun _ => false) hLM
  refine ⟨steps, hrun, hlen.trans ?_⟩
  have hDN23 : D * N ^ 2 ≤ D * N ^ 3 := Nat.mul_le_mul_left D hN2_cu
  have h1N3 : 1 ≤ N ^ 3 := by omega
  have h1 : L.length + 6 ≤ 6 * (D * N ^ 3) := by
    have : 6 ≤ D * N ^ 3 := by nlinarith only [hD0, h1N3]
    linarith only [hLS, hDN23, this]
  have h2 : 9 * (30 * D ^ 2 * N ^ 3) + L.length + 160 ≤ 300 * (D ^ 2 * N ^ 3) := by
    have : 160 ≤ D ^ 2 * N ^ 3 := by nlinarith only [hD0, hDD, h1N3]
    linarith only [h1, hD2N3, this]
  calc 32 * (L.length + 6) * (9 * (30 * D ^ 2 * N ^ 3) + L.length + 160)
      ≤ 32 * (6 * (D * N ^ 3)) * (300 * (D ^ 2 * N ^ 3)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 32 h1) h2
    _ = 57600 * D ^ 3 * N ^ 6 := by ring
    _ ≤ 80000 * D ^ 3 * N ^ 6 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))

end CslibFrontier.ProofComplexity
