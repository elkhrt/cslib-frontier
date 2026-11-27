/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.RandomizedProtocol
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

import CslibFrontier.Probability.Entropy
import CslibFrontier.Probability.MutualInformation
import CslibFrontier.Probability.Divergence
import Mathlib.Topology.Sion
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Interactive Information Complexity, Braverman's Minimax Theorem, and Majority Boosting

Protocol multiplexing, prior concavity, Braverman's minimax theorem relating worst-case and
max-distributional interactive information complexity, odd-repetition majority-vote boosting,
zero-cost half-error threshold, and binary XOR Fano lower bounds
.

## Main definitions
- `RandomizedProtocol.mux`: convex multiplexing of protocols.
- `RandomizedProtocol.repeatMajority`: odd-repetition majority-vote protocol.
- `bxor`: two-bit Boolean exclusive-or.

## Main results
- `RandomizedProtocol.inputError_mux`, `RandomizedProtocol.internalInfoCost_mux`,
  `infoComplexity_le_div_maxDistInfoComplexity` (Braverman's minimax theorem).
- `RandomizedProtocol.inputError_repeatMajority_le`,
  `RandomizedProtocol.internalInfoCost_repeatMajority_le`,
  `exists_nat_infoComplexity_le_mul_of_lt_half`, `infoComplexity_le_mul_of_lt`.
- `infoComplexity_eq_zero_of_half_le`, `distInfoComplexity_bxor_uniform_ge`.
-/

noncomputable section
open scoped BigOperators ENNReal NNReal
open Set
namespace CslibFrontier.Computability.Communication
universe u v w
private abbrev pmfH {α : Type*} [Fintype α] (p : PMF α) : ℝ :=
  Cslib.Probability.PMF.entropy p * Real.log 2
private lemma pmfHD {α : Type*} [Fintype α] (p : PMF α) :
    pmfH p = ∑ a : α, Real.negMulLog (p a).toReal := by
  rw [pmfH, Cslib.Probability.PMF.entropy_eq_sum, div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne']
private lemma pmfHInj {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) {f : α → β}
    (hf : Function.Injective f) : pmfH (p.map f) = pmfH p := by
  rw [pmfH, pmfH, Cslib.Probability.PMF.entropy_map_of_injective p hf]
private lemma pmfHInjOn {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) {f : α → β}
    (hf : Set.InjOn f p.support) : pmfH (p.map f) = pmfH p := by
  rw [pmfH, pmfH, Cslib.Probability.PMF.entropy_map_of_injOn p hf]
private lemma pmfH_uniform {α : Type*} [Fintype α] [Nonempty α] :
    pmfH (Cslib.Probability.PMF.uniformOfFintype α) = Real.log (Fintype.card α) := by
  rw [pmfH, Cslib.Probability.PMF.entropy_uniform, Real.logb,
    div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne']
private abbrev cEntP {Ω α β : Type*} [Fintype α] [Fintype β]
    (p : PMF Ω) (U : Ω → α) (V : Ω → β) : ℝ :=
  Cslib.Probability.PMF.conditionalEntropy (p.map fun w ↦ (V w, U w)) * Real.log 2
private lemma pmf_cEntP {Ω α β : Type*} [Fintype α] [Fintype β] (p : PMF Ω) (U : Ω → α)
    (V : Ω → β) : pmfH (p.map fun w ↦ (U w, V w)) - pmfH (p.map V) = cEntP p U V := by
  have hsw : Cslib.Probability.PMF.entropy (p.map fun w ↦ (U w, V w)) =
      Cslib.Probability.PMF.entropy (p.map fun w ↦ (V w, U w)) := by
    rw [show (fun w : Ω ↦ (U w, V w)) = Prod.swap ∘ (fun w ↦ (V w, U w)) from rfl, ← PMF.map_comp]
    exact Cslib.Probability.PMF.entropy_map_of_injective _ Prod.swap_injective
  rw [cEntP, Cslib.Probability.PMF.conditionalEntropy, PMF.map_comp]
  change _ = (Cslib.Probability.PMF.entropy (p.map fun w ↦ (V w, U w)) -
    Cslib.Probability.PMF.entropy (p.map V)) * Real.log 2
  rw [← hsw]; dsimp only [pmfH]; ring
local macro "cpd" : term => `(Classical.propDecidable _)
local macro "sglU" : term => `(fun h ↦ (h (Finset.mem_univ _)).elim)
local macro "inj3" : term => `(fun ⟨_,_,_⟩ ⟨_,_,_⟩ h ↦ by cases h; rfl)
local macro "inj4" : term => `(fun ⟨_,_,_,_⟩ ⟨_,_,_,_⟩ h ↦ by cases h; rfl)
local macro "sumC" x:ident "↦" b:term : term => `(Finset.sum_congr rfl fun $x _ ↦ $b)
local macro "prodC" x:ident "↦" b:term : term => `(Finset.prod_congr rfl fun $x _ ↦ $b)
local macro "sum0" x:ident "↦" b:term : term => `(Finset.sum_eq_zero fun $x _ ↦ $b)
local macro "fSP" : term => `(Fintype.sum_prod_type)
local macro "sum1" : term => `(Finset.sum_eq_single)
local macro "nml" : term => `(Real.negMulLog)
local macro "iteL" : term => `(ite_eq_left)
local macro "iteR" : term => `(ite_eq_right)
local macro "diteL" : term => `(dite_eq_left)
local macro "diteR" : term => `(dite_eq_right)
local macro "mulS" : term => `(Finset.mul_sum)
local macro "sumM" : term => `(Finset.sum_mul)
local macro "sumA" : term => `(Finset.sum_add_distrib)
local macro "sumSub" : term => `(Finset.sum_sub_distrib)
local macro "pmfOF" : term => `(PMF.ofFintype_apply)
local macro "memU" : term => `(Finset.mem_univ)
local macro "eTR" : term => `(ENNReal.toReal)
local macro "eOR" : term => `(ENNReal.ofReal)
local macro "eTRM" : term => `(ENNReal.toReal_mul)
local macro "eTRS" : term => `(ENNReal.toReal_sum)
local macro "eTRO" : term => `(ENNReal.toReal_ofReal)
local macro "eTRN" : term => `(ENNReal.toReal_nonneg)
local macro "sumLe" : term => `(Finset.sum_le_sum)
local macro "sumNn" : term => `(Finset.sum_nonneg)
local macro "sumCon" : term => `(Finset.sum_const)
local macro "cardU" : term => `(Finset.card_univ)
local macro "cardF" : term => `(Fintype.card_fin)
local macro "prodS" : term => `(Fintype.prod_sum)
local macro "mLeL" : term => `(mul_le_mul_of_nonneg_left)
local macro "pMapC" : term => `(PMF.map_comp)
local macro "pMapA" : term => `(PMF.map_apply)
local macro "pPureA" : term => `(PMF.pure_apply)
local macro "cArb" : term => `(Classical.arbitrary)
local macro "fC" : term => `(finCongr)
local macro "rL" : term => `(Real.log)
local macro "rL2" : term => `(Real.log 2)
local macro "hL2nn" : term => `(inv_nonneg.2 (Real.log_nonneg (by norm_num)))
local macro "pmi" : term => `(Prod.mk.inj)
local macro "uFilt" f:term : term => `(Finset.univ.filter ($f))
local macro "fCard" : term => `(Fintype.card)
local macro "fInj" : term => `(Function.Injective)
local macro "r0inf" : term => `(ℝ≥0∞)
public section
section PMFHelpers
private def eFin (α : Type*) [Fintype α] [Nonempty α] : α ≃ Fin (fCard α - 1 + 1) :=
  (Fintype.equivFin α).trans (fC (Nat.sub_add_cancel Fintype.card_pos).symm)
private lemma pSum1 {α : Type*} [Fintype α] (p : PMF α) : ∑ a : α, p a = 1 := by
  simpa [tsum_fintype] using p.tsum_coe
private lemma pSum1R {α : Type*} [Fintype α] (p : PMF α) : ∑ a : α, eTR (p a) = 1 := by
  rw [← eTRS fun a _ ↦ p.apply_ne_top a, pSum1, ENNReal.toReal_one]
private lemma pProd1 {n : ℕ} {α : Type*} [Fintype α] (P : Fin n → PMF α) :
    ∑ z : Fin n → α, ∏ i, P i (z i) = 1 := by
  rw [← prodS]; exact Finset.prod_eq_one fun _ _ ↦ pSum1 _
private lemma pMapE {α β : Type*} (p : PMF α) (e : α ≃ β) (b : β) : p.map e b = p (e.symm b) := by
  classical rw [pMapA, tsum_eq_single (e.symm b)]; · simp
  · exact fun a ha ↦ by simp [show b ≠ e a from fun h ↦ ha (by simpa using congrArg e.symm h.symm)]
private lemma pMapS {α β : Type*} [Fintype α] (p : PMF α) (f : α → β) (b : β) :
    p.map f b = ∑ a : α, @ite r0inf (b = f a) (cpd) (p a) 0 := by classical rw [pMapA, tsum_fintype]
private lemma pMapU {α β : Type*} [Finite α] (p : PMF α) (f : α → β) (b : β) (a₀ : α)
    (h0 : b = f a₀) (hu : ∀ a, b = f a → a = a₀) : p.map f b = p a₀ := by
  classical let _ := Fintype.ofFinite α
  rw [pMapS, sum1 a₀ (fun a _ ha ↦ iteR fun h ↦ ha (hu a h)) sglU, iteL h0]
private lemma pMapZ {α β : Type*} [Finite α] (p : PMF α) (f : α → β) (b : β) (hz : ∀ a, b ≠ f a) :
    p.map f b = 0 := by
  classical let _ := Fintype.ofFinite α; rw [pMapS]; exact sum0 a ↦ iteR (hz a)
private lemma iInv {A B : Type*} (g : A → B) (inv : B → A) (h : ∀ a, inv (g a) = a) : fInj g :=
  fun _ _ e ↦ by simpa [h] using congrArg inv e
private lemma sumImg0 {A B M : Type*} [Fintype A] [Fintype B] [AddCommMonoid M] (emb : A → B)
    (hinj : fInj emb) (g : B → M) (hz : ∀ b, (¬ ∃ a, b = emb a) → g b = 0) :
    ∑ b, g b = ∑ a, g (emb a) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image emb)),
    Finset.sum_image fun _ _ _ _ h ↦ hinj h]
  exact fun b _ hb ↦ hz b fun ⟨a, ha⟩ ↦ hb (Finset.mem_image.2 ⟨a, memU _, ha.symm⟩)
private lemma prodImg1 {A B M : Type*} [Fintype A] [Fintype B] [CommMonoid M] (emb : A → B)
    (hinj : fInj emb) (g : B → M) (h1 : ∀ b, (¬ ∃ a, b = emb a) → g b = 1) :
    ∏ b, g b = ∏ a, g (emb a) := by
  classical
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image emb)),
    Finset.prod_image fun _ _ _ _ h ↦ hinj h]
  exact fun b _ hb ↦ h1 b fun ⟨a, ha⟩ ↦ hb (Finset.mem_image.2 ⟨a, memU _, ha.symm⟩)
private lemma pMapPS {α β γ : Type*} [Finite α] [Fintype β] (p : PMF (α × β)) (f : α × β → γ)
    (c : γ) (a₀ : α) (hc : ∀ a b, c = f (a, b) → a = a₀) :
    p.map f c = ∑ b : β, @ite r0inf (c = f (a₀, b)) (cpd) (p (a₀, b)) 0 := by
  classical let _ := Fintype.ofFinite α
  rw [pMapS, fSP]; exact sum1 a₀ (fun a _ ha ↦ sum0 b ↦ iteR fun h ↦ ha (hc a b h)) sglU
private lemma prod_pi_coord {n : ℕ} {α : Type*} [Fintype α] (f : Fin n → α → r0inf)
    (h : ∀ i, ∑ a : α, f i a = 1) (k : Fin n) (b : α) :
    (∑ x : Fin n → α, @ite r0inf (b = x k) (cpd) (∏ i, f i (x i)) 0) = f k b := by
  classical
  have h1 : (∑ x : Fin n → α, @ite r0inf (b = x k) (cpd) (∏ i, f i (x i)) 0) =
      ∑ x : Fin n → α, ∏ i, if i = k then (if x i = b then f i (x i) else 0) else f i (x i) :=
    sumC x ↦ by
      by_cases hxk : b = x k
      · rw [iteL hxk]; exact prodC i ↦ by by_cases hik : i = k <;> simp [hik, hxk.symm]
      · rw [iteR hxk]; exact (Finset.prod_eq_zero (memU k) (by simp [Ne.symm hxk])).symm
  rw [h1, ← prodS (fun i a ↦ if i = k then (if a = b then f i a else 0) else f i a),
    Finset.prod_eq_single k (fun i _ hik ↦ by simp_rw [iteR hik]; exact h i) sglU]; simp
private lemma eInj {Ω A B : Type*} [Fintype A] [Fintype B] (p : PMF Ω) (f : Ω → A) (g : A → B)
    (hg : fInj g) : pmfH (p.map fun w ↦ g (f w)) = pmfH (p.map f) := by
  rw [show (fun w ↦ g (f w)) = g ∘ f from rfl, ← pMapC, pmfHInj _ hg]
private lemma eKer {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (K : α → PMF β)
    (q : PMF (α × β)) (hq : ∀ a b, q (a, b) = p a * K a b) :
    pmfH q = pmfH p + ∑ a : α, eTR (p a) * pmfH (K a) := by
  rw [pmfHD, pmfHD, fSP]
  simp_rw [hq, eTRM, Real.negMulLog_mul, sumA, ← sumM, ← mulS, pSum1R, one_mul, ← pmfHD]
private lemma ent_sigma {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Fintype (β i)] (w : ι → ℝ)
    (hw₀ : ∀ i, 0 ≤ w i) (K : ∀ i, PMF (β i)) (q : PMF (Σ i, β i))
    (hq : ∀ i b, q ⟨i, b⟩ = eOR (w i) * K i b) :
    pmfH q = (∑ i : ι, nml (w i)) + ∑ i : ι, w i * pmfH (K i) := by
  rw [pmfHD, Fintype.sum_sigma]
  simp_rw [fun i ↦ show ∑ b : β i, nml (eTR (q ⟨i, b⟩)) = nml (w i) + w i * pmfH (K i) by
    simp_rw [hq, eTRM, eTRO (hw₀ i), Real.negMulLog_mul, sumA, ← sumM, ← mulS, pSum1R, one_mul,
      ← pmfHD], sumA]
private def rIC {X Y M T : Type*} [Fintype X] [Fintype Y] [Fintype M] [Fintype T]
    (q : PMF (X × Y × M × T)) : ℝ :=
  (pmfH (q.map fun w ↦ (w.2.2.2, w.2.1, w.2.2.1)) - pmfH (q.map fun w ↦ (w.2.1, w.2.2.1)) -
   pmfH (q.map fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) +
     pmfH (q.map fun w ↦ (w.1, w.2.1, w.2.2.1))) +
  (pmfH (q.map fun w ↦ (w.2.2.2, w.1, w.2.2.1)) - pmfH (q.map fun w ↦ (w.1, w.2.2.1)) -
   pmfH (q.map fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) +
     pmfH (q.map fun w ↦ (w.1, w.2.1, w.2.2.1)))
private lemma rIC_inj {X Y R₁ R₂ T₁ T₂ : Type*} [Fintype X] [Fintype Y] [Fintype R₁] [Fintype R₂]
    [Fintype T₁] [Fintype T₂] (q : PMF (X × Y × R₁ × T₁)) (f₀ : R₁ → R₂) (fT : T₁ → T₂)
    (h₀ : fInj f₀) (hT : fInj fT) :
    rIC (q.map fun w ↦ (w.1, w.2.1, f₀ w.2.2.1, fT w.2.2.2)) = rIC q := by
  rw [rIC, rIC]; simp only [pMapC, Function.comp_def]
  rw [eInj q (fun w ↦ (w.2.2.2, w.2.1, w.2.2.1)) (fun v ↦ (fT v.1, v.2.1, f₀ v.2.2))
      (fun ⟨_,_,_⟩ ⟨_,_,_⟩ h ↦ by aesop),
    eInj q (fun w ↦ (w.2.1, w.2.2.1)) (fun v ↦ (v.1, f₀ v.2)) (fun ⟨_,_⟩ ⟨_,_⟩ h ↦ by aesop),
    eInj q (fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) (fun v ↦ (fT v.1, v.2.1, v.2.2.1, f₀ v.2.2.2))
      (fun ⟨_,_,_,_⟩ ⟨_,_,_,_⟩ h ↦ by aesop),
    eInj q (fun w ↦ (w.1, w.2.1, w.2.2.1)) (fun v ↦ (v.1, v.2.1, f₀ v.2.2))
      (fun ⟨_,_,_⟩ ⟨_,_,_⟩ h ↦ by aesop),
    eInj q (fun w ↦ (w.2.2.2, w.1, w.2.2.1)) (fun v ↦ (fT v.1, v.2.1, f₀ v.2.2))
      (fun ⟨_,_,_⟩ ⟨_,_,_⟩ h ↦ by aesop),
    eInj q (fun w ↦ (w.1, w.2.2.1)) (fun v ↦ (v.1, f₀ v.2)) (fun ⟨_,_⟩ ⟨_,_⟩ h ↦ by aesop)]
private lemma ent_prod_pi {α : Type*} [Fintype α] :
    ∀ (n : ℕ) (P : Fin n → PMF α) (q : PMF (Fin n → α)),
      (∀ z, q z = ∏ i : Fin n, P i (z i)) → pmfH q = ∑ i : Fin n, pmfH (P i)
  | 0, _, q, hq => by simp [pmfHD, show q default = 1 by simp [hq]]
  | n + 1, P, q, hq => by
    let e : (Fin (n + 1) → α) ≃ (Fin n → α) × α :=
      ⟨fun z ↦ (fun j ↦ z j.castSucc, z (Fin.last n)), fun p ↦ Fin.snoc p.1 p.2,
        fun _ ↦ funext fun i ↦ Fin.lastCases (by simp) (fun _ ↦ by simp) i,
        fun ⟨_, _⟩ ↦ Prod.ext (by ext; simp) (by simp)⟩
    let q0 : PMF (Fin n → α) := PMF.ofFintype (fun z ↦ ∏ j, P j.castSucc (z j)) (pProd1 _)
    have hk := eKer q0 (fun _ ↦ P (Fin.last n)) (q.map e) fun _ _ ↦ by
      rw [pMapE]; simp [e, hq, Fin.prod_univ_castSucc, q0, pmfOF]
    rw [pmfHInj _ e.injective, ← sumM, pSum1R, one_mul, ent_prod_pi n _ q0 (fun _ ↦ rfl)] at hk
    exact hk.trans (Fin.sum_univ_castSucc (fun i ↦ pmfH (P i))).symm
private lemma cEntP_le_comp_right {Ω α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : PMF Ω) (U : Ω → α) (V : Ω → β) (h : β → γ) :
    cEntP p U V ≤ cEntP p U (h ∘ V) := by
  have hle := Cslib.Probability.PMF.conditionalEntropy_map_fst_ge (p.map fun w ↦ (V w, U w)) h
  rw [pMapC] at hle
  exact mul_le_mul_of_nonneg_right hle (Real.log_nonneg (by norm_num))
private lemma cEntP_prod_right_le {Ω α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : PMF Ω) (U : Ω → α) (V : Ω → β) (W : Ω → γ) :
    cEntP p U (fun w ↦ (V w, W w)) ≤ cEntP p U W :=
  cEntP_le_comp_right p U (fun w ↦ (V w, W w)) Prod.snd
private lemma condEnt_pi_le {Ω α β : Type*} [Fintype α] [Fintype β] (p : PMF Ω) (V : Ω → β) :
    ∀ (n : ℕ) (U : Fin n → Ω → α), cEntP p (fun w i ↦ U i w) V ≤ ∑ i : Fin n, cEntP p (U i) V
  | 0, U => by
    rw [Finset.univ_eq_empty, Finset.sum_empty, cEntP, Cslib.Probability.PMF.conditionalEntropy]
    simp only [pMapC, Function.comp_def]
    have h1 : Cslib.Probability.PMF.entropy (p.map fun w ↦ (V w, fun i : Fin 0 ↦ U i w)) =
        Cslib.Probability.PMF.entropy (p.map V) := by
      have heq : (p.map fun w ↦ (V w, fun i : Fin 0 ↦ U i w)) =
          (p.map V).map fun v ↦ (v, (default : Fin 0 → α)) := by
        rw [pMapC]; congr 1; funext w; exact Prod.ext rfl (Subsingleton.elim _ _)
      rw [heq]; exact Cslib.Probability.PMF.entropy_map_of_injective _ (fun _ _ h ↦ (pmi h).1)
    rw [h1, sub_self, zero_mul]
  | n + 1, U => by
    let e : β × (Fin (n + 1) → α) ≃ (β × (Fin n → α)) × α :=
      ⟨fun x ↦ ((x.1, fun j ↦ x.2 j.castSucc), x.2 (Fin.last n)),
        fun y ↦ (y.1.1, Fin.snoc y.1.2 y.2),
        fun ⟨_, _⟩ ↦ Prod.ext rfl (funext fun i ↦ Fin.lastCases (by simp) (fun _ ↦ by simp) i),
        fun ⟨⟨_, _⟩, _⟩ ↦ Prod.ext (Prod.ext rfl (by ext; simp)) (by simp)⟩
    have hsw : Cslib.Probability.PMF.conditionalEntropy (p.map fun w ↦ (V w, fun i ↦ U i w)) =
        Cslib.Probability.PMF.conditionalEntropy (p.map fun w ↦
          (V w, fun j : Fin n ↦ U j.castSucc w)) + Cslib.Probability.PMF.conditionalEntropy
          (p.map fun w ↦ ((V w, fun j : Fin n ↦ U j.castSucc w), U (Fin.last n) w)) := by
      simp only [Cslib.Probability.PMF.conditionalEntropy, pMapC, Function.comp_def]
      have hmap : (p.map fun w ↦ ((V w, fun j : Fin n ↦ U j.castSucc w), U (Fin.last n) w)) =
          (p.map fun w ↦ (V w, fun i ↦ U i w)).map e := by rw [pMapC]; rfl
      rw [hmap, Cslib.Probability.PMF.entropy_map_of_injective _ e.injective]; ring
    have hdrop := Cslib.Probability.PMF.conditionalEntropy_map_fst_ge
      (p.map fun w ↦ ((V w, fun j : Fin n ↦ U j.castSucc w), U (Fin.last n) w)) Prod.fst
    simp only [pMapC, Function.comp_def] at hdrop
    have hrec := condEnt_pi_le p V n (fun j ↦ U j.castSucc)
    have hsum : ∑ i : Fin (n + 1), cEntP p (U i) V =
        (∑ j : Fin n, cEntP p (U j.castSucc) V) + cEntP p (U (Fin.last n)) V :=
      Fin.sum_univ_castSucc _
    rw [hsum, cEntP, hsw, add_mul]
    linarith [mul_le_mul_of_nonneg_right hdrop (Real.log_nonneg (by norm_num) : (0 : ℝ) ≤ rL2)]
end PMFHelpers
section SharedHelpers
open RandomizedProtocol
variable {X : Type u} {Y : Type v} {Z : Type w}
private abbrev sum_exec_tr := @RandomizedProtocol.sum_execPMF_transcript
private lemma joint_map_xym₀ [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z)
    (μ : PMF (X × Y)) (x : X) (y : Y) (m₀ : P.Pub) :
    (P.jointPMF μ).map (fun w ↦ (w.1, w.2.1, w.2.2.1)) (x, y, m₀) = μ (x, y) * P.pubCoin m₀ := by
  classical rw [pMapS, fSP]; simp_rw [fSP]
  rw [sum1 x (fun _ _ h ↦ sum0 y' ↦ sum0 m' ↦ sum0 tr' ↦ by simp [h.symm]) sglU,
    sum1 y (fun _ _ h ↦ sum0 m' ↦ sum0 tr' ↦ by simp [h.symm]) sglU,
    sum1 m₀ (fun _ _ h ↦ sum0 tr' ↦ by simp [h.symm]) sglU]
  simp only [↓reduceIte]; simp_rw [jointPMF_apply, ← mulS, sum_exec_tr]
private lemma ent_joint_xym₀ [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z)
    (μ : PMF (X × Y)) :
    pmfH ((P.jointPMF μ).map fun w ↦ (w.1, w.2.1, w.2.2.1)) = pmfH μ + pmfH P.pubCoin := by
  let e2 : (X × Y × P.Pub) ≃ ((X × Y) × P.Pub) :=
    ⟨fun w ↦ ((w.1, w.2.1), w.2.2), fun v ↦ (v.1.1, v.1.2, v.2), fun ⟨_,_,_⟩ ↦ rfl,
      fun ⟨⟨_,_⟩,_⟩ ↦ rfl⟩
  rw [← pmfHInj _ e2.injective, eKer μ (fun _ ↦ P.pubCoin)
    (((P.jointPMF μ).map fun w ↦ (w.1, w.2.1, w.2.2.1)).map e2)
    fun ⟨x, y⟩ m₀ ↦ by rw [pMapE]; exact joint_map_xym₀ P μ x y m₀, ← sumM, pSum1R, one_mul]
private lemma joint_condEnt_exec [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z)
    (μ : PMF (X × Y)) :
    pmfH ((P.jointPMF μ).map fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) -
        pmfH ((P.jointPMF μ).map fun w ↦ (w.1, w.2.1, w.2.2.1)) =
      ∑ xy : X × Y, (μ xy).toReal * (pmfH (P.execPMF xy.1 xy.2) - pmfH P.pubCoin) := by
  let e1 : (X × Y × P.Pub × P.Transcript) ≃ ((X × Y) × (P.Pub × P.Transcript)) :=
    ⟨fun w ↦ ((w.1, w.2.1), (w.2.2.1, w.2.2.2)), fun v ↦ (v.1.1, v.1.2, v.2.1, v.2.2),
        fun ⟨_,_,_,_⟩ ↦ rfl, fun ⟨⟨_,_⟩,⟨_,_⟩⟩ ↦ rfl⟩
  have hH1 : pmfH ((P.jointPMF μ).map fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) =
      pmfH μ + ∑ xy : X × Y, (μ xy).toReal * pmfH (P.execPMF xy.1 xy.2) := by
    have hJ4 : pmfH ((P.jointPMF μ).map fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) =
        pmfH (P.jointPMF μ) :=
      pmfHInj (P.jointPMF μ) (f := fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) inj4
    rw [hJ4, ← pmfHInj (P.jointPMF μ) e1.injective]
    exact eKer μ (fun xy ↦ P.execPMF xy.1 xy.2) ((P.jointPMF μ).map e1)
      fun ⟨_, _⟩ ⟨_, _⟩ ↦ by rw [pMapE]; rfl
  rw [hH1, ent_joint_xym₀]; simp_rw [mul_sub, sumSub, ← sumM, pSum1R, one_mul]; ring
private lemma ic_eq_raw [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z) (μ : PMF (X × Y)) :
    P.internalInfoCost μ = (rL2)⁻¹ * rIC (P.jointPMF μ) := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [internalInfoCost_def, rIC]; dsimp only [pmfH]; field_simp [h2]
private lemma ic_ofFintype_eqv [Fintype X] [Fintype Y] {R₀ R₀' : Type*} {r : ℕ}
    {Ω : Fin r → Type*} [Fintype R₀] [Nonempty R₀] [Fintype R₀'] [∀ t, Fintype (Ω t)]
    [∀ t, Nonempty (Ω t)] (pub : PMF R₀)
    (aStep : ∀ t : Fin r, X → R₀ → (∀ j : Fin t.1, Ω ⟨j.1, j.2.trans t.2⟩) → PMF (Ω t))
    (bStep : ∀ t : Fin r, Y → R₀ → (∀ j : Fin t.1, Ω ⟨j.1, j.2.trans t.2⟩) → PMF (Ω t))
    (out : R₀ → (∀ t : Fin r, Ω t) → Z) (μ : PMF (X × Y))
    (q : PMF (X × Y × R₀' × (∀ t : Fin r, Ω t))) (eR : R₀' ≃ R₀)
    (hq : ∀ x y r₀' ω, μ (x, y) * (pub (eR r₀') * ∏ t : Fin r,
      (if Even t.1 then aStep t x (eR r₀') (fun j ↦ ω ⟨j.1, j.2.trans t.2⟩) (ω t)
       else bStep t y (eR r₀') (fun j ↦ ω ⟨j.1, j.2.trans t.2⟩) (ω t))) = q (x, y, r₀', ω)) :
    (ofFintype pub aStep bStep out).internalInfoCost μ = (rL2)⁻¹ * rIC q := by
  let e₀ := eFin R₀
  let eTr : (∀ t : Fin r, Ω t) ≃ (ofFintype pub aStep bStep out).Transcript :=
    Equiv.piCongrRight fun t ↦ eFin (Ω t)
  let eAll : (X × Y × R₀' × (∀ t : Fin r, Ω t)) ≃
      (X × Y × (ofFintype pub aStep bStep out).Pub × (ofFintype pub aStep bStep out).Transcript) :=
    Equiv.prodCongr (Equiv.refl X) (Equiv.prodCongr (Equiv.refl Y)
      (Equiv.prodCongr (eR.trans e₀) eTr))
  have hJm : (ofFintype pub aStep bStep out).jointPMF μ = q.map eAll := by
    ext ⟨x, y, p₀, ptr⟩; rw [pMapE, jointPMF_apply]
    have h1 : (p₀, ptr) = ofFintypeExecEquiv pub aStep bStep out (e₀.symm p₀, eTr.symm ptr) :=
      Prod.ext (e₀.apply_symm_apply p₀).symm (funext fun t ↦
          (congrFun (eTr.apply_symm_apply ptr) t).symm)
    have hq0 := hq x y (eR.symm (e₀.symm p₀)) (eTr.symm ptr); rw [eR.apply_symm_apply] at hq0
    rw [h1, execPMF_ofFintype_apply, hq0, ← h1]; rfl
  rw [ic_eq_raw, hJm]
  exact congrArg ((rL2)⁻¹ * ·) (rIC_inj q (eR.trans e₀) eTr (eR.trans e₀).injective eTr.injective)
private def inRev [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] (f : X × Y → Z) :
    RandomizedProtocol X Y Z :=
  ofFintype (Ω := fun _ : Fin 2 ↦ X ⊕ Y) (PMF.pure (0 : Fin 1))
    (fun _ x _ _ ↦ PMF.pure (Sum.inl x)) (fun _ y _ _ ↦ PMF.pure (Sum.inr y))
    (fun _ tr ↦ match tr 0, tr 1 with
      | Sum.inl x, Sum.inr y => f (x, y)
      | _, _ => f (cArb X, cArb Y))
private lemma inputErr_rev [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] (f : X × Y → Z)
    (x : X) (y : Y) : (inRev f).inputError f x y = 0 := by
  classical rw [inRev, inputError_ofFintype]
  refine Finset.sum_eq_zero fun ⟨_, ω⟩ _ ↦ ?_; split_ifs with hne; swap; · rfl
  rw [Fin.prod_univ_two, iteL (by decide : Even (0 : Fin 2).1),
      iteR (by decide : ¬ Even (1 : Fin 2).1)]
  by_cases hx : ω 0 = Sum.inl x
  · have hy : ω 1 ≠ Sum.inr y := fun hy ↦ hne (by
      change (match ω 0, ω 1 with
        | Sum.inl x, Sum.inr y => f (x, y)
        | _, _ => _) = f (x, y)
      rw [hx, hy])
    simp [pPureA, iteR hy]
  · simp [pPureA, iteR hx]
private lemma distErr_rev [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] (f : X × Y → Z)
    (μ : PMF (X × Y)) : (inRev f).distError f μ = 0 := by rw [distError_def]; simp [inputErr_rev]
end SharedHelpers

/-! ### Protocol Multiplexing, Prior Concavity, and Braverman's Minimax Theorem -/
section Minimax
open RandomizedProtocol
variable {X : Type u} {Y : Type v} {Z : Type w}
@[reducible] private def muxR {N : ℕ} (Ps : Fin N → RandomizedProtocol X Y Z) : ℕ :=
  Finset.univ.sup fun j ↦ (Ps j).rounds
@[reducible] private def muxMC {N : ℕ} (Ps : Fin N → RandomizedProtocol X Y Z)
    (t : Fin (muxR Ps)) : ℕ :=
  Finset.univ.sup fun j ↦ if h : t.1 < (Ps j).rounds then (Ps j).msgCard ⟨t.1, h⟩ else 0
private lemma le_muxR {N : ℕ} (Ps : Fin N → RandomizedProtocol X Y Z) (j : Fin N) :
    (Ps j).rounds ≤ muxR Ps := Finset.le_sup (f := fun i ↦ (Ps i).rounds) (memU j)
private lemma le_muxMC {N : ℕ} (Ps : Fin N → RandomizedProtocol X Y Z) (j : Fin N)
    (t : Fin (muxR Ps)) (ht : t.1 < (Ps j).rounds) : (Ps j).msgCard ⟨t.1, ht⟩ ≤ muxMC Ps t :=
  (by simp [ht] : (Ps j).msgCard ⟨t.1, ht⟩ ≤ _).trans
    (Finset.le_sup (f := fun i ↦ if h : t.1 < (Ps i).rounds then (Ps i).msgCard ⟨t.1, h⟩ else 0)
      (memU j))
private def muxTr {N : ℕ} (Ps : Fin N → RandomizedProtocol X Y Z) (j : Fin N)
    (tr : (Ps j).Transcript) : ∀ t : Fin (muxR Ps), Fin (muxMC Ps t + 1) := fun t ↦
  if ht : t.1 < (Ps j).rounds then
    Fin.castLE (Nat.succ_le_succ (le_muxMC Ps j t ht)) (tr ⟨t.1, ht⟩) else 0
private def muxExtr {N : ℕ} (Ps : Fin N → RandomizedProtocol X Y Z) (j : Fin N)
    (tr : ∀ t : Fin (muxR Ps), Fin (muxMC Ps t + 1)) : (Ps j).Transcript := fun t ↦
  if hm : (tr ⟨t.1, t.2.trans_le (le_muxR Ps j)⟩).1 < (Ps j).msgCard t + 1 then ⟨_, hm⟩ else 0
private lemma muxExtr_muxTr {N : ℕ} (Ps : Fin N → RandomizedProtocol X Y Z) (j : Fin N)
    (tr : (Ps j).Transcript) : muxExtr Ps j (muxTr Ps j tr) = tr := funext fun t ↦
  Fin.ext (by simp [muxExtr, muxTr, t.2, Nat.lt_succ_iff.1 (tr t).2])
private lemma muxTr_inj {N : ℕ} (Ps : Fin N → RandomizedProtocol X Y Z) (j : Fin N) :
    fInj (muxTr Ps j) := iInv (muxTr Ps j) (muxExtr Ps j) (muxExtr_muxTr Ps j)
private lemma castLE_pmf {a b : ℕ} (hab : a ≤ b) (p : PMF (Fin a)) (m : Fin b) :
    p.map (Fin.castLE hab) m = if hm : m.1 < a then p ⟨m.1, hm⟩ else 0 := by
  classical rw [pMapA]; split_ifs with hm
  · rw [tsum_eq_single ⟨m.1, hm⟩]; · simp
    · exact fun _ hk ↦ by simp [show m ≠ Fin.castLE hab _ from fun he ↦
        hk (Fin.ext (congrArg Fin.val he).symm)]
  · rw [tsum_fintype, sum0 k ↦ by simp [show m ≠ Fin.castLE hab k from
      fun he ↦ hm (by rw [congrArg Fin.val he]; exact k.2)]]
private lemma sum_sigma_ofReal_mul {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (w : ι → ℝ) (hw₀ : ∀ j, 0 ≤ w j) (hw₁ : ∑ j, w j = 1) (K : ∀ i, PMF (α i)) :
    ∑ s : (Σ j, α j), eOR (w s.1) * K s.1 s.2 = 1 := by
  rw [Fintype.sum_sigma, sumC j ↦ (show (∑ y : α j, eOR (w j) * K j y) = eOR (w j) by
      rw [← Finset.mul_sum, pSum1, mul_one]),
    ← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hw₀ j), hw₁, ENNReal.ofReal_one]
private def muxPub {N : ℕ} (w : Fin N → ℝ) (hw₀ : ∀ j, 0 ≤ w j) (hw₁ : ∑ j, w j = 1)
    (Ps : Fin N → RandomizedProtocol X Y Z) : PMF (Σ j : Fin N, (Ps j).Pub) :=
  PMF.ofFintype (fun jm ↦ eOR (w jm.1) * (Ps jm.1).pubCoin jm.2)
    (sum_sigma_ofReal_mul w hw₀ hw₁ fun j ↦ (Ps j).pubCoin)
private def muxStep {N : ℕ} (Ps : Fin N → RandomizedProtocol X Y Z)
    (fn : ∀ (j : Fin N) (t : Fin (Ps j).rounds), (Ps j).Pub →
      (∀ s : Fin t.1, (Ps j).Msg ⟨s.1, s.2.trans t.2⟩) → PMF ((Ps j).Msg t))
    (t : Fin (muxR Ps)) (jm : Σ j : Fin N, (Ps j).Pub)
    (h : ∀ s : Fin t.1, Fin (muxMC Ps ⟨s.1, s.2.trans t.2⟩ + 1)) : PMF (Fin (muxMC Ps t + 1)) :=
  if ht : t.1 < (Ps jm.1).rounds then
    (fn jm.1 ⟨t.1, ht⟩ jm.2 fun s ↦ if hm : (h s).1 < (Ps jm.1).msgCard ⟨s.1, s.2.trans ht⟩ + 1
      then ⟨_, hm⟩ else 0).map (Fin.castLE (Nat.succ_le_succ (le_muxMC Ps jm.1 t ht)))
  else PMF.pure 0

/-- Convex mixture (multiplexing) of protocols `Ps` weighted by `w` (`w j ≥ 0`, `∑ j, w j = 1`). -/
def RandomizedProtocol.mux {N : ℕ} [NeZero N] (w : Fin N → ℝ) (hw₀ : ∀ j, 0 ≤ w j)
    (hw₁ : ∑ j, w j = 1) (Ps : Fin N → RandomizedProtocol X Y Z) : RandomizedProtocol X Y Z :=
  let _ : Nonempty (Σ j : Fin N, (Ps j).Pub) := ⟨⟨0, 0⟩⟩
  ofFintype (R₀ := Σ j : Fin N, (Ps j).Pub) (r := muxR Ps) (Ω := fun t ↦ Fin (muxMC Ps t + 1))
    (muxPub w hw₀ hw₁ Ps) (fun t x ↦ muxStep Ps (fun j s m h ↦ (Ps j).aliceStep s x m h) t)
    (fun t y ↦ muxStep Ps (fun j s m h ↦ (Ps j).bobStep s y m h) t)
    (fun jm tr ↦ (Ps jm.1).out jm.2 (muxExtr Ps jm.1 tr))

private lemma mux_prod_eq {N : ℕ} (Ps : Fin N → RandomizedProtocol X Y Z) (x : X) (y : Y)
    (j : Fin N) (m₀ : (Ps j).Pub) (tr : ∀ t : Fin (muxR Ps), Fin (muxMC Ps t + 1)) :
    (∏ t : Fin (muxR Ps),
      if Even t.1 then muxStep Ps (fun i s m h ↦ (Ps i).aliceStep s x m h) t ⟨j, m₀⟩
        (fun s ↦ tr ⟨s.1, s.2.trans t.2⟩) (tr t)
      else muxStep Ps (fun i s m h ↦ (Ps i).bobStep s y m h) t ⟨j, m₀⟩
        (fun s ↦ tr ⟨s.1, s.2.trans t.2⟩) (tr t)) =
      @dite r0inf (∃ tr' : (Ps j).Transcript, tr = muxTr Ps j tr') (cpd)
        (fun h ↦ ∏ t : Fin (Ps j).rounds, (Ps j).stepPMF x y m₀ t
          (fun s ↦ h.choose ⟨s.1, s.2.trans t.2⟩) (h.choose t)) (fun _ ↦ 0) := by
  classical
  let term (t : Fin (muxR Ps)) : r0inf := if ht : t.1 < (Ps j).rounds then
    if hm : (tr t).1 < (Ps j).msgCard ⟨t.1, ht⟩ + 1 then (Ps j).stepPMF x y m₀ ⟨t.1, ht⟩
      (fun s ↦ muxExtr Ps j tr ⟨s.1, s.2.trans ht⟩) ⟨(tr t).1, hm⟩ else 0
    else if tr t = 0 then 1 else 0
  have hprod : (∏ t, if Even t.1 then muxStep Ps (fun i s m h ↦ (Ps i).aliceStep s x m h) t
      ⟨j, m₀⟩ (fun s ↦ tr ⟨s.1, s.2.trans t.2⟩) (tr t)
      else muxStep Ps (fun i s m h ↦ (Ps i).bobStep s y m h) t ⟨j, m₀⟩
        (fun s ↦ tr ⟨s.1, s.2.trans t.2⟩) (tr t)) = ∏ t, term t := prodC t ↦ by
    dsimp only [term, muxStep, muxExtr]
    by_cases he : Even t.1 <;> by_cases ht : t.1 < (Ps j).rounds
    · rw [iteL he, diteL ht, diteL ht, castLE_pmf, (Ps j).stepPMF_of_even _ _ _ he]
    · rw [iteL he, diteR ht, diteR ht, pPureA]; split_ifs <;> simp [*]
    · rw [iteR he, diteL ht, diteL ht, castLE_pmf, (Ps j).stepPMF_of_not_even _ _ _ he]
    · rw [iteR he, diteR ht, diteR ht, pPureA]; split_ifs <;> simp [*]
  rw [hprod]; split_ifs with h
  · rw [prodImg1 (Fin.castLE (le_muxR Ps j)) (fun _ _ e ↦ Fin.ext (Fin.mk.inj e)) term]
    · refine prodC t ↦ ?_
      have hx := congrArg (muxExtr Ps j ·) h.choose_spec; rw [muxExtr_muxTr] at hx
      have hv : (tr (Fin.castLE (le_muxR Ps j) t)).1 = (h.choose t).1 := by
        rw [congrFun h.choose_spec]; simp [muxTr, t.2]
      dsimp only [term]; simp only [Fin.val_castLE, t.2, ↓reduceDIte, hv, (h.choose t).2]
      congr 1; · congr 1; funext s; rw [hx]
    · intro t hni; have hns : ¬ t.1 < (Ps j).rounds := fun hlt ↦ hni ⟨⟨t.1, hlt⟩, Fin.ext rfl⟩
      have htr := congrFun h.choose_spec t; dsimp only [muxTr] at htr
      rw [diteR hns] at htr; simp [term, hns, htr]
  · by_contra hne; have hall : ∀ t, term t ≠ 0 := fun t h0 ↦ hne (Finset.prod_eq_zero (memU t) h0)
    refine h ⟨muxExtr Ps j tr, funext fun t ↦ ?_⟩; by_cases ht : t.1 < (Ps j).rounds
    · have hm : (tr ⟨t.1, t.2⟩).1 < (Ps j).msgCard ⟨t.1, ht⟩ + 1 :=
        by_contra fun hge ↦ hall t (by dsimp only [term]; rw [diteL ht, diteR hge])
      exact Fin.ext (by simp [muxTr, muxExtr, ht, hm])
    · dsimp only [muxTr]; rw [diteR ht]
      exact by_contra fun h0 ↦ hall t (by dsimp only [term]; rw [diteR ht, iteR h0])

/-- Per-input error of a multiplexed protocol is the `w`-weighted average of component errors. -/
theorem RandomizedProtocol.inputError_mux {N : ℕ} [NeZero N] (w : Fin N → ℝ)
    (hw₀ : ∀ j, 0 ≤ w j) (hw₁ : ∑ j, w j = 1) (Ps : Fin N → RandomizedProtocol X Y Z)
    (f : X × Y → Z) (x : X) (y : Y) :
    (RandomizedProtocol.mux w hw₀ hw₁ Ps).inputError f x y =
      ∑ j : Fin N, w j * (Ps j).inputError f x y := by
  classical rw [mux, inputError_ofFintype, fSP, Fintype.sum_sigma]
  refine sumC j ↦ ?_; rw [inputError_def, fSP, mulS]
  refine sumC m₀ ↦ ?_; rw [mulS, sumImg0 (muxTr Ps j) (muxTr_inj Ps j)]
  · refine sumC tr' ↦ ?_; have hex : ∃ tr'', muxTr Ps j tr' = muxTr Ps j tr'' := ⟨tr', rfl⟩
    rw [muxPub, pmfOF, mul_assoc, mux_prod_eq, diteL hex, muxTr_inj Ps j hex.choose_spec.symm,
      ← (Ps j).execPMF_apply x y (m₀, tr'), muxExtr_muxTr, eTRM, eTRO (hw₀ j)]; split_ifs <;> simp
  · intro tr hne; rw [muxPub, pmfOF, mul_assoc, mux_prod_eq, diteR hne]; simp

private lemma mux_sigma_ent {ι : Type*} [Fintype ι] {α β : ι → Type*} {A B : Type*}
    [∀ i, Fintype (β i)] [Fintype B] (w : ι → ℝ) (hw₀ : ∀ i, 0 ≤ w i) (K : ∀ i, PMF (α i))
    (qS : PMF (Σ i, α i)) (hqS : ∀ i a, qS ⟨i, a⟩ = eOR (w i) * K i a)
    (emb : (Σ i, α i) → A) (g : A → B) (h : ∀ i, α i → β i) (κ : (Σ i, β i) → B)
    (hκ : fInj κ) (hcomm : ∀ i a, g (emb ⟨i, a⟩) = κ ⟨i, h i a⟩) :
    pmfH ((qS.map emb).map g) = (∑ i : ι, nml (w i)) + ∑ i : ι, w i * pmfH ((K i).map (h i)) := by
  classical rw [pMapC, show g ∘ emb = κ ∘ fun s : Σ i, α i ↦ (⟨s.1, h s.1 s.2⟩ : Σ i, β i)
      from funext fun ⟨i, a⟩ ↦ hcomm i a, ← pMapC, pmfHInjOn _ hκ.injOn]
  refine ent_sigma w hw₀ (fun i ↦ (K i).map (h i)) _ fun i b ↦ ?_
  rw [pMapA, tsum_sigma', tsum_eq_single i]
  · rw [pMapA]; refine (tsum_congr fun a ↦ ?_).trans ENNReal.tsum_mul_left
    by_cases hb : b = h i a; · subst hb; simp [hqS i a]
    · simp [hb, show (⟨i, b⟩ : Σ k, β k) ≠ ⟨i,
        h i a⟩ from fun he ↦ hb (eq_of_heq (Sigma.mk.inj he).2)]
  · exact fun j hji ↦ tsum_eq_zero_iff.2 fun a ↦ iteR fun he ↦ hji (congrArg Sigma.fst he).symm

private def muxEmb {N : ℕ} (Ps : Fin N → RandomizedProtocol X Y Z)
    (s : Σ j : Fin N, X × Y × (Ps j).Pub × (Ps j).Transcript) :
    X × Y × (Σ j : Fin N, (Ps j).Pub) × (∀ t : Fin (muxR Ps), Fin (muxMC Ps t + 1)) :=
  (s.2.1, s.2.2.1, ⟨s.1, s.2.2.2.1⟩, muxTr Ps s.1 s.2.2.2.2)
private lemma muxEmb_inj {N : ℕ} (Ps : Fin N → RandomizedProtocol X Y Z) : fInj (muxEmb Ps) := by
  rintro ⟨i, _, _, _, _⟩ ⟨j, _, _, _, _⟩ h
  rcases pmi h with ⟨rfl, h2⟩; rcases pmi h2 with ⟨rfl, h3⟩; rcases pmi h3 with ⟨hm, htr⟩
  rcases Sigma.mk.inj hm with ⟨rfl, hm'⟩; cases eq_of_heq hm'; cases muxTr_inj Ps i htr; rfl

private lemma mux_ent_aux {N : ℕ} {X : Type u} {Y : Type v} {Z : Type w} [Fintype X] [Fintype Y]
    (w : Fin N → ℝ) (hw₀ : ∀ j, 0 ≤ w j) (Ps : Fin N → RandomizedProtocol X Y Z) (μ : PMF (X × Y))
    (qS : PMF (Σ j : Fin N, X × Y × (Ps j).Pub × (Ps j).Transcript))
    (hqS : ∀ j u, qS ⟨j, u⟩ = eOR (w j) * (Ps j).jointPMF μ u) {C : Type*} [Fintype C]
    (b : X × Y → C) :
    pmfH ((qS.map (muxEmb Ps)).map fun u ↦ (u.2.2.2, b (u.1, u.2.1), u.2.2.1)) =
      (∑ j, nml (w j)) + ∑ j, w j * pmfH (((Ps j).jointPMF μ).map fun u ↦
        (u.2.2.2, b (u.1, u.2.1), u.2.2.1)) ∧
    pmfH ((qS.map (muxEmb Ps)).map fun u ↦ (b (u.1, u.2.1), u.2.2.1)) =
      (∑ j, nml (w j)) + ∑ j, w j * pmfH (((Ps j).jointPMF μ).map fun u ↦
        (b (u.1, u.2.1), u.2.2.1)) := by
  classical
  let R₀ := Σ j : Fin N, (Ps j).Pub; let Tr := ∀ t : Fin (muxR Ps), Fin (muxMC Ps t + 1)
  refine ⟨mux_sigma_ent (α := fun j ↦ X × Y × (Ps j).Pub × (Ps j).Transcript)
      (β := fun i ↦ (Ps i).Transcript × C × (Ps i).Pub) (B := Tr × C × R₀)
      w hw₀ (fun j ↦ (Ps j).jointPMF μ) qS hqS (muxEmb Ps)
      (fun u ↦ (u.2.2.2, b (u.1, u.2.1), u.2.2.1)) (fun _ u ↦ (u.2.2.2, b (u.1, u.2.1), u.2.2.1))
      (fun s ↦ (muxTr Ps s.1 s.2.1, s.2.2.1, (⟨s.1, s.2.2.2⟩ : R₀)))
      (fun ⟨j₁, _, _, _⟩ ⟨_, _, _, _⟩ he ↦ by
        rcases pmi he with ⟨htr, h2⟩; rcases pmi h2 with ⟨rfl, hm⟩
        rcases Sigma.mk.inj hm with ⟨rfl, hm'⟩
        cases eq_of_heq hm'; cases muxTr_inj Ps j₁ htr; rfl) (fun _ _ ↦ rfl),
    mux_sigma_ent (α := fun j ↦ X × Y × (Ps j).Pub × (Ps j).Transcript)
      (β := fun i ↦ C × (Ps i).Pub) (B := C × R₀) w hw₀ (fun j ↦ (Ps j).jointPMF μ) qS hqS
      (muxEmb Ps) (fun u ↦ (b (u.1, u.2.1), u.2.2.1)) (fun _ u ↦ (b (u.1, u.2.1), u.2.2.1))
      (fun s ↦ (s.2.1, (⟨s.1, s.2.2⟩ : R₀))) (fun ⟨_, _, _⟩ ⟨_, _, _⟩ he ↦ by
        rcases pmi he with ⟨rfl, hm⟩; rcases Sigma.mk.inj hm with ⟨rfl, hm'⟩
        cases eq_of_heq hm'; rfl) (fun _ _ ↦ rfl)⟩

/-- Internal information cost of a multiplexed protocol is the `w`-weighted average of costs. -/
theorem RandomizedProtocol.internalInfoCost_mux [Fintype X] [Fintype Y] {N : ℕ} [NeZero N]
    (w : Fin N → ℝ) (hw₀ : ∀ j, 0 ≤ w j) (hw₁ : ∑ j, w j = 1)
    (Ps : Fin N → RandomizedProtocol X Y Z) (μ : PMF (X × Y)) :
    (RandomizedProtocol.mux w hw₀ hw₁ Ps).internalInfoCost μ =
      ∑ j : Fin N, w j * (Ps j).internalInfoCost μ := by
  classical let _ : Nonempty (Σ j : Fin N, (Ps j).Pub) := ⟨⟨0, 0⟩⟩
  let R₀ := Σ j : Fin N, (Ps j).Pub
  let qS : PMF (Σ j : Fin N, X × Y × (Ps j).Pub × (Ps j).Transcript) :=
    PMF.ofFintype (fun s ↦ eOR (w s.1) * (Ps s.1).jointPMF μ s.2)
      (sum_sigma_ofReal_mul w hw₀ hw₁ fun j ↦ (Ps j).jointPMF μ)
  have hY := mux_ent_aux w hw₀ Ps μ qS (fun _ _ ↦ rfl) Prod.snd
  have hX := mux_ent_aux w hw₀ Ps μ qS (fun _ _ ↦ rfl) Prod.fst
  have hXY := mux_ent_aux w hw₀ Ps μ qS (fun _ _ ↦ rfl) (fun xy : X × Y ↦ xy)
  rw [mux, ic_ofFintype_eqv _ _ _ _ μ (qS.map (muxEmb Ps)) (Equiv.refl R₀) fun x y ⟨j, m₀⟩ tr ↦ ?_]
  · have e3 {R' T' : Type} [Fintype R'] [Fintype T'] (q : PMF (X × Y × R' × T')) :
        pmfH (q.map fun u ↦ (u.2.2.2, u.1, u.2.1, u.2.2.1)) =
          pmfH (q.map fun u ↦ (u.2.2.2, (u.1, u.2.1), u.2.2.1)) :=
      (eInj q (fun u ↦ (u.2.2.2, u.1, u.2.1, u.2.2.1)) (fun v ↦ (v.1, (v.2.1, v.2.2.1),
        v.2.2.2)) inj4).symm
    have e4 {R' T' : Type} [Fintype R'] [Fintype T'] (q : PMF (X × Y × R' × T')) :
        pmfH (q.map fun u ↦ (u.1, u.2.1, u.2.2.1)) = pmfH (q.map fun u ↦ ((u.1, u.2.1), u.2.2.1)) :=
      (eInj q (fun u ↦ (u.1, u.2.1, u.2.2.1)) (fun v ↦ ((v.1, v.2.1), v.2.2)) inj3).symm
    rw [rIC, hY.1, hY.2, hX.1, hX.2, e3, hXY.1, e4, hXY.2]
    have hc (a b c d e f g : ℝ) : (a + b) - (a + c) - (a + d) + (a + e) +
        ((a + f) - (a + g) - (a + d) + (a + e)) = (b - c - d + e) + (f - g - d + e) := by ring
    rw [hc]; simp_rw [← sumSub, ← sumA, mulS]
    exact sumC j ↦ by rw [ic_eq_raw, rIC, ← e3 ((Ps j).jointPMF μ), ← e4 ((Ps j).jointPMF μ)]; ring
  · rw [Equiv.refl_apply, muxPub, pmfOF]; dsimp only; rw [mux_prod_eq]; split_ifs with hex
    · rw [pMapU qS (muxEmb Ps) (x, y, ⟨j, m₀⟩, tr) ⟨j, (x, y, m₀, hex.choose)⟩
        (by simp [muxEmb, ← hex.choose_spec]) fun a h ↦ muxEmb_inj Ps (by
          simpa [muxEmb, ← hex.choose_spec] using h.symm)]
      simp [qS, pmfOF, jointPMF_apply, execPMF_apply]; ring
    · rw [mul_zero, mul_zero]; symm; refine pMapZ qS (muxEmb Ps) _ fun s h ↦ ?_
      rcases pmi (pmi (pmi h).2).2 with ⟨hm, htr⟩; rcases Sigma.mk.inj hm with ⟨rfl, _⟩
      exact hex ⟨s.2.2.2.2, htr⟩

private def simplexSet (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {v | (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1}
private lemma simplex_ne {ι : Type*} [Fintype ι] [Nonempty ι] : (simplexSet ι).Nonempty := by
  classical
  let i₀ := cArb ι
  exact ⟨fun i ↦ if i = i₀ then 1 else 0, fun i ↦ by dsimp only; split_ifs <;> norm_num, by simp⟩
private lemma simplex_conv (ι : Type*) [Fintype ι] : Convex ℝ (simplexSet ι) := by
  rintro u ⟨hu0, hu1⟩ v ⟨hv0, hv1⟩ a b ha hb hab
  exact ⟨fun i ↦ add_nonneg (mul_nonneg ha (hu0 i)) (mul_nonneg hb (hv0 i)), by simp [sumA, ← mulS,
      hu1, hv1, hab]⟩
private lemma simplex_cpt (ι : Type*) [Fintype ι] : IsCompact (simplexSet ι) :=
  IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ ↦ isCompact_Icc (a := (0 : ℝ)) (b := 1))
    ((show IsClosed {v : ι → ℝ | ∀ i, 0 ≤ v i} by
      rw [show {v : ι → ℝ | ∀ i, 0 ≤ v i} = ⋂ i, {v | 0 ≤ v i} by ext; simp]
      exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (by fun_prop) continuous_const))
    fun v ⟨hv0, hv1⟩ i _ ↦ ⟨hv0 i, hv1 ▸ Finset.single_le_sum (fun j _ ↦ hv0 j) (memU i)⟩
private def pmfSimp {ι : Type*} [Fintype ι] {v : ι → ℝ} (hv : v ∈ simplexSet ι) : PMF ι :=
  PMF.ofFintype (fun i ↦ eOR (v i))
    (by rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hv.1 i), hv.2, ENNReal.ofReal_one])
private lemma simplex_linear_conc {ι : Type*} [Fintype ι] (c : ι → ℝ) :
    ConcaveOn ℝ (simplexSet ι) (fun v ↦ ∑ i, v i * c i) :=
  ⟨simplex_conv _, fun _ _ _ _ _ _ _ _ _ ↦ by
    simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply, add_mul, sumA, mul_assoc,
      ← mulS]; linarith⟩

private lemma negMulLog_sub_concave {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (K : ι → α → β → ℝ) (hK : ∀ i a b, 0 ≤ K i a b) :
    ConcaveOn ℝ (simplexSet ι) fun v ↦ (∑ a : α, ∑ b : β, nml (∑ i : ι, v i * K i a b)) -
      ∑ b : β, nml (∑ i : ι, v i * ∑ a : α, K i a b) := by
  refine ⟨simplex_conv ι, fun v₁ hv₁ v₂ hv₂ t₁ t₂ ht₁ ht₂ _ ↦ ?_⟩
  simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  let F (v : ι → ℝ) a b := ∑ i : ι, v i * K i a b
  let G (v : ι → ℝ) b := ∑ i : ι, v i * ∑ a : α, K i a b
  have hp_nn {t : ℝ} {v : ι → ℝ} (ht : 0 ≤ t) (hv : ∀ i, 0 ≤ v i) (a : α) (b : β) :
      0 ≤ t * F v a b := mul_nonneg ht (sumNn fun i _ ↦ mul_nonneg (hv i) (hK i _ _))
  have hsum (v : ι → ℝ) (b : β) : (∑ a, F v a b) = G v b := by
    rw [Finset.sum_comm]; simp_rw [← mulS, G]
  have hrew (p : α → β → ℝ) (q : β → ℝ) (hp : ∀ a b, 0 ≤ p a b) (hq : ∀ b, ∑ a, p a b = q b) :
      (∑ a, ∑ b, nml (p a b)) - ∑ b, nml (q b) = -(∑ a, ∑ b, p a b * rL (p a b / q b)) := by
    have h1 (a : α) (b : β) : p a b * rL (p a b / q b) = -nml (p a b) - p a b * rL (q b) := by
      rcases (hp a b).eq_or_lt with h0 | hpos; · simp [← h0]
      · have hqb := lt_of_lt_of_le hpos (hq b ▸ Finset.single_le_sum (fun a' _ ↦ hp a' b) (memU a))
        rw [Real.log_div hpos.ne' hqb.ne', Real.negMulLog]; ring
    simp_rw [h1, sumSub, Finset.sum_neg_distrib, Finset.sum_comm (f := fun a b ↦ p a b * rL (q b))]
    have h2 : ∑ b, ∑ a, p a b * rL (q b) = -∑ b, nml (q b) := by
      rw [← Finset.sum_neg_distrib]; exact sumC b ↦ by rw [← sumM, hq b, Real.negMulLog]; ring
    rw [h2]; ring
  have hsc (t : ℝ) (ht : 0 ≤ t) (p : α → β → ℝ) (q : β → ℝ) :
      ∑ a, ∑ b, (t * p a b) * rL ((t * p a b) / (t * q b)) =
        t * ∑ a, ∑ b, p a b * rL (p a b / q b) := by
    rcases ht.eq_or_lt with rfl | htp; · simp
    · simp_rw [mul_div_mul_left _ _ htp.ne', mul_assoc, ← mulS]
  have hF a b : (∑ i : ι, (t₁ * v₁ i + t₂ * v₂ i) * K i a b) = t₁ * F v₁ a b + t₂ * F v₂ a b := by
    simp_rw [F, add_mul, sumA, mul_assoc, ← mulS]
  have hG b : (∑ i : ι, (t₁ * v₁ i + t₂ * v₂ i) * ∑ a : α, K i a b) = t₁ * G v₁ b + t₂ * G v₂ b :=
    by simp_rw [G, add_mul, sumA, mul_assoc, ← mulS]
  simp_rw [hF, hG]
  rw [hrew _ _ (fun a b ↦ add_nonneg (hp_nn ht₁ hv₁.1 a b) (hp_nn ht₂ hv₂.1 a b)) (fun b ↦ by
      simp_rw [sumA, ← mulS, hsum]),
    hrew (F v₁) (G v₁) (fun a b ↦ (hp_nn zero_le_one hv₁.1 a b).trans_eq (one_mul _)) (hsum v₁),
    hrew (F v₂) (G v₂) (fun a b ↦ (hp_nn zero_le_one hv₂.1 a b).trans_eq (one_mul _)) (hsum v₂)]
  have hs1 := hsc t₁ ht₁ (F v₁) (G v₁); have hs2 := hsc t₂ ht₂ (F v₂) (G v₂)
  have hle : ∑ a : α, ∑ b : β, (t₁ * F v₁ a b + t₂ * F v₂ a b) *
      rL ((t₁ * F v₁ a b + t₂ * F v₂ a b) / (t₁ * G v₁ b + t₂ * G v₂ b)) ≤
      (∑ a : α, ∑ b : β, (t₁ * F v₁ a b) * rL ((t₁ * F v₁ a b) / (t₁ * G v₁ b))) +
        ∑ a : α, ∑ b : β, (t₂ * F v₂ a b) * rL ((t₂ * F v₂ a b) / (t₂ * G v₂ b)) := by
    rw [← sumA]; refine sumLe fun a _ ↦ ?_; rw [← sumA]; refine sumLe fun b _ ↦ ?_
    have hp1 := hp_nn ht₁ hv₁.1 a b; have hp2 := hp_nn ht₂ hv₂.1 a b
    have hg1 : t₁ * F v₁ a b ≤ t₁ * G v₁ b := by
      rw [← hsum v₁]; exact mLeL (Finset.single_le_sum (fun a' _ ↦
        (hp_nn zero_le_one hv₁.1 a' b).trans_eq (one_mul _)) (memU a)) ht₁
    have hg2 : t₂ * F v₂ a b ≤ t₂ * G v₂ b := by
      rw [← hsum v₂]; exact mLeL (Finset.single_le_sum (fun a' _ ↦
        (hp_nn zero_le_one hv₂.1 a' b).trans_eq (one_mul _)) (memU a)) ht₂
    rcases (hp1.trans hg1).eq_or_lt with h1z | h1p
    · rw [le_antisymm (hg1.trans_eq h1z.symm) hp1, ← h1z]; simp
    · rcases (hp2.trans hg2).eq_or_lt with h2z | h2p
      · rw [le_antisymm (hg2.trans_eq h2z.symm) hp2, ← h2z]; simp
      · set a₁ := t₁ * F v₁ a b; set a₂ := t₂ * F v₂ a b
        set b₁ := t₁ * G v₁ b; set b₂ := t₂ * G v₂ b; have hB : 0 < b₁ + b₂ := add_pos h1p h2p
        have hconv := Real.convexOn_mul_log.2 (show 0 ≤ a₁ / b₁ by positivity)
          (show 0 ≤ a₂ / b₂ by positivity) (show 0 ≤ b₁ / (b₁ + b₂) by positivity)
          (show 0 ≤ b₂ / (b₁ + b₂) by positivity) (by field_simp [hB.ne'])
        simp only [smul_eq_mul] at hconv
        rw [show b₁ / (b₁ + b₂) * (a₁ / b₁) + b₂ / (b₁ + b₂) * (a₂ / b₂) = (a₁ + a₂) / (b₁ + b₂)
          by field_simp [h1p.ne', h2p.ne', hB.ne']] at hconv
        have hmul := mul_le_mul_of_nonneg_left hconv hB.le
        rw [show (b₁ + b₂) * ((a₁ + a₂) / (b₁ + b₂) * rL ((a₁ + a₂) / (b₁ + b₂))) =
            (a₁ + a₂) * rL ((a₁ + a₂) / (b₁ + b₂)) by field_simp [hB.ne'],
          show (b₁ + b₂) * (b₁ / (b₁ + b₂) * (a₁ / b₁ * rL (a₁ / b₁)) +
            b₂ / (b₁ + b₂) * (a₂ / b₂ * rL (a₂ / b₂))) = a₁ * rL (a₁ / b₁) + a₂ * rL (a₂ / b₂)
            by field_simp [h1p.ne', h2p.ne', hB.ne']] at hmul
        exact hmul
  linarith

private def kerCoord {C : Type*} (P : RandomizedProtocol X Y Z) (coord : X × Y → C)
    (xy : X × Y) (tr : P.Transcript) (cm₀ : C × P.Pub) : ℝ :=
  @ite ℝ (coord xy = cm₀.1) (cpd) (P.execPMF xy.1 xy.2 (cm₀.2, tr)).toReal 0
private def icVec [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z) (v : X × Y → ℝ) : ℝ :=
  (rL2)⁻¹ * (((∑ tr, ∑ ym₀, nml (∑ xy, v xy * kerCoord P Prod.snd xy tr ym₀)) -
      ∑ ym₀, nml (∑ xy, v xy * ∑ tr, kerCoord P Prod.snd xy tr ym₀)) +
    ((∑ tr, ∑ xm₀, nml (∑ xy, v xy * kerCoord P Prod.fst xy tr xm₀)) -
      ∑ xm₀, nml (∑ xy, v xy * ∑ tr, kerCoord P Prod.fst xy tr xm₀)) -
    2 * ∑ xy, v xy * (pmfH (P.execPMF xy.1 xy.2) - pmfH P.pubCoin))

private lemma ent_joint_coord [Fintype X] [Fintype Y] {C : Type*} [Fintype C]
    (P : RandomizedProtocol X Y Z) {v : X × Y → ℝ} (hv : v ∈ simplexSet (X × Y))
    (coord : X × Y → C) : let μ := pmfSimp hv
    pmfH ((P.jointPMF μ).map fun w ↦ (w.2.2.2, coord (w.1, w.2.1), w.2.2.1)) =
      ∑ tr : P.Transcript, ∑ cm₀ : C × P.Pub,
        nml (∑ xy : X × Y, v xy * kerCoord P coord xy tr cm₀) ∧
    pmfH ((P.jointPMF μ).map fun w ↦ (coord (w.1, w.2.1), w.2.2.1)) =
      ∑ cm₀ : C × P.Pub, nml (∑ xy : X × Y, v xy * ∑ tr : P.Transcript,
        kerCoord P coord xy tr cm₀) := by
  classical intro μ; have hμ xy : (μ xy).toReal = v xy := by simp [μ, pmfSimp, eTRO (hv.1 xy)]
  have hmass tr c m₀ : ((P.jointPMF μ).map (fun w ↦ (w.2.2.2, coord (w.1, w.2.1), w.2.2.1))
      (tr, c, m₀)).toReal = ∑ xy : X × Y, v xy * kerCoord P coord xy tr (c, m₀) := by
    rw [pMapS, eTRS fun _ _ ↦ by split_ifs <;> [exact PMF.apply_ne_top _ _;
      exact ENNReal.zero_ne_top], fSP]
    simp_rw [fSP]; refine sumC x ↦ sumC y ↦ ?_; rw [sum1 m₀ _ sglU, sum1 tr _ sglU]
    · by_cases hc : coord (x, y) = c
      · simp [hc, kerCoord, jointPMF_apply, eTRM, hμ]
      · simp [hc, kerCoord, Prod.mk.injEq, Ne.symm hc, Ne.symm]
    · exact fun _ _ hne ↦ by simp [show (tr, c, m₀) ≠ _ from fun h ↦ hne (pmi h).1.symm]
    · exact fun _ _ hne ↦ sum0 tr' ↦ by simp [hne.symm]
  refine ⟨by rw [pmfHD, fSP]; exact sumC tr ↦ sumC cm₀ ↦ congrArg nml (hmass tr cm₀.1 cm₀.2), ?_⟩
  rw [pmfHD]; refine sumC cm₀ ↦ congrArg nml ?_
  have hproj : ((P.jointPMF μ).map fun w ↦ (coord (w.1, w.2.1), w.2.2.1)) (cm₀.1, cm₀.2) =
      ∑ tr, ((P.jointPMF μ).map fun w ↦ (w.2.2.2, coord (w.1, w.2.1), w.2.2.1))
        (tr, cm₀.1, cm₀.2) := by
    rw [show ((P.jointPMF μ).map fun w ↦ (coord (w.1, w.2.1), w.2.2.1)) =
        ((P.jointPMF μ).map fun w ↦ (w.2.2.2, coord (w.1, w.2.1), w.2.2.1)).map Prod.snd by
          rw [pMapC]; rfl, pMapS, fSP]
    refine sumC tr ↦ ?_; rw [fSP, sum1 cm₀.1 _ sglU, sum1 cm₀.2 _ sglU]
    · simp
    · exact fun _ _ hm ↦ iteR fun h ↦ hm (pmi h).2.symm
    · exact fun _ _ hc ↦ sum0 m' ↦ iteR fun h ↦ hc (pmi h).1.symm
  rw [hproj, eTRS fun _ _ ↦ PMF.apply_ne_top _ _]; simp_rw [hmass]
  rw [Finset.sum_comm]; simp_rw [mulS]

private lemma icVec_eq [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z) {v : X × Y → ℝ}
    (hv : v ∈ simplexSet (X × Y)) : icVec P v = P.internalInfoCost (pmfSimp hv) := by
  set μ := pmfSimp hv; have hY := ent_joint_coord P hv Prod.snd
  have hX := ent_joint_coord P hv Prod.fst; have h5 := joint_condEnt_exec P μ
  simp_rw [show ∀ xy, (μ xy).toReal = v xy from fun xy ↦ by simp [μ, pmfSimp, eTRO (hv.1 xy)]] at h5
  rw [icVec, ic_eq_raw, rIC, hY.1, hY.2, hX.1, hX.2]; congr 1; linarith

private lemma concaveOn_icVec [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z) :
    ConcaveOn ℝ (simplexSet (X × Y)) (icVec P) := by
  have hA := (negMulLog_sub_concave (kerCoord P Prod.snd) fun _ _ _ ↦ by
    dsimp only [kerCoord]; split_ifs <;> positivity).2
  have hB := (negMulLog_sub_concave (kerCoord P Prod.fst) fun _ _ _ ↦ by
    dsimp only [kerCoord]; split_ifs <;> positivity).2
  refine ⟨simplex_conv _, fun u hu v hv a b ha hb hab ↦ ?_⟩
  have hA2 := hA hu hv ha hb hab; have hB2 := hB hu hv ha hb hab
  simp only [icVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hA2 hB2 ⊢
  rw [mul_left_comm a, mul_left_comm b, ← mul_add,
    mul_le_mul_iff_right₀ (inv_pos.2 (Real.log_pos (by norm_num)))]
  have hL : (∑ xy : X × Y, (a * u xy + b * v xy) * (pmfH (P.execPMF xy.1 xy.2) - pmfH P.pubCoin)) =
      a * (∑ xy, u xy * (pmfH (P.execPMF xy.1 xy.2) - pmfH P.pubCoin)) +
      b * (∑ xy, v xy * (pmfH (P.execPMF xy.1 xy.2) - pmfH P.pubCoin)) := by
    simp_rw [add_mul, sumA, mul_assoc, ← mulS]
  rw [hL]; linarith

/-- **Braverman's Minimax Theorem**:
$\mathrm{IC}(f, \varepsilon / \alpha) \le \mathrm{IC}_D(f, \varepsilon) / (1 - \alpha)$.
-/
theorem infoComplexity_le_div_maxDistInfoComplexity [Fintype X] [Fintype Y] [Nonempty X]
    [Nonempty Y] (f : X × Y → Z) {ε α : ℝ} (hε : 0 < ε) (hα₀ : 0 < α) (hα₁ : α < 1) :
    infoComplexity f (ε / α) ≤ maxDistInfoComplexity f ε / (1 - α) := by
  classical have h1α : 0 < 1 - α := sub_pos.2 hα₁
  suffices hδ : ∀ δ > 0, infoComplexity f (ε / α) ≤ (maxDistInfoComplexity f ε + δ) / (1 - α) by
    refine le_of_forall_pos_le_add fun η hη ↦ ?_
    have h1 := hδ (η * (1 - α)) (mul_pos hη h1α)
    rwa [add_div, mul_div_cancel_right₀ _ h1α.ne'] at h1
  intro δ hδ; set I' := maxDistInfoComplexity f ε + δ
  have hI'_pos : 0 < I' := add_pos_of_nonneg_of_pos (maxDistInfoComplexity_nonneg f ε) hδ
  let Φ (P : RandomizedProtocol X Y Z) (v : X × Y → ℝ) : ℝ :=
    (α / ε) * (∑ xy, v xy * P.inputError f xy.1 xy.2) + ((1 - α) / I') * icVec P v
  have hΦ_cont (P : RandomizedProtocol X Y Z) : Continuous (Φ P) := by
    dsimp only [Φ, icVec]; fun_prop
  have hΦ_conc (P : RandomizedProtocol X Y Z) : ConcaveOn ℝ (simplexSet (X × Y)) (Φ P) :=
    ((simplex_linear_conc fun xy ↦ (α / ε) * P.inputError f xy.1 xy.2).congr fun v _ ↦
        by simp [mulS, mul_left_comm]).add
      ((concaveOn_icVec P).smul (div_nonneg h1α.le hI'_pos.le))
  have hcov v (hv : v ∈ simplexSet (X × Y)) : ∃ P : RandomizedProtocol X Y Z, Φ P v < 1 := by
    set μ := pmfSimp hv
    have hlt : distInfoComplexity f μ ε < I' :=
        (distInfoComplexity_le_maxDistInfoComplexity f μ hε.le).trans_lt (by linarith)
    rw [distInfoComplexity_def] at hlt
    have hne : ({c : ℝ | ∃ P : RandomizedProtocol X Y Z,
        P.distError f μ ≤ ε ∧ P.internalInfoCost μ = c}).Nonempty :=
      ⟨_, inRev f, by rw [distErr_rev]; exact hε.le, rfl⟩
    obtain ⟨_, ⟨P, herr, rfl⟩, hc⟩ := exists_lt_of_csInf_lt hne hlt
    refine ⟨P, ?_⟩
    have hd : ∑ xy, v xy * P.inputError f xy.1 xy.2 = P.distError f μ := by
      rw [distError_def]; exact sumC xy ↦ by simp [μ, pmfSimp, eTRO (hv.1 xy)]
    have h1 : (α / ε) * P.distError f μ ≤ α := by rw [div_mul_eq_mul_div, div_le_iff₀ hε]; nlinarith
    have h2 : ((1 - α) / I') * P.internalInfoCost μ < 1 - α := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hI'_pos]; nlinarith
    rw [show Φ P v = (α / ε) * P.distError f μ +
        ((1 - α) / I') * P.internalInfoCost μ by dsimp only [Φ]; rw [hd, icVec_eq P hv]]; linarith
  obtain ⟨S, hS⟩ := (simplex_cpt (X × Y)).elim_finite_subcover (fun P ↦ {v | Φ P v < 1})
    (fun P ↦ isOpen_lt (hΦ_cont P) continuous_const) fun v hv ↦ Set.mem_iUnion.2 (hcov v hv)
  have hSne : S.Nonempty := by
    obtain ⟨_, hv₀⟩ := simplex_ne (ι := X × Y)
    obtain ⟨P, hP, _⟩ := Set.mem_iUnion₂.1 (hS hv₀); exact ⟨P, hP⟩
  let N := S.card; have _ : NeZero N := ⟨Finset.card_ne_zero.2 hSne⟩
  let eS : Fin N ≃ {P // P ∈ S} :=
      (fC (Fintype.card_coe S).symm).trans (Fintype.equivFin {P // P ∈ S}).symm
  let Ps (j : Fin N) := (eS j).1
  let L (v : X × Y → ℝ) (w : Fin N → ℝ) : ℝ := -∑ j : Fin N, w j * Φ (Ps j) v
  obtain ⟨v₀, hv₀, w, hw, hsp⟩ := Sion.exists_isSaddlePointOn
    (X := simplexSet (X × Y)) (Y := simplexSet (Fin N)) (f := L)
    simplex_ne (simplex_conv _) (simplex_cpt _)
    (fun w _ ↦ (by have := hΦ_cont; fun_prop :
      Continuous fun v : X × Y → ℝ ↦ L v w).continuousOn.lowerSemicontinuousOn)
    (fun w hw ↦ by
      have hconv : ConvexOn ℝ (simplexSet (X × Y)) (fun v ↦ L v w) :=
        (ConcaveOn.neg ⟨simplex_conv _, fun u hu v hv a b ha hb hab ↦ by
          simp only [smul_eq_mul, mulS]; rw [← sumA]
          exact sumLe fun j _ ↦ by
            have hle := (hΦ_conc (Ps j)).2 hu hv ha hb hab
            simp only [smul_eq_mul] at hle; nlinarith [hw.1 j]⟩)
      exact hconv.quasiconvexOn)
    (simplex_conv _) simplex_ne (simplex_cpt _)
    (fun v _ ↦ (by fun_prop :
      Continuous fun w : Fin N → ℝ ↦ L v w).continuousOn.upperSemicontinuousOn)
    (fun v _ ↦ ((simplex_linear_conc fun j ↦ -Φ (Ps j) v).congr fun w _ ↦ by
      simp [Finset.sum_neg_distrib]; rfl).quasiconcaveOn)
  have hLw : ∀ v ∈ simplexSet (X × Y), -1 ≤ L v w := fun v hv ↦ by
    obtain ⟨P, hPS, hPv⟩ := Set.mem_iUnion₂.1 (hS hv₀)
    let j₀ : Fin N := eS.symm ⟨P, hPS⟩
    have hj₀ : (fun j : Fin N ↦ if j = j₀ then (1 : ℝ) else 0) ∈ simplexSet (Fin N) :=
      ⟨fun j ↦ by by_cases h : j = j₀ <;> simp [h], by simp⟩
    have h1 : (-1 : ℝ) ≤ L v₀ (fun j ↦ if j = j₀ then 1 else 0) := by
      change Φ P v₀ < 1 at hPv; dsimp only [L]; simp [show Ps j₀ = P by simp [Ps, j₀]]; linarith
    exact h1.trans (hsp v hv _ hj₀)
  let Q := mux w hw.1 hw.2 Ps
  have hQ_bound (μ : PMF (X × Y)) : (α / ε) * Q.distError f μ +
      ((1 - α) / I') * Q.internalInfoCost μ ≤ 1 := by
    let v xy := (μ xy).toReal; have hv : v ∈ simplexSet (X × Y) := ⟨fun _ ↦ eTRN, pSum1R μ⟩
    have hμeq : pmfSimp hv = μ := PMF.ext fun xy ↦ by simp [pmfSimp, v,
        ENNReal.ofReal_toReal (μ.apply_ne_top xy)]
    have hle := hLw v hv
    have hd : ∑ j, w j * ∑ xy, v xy * (Ps j).inputError f xy.1 xy.2 = Q.distError f μ := by
      rw [distError_def]; simp_rw [Q, inputError_mux, mulS]
      rw [Finset.sum_comm]; exact sumC j ↦ sumC xy ↦ by ring
    have hi : ∑ j, w j * icVec (Ps j) v = Q.internalInfoCost μ := by
      rw [internalInfoCost_mux w hw.1 hw.2 Ps μ]; exact sumC j ↦ by rw [icVec_eq (Ps j) hv, hμeq]
    have hLval : L v w = -((α / ε) * Q.distError f μ + ((1 - α) / I') * Q.internalInfoCost μ) := by
      dsimp only [L, Φ]; simp_rw [mul_add, sumA, ← mul_assoc, mul_comm (w _), mul_assoc, ← mulS]
      rw [hd, hi]
    linarith
  refine (infoComplexity_le_of_inputError_le fun x y ↦ ?_).trans (worstCaseInfoCost_le Q fun μ ↦ ?_)
  · have h := hQ_bound (PMF.pure (x, y)); rw [Q.distError_pure, Q.internalInfoCost_pure, mul_zero,
      add_zero, div_mul_eq_mul_div, div_le_iff₀ hε] at h; rw [le_div_iff₀ hα₀]; linarith
  · have h := hQ_bound μ; have hnn := mul_nonneg (div_nonneg hα₀.le hε.le) (Q.distError_nonneg f μ)
    rw [le_div_iff₀ h1α]; have h2 : ((1 - α) / I') * Q.internalInfoCost μ ≤ 1 := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hI'_pos] at h2; linarith
end Minimax

/-! ### Majority-Vote Boosting, Zero-Cost Threshold, and Binary XOR Fano Bounds -/
section BoostingAndLowerBounds
open RandomizedProtocol
variable {X : Type u} {Y : Type v} {Z : Type w}
private def padR (r : ℕ) : ℕ := if Even r then max 2 r else r + 1
private lemma padR_pos (r : ℕ) : 0 < padR r := by dsimp only [padR]; split_ifs <;> omega
private lemma le_padR (r : ℕ) : r ≤ padR r := by dsimp only [padR]; split_ifs <;> omega
private lemma even_mod_padR (r m : ℕ) : Even (m % padR r) ↔ Even m := by
  have he : Even (padR r) := by
    dsimp only [padR]; split_ifs with h
    · rcases le_total 2 r with hr | hr; · simpa [max_eq_right hr] using h
      · rw [max_eq_left hr]; exact ⟨1, rfl⟩
    · obtain ⟨m', _⟩ := Nat.not_even_iff_odd.1 h; exact ⟨m' + 1, by omega⟩
  conv_rhs => rw [← Nat.div_add_mod m (padR r), Nat.mul_comm (padR r), Nat.even_add,
      iff_true_left (he.mul_left _)]
private lemma rep_lt {r k : ℕ} (i : Fin (2 * k + 1)) {s : ℕ} (hs : s < padR r) :
    i.1 * padR r + s < (2 * k + 1) * padR r :=
  (Nat.add_lt_add_left hs _).trans_le
    (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right (padR r) i.2)
private lemma rep_div {r : ℕ} (i s : ℕ) (hs : s < padR r) : (i * padR r + s) / padR r = i := by
  rw [Nat.mul_comm i, Nat.mul_add_div (padR_pos r), Nat.div_eq_of_lt hs, add_zero]
private lemma rep_mod {r : ℕ} (i s : ℕ) (hs : s < padR r) : (i * padR r + s) % padR r = s := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
private lemma rep_prev {r k : ℕ} (t : Fin ((2 * k + 1) * padR r)) {j : ℕ} (hj : j < t.1 % padR r) :
    (t.1 / padR r) * padR r + j < t.1 := by
  have := Nat.div_add_mod t.1 (padR r); rw [Nat.mul_comm] at this; linarith
private lemma rep_blk {r k : ℕ} (t : Fin ((2 * k + 1) * padR r)) : t.1 / padR r < 2 * k + 1 :=
  Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq t.2 (Nat.mul_comm _ _))
private def repIdx (r k : ℕ) : Fin (2 * k + 1) × Fin (padR r) ≃ Fin ((2 * k + 1) * padR r) :=
  ⟨fun p ↦ ⟨p.1.1 * padR r + p.2.1, rep_lt p.1 p.2.2⟩,
   fun t ↦ (⟨t.1 / padR r, rep_blk t⟩, ⟨t.1 % padR r, Nat.mod_lt _ (padR_pos r)⟩),
   fun ⟨i, s⟩ ↦ Prod.ext (Fin.ext (rep_div i.1 s.1 s.2)) (Fin.ext (rep_mod i.1 s.1 s.2)),
   fun t ↦ Fin.ext (by have := Nat.div_add_mod t.1 (padR r); rw [Nat.mul_comm] at this; exact this)⟩
private abbrev repΩ (P : RandomizedProtocol X Y Z) (k : ℕ) (t : Fin ((2 * k +
    1) * padR P.rounds)) :=
  Fin ((if hs : t.1 % padR P.rounds < P.rounds then P.msgCard ⟨t.1 % padR P.rounds, hs⟩ else 0) + 1)
private lemma rep_mc_eq (P : RandomizedProtocol X Y Z) {m : ℕ} {s : Fin P.rounds}
    (hmod : m % padR P.rounds = s.1) :
    (if hs : m % padR P.rounds < P.rounds then P.msgCard ⟨m % padR P.rounds, hs⟩ else 0) + 1 =
      P.msgCard s + 1 := by
  split_ifs with hs; exacts [congrArg (· + 1) (congrArg P.msgCard (Fin.ext hmod)),
    absurd (hmod.symm ▸ s.2) hs]
private def repSide (P : RandomizedProtocol X Y Z) (k : ℕ)
    (fn : ∀ t : Fin P.rounds, P.Pub → (∀ j : Fin t.1, P.Msg ⟨j.1, j.2.trans t.2⟩) → PMF (P.Msg t))
    (t : Fin ((2 * k + 1) * padR P.rounds)) (r₀ : Fin (2 * k + 1) → P.Pub)
    (h : ∀ j : Fin t.1, repΩ P k ⟨j.1, j.2.trans t.2⟩) : PMF (repΩ P k t) :=
  let i : Fin (2 * k + 1) := ⟨t.1 / padR P.rounds, rep_blk t⟩
  if hs : t.1 % padR P.rounds < P.rounds then
    (fn ⟨t.1 % padR P.rounds, hs⟩ (r₀ i) fun j ↦
      fC (rep_mc_eq P (rep_mod i.1 j.1 ((j.2.trans hs).trans_le (le_padR P.rounds))))
        (h ⟨i.1 * padR P.rounds + j.1, rep_prev t j.2⟩)).map
      (fC (rep_mc_eq P (s := ⟨_, hs⟩) rfl).symm)
  else PMF.pure 0
private def repExtr (P : RandomizedProtocol X Y Z) (k : ℕ)
    (tr : ∀ t : Fin ((2 * k + 1) * padR P.rounds), repΩ P k t) (i : Fin (2 * k + 1)) :
    P.Transcript := fun s ↦
  fC (rep_mc_eq P (rep_mod i.1 s.1 (s.2.trans_le (le_padR P.rounds))))
    (tr ⟨i.1 * padR P.rounds + s.1, rep_lt i (s.2.trans_le (le_padR P.rounds))⟩)
private def repEmb (P : RandomizedProtocol X Y Z) (k : ℕ) (trs : Fin (2 * k + 1) → P.Transcript) :
    ∀ t : Fin ((2 * k + 1) * padR P.rounds), repΩ P k t := fun t ↦
  let i : Fin (2 * k + 1) := ⟨t.1 / padR P.rounds, rep_blk t⟩
  if hs : t.1 % padR P.rounds < P.rounds then
    fC (rep_mc_eq P (s := ⟨_, hs⟩) rfl).symm (trs i ⟨t.1 % padR P.rounds, hs⟩) else 0
private lemma repEmb_val (P : RandomizedProtocol X Y Z) (k : ℕ)
    (trs : Fin (2 * k + 1) → P.Transcript) (i : Fin (2 * k + 1)) (s : Fin P.rounds) :
    (repEmb P k trs ⟨i.1 * padR P.rounds + s.1,
      rep_lt i (s.2.trans_le (le_padR P.rounds))⟩).1 = (trs i s).1 := by
  have hsR := s.2.trans_le (le_padR P.rounds); have hm := rep_mod i.1 s.1 hsR
  dsimp only [repEmb]; split_ifs with h
  · have hi : (⟨(i.1 * padR P.rounds + s.1) / padR P.rounds, rep_blk ⟨i.1 * padR P.rounds + s.1,
      rep_lt i hsR⟩⟩ : Fin (2 * k + 1)) = i := Fin.ext (rep_div i.1 s.1 hsR)
    simp only [finCongr_apply, Fin.val_cast, hi]
    rw [show (⟨_, h⟩ : Fin P.rounds) = s from Fin.ext hm]
  · exact absurd (hm.symm ▸ s.2) h
private lemma repExtr_repEmb (P : RandomizedProtocol X Y Z) (k : ℕ)
    (trs : Fin (2 * k + 1) → P.Transcript) : repExtr P k (repEmb P k trs) = trs :=
  funext fun _ ↦ funext fun _ ↦ Fin.ext (by simp [repExtr, repEmb_val])
private lemma repEmb_inj (P : RandomizedProtocol X Y Z) (k : ℕ) : fInj (repEmb P k) :=
  iInv (repEmb P k) (repExtr P k) (repExtr_repEmb P k)
private def repPub (P : RandomizedProtocol X Y Z) (k : ℕ) : PMF (Fin (2 * k + 1) → P.Pub) :=
  PMF.ofFintype (fun r₀ : Fin (2 * k + 1) → P.Pub ↦ ∏ i, P.pubCoin (r₀ i))
    (by rw [← prodS]; exact Finset.prod_eq_one fun _ _ ↦ pSum1 _)
private def repOut (P : RandomizedProtocol X Y Bool) (k : ℕ) (r₀ : Fin (2 * k + 1) → P.Pub)
    (tr : ∀ t : Fin ((2 * k + 1) * padR P.rounds), repΩ P k t) : Bool :=
  decide (k + 1 ≤ Finset.card (uFilt fun i : Fin (2 * k + 1) ↦
    P.out (r₀ i) (repExtr P k tr i) = true))

/-- Odd-repetition majority-vote protocol executing `2 * k + 1` independent copies of `P`. -/
def RandomizedProtocol.repeatMajority (P : RandomizedProtocol X Y Bool) (k : ℕ) :
    RandomizedProtocol X Y Bool :=
  let _ : Nonempty (Fin (2 * k + 1) → P.Pub) := ⟨fun _ ↦ 0⟩
  ofFintype (R₀ := Fin (2 * k + 1) → P.Pub) (r := (2 * k + 1) * padR P.rounds) (Ω := repΩ P k)
    (repPub P k) (fun t x ↦ repSide P k (fun s r h ↦ P.aliceStep s x r h) t)
    (fun t y ↦ repSide P k (fun s r h ↦ P.bobStep s y r h) t) (repOut P k)

private lemma stepPMF_cast_eq (P : RandomizedProtocol X Y Z) (x : X) (y : Y) (m₀ m₁ : P.Pub)
    {s' s : Fin P.rounds} (hm : m₀ = m₁) (hs : s' = s)
    {h₁ : ∀ j : Fin s'.1, P.Msg ⟨j.1, j.2.trans s'.2⟩}
    {h₂ : ∀ j : Fin s.1, P.Msg ⟨j.1, j.2.trans s.2⟩} {a₁ : P.Msg s'} {a₂ : P.Msg s}
    (hh : ∀ j : Fin s'.1, (h₁ j).1 = (h₂ ⟨j.1, hs ▸ j.2⟩).1) (ha : a₁.1 = a₂.1) :
    P.stepPMF x y m₀ s' h₁ a₁ = P.stepPMF x y m₁ s h₂ a₂ := by
  subst hm hs; rw [show h₁ = h₂ from funext fun j ↦ Fin.ext (hh j), Fin.ext ha]

private lemma rep_prod_eq (P : RandomizedProtocol X Y Z) (k : ℕ) (x : X) (y : Y)
    (r₀ : Fin (2 * k + 1) → P.Pub) (tr : ∀ t : Fin ((2 * k + 1) * padR P.rounds), repΩ P k t) :
    (∏ i : Fin (2 * k + 1), P.pubCoin (r₀ i)) * (∏ t : Fin ((2 * k + 1) * padR P.rounds),
      if Even t.1 then repSide P k (fun s r h ↦ P.aliceStep s x r h) t r₀
        (fun j ↦ tr ⟨j.1, j.2.trans t.2⟩) (tr t)
      else repSide P k (fun s r h ↦ P.bobStep s y r h) t r₀
        (fun j ↦ tr ⟨j.1, j.2.trans t.2⟩) (tr t)) =
      @dite r0inf (∃ trs : Fin (2 * k + 1) → P.Transcript, tr = repEmb P k trs)
        (cpd) (fun h ↦ ∏ i, P.execPMF x y (r₀ i, h.choose i)) (fun _ ↦ 0) := by
  classical
  let term (t : Fin ((2 * k + 1) * padR P.rounds)) : r0inf :=
    let i : Fin (2 * k + 1) := ⟨t.1 / padR P.rounds, rep_blk t⟩
    if hs : t.1 % padR P.rounds < P.rounds then P.stepPMF x y (r₀ i) ⟨t.1 % padR P.rounds, hs⟩
      (fun j ↦ fC (rep_mc_eq P (rep_mod i.1 j.1 ((j.2.trans hs).trans_le (le_padR P.rounds))))
        (tr ⟨i.1 * padR P.rounds + j.1, (rep_prev t j.2).trans t.2⟩))
      (fC (rep_mc_eq P (s := ⟨_, hs⟩) rfl) (tr t))
    else if tr t = 0 then 1 else 0
  have hprod : (∏ t, if Even t.1 then repSide P k (fun s r h ↦ P.aliceStep s x r h) t r₀
      (fun j ↦ tr ⟨j.1, j.2.trans t.2⟩) (tr t)
      else repSide P k (fun s r h ↦ P.bobStep s y r h) t r₀
        (fun j ↦ tr ⟨j.1, j.2.trans t.2⟩) (tr t)) = ∏ t, term t := prodC t ↦ by
    dsimp only [term, repSide]
    by_cases he : Even t.1 <;> by_cases hs : t.1 % padR P.rounds < P.rounds
    · simp only [he, hs, ↓reduceIte, ↓reduceDIte, pMapE, P.stepPMF_of_even x y _ (t := ⟨_, hs⟩)
        ((even_mod_padR P.rounds t.1).2 he)]; congr 2
    · simp only [he, hs, ↓reduceIte, ↓reduceDIte, pPureA]; by_cases h0 : tr t = 0 <;> simp [h0]
    · simp only [he, hs, ↓reduceIte, ↓reduceDIte, pMapE, P.stepPMF_of_not_even x y _ (t := ⟨_, hs⟩)
        (mt (even_mod_padR P.rounds t.1).1 he)]; congr 2
    · simp only [he, hs, ↓reduceIte, ↓reduceDIte, pPureA]; by_cases h0 : tr t = 0 <;> simp [h0]
  rw [hprod]; split_ifs with h
  · have hsplit : (∏ t, term t) = ∏ i : Fin (2 * k + 1), ∏ s : Fin P.rounds,
        P.stepPMF x y (r₀ i) s (fun j ↦ h.choose i ⟨j.1, j.2.trans s.2⟩) (h.choose i s) := by
      rw [← (repIdx P.rounds k).prod_comp, Fintype.prod_prod_type]; refine prodC i ↦ ?_
      rw [prodImg1 (Fin.castLE (le_padR P.rounds)) (fun _ _ e ↦ Fin.ext (Fin.mk.inj e))
        (fun s ↦ term (repIdx P.rounds k (i, s)))]
      · refine prodC s ↦ ?_
        have hsR := s.2.trans_le (le_padR P.rounds)
        have hd := rep_div i.1 s.1 hsR; have hm := rep_mod i.1 s.1 hsR
        dsimp only [term, repIdx, Equiv.coe_fn_mk, Fin.val_castLE]; rw [diteL (hm.symm ▸ s.2)]
        have hv (u : Fin P.rounds) : (tr ⟨i.1 * padR P.rounds + u.1,
            rep_lt i (u.2.trans_le (le_padR P.rounds))⟩).1 = (h.choose i u).1 := by
          rw [congrFun h.choose_spec _]; exact repEmb_val P k h.choose i u
        refine stepPMF_cast_eq P x y _ _ (congrArg r₀ (Fin.ext hd)) (Fin.ext hm)
          (fun j ↦ ?_) (by simp [hv s])
        have htv {a b : Fin ((2 * k + 1) * padR P.rounds)} (e : a.1 = b.1) : (tr a).1 = (tr b).1 :=
          by cases Fin.ext e; rfl
        simp only [finCongr_apply, Fin.val_cast]
        have hidx : (⟨(i.1 * padR P.rounds + s.1) / padR P.rounds * padR P.rounds + j.1,
            rep_lt ⟨(i.1 * padR P.rounds + s.1) / padR P.rounds, by rw [hd]; exact i.2⟩
              ((j.2.trans_eq hm).trans s.2 |>.trans_le (le_padR P.rounds))⟩ :
            Fin ((2 * k + 1) * padR P.rounds)) = ⟨i.1 * padR P.rounds + j.1, rep_lt i
              ((j.2.trans_eq hm).trans s.2 |>.trans_le (le_padR P.rounds))⟩ :=
          Fin.ext (by dsimp only; rw [hd])
        exact (htv (congrArg Fin.val hidx)).trans (hv ⟨j.1, (j.2.trans_eq hm).trans s.2⟩)
      · intro s hni; have hns : ¬ s.1 < P.rounds := fun hlt ↦ hni ⟨⟨s.1, hlt⟩, Fin.ext rfl⟩
        have hm := rep_mod i.1 s.1 s.2; have htr :=
          congrFun h.choose_spec (repIdx P.rounds k (i, s))
        dsimp only [repEmb, repIdx, Equiv.coe_fn_mk] at htr; rw [diteR (hm.symm ▸ hns)] at htr
        dsimp only [term, repIdx, Equiv.coe_fn_mk]; rw [diteR (hm.symm ▸ hns), iteL htr]
    rw [hsplit, ← Finset.prod_mul_distrib]
    exact prodC i ↦ (P.execPMF_apply x y (r₀ i, h.choose i)).symm
  · by_contra hne
    have hall : ∀ t, term t ≠ 0 :=
      fun t ht0 ↦ hne (by rw [Finset.prod_eq_zero (memU t) ht0, mul_zero])
    refine h ⟨repExtr P k tr, funext fun t ↦ ?_⟩; by_cases hs : t.1 % padR P.rounds < P.rounds
    · dsimp only [repEmb]; rw [diteL hs]
      have ht_eq : (⟨(t.1 / padR P.rounds) * padR P.rounds + t.1 % padR P.rounds, rep_lt
          ⟨t.1 / padR P.rounds, rep_blk t⟩ (hs.trans_le (le_padR P.rounds))⟩ :
          Fin ((2 * k + 1) * padR P.rounds)) = t :=
        Fin.ext (by have :=
          Nat.div_add_mod t.1 (padR P.rounds); rw [Nat.mul_comm] at this; exact this)
      have htv {a b : Fin ((2 * k + 1) * padR P.rounds)} (e : a = b) : (tr a).1 = (tr b).1 :=
        by cases e; rfl
      exact Fin.ext (by simp only [repExtr, finCongr_apply, Fin.val_cast]; exact htv ht_eq.symm)
    · dsimp only [repEmb]; rw [diteR hs]
      exact by_contra fun h0 ↦ hall t (by simp [term, hs, h0])

private lemma prod_bern_fail_tail {Ω : Type*} [Fintype Ω] (k : ℕ) (pμ : PMF Ω) (bad : Ω → Prop)
    [DecidablePred bad] {ε : ℝ} (hp : ∑ ω : Ω, (if bad ω then (pμ ω).toReal else 0) ≤ ε)
    (hε_half : ε ≤ 1 / 2) :
    (∑ ωs : Fin (2 * k + 1) → Ω, if k + 1 ≤ (uFilt fun i ↦ bad (ωs i)).card
      then (∏ i : Fin (2 * k + 1), pμ (ωs i)).toReal else 0) ≤ (4 * ε * (1 - ε)) ^ k := by
  let p := ∑ ω : Ω, if bad ω then (pμ ω).toReal else 0
  have hp0 : 0 ≤ p := sumNn fun _ _ ↦ by split_ifs <;> positivity
  have hp1 : ∑ ω : Ω, (if ¬ bad ω then (pμ ω).toReal else 0) = 1 - p := by
    rw [← pSum1R pμ, ← sumSub]; exact sumC ω ↦ by split_ifs <;> ring
  have hpp0 : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  rcases hp0.eq_or_lt with hp_eq | hp_pos
  · have hz ω (hb : bad ω) : pμ ω = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).1 (le_antisymm (((iteL hb).symm.le.trans
        (Finset.single_le_sum (f := fun x ↦ if bad x then (pμ x).toReal else 0)
          (fun _ _ ↦ by split_ifs <;> positivity) (memU ω))).trans_eq hp_eq.symm)
        eTRN)).resolve_right (pμ.apply_ne_top ω)
    rw [sum0 ωs ↦ ?_]; · exact pow_nonneg (by nlinarith) k
    split_ifs with hc; swap; · rfl
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (lt_of_lt_of_le (Nat.succ_pos k) hc)
    rw [Finset.prod_eq_zero (memU i) (hz _ (Finset.mem_filter.1 hi).2), ENNReal.toReal_zero]
  · let t := Real.sqrt ((1 - p) / p)
    have ht1 : 1 ≤ t := Real.one_le_sqrt.2 ((one_le_div hp_pos).2 (by linarith))
    have htp : 0 < t := lt_of_lt_of_le one_pos ht1
    have hterm (ωs : Fin (2 * k + 1) → Ω) :
        (if k + 1 ≤ (uFilt fun i ↦ bad (ωs i)).card then (∏ i, pμ (ωs i)).toReal else 0) ≤
          t⁻¹ * ∏ i : Fin (2 * k + 1), (pμ (ωs i)).toReal * (if bad (ωs i) then t else t⁻¹) := by
      rw [ENNReal.toReal_prod, Finset.prod_mul_distrib, mul_left_comm]
      split_ifs with hcard; swap; · positivity
      refine le_mul_of_one_le_right (Finset.prod_nonneg fun _ _ ↦ eTRN) ?_
      set S := uFilt fun i : Fin (2 * k + 1) ↦ bad (ωs i)
      have hS_le : S.card ≤ 2 * k + 1 := (Finset.card_le_univ _).trans_eq (cardF _)
      have hc2 : (uFilt fun i : Fin (2 * k + 1) ↦ ¬ bad (ωs i)).card = 2 * k + 1 - S.card := by
        have hc := Finset.univ.card_filter_add_card_filter_not (fun i : Fin (2 * k +
          1) ↦ bad (ωs i))
        rw [cardU, cardF] at hc; change S.card + _ = _ at hc; omega
      have hS_prod : (∏ i : Fin (2 * k + 1), if bad (ωs i) then t else t⁻¹) =
          t ^ S.card * (t⁻¹) ^ (2 * k + 1 - S.card) := by
        rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ fun i ↦ bad (ωs i),
          Finset.prod_congr rfl (fun i hi ↦ iteL (Finset.mem_filter.1 hi).2),
          Finset.prod_congr rfl (fun i hi ↦ iteR (Finset.mem_filter.1 hi).2),
          Finset.prod_const, Finset.prod_const, hc2]
      rw [hS_prod, show t ^ S.card = t ^ ((2 * k + 1 - S.card) + (2 * S.card - (2 * k + 1))) by
          congr 1; omega,
        pow_add, mul_right_comm, ← mul_pow, mul_inv_cancel₀ htp.ne', one_pow, one_mul]
      have hpg : t ≤ t ^ (2 * S.card - (2 * k + 1)) := by
        rw [← Nat.sub_add_cancel (by omega : 1 ≤ 2 * S.card - (2 * k + 1)), pow_succ']
        exact le_mul_of_one_le_right htp.le (one_le_pow₀ ht1)
      have hm := mLeL hpg (inv_nonneg.2 htp.le); rwa [inv_mul_cancel₀ htp.ne'] at hm
    refine (sumLe fun ωs _ ↦ hterm ωs).trans ?_
    rw [← mulS, ← prodS (f := fun (_ : Fin (2 * k + 1)) ω ↦
      (pμ ω).toReal * (if bad ω then t else t⁻¹))]
    have h1 : (∑ ω : Ω, (pμ ω).toReal * (if bad ω then t else t⁻¹)) = p * t + (1 - p) * t⁻¹ := by
      simp_rw [show ∀ ω, (pμ ω).toReal * (if bad ω then t else t⁻¹) =
        (if bad ω then (pμ ω).toReal else 0) * t + (if ¬ bad ω then (pμ ω).toReal else 0) * t⁻¹ from
        fun ω ↦ by by_cases h : bad ω <;> simp [h], sumA, ← sumM, hp1]; rfl
    have htm : p * t = Real.sqrt (p * (1 - p)) := by
      rw [← Real.sqrt_sq (mul_nonneg hp_pos.le htp.le), mul_pow,
        Real.sq_sqrt (div_nonneg (by linarith) hp_pos.le)]; congr 1; field_simp
    have hti : (1 - p) * t⁻¹ = Real.sqrt (p * (1 - p)) := by
      rw [inv_eq_one_div, mul_one_div, div_eq_iff htp.ne', ← Real.sqrt_mul hpp0,
        show p * (1 - p) * ((1 - p) / p) = (1 - p) ^ 2 by field_simp, Real.sqrt_sq (by linarith)]
    rw [Finset.prod_const, cardU, cardF, h1, htm, hti, ← two_mul, pow_add, pow_one, mul_pow,
      show (2 : ℝ) ^ (2 * k) = (4 : ℝ) ^ k by rw [pow_mul]; norm_num,
      show Real.sqrt (p * (1 - p)) ^ (2 * k) = (p * (1 - p)) ^ k by rw [pow_mul, Real.sq_sqrt hpp0]]
    have h2p : t⁻¹ * (2 * Real.sqrt (p * (1 - p))) = 2 * p := by
      rw [inv_eq_one_div, mul_comm, ← div_eq_mul_one_div, div_eq_iff htp.ne']; linarith
    calc t⁻¹ * ((4 : ℝ) ^ k * (p * (1 - p)) ^ k * (2 * Real.sqrt (p * (1 - p))))
        = (t⁻¹ * (2 * Real.sqrt (p * (1 - p)))) * (4 * p * (1 - p)) ^ k := by
          rw [mul_pow, mul_pow]; ring
      _ ≤ 1 * (4 * ε * (1 - ε)) ^ k := by
          rw [h2p]; exact mul_le_mul (by linarith)
            (pow_le_pow_left₀ (by nlinarith) (by nlinarith) k)
            (pow_nonneg (by nlinarith) k) (by norm_num)
      _ = (4 * ε * (1 - ε)) ^ k := one_mul _

/-- Per-input error of the `(2k + 1)`-copy majority protocol decays as `(4 * ε * (1 - ε)) ^ k`. -/
theorem RandomizedProtocol.inputError_repeatMajority_le (P : RandomizedProtocol X Y Bool) (k : ℕ)
    (g : X × Y → Bool) (x : X) (y : Y) {ε : ℝ} (hε : P.inputError g x y ≤ ε)
    (hε_half : ε ≤ 1 / 2) : (P.repeatMajority k).inputError g x y ≤ (4 * ε * (1 - ε)) ^ k := by
  classical rw [repeatMajority, inputError_ofFintype, fSP]
  have hsub r₀ : (∑ tr : ∀ t : Fin ((2 * k + 1) * padR P.rounds), repΩ P k t,
      @ite ℝ (repOut P k r₀ tr ≠ g (x, y)) (cpd) ((repPub P k r₀ * ∏ t,
        if Even t.1 then repSide P k (fun s r h ↦ P.aliceStep s x r h) t r₀
          (fun j ↦ tr ⟨j.1, j.2.trans t.2⟩) (tr t)
        else repSide P k (fun s r h ↦ P.bobStep s y r h) t r₀
          (fun j ↦ tr ⟨j.1, j.2.trans t.2⟩) (tr t)).toReal) 0) =
      ∑ trs : Fin (2 * k + 1) → P.Transcript, @ite ℝ (decide (k + 1 ≤
        (uFilt fun i : Fin (2 * k + 1) ↦ P.out (r₀ i) (trs i) = true).card) ≠ g (x, y)) (cpd)
        (∏ i : Fin (2 * k + 1), P.execPMF x y (r₀ i, trs i)).toReal 0 := by
    rw [sumImg0 (repEmb P k) (repEmb_inj P k)]
    · refine sumC trs ↦ ?_; have hex : ∃ trs', repEmb P k trs = repEmb P k trs' := ⟨trs, rfl⟩
      rw [repPub, pmfOF, rep_prod_eq, diteL hex, repEmb_inj P k hex.choose_spec.symm,
        show repOut P k r₀ (repEmb P k trs) = decide (k + 1 ≤ (uFilt fun i : Fin (2 * k + 1) ↦
          P.out (r₀ i) (trs i) = true).card) by simp [repOut, repExtr_repEmb]]
    · intro tr hne; rw [repPub, pmfOF, rep_prod_eq, diteR hne]; simp
  refine le_of_eq_of_le (sumC r₀ ↦ hsub r₀) ?_
  let ePi : (Fin (2 * k + 1) → P.Pub × P.Transcript) ≃
      (Fin (2 * k + 1) → P.Pub) × (Fin (2 * k + 1) → P.Transcript) :=
    ⟨fun f ↦ (fun i ↦ (f i).1, fun i ↦ (f i).2), fun p i ↦ (p.1 i, p.2 i),
      fun _ ↦ rfl, fun ⟨_, _⟩ ↦ rfl⟩
  rw [← Fintype.sum_prod_type', ← ePi.sum_comp]
  have hf_iff (mts : Fin (2 * k + 1) → P.Pub × P.Transcript) :
      (decide (k + 1 ≤ (uFilt fun i : Fin (2 * k + 1) ↦
        P.out (mts i).1 (mts i).2 = true).card) ≠ g (x, y)) ↔
      k + 1 ≤ (uFilt fun i ↦ P.out (mts i).1 (mts i).2 ≠ g (x, y)).card := by
    cases g (x, y); · simp
    · simp only [ne_eq, decide_eq_true_eq, not_le]
      have hs := Finset.univ.card_filter_add_card_filter_not
        (fun i : Fin (2 * k + 1) ↦ P.out (mts i).1 (mts i).2 = true)
      simp only [cardU, cardF] at hs; omega
  have hp : ∑ mt : P.Pub × P.Transcript,
      (if P.out mt.1 mt.2 ≠ g (x, y) then (P.execPMF x y mt).toReal else 0) ≤ ε := by
    rw [P.inputError_def] at hε
    exact (sumC mt ↦ by by_cases h : P.out mt.1 mt.2 ≠ g (x, y) <;> simp [h]).trans_le hε
  refine le_trans (le_of_eq (sumC mts ↦ ?_)) (prod_bern_fail_tail k (P.execPMF x y)
    (fun mt ↦ P.out mt.1 mt.2 ≠ g (x, y)) hp hε_half)
  dsimp only [ePi, Equiv.coe_fn_mk]
  by_cases hc : k + 1 ≤ (uFilt fun i ↦ P.out (mts i).1 (mts i).2 ≠ g (x, y)).card
  · rw [iteL ((hf_iff mts).2 hc), iteL hc]
  · rw [iteR (mt (hf_iff mts).1 hc), iteR hc]

private lemma subadd_cmi {W M T B : Type*} [Fintype W] [Fintype M] [Fintype T] [Fintype B]
    (n : ℕ) (μ : PMF W) (K : W → PMF (M × T)) (pM : PMF M)
    (hKM : ∀ w m, ∑ tr : T, K w (m, tr) = pM m) (fB : W → B)
    (q : PMF (W × (Fin n → M × T))) (q1 : PMF (W × M × T))
    (hq : ∀ u, q u = μ u.1 * ∏ i : Fin n, K u.1 (u.2 i)) (hq1 : ∀ w mt, q1 (w, mt) = μ w * K w mt) :
    (pmfH (q.map fun u ↦ (fun i ↦ (u.2 i).2, fB u.1, fun i ↦ (u.2 i).1)) -
     pmfH (q.map fun u ↦ (fB u.1, fun i ↦ (u.2 i).1)) -
     pmfH (q.map fun u ↦ (fun i ↦ (u.2 i).2, u.1, fun i ↦ (u.2 i).1)) +
     pmfH (q.map fun u ↦ (u.1, fun i ↦ (u.2 i).1))) ≤
    (n : ℝ) * (pmfH (q1.map fun u ↦ (u.2.2, fB u.1, u.2.1)) -
      pmfH (q1.map fun u ↦ (fB u.1, u.2.1)) - pmfH (q1.map fun u ↦ (u.2.2, u.1, u.2.1)) +
      pmfH (q1.map fun u ↦ (u.1, u.2.1))) := by
  classical
  have hcoord i : q.map (fun u ↦ (u.1, u.2 i)) = q1 := by
    ext ⟨w, mt⟩; rw [pMapPS q _ (w, mt) w (fun _ _ h ↦ (pmi h).1.symm), hq1,
      ← prod_pi_coord (fun _ ↦ K w) (fun _ ↦ pSum1 _) i mt, mulS]
    exact sumC z ↦ by by_cases hmt : mt = z i <;> [rw [iteL (congrArg (w, ·) hmt), iteL hmt, hq];
      rw [iteR fun h ↦ hmt (pmi h).2, iteR hmt, mul_zero]]
  have h1 := condEnt_pi_le q (fun u ↦ (fB u.1, fun i ↦ (u.2 i).1)) n (fun i u ↦ (u.2 i).2)
  have h1_i i : cEntP q (fun u ↦ (u.2 i).2) (fun u ↦ (fB u.1, fun j ↦ (u.2 j).1)) ≤
      pmfH (q1.map fun u ↦ (u.2.2, fB u.1, u.2.1)) - pmfH (q1.map fun u ↦ (fB u.1, u.2.1)) := by
    have hdp := cEntP_le_comp_right q (fun u ↦ (u.2 i).2)
      (fun u ↦ (fB u.1, fun j ↦ (u.2 j).1)) (fun p : B × (Fin n → M) ↦ (p.1, p.2 i))
    have he1 := pmf_cEntP q (fun u ↦ (u.2 i).2) (fun u ↦ (fB u.1, (u.2 i).1))
    rw [show q.map (fun u ↦ ((u.2 i).2, fB u.1, (u.2 i).1)) =
      q1.map (fun u ↦ (u.2.2, fB u.1, u.2.1))
        from by rw [← hcoord i, pMapC]; rfl,
      show q.map (fun u ↦ (fB u.1, (u.2 i).1)) = q1.map (fun u ↦ (fB u.1, u.2.1)) from by
        rw [← hcoord i, pMapC]; rfl] at he1
    exact hdp.trans_eq he1.symm
  have h1' : pmfH (q.map fun u ↦ (fun i ↦ (u.2 i).2, fB u.1, fun i ↦ (u.2 i).1)) -
      pmfH (q.map fun u ↦ (fB u.1, fun i ↦ (u.2 i).1)) ≤
      (n : ℝ) * (pmfH (q1.map fun u ↦ (u.2.2, fB u.1, u.2.1)) -
        pmfH (q1.map fun u ↦ (fB u.1, u.2.1))) := by
    have he := pmf_cEntP q (fun u i ↦ (u.2 i).2) (fun u ↦ (fB u.1, fun i ↦ (u.2 i).1))
    rw [eInj q (fun u ↦ ((fun i ↦ (u.2 i).2), (fB u.1, fun i ↦ (u.2 i).1)))
      (fun v ↦ (v.1, v.2.1, v.2.2)) inj3] at he
    calc _ = _ := he
      _ ≤ ∑ i : Fin n, _ := h1.trans (sumLe fun i _ ↦ h1_i i)
      _ = _ := by rw [sumCon, cardU, cardF, nsmul_eq_mul]
  let qK w : PMF (Fin n → M × T) := PMF.ofFintype (fun z ↦ ∏ i, K w (z i)) (pProd1 _)
  let qM : PMF (Fin n → M) := PMF.ofFintype (fun r₀ ↦ ∏ i, pM (r₀ i)) (pProd1 _)
  have hK_all : pmfH (q.map fun u ↦ (fun i ↦ (u.2 i).2, u.1, fun i ↦ (u.2 i).1)) =
      pmfH μ + (n : ℝ) * ∑ w : W, (μ w).toReal * pmfH (K w) := by
    let eW : W × (Fin n → M × T) ≃ (Fin n → T) × W × (Fin n → M) :=
      ⟨fun u ↦ (fun i ↦ (u.2 i).2, u.1, fun i ↦ (u.2 i).1),
        fun v ↦ (v.2.1, fun i ↦ (v.2.2 i, v.1 i)), fun ⟨_, _⟩ ↦ rfl, fun ⟨_, _, _⟩ ↦ rfl⟩
    rw [show (q.map fun u ↦ (fun i ↦ (u.2 i).2, u.1, fun i ↦ (u.2 i).1)) = q.map eW from rfl,
      pmfHInj q eW.injective, eKer μ qK q fun w z ↦ by simp [qK, pmfOF, hq], mulS]
    congr 1; refine sumC w ↦ ?_
    rw [ent_prod_pi n (fun _ ↦ K w) (qK w) (fun _ ↦ rfl), sumCon, cardU, cardF, nsmul_eq_mul]; ring
  let eMT : (Fin n → M × T) ≃ (Fin n → M) × (Fin n → T) :=
    ⟨fun z ↦ (fun i ↦ (z i).1, fun i ↦ (z i).2), fun p i ↦ (p.1 i, p.2 i),
      fun _ ↦ rfl, fun ⟨_, _⟩ ↦ rfl⟩
  have hM_all : pmfH (q.map fun u ↦ (u.1, fun i ↦ (u.2 i).1)) = pmfH μ + (n : ℝ) * pmfH pM := by
    rw [eKer μ (fun _ ↦ qM) _ fun w r₀ ↦ ?_, ← sumM, pSum1R, one_mul,
      ent_prod_pi n (fun _ ↦ pM) qM (fun _ ↦ rfl), sumCon, cardU, cardF, nsmul_eq_mul]
    rw [pMapPS q _ (w, r₀) w (fun _ _ h ↦ (pmi h).1.symm), ← eMT.symm.sum_comp, fSP]
    simp only [eMT, Equiv.coe_fn_symm_mk]
    rw [sum1 r₀ (fun _ _ hm ↦ sum0 x ↦ iteR fun h ↦ hm (pmi h).2.symm) sglU]
    simp only [↓reduceIte, hq, ← mulS, ← prodS (f := fun i t ↦ K w (r₀ i, t)), qM, pmfOF, hKM]
  have hK_1 : pmfH (q1.map fun u ↦ (u.2.2, u.1, u.2.1)) =
      pmfH μ + ∑ w : W, (μ w).toReal * pmfH (K w) := by
    let e1 : W × M × T ≃ T × W × M := ⟨fun u ↦ (u.2.2, u.1, u.2.1), fun v ↦ (v.2.1, v.2.2, v.1),
      fun ⟨_, _, _⟩ ↦ rfl, fun ⟨_, _, _⟩ ↦ rfl⟩
    rw [show (q1.map fun u ↦ (u.2.2, u.1, u.2.1)) = q1.map e1 from rfl, pmfHInj q1 e1.injective,
      eKer μ K q1 hq1]
  have hM_1 : pmfH (q1.map fun u ↦ (u.1, u.2.1)) = pmfH μ + pmfH pM := by
    rw [eKer μ (fun _ ↦ pM) _ fun w m ↦ ?_, ← sumM, pSum1R, one_mul]
    rw [pMapPS q1 _ (w, m) w (fun _ _ h ↦ (pmi h).1.symm), fSP]
    simp only [Prod.mk.injEq, true_and]
    rw [sum1 m (fun _ _ hm' ↦ sum0 t ↦ iteR fun h ↦ hm' h.symm) sglU]
    exact (sumC t ↦ by rw [iteL rfl, hq1]).trans (by rw [← mulS, hKM])
  rw [hK_all, hM_all, hK_1, hM_1]; linarith

/-- Subadditivity of internal information cost across `2k + 1` independent copies. -/
theorem RandomizedProtocol.internalInfoCost_repeatMajority_le [Fintype X] [Fintype Y]
    (P : RandomizedProtocol X Y Bool) (k : ℕ) (μ : PMF (X × Y)) :
    (P.repeatMajority k).internalInfoCost μ ≤ (2 * k + 1 : ℝ) * P.internalInfoCost μ := by
  classical let n := 2 * k + 1
  let q : PMF ((X × Y) × (Fin n → P.Pub × P.Transcript)) :=
    PMF.ofFintype (fun u ↦ μ u.1 * ∏ i : Fin n, P.execPMF u.1.1 u.1.2 (u.2 i))
      (by rw [fSP]; simp_rw [← mulS, ← prodS, show ∀ xy : X × Y, (∏ _ : Fin n, ∑ mt,
          P.execPMF xy.1 xy.2 mt) = 1 from fun _ ↦ Finset.prod_eq_one fun _ _ ↦ pSum1 _,
        mul_one, pSum1])
  let q0 := q.map fun u ↦ (u.1.1, u.1.2, fun i ↦ (u.2 i).1, fun i ↦ (u.2 i).2)
  have hRep := ic_ofFintype_eqv (Z := Bool) (repPub P k)
    (fun t x ↦ repSide P k (fun s r h ↦ P.aliceStep s x r h) t)
    (fun t y ↦ repSide P k (fun s r h ↦ P.bobStep s y r h) t) (repOut P k) μ
    (q0.map fun w ↦ (w.1, w.2.1, w.2.2.1, repEmb P k w.2.2.2)) (Equiv.refl (Fin n → P.Pub))
    fun x y r₀ tr ↦ by
      rw [Equiv.refl_apply, repPub, pmfOF, rep_prod_eq, pMapC]; dsimp only [q0, Function.comp_def]
      split_ifs with hex
      · rw [pMapU q _ (x, y, r₀, tr) ((x, y), fun i ↦ (r₀ i, hex.choose i))
          (by simp [← hex.choose_spec]) fun ⟨_, _⟩ h ↦ by
          rcases pmi h with ⟨hx, h2⟩; rcases pmi h2 with ⟨hy, h3⟩; rcases pmi h3 with ⟨hm, htr⟩
          exact Prod.ext (Prod.ext hx.symm hy.symm) (funext fun i ↦ Prod.ext (congrFun hm i).symm
            (congrFun (repEmb_inj P k (htr.symm.trans hex.choose_spec)) i))]; rfl
      · rw [mul_zero]
        exact (pMapZ q _ _ fun u h ↦ hex ⟨fun i ↦ (u.2 i).2, (pmi (pmi (pmi h).2).2).2⟩).symm
  let q1 := (P.jointPMF μ).map fun w ↦ ((w.1, w.2.1), (w.2.2.1, w.2.2.2))
  have hq1 xy mt : q1 (xy, mt) = μ xy * P.execPMF xy.1 xy.2 mt := by
    rw [pMapU (P.jointPMF μ) _ (xy, mt) (xy.1, xy.2, mt.1, mt.2) rfl
      (fun ⟨_,_,_,_⟩ h ↦ by cases h; rfl), jointPMF_apply]
  have h1 := subadd_cmi n μ (fun xy ↦ P.execPMF xy.1 xy.2) P.pubCoin (fun xy m₀ ↦
    sum_exec_tr P xy.1 xy.2 m₀) Prod.snd q q1 (fun _ ↦ rfl) hq1
  have h2 := subadd_cmi n μ (fun xy ↦ P.execPMF xy.1 xy.2) P.pubCoin (fun xy m₀ ↦
    sum_exec_tr P xy.1 xy.2 m₀) Prod.fst q q1 (fun _ ↦ rfl) hq1
  rw [repeatMajority, hRep, rIC_inj q0 (fun r ↦ r) (repEmb P k) (fun _ _ h ↦ h) (repEmb_inj P k),
    ic_eq_raw, rIC]
  dsimp only [q0, q1] at h1 h2 ⊢; simp only [pMapC, Function.comp_def] at h1 h2 ⊢
  rw [eInj q (fun u ↦ (u.1, fun i ↦ (u.2 i).1)) (fun v ↦ (v.1.1, v.1.2, v.2))
      (fun ⟨⟨_,_⟩,_⟩ ⟨⟨_,_⟩,_⟩ h ↦ by cases h; rfl),
    eInj q (fun u ↦ (fun i ↦ (u.2 i).2, u.1, fun i ↦ (u.2 i).1))
      (fun v ↦ (v.1, v.2.1.1, v.2.1.2, v.2.2)) (fun ⟨_,⟨_,_⟩,_⟩ ⟨_,⟨_,_⟩,_⟩ h ↦ by cases h; rfl)]
  rw [eInj (P.jointPMF μ) (fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1))
      (fun v ↦ (v.1, (v.2.1, v.2.2.1), v.2.2.2)) inj4,
    eInj (P.jointPMF μ) (fun w ↦ (w.1, w.2.1, w.2.2.1)) (fun v ↦ ((v.1, v.2.1), v.2.2)) inj3]
    at h1 h2
  rw [rIC]
  refine (mLeL ((add_le_add h1 h2).trans_eq (mul_add (n : ℝ) _ _).symm) hL2nn).trans_eq ?_
  push_cast [n]; ring

private lemma ic_rep_mul [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] (g : X × Y → Bool)
    (k : ℕ) {ε ε' : ℝ} (hε₀ : 0 ≤ ε) (hε_half : ε ≤ 1 / 2) (hpow : (4 * ε * (1 - ε)) ^ k ≤ ε') :
    infoComplexity g ε' ≤ (2 * k + 1 : ℝ) * infoComplexity g ε := by
  have hk : (0 : ℝ) < 2 * k + 1 := by positivity
  rw [← div_le_iff₀' hk]
  refine le_csInf ⟨_, inRev g, fun x y ↦ by rw [inputErr_rev]; exact hε₀, rfl⟩ ?_
  rintro c ⟨P, herr, rfl⟩; rw [div_le_iff₀' hk]
  refine (infoComplexity_le_of_inputError_le (P := P.repeatMajority k) fun x y ↦
    (P.inputError_repeatMajority_le k g x y (herr x y) hε_half).trans hpow).trans ?_
  exact worstCaseInfoCost_le _ fun μ ↦
      (P.internalInfoCost_repeatMajority_le k μ).trans (mLeL (internalInfoCost_le_worstCaseInfoCost
      P μ) hk.le)

/-- Constant-factor error reduction for Boolean functions: for every $0 < \varepsilon'$ and
$0 \le \varepsilon < 1/2$, there exists $T \in \mathbb{N}$ independent of the domains and function
$g : X \times Y \to \mathrm{Bool}$ such that
$\mathrm{IC}(g, \varepsilon') \le T \cdot \mathrm{IC}(g, \varepsilon)$. -/
theorem exists_nat_infoComplexity_le_mul_of_lt_half {ε' ε : ℝ} (hε' : 0 < ε') (hε₀ : 0 ≤ ε)
    (hε : ε < 1 / 2) :
    ∃ T : ℕ, ∀ {X : Type u} {Y : Type v} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
      (g : X × Y → Bool), infoComplexity g ε' ≤ (T : ℝ) * infoComplexity g ε := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε'
    (by nlinarith [sq_nonneg (1 - 2 * ε)] : 4 * ε * (1 - ε) < 1)
  exact ⟨2 * k + 1, fun g ↦ by push_cast; exact ic_rep_mul g k hε₀ hε.le hk.le⟩

/-- Quantitative logarithmic error-reduction bound: for sufficiently small
$\varepsilon > \varepsilon' > 0$,
$\mathrm{IC}(g, \varepsilon') \le C \frac{\log(1/\varepsilon')}{\log(1/\varepsilon)}
\mathrm{IC}(g, \varepsilon)$. -/
theorem infoComplexity_le_mul_of_lt :
    ∃ C > 0, ∀ {X : Type u} {Y : Type v} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
      (g : X × Y → Bool) {ε' ε : ℝ}, 0 < ε' → ε' < ε → ε < (2 * Real.exp 1)⁻¹ - 1 / 100 →
      infoComplexity g ε' ≤ C * (Real.log (1 / ε') / Real.log (1 / ε)) * infoComplexity g ε := by
  let c := 1 - rL 4 / rL 5; have hexp : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have hc₀ : 0 < c := by
    rw [sub_pos, div_lt_one (Real.log_pos (by norm_num))]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  refine ⟨3 / c + 3, by positivity, fun {X} {Y} _ _ _ _ g {ε' ε} hε' hε'ε hε_ub ↦ ?_⟩
  have h2e : (2 * Real.exp 1)⁻¹ < 1 / 5 := by
    rw [inv_lt_comm₀ (by positivity) (by norm_num)]; linarith
  have hεp : 0 < ε := hε'.trans hε'ε
  let L1 := rL (1 / ε'); let L2 := rL (1 / ε); let L3 := rL (1 / (4 * ε)); let k := ⌈L1 / L3⌉₊
  have hlε : rL 5 < L2 := Real.log_lt_log (by norm_num) (by rw [lt_div_iff₀ hεp]; linarith)
  have hl4 : 0 < L3 := Real.log_pos (by rw [lt_div_iff₀ (by positivity)]; linarith)
  have hlε' : L2 < L1 := Real.log_lt_log (by positivity) (one_div_lt_one_div_of_lt hε' hε'ε)
  have hlεp : 0 < L2 := (Real.log_pos (by norm_num)).trans hlε
  have hk_l : (k : ℝ) < L1 / L3 + 1 := Nat.ceil_lt_add_one (div_nonneg (hlεp.trans hlε').le hl4.le)
  have hrel : c * L2 ≤ L3 := by
    dsimp only [c, L2, L3]
    rw [show (1 / (4 * ε) : ℝ) = (1 / ε) / 4 by ring,
      Real.log_div (one_div_pos.2 hεp).ne' (by norm_num), sub_mul, one_mul, div_mul_eq_mul_div,
      sub_le_sub_iff_left, le_div_iff₀ (Real.log_pos (by norm_num))]
    exact mLeL hlε.le (Real.log_nonneg (by norm_num))
  have hdl : L1 / L3 ≤ (1 / c) * (L1 / L2) := by
    rw [one_div_mul_eq_div, div_div, mul_comm L2 _, div_le_div_iff₀ hl4 (mul_pos hc₀ hlεp)]
    exact mLeL hrel (hlεp.trans hlε').le
  have hk1 : (1 : ℝ) ≤ k := by
    have h1 : 1 ≤ L1 / L3 := (le_div_iff₀ hl4).2 <| (one_mul L3).symm ▸
      (Real.log_lt_log (by positivity) (one_div_lt_one_div_of_lt (by positivity)
        (by linarith))).le.trans hlε'.le
    linarith [Nat.le_ceil (L1 / L3)]
  have h2k : (2 * k + 1 : ℝ) ≤ (3 / c + 3) * (L1 / L2) := by
    have hratio : 1 < L1 / L2 := (one_lt_div hlεp).2 hlε'
    calc (2 * k + 1 : ℝ) ≤ 3 * (k : ℝ) := by linarith
      _ ≤ 3 * (L1 / L3 + 1) := by linarith
      _ ≤ 3 * ((1 / c) * (L1 / L2) + (L1 / L2)) := by linarith
      _ = _ := by ring
  have hpow : (4 * ε * (1 - ε)) ^ k ≤ ε' := by
    refine (pow_le_pow_left₀ (by nlinarith) (by nlinarith : 4 * ε * (1 - ε) ≤ 4 * ε) k).trans ?_
    have hi : 1 / ε' ≤ (1 / (4 * ε)) ^ k := by
      rw [← Real.log_le_log_iff (one_div_pos.2 hε') (pow_pos (one_div_pos.2 (by positivity)) k),
        Real.log_pow]
      exact (div_le_iff₀ hl4).1 (Nat.le_ceil _)
    rw [one_div_pow] at hi; exact (one_div_le_one_div hε' (pow_pos (by positivity) k)).1 hi
  exact (ic_rep_mul g k hεp.le (by linarith) hpow).trans
    (mul_le_mul_of_nonneg_right h2k (infoComplexity_nonneg g ε))

/-- Zero-cost threshold: at error $\varepsilon \ge 1/2$, any Boolean function has zero interactive
information complexity (achieved by a 0-round random-coin guess). -/
theorem infoComplexity_eq_zero_of_half_le [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (g : X × Y → Bool) {ε : ℝ} (hε : 1 / 2 ≤ ε) : infoComplexity g ε = 0 := by
  let P0 : RandomizedProtocol X Y Bool :=
    { rounds := 0, pubCard := 1, msgCard := fun t ↦ Fin.elim0 t,
      pubCoin := Cslib.Probability.PMF.uniformOfFintype _,
      aliceStep := fun t ↦ Fin.elim0 t, bobStep := fun t ↦ Fin.elim0 t,
      out := fun m₀ _ ↦ decide (m₀ = 0) }
  refine le_antisymm ((infoComplexity_le_of_inputError_le (P := P0) fun x y ↦ ?_).trans
    (worstCaseInfoCost_le P0 fun μ ↦ by rw [P0.internalInfoCost_zero_rounds rfl μ]))
    (infoComplexity_nonneg g ε)
  rw [P0.inputError_def, fSP, Fin.sum_univ_two]; let tr0 : P0.Transcript := fun t ↦ Fin.elim0 t
  have hu : Finset.univ = ({tr0} : Finset P0.Transcript) := by
    ext tr; simp only [memU, Finset.mem_singleton, true_iff]; exact funext fun t ↦ Fin.elim0 t
  have he m₀ : P0.execPMF x y (m₀, tr0) = 1 / 2 := by
    rw [P0.execPMF_apply, Finset.univ_eq_empty_iff.2 ⟨Fin.elim0⟩, Finset.prod_empty, mul_one]
    simp [P0, Cslib.Probability.PMF.uniformOfFintype_apply, one_div]
  simp_rw [hu, Finset.sum_singleton, he]
  change @ite ℝ (decide ((0 : P0.Pub) = 0) ≠ g (x, y)) _ _ _ +
    @ite ℝ (decide ((1 : P0.Pub) = 0) ≠ g (x, y)) _ _ _ ≤ ε
  cases g (x, y) <;> norm_num at hε ⊢ <;> linarith

/-- Two-bit Boolean exclusive-or $\mathrm{XOR}(x, y) = x \oplus y$. -/
@[expose] def bxor (xy : Bool × Bool) : Bool := xor xy.1 xy.2
@[simp] theorem bxor_apply (xy : Bool × Bool) : bxor xy = xor xy.1 xy.2 := rfl
private def unif4 : PMF (Bool × Bool) := PMF.ofFintype (fun _ : Bool × Bool ↦ (4 : r0inf)⁻¹) (by
  rw [sumCon, cardU, Fintype.card_prod, Fintype.card_bool, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))
private lemma cEntP_bool_le_binEntropy {Ω : Type*} [Fintype Ω] (p : PMF Ω) (U V : Ω → Bool) :
    cEntP p U V ≤ Real.binEntropy (∑ w : Ω, if U w ≠ V w then (p w).toReal else 0) := by
  classical let E : Ω → Bool := fun w ↦ decide (U w ≠ V w)
  have hbi : ∀ w, U w = xor (V w) (E w) := fun w ↦ by dsimp [E]; cases U w <;> cases V w <;> decide
  have hmap : cEntP p U V = cEntP p E V := by
    rw [← pmf_cEntP, ← pmf_cEntP]; congr 1
    let e : Bool × Bool ≃ Bool × Bool := ⟨fun ab ↦ (xor ab.2 ab.1, ab.2),
      fun ab ↦ (xor ab.2 ab.1, ab.2), fun ⟨a, b⟩ ↦ by cases a <;> cases b <;> rfl,
      fun ⟨a, b⟩ ↦ by cases a <;> cases b <;> rfl⟩
    rw [show (p.map fun w ↦ (U w, V w)) = (p.map fun w ↦ (E w, V w)).map e by
      rw [pMapC]; congr 1; funext w; exact Prod.ext (hbi w) rfl, pmfHInj _ e.injective]
  have hle : cEntP p E V ≤ pmfH (p.map E) := by
    have h := Cslib.Probability.PMF.conditionalEntropy_map_fst_ge
      (p.map fun w ↦ (V w, E w)) (fun _ ↦ ())
    simp only [pMapC, Function.comp_def] at h
    have h0 : Cslib.Probability.PMF.conditionalEntropy (p.map fun w ↦ ((), E w)) =
        Cslib.Probability.PMF.entropy (p.map E) := by
      rw [Cslib.Probability.PMF.conditionalEntropy, pMapC]
      have h1 : (p.map fun w ↦ ((), E w)) = (p.map E).map fun e ↦ ((), e) := by rw [pMapC]; rfl
      have h2 : p.map (Prod.fst ∘ fun w ↦ ((), E w)) = PMF.pure () := by
        ext ⟨⟩; rw [pMapA, PMF.pure_apply_self, ← p.tsum_coe]; exact tsum_congr fun _ ↦ by simp
      rw [h1, Cslib.Probability.PMF.entropy_map_of_injective _ (fun _ _ h ↦ (pmi h).2), h2,
        Cslib.Probability.PMF.entropy_pure, sub_zero]
    rw [h0] at h; exact mul_le_mul_of_nonneg_right h (Real.log_nonneg (by norm_num))
  have hE : pmfH (p.map E) = Real.binEntropy (∑ w : Ω, if U w ≠ V w then (p w).toReal else 0) := by
    have hpt : (p.map E true).toReal = ∑ w : Ω, if U w ≠ V w then (p w).toReal else 0 := by
      rw [pMapS, eTRS fun _ _ ↦ by
        split_ifs <;> [exact p.apply_ne_top _; exact ENNReal.zero_ne_top]]
      exact sumC w ↦ by dsimp [E]; by_cases h : U w ≠ V w <;> simp [h]
    have hpf : (p.map E false).toReal = 1 - (p.map E true).toReal := by
      have hsum := pSum1R (p.map E); rw [Fintype.sum_bool] at hsum; linarith
    rw [pmfHD, Fintype.sum_bool, hpf, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hpt]
  exact hmap.le.trans (hle.trans_eq hE)
/-- Fano-type distributional information complexity lower bound for binary XOR under the uniform
input distribution on $\mathrm{Bool} \times \mathrm{Bool}$. -/
theorem distInfoComplexity_bxor_uniform_ge {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 2) :
    2 - 2 * (Real.binEntropy δ / Real.log 2) ≤
      distInfoComplexity bxor (PMF.ofFintype (fun _ : Bool × Bool ↦ (4 : ℝ≥0∞)⁻¹) (by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool, nsmul_eq_mul]
        exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))) δ := by
  classical
  have hmu : pmfH unif4 = 2 * rL2 := by
    have hunif : unif4 = Cslib.Probability.PMF.uniformOfFintype (Bool × Bool) := PMF.ext fun xy ↦ by
      simp [unif4, pmfOF, Cslib.Probability.PMF.uniformOfFintype_apply]
    rw [hunif, pmfH_uniform, Fintype.card_prod, Fintype.card_bool,
      show ((2 * 2 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hbool : pmfH (Cslib.Probability.PMF.uniformOfFintype Bool) = rL2 := by
    rw [pmfH_uniform, Fintype.card_bool]; norm_num
  change _ ≤ distInfoComplexity bxor unif4 δ
  refine le_csInf ⟨_, inRev bxor, by rw [distErr_rev]; exact hδ₀, rfl⟩ ?_
  rintro c ⟨P, herr, rfl⟩; set J := P.jointPMF unif4
  have herr_eq : (∑ w : Bool × Bool × P.Pub × P.Transcript,
      if bxor (w.1, w.2.1) ≠ P.out w.2.2.1 w.2.2.2 then (J w).toReal else 0) =
      P.distError bxor unif4 := by
    rw [P.distError_eq_sum_jointPMF]; refine sumC w ↦ ?_
    by_cases h : bxor (w.1, w.2.1) = P.out w.2.2.1 w.2.2.2
    · rw [iteR (not_not.2 h), iteR (not_not.2 h.symm)]
    · rw [iteL h, iteL (Ne.symm h)]
  have hpart (fB : Bool × Bool → Bool) (inv : Bool × Bool → Bool × Bool)
      (hinv : ∀ xy, inv (bxor xy, fB xy) = xy) :
      (pmfH (J.map fun w ↦ (w.1, w.2.1, w.2.2.1)) -
        pmfH (J.map fun w ↦ (fB (w.1, w.2.1), w.2.2.1)) = rL2) ∧
      (pmfH (J.map fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) -
        pmfH (J.map fun w ↦ (w.2.2.2, fB (w.1, w.2.1), w.2.2.1)) ≤ Real.binEntropy δ) := by
    have hinj := iInv (fun xy ↦ (bxor xy, fB xy)) inv hinv
    have hK2 := eKer (Cslib.Probability.PMF.uniformOfFintype Bool) (fun _ ↦ P.pubCoin)
        (J.map fun w ↦ (fB (w.1, w.2.1), w.2.2.1)) fun b m₀ ↦ by
      rw [show (J.map fun w ↦ (fB (w.1, w.2.1), w.2.2.1)) = (J.map fun w ↦ (w.1, w.2.1,
        w.2.2.1)).map fun v ↦ (fB (v.1, v.2.1), v.2.2) from by rw [pMapC]; rfl, pMapS, fSP]
      simp_rw [fSP]
      have hsum : (∑ x : Bool, ∑ y : Bool, ∑ m' : P.Pub,
          @ite r0inf ((b, m₀) = (fB (x, y), m')) (cpd)
          ((J.map fun w ↦ (w.1, w.2.1, w.2.2.1)) (x, y, m')) 0) =
          ∑ xy : Bool × Bool, if fB xy = b then (4 : r0inf)⁻¹ * P.pubCoin m₀ else 0 := by
        rw [fSP]; exact sumC x ↦ sumC y ↦ by
          rw [Finset.sum_eq_single m₀ (fun m' _ hm ↦ by simp [hm.symm]) sglU, joint_map_xym₀]
          by_cases hb : fB (x, y) = b
          · rw [iteL (by simp [hb]), iteL hb]; simp [unif4, pmfOF]
          · rw [iteR (by simp [Ne.symm hb]), iteR hb]
      have hfib : (∑ xy : Bool × Bool, if fB xy = b then (4 : r0inf)⁻¹ * P.pubCoin m₀ else 0) =
          2 * ((4 : r0inf)⁻¹ * P.pubCoin m₀) :=
        (((Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by simp⟩).sum_comp
          fun ab : Bool × Bool ↦ if ab.2 = b then (4 : r0inf)⁻¹ * P.pubCoin m₀ else 0).trans
          (by cases b <;> simp [fSP, two_mul])
      rw [hsum, hfib, Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_bool, ← mul_assoc]
      congr 1; rw [show (4 : r0inf) = 2 * 2 by norm_num,
        ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← mul_assoc,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]; norm_num
    simp_rw [← sumM, pSum1R, one_mul] at hK2
    refine ⟨by rw [ent_joint_xym₀ P unif4, hK2, hmu, hbool]; ring, ?_⟩
    have he := pmf_cEntP J (fun w ↦ bxor (w.1, w.2.1)) (fun w ↦ (fB (w.1, w.2.1), w.2.2.1, w.2.2.2))
    rw [eInj J (fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1))
        (fun v ↦ (bxor (v.2.1, v.2.2.1), fB (v.2.1, v.2.2.1), v.2.2.2, v.1))
        (iInv _ (fun v ↦ (v.2.2.2, (inv (v.1, v.2.1)).1, (inv (v.1, v.2.1)).2, v.2.2.1))
          fun ⟨_,_,_,_⟩ ↦ by simp [-bxor_apply, hinv]),
      ← eInj J (fun w ↦ (fB (w.1, w.2.1), w.2.2.1, w.2.2.2)) (fun v ↦ (v.2.2, v.1, v.2.1)) inj3]
      at he
    have hdp1 := cEntP_le_comp_right J (fun w ↦ bxor (w.1, w.2.1))
      (fun w ↦ (fB (w.1, w.2.1), w.2.2.1, w.2.2.2)) (fun v ↦ (v.1, P.out v.2.1 v.2.2))
    have hdp2 := cEntP_prod_right_le J (fun w ↦ bxor (w.1, w.2.1))
      (fun w ↦ fB (w.1, w.2.1)) (fun w ↦ P.out w.2.2.1 w.2.2.2)
    have hbin := cEntP_bool_le_binEntropy J (fun w ↦ bxor (w.1, w.2.1))
      (fun w ↦ P.out w.2.2.1 w.2.2.2)
    rw [herr_eq] at hbin
    have hδ₁' : δ ≤ 2⁻¹ := by norm_num at hδ₁ ⊢; exact hδ₁
    exact he.le.trans (hdp1.trans (hdp2.trans (hbin.trans
      (Real.binEntropy_strictMonoOn.monotoneOn ⟨P.distError_nonneg bxor unif4,
        herr.trans hδ₁'⟩ ⟨hδ₀, hδ₁'⟩ herr))))
  have hS := hpart Prod.snd (fun uv ↦ (bxor uv, uv.2)) fun ⟨a, b⟩ ↦ by cases a <;> cases b <;> rfl
  have hF := hpart Prod.fst (fun uv ↦ (uv.2, bxor uv)) fun ⟨a, b⟩ ↦ by cases a <;> cases b <;> rfl
  rw [ic_eq_raw P unif4, rIC, show P.jointPMF unif4 = J from rfl]
  have hlog : 0 < rL2 := Real.log_pos (by norm_num)
  calc 2 - 2 * (Real.binEntropy δ / rL2)
      = (rL2)⁻¹ * (2 * rL2 - 2 * Real.binEntropy δ) := by have := hlog.ne'; field_simp
    _ ≤ (rL2)⁻¹ * _ := mLeL (by linarith [hS.1, hS.2, hF.1, hF.2]) (inv_nonneg.2 hlog.le)
end BoostingAndLowerBounds
end
end CslibFrontier.Computability.Communication
