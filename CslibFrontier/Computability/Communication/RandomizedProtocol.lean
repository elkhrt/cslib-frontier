/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Entropy
public import Mathlib.Analysis.SpecialFunctions.Log.Base

import CslibFrontier.Probability.MutualInformation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Public-Coin Randomized Interactive Protocols and Information Complexity

Public-coin randomized two-party interactive communication protocols, execution distributions,
finite-alphabet transports, base-2 internal information cost, exact input-reveal benchmark, and
distributional, max-distributional, and worst-case information complexity functionals
.

## Main definitions

- `CslibFrontier.Computability.Communication.pmfCondEntropyBits`: base-2 conditional Shannon
  entropy.
- `CslibFrontier.Computability.Communication.RandomizedProtocol`: public-coin randomized two-party
  interactive protocol with execution law `execPMF`, joint law `jointPMF`, finite-alphabet
  transport `ofFintype`, error functionals `inputError` and `distError`, base-2 internal
  information cost `internalInfoCost`, and exact input-reveal protocol `trivialExact`.
- `CslibFrontier.Computability.Communication.distInfoComplexity`, `maxDistInfoComplexity`,
  `worstCaseInfoCost`, `infoComplexity`: distributional, max-distributional, and worst-case
  information complexity functionals.

## Main results

- `RandomizedProtocol.internalInfoCost_eq_input_condEntropy_sub`,
  `internalInfoCost_eq_sum_logb`, `internalInfoCost_nonneg`, `internalInfoCost_pure`,
  `internalInfoCost_zero_rounds`, `internalInfoCost_le_log_card`.
- `CslibFrontier.Computability.Communication.RandomizedProtocol.inputError_trivialExact`,
  `internalInfoCost_trivialExact_le`.
- `CslibFrontier.Computability.Communication.maxDistInfoComplexity_le_infoComplexity`: weak minimax
  inequality $\mathrm{IC}_D(f, \varepsilon) \le \mathrm{IC}(f, \varepsilon)$.
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
private lemma pmfH_pure {α : Type*} [Fintype α] (a : α) : pmfH (PMF.pure a) = 0 := by
  rw [pmfH, Cslib.Probability.PMF.entropy_pure, zero_mul]
private lemma pmfH_le_log_card {α : Type*} [Fintype α] (p : PMF α) :
    pmfH p ≤ Real.log (Fintype.card α) := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  calc pmfH p = Cslib.Probability.PMF.entropy p * Real.log 2 := rfl
    _ ≤ Real.logb 2 (Fintype.card α) * Real.log 2 :=
        mul_le_mul_of_nonneg_right (Cslib.Probability.PMF.entropy_le_log_card p) h2.le
    _ = Real.log (Fintype.card α) := by rw [Real.logb, div_mul_cancel₀ _ h2.ne']
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
private lemma pmf_le_map {α β : Type*} [Finite α] (p : PMF α) (f : α → β) (a : α) :
    p a ≤ p.map f (f a) := by
  classical let _ := Fintype.ofFinite α; rw [pMapA, tsum_fintype]
  exact (iteL (rfl : f a = f a)).symm.le.trans (Finset.single_le_sum
    (f := fun b ↦ @ite ℝ≥0∞ (f a = f b) (cpd) (p b) 0) (fun _ _ ↦ bot_le) (memU a))
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
private lemma sum_log_map {Ω D : Type*} [Fintype Ω] [Fintype D] (p : PMF Ω) (g : Ω → D) :
    (∑ w : Ω, eTR (p w) * rL (eTR (p.map g (g w)))) = -pmfH (p.map g) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (fun w _ ↦ memU (g w)), pmfHD,
      ← Finset.sum_neg_distrib]
  refine sumC d ↦ ?_
  have hfg : ∑ w with g w = d, eTR (p w) = eTR (p.map g d) := by
    rw [← eTRS fun w _ ↦ p.apply_ne_top w, pMapS, Finset.sum_filter]
    exact congrArg eTR (sumC w ↦ by by_cases h : g w = d <;> [simp [h]; simp [h, Ne.symm h]])
  rw [Finset.sum_congr rfl fun w hw ↦ by rw [(Finset.mem_filter.1 hw).2], ← sumM, hfg,
    Real.negMulLog]; ring
private lemma sum_log_ratio {Ω B C D : Type*} [Fintype Ω] [Fintype B] [Fintype C] [Fintype D]
    (p : PMF Ω) (b : Ω → B) (c : Ω → C) (d : Ω → D) :
    (∑ w : Ω, eTR (p w) * rL ((eTR (p w) / eTR (p.map b (b w))) /
      (eTR (p.map c (c w)) / eTR (p.map d (d w))))) =
      pmfH (p.map b) - pmfH (p.map d) - pmfH p + pmfH (p.map c) := by
  have ht : ∀ w : Ω, eTR (p w) * rL ((eTR (p w) / eTR (p.map b (b w))) /
      (eTR (p.map c (c w)) / eTR (p.map d (d w)))) = -nml (eTR (p w)) -
      eTR (p w) * rL (eTR (p.map b (b w))) - eTR (p w) * rL (eTR (p.map c (c w))) +
      eTR (p w) * rL (eTR (p.map d (d w))) := fun w ↦ by
    by_cases hw : eTR (p w) = 0; · simp [hw]
    have hp : 0 < eTR (p w) := lt_of_le_of_ne eTRN (Ne.symm hw)
    have hb := lt_of_lt_of_le hp (ENNReal.toReal_mono ((p.map b).apply_ne_top _) (pmf_le_map p b w))
    have hc := lt_of_lt_of_le hp (ENNReal.toReal_mono ((p.map c).apply_ne_top _) (pmf_le_map p c w))
    have hd := lt_of_lt_of_le hp (ENNReal.toReal_mono ((p.map d).apply_ne_top _) (pmf_le_map p d w))
    rw [Real.log_div (div_pos hp hb).ne' (div_pos hc hd).ne', Real.log_div hp.ne' hb.ne',
      Real.log_div hc.ne' hd.ne', Real.negMulLog]; ring
  simp_rw [ht, sumA, sumSub, Finset.sum_neg_distrib]
  rw [← pmfHD p, sum_log_map p b, sum_log_map p c, sum_log_map p d]; ring
/-- Base-2 discrete conditional Shannon entropy $H_2(A \mid B) = H_2(A, B) - H_2(B)$. -/
@[expose] def pmfCondEntropyBits {α β : Type*} [Fintype α] [Fintype β] (p : PMF (α × β)) : ℝ :=
  Cslib.Probability.PMF.entropy p - Cslib.Probability.PMF.entropy (p.map Prod.snd)
lemma pmfCondEntropyBits_def {α β : Type*} [Fintype α] [Fintype β] (p : PMF (α × β)) :
    pmfCondEntropyBits p =
      Cslib.Probability.PMF.entropy p - Cslib.Probability.PMF.entropy (p.map Prod.snd) := rfl
private lemma eKer {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (K : α →
    PMF β) (q : PMF (α × β))
    (hq : ∀ a b, q (a, b) = p a * K a b) : pmfH q = pmfH p + ∑ a : α, eTR (p a) * pmfH (K a) := by
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
   pmfH (q.map fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) + pmfH (q.map fun w ↦ (w.1, w.2.1,
       w.2.2.1))) +
  (pmfH (q.map fun w ↦ (w.2.2.2, w.1, w.2.2.1)) - pmfH (q.map fun w ↦ (w.1, w.2.2.1)) -
   pmfH (q.map fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) + pmfH (q.map fun w ↦ (w.1, w.2.1, w.2.2.1)))
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
private lemma ent_prod_pi {α : Type*} [Fintype α] : ∀ (n : ℕ) (P : Fin n → PMF α) (q : PMF (Fin n →
    α)),
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
end PMFHelpers

/-! ### Public-Coin Randomized Interactive Protocols and Execution Distributions -/

/-- Public-coin randomized two-party interactive protocol on `(X, Y, Z)` with alternating Alice
(`Even t.1`) and Bob (`¬ Even t.1`) rounds. -/
@[ext] structure RandomizedProtocol (X : Type u) (Y : Type v) (Z : Type w) where
  /-- Number of interactive message rounds. -/
  rounds : ℕ
  /-- Public coin alphabet size minus one (`Pub = Fin (pubCard + 1)`). -/
  pubCard : ℕ
  /-- Message alphabet size minus one at 0-indexed round `t : Fin rounds`. -/
  msgCard : Fin rounds → ℕ
  /-- Shared public coin distribution on `Fin (pubCard + 1)`. -/
  pubCoin : PMF (Fin (pubCard + 1))
  /-- Alice's next-message kernel at 0-indexed round `t` (active when `Even t.1`). -/
  aliceStep : ∀ t : Fin rounds, X → Fin (pubCard + 1) →
    (∀ j : Fin t.1, Fin (msgCard ⟨j.1, j.2.trans t.2⟩ + 1)) → PMF (Fin (msgCard t + 1))
  /-- Bob's next-message kernel at 0-indexed round `t` (active when `¬ Even t.1`). -/
  bobStep : ∀ t : Fin rounds, Y → Fin (pubCard + 1) →
    (∀ j : Fin t.1, Fin (msgCard ⟨j.1, j.2.trans t.2⟩ + 1)) → PMF (Fin (msgCard t + 1))
  /-- Public readout map producing the protocol output in `Z`. -/
  out : Fin (pubCard + 1) → (∀ t : Fin rounds, Fin (msgCard t + 1)) → Z

namespace RandomizedProtocol
section Execution
variable {X : Type u} {Y : Type v} {Z : Type w}
/-- Public coin alphabet `Fin (P.pubCard + 1)`. -/
abbrev Pub (P : RandomizedProtocol X Y Z) : Type := Fin (P.pubCard + 1)
/-- Round-`t` message alphabet `Fin (P.msgCard t + 1)`. -/
abbrev Msg (P : RandomizedProtocol X Y Z) (t : Fin P.rounds) : Type := Fin (P.msgCard t + 1)
/-- Complete message transcript space `∀ t : Fin P.rounds, P.Msg t`. -/
abbrev Transcript (P : RandomizedProtocol X Y Z) : Type := ∀ t : Fin P.rounds, P.Msg t
/-- Active next-message kernel at round `t`. -/
@[expose] def stepPMF (P : RandomizedProtocol X Y Z) (x : X) (y : Y) (m₀ : P.Pub) (t : Fin P.rounds)
    (hist : ∀ j : Fin t.1, P.Msg ⟨j.1, j.2.trans t.2⟩) : PMF (P.Msg t) :=
  if Even t.1 then P.aliceStep t x m₀ hist else P.bobStep t y m₀ hist
lemma stepPMF_def (P : RandomizedProtocol X Y Z) (x : X) (y : Y) (m₀ : P.Pub) (t : Fin P.rounds)
    (hist : ∀ j : Fin t.1, P.Msg ⟨j.1, j.2.trans t.2⟩) : P.stepPMF x y m₀ t hist =
      if Even t.1 then P.aliceStep t x m₀ hist else P.bobStep t y m₀ hist := rfl
@[simp] lemma stepPMF_of_even (P : RandomizedProtocol X Y Z) (x : X) (y : Y) (m₀ : P.Pub)
    {t : Fin P.rounds} (ht : Even t.1) (hist : ∀ j : Fin t.1, P.Msg ⟨j.1, j.2.trans t.2⟩) :
    P.stepPMF x y m₀ t hist = P.aliceStep t x m₀ hist := iteL ht
@[simp] lemma stepPMF_of_not_even (P : RandomizedProtocol X Y Z) (x : X) (y : Y) (m₀ : P.Pub)
    {t : Fin P.rounds} (ht : ¬ Even t.1) (hist : ∀ j : Fin t.1, P.Msg ⟨j.1, j.2.trans t.2⟩) :
    P.stepPMF x y m₀ t hist = P.bobStep t y m₀ hist := iteR ht
private lemma sum_prod_step_eq1 : ∀ (r : ℕ) (α : Fin r → Type*) [∀ t, Fintype (α t)]
    (K : ∀ t : Fin r, (∀ j : Fin t.1, α ⟨j.1, j.2.trans t.2⟩) → PMF (α t)),
    ∑ tr : (∀ t : Fin r, α t), ∏ t : Fin r, K t (fun j ↦ tr ⟨j.1, j.2.trans t.2⟩) (tr t) = 1
  | 0, α, _, _ => by
    have _ : Unique (∀ t : Fin 0, α t) := inferInstance
    rw [Finset.univ_unique, Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty]
  | r + 1, α, _, K => by
    rw [← (Fin.snocEquiv α).sum_comp, fSP]
    have hs (m : α (Fin.last r)) (init : ∀ i : Fin r, α i.castSucc) :
        (∏ t : Fin (r + 1), K t (fun j ↦ Fin.snocEquiv α (m, init) ⟨j.1, j.2.trans t.2⟩)
            (Fin.snocEquiv α (m, init) t)) =
          (∏ i : Fin r, K i.castSucc (fun j ↦ init ⟨j.1, j.2.trans i.2⟩) (init i)) *
            K (Fin.last r) init m := by
      rw [Fin.prod_univ_castSucc]; simp only [Fin.snocEquiv_apply, Fin.snoc_last]; congr 1
      · exact prodC i ↦ by
          rw [show (fun j : Fin i.castSucc.1 ↦ Fin.snoc init m ⟨j.1, j.2.trans i.castSucc.2⟩) =
            fun j : Fin i.castSucc.1 ↦ init ⟨j.1, j.2.trans i.2⟩ from
              funext fun j ↦ Fin.snoc_castSucc (α := α) m init ⟨j.1, j.2.trans i.2⟩,
            Fin.snoc_castSucc]
      · rw [show (fun j : Fin (Fin.last r).1 ↦ Fin.snoc init m ⟨j.1, j.2.trans (Fin.last r).2⟩) =
          init from funext fun j ↦ Fin.snoc_castSucc (α := α) m init j]
    simp_rw [hs]; rw [Finset.sum_comm]; simp_rw [← mulS, pSum1, mul_one]
    exact sum_prod_step_eq1 r (fun i ↦ α i.castSucc) (fun i h ↦ K i.castSucc h)
/-- Execution distribution on `P.Pub × P.Transcript` on `(x, y)`. -/
@[expose] def execPMF (P : RandomizedProtocol X Y Z) (x : X) (y : Y) : PMF (P.Pub × P.Transcript) :=
  PMF.ofFintype (fun mt ↦ P.pubCoin mt.1 * ∏ t : Fin P.rounds,
    P.stepPMF x y mt.1 t (fun j ↦ mt.2 ⟨j.1, j.2.trans t.2⟩) (mt.2 t))
    (by
      rw [fSP]; simp_rw [← mulS, sum_prod_step_eq1 P.rounds P.Msg (P.stepPMF x y _), mul_one]
      exact pSum1 P.pubCoin)
lemma execPMF_def (P : RandomizedProtocol X Y Z) (x : X) (y : Y) :
    (P.execPMF x y : P.Pub × P.Transcript → ℝ≥0∞) = fun mt ↦ P.pubCoin mt.1 *
      ∏ t : Fin P.rounds, P.stepPMF x y mt.1 t (fun j ↦ mt.2 ⟨j.1, j.2.trans t.2⟩) (mt.2 t) := rfl
@[simp, grind =] lemma execPMF_apply (P : RandomizedProtocol X Y Z) (x : X) (y : Y)
    (mt : P.Pub × P.Transcript) : P.execPMF x y mt = P.pubCoin mt.1 *
      ∏ t : Fin P.rounds, P.stepPMF x y mt.1 t (fun j ↦ mt.2 ⟨j.1, j.2.trans t.2⟩) (mt.2 t) := rfl
/-- Summing `P.execPMF x y (m₀, tr)` over all transcripts `tr` recovers `P.pubCoin m₀`. -/
theorem sum_execPMF_transcript (P : RandomizedProtocol X Y Z) (x : X) (y : Y) (m₀ : P.Pub) :
    ∑ tr : P.Transcript, P.execPMF x y (m₀, tr) = P.pubCoin m₀ := by
  simp_rw [execPMF_apply, ← mulS, sum_prod_step_eq1 P.rounds P.Msg (P.stepPMF x y m₀), mul_one]
private lemma sum_exec_tr (P : RandomizedProtocol X Y Z) (x : X) (y : Y) (m₀ : P.Pub) :
    ∑ tr : P.Transcript, P.execPMF x y (m₀, tr) = P.pubCoin m₀ :=
  P.sum_execPMF_transcript x y m₀
/-- Joint distribution on `X × Y × P.Pub × P.Transcript` under input prior `μ`. -/
@[expose] def jointPMF [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z) (μ : PMF (X × Y)) :
    PMF (X × Y × P.Pub × P.Transcript) :=
  PMF.ofFintype (fun w ↦ μ (w.1, w.2.1) * P.execPMF w.1 w.2.1 (w.2.2.1, w.2.2.2))
    (by rw [fSP]; simp_rw [fSP, ← mulS, ← fSP, pSum1, mul_one, ← fSP, pSum1])
lemma jointPMF_def [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z) (μ : PMF (X × Y)) :
    (P.jointPMF μ : X × Y × P.Pub × P.Transcript → ℝ≥0∞) =
      fun w ↦ μ (w.1, w.2.1) * P.execPMF w.1 w.2.1 (w.2.2.1, w.2.2.2) := rfl
@[simp, grind =] lemma jointPMF_apply [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z)
    (μ : PMF (X × Y)) (w : X × Y × P.Pub × P.Transcript) :
    P.jointPMF μ w = μ (w.1, w.2.1) * P.execPMF w.1 w.2.1 (w.2.2.1, w.2.2.2) := rfl
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
    rw [pmfHInjOn _ (fun ⟨_,_,_,_⟩ _ ⟨_,_,_,_⟩ _ h ↦ by cases h; rfl),
      ← pmfHInj (P.jointPMF μ) e1.injective]
    exact eKer μ (fun xy ↦ P.execPMF xy.1 xy.2) ((P.jointPMF μ).map e1)
      fun ⟨_, _⟩ ⟨_, _⟩ ↦ by rw [pMapE]; rfl
  rw [hH1, ent_joint_xym₀]; simp_rw [mul_sub, sumSub, ← sumM, pSum1R, one_mul]; ring
/-- Per-input error probability of `P` for computing `f` at `(x, y)`. -/
@[expose] def inputError (P : RandomizedProtocol X Y Z) (f : X × Y → Z) (x : X) (y : Y) : ℝ :=
  ∑ mt : P.Pub × P.Transcript, @ite ℝ (P.out mt.1 mt.2 ≠ f (x, y)) (cpd) (P.execPMF x y mt).toReal 0
lemma inputError_def (P : RandomizedProtocol X Y Z) (f : X × Y → Z) (x : X) (y : Y) :
    P.inputError f x y = ∑ mt : P.Pub × P.Transcript,
      @ite ℝ (P.out mt.1 mt.2 ≠ f (x, y)) (Classical.propDecidable _)
        (P.execPMF x y mt).toReal 0 := rfl
/-- Per-input error probability is nonnegative. -/
theorem inputError_nonneg (P : RandomizedProtocol X Y Z) (f : X × Y → Z) (x : X) (y : Y) :
    0 ≤ P.inputError f x y := by classical exact sumNn fun _ _ ↦ by split_ifs <;> positivity
/-- Per-input error probability is at most `1`. -/
theorem inputError_le_one (P : RandomizedProtocol X Y Z) (f : X × Y → Z) (x : X) (y : Y) :
    P.inputError f x y ≤ 1 := by
  classical exact (sumLe fun _ _ ↦ by split_ifs <;> [exact le_rfl;
    positivity]).trans_eq (pSum1R (P.execPMF x y))
/-- Distributional error probability of `P` for `f` under prior `μ`. -/
@[expose] def distError [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z) (f : X × Y → Z)
    (μ : PMF (X × Y)) : ℝ := ∑ xy : X × Y, (μ xy).toReal * P.inputError f xy.1 xy.2
lemma distError_def [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z) (f : X × Y → Z)
    (μ : PMF (X × Y)) :
    P.distError f μ = ∑ xy : X × Y, (μ xy).toReal * P.inputError f xy.1 xy.2 := rfl
/-- Distributional error equals failure probability under `P.jointPMF μ`. -/
theorem distError_eq_sum_jointPMF [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z)
    (f : X × Y → Z) (μ : PMF (X × Y)) :
    P.distError f μ = ∑ w : X × Y × P.Pub × P.Transcript,
      @ite ℝ (P.out w.2.2.1 w.2.2.2 ≠ f (w.1, w.2.1)) (Classical.propDecidable _)
        (P.jointPMF μ w).toReal 0 := by
  classical rw [distError_def, fSP]; simp_rw [fSP, inputError_def, mulS, fSP]
  exact sumC x ↦ sumC y ↦ sumC m ↦ sumC tr ↦ by split_ifs <;> simp [jointPMF_apply, eTRM]
/-- Distributional error under `PMF.pure xy` equals `P.inputError f xy.1 xy.2`. -/
@[simp, grind =] theorem distError_pure [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z)
    (f : X × Y → Z) (xy : X × Y) : P.distError f (PMF.pure xy) = P.inputError f xy.1 xy.2 := by
  classical rw [distError_def, sum1 xy (fun z _ hz ↦ by simp [pPureA, hz]) sglU]; simp
/-- Distributional error is nonnegative. -/
theorem distError_nonneg [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z) (f : X × Y → Z)
    (μ : PMF (X × Y)) : 0 ≤ P.distError f μ :=
  sumNn fun xy _ ↦ mul_nonneg eTRN (P.inputError_nonneg f xy.1 xy.2)
/-- Distributional error is at most `1`. -/
theorem distError_le_one [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z) (f : X × Y → Z)
    (μ : PMF (X × Y)) : P.distError f μ ≤ 1 :=
  (sumLe fun xy _ ↦
      mul_le_of_le_one_right eTRN (P.inputError_le_one f xy.1 xy.2)).trans_eq (pSum1R μ)
/-- Base-2 internal information cost $I_2(M^+ : X \mid Y, M^0) + I_2(M^+ : Y \mid X, M^0)$. -/
@[expose] def internalInfoCost [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z)
    (μ : PMF (X × Y)) : ℝ :=
  (Cslib.Probability.PMF.entropy ((P.jointPMF μ).map fun w ↦ (w.2.2.2, w.2.1, w.2.2.1)) -
   Cslib.Probability.PMF.entropy ((P.jointPMF μ).map fun w ↦ (w.2.1, w.2.2.1)) -
   Cslib.Probability.PMF.entropy ((P.jointPMF μ).map fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) +
   Cslib.Probability.PMF.entropy ((P.jointPMF μ).map fun w ↦ (w.1, w.2.1, w.2.2.1))) +
  (Cslib.Probability.PMF.entropy ((P.jointPMF μ).map fun w ↦ (w.2.2.2, w.1, w.2.2.1)) -
   Cslib.Probability.PMF.entropy ((P.jointPMF μ).map fun w ↦ (w.1, w.2.2.1)) -
   Cslib.Probability.PMF.entropy ((P.jointPMF μ).map fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) +
   Cslib.Probability.PMF.entropy ((P.jointPMF μ).map fun w ↦ (w.1, w.2.1, w.2.2.1)))
lemma internalInfoCost_def [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z)
    (μ : PMF (X × Y)) : P.internalInfoCost μ =
      (Cslib.Probability.PMF.entropy ((P.jointPMF μ).map fun w ↦ (w.2.2.2, w.2.1, w.2.2.1)) -
       Cslib.Probability.PMF.entropy ((P.jointPMF μ).map fun w ↦ (w.2.1, w.2.2.1)) -
       Cslib.Probability.PMF.entropy ((P.jointPMF μ).map fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) +
       Cslib.Probability.PMF.entropy ((P.jointPMF μ).map fun w ↦ (w.1, w.2.1, w.2.2.1))) +
      (Cslib.Probability.PMF.entropy ((P.jointPMF μ).map fun w ↦ (w.2.2.2, w.1, w.2.2.1)) -
       Cslib.Probability.PMF.entropy ((P.jointPMF μ).map fun w ↦ (w.1, w.2.2.1)) -
       Cslib.Probability.PMF.entropy ((P.jointPMF μ).map fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) +
       Cslib.Probability.PMF.entropy ((P.jointPMF μ).map fun w ↦ (w.1, w.2.1, w.2.2.1))) := rfl
private lemma ic_eq_raw [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z) (μ : PMF (X × Y)) :
    P.internalInfoCost μ = (rL2)⁻¹ * rIC (P.jointPMF μ) := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [internalInfoCost_def, rIC]; dsimp only [pmfH]; field_simp [h2]
/-- Input conditional-entropy reduction characterization of `internalInfoCost`. -/
theorem internalInfoCost_eq_input_condEntropy_sub [Fintype X] [Fintype Y]
    (P : RandomizedProtocol X Y Z) (μ : PMF (X × Y)) :
    P.internalInfoCost μ =
      (pmfCondEntropyBits ((P.jointPMF μ).map fun w ↦ (w.1, w.2.1, w.2.2.1)) -
       pmfCondEntropyBits ((P.jointPMF μ).map fun w ↦ (w.1, w.2.1, w.2.2.1, w.2.2.2))) +
      (pmfCondEntropyBits ((P.jointPMF μ).map fun w ↦ (w.2.1, w.1, w.2.2.1)) -
       pmfCondEntropyBits ((P.jointPMF μ).map fun w ↦ (w.2.1, w.1, w.2.2.1, w.2.2.2))) := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [ic_eq_raw, rIC]; set J := P.jointPMF μ
  simp only [pmfCondEntropyBits_def, pMapC, Function.comp_def]
  have hE1 : pmfH (J.map fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) =
      pmfH (J.map fun w ↦ (w.1, w.2.1, w.2.2.1, w.2.2.2)) :=
    (eInj J (fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1))
      (fun v ↦ (v.2.1, v.2.2.1, v.2.2.2, v.1)) inj4).symm
  have hE2 : pmfH (J.map fun w ↦ (w.2.2.2, w.2.1, w.2.2.1)) =
      pmfH (J.map fun w ↦ (w.2.1, w.2.2.1, w.2.2.2)) :=
    (eInj J (fun w ↦ (w.2.2.2, w.2.1, w.2.2.1)) (fun v ↦ (v.2.1, v.2.2, v.1)) inj3).symm
  have hE3 : pmfH (J.map fun w ↦ (w.1, w.2.1, w.2.2.1)) =
      pmfH (J.map fun w ↦ (w.2.1, w.1, w.2.2.1)) :=
    (eInj J (fun w ↦ (w.1, w.2.1, w.2.2.1)) (fun v ↦ (v.2.1, v.1, v.2.2)) inj3).symm
  have hE4 : pmfH (J.map fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) =
      pmfH (J.map fun w ↦ (w.2.1, w.1, w.2.2.1, w.2.2.2)) :=
    (eInj J (fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1))
      (fun v ↦ (v.2.2.1, v.2.1, v.2.2.2, v.1)) inj4).symm
  have hE5 : pmfH (J.map fun w ↦ (w.2.2.2, w.1, w.2.2.1)) =
      pmfH (J.map fun w ↦ (w.1, w.2.2.1, w.2.2.2)) :=
    (eInj J (fun w ↦ (w.2.2.2, w.1, w.2.2.1)) (fun v ↦ (v.2.1, v.2.2, v.1)) inj3).symm
  dsimp only [pmfH] at hE1 hE2 hE3 hE4 hE5 ⊢
  have c1 := (mul_eq_mul_right_iff.1 hE1).resolve_right h2
  have c2 := (mul_eq_mul_right_iff.1 hE2).resolve_right h2
  have c3 := (mul_eq_mul_right_iff.1 hE3).resolve_right h2
  have c4 := (mul_eq_mul_right_iff.1 hE4).resolve_right h2
  have c5 := (mul_eq_mul_right_iff.1 hE5).resolve_right h2
  field_simp [h2]; linarith
/-- Log-ratio expectation characterization of `internalInfoCost` in base 2. -/
theorem internalInfoCost_eq_sum_logb [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z)
    (μ : PMF (X × Y)) :
    P.internalInfoCost μ =
      (∑ w : X × Y × P.Pub × P.Transcript, (P.jointPMF μ w).toReal * Real.logb 2
        (((P.jointPMF μ w).toReal / (((P.jointPMF μ).map fun u ↦ (u.2.1, u.2.2.1, u.2.2.2))
            (w.2.1, w.2.2.1, w.2.2.2)).toReal) /
          ((((P.jointPMF μ).map fun u ↦ (u.1, u.2.1, u.2.2.1)) (w.1, w.2.1, w.2.2.1)).toReal /
            (((P.jointPMF μ).map fun u ↦ (u.2.1, u.2.2.1)) (w.2.1, w.2.2.1)).toReal))) +
      (∑ w : X × Y × P.Pub × P.Transcript, (P.jointPMF μ w).toReal * Real.logb 2
        (((P.jointPMF μ w).toReal / (((P.jointPMF μ).map fun u ↦ (u.1, u.2.2.1, u.2.2.2))
            (w.1, w.2.2.1, w.2.2.2)).toReal) /
          ((((P.jointPMF μ).map fun u ↦ (u.1, u.2.1, u.2.2.1)) (w.1, w.2.1, w.2.2.1)).toReal /
            (((P.jointPMF μ).map fun u ↦ (u.1, u.2.2.1)) (w.1, w.2.2.1)).toReal))) := by
  rw [ic_eq_raw, rIC]; set J := P.jointPMF μ
  have hl : ∀ f : X × Y × P.Pub × P.Transcript → ℝ, (∑ w, (J w).toReal * Real.logb 2 (f w)) =
      (rL2)⁻¹ * ∑ w, (J w).toReal * rL (f w) := fun f ↦ by
    rw [mulS]; exact sumC w ↦ by rw [Real.logb]; ring
  have hJ4 : pmfH (J.map fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) = pmfH J :=
    pmfHInj J (f := fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) inj4
  rw [hl, hl, sum_log_ratio J (fun u ↦ (u.2.1, u.2.2.1, u.2.2.2)) (fun u ↦ (u.1, u.2.1,
      u.2.2.1)) (fun u ↦ (u.2.1, u.2.2.1)),
    sum_log_ratio J (fun u ↦ (u.1, u.2.2.1, u.2.2.2)) (fun u ↦ (u.1, u.2.1,
        u.2.2.1)) (fun u ↦ (u.1, u.2.2.1)), hJ4,
    eInj J (fun w ↦ (w.2.2.2, w.2.1, w.2.2.1)) (fun v ↦ (v.2.1, v.2.2, v.1)) inj3,
    eInj J (fun w ↦ (w.2.2.2, w.1, w.2.2.1)) (fun v ↦ (v.2.1, v.2.2, v.1)) inj3]; ring
private lemma cmi_bridge [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z) (μ : PMF (X × Y)) :
    P.internalInfoCost μ =
      Cslib.Probability.PMF.condMutualInfo
        ((P.jointPMF μ).map fun w ↦ ((w.2.1, w.2.2.1), w.2.2.2, w.1)) +
      Cslib.Probability.PMF.condMutualInfo
        ((P.jointPMF μ).map fun w ↦ ((w.1, w.2.2.1), w.2.2.2, w.2.1)) := by
  set J := P.jointPMF μ
  rw [internalInfoCost_def, Cslib.Probability.PMF.condMutualInfo_map,
    Cslib.Probability.PMF.condMutualInfo_map]
  have h1 : Cslib.Probability.PMF.entropy (J.map fun w ↦ ((w.2.1, w.2.2.1), w.2.2.2)) =
      Cslib.Probability.PMF.entropy (J.map fun w ↦ (w.2.2.2, w.2.1, w.2.2.1)) := by
    rw [show (fun w : X × Y × P.Pub × P.Transcript ↦ ((w.2.1, w.2.2.1), w.2.2.2)) =
      (fun v : P.Transcript × Y × P.Pub ↦ ((v.2.1, v.2.2), v.1)) ∘
        (fun w ↦ (w.2.2.2, w.2.1, w.2.2.1)) from rfl, ← pMapC]
    exact Cslib.Probability.PMF.entropy_map_of_injective _ inj3
  have h2 : Cslib.Probability.PMF.entropy (J.map fun w ↦ ((w.2.1, w.2.2.1), w.1)) =
      Cslib.Probability.PMF.entropy (J.map fun w ↦ (w.1, w.2.1, w.2.2.1)) := by
    rw [show (fun w : X × Y × P.Pub × P.Transcript ↦ ((w.2.1, w.2.2.1), w.1)) =
      (fun v : X × Y × P.Pub ↦ ((v.2.1, v.2.2), v.1)) ∘
        (fun w ↦ (w.1, w.2.1, w.2.2.1)) from rfl, ← pMapC]
    exact Cslib.Probability.PMF.entropy_map_of_injective _ inj3
  have h3 : Cslib.Probability.PMF.entropy (J.map fun w ↦ ((w.2.1, w.2.2.1), w.2.2.2, w.1)) =
      Cslib.Probability.PMF.entropy (J.map fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) := by
    rw [show (fun w : X × Y × P.Pub × P.Transcript ↦ ((w.2.1, w.2.2.1), w.2.2.2, w.1)) =
      (fun v : P.Transcript × X × Y × P.Pub ↦ ((v.2.2.1, v.2.2.2), v.1, v.2.1)) ∘
        (fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) from rfl, ← pMapC]
    exact Cslib.Probability.PMF.entropy_map_of_injective _ inj4
  have h4 : Cslib.Probability.PMF.entropy (J.map fun w ↦ ((w.1, w.2.2.1), w.2.2.2)) =
      Cslib.Probability.PMF.entropy (J.map fun w ↦ (w.2.2.2, w.1, w.2.2.1)) := by
    rw [show (fun w : X × Y × P.Pub × P.Transcript ↦ ((w.1, w.2.2.1), w.2.2.2)) =
      (fun v : P.Transcript × X × P.Pub ↦ ((v.2.1, v.2.2), v.1)) ∘
        (fun w ↦ (w.2.2.2, w.1, w.2.2.1)) from rfl, ← pMapC]
    exact Cslib.Probability.PMF.entropy_map_of_injective _ inj3
  have h5 : Cslib.Probability.PMF.entropy (J.map fun w ↦ ((w.1, w.2.2.1), w.2.1)) =
      Cslib.Probability.PMF.entropy (J.map fun w ↦ (w.1, w.2.1, w.2.2.1)) := by
    rw [show (fun w : X × Y × P.Pub × P.Transcript ↦ ((w.1, w.2.2.1), w.2.1)) =
      (fun v : X × Y × P.Pub ↦ ((v.1, v.2.2), v.2.1)) ∘
        (fun w ↦ (w.1, w.2.1, w.2.2.1)) from rfl, ← pMapC]
    exact Cslib.Probability.PMF.entropy_map_of_injective _ inj3
  have h6 : Cslib.Probability.PMF.entropy (J.map fun w ↦ ((w.1, w.2.2.1), w.2.2.2, w.2.1)) =
      Cslib.Probability.PMF.entropy (J.map fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) := by
    rw [show (fun w : X × Y × P.Pub × P.Transcript ↦ ((w.1, w.2.2.1), w.2.2.2, w.2.1)) =
      (fun v : P.Transcript × X × Y × P.Pub ↦ ((v.2.1, v.2.2.2), v.1, v.2.2.1)) ∘
        (fun w ↦ (w.2.2.2, w.1, w.2.1, w.2.2.1)) from rfl, ← pMapC]
    exact Cslib.Probability.PMF.entropy_map_of_injective _ inj4
  rw [h1, h2, h3, h4, h5, h6]; ring
/-- Internal information cost is nonnegative. -/
theorem internalInfoCost_nonneg [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z)
    (μ : PMF (X × Y)) : 0 ≤ P.internalInfoCost μ := by
  rw [cmi_bridge P μ]
  exact add_nonneg (Cslib.Probability.PMF.condMutualInfo_nonneg _)
    (Cslib.Probability.PMF.condMutualInfo_nonneg _)
private lemma cmi_le_ent {Ω A B C : Type*} [Finite A] [Finite B] [Finite C]
    (p : PMF Ω) (U : Ω → A) (V : Ω → B) (W : Ω → C) :
    Cslib.Probability.PMF.condMutualInfo (p.map fun w ↦ (W w, U w, V w)) ≤
      Cslib.Probability.PMF.entropy (p.map V) := by
  have h1 := Cslib.Probability.PMF.condMutualInfo_le_conditionalEntropy_snd
    (p.map fun w ↦ (W w, U w, V w))
  have h2 := Cslib.Probability.PMF.conditionalEntropy_map_fst_ge
    ((p.map fun w ↦ (W w, U w, V w)).map (Prod.map id Prod.snd)) (fun _ ↦ ())
  simp only [pMapC, Function.comp_def, Prod.map_apply, id_eq] at h1 h2
  have h3 : Cslib.Probability.PMF.conditionalEntropy (p.map fun w ↦ ((), V w)) =
      Cslib.Probability.PMF.entropy (p.map V) := by
    rw [Cslib.Probability.PMF.conditionalEntropy, pMapC]
    have h4 : (p.map fun w ↦ ((), V w)) = (p.map V).map (fun v ↦ ((), v)) := by
      rw [pMapC]; rfl
    have h5 : p.map (Prod.fst ∘ fun w ↦ ((), V w)) = PMF.pure () := by
      ext ⟨⟩; rw [pMapA, PMF.pure_apply_self, ← p.tsum_coe]; exact tsum_congr fun _ ↦ by simp
    rw [h4, Cslib.Probability.PMF.entropy_map_of_injective _ (fun _ _ h ↦ (pmi h).2), h5,
      Cslib.Probability.PMF.entropy_pure, sub_zero]
  exact h1.trans (h2.trans_eq h3)
private lemma condEnt_le_log_card {Ω α β : Type*} [Fintype α] [Fintype β] (p : PMF Ω) (U : Ω →
    α) (V : Ω → β) :
    pmfH (p.map fun w ↦ (U w, V w)) - pmfH (p.map V) ≤ rL (fCard α) := by
  have h2 : (0 : ℝ) < rL2 := Real.log_pos one_lt_two
  have hsw : Cslib.Probability.PMF.entropy (p.map fun w ↦ (U w, V w)) =
      Cslib.Probability.PMF.entropy (p.map fun w ↦ (V w, U w)) := by
    rw [show (fun w : Ω ↦ (U w, V w)) = Prod.swap ∘ (fun w ↦ (V w, U w)) from rfl, ← pMapC]
    exact Cslib.Probability.PMF.entropy_map_of_injective _ Prod.swap_injective
  have hle : Cslib.Probability.PMF.conditionalEntropy (p.map fun w ↦ (V w, U w)) ≤
      Real.logb 2 (fCard α) :=
    Cslib.Probability.PMF.conditionalEntropy_le_log_card _
  rw [Cslib.Probability.PMF.conditionalEntropy, pMapC] at hle
  change _ - Cslib.Probability.PMF.entropy (p.map V) ≤ _ at hle
  rw [← hsw] at hle
  calc pmfH (p.map fun w ↦ (U w, V w)) - pmfH (p.map V)
      = (Cslib.Probability.PMF.entropy (p.map fun w ↦ (U w, V w)) -
          Cslib.Probability.PMF.entropy (p.map V)) * rL2 := by dsimp only [pmfH]; ring
    _ ≤ Real.logb 2 (fCard α) * rL2 := mul_le_mul_of_nonneg_right hle h2.le
    _ = rL (fCard α) := by rw [Real.logb, div_mul_cancel₀ _ h2.ne']
private lemma joint_pure_map [Fintype X] [Fintype Y] {α : Type*} (P : RandomizedProtocol X Y Z) (xy
    : X × Y)
    (g : X × Y × P.Pub × P.Transcript → α) (a : α) (hg : ∀ w, w.1 = xy.1 ∧ w.2.1 = xy.2 → g w = a) :
    (P.jointPMF (PMF.pure xy)).map g = PMF.pure a := by
  classical ext b; rw [pMapS]; by_cases h : b = a
  · subst h; rw [PMF.pure_apply_self, ← pSum1 (P.jointPMF (PMF.pure xy))]
    refine sumC w ↦ ?_; split_ifs with hw; · rfl
    · rw [jointPMF_apply, pPureA, iteR fun he ↦ hw (hg w (Prod.ext_iff.1 he)).symm, zero_mul]
  · rw [pPureA, iteR h]; refine sum0 w ↦ ?_; split_ifs with hw
    · rw [jointPMF_apply, pPureA, iteR fun he ↦ h (hw.trans (hg w (Prod.ext_iff.1 he))), zero_mul]
    · rfl
/-- Internal information cost vanishes under any Dirac input distribution. -/
@[simp, grind =] theorem internalInfoCost_pure [Fintype X] [Fintype Y]
    (P : RandomizedProtocol X Y Z) (xy : X × Y) : P.internalInfoCost (PMF.pure xy) = 0 := by
  refine le_antisymm ?_ (P.internalInfoCost_nonneg _); rw [cmi_bridge]
  have hA := cmi_le_ent (P.jointPMF (PMF.pure xy)) (fun w ↦ w.2.2.2) (fun w ↦ w.1) (fun w ↦ (w.2.1,
      w.2.2.1))
  have hB := cmi_le_ent (P.jointPMF (PMF.pure xy)) (fun w ↦ w.2.2.2) (fun w ↦ w.2.1) (fun w ↦ (w.1,
      w.2.2.1))
  rw [joint_pure_map P xy (fun w ↦ w.1) xy.1 (fun _ h ↦ h.1),
    Cslib.Probability.PMF.entropy_pure] at hA
  rw [joint_pure_map P xy (fun w ↦ w.2.1) xy.2 (fun _ h ↦ h.2),
    Cslib.Probability.PMF.entropy_pure] at hB
  linarith
private lemma map_drop_sub {Ω τ α : Type*} [Fintype τ] [Fintype α] [Subsingleton τ] (p : PMF Ω)
    (f : Ω → τ) (g : Ω → α) : pmfH (p.map fun w ↦ (f w, g w)) = pmfH (p.map g) := by
  obtain ⟨w₀, _⟩ := p.support_nonempty
  have h : (p.map fun w ↦ (f w, g w)) = (p.map g).map fun a ↦ (f w₀, a) := by
    rw [pMapC]; congr 1; funext w; exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [h]; exact pmfHInj (p.map g) fun _ _ he ↦ (pmi he).2
/-- Zero-round protocols have zero internal information cost. -/
theorem internalInfoCost_zero_rounds [Fintype X] [Fintype Y] {P : RandomizedProtocol X Y Z}
    (h0 : P.rounds = 0) (μ : PMF (X × Y)) : P.internalInfoCost μ = 0 := by
  have _ : Subsingleton P.Transcript := ⟨fun _ _ ↦ funext fun t ↦ Fin.elim0 (h0 ▸ t)⟩
  set J := P.jointPMF μ
  rw [ic_eq_raw, rIC, map_drop_sub J (fun w ↦ w.2.2.2) (fun w ↦ (w.2.1, w.2.2.1)),
    map_drop_sub J (fun w ↦ w.2.2.2) (fun w ↦ (w.1, w.2.1, w.2.2.1)),
    map_drop_sub J (fun w ↦ w.2.2.2) (fun w ↦ (w.1, w.2.2.1))]; ring
/-- Upper bound $I_2(\Pi; \mu) \le \log_2(|X| \cdot |Y|)$ on nonempty finite inputs. -/
theorem internalInfoCost_le_log_card [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (P : RandomizedProtocol X Y Z) (μ : PMF (X × Y)) :
    P.internalInfoCost μ ≤ Real.logb 2 (Fintype.card X * Fintype.card Y) := by
  rw [cmi_bridge P μ]
  have hA := (cmi_le_ent (P.jointPMF μ) (fun w ↦ w.2.2.2) (fun w ↦ w.1) (fun w ↦ (w.2.1,
      w.2.2.1))).trans (Cslib.Probability.PMF.entropy_le_log_card _)
  have hB := (cmi_le_ent (P.jointPMF μ) (fun w ↦ w.2.2.2) (fun w ↦ w.2.1) (fun w ↦ (w.1,
      w.2.2.1))).trans (Cslib.Probability.PMF.entropy_le_log_card _)
  have hcx : (0 : ℝ) < fCard X := Nat.cast_pos.2 Fintype.card_pos
  have hcy : (0 : ℝ) < fCard Y := Nat.cast_pos.2 Fintype.card_pos
  rw [Real.logb_mul hcx.ne' hcy.ne']; exact add_le_add hA hB
/-- Construct a `RandomizedProtocol` from finite public-coin and round message alphabets. -/
@[expose] def ofFintype {R₀ : Type*} {r : ℕ} {Ω : Fin r → Type*} [Fintype R₀] [Nonempty R₀]
    [∀ t, Fintype (Ω t)] [∀ t, Nonempty (Ω t)] (pub : PMF R₀)
    (aStep : ∀ t : Fin r, X → R₀ → (∀ j : Fin t.1, Ω ⟨j.1, j.2.trans t.2⟩) → PMF (Ω t))
    (bStep : ∀ t : Fin r, Y → R₀ → (∀ j : Fin t.1, Ω ⟨j.1, j.2.trans t.2⟩) → PMF (Ω t))
    (out : R₀ → (∀ t : Fin r, Ω t) → Z) : RandomizedProtocol X Y Z :=
  let e₀ := (Fintype.equivFin R₀).trans (fC (Nat.sub_add_cancel Fintype.card_pos).symm)
  let eΩ := fun t ↦ (Fintype.equivFin (Ω t)).trans (fC (Nat.sub_add_cancel Fintype.card_pos).symm)
  { rounds := r, pubCard := fCard R₀ - 1, msgCard := fun t ↦ fCard (Ω t) - 1, pubCoin := pub.map e₀
    aliceStep := fun t x m₀ h ↦ (aStep t x (e₀.symm m₀) (fun j ↦ (eΩ ⟨j.1,
        j.2.trans t.2⟩).symm (h j))).map (eΩ t)
    bobStep := fun t y m₀ h ↦ (bStep t y (e₀.symm m₀) (fun j ↦ (eΩ ⟨j.1,
        j.2.trans t.2⟩).symm (h j))).map (eΩ t)
    out := fun m₀ tr ↦ out (e₀.symm m₀) (fun t ↦ (eΩ t).symm (tr t)) }
/-- Canonical execution-space equivalence for `RandomizedProtocol.ofFintype`. -/
@[expose] def ofFintypeExecEquiv {R₀ : Type*} {r : ℕ} {Ω : Fin r → Type*} [Fintype R₀] [Nonempty R₀]
    [∀ t, Fintype (Ω t)] [∀ t, Nonempty (Ω t)] (pub : PMF R₀)
    (aStep : ∀ t : Fin r, X → R₀ → (∀ j : Fin t.1, Ω ⟨j.1, j.2.trans t.2⟩) → PMF (Ω t))
    (bStep : ∀ t : Fin r, Y → R₀ → (∀ j : Fin t.1, Ω ⟨j.1, j.2.trans t.2⟩) → PMF (Ω t))
    (out : R₀ → (∀ t : Fin r, Ω t) → Z) : (R₀ × (∀ t : Fin r, Ω t)) ≃
      (ofFintype pub aStep bStep out).Pub × (ofFintype pub aStep bStep out).Transcript :=
  Equiv.prodCongr ((Fintype.equivFin R₀).trans (fC (Nat.sub_add_cancel Fintype.card_pos).symm))
    (Equiv.piCongrRight fun t ↦
        (Fintype.equivFin (Ω t)).trans (fC (Nat.sub_add_cancel Fintype.card_pos).symm))
/-- Pointwise evaluation of `(ofFintype ...).execPMF` along `ofFintypeExecEquiv`. -/
theorem execPMF_ofFintype_apply {R₀ : Type*} {r : ℕ} {Ω : Fin r → Type*} [Fintype R₀]
    [Nonempty R₀] [∀ t, Fintype (Ω t)] [∀ t, Nonempty (Ω t)] (pub : PMF R₀)
    (aStep : ∀ t : Fin r, X → R₀ → (∀ j : Fin t.1, Ω ⟨j.1, j.2.trans t.2⟩) → PMF (Ω t))
    (bStep : ∀ t : Fin r, Y → R₀ → (∀ j : Fin t.1, Ω ⟨j.1, j.2.trans t.2⟩) → PMF (Ω t))
    (out : R₀ → (∀ t : Fin r, Ω t) → Z) (x : X) (y : Y) (r₀ : R₀) (ω : ∀ t : Fin r, Ω t) :
    (ofFintype pub aStep bStep out).execPMF x y (ofFintypeExecEquiv pub aStep bStep out (r₀, ω)) =
      pub r₀ * ∏ t : Fin r,
        (if Even t.1 then aStep t x r₀ (fun j ↦ ω ⟨j.1, j.2.trans t.2⟩) (ω t)
         else bStep t y r₀ (fun j ↦ ω ⟨j.1, j.2.trans t.2⟩) (ω t)) := by
  let e₀ := eFin R₀; let eΩ := fun t ↦ eFin (Ω t); rw [execPMF_apply]
  refine congrArg₂ (· * ·)
    (by change (pub.map e₀) (e₀ r₀) = pub r₀; rw [pMapE, e₀.symm_apply_apply])
    (prodC t ↦ ?_)
  change (if Even t.1 then (aStep t x (e₀.symm (e₀ r₀)) (fun j ↦ (eΩ ⟨j.1, j.2.trans t.2⟩).symm
        (eΩ ⟨j.1, j.2.trans t.2⟩ (ω ⟨j.1, j.2.trans t.2⟩)))).map (eΩ t)
      else (bStep t y (e₀.symm (e₀ r₀)) (fun j ↦ (eΩ ⟨j.1, j.2.trans t.2⟩).symm
        (eΩ ⟨j.1, j.2.trans t.2⟩ (ω ⟨j.1, j.2.trans t.2⟩)))).map (eΩ t)) (eΩ t (ω t)) = _
  split_ifs <;>
    (rw [pMapE, (eΩ t).symm_apply_apply, e₀.symm_apply_apply]
     congr 2; funext j; exact (eΩ _).symm_apply_apply _)
/-- Per-input error preservation formula for `RandomizedProtocol.ofFintype`. -/
theorem inputError_ofFintype {R₀ : Type*} {r : ℕ} {Ω : Fin r → Type*} [Fintype R₀] [Nonempty R₀]
    [∀ t, Fintype (Ω t)] [∀ t, Nonempty (Ω t)] (pub : PMF R₀)
    (aStep : ∀ t : Fin r, X → R₀ → (∀ j : Fin t.1, Ω ⟨j.1, j.2.trans t.2⟩) → PMF (Ω t))
    (bStep : ∀ t : Fin r, Y → R₀ → (∀ j : Fin t.1, Ω ⟨j.1, j.2.trans t.2⟩) → PMF (Ω t))
    (out : R₀ → (∀ t : Fin r, Ω t) → Z) (f : X × Y → Z) (x : X) (y : Y) :
    (ofFintype pub aStep bStep out).inputError f x y =
      ∑ rω : R₀ × (∀ t : Fin r, Ω t), @ite ℝ (out rω.1 rω.2 ≠ f (x, y)) (Classical.propDecidable _)
        (pub rω.1 * ∏ t : Fin r,
          if Even t.1 then aStep t x rω.1 (fun j ↦ rω.2 ⟨j.1, j.2.trans t.2⟩) (rω.2 t)
          else bStep t y rω.1 (fun j ↦ rω.2 ⟨j.1, j.2.trans t.2⟩) (rω.2 t)).toReal 0 := by
  classical let e₀ := eFin R₀; let eΩ := fun t ↦ eFin (Ω t)
  rw [inputError_def, ← (ofFintypeExecEquiv pub aStep bStep out).sum_comp]
  refine Finset.sum_congr rfl fun ⟨r₀, ω⟩ _ ↦ ?_
  have hout : (ofFintype pub aStep bStep out).out (ofFintypeExecEquiv pub aStep bStep out (r₀, ω)).1
      (ofFintypeExecEquiv pub aStep bStep out (r₀, ω)).2 = out r₀ ω := by
    change out (e₀.symm (e₀ r₀)) (fun t ↦ (eΩ t).symm (eΩ t (ω t))) = out r₀ ω
    rw [e₀.symm_apply_apply]; congr 1; funext t; exact (eΩ t).symm_apply_apply _
  rw [hout, execPMF_ofFintype_apply]
/-- Distributional error preservation formula for `RandomizedProtocol.ofFintype`. -/
theorem distError_ofFintype [Fintype X] [Fintype Y] {R₀ : Type*} {r : ℕ} {Ω : Fin r → Type*}
    [Fintype R₀] [Nonempty R₀] [∀ t, Fintype (Ω t)] [∀ t, Nonempty (Ω t)] (pub : PMF R₀)
    (aStep : ∀ t : Fin r, X → R₀ → (∀ j : Fin t.1, Ω ⟨j.1, j.2.trans t.2⟩) → PMF (Ω t))
    (bStep : ∀ t : Fin r, Y → R₀ → (∀ j : Fin t.1, Ω ⟨j.1, j.2.trans t.2⟩) → PMF (Ω t))
    (out : R₀ → (∀ t : Fin r, Ω t) → Z) (f : X × Y → Z) (μ : PMF (X × Y)) :
    (ofFintype pub aStep bStep out).distError f μ = ∑ xy : X × Y, (μ xy).toReal *
      ∑ rω : R₀ × (∀ t : Fin r, Ω t), @ite ℝ (out rω.1 rω.2 ≠ f xy) (Classical.propDecidable _)
        (pub rω.1 * ∏ t : Fin r,
          if Even t.1 then aStep t xy.1 rω.1 (fun j ↦ rω.2 ⟨j.1, j.2.trans t.2⟩) (rω.2 t)
          else bStep t xy.2 rω.1 (fun j ↦ rω.2 ⟨j.1, j.2.trans t.2⟩) (rω.2 t)).toReal 0 := by
  rw [distError_def]; exact sumC xy ↦ by rw [inputError_ofFintype]
private lemma ic_ofFintype_eqv [Fintype X] [Fintype Y] {R₀ R₀' : Type*} {r : ℕ}
    {Ω : Fin r → Type*} [Fintype R₀]
    [Nonempty R₀] [Fintype R₀'] [∀ t, Fintype (Ω t)] [∀ t, Nonempty (Ω t)] (pub : PMF R₀)
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
/-- Transporting an existing `RandomizedProtocol` through `ofFintype` preserves cost. -/
theorem internalInfoCost_ofFintype_self [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z)
    (μ : PMF (X × Y)) :
    (ofFintype P.pubCoin P.aliceStep P.bobStep P.out).internalInfoCost μ =
      P.internalInfoCost μ := by
  rw [ic_ofFintype_eqv _ _ _ _ μ (P.jointPMF μ) (Equiv.refl P.Pub) fun x y m₀ tr ↦ by
    rw [Equiv.refl_apply, jointPMF_apply, execPMF_apply]
    exact congrArg (μ (x, y) * ·) (congrArg (P.pubCoin m₀ * ·) (prodC t ↦ by
      rw [stepPMF_def]; split_ifs <;> rfl)), ← ic_eq_raw]
/-- Exact 2-round input-reveal protocol: Alice sends `x`, Bob sends `f(x, y)`. -/
@[expose] def trivialExact [Fintype X] [Fintype Z] [Nonempty Z] (f : X × Y → Z) :
    RandomizedProtocol X Y Z :=
  ofFintype (R₀ := Unit) (r := 2) (Ω := fun _ : Fin 2 ↦ X ⊕ Z) (PMF.pure ())
    (fun _ x _ _ ↦ PMF.pure (Sum.inl x))
    (fun t y _ h ↦ if ht : t.1 = 1 then match h ⟨0, by omega⟩ with
      | Sum.inl x => PMF.pure (Sum.inr (f (x, y)))
      | Sum.inr _ => PMF.pure (Sum.inr (cArb Z))
    else PMF.pure (Sum.inr (cArb Z)))
    (fun _ tr ↦ match tr 1 with | Sum.inr z => z | Sum.inl _ => cArb Z)
/-- `trivialExact f` has zero error on every input. -/
@[simp, grind =] theorem inputError_trivialExact [Fintype X] [Fintype Z] [Nonempty Z]
    (f : X × Y → Z) (x : X) (y : Y) : (trivialExact f).inputError f x y = 0 := by
  classical rw [trivialExact, inputError_ofFintype]
  refine Finset.sum_eq_zero fun ⟨_, ω⟩ _ ↦ ?_; split_ifs with hne; swap; · rfl
  rw [Fin.prod_univ_two, iteL (by decide : Even (0 : Fin 2).1),
      iteR (by decide : ¬ Even (1 : Fin 2).1)]
  by_cases hx : ω 0 = Sum.inl x
  · have hy : ω 1 ≠ Sum.inr (f (x, y)) := fun hy ↦ hne (by
      change (match ω 1 with | Sum.inr z => z | Sum.inl _ => cArb Z) = f (x, y); rw [hy])
    simp [hx, pPureA, iteR hy]
  · simp [pPureA, iteR hx]
/-- `trivialExact f` has internal information cost at most $\log_2 |X| + \log_2 |Z|$. -/
theorem internalInfoCost_trivialExact_le [Fintype X] [Fintype Y] [Nonempty X] [Fintype Z]
    [Nonempty Z] (f : X × Y → Z) (μ : PMF (X × Y)) :
    (trivialExact f).internalInfoCost μ ≤
      Real.logb 2 (Fintype.card X) + Real.logb 2 (Fintype.card Z) := by
  classical let detTr : X × Y → (Fin 2 → X ⊕ Z) := fun xy t ↦
      if t = 0 then Sum.inl xy.1 else Sum.inr (f xy)
  rw [trivialExact, ic_ofFintype_eqv _ _ _ _ μ (μ.map fun xy ↦ (xy.1, xy.2, (),
      detTr xy)) (Equiv.refl Unit) fun x y u ω ↦ ?_]
  · rw [rIC]; simp only [pMapC, Function.comp_def]
    rw [eInj μ (fun xy ↦ (xy.1, xy.2)) (fun xy ↦ (detTr xy, xy.2, ()))
        (iInv _ (fun v ↦ (match v.1 0 with | Sum.inl x => x | _ => cArb X, v.2.1))
          fun ⟨_, _⟩ ↦ by simp [detTr]),
      eInj μ Prod.snd (fun y ↦ (y, ())) (fun _ _ h ↦ (pmi h).1),
      eInj μ (fun xy ↦ (xy.1, xy.2)) (fun xy ↦ (detTr xy, xy.1, xy.2, ())) (iInv _ (fun v ↦ (v.2.1,
          v.2.2.1)) fun ⟨_, _⟩ ↦ rfl),
      eInj μ (fun xy ↦ (xy.1, xy.2)) (fun xy ↦ (xy.1, xy.2, ())) (iInv _ (fun v ↦ (v.1,
          v.2.1)) fun ⟨_, _⟩ ↦ rfl),
      eInj μ (fun xy ↦ (f xy, xy.1))
        (fun zx ↦ (fun t : Fin 2 ↦ if t = 0 then Sum.inl zx.2 else Sum.inr zx.1, zx.2, ()))
        (iInv _ (fun v ↦ (match v.1 1 with | Sum.inr z => z | _ => cArb Z, v.2.1))
          fun ⟨_, _⟩ ↦ by simp),
      eInj μ Prod.fst (fun x ↦ (x, ())) (fun _ _ h ↦ (pmi h).1)]
    have hX := condEnt_le_log_card μ Prod.fst Prod.snd; have hZ := condEnt_le_log_card μ f Prod.fst
    calc (rL2)⁻¹ * _ ≤ (rL2)⁻¹ * (rL (fCard X) + rL (fCard Z)) := mLeL (by linarith) hL2nn
      _ = Real.logb 2 (fCard X) + Real.logb 2 (fCard Z) := by
          simp [Real.logb, div_eq_inv_mul, mul_add]
  · simp only [Equiv.refl_apply, PMF.pure_apply_self, one_mul, Fin.prod_univ_two,
      iteL (by decide : Even (0 : Fin 2).1), iteR (by decide : ¬ Even (1 : Fin 2).1)]
    by_cases hω : ω = detTr (x, y)
    · subst hω; rw [pMapU μ _ _ (x, y) rfl fun ⟨_, _⟩ h ↦ by aesop]; simp [detTr]
    · cases u; rw [pMapZ μ _ (x, y, (), ω) fun _ h ↦ hω (by aesop)]
      by_cases h0w : ω 0 = Sum.inl x
      · have h1w : ω 1 ≠ Sum.inr (f (x, y)) := fun h1w ↦
          hω (funext fun t ↦ by fin_cases t <;> simp [detTr, h0w, h1w])
        simp [h0w, pPureA, iteR h1w]
      · simp [pPureA, iteR h0w]
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
      change (match ω 0, ω 1 with | Sum.inl x, Sum.inr y => f (x, y) | _, _ => _) = f (x, y)
      rw [hx, hy])
    simp [pPureA, iteR hy]
  · simp [pPureA, iteR hx]
end Execution
end RandomizedProtocol

/-! ### Distributional, Max-Distributional, and Worst-Case Information Complexity -/

section ComplexityFunctionals
variable {X : Type u} {Y : Type v} {Z : Type w}
open RandomizedProtocol in
private lemma distErr_rev [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] (f : X × Y → Z)
    (μ : PMF (X × Y)) : (inRev f).distError f μ = 0 := by rw [distError_def]; simp [inputErr_rev]
/-- Distributional information complexity $\mathrm{IC}_\mu(f, \varepsilon)$. -/
@[expose] def distInfoComplexity [Fintype X] [Fintype Y] (f : X × Y → Z) (μ : PMF (X × Y))
    (ε : ℝ) : ℝ :=
  sInf { c : ℝ | ∃ P : RandomizedProtocol X Y Z, P.distError f μ ≤ ε ∧ P.internalInfoCost μ = c }
lemma distInfoComplexity_def [Fintype X] [Fintype Y] (f : X × Y → Z) (μ : PMF (X × Y)) (ε : ℝ) :
    distInfoComplexity f μ ε = sInf { c : ℝ | ∃ P : RandomizedProtocol X Y Z,
      P.distError f μ ≤ ε ∧ P.internalInfoCost μ = c } := rfl
/-- Max-distributional information complexity $\mathrm{IC}_D(f, \varepsilon)$. -/
@[expose] def maxDistInfoComplexity [Fintype X] [Fintype Y] (f : X × Y → Z) (ε : ℝ) : ℝ :=
  sSup (Set.range fun μ : PMF (X × Y) ↦ distInfoComplexity f μ ε)
lemma maxDistInfoComplexity_def [Fintype X] [Fintype Y] (f : X × Y → Z) (ε : ℝ) :
    maxDistInfoComplexity f ε = sSup (Set.range fun μ : PMF (X × Y) ↦ distInfoComplexity f μ ε) :=
  rfl
/-- Worst-case internal information cost $\sup_\mu I_2(\Pi; \mu)$. -/
@[expose] def worstCaseInfoCost [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z) : ℝ :=
  sSup (Set.range fun μ : PMF (X × Y) ↦ P.internalInfoCost μ)
lemma worstCaseInfoCost_def [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z) :
    worstCaseInfoCost P = sSup (Set.range fun μ : PMF (X × Y) ↦ P.internalInfoCost μ) := rfl
/-- Worst-case interactive information complexity $\mathrm{IC}(f, \varepsilon)$. -/
@[expose] def infoComplexity [Fintype X] [Fintype Y] (f : X × Y → Z) (ε : ℝ) : ℝ :=
  sInf { c : ℝ | ∃ P : RandomizedProtocol X Y Z,
    (∀ x y, P.inputError f x y ≤ ε) ∧ worstCaseInfoCost P = c }
lemma infoComplexity_def [Fintype X] [Fintype Y] (f : X × Y → Z) (ε : ℝ) :
    infoComplexity f ε = sInf { c : ℝ | ∃ P : RandomizedProtocol X Y Z,
      (∀ x y, P.inputError f x y ≤ ε) ∧ worstCaseInfoCost P = c } := rfl
/-- Worst-case internal information cost is nonnegative. -/
theorem worstCaseInfoCost_nonneg [Fintype X] [Fintype Y] (P : RandomizedProtocol X Y Z) :
    0 ≤ worstCaseInfoCost P := Real.sSup_nonneg fun _ ⟨μ, hμ⟩ ↦ hμ ▸ P.internalInfoCost_nonneg μ
/-- Internal information cost at any prior `μ` is bounded by `worstCaseInfoCost P`. -/
theorem internalInfoCost_le_worstCaseInfoCost [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (P : RandomizedProtocol X Y Z) (μ : PMF (X × Y)) :
    P.internalInfoCost μ ≤ worstCaseInfoCost P :=
  le_csSup ⟨Real.logb 2 (fCard X * fCard Y), fun _ ⟨ν,
      hν⟩ ↦ hν ▸ P.internalInfoCost_le_log_card ν⟩ ⟨μ, rfl⟩
/-- Upper bound criterion for `worstCaseInfoCost P`. -/
theorem worstCaseInfoCost_le [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (P : RandomizedProtocol X Y Z) {c : ℝ} (h : ∀ μ : PMF (X × Y), P.internalInfoCost μ ≤ c) :
    worstCaseInfoCost P ≤ c :=
  csSup_le ⟨P.internalInfoCost (PMF.pure (cArb _)), ⟨_, rfl⟩⟩ fun _ ⟨μ, hμ⟩ ↦ hμ ▸ h μ
/-- Distributional information complexity is nonnegative. -/
theorem distInfoComplexity_nonneg [Fintype X] [Fintype Y] (f : X × Y → Z) (μ : PMF (X × Y))
    (ε : ℝ) : 0 ≤ distInfoComplexity f μ ε :=
  Real.sInf_nonneg fun _ ⟨P, _, hP⟩ ↦ hP ▸ P.internalInfoCost_nonneg μ
/-- Any protocol with distributional error at most `ε` upper-bounds `distInfoComplexity f μ ε`. -/
theorem distInfoComplexity_le_of_distError_le [Fintype X] [Fintype Y] {f : X × Y → Z}
    {μ : PMF (X × Y)} {ε : ℝ} {P : RandomizedProtocol X Y Z} (herr : P.distError f μ ≤ ε) :
    distInfoComplexity f μ ε ≤ P.internalInfoCost μ :=
  csInf_le ⟨0, fun _ ⟨Q, _, hQ⟩ ↦ hQ ▸ Q.internalInfoCost_nonneg μ⟩ ⟨P, herr, rfl⟩
/-- Distributional information complexity is bounded by $\log_2 |X| + \log_2 |Z|$. -/
theorem distInfoComplexity_le_log_card [Fintype X] [Fintype Y] [Nonempty X]
    [Fintype Z] [Nonempty Z] (f : X × Y → Z) (μ : PMF (X × Y)) {ε : ℝ} (hε : 0 ≤ ε) :
    distInfoComplexity f μ ε ≤ Real.logb 2 (Fintype.card X) + Real.logb 2 (Fintype.card Z) :=
  (distInfoComplexity_le_of_distError_le (P := RandomizedProtocol.trivialExact f) (by
    rw [RandomizedProtocol.distError_def]; simp [hε])).trans
      (RandomizedProtocol.internalInfoCost_trivialExact_le f μ)
/-- Distributional information complexity is antitone in `ε`. -/
theorem distInfoComplexity_antitone [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (f : X × Y → Z) (μ : PMF (X × Y)) {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (h : ε₁ ≤ ε₂) :
    distInfoComplexity f μ ε₂ ≤ distInfoComplexity f μ ε₁ :=
  csInf_le_csInf ⟨0, fun _ ⟨P, _, hP⟩ ↦ hP ▸ P.internalInfoCost_nonneg μ⟩
    ⟨_, RandomizedProtocol.inRev f, by simpa [distErr_rev], rfl⟩ fun _ ⟨P, herr, hP⟩ ↦ ⟨P,
        herr.trans h, hP⟩
/-- Max-distributional information complexity is nonnegative. -/
theorem maxDistInfoComplexity_nonneg [Fintype X] [Fintype Y] (f : X × Y → Z) (ε : ℝ) :
    0 ≤ maxDistInfoComplexity f ε := Real.sSup_nonneg fun _ ⟨μ,
        hμ⟩ ↦ hμ ▸ distInfoComplexity_nonneg f μ ε
/-- Distributional information complexity at `μ` is bounded by `maxDistInfoComplexity f ε`. -/
theorem distInfoComplexity_le_maxDistInfoComplexity [Fintype X] [Fintype Y] [Nonempty X]
    [Nonempty Y] (f : X × Y → Z) (μ : PMF (X × Y)) {ε : ℝ} (hε : 0 ≤ ε) :
    distInfoComplexity f μ ε ≤ maxDistInfoComplexity f ε :=
  le_csSup ⟨Real.logb 2 (fCard X * fCard Y), fun _ ⟨ν, hν⟩ ↦ hν ▸
    (distInfoComplexity_le_of_distError_le (P := RandomizedProtocol.inRev f)
      (by simpa [distErr_rev])).trans ((RandomizedProtocol.inRev f).internalInfoCost_le_log_card
          ν)⟩ ⟨μ, rfl⟩
/-- Max-distributional information complexity is bounded by $\log_2 |X| + \log_2 |Z|$. -/
theorem maxDistInfoComplexity_le_log_card [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    [Fintype Z] [Nonempty Z] (f : X × Y → Z) {ε : ℝ} (hε : 0 ≤ ε) :
    maxDistInfoComplexity f ε ≤ Real.logb 2 (Fintype.card X) + Real.logb 2 (Fintype.card Z) :=
  csSup_le ⟨_, ⟨PMF.pure (cArb _), rfl⟩⟩ fun _ ⟨μ, hμ⟩ ↦ hμ ▸ distInfoComplexity_le_log_card f μ hε
/-- Max-distributional information complexity is antitone in `ε`. -/
theorem maxDistInfoComplexity_antitone [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (f : X × Y → Z) {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (h : ε₁ ≤ ε₂) :
    maxDistInfoComplexity f ε₂ ≤ maxDistInfoComplexity f ε₁ :=
  csSup_le ⟨_, ⟨PMF.pure (cArb _), rfl⟩⟩ fun _ ⟨μ, hμ⟩ ↦
    hμ ▸ (distInfoComplexity_antitone f μ hε₁ h).trans (distInfoComplexity_le_maxDistInfoComplexity
        f μ hε₁)
/-- Worst-case information complexity is nonnegative. -/
theorem infoComplexity_nonneg [Fintype X] [Fintype Y] (f : X × Y → Z) (ε : ℝ) :
    0 ≤ infoComplexity f ε := Real.sInf_nonneg fun _ ⟨P, _, hP⟩ ↦ hP ▸ worstCaseInfoCost_nonneg P
/-- Any protocol with per-input error at most `ε` upper-bounds `infoComplexity f ε`. -/
theorem infoComplexity_le_of_inputError_le [Fintype X] [Fintype Y] {f : X × Y → Z} {ε : ℝ}
    {P : RandomizedProtocol X Y Z} (herr : ∀ x y, P.inputError f x y ≤ ε) :
    infoComplexity f ε ≤ worstCaseInfoCost P :=
  csInf_le ⟨0, fun _ ⟨Q, _, hQ⟩ ↦ hQ ▸ worstCaseInfoCost_nonneg Q⟩ ⟨P, herr, rfl⟩
/-- Worst-case information complexity is bounded by $\log_2 |X| + \log_2 |Z|$. -/
theorem infoComplexity_le_log_card [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    [Fintype Z] [Nonempty Z] (f : X × Y → Z) {ε : ℝ} (hε : 0 ≤ ε) :
    infoComplexity f ε ≤ Real.logb 2 (Fintype.card X) + Real.logb 2 (Fintype.card Z) :=
  (infoComplexity_le_of_inputError_le (P := RandomizedProtocol.trivialExact f) fun _ _ ↦
      by simp [hε]).trans
    (worstCaseInfoCost_le _ fun μ ↦ RandomizedProtocol.internalInfoCost_trivialExact_le f μ)
/-- Worst-case information complexity is antitone in `ε`. -/
theorem infoComplexity_antitone [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (f : X × Y → Z) {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (h : ε₁ ≤ ε₂) :
    infoComplexity f ε₂ ≤ infoComplexity f ε₁ :=
  csInf_le_csInf ⟨0, fun _ ⟨P, _, hP⟩ ↦ hP ▸ worstCaseInfoCost_nonneg P⟩
    ⟨_, RandomizedProtocol.inRev f,
      fun x y ↦ by rw [RandomizedProtocol.inputErr_rev]; exact hε₁, rfl⟩
    fun _ ⟨P, herr, hP⟩ ↦ ⟨P, fun x y ↦ (herr x y).trans h, hP⟩
/-- Weak minimax inequality: $\mathrm{IC}_D(f, \varepsilon) \le \mathrm{IC}(f, \varepsilon)$. -/
theorem maxDistInfoComplexity_le_infoComplexity [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (f : X × Y → Z) {ε : ℝ} (hε : 0 ≤ ε) : maxDistInfoComplexity f ε ≤ infoComplexity f ε := by
  refine le_csInf ⟨_, RandomizedProtocol.inRev f,
      fun x y ↦ by rw [RandomizedProtocol.inputErr_rev]; exact hε, rfl⟩ ?_
  rintro c ⟨P, herr, rfl⟩
  refine csSup_le ⟨_, ⟨PMF.pure (cArb _), rfl⟩⟩ fun _ ⟨μ, hμ⟩ ↦ ?_
  rw [← hμ]
  exact (distInfoComplexity_le_of_distError_le ((sumLe fun xy _ ↦
      mLeL (herr xy.1 xy.2) eTRN).trans_eq
    (by rw [← sumM, pSum1R, one_mul]))).trans (internalInfoCost_le_worstCaseInfoCost P μ)
end ComplexityFunctionals

end

end CslibFrontier.Computability.Communication
