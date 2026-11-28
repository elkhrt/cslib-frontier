/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.NOF.PatternTensor
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multiparty NOF Set Disjointness Lower Bounds and Nondeterministic Separation

This module defines `k`-party Set Intersection (`nofSetInter`) and Set Disjointness (`nofDisj`),
proves player-local protocol pullback invariance (`comapProtocol`, `ecomplexityFun_comap_not_le`),
embeds disjunction pattern tensors into multiparty disjointness via a player-local gadget
(`disjEmbedPlayer`), establishes explicit, uniform-in-`k`, and asymptotic `Ω(n^{1/(k+1)} / 2^{2^k})`
lower bounds for public-coin randomized NOF protocols computing `nofDisj`, and exhibits an
exponential separation between nondeterministic covers and randomized NOF communication complexity.

## Main definitions

* `nofSetInter`, `nofDisj`: `k`-party Set Intersection and Set Disjointness on `BitString n`.
* `comapProtocol`, `mapOutputProtocol`: player-local input pullback and output post-composition for
  NOF protocols.
* `disjEmbedPlayer`: player-local gadget embedding pattern tensors of `OR_m` into `¬nofDisj`.
* `setInterNondetCover`: explicit size-`n` nondeterministic cylinder-intersection cover.

## Main results

* `not_nofDisj_disjEmbed_eq_or_patternProj`: exact subtensor reduction from `OR_m` pattern tensors.
* `nofDisj_publicCoin_explicit_lower_bound`, `nofDisj_publicCoin_uniform_lower_bound`,
  `nofDisj_publicCoin_isBigO`: public-coin randomized NOF lower bounds for `nofDisj`.
* `nof_nondet_vs_randomized_separation`: exponential separation between nondeterministic and
  randomized NOF communication complexity.
-/

public section

open scoped BigOperators
open Cslib Cslib.BitString Cslib.Communication.NOF

open CslibFrontier.Computability.QueryComplexity
namespace CslibFrontier.Computability.Communication.NOF

section DisjointnessDefs

/-- **`k`-Party Set Intersection `SET_INTER_{k, n}`**:
outputs `true` iff there is a coordinate `idx: Fin n` where every player holds `true`. -/
def nofSetInter (k n : ℕ) (x : Fin k → BitString n) : Bool :=
  decide (∃ idx : Fin n, ∀ p : Fin k, x p idx = true)

/-- **`k`-Party Set Disjointness `DISJ_{k, n} = ¬SET_INTER_{k, n}`**). -/
def nofDisj (k n : ℕ) (x : Fin k → BitString n) : Bool :=
  !(nofSetInter k n x)

/-- Pull back a deterministic NOF protocol along player-local input maps `g: ∀ i, X i → Y i`. -/
def comapProtocol {ι : Type*} {X Y : ι → Type*} {Z : Type*}
    (g : ∀ i, X i → Y i) : Protocol Y Z → Protocol X Z
  | .output z => .output z
  | .speak i send p₀ p₁ =>
    .speak i (fun v ↦ send (fun j ↦ g j.1 (v j))) (comapProtocol g p₀) (comapProtocol g p₁)

/-- Pulling back along player-local maps preserves protocol depth. -/
theorem depth_comapProtocol {ι : Type*} {X Y : ι → Type*} {Z : Type*}
    (g : ∀ i, X i → Y i) (p : Protocol Y Z) :
    (comapProtocol g p).depth = p.depth := by
  induction p with
  | output _ => rfl
  | speak _ _ _ _ ih₀ ih₁ => simp [comapProtocol, Protocol.depth, ih₀, ih₁]

/-- Running a pulled-back protocol evaluates the original protocol on the mapped inputs. -/
theorem run_comapProtocol {ι : Type*} {X Y : ι → Type*} {Z : Type*}
    (g : ∀ i, X i → Y i) (p : Protocol Y Z) (x : ∀ i, X i) :
    (comapProtocol g p).run x = p.run (fun i ↦ g i (x i)) := by
  induction p with
  | output _ => rfl
  | speak i send p₀ p₁ ih₀ ih₁ =>
    simp only [comapProtocol, Protocol.run]
    have hview : (fun j : {j : ι // j ≠ i} ↦ g j.1 (view i x j)) =
        view i (fun j ↦ g j (x j)) := rfl
    rw [hview]
    cases send (view i (fun j ↦ g j (x j)))
    · exact ih₀
    · exact ih₁

/-- Post-compose a deterministic NOF protocol's output with `h: Z → W`. -/
def mapOutputProtocol {ι : Type*} {X : ι → Type*} {Z W : Type*}
    (h : Z → W) : Protocol X Z → Protocol X W
  | .output z => .output (h z)
  | .speak i send p₀ p₁ => .speak i send (mapOutputProtocol h p₀) (mapOutputProtocol h p₁)

/-- Post-composing a protocol's output preserves depth. -/
theorem depth_mapOutputProtocol {ι : Type*} {X : ι → Type*} {Z W : Type*}
    (h : Z → W) (p : Protocol X Z) :
    (mapOutputProtocol h p).depth = p.depth := by
  induction p with
  | output _ => rfl
  | speak _ _ _ _ ih₀ ih₁ => simp [mapOutputProtocol, Protocol.depth, ih₀, ih₁]

/-- Post-composing a protocol's output transforms `Protocol.run` pointwise. -/
theorem run_mapOutputProtocol {ι : Type*} {X : ι → Type*} {Z W : Type*}
    (h : Z → W) (p : Protocol X Z) (x : ∀ i, X i) :
    (mapOutputProtocol h p).run x = h (p.run x) := by
  induction p with
  | output _ => rfl
  | speak i send p₀ p₁ ih₀ ih₁ =>
    simp only [mapOutputProtocol, Protocol.run]
    cases send (view i x)
    · exact ih₀
    · exact ih₁

/-- Pulling back along player-local maps and negating the Boolean output does not increase
public-coin NOF communication complexity. -/
theorem ecomplexityFun_comap_not_le {ι : Type*} {X Y : ι → Type*}
    (g : ∀ i, X i → Y i) (f : (∀ i, Y i) → Bool) (ε : ℝ) :
    PublicCoin.ecomplexityFun ε (fun x ↦ !f (fun i ↦ g i (x i))) ≤
      PublicCoin.ecomplexityFun ε f := by
  change PublicCoin.ecomplexity ε (fun x b ↦ (!f (fun i ↦ g i (x i))) = b) Set.univ ≤
    PublicCoin.ecomplexity ε (fun y b ↦ f y = b) Set.univ
  rw [PublicCoin.le_ecomplexity_iff]
  intro μ hsol
  let tr : Protocol Y Bool → Protocol X Bool := fun p ↦ mapOutputProtocol (! ·) (comapProtocol g p)
  let μ' : PublicCoin X Bool := μ.map tr
  have hsol' : μ'.Solves ε (fun x b ↦ (!f (fun i ↦ g i (x i))) = b) Set.univ := by
    intro x _
    have herr_eq : μ'.errorProb (fun x b ↦ (!f (fun i ↦ g i (x i))) = b) x =
        μ.errorProb (fun y b ↦ f y = b) (fun i ↦ g i (x i)) := by
      change (μ'.toOuterMeasure {P | ¬ (!f (fun i ↦ g i (x i))) = P.run x}).toReal =
        (μ.toOuterMeasure {Q | ¬ f (fun i ↦ g i (x i)) = Q.run (fun i ↦ g i (x i))}).toReal
      rw [PMF.toOuterMeasure_map_apply]
      congr 2
      ext Q
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, tr, run_mapOutputProtocol, run_comapProtocol]
      cases f (fun i ↦ g i (x i)) <;> cases Q.run (fun i ↦ g i (x i)) <;> simp
    rw [herr_eq]
    exact hsol (fun i ↦ g i (x i)) (Set.mem_univ _)
  have hdepth' : μ'.depth ≤ μ.depth := by
    rw [PublicCoin.depth_le_iff]
    intro P hP
    rw [PMF.mem_support_map_iff] at hP
    rcases hP with ⟨Q, hQ, rfl⟩
    have hd : (tr Q).depth = Q.depth := by
      simp [tr, depth_mapOutputProtocol, depth_comapProtocol]
    rw [hd]
    exact PublicCoin.depth_le_depth hQ
  exact (PublicCoin.ecomplexity_le_depth hsol').trans hdepth'

/-- **Player-Local Gadget Embedding `PatternSpace r m M → BitString n`**:
given an injection `emb: (Fin m × (Fin r → Fin M)) ↪ Fin n`, embeds the pattern tensor of `OR_m`
as an exact subtensor of `¬DISJ_{r+1, n}`. -/
noncomputable def disjEmbedPlayer {r m M n : ℕ}
    (emb : (Fin m × (Fin r → Fin M)) ↪ Fin n) :
    ∀ p : Fin (r + 1), PatternSpace r m M p → BitString n := by
  classical
  exact fun p zp idx ↦
    if h : ∃ it : Fin m × (Fin r → Fin M), emb it = idx then
      let it := Classical.choose h
      Fin.cases
        (fun x0 : PatternSpace r m M 0 ↦ patternPlayer0Equiv r m M x0 it.1 it.2)
        (fun (j : Fin r) (yj : PatternSpace r m M j.succ) ↦
          decide (it.2 j = patternSuccEquiv r m M j yj it.1))
        p zp
    else
      false

/-- **Exact Subtensor Identity**):
`(!nofDisj (r + 1) n (disjEmbedPlayer emb z)) = threshold m 1 (patternProj z)`. -/
theorem not_nofDisj_disjEmbed_eq_or_patternProj {r m M n : ℕ}
    (emb : (Fin m × (Fin r → Fin M)) ↪ Fin n)
    (z : ∀ p : Fin (r + 1), PatternSpace r m M p) :
    (!nofDisj (r + 1) n (fun p ↦ disjEmbedPlayer emb p (z p))) =
      threshold m 1 (patternProj z) := by
  classical
  have hthresh_iff : ∀ w : BitString m, threshold m 1 w = true ↔ ∃ i : Fin m, w i = true := by
    intro w
    rw [threshold_apply, decide_eq_true_eq, weight]
    constructor
    · intro h
      have hne : (Finset.univ.filter fun i : Fin m ↦ w i = true).Nonempty :=
        Finset.card_pos.mp (by omega)
      obtain ⟨i, hi⟩ := hne
      exact ⟨i, (Finset.mem_filter.mp hi).2⟩
    · rintro ⟨i, hi⟩
      exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  unfold nofDisj nofSetInter
  rw [Bool.not_not]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, hthresh_iff]
  constructor
  · rintro ⟨idx, hall⟩
    have h0 := hall 0
    dsimp only [disjEmbedPlayer] at h0
    by_cases hex : ∃ it : Fin m × (Fin r → Fin M), emb it = idx
    · rw [dite_eq_left hex, Fin.cases_zero] at h0
      let it := Classical.choose hex
      have h_x0 : patternPlayer0Equiv r m M (z 0) it.1 it.2 = true := h0
      have ht_eq : it.2 = fun j : Fin r ↦ patternSelector z j it.1 := by
        funext j
        have hj := hall j.succ
        dsimp only [disjEmbedPlayer] at hj
        rw [dite_eq_left hex, Fin.cases_succ, decide_eq_true_eq] at hj
        exact hj
      rw [ht_eq] at h_x0
      exact ⟨it.1, h_x0⟩
    · rw [dite_eq_right hex] at h0
      cases h0
  · rintro ⟨i₀, hi₀⟩
    let t₀ : Fin r → Fin M := fun j ↦ patternSelector z j i₀
    refine ⟨emb (i₀, t₀), fun p ↦ ?_⟩
    dsimp only [disjEmbedPlayer]
    have hex : ∃ it : Fin m × (Fin r → Fin M), emb it = emb (i₀, t₀) := ⟨(i₀, t₀), rfl⟩
    rw [dite_eq_left hex]
    have hchoose : Classical.choose hex = (i₀, t₀) := emb.injective (Classical.choose_spec hex)
    refine Fin.cases ?_ ?_ p
    · rw [Fin.cases_zero, hchoose]
      exact hi₀
    · intro j
      rw [Fin.cases_succ, hchoose]
      simp [t₀, patternSelector_eq]

end DisjointnessDefs

section DisjointnessLowerBounds

/-- **finite explicit form**:
For `k = r + 1 ≥ 2` (`1 ≤ r`), `1 ≤ d`, `n ≥ 6 * (36 * r * 2^{2^r})^r * d^{r + 2}`, and
`0 ≤ ε ≤ 1 / 4`, if `R^{r+1}_ε(DISJ_{r+1, n}) ≤ c`, then `d ≤ (c + 2) * 2^r`. -/
theorem nofDisj_publicCoin_explicit_lower_bound {r d n c : ℕ} {ε : ℝ}
    (hr : 1 ≤ r) (hd : 1 ≤ d)
    (hn : 6 * (36 * r * 2 ^ (2 ^ r)) ^ r * d ^ (r + 2) ≤ n)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (hcomp : PublicCoin.ecomplexityFun ε (nofDisj (r + 1) n) ≤ c) :
    d ≤ (c + 2) * 2 ^ r := by
  let m : ℕ := 6 * d ^ 2
  let M : ℕ := 36 * r * 2 ^ (2 ^ r) * d
  have hm1 : 1 ≤ m := by dsimp only [m]; nlinarith
  have hM_pos : 0 < M := by
    dsimp only [M]
    have h2 : 0 < 2 ^ (2 ^ r) := pow_pos (by omega) _
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) hr) h2) hd
  have _ : NeZero M := ⟨Nat.ne_of_gt hM_pos⟩
  have _ : Nontrivial (Fin (r + 1)) := ⟨⟨0, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩⟩
 -- Nisan–Szegedy lower bound `d ≤ deg_5(OR_m)`:
  have hd_le_deg : d ≤ alphaApproxDeg 5 (threshold m 1) := by
    have hns := nisan_szegedy_alphaApproxDeg_five_or m
    have hsq : d ^ 2 ≤ alphaApproxDeg 5 (threshold m 1) ^ 2 := by
      dsimp only [m] at hns ⊢; omega
    nlinarith
  have hdeg1 : 1 ≤ alphaApproxDeg 5 (threshold m 1) := le_trans hd hd_le_deg
 -- Verify `M ≥ 2 * exp 1 * r * 2^{2^r} * m / deg_5(OR_m)`:
  have hM_ge : 2 * Real.exp 1 * (r : ℝ) * (2 : ℝ) ^ (2 ^ r) * (m : ℝ) /
      (alphaApproxDeg 5 (threshold m 1) : ℝ) ≤ (M : ℝ) := by
    have hdeg_pos : (0 : ℝ) < alphaApproxDeg 5 (threshold m 1) := by exact_mod_cast hdeg1
    have hd_leR : (d : ℝ) ≤ alphaApproxDeg 5 (threshold m 1) := by exact_mod_cast hd_le_deg
    have hexp_lt : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    rw [div_le_iff₀ hdeg_pos]
    calc 2 * Real.exp 1 * (r : ℝ) * (2 : ℝ) ^ (2 ^ r) * (m : ℝ)
        ≤ 2 * 3 * (r : ℝ) * (2 : ℝ) ^ (2 ^ r) * (6 * (d : ℝ) ^ 2) := by
          have hmR : (m : ℝ) = 6 * (d : ℝ) ^ 2 := by dsimp only [m]; push_cast; ring
          rw [hmR]
          have hnn : 0 ≤ (r : ℝ) * (2 : ℝ) ^ (2 ^ r) * (6 * (d : ℝ) ^ 2) := by positivity
          nlinarith
      _ = (M : ℝ) * (d : ℝ) := by
          dsimp only [M]; push_cast; ring
      _ ≤ (M : ℝ) * (alphaApproxDeg 5 (threshold m 1) : ℝ) :=
          mul_le_mul_of_nonneg_left hd_leR (Nat.cast_nonneg M)
 -- Construct injection `emb: Fin m × (Fin r → Fin M) ↪ Fin n`:
  have hmM_le : m * M ^ r ≤ n := by
    have heq : m * M ^ r = 6 * (36 * r * 2 ^ (2 ^ r)) ^ r * d ^ (r + 2) := by
      dsimp only [m, M]
      rw [mul_pow]
      ring
    rwa [heq]
  have hcard_le : Fintype.card (Fin m × (Fin r → Fin M)) ≤ Fintype.card (Fin n) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_pi, Finset.prod_const,
      Finset.card_univ]
    exact hmM_le
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard_le
 -- Pull back complexity from `DISJ_{r+1, n}` to `OR_m ∘ patternProj`:
  have hpull : PublicCoin.ecomplexityFun ε (fun z : ∀ p : Fin (r + 1), PatternSpace r m M p ↦
      threshold m 1 (patternProj z)) ≤ c := by
    have hfun : (fun z : ∀ p : Fin (r + 1), PatternSpace r m M p ↦
        !nofDisj (r + 1) n (fun p ↦ disjEmbedPlayer emb p (z p))) =
        fun z ↦ threshold m 1 (patternProj z) :=
      funext (not_nofDisj_disjEmbed_eq_or_patternProj emb)
    rw [← hfun]
    exact (ecomplexityFun_comap_not_le (disjEmbedPlayer emb) (nofDisj (r + 1) n) ε).trans hcomp
 -- Combine the lifting theorem (`α = 2, α₀ = 5`) and the duality theorem (`ε ≤ 1/4`):
  have hαε : 1 / (1 - 2 * ε) ≤ (2 : ℝ) := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - 2 * ε)]; linarith
  have hupper := muAlpha_le_of_publicCoin_ecomplexityFun_le hε0 (by linarith) hαε hpull
  have hlower := muAlpha_patternTensor_ge_exp hr hM_pos (f := threshold m 1) (α := 2) (α₀ := 5)
    (by norm_num) (by norm_num) hdeg1 hM_ge
  have hsign_eq : signTensor (fun z : ∀ p : Fin (r + 1), PatternSpace r m M p ↦
      threshold m 1 (patternProj z)) =
      patternTensor r m M (fun w ↦ signVal (threshold m 1 w)) := rfl
  rw [hsign_eq] at hupper
 -- `(1/2) * 2^{deg/2^r} ≤ muAlpha 2 A ≤ 2 * 2^c`, so `2^{d/2^r} ≤ 2^{c + 2}`:
  have hfrac : ((5 : ℝ) - 2) / (5 + 1) = 1 / 2 := by norm_num
  rw [hfrac] at hlower
  have hcomb : (1 / 2 : ℝ) * (2 : ℝ) ^ ((alphaApproxDeg 5 (threshold m 1) : ℝ) / (2 ^ r : ℝ)) ≤
      (2 : ℝ) * (2 : ℝ) ^ c :=
    hlower.trans (hupper.trans (mul_le_mul_of_nonneg_right hαε (by positivity)))
  have hpow_le : (2 : ℝ) ^ ((d : ℝ) / (2 ^ r : ℝ)) ≤ (2 : ℝ) ^ ((c + 2 : ℕ) : ℝ) := by
    have hmon : (2 : ℝ) ^ ((d : ℝ) / (2 ^ r : ℝ)) ≤
        (2 : ℝ) ^ ((alphaApproxDeg 5 (threshold m 1) : ℝ) / (2 ^ r : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      exact div_le_div_of_nonneg_right (by exact_mod_cast hd_le_deg) (by positivity)
    calc (2 : ℝ) ^ ((d : ℝ) / (2 ^ r : ℝ))
        ≤ (2 : ℝ) ^ ((alphaApproxDeg 5 (threshold m 1) : ℝ) / (2 ^ r : ℝ)) := hmon
      _ ≤ 4 * (2 : ℝ) ^ c := by linarith
      _ = (2 : ℝ) ^ ((c + 2 : ℕ) : ℝ) := by
          rw [Real.rpow_natCast, pow_add]; norm_num; ring
  have hexp_le : (d : ℝ) / (2 ^ r : ℝ) ≤ ((c + 2 : ℕ) : ℝ) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hpow_le
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 ^ r : ℝ))] at hexp_le
  exact_mod_cast hexp_le

/-- Elementary growth lemma: `r * 2^r ≤ 2^{2^r}` for all `r ≥ 1`. -/
private theorem mul_two_pow_le_two_pow_two_pow {r : ℕ} (hr : 1 ≤ r) :
    r * 2 ^ r ≤ 2 ^ (2 ^ r) := by
  induction r with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have hprev := ih hk
      have h4 : 4 ≤ 2 ^ (2 ^ k) := by
        have h2k : 2 ≤ 2 ^ k := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by omega) h2k
      have hstep : (k + 1) * 2 ^ (k + 1) ≤ 4 * (k * 2 ^ k) := by
        calc (k + 1) * 2 ^ (k + 1) = (k + 1) * 2 * 2 ^ k := by rw [pow_succ]; ring
          _ ≤ (4 * k) * 2 ^ k := Nat.mul_le_mul_right _ (by omega)
          _ = 4 * (k * 2 ^ k) := by ring
      calc (k + 1) * 2 ^ (k + 1) ≤ 4 * (k * 2 ^ k) := hstep
        _ ≤ 2 ^ (2 ^ k) * 2 ^ (2 ^ k) := Nat.mul_le_mul h4 hprev
        _ = 2 ^ (2 ^ (k + 1)) := by rw [← pow_add, pow_succ]; ring_nf

/-- **uniform-in-`k` explicit bound**):
for every `k ≥ 2`, every `n ≥ (1296 * 2^{2^k})^{k + 1}`, and every `c: ℕ` with
`R^k_{1/4}(DISJ_{k, n}) ≤ c`,
`n^{1 / (k + 1)} / (432 * 2^{2^k}) ≤ c`. -/
theorem nofDisj_publicCoin_uniform_lower_bound {k n c : ℕ} (hk : 2 ≤ k)
    (hn : (1296 * 2 ^ (2 ^ k)) ^ (k + 1) ≤ n)
    (hcomp : PublicCoin.ecomplexityFun (1 / 4) (nofDisj k n) ≤ c) :
    (n : ℝ) ^ (1 / ((k + 1 : ℕ) : ℝ)) / (432 * (2 : ℝ) ^ (2 ^ k)) ≤ (c : ℝ) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  have hr : 1 ≤ r := by omega
  let A : ℕ := 6 * (36 * r * 2 ^ (2 ^ r)) ^ r
  have hA_pos : 0 < A := by
    dsimp only [A]
    have h2 : 0 < 2 ^ (2 ^ r) := pow_pos (by omega) _
    exact Nat.mul_pos (by omega) (pow_pos (Nat.mul_pos (Nat.mul_pos (by omega) hr) h2) r)
  have hA_le : (A : ℝ) ^ (1 / ((r + 2 : ℕ) : ℝ)) * (2 : ℝ) ^ r ≤ 216 * (2 : ℝ) ^ (2 ^ (r + 1)) := by
    have hbase_le : (A : ℝ) ≤ (216 * (2 : ℝ) ^ (2 ^ r) * (r : ℝ)) ^ (r + 2) := by
      have h1 : 6 * (36 * r * 2 ^ (2 ^ r)) ^ r ≤ (216 * 2 ^ (2 ^ r) * r) ^ (r + 2) := by
        have hge : 36 * r * 2 ^ (2 ^ r) ≤ 216 * 2 ^ (2 ^ r) * r := by
          have : 0 ≤ 2 ^ (2 ^ r) * r := Nat.zero_le _
          nlinarith
        have h6 : 6 ≤ (216 * 2 ^ (2 ^ r) * r) ^ 2 := by
          have h1' : 6 ≤ 216 * 2 ^ (2 ^ r) * r := by
            have : 1 ≤ 2 ^ (2 ^ r) := Nat.one_le_pow _ _ (by omega)
            nlinarith
          nlinarith
        calc 6 * (36 * r * 2 ^ (2 ^ r)) ^ r
            ≤ (216 * 2 ^ (2 ^ r) * r) ^ 2 * (216 * 2 ^ (2 ^ r) * r) ^ r :=
              Nat.mul_le_mul h6 (Nat.pow_le_pow_left hge r)
          _ = (216 * 2 ^ (2 ^ r) * r) ^ (r + 2) := by rw [← pow_add, add_comm]
      exact_mod_cast h1
    have hroot : (A : ℝ) ^ (1 / ((r + 2 : ℕ) : ℝ)) ≤ 216 * (2 : ℝ) ^ (2 ^ r) * (r : ℝ) := by
      have hpos_exp : (0 : ℝ) < ((r + 2 : ℕ) : ℝ) := by positivity
      calc (A : ℝ) ^ (1 / ((r + 2 : ℕ) : ℝ))
          ≤ ((216 * (2 : ℝ) ^ (2 ^ r) * (r : ℝ)) ^ (r + 2)) ^ (1 / ((r + 2 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow (Nat.cast_nonneg A) hbase_le (by positivity)
        _ = 216 * (2 : ℝ) ^ (2 ^ r) * (r : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), one_div,
              mul_inv_cancel₀ hpos_exp.ne', Real.rpow_one]
    have hgrowth : (r : ℝ) * (2 : ℝ) ^ r ≤ (2 : ℝ) ^ (2 ^ r) := by
      exact_mod_cast mul_two_pow_le_two_pow_two_pow hr
    calc (A : ℝ) ^ (1 / ((r + 2 : ℕ) : ℝ)) * (2 : ℝ) ^ r
        ≤ (216 * (2 : ℝ) ^ (2 ^ r) * (r : ℝ)) * (2 : ℝ) ^ r :=
          mul_le_mul_of_nonneg_right hroot (by positivity)
      _ = 216 * (2 : ℝ) ^ (2 ^ r) * ((r : ℝ) * (2 : ℝ) ^ r) := by ring
      _ ≤ 216 * (2 : ℝ) ^ (2 ^ r) * (2 : ℝ) ^ (2 ^ r) :=
          mul_le_mul_of_nonneg_left hgrowth (by positivity)
      _ = 216 * (2 : ℝ) ^ (2 ^ (r + 1)) := by
          rw [mul_assoc, ← pow_add, pow_succ]; ring_nf
 -- Choose `d = ⌊(n / A)^{1 / (r + 2)}⌋`:
  let x : ℝ := ((n : ℝ) / (A : ℝ)) ^ (1 / ((r + 2 : ℕ) : ℝ))
  let d : ℕ := Nat.floor x
  have h2r_pos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hB_pos : (0 : ℝ) < 216 * (2 : ℝ) ^ (2 ^ (r + 1)) := by positivity
  have hx_ge : (n : ℝ) ^ (1 / ((r + 2 : ℕ) : ℝ)) / (216 * (2 : ℝ) ^ (2 ^ (r + 1))) ≤
      x / (2 : ℝ) ^ r := by
    have hA_posR : (0 : ℝ) < A := by exact_mod_cast hA_pos
    have hx_eq : x = (n : ℝ) ^ (1 / ((r + 2 : ℕ) : ℝ)) / (A : ℝ) ^ (1 / ((r + 2 : ℕ) : ℝ)) :=
      Real.div_rpow (Nat.cast_nonneg n) hA_posR.le _
    rw [hx_eq, div_div]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hA_le
  have hn_root : 1296 * (2 : ℝ) ^ (2 ^ (r + 1)) ≤ (n : ℝ) ^ (1 / ((r + 2 : ℕ) : ℝ)) := by
    have hnR : ((1296 * (2 : ℝ) ^ (2 ^ (r + 1))) ^ (r + 2)) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hpos_exp : (0 : ℝ) < ((r + 2 : ℕ) : ℝ) := by positivity
    calc 1296 * (2 : ℝ) ^ (2 ^ (r + 1))
        = ((1296 * (2 : ℝ) ^ (2 ^ (r + 1))) ^ (r + 2)) ^ (1 / ((r + 2 : ℕ) : ℝ)) := by
          rw [← Real.rpow_natCast _ (r + 2), ← Real.rpow_mul (by positivity), one_div,
            mul_inv_cancel₀ hpos_exp.ne', Real.rpow_one]
      _ ≤ (n : ℝ) ^ (1 / ((r + 2 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow (by positivity) hnR (by positivity)
  have hratio_ge6 :
      (6 : ℝ) ≤ (n : ℝ) ^ (1 / ((r + 2 : ℕ) : ℝ)) / (216 * (2 : ℝ) ^ (2 ^ (r + 1))) := by
    rw [le_div_iff₀ hB_pos]
    linarith
  have hd1 : 1 ≤ d := by
    have hx1 : (1 : ℝ) ≤ x := by
      have h1 : (6 : ℝ) ≤ x / (2 : ℝ) ^ r := hratio_ge6.trans hx_ge
      rw [le_div_iff₀ h2r_pos] at h1
      have h2r_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
      nlinarith
    exact Nat.le_floor (by simpa using hx1)
  have hAd_le : A * d ^ (r + 2) ≤ n := by
    have hd_le_x : (d : ℝ) ≤ x := Nat.floor_le (by positivity)
    have hpow : (d : ℝ) ^ (r + 2) ≤ (n : ℝ) / (A : ℝ) := by
      have hpos_exp : (0 : ℝ) < ((r + 2 : ℕ) : ℝ) := by positivity
      calc (d : ℝ) ^ (r + 2) ≤ x ^ (r + 2) := pow_le_pow_left₀ (Nat.cast_nonneg d) hd_le_x _
        _ = (((n : ℝ) / (A : ℝ)) ^ (1 / ((r + 2 : ℕ) : ℝ))) ^ ((r + 2 : ℕ) : ℝ) := by
            rw [Real.rpow_natCast]
        _ = (n : ℝ) / (A : ℝ) := by
            rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hpos_exp.ne',
              Real.rpow_one]
    have hA_posR : (0 : ℝ) < A := by exact_mod_cast hA_pos
    rw [le_div_iff₀ hA_posR, mul_comm] at hpow
    exact_mod_cast hpow
  have hlb := nofDisj_publicCoin_explicit_lower_bound hr hd1 hAd_le (by norm_num) le_rfl hcomp
  have hlbR : (d : ℝ) ≤ ((c : ℝ) + 2) * (2 : ℝ) ^ r := by exact_mod_cast hlb
  have hx_lt_d1 : x < (d : ℝ) + 1 := Nat.lt_floor_add_one x
  have hc_ge : x / (2 : ℝ) ^ r - 3 ≤ (c : ℝ) := by
    have h1 : (d : ℝ) / (2 : ℝ) ^ r ≤ (c : ℝ) + 2 := (div_le_iff₀ h2r_pos).mpr hlbR
    have h2 : x / (2 : ℝ) ^ r ≤ (d : ℝ) / (2 : ℝ) ^ r + 1 / (2 : ℝ) ^ r := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hx_lt_d1.le h2r_pos.le
    have h3 : 1 / (2 : ℝ) ^ r ≤ 1 := by
      rw [div_le_one h2r_pos]; exact one_le_pow₀ (by norm_num)
    linarith
  have hhalf : (n : ℝ) ^ (1 / ((r + 2 : ℕ) : ℝ)) / (432 * (2 : ℝ) ^ (2 ^ (r + 1))) ≤
      (n : ℝ) ^ (1 / ((r + 2 : ℕ) : ℝ)) / (216 * (2 : ℝ) ^ (2 ^ (r + 1))) - 3 := by
    have heq : (n : ℝ) ^ (1 / ((r + 2 : ℕ) : ℝ)) / (216 * (2 : ℝ) ^ (2 ^ (r + 1))) =
        2 * ((n : ℝ) ^ (1 / ((r + 2 : ℕ) : ℝ)) / (432 * (2 : ℝ) ^ (2 ^ (r + 1)))) := by
      field_simp [hB_pos.ne']; ring
    linarith
  linarith

/-- Every Boolean function on `Fin k → BitString n` (`k ≥ 2`) has finite public-coin NOF
communication complexity `≤ n + 1` (player `1` broadcasts player `0`'s `n` bits, then player `0`
outputs the answer). -/
theorem ecomplexityFun_nofDisj_le_succ {k n : ℕ} (hk : 2 ≤ k) :
    PublicCoin.ecomplexityFun (1 / 4) (nofDisj k n) ≤ n + 1 := by
  have hp0 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hdet : Protocol.ecomplexityFun (nofDisj k n) ≤ n + 1 :=
    Protocol.ecomplexityFun_le_succ (i := (⟨0, by omega⟩ : Fin k)) (j := ⟨1, by omega⟩) hp0
      (fun v ↦ v ⟨⟨0, by omega⟩, hp0⟩) id (fun _ ↦ rfl) (nofDisj k n)
  exact (PublicCoin.ecomplexity_le_protocol (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans hdet

/-- **Mathlib `Asymptotics.IsBigO` / `Ω` form**):
for every `k ≥ 2`, `n^{1 / (k + 1)} / 2^{2^k} = O(R^k_{1/4}(DISJ_{k, n}))` as `n → ∞`, i.e.,
`R^k_{1/4}(DISJ_{k, n}) = Ω(n^{1 / (k + 1)} / 2^{2^k})`. -/
theorem nofDisj_publicCoin_isBigO {k : ℕ} (hk : 2 ≤ k) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ ↦ (n : ℝ) ^ (1 / ((k + 1 : ℕ) : ℝ)) / (2 : ℝ) ^ (2 ^ k))
      (fun n : ℕ ↦ ((PublicCoin.ecomplexityFun (1 / 4) (nofDisj k n)).toNat : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨432, Filter.eventually_atTop.mpr ⟨(1296 * 2 ^ (2 ^ k)) ^ (k + 1), fun n hn ↦ ?_⟩⟩
  have hfin : PublicCoin.ecomplexityFun (1 / 4) (nofDisj k n) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (ecomplexityFun_nofDisj_le_succ hk)
  set c : ℕ := (PublicCoin.ecomplexityFun (1 / 4) (nofDisj k n)).toNat
  have hcomp : PublicCoin.ecomplexityFun (1 / 4) (nofDisj k n) ≤ c := by
    rw [ENat.natCast_toNat hfin]
  have hlb := nofDisj_publicCoin_uniform_lower_bound hk hn hcomp
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Nat.cast_nonneg c)]
  have hrew : (n : ℝ) ^ (1 / ((k + 1 : ℕ) : ℝ)) / (432 * (2 : ℝ) ^ (2 ^ k)) =
      ((n : ℝ) ^ (1 / ((k + 1 : ℕ) : ℝ)) / (2 : ℝ) ^ (2 ^ k)) / 432 := by ring
  rw [hrew, div_le_iff₀ (by norm_num : (0 : ℝ) < 432)] at hlb
  linarith

end DisjointnessLowerBounds

section NondetSeparationAndSanity

/-- **Explicit Size-`n` Nondeterministic Cover for `SET_INTER_{k, n}`**:
guessing the intersecting coordinate `idx : Fin n` yields a
cylinder intersection of `k` players, certifying `N^k(SET_INTER_{k, n}) ≤ ⌈log₂ n⌉`. -/
def setInterNondetCover {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    NondetCover (signTensor (nofSetInter k n)) where
  size := n
  sets := fun idx ↦ {x : Fin k → BitString n | ∀ p : Fin k, x p idx = true}
  all_cyl := fun idx ↦ by
    refine isCylinderIntersection_iff.mpr
      ⟨fun p v ↦ decide (∀ q : {q : Fin k // q ≠ p}, v q idx = true), Set.ext fun x ↦ ?_⟩
    simp only [Set.mem_ofPred_eq, mem_cylinderIntersection, view_apply]
    constructor
    · intro h p; exact decide_eq_true (fun q ↦ h q.1)
    · intro h q
      let p : Fin k := if q.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have hqp : q ≠ p := by
        dsimp only [p]
        split_ifs with hq0
        · intro heq; have := congrArg Fin.val heq; dsimp at this; omega
        · intro heq; have := congrArg Fin.val heq; dsimp at this; omega
      exact of_decide_eq_true (h p) ⟨q, hqp⟩
  sound := fun idx x hx ↦ by
    have htrue : nofSetInter k n x = true := decide_eq_true ⟨idx, hx⟩
    simp [signTensor_apply, htrue]
  complete := fun x hx ↦ by
    have htrue : nofSetInter k n x = true := by
      cases hf : nofSetInter k n x
      · simp [signTensor_apply, hf] at hx; linarith
      · rfl
    exact of_decide_eq_true htrue

/-- **Exponential Separation Between Nondeterministic (`coNP^{NOF}`) and Randomized (`BPP^{NOF}`)
Multiparty Communication Complexity**:
`SET_INTER_{k, n}` has a nondeterministic cylinder-intersection cover of size `n` (cost `log₂ n`),
while every `1/4`-error public-coin randomized `k`-party NOF protocol for `DISJ_{k, n}` requires
`Ω(n^{1 / (k + 1)} / 2^{2^k})` communication bits. -/
theorem nof_nondet_vs_randomized_separation {k n : ℕ} (hk : 2 ≤ k)
    (hn : (1296 * 2 ^ (2 ^ k)) ^ (k + 1) ≤ n) :
    (∃ C : NondetCover (signTensor (nofSetInter k n)), C.size = n) ∧
      (∀ c : ℕ, PublicCoin.ecomplexityFun (1 / 4) (nofDisj k n) ≤ c →
        (n : ℝ) ^ (1 / ((k + 1 : ℕ) : ℝ)) / (432 * (2 : ℝ) ^ (2 ^ k)) ≤ (c : ℝ)) :=
  ⟨⟨setInterNondetCover hk n, rfl⟩,
    fun _ hcomp ↦ nofDisj_publicCoin_uniform_lower_bound hk hn hcomp⟩

/-- Non-vacuity witness: `DISJ_{k, 1}` (`k ≥ 2`) has a 2-bit deterministic NOF protocol. -/
theorem nofDisj_one_ecomplexity_le_two {k : ℕ} (hk : 2 ≤ k) :
    Protocol.ecomplexityFun (nofDisj k 1) ≤ 2 := by
  have hp0 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  exact Protocol.ecomplexityFun_le_succ (i := (⟨0, by omega⟩ : Fin k)) (j := ⟨1, by omega⟩) hp0
    (fun v ↦ v ⟨⟨0, by omega⟩, hp0⟩) id (fun _ ↦ rfl) (nofDisj k 1)

end NondetSeparationAndSanity

end CslibFrontier.Computability.Communication.NOF
