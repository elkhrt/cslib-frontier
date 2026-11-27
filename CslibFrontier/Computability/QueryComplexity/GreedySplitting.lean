module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Chebyshev

/-!
# Greedy Candidate Splitting on the Boolean Cube and Radical-Sum Bounds

Given a finite set `C` of `n`-bit strings, iteratively querying the coordinate that maximizes the
minority bit count and predicting the majority bit partitions `C` into disagreement pieces whose
sizes decay harmonically: at step `j`, at most a `1 / max(2, j + 1)` fraction of `C` can disagree
with the predicted bit after matching all preceding predictions.

Combined with a threshold split at `√(n / log M)` and the Cauchy–Schwarz inequality, any sequence
of step lengths `p_0, …, p_{k - 1}` and terminal run `T_last` obeying `∑ p_g ≤ n`, `T_last ≤ n`,
and `∏ max(2, p_g) ≤ M` (for `1 ≤ n < M ≤ 2 ^ n`) has radical sum bounded by
`8 √(n log M / (log(n / log M) + 1))`.

## Main definitions

* `CslibFrontier.QueryComplexity.splittingPiece`: subset of `C` agreeing with `s` on `π 0, …,
  π (j - 1)` and disagreeing at `π j`.

## Main results

* `CslibFrontier.QueryComplexity.exists_greedy_splitting_order`: existence of a prediction string
  `s` and permutation `π` with `|(splittingPiece C s π j)| ≤ |C| / max(2, j + 1)`.
* `CslibFrontier.QueryComplexity.sum_sqrt_le_of_sum_le_of_prod_max_le`: upper bound
  `∑ √(p_g) + √(T_last) ≤ 8 √(n log M / (log(n / log M) + 1))` under linear sum and product
  constraints.
-/

public section

namespace CslibFrontier.QueryComplexity

open Finset

private def minorityCount {ι : Type*} (R : Finset (ι → Bool)) (k : ι) : ℕ :=
  min (R.filter fun c ↦ c k = false).card (R.filter fun c ↦ c k = true).card

private def majorityBit {ι : Type*} (R : Finset (ι → Bool)) (k : ι) : Bool :=
  decide ((R.filter fun c ↦ c k = false).card ≤ (R.filter fun c ↦ c k = true).card)

private theorem card_filter_false_add_true {ι : Type*} (R : Finset (ι → Bool)) (k : ι) :
    (R.filter fun c ↦ c k = false).card + (R.filter fun c ↦ c k = true).card = R.card := by
  have heq : (R.filter fun c ↦ ¬ (c k = false)) = R.filter fun c ↦ c k = true := by
    ext c; cases c k <;> simp
  rw [← heq]
  exact Finset.card_filter_add_card_filter_not _

private theorem card_filter_ne_majorityBit {ι : Type*} (R : Finset (ι → Bool)) (k : ι) :
    (R.filter fun c ↦ c k ≠ majorityBit R k).card = minorityCount R k := by
  unfold majorityBit minorityCount
  by_cases hle : (R.filter fun c ↦ c k = false).card ≤ (R.filter fun c ↦ c k = true).card
  · have hfilt : (R.filter fun c ↦ c k ≠ decide ((R.filter fun c ↦ c k = false).card ≤
        (R.filter fun c ↦ c k = true).card)) = R.filter fun c ↦ c k = false := by
      ext c; simp [hle]
    rw [hfilt, Nat.min_eq_left hle]
  · have hfilt : (R.filter fun c ↦ c k ≠ decide ((R.filter fun c ↦ c k = false).card ≤
        (R.filter fun c ↦ c k = true).card)) = R.filter fun c ↦ c k = true := by
      ext c; simp [hle]
    rw [hfilt, Nat.min_eq_right (Nat.le_of_not_le hle)]

private theorem two_mul_minorityCount_le {ι : Type*} (R : Finset (ι → Bool)) (k : ι) :
    2 * minorityCount R k ≤ R.card := by
  have hsum := card_filter_false_add_true R k
  unfold minorityCount
  omega

private theorem minorityCount_mono {ι : Type*} {R₁ R₂ : Finset (ι → Bool)} (hsub : R₁ ⊆ R₂)
    (k : ι) : minorityCount R₁ k ≤ minorityCount R₂ k :=
  min_le_min (Finset.card_le_card (Finset.filter_subset_filter _ hsub))
    (Finset.card_le_card (Finset.filter_subset_filter _ hsub))

private def listPiece {ι : Type*} (C : Finset (ι → Bool)) (s : ι → Bool) :
    List ι → ℕ → Finset (ι → Bool)
  | [], _ => ∅
  | k :: _, 0 => C.filter fun c ↦ c k ≠ s k
  | k :: ks, idx + 1 => listPiece (C.filter fun c ↦ c k = s k) s ks idx

private theorem listPiece_congr_on {ι : Type*} (C : Finset (ι → Bool)) {s₁ s₂ : ι → Bool}
    (ks : List ι) (hs : ∀ k ∈ ks, s₁ k = s₂ k) (idx : ℕ) :
    listPiece C s₁ ks idx = listPiece C s₂ ks idx := by
  induction ks generalizing C idx with
  | nil => rfl
  | cons k ks ih =>
    have hk : s₁ k = s₂ k := hs k List.mem_cons_self
    cases idx with
    | zero => simp only [listPiece, hk]
    | succ idx =>
      simp only [listPiece, hk]
      exact ih _ (fun k' hk' ↦ hs k' (List.mem_cons_of_mem k hk')) idx

private theorem mem_listPiece_iff {ι : Type*} {C : Finset (ι → Bool)} {s : ι → Bool}
    {ks : List ι} {idx : ℕ} (hidx : idx < ks.length) (c : ι → Bool) :
    c ∈ listPiece C s ks idx ↔
      c ∈ C ∧ c (ks[idx]) ≠ s (ks[idx]) ∧
        ∀ (i : ℕ) (hi : i < idx), c (ks[i]'(lt_trans hi hidx)) = s (ks[i]'(lt_trans hi hidx)) := by
  induction ks generalizing C idx with
  | nil => simp at hidx
  | cons k ks ih =>
    cases idx with
    | zero => simp [listPiece]
    | succ idx =>
      have hidx' : idx < ks.length := Nat.lt_of_succ_lt_succ hidx
      simp only [listPiece, ih hidx', Finset.mem_filter, List.getElem_cons_succ]
      constructor
      · rintro ⟨⟨hcC, hck⟩, hcne, hall⟩
        refine ⟨hcC, hcne, fun i hi ↦ ?_⟩
        cases i with
        | zero => simpa using hck
        | succ i => exact hall i (Nat.lt_of_succ_lt_succ hi)
      · rintro ⟨hcC, hcne, hall⟩
        refine ⟨⟨hcC, by simpa using hall 0 (Nat.zero_lt_succ idx)⟩, hcne, fun i hi ↦ ?_⟩
        exact hall (i + 1) (Nat.succ_lt_succ hi)

private theorem exists_greedy_list {ι : Type*} (U : Finset ι)
    (C : Finset (ι → Bool)) :
    ∃ (ks : List ι) (s : ι → Bool),
      ks.Nodup ∧ ks.length = U.card ∧ (∀ k, k ∈ ks ↔ k ∈ U) ∧
      (∀ idx < ks.length, ∃ k ∈ U, (listPiece C s ks idx).card ≤ minorityCount C k) ∧
      (∀ idx < ks.length, max 2 (idx + 1) * (listPiece C s ks idx).card ≤ C.card) := by
  classical
  induction hm : U.card generalizing U C with
  | zero =>
    have hU : U = ∅ := Finset.card_eq_zero.mp hm
    subst hU
    exact ⟨[], fun _ ↦ false, List.nodup_nil, rfl, fun _ ↦ by simp,
      fun _ h ↦ by simp at h, fun _ h ↦ by simp at h⟩
  | succ m ih =>
    have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨k₀, hk₀U, hk₀_max⟩ := Finset.exists_max_image U (minorityCount C) hUne
    let b₀ := majorityBit C k₀
    let C_surv := C.filter fun c ↦ c k₀ = b₀
    let U' := U.erase k₀
    have hcard' : U'.card = m := by
      rw [Finset.card_erase_of_mem hk₀U, hm]
      rfl
    obtain ⟨ks', s', hnodup', hlen', hmem', hmin', hbound'⟩ := ih U' C_surv hcard'
    let s : ι → Bool := Function.update s' k₀ b₀
    have hk₀_not_ks' : k₀ ∉ ks' := fun h ↦ Finset.notMem_erase k₀ U ((hmem' k₀).mp h)
    have hs_on_ks' : ∀ k ∈ ks', s k = s' k := fun k hk ↦
      Function.update_of_ne (fun heq ↦ by subst heq; exact hk₀_not_ks' hk) b₀ s'
    have hpiece0 : listPiece C s (k₀ :: ks') 0 = C.filter (fun c ↦ c k₀ ≠ b₀) := by
      simp [listPiece, s]
    have hcard0 : (listPiece C s (k₀ :: ks') 0).card = minorityCount C k₀ := by
      rw [hpiece0]
      exact card_filter_ne_majorityBit C k₀
    have hpiece_succ (idx : ℕ) :
        listPiece C s (k₀ :: ks') (idx + 1) = listPiece C_surv s' ks' idx := by
      simp only [listPiece, s, Function.update_self]
      exact listPiece_congr_on C_surv ks' hs_on_ks' idx
    refine ⟨k₀ :: ks', s, List.nodup_cons.mpr ⟨hk₀_not_ks', hnodup'⟩, by simp [hlen'], ?_, ?_, ?_⟩
    · intro k
      simp only [List.mem_cons, hmem', U', Finset.mem_erase]
      by_cases hk : k = k₀
      · subst hk; simp [hk₀U]
      · simp [hk]
    · intro idx hidx
      cases idx with
      | zero => exact ⟨k₀, hk₀U, hcard0.le⟩
      | succ idx =>
        have hlt : idx < ks'.length := Nat.lt_of_succ_lt_succ hidx
        obtain ⟨k, hkU', hle⟩ := hmin' idx hlt
        refine ⟨k, Finset.mem_of_mem_erase hkU', ?_⟩
        rw [hpiece_succ]
        exact hle.trans (minorityCount_mono (Finset.filter_subset _ _) k)
    · intro idx hidx
      cases idx with
      | zero =>
        rw [hcard0]
        simpa using two_mul_minorityCount_le C k₀
      | succ idx =>
        have hlt : idx < ks'.length := Nat.lt_of_succ_lt_succ hidx
        rw [hpiece_succ]
        obtain ⟨k, hkU', hle_min⟩ := hmin' idx hlt
        have hkU : k ∈ U := Finset.mem_of_mem_erase hkU'
        have hle_c0 : (listPiece C_surv s' ks' idx).card ≤ (listPiece C s (k₀ :: ks') 0).card := by
          rw [hcard0]
          exact (hle_min.trans (minorityCount_mono (Finset.filter_subset _ _) k)).trans
            (hk₀_max k hkU)
        have hle_surv := hbound' idx hlt
        have hpart : (listPiece C s (k₀ :: ks') 0).card + C_surv.card = C.card := by
          rw [hpiece0, add_comm]
          exact Finset.card_filter_add_card_filter_not _
        have hcoef : max 2 (idx + 2) ≤ 1 + max 2 (idx + 1) := by omega
        calc
          max 2 (idx + 1 + 1) * (listPiece C_surv s' ks' idx).card
              ≤ (1 + max 2 (idx + 1)) * (listPiece C_surv s' ks' idx).card :=
                Nat.mul_le_mul_right _ hcoef
          _ = (listPiece C_surv s' ks' idx).card +
                max 2 (idx + 1) * (listPiece C_surv s' ks' idx).card := by ring
          _ ≤ (listPiece C s (k₀ :: ks') 0).card + C_surv.card := Nat.add_le_add hle_c0 hle_surv
          _ = C.card := hpart

/-- Subset of candidates `c ∈ C` matching prediction string `s` at `π i` for all `i < j` and
disagreeing with `s` at `π j`. -/
def splittingPiece {n : ℕ} (C : Finset (Cslib.BitString n)) (s : Cslib.BitString n)
    (π : Equiv.Perm (Fin n)) (j : Fin n) : Finset (Cslib.BitString n) :=
  C.filter fun c ↦ c (π j) ≠ s (π j) ∧ ∀ i : Fin n, i < j → c (π i) = s (π i)

/-- **Greedy splitting bound on the Boolean cube**: for every finite set `C` of `n`-bit strings,
there exist a prediction string `s` and a coordinate permutation `π` such that for every
`j : Fin n`, `|(splittingPiece C s π j)| ≤ |C| / max(2, j + 1)`. -/
theorem exists_greedy_splitting_order {n : ℕ} (C : Finset (Cslib.BitString n)) :
    ∃ (s : Cslib.BitString n) (π : Equiv.Perm (Fin n)),
      ∀ j : Fin n,
        ((splittingPiece C s π j).card : ℝ) ≤ (C.card : ℝ) / max 2 ((j.val : ℝ) + 1) := by
  obtain ⟨ks, s, hnodup, hlen, _hmem, _hmin, hbound⟩ :=
    exists_greedy_list (Finset.univ : Finset (Fin n)) C
  simp only [Finset.card_univ, Fintype.card_fin] at hlen
  let π_fn : Fin n → Fin n := fun j ↦ ks[j.val]'(by omega)
  have hinj : Function.Injective π_fn := by
    intro j₁ j₂ heq
    have hnodup_get := List.nodup_iff_injective_get.mp hnodup
    have hget : ks.get ⟨j₁.val, by omega⟩ = ks.get ⟨j₂.val, by omega⟩ := heq
    exact Fin.ext (Fin.mk.inj (hnodup_get hget))
  let π : Equiv.Perm (Fin n) :=
    Equiv.ofBijective π_fn ((Fintype.bijective_iff_injective_and_card π_fn).mpr ⟨hinj, rfl⟩)
  refine ⟨s, π, fun j ↦ ?_⟩
  have hjlt : j.val < ks.length := by omega
  have heq_piece : splittingPiece C s π j = listPiece C s ks j.val := by
    ext c
    rw [mem_listPiece_iff hjlt, splittingPiece, Finset.mem_filter]
    refine and_congr_right fun _ ↦ ?_
    have hπ : ∀ i : Fin n, π i = ks[i.val]'(by omega) := fun _ ↦ rfl
    simp only [hπ]
    refine and_congr_right fun _ ↦ ⟨fun h i hi ↦ h ⟨i, by omega⟩ hi, fun h i hi ↦ h i.val hi⟩
  rw [heq_piece]
  have hb_nat := hbound j.val hjlt
  have hmax_pos : (0 : ℝ) < max 2 ((j.val : ℝ) + 1) := by positivity
  rw [le_div_iff₀ hmax_pos, mul_comm]
  have hcast : (max 2 ((j.val : ℝ) + 1)) * ((listPiece C s ks j.val).card : ℝ) =
      ((max 2 (j.val + 1) * (listPiece C s ks j.val).card : ℕ) : ℝ) := by
    push_cast; rfl
  rw [hcast]
  exact_mod_cast hb_nat

private theorem log_two_bounds : (1 / 2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have hexp_neg : (1 / 2 : ℝ) ≤ Real.exp (-1 / 2) := by
      linarith [Real.add_one_le_exp (-1 / 2 : ℝ)]
    have hexp_half : Real.exp (1 / 2) ≤ 2 := by
      have hmul : Real.exp (-1 / 2) * Real.exp (1 / 2) = 1 := by
        rw [← Real.exp_add]; norm_num
      have hpos : 0 < Real.exp (1 / 2) := Real.exp_pos _
      nlinarith
    have h := Real.log_le_log (Real.exp_pos _) hexp_half
    rwa [Real.log_exp] at h
  · have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.add_one_le_exp (1 : ℝ)]
    have h := Real.log_le_log (by positivity) hexp1
    rwa [Real.log_exp] at h

/-- **Radical-sum bound under sum and multiplicative elimination constraints**: for
`1 ≤ n < M ≤ 2 ^ n`, any sequence `p : ℕ → ℕ` on `Finset.range k` and tail `T_last : ℕ` satisfying
`∑_{g < k} p_g ≤ n`, `T_last ≤ n`, and `∏_{g < k} max(2, p_g) ≤ M` satisfies
`∑_{g < k} √(p_g) + √(T_last) ≤ 8 √(n log M / (log(n / log M) + 1))`. -/
theorem sum_sqrt_le_of_sum_le_of_prod_max_le {n M k T_last : ℕ} {p : ℕ → ℕ}
    (hn : 1 ≤ n) (hnM : n < M) (hM2 : M ≤ 2 ^ n)
    (hsum : ∑ g ∈ Finset.range k, p g ≤ n) (hlast : T_last ≤ n)
    (hprod : ∏ g ∈ Finset.range k, max 2 (p g) ≤ M) :
    (∑ g ∈ Finset.range k, Real.sqrt (p g)) + Real.sqrt T_last ≤
      8 * Real.sqrt ((n : ℝ) * Real.log M / (Real.log ((n : ℝ) / Real.log M) + 1)) := by
  obtain ⟨hlog2_lo, hlog2_hi⟩ := log_two_bounds
  have hM_ge2 : 2 ≤ M := by omega
  set L : ℝ := Real.log M
  have hL_ge : (1 / 2 : ℝ) ≤ L :=
    hlog2_lo.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hM_ge2))
  have hL_pos : 0 < L := by linarith
  have hL_le_n : L ≤ n := by
    have hle2n : L ≤ Real.log ((2 : ℝ) ^ n) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hM2)
    rw [Real.log_pow] at hle2n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  set u : ℝ := (n : ℝ) / L
  have hu_ge1 : 1 ≤ u := (one_le_div hL_pos).mpr hL_le_n
  have hu_pos : 0 < u := by linarith
  set D : ℝ := Real.log u + 1
  have hD_ge1 : 1 ≤ D := by
    have := Real.log_nonneg hu_ge1
    linarith
  have hD_pos : 0 < D := by linarith
  set Q : ℝ := Real.sqrt ((n : ℝ) * L / D)
  have hQ_sq : Q ^ 2 = (n : ℝ) * L / D := Real.sq_sqrt (by positivity)
  have hlog_sum : ∑ g ∈ Finset.range k, Real.log (max 2 (p g : ℝ)) ≤ L := by
    have hpos_fac : ∀ g ∈ Finset.range k, (0 : ℝ) < max 2 (p g : ℝ) := fun _ _ ↦
      lt_of_lt_of_le (by norm_num) (le_max_left 2 _)
    have hprod_pos : (0 : ℝ) < ∏ g ∈ Finset.range k, max 2 (p g : ℝ) :=
      Finset.prod_pos hpos_fac
    have hprod_real : (∏ g ∈ Finset.range k, max 2 (p g : ℝ)) ≤ (M : ℝ) := by
      have hcast : (∏ g ∈ Finset.range k, max 2 (p g : ℝ)) =
          ((∏ g ∈ Finset.range k, max 2 (p g) : ℕ) : ℝ) := by
        push_cast
        refine Finset.prod_congr rfl fun _ _ ↦ ?_
        norm_cast
      rw [hcast]
      exact_mod_cast hprod
    rw [← Real.log_prod (fun g hg ↦ (hpos_fac g hg).ne')]
    exact Real.log_le_log hprod_pos hprod_real
  have hterm_nonneg : ∀ g, 0 ≤ Real.log (max 2 (p g : ℝ)) := fun g ↦
    Real.log_nonneg (le_trans (by norm_num) (le_max_left 2 _))
  set S₁ := (Finset.range k).filter fun g ↦ (p g : ℝ) < Real.sqrt u
  set S₂ := (Finset.range k).filter fun g ↦ ¬ ((p g : ℝ) < Real.sqrt u)
  have hsplit : (∑ g ∈ Finset.range k, Real.sqrt (p g)) =
      (∑ g ∈ S₁, Real.sqrt (p g)) + ∑ g ∈ S₂, Real.sqrt (p g) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hS₁_le : ∑ g ∈ S₁, Real.sqrt (p g) ≤ 3 * Q := by
    have hcard_S₁ : (S₁.card : ℝ) ≤ 2 * L := by
      have hsub : ∑ g ∈ S₁, (1 / 2 : ℝ) ≤ ∑ g ∈ Finset.range k, Real.log (max 2 (p g : ℝ)) := by
        calc
          ∑ g ∈ S₁, (1 / 2 : ℝ) ≤ ∑ g ∈ S₁, Real.log (max 2 (p g : ℝ)) :=
            Finset.sum_le_sum fun g _ ↦
              hlog2_lo.trans (Real.log_le_log (by norm_num) (le_max_left 2 _))
          _ ≤ ∑ g ∈ Finset.range k, Real.log (max 2 (p g : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun g _ _ ↦ hterm_nonneg g
      rw [Finset.sum_const, nsmul_eq_mul] at hsub
      linarith
    have hsum_S₁ : ∑ g ∈ S₁, Real.sqrt (p g) ≤ 2 * L * Real.sqrt (Real.sqrt u) := by
      calc
        ∑ g ∈ S₁, Real.sqrt (p g) ≤ ∑ _g ∈ S₁, Real.sqrt (Real.sqrt u) :=
          Finset.sum_le_sum fun g hg ↦ Real.sqrt_le_sqrt (Finset.mem_filter.mp hg).2.le
        _ = (S₁.card : ℝ) * Real.sqrt (Real.sqrt u) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 2 * L * Real.sqrt (Real.sqrt u) :=
          mul_le_mul_of_nonneg_right hcard_S₁ (Real.sqrt_nonneg _)
    set z : ℝ := Real.sqrt (Real.sqrt u)
    have hz_pos : 0 < z := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hu_pos)
    have hz2 : z ^ 2 = Real.sqrt u := Real.sq_sqrt (Real.sqrt_nonneg u)
    have hz4 : z ^ 4 = u := by
      calc
        z ^ 4 = (z ^ 2) ^ 2 := by ring
        _ = u := by rw [hz2, Real.sq_sqrt hu_pos.le]
    have hlog_z : Real.log z ≤ z - 1 := Real.log_le_sub_one_of_pos hz_pos
    have hD_le_2sqrt : D ≤ 2 * Real.sqrt u := by
      have hlog_u : Real.log u = 4 * Real.log z := by rw [← hz4, Real.log_pow]; ring
      have hquad : 0 ≤ 2 * (z - 1) ^ 2 + 1 := by positivity
      nlinarith [hz2, hlog_u, hlog_z, hquad]
    have hsq_S₁ : (2 * L * z) ^ 2 ≤ (3 * Q) ^ 2 := by
      have hn_eq : L * u = (n : ℝ) := mul_div_cancel₀ (n : ℝ) hL_pos.ne'
      have h1 : D * (4 * L ^ 2 * Real.sqrt u) ≤ D * (3 * Q) ^ 2 := by
        calc
          D * (4 * L ^ 2 * Real.sqrt u) = 4 * L ^ 2 * (D * Real.sqrt u) := by ring
          _ ≤ 4 * L ^ 2 * (2 * Real.sqrt u * Real.sqrt u) := by gcongr
          _ = 8 * L ^ 2 * (Real.sqrt u * Real.sqrt u) := by ring
          _ = 8 * L * (L * u) := by rw [Real.mul_self_sqrt hu_pos.le]; ring
          _ = 8 * ((n : ℝ) * L) := by rw [hn_eq]; ring
          _ ≤ 9 * ((n : ℝ) * L) := by linarith [mul_nonneg (Nat.cast_nonneg n) hL_pos.le]
          _ = D * (3 * Q) ^ 2 := by
            rw [mul_pow, hQ_sq]
            field_simp [hD_pos.ne']
            ring
      have h2 : (2 * L * z) ^ 2 = 4 * L ^ 2 * Real.sqrt u := by
        rw [mul_pow, mul_pow, hz2]
        ring
      rw [h2]
      exact le_of_mul_le_mul_left h1 hD_pos
    exact hsum_S₁.trans ((sq_le_sq₀ (by positivity) (by positivity)).mp hsq_S₁)
  have hS₂_le : ∑ g ∈ S₂, Real.sqrt (p g) ≤ 2 * Q := by
    have hcard_S₂ : (S₂.card : ℝ) ≤ 4 * L / D := by
      rw [le_div_iff₀ hD_pos, mul_comm]
      have h4log : ∀ g ∈ S₂, D ≤ 4 * Real.log (max 2 (p g : ℝ)) := by
        intro g hg
        have hp_ge : Real.sqrt u ≤ (p g : ℝ) := not_lt.mp (Finset.mem_filter.mp hg).2
        have h1 : 2 * Real.log 2 ≤ 2 * Real.log (max 2 (p g : ℝ)) := by
          gcongr
          exact le_max_left 2 _
        have h2 : Real.log u ≤ 2 * Real.log (max 2 (p g : ℝ)) := by
          have hlog_su : Real.log u = 2 * Real.log (Real.sqrt u) := by
            conv_lhs => rw [← Real.sq_sqrt hu_pos.le, Real.log_pow]
            ring
          rw [hlog_su]
          gcongr
          exact hp_ge.trans (le_max_right 2 _)
        linarith
      calc
        D * (S₂.card : ℝ) = ∑ _g ∈ S₂, D := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ g ∈ S₂, 4 * Real.log (max 2 (p g : ℝ)) := Finset.sum_le_sum h4log
        _ = 4 * ∑ g ∈ S₂, Real.log (max 2 (p g : ℝ)) := (Finset.mul_sum _ _ _).symm
        _ ≤ 4 * ∑ g ∈ Finset.range k, Real.log (max 2 (p g : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun g _ _ ↦ hterm_nonneg g)
            (by norm_num)
        _ ≤ 4 * L := by linarith
    have hcs := sq_sum_le_card_mul_sum_sq (s := S₂) (f := fun g ↦ Real.sqrt (p g))
    have hsum_p : ∑ g ∈ S₂, (Real.sqrt (p g)) ^ 2 ≤ (n : ℝ) := by
      calc
        ∑ g ∈ S₂, (Real.sqrt (p g)) ^ 2 = ∑ g ∈ S₂, (p g : ℝ) :=
          Finset.sum_congr rfl fun g _ ↦ Real.sq_sqrt (Nat.cast_nonneg _)
        _ ≤ ∑ g ∈ Finset.range k, (p g : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ ↦ Nat.cast_nonneg _
        _ ≤ (n : ℝ) := by exact_mod_cast hsum
    have hsq_S₂ : (∑ g ∈ S₂, Real.sqrt (p g)) ^ 2 ≤ (2 * Q) ^ 2 := by
      calc
        (∑ g ∈ S₂, Real.sqrt (p g)) ^ 2 ≤ (S₂.card : ℝ) * ∑ g ∈ S₂, (Real.sqrt (p g)) ^ 2 := hcs
        _ ≤ (4 * L / D) * (n : ℝ) :=
          mul_le_mul hcard_S₂ hsum_p
            (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (by positivity)
        _ = (2 * Q) ^ 2 := by rw [mul_pow, hQ_sq]; ring
    exact (sq_le_sq₀ (Finset.sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _) (by positivity)).mp hsq_S₂
  have hlast_le : Real.sqrt T_last ≤ 3 * Q := by
    have hu_le : u ≤ 2 * (M : ℝ) := by
      rw [le_iff_lt_or_eq]
      left
      rw [div_lt_iff₀ hL_pos]
      have hnM_real : (n : ℝ) < (M : ℝ) := by exact_mod_cast hnM
      nlinarith
    have hlog_u_le : Real.log u ≤ L + 1 := by
      calc
        Real.log u ≤ Real.log (2 * (M : ℝ)) := Real.log_le_log hu_pos hu_le
        _ = Real.log 2 + Real.log M := Real.log_mul two_ne_zero (by positivity)
        _ ≤ L + 1 := by linarith
    have hD_le_9L : D ≤ 9 * L := by linarith
    have hsq_last : (Real.sqrt T_last) ^ 2 ≤ (3 * Q) ^ 2 := by
      rw [Real.sq_sqrt (Nat.cast_nonneg T_last), mul_pow, hQ_sq, mul_div_assoc', le_div_iff₀ hD_pos]
      have hT_le_n : (T_last : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlast
      calc
        (T_last : ℝ) * D ≤ (n : ℝ) * D := mul_le_mul_of_nonneg_right hT_le_n hD_pos.le
        _ ≤ (n : ℝ) * (9 * L) := mul_le_mul_of_nonneg_left hD_le_9L (Nat.cast_nonneg n)
        _ = 3 ^ 2 * ((n : ℝ) * L) := by ring
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp hsq_last
  rw [hsplit]
  linarith

end CslibFrontier.QueryComplexity
