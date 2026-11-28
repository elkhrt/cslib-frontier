module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Harper's Vertex Isoperimetric Inequality for Hamming Balls

Self-contained proof of Harper's vertex isoperimetric inequality for Hamming balls in the Boolean
hypercube via down-compression and left-compression.

## Main definitions

* `CslibFrontier.Combinatorics.ballVol`: volume `∑ i ≤ k, N.choose i` of a radius-`k` Hamming ball.
* `CslibFrontier.Combinatorics.cubeNeigh`: closed `1`-neighborhood in `Finset (Fin N)`.
* `CslibFrontier.Combinatorics.hammingNeigh`: closed `1`-neighborhood in `Fin N → Bool`.

## Main results

* `CslibFrontier.Combinatorics.harper_ball_isoperimetric`: if `#A ≥ ballVol N k` (`k < N`),
  then `#(cubeNeigh A) ≥ ballVol N (k + 1)`.
* `CslibFrontier.Combinatorics.harper_hammingNeigh`: the same bound on `Fin N → Bool` under
  `hammingDist`.
-/

public section

namespace CslibFrontier.Combinatorics

open scoped Finset BigOperators

/-- Volume `∑ i ≤ k, N.choose i` of a Hamming ball of radius `k` in the `N`-dimensional cube. -/
@[expose] def ballVol (N k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), N.choose i

/-- Pascal recurrence for Hamming ball volumes. -/
theorem ballVol_succ_succ (N k : ℕ) :
    ballVol (N + 1) (k + 1) = ballVol N (k + 1) + ballVol N k := by
  unfold ballVol
  rw [Finset.sum_range_succ' _ (k + 1), Finset.sum_range_succ' _ (k + 1)]
  simp only [Nat.choose_zero_right, Nat.choose_succ_succ, Finset.sum_add_distrib,
    Nat.succ_eq_add_one]
  omega

/-- Radius-0 Hamming ball has volume `1`. -/
@[simp] theorem ballVol_zero (N : ℕ) : ballVol N 0 = 1 := by
  simp [ballVol]

/-- Radius-1 Hamming ball has volume `1 + N`. -/
theorem ballVol_one (N : ℕ) : ballVol N 1 = 1 + N := by
  simp [ballVol, Finset.sum_range_succ]

/-- Radius-`N` Hamming ball covers the entire cube of size `2 ^ N`. -/
theorem ballVol_self (N : ℕ) : ballVol N N = 2 ^ N :=
  Nat.sum_range_choose N

/-- `ballVol N k` is monotone in `k`. -/
theorem ballVol_mono {N k₁ k₂ : ℕ} (h : k₁ ≤ k₂) : ballVol N k₁ ≤ ballVol N k₂ :=
  Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ h))

/-- Closed `1`-neighborhood of `A ⊆ Finset (Fin N)` in the Boolean cube. -/
@[expose] def cubeNeigh {N : ℕ} (A : Finset (Finset (Fin N))) : Finset (Finset (Fin N)) :=
  Finset.univ.filter fun t => ∃ s ∈ A, #(symmDiff s t) ≤ 1

/-- Membership characterization of `cubeNeigh`. -/
theorem mem_cubeNeigh_iff {N : ℕ} {A : Finset (Finset (Fin N))} {t : Finset (Fin N)} :
    t ∈ cubeNeigh A ↔ ∃ s ∈ A, #(symmDiff s t) ≤ 1 := by
  simp [cubeNeigh]

/-- Every member of `A` lies in its closed `1`-neighborhood. -/
theorem subset_cubeNeigh {N : ℕ} (A : Finset (Finset (Fin N))) : A ⊆ cubeNeigh A := fun s hs =>
  mem_cubeNeigh_iff.mpr ⟨s, hs, by simp⟩

/-- `cubeNeigh` distributes over union. -/
theorem cubeNeigh_union {N : ℕ} (A B : Finset (Finset (Fin N))) :
    cubeNeigh (A ∪ B) = cubeNeigh A ∪ cubeNeigh B := by
  ext t
  simp only [mem_cubeNeigh_iff, Finset.mem_union]
  constructor
  · rintro ⟨s, hs | hs, hd⟩
    · exact Or.inl ⟨s, hs, hd⟩
    · exact Or.inr ⟨s, hs, hd⟩
  · rintro (⟨s, hs, hd⟩ | ⟨s, hs, hd⟩)
    · exact ⟨s, Or.inl hs, hd⟩
    · exact ⟨s, Or.inr hs, hd⟩

/-- `cubeNeigh` is monotone. -/
theorem cubeNeigh_mono {N : ℕ} {A B : Finset (Finset (Fin N))} (h : A ⊆ B) :
    cubeNeigh A ⊆ cubeNeigh B := fun _ ht =>
  let ⟨s, hs, hd⟩ := mem_cubeNeigh_iff.mp ht
  mem_cubeNeigh_iff.mpr ⟨s, h hs, hd⟩

/-- `cubeNeigh` of an intersection is contained in the intersection of neighborhoods. -/
theorem cubeNeigh_inter_subset {N : ℕ} (A B : Finset (Finset (Fin N))) :
    cubeNeigh (A ∩ B) ⊆ cubeNeigh A ∩ cubeNeigh B :=
  Finset.subset_inter (cubeNeigh_mono Finset.inter_subset_left)
    (cubeNeigh_mono Finset.inter_subset_right)

/-- If `#(symmDiff s t) ≤ 1` and `i ∈ symmDiff s t`, then `s` and `t` agree on all `a ≠ i`. -/
private theorem mem_iff_of_symmDiff_card_le_one {α : Type*} [DecidableEq α]
    {s t : Finset α} {i : α} (hdist : #(symmDiff s t) ≤ 1) (hi : i ∈ symmDiff s t)
    {a : α} (ha : a ≠ i) : a ∈ s ↔ a ∈ t := by
  have hnot : a ∉ symmDiff s t := fun hmem => ha (Finset.card_le_one.mp hdist a hmem i hi)
  rw [Finset.mem_symmDiff] at hnot
  tauto

/-- `symmDiff s t` has card `≤ 1` iff `t = s`, `t = s.erase i`, or `t = insert i s`. -/
private theorem card_symmDiff_le_one_iff {α : Type*} [DecidableEq α] {s t : Finset α} :
    #(symmDiff s t) ≤ 1 ↔
      t = s ∨ ∃ i : α, (i ∈ s ∧ t = s.erase i) ∨ (i ∉ s ∧ t = insert i s) := by
  constructor
  · intro h
    rcases Finset.eq_empty_or_nonempty (symmDiff s t) with hemp | ⟨i, hi⟩
    · exact Or.inl (symmDiff_eq_bot.mp hemp).symm
    · right
      refine ⟨i, ?_⟩
      rcases Finset.mem_symmDiff.mp hi with ⟨his, hit⟩ | ⟨hit, his⟩
      · left
        refine ⟨his, ?_⟩
        ext a
        by_cases ha : a = i
        · subst ha; simp [hit]
        · simp [ha, (mem_iff_of_symmDiff_card_le_one h hi ha).symm]
      · right
        refine ⟨his, ?_⟩
        ext a
        by_cases ha : a = i
        · subst ha; simp [hit]
        · simp [ha, (mem_iff_of_symmDiff_card_le_one h hi ha).symm]
  · rintro (rfl | ⟨i, ⟨his, rfl⟩ | ⟨his, rfl⟩⟩)
    · simp
    · have : symmDiff s (s.erase i) = {i} := by
        ext a; rw [Finset.mem_symmDiff, Finset.mem_erase, Finset.mem_singleton]
        by_cases ha : a = i <;> simp [ha, his]
      rw [this]; simp
    · have : symmDiff s (insert i s) = {i} := by
        ext a; rw [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
        by_cases ha : a = i <;> simp [ha, his]
      rw [this]; simp

/-! ### Coordinate slices and down-compression -/

private def slice0 {N : ℕ} (i : Fin N) (A : Finset (Finset (Fin N))) :
    Finset (Finset (Fin N)) :=
  A.filter fun s => i ∉ s

private def slice1 {N : ℕ} (i : Fin N) (A : Finset (Finset (Fin N))) :
    Finset (Finset (Fin N)) :=
  (A.filter fun s => i ∈ s).image fun s => s.erase i

private theorem mem_slice0 {N : ℕ} {i : Fin N} {A : Finset (Finset (Fin N))}
    {s : Finset (Fin N)} : s ∈ slice0 i A ↔ s ∈ A ∧ i ∉ s :=
  Finset.mem_filter

private theorem mem_slice1 {N : ℕ} {i : Fin N} {A : Finset (Finset (Fin N))}
    {s : Finset (Fin N)} : s ∈ slice1 i A ↔ insert i s ∈ A ∧ i ∉ s := by
  simp only [slice1, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨t, ⟨htA, hit⟩, rfl⟩
    exact ⟨by simpa [Finset.insert_erase hit] using htA, Finset.notMem_erase i t⟩
  · rintro ⟨hins, his⟩
    exact ⟨insert i s, ⟨hins, Finset.mem_insert_self i s⟩, Finset.erase_insert his⟩

private theorem injOn_erase_of_mem {N : ℕ} (i : Fin N) (A : Finset (Finset (Fin N))) :
    Set.InjOn (fun s : Finset (Fin N) => s.erase i) (A.filter fun s => i ∈ s) := by
  intro s hs t ht hst
  dsimp only at hst
  rw [← Finset.insert_erase (Finset.mem_filter.mp hs).2,
    ← Finset.insert_erase (Finset.mem_filter.mp ht).2, hst]

private theorem card_eq_slice0_add_slice1 {N : ℕ} (i : Fin N) (A : Finset (Finset (Fin N))) :
    #A = #(slice0 i A) + #(slice1 i A) := by
  have hpart := Finset.card_filter_add_card_filter_not (s := A) (p := fun s => i ∈ s)
  unfold slice0 slice1
  rw [Finset.card_image_of_injOn (injOn_erase_of_mem i A)]
  omega

private def cubeNeighWithout {N : ℕ} (i : Fin N) (B : Finset (Finset (Fin N))) :
    Finset (Finset (Fin N)) :=
  (cubeNeigh B).filter fun t => i ∉ t

private theorem slice0_cubeNeigh {N : ℕ} (i : Fin N) (A : Finset (Finset (Fin N))) :
    slice0 i (cubeNeigh A) = cubeNeighWithout i (slice0 i A) ∪ slice1 i A := by
  ext t
  simp only [mem_slice0, mem_cubeNeigh_iff, Finset.mem_union, cubeNeighWithout, Finset.mem_filter,
    mem_slice1]
  constructor
  · rintro ⟨⟨s, hsA, hdist⟩, hit⟩
    by_cases his : i ∈ s
    · right
      have hsymm : i ∈ symmDiff s t := Finset.mem_symmDiff.mpr (Or.inl ⟨his, hit⟩)
      have ht_eq : insert i t = s := by
        ext a
        by_cases ha : a = i
        · subst ha; simp [his]
        · simp [ha, (mem_iff_of_symmDiff_card_le_one hdist hsymm ha).symm]
      exact ⟨ht_eq.symm ▸ hsA, hit⟩
    · exact Or.inl ⟨⟨s, ⟨hsA, his⟩, hdist⟩, hit⟩
  · rintro (⟨⟨s, ⟨hsA, _⟩, hdist⟩, hit⟩ | ⟨hins, hit⟩)
    · exact ⟨⟨s, hsA, hdist⟩, hit⟩
    · refine ⟨⟨insert i t, hins, ?_⟩, hit⟩
      rw [card_symmDiff_le_one_iff]
      exact Or.inr ⟨i, Or.inl ⟨Finset.mem_insert_self i t, (Finset.erase_insert hit).symm⟩⟩

private theorem slice1_cubeNeigh {N : ℕ} (i : Fin N) (A : Finset (Finset (Fin N))) :
    slice1 i (cubeNeigh A) = cubeNeighWithout i (slice1 i A) ∪ slice0 i A := by
  ext t
  simp only [mem_slice1, mem_cubeNeigh_iff, Finset.mem_union, cubeNeighWithout, Finset.mem_filter,
    mem_slice0]
  constructor
  · rintro ⟨⟨s, hsA, hdist⟩, hit⟩
    by_cases his : i ∈ s
    · left
      refine ⟨⟨s.erase i, ⟨by simpa [Finset.insert_erase his] using hsA,
          Finset.notMem_erase i s⟩, ?_⟩, hit⟩
      have hsd : symmDiff (s.erase i) t = symmDiff s (insert i t) := by
        ext a
        by_cases ha : a = i
        · subst ha; simp [Finset.mem_symmDiff, his, hit]
        · simp [Finset.mem_symmDiff, ha]
      rw [hsd]; exact hdist
    · right
      have hsymm : i ∈ symmDiff s (insert i t) :=
        Finset.mem_symmDiff.mpr (Or.inr ⟨Finset.mem_insert_self i t, his⟩)
      have hs_eq : s = t := by
        ext a
        by_cases ha : a = i
        · subst ha; simp [his, hit]
        · simpa [ha] using mem_iff_of_symmDiff_card_le_one hdist hsymm ha
      exact ⟨hs_eq ▸ hsA, hit⟩
  · rintro (⟨⟨s, ⟨hins, his⟩, hdist⟩, hit⟩ | ⟨htA, hit⟩)
    · refine ⟨⟨insert i s, hins, ?_⟩, hit⟩
      have hsd : symmDiff (insert i s) (insert i t) = symmDiff s t := by
        ext a
        by_cases ha : a = i
        · subst ha; simp [Finset.mem_symmDiff, his, hit]
        · simp [Finset.mem_symmDiff, ha]
      rw [hsd]; exact hdist
    · refine ⟨⟨t, htA, ?_⟩, hit⟩
      rw [card_symmDiff_le_one_iff]
      exact Or.inr ⟨i, Or.inr ⟨hit, rfl⟩⟩

private def downComp {N : ℕ} (i : Fin N) (A : Finset (Finset (Fin N))) :
    Finset (Finset (Fin N)) :=
  (slice0 i A ∪ slice1 i A) ∪ ((slice0 i A ∩ slice1 i A).image (insert i))

private theorem slice0_downComp {N : ℕ} (i : Fin N) (A : Finset (Finset (Fin N))) :
    slice0 i (downComp i A) = slice0 i A ∪ slice1 i A := by
  ext s
  simp only [mem_slice0, downComp, Finset.mem_union, Finset.mem_image, Finset.mem_inter]
  constructor
  · rintro ⟨h | ⟨t, _, rfl⟩, his⟩
    · exact h
    · exact absurd (Finset.mem_insert_self i t) his
  · intro h
    refine ⟨Or.inl h, ?_⟩
    rcases h with h0 | h1
    · exact h0.2
    · exact (mem_slice1.mp h1).2

private theorem slice1_downComp {N : ℕ} (i : Fin N) (A : Finset (Finset (Fin N))) :
    slice1 i (downComp i A) = slice0 i A ∩ slice1 i A := by
  ext s
  simp only [mem_slice1, downComp, Finset.mem_union, Finset.mem_image, Finset.mem_inter]
  constructor
  · rintro ⟨(h0 | h1) | ⟨t, ⟨ht0, ht1⟩, heq⟩, his⟩
    · exact absurd (Finset.mem_insert_self i s) (mem_slice0.mp h0).2
    · exact absurd (Finset.mem_insert_self i s) h1.2
    · have ht : t = s := by
        have hti : i ∉ t := (mem_slice0.mp ht0).2
        have := congrArg (fun u => u.erase i) heq
        simpa [Finset.erase_insert hti, Finset.erase_insert his] using this
      subst ht; exact ⟨ht0, ht1⟩
  · rintro ⟨hs0, hs1⟩
    exact ⟨Or.inr ⟨s, ⟨hs0, hs1⟩, rfl⟩, (mem_slice0.mp hs0).2⟩

private theorem card_downComp {N : ℕ} (i : Fin N) (A : Finset (Finset (Fin N))) :
    #(downComp i A) = #A := by
  rw [card_eq_slice0_add_slice1 i (downComp i A), card_eq_slice0_add_slice1 i A,
    slice0_downComp, slice1_downComp, Finset.card_union_add_card_inter]

private theorem card_cubeNeigh_downComp_le {N : ℕ} (i : Fin N) (A : Finset (Finset (Fin N))) :
    #(cubeNeigh (downComp i A)) ≤ #(cubeNeigh A) := by
  rw [card_eq_slice0_add_slice1 i (cubeNeigh (downComp i A)),
    card_eq_slice0_add_slice1 i (cubeNeigh A),
    slice0_cubeNeigh, slice1_cubeNeigh, slice0_cubeNeigh, slice1_cubeNeigh,
    slice0_downComp, slice1_downComp]
  set A₀ := slice0 i A
  set A₁ := slice1 i A
  have hA₀_sub : A₀ ⊆ cubeNeighWithout i A₀ := fun s hs =>
    Finset.mem_filter.mpr ⟨subset_cubeNeigh A₀ hs, (mem_slice0.mp hs).2⟩
  have hA₁_sub : A₁ ⊆ cubeNeighWithout i A₁ := fun s hs =>
    Finset.mem_filter.mpr ⟨subset_cubeNeigh A₁ hs, (mem_slice1.mp hs).2⟩
  have h1 : cubeNeighWithout i (A₀ ∪ A₁) ∪ (A₀ ∩ A₁) ⊆
      (cubeNeighWithout i A₀ ∪ A₁) ∪ (cubeNeighWithout i A₁ ∪ A₀) := by
    intro t ht
    simp only [cubeNeighWithout, cubeNeigh_union, Finset.filter_union, Finset.mem_union,
      Finset.mem_inter] at ht ⊢
    rcases ht with (h | h) | ⟨h0, _⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h0)
  have h2 : cubeNeighWithout i (A₀ ∩ A₁) ∪ (A₀ ∪ A₁) ⊆
      (cubeNeighWithout i A₀ ∪ A₁) ∩ (cubeNeighWithout i A₁ ∪ A₀) := by
    intro t ht
    simp only [Finset.mem_union, Finset.mem_inter] at ht ⊢
    rcases ht with h | (h0 | h1)
    · have ⟨hmem, hni⟩ := Finset.mem_filter.mp h
      have ⟨ha, hb⟩ := Finset.mem_inter.mp (cubeNeigh_inter_subset A₀ A₁ hmem)
      exact ⟨Or.inl (Finset.mem_filter.mpr ⟨ha, hni⟩), Or.inl (Finset.mem_filter.mpr ⟨hb, hni⟩)⟩
    · exact ⟨Or.inl (hA₀_sub h0), Or.inr h0⟩
    · exact ⟨Or.inr h1, Or.inl (hA₁_sub h1)⟩
  calc #(cubeNeighWithout i (A₀ ∪ A₁) ∪ (A₀ ∩ A₁)) +
          #(cubeNeighWithout i (A₀ ∩ A₁) ∪ (A₀ ∪ A₁))
      ≤ #((cubeNeighWithout i A₀ ∪ A₁) ∪ (cubeNeighWithout i A₁ ∪ A₀)) +
          #((cubeNeighWithout i A₀ ∪ A₁) ∩ (cubeNeighWithout i A₁ ∪ A₀)) :=
        Nat.add_le_add (Finset.card_le_card h1) (Finset.card_le_card h2)
    _ = #(cubeNeighWithout i A₀ ∪ A₁) + #(cubeNeighWithout i A₁ ∪ A₀) :=
        Finset.card_union_add_card_inter _ _

/-! ### Left-compression -/

private def swapOne {N : ℕ} (i j : Fin N) (s : Finset (Fin N)) : Finset (Fin N) :=
  insert i (s.erase j)

private def leftComp {N : ℕ} (i j : Fin N) (A : Finset (Finset (Fin N))) :
    Finset (Finset (Fin N)) :=
  A.image fun s =>
    if j ∈ s ∧ i ∉ s ∧ swapOne i j s ∉ A then swapOne i j s else s

private theorem swapOne_idem {N : ℕ} {i j : Fin N} (hij : i ≠ j) {s : Finset (Fin N)}
    (hj : j ∈ s) (hi : i ∉ s) : swapOne j i (swapOne i j s) = s := by
  ext a
  simp only [swapOne, Finset.mem_insert, Finset.mem_erase]
  by_cases ha : a = i
  · subst ha; simp [hij, hi]
  · by_cases haj : a = j
    · subst haj; simp [hj]
    · simp [ha, haj]

private theorem card_leftComp {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    (A : Finset (Finset (Fin N))) : #(leftComp i j A) = #A := by
  unfold leftComp
  rw [Finset.card_image_of_injOn]
  intro s hs t ht heq
  dsimp only at heq
  split_ifs at heq with hs' ht' ht'
  · have := congrArg (swapOne j i) heq
    rwa [swapOne_idem hij hs'.1 hs'.2.1, swapOne_idem hij ht'.1 ht'.2.1] at this
  · exact absurd (heq ▸ ht) hs'.2.2
  · exact absurd (heq.symm ▸ hs) ht'.2.2
  · exact heq

private theorem mem_leftComp {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    {A : Finset (Finset (Fin N))} {t : Finset (Fin N)} :
    t ∈ leftComp i j A ↔
      (t ∈ A ∧ ¬ (j ∈ t ∧ i ∉ t ∧ swapOne i j t ∉ A)) ∨
      (i ∈ t ∧ j ∉ t ∧ swapOne j i t ∈ A ∧ t ∉ A) := by
  simp only [leftComp, Finset.mem_image]
  constructor
  · rintro ⟨s, hsA, hst⟩
    split_ifs at hst with h
    · subst hst
      exact Or.inr ⟨Finset.mem_insert_self i _, by simp [swapOne, hij.symm],
        by rwa [swapOne_idem hij h.1 h.2.1], h.2.2⟩
    · subst hst
      exact Or.inl ⟨hsA, h⟩
  · rintro (⟨htA, hnot⟩ | ⟨hit, hjt, hswA, htnotA⟩)
    · exact ⟨t, htA, by simp [hnot]⟩
    · refine ⟨swapOne j i t, hswA, ?_⟩
      have hj : j ∈ swapOne j i t := Finset.mem_insert_self j _
      have hi : i ∉ swapOne j i t := by simp [swapOne, hij]
      have hback : swapOne i j (swapOne j i t) = t := swapOne_idem hij.symm hit hjt
      simp [hj, hi, hback, htnotA]

private def s00 {N : ℕ} (i j : Fin N) (A : Finset (Finset (Fin N))) :
    Finset (Finset (Fin N)) :=
  A.filter fun s => i ∉ s ∧ j ∉ s

private def s11 {N : ℕ} (i j : Fin N) (A : Finset (Finset (Fin N))) :
    Finset (Finset (Fin N)) :=
  (A.filter fun s => i ∈ s ∧ j ∈ s).image fun s => (s.erase i).erase j

private def s10 {N : ℕ} (i j : Fin N) (A : Finset (Finset (Fin N))) :
    Finset (Finset (Fin N)) :=
  (A.filter fun s => i ∈ s ∧ j ∉ s).image fun s => s.erase i

private theorem mem_s00 {N : ℕ} {i j : Fin N} {A : Finset (Finset (Fin N))} {s : Finset (Fin N)} :
    s ∈ s00 i j A ↔ s ∈ A ∧ i ∉ s ∧ j ∉ s := Finset.mem_filter

private theorem mem_s10 {N : ℕ} {i j : Fin N} (hij : i ≠ j) {A : Finset (Finset (Fin N))}
    {s : Finset (Fin N)} :
    s ∈ s10 i j A ↔ insert i s ∈ A ∧ i ∉ s ∧ j ∉ s := by
  simp only [s10, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨t, ⟨htA, hit, hjt⟩, rfl⟩
    exact ⟨by simpa [Finset.insert_erase hit] using htA, Finset.notMem_erase i t,
      fun h => hjt (Finset.mem_of_mem_erase h)⟩
  · rintro ⟨hins, his, hjs⟩
    exact ⟨insert i s, ⟨hins, Finset.mem_insert_self i s, by simp [hij.symm, hjs]⟩,
      Finset.erase_insert his⟩

private theorem mem_s11 {N : ℕ} {i j : Fin N} (hij : i ≠ j) {A : Finset (Finset (Fin N))}
    {s : Finset (Fin N)} :
    s ∈ s11 i j A ↔ insert i (insert j s) ∈ A ∧ i ∉ s ∧ j ∉ s := by
  simp only [s11, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨t, ⟨htA, hit, hjt⟩, rfl⟩
    refine ⟨?_, fun h => Finset.notMem_erase i t (Finset.mem_of_mem_erase h),
      Finset.notMem_erase j _⟩
    have h1 : insert j ((t.erase i).erase j) = t.erase i :=
      Finset.insert_erase (Finset.mem_erase.mpr ⟨hij.symm, hjt⟩)
    rw [h1, Finset.insert_erase hit]
    exact htA
  · rintro ⟨hins, his, hjs⟩
    refine ⟨insert i (insert j s), ⟨hins, Finset.mem_insert_self i _,
      Finset.mem_insert_of_mem (Finset.mem_insert_self j _)⟩, ?_⟩
    rw [Finset.erase_insert (by simp [hij, his]), Finset.erase_insert hjs]

private theorem s00_comm {N : ℕ} (i j : Fin N) (A : Finset (Finset (Fin N))) :
    s00 j i A = s00 i j A := by
  ext s; simp only [mem_s00]; tauto

private theorem s11_comm {N : ℕ} {i j : Fin N} (hij : i ≠ j) (A : Finset (Finset (Fin N))) :
    s11 j i A = s11 i j A := by
  ext s; simp only [mem_s11 hij, mem_s11 hij.symm, Finset.insert_comm]; tauto

private theorem card_eq_four_slices {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    (A : Finset (Finset (Fin N))) :
    #A = #(s00 i j A) + #(s10 i j A) + #(s10 j i A) + #(s11 i j A) := by
  have h1 := card_eq_slice0_add_slice1 i A
  have h2 := card_eq_slice0_add_slice1 j (slice0 i A)
  have h3 := card_eq_slice0_add_slice1 j (slice1 i A)
  have e00 : slice0 j (slice0 i A) = s00 i j A := by
    ext s; simp only [mem_slice0, mem_s00]; tauto
  have e01 : slice1 j (slice0 i A) = s10 j i A := by
    ext s; simp only [mem_slice1, mem_slice0, mem_s10 hij.symm, Finset.mem_insert, not_or]
    exact ⟨fun ⟨⟨h1, _, h3⟩, h4⟩ => ⟨h1, h4, h3⟩,
      fun ⟨h1, h2, h3⟩ => ⟨⟨h1, hij, h3⟩, h2⟩⟩
  have e10 : slice0 j (slice1 i A) = s10 i j A := by
    ext s; simp only [mem_slice0, mem_slice1, mem_s10 hij]; tauto
  have e11 : slice1 j (slice1 i A) = s11 i j A := by
    ext s
    simp only [mem_slice1, mem_s11 hij, Finset.mem_insert, not_or]
    exact ⟨fun ⟨⟨h1, _, h3⟩, h4⟩ => ⟨h1, h3, h4⟩,
      fun ⟨h1, h2, h3⟩ => ⟨⟨h1, hij, h2⟩, h3⟩⟩
  rw [e00, e01] at h2
  rw [e10, e11] at h3
  omega

private theorem slices_leftComp {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    (A : Finset (Finset (Fin N))) :
    s00 i j (leftComp i j A) = s00 i j A ∧
    s11 i j (leftComp i j A) = s11 i j A ∧
    s10 i j (leftComp i j A) = s10 i j A ∪ s10 j i A ∧
    s10 j i (leftComp i j A) = s10 i j A ∩ s10 j i A := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext s
    simp only [mem_s00, mem_leftComp hij]
    constructor
    · rintro ⟨⟨hsA, _⟩ | ⟨his, _⟩, hni, hnj⟩
      · exact ⟨hsA, hni, hnj⟩
      · exact absurd his hni
    · rintro ⟨hsA, hni, hnj⟩
      exact ⟨Or.inl ⟨hsA, fun h => hnj h.1⟩, hni, hnj⟩
  · ext s
    simp only [mem_s11 hij, mem_leftComp hij]
    constructor
    · rintro ⟨⟨hsA, _⟩ | ⟨_, hnj, _⟩, hni, hnj'⟩
      · exact ⟨hsA, hni, hnj'⟩
      · exact absurd (Finset.mem_insert_of_mem (Finset.mem_insert_self j s)) hnj
    · rintro ⟨hsA, hni, hnj⟩
      exact ⟨Or.inl ⟨hsA, fun h => h.2.1 (Finset.mem_insert_self i _)⟩, hni, hnj⟩
  · ext s
    simp only [mem_s10 hij, mem_s10 hij.symm, Finset.mem_union, mem_leftComp hij]
    constructor
    · rintro ⟨⟨hins, _⟩ | ⟨_, _, hsw, _⟩, hni, hnj⟩
      · exact Or.inl ⟨hins, hni, hnj⟩
      · right
        have hsw_eq : swapOne j i (insert i s) = insert j s := by
          simp [swapOne, Finset.erase_insert hni]
        rw [hsw_eq] at hsw
        exact ⟨hsw, hnj, hni⟩
    · rintro (⟨h10, hni, hnj⟩ | ⟨h01, hnj, hni⟩)
      · exact ⟨Or.inl ⟨h10, fun h => h.2.1 (Finset.mem_insert_self i s)⟩, hni, hnj⟩
      · by_cases h10 : insert i s ∈ A
        · exact ⟨Or.inl ⟨h10, fun h => h.2.1 (Finset.mem_insert_self i s)⟩, hni, hnj⟩
        · refine ⟨Or.inr ⟨Finset.mem_insert_self i s, by simp [hij.symm, hnj], ?_, h10⟩, hni, hnj⟩
          simpa [swapOne, Finset.erase_insert hni] using h01
  · ext s
    simp only [mem_s10 hij.symm, mem_s10 hij, Finset.mem_inter, mem_leftComp hij]
    constructor
    · rintro ⟨⟨hins, hnot⟩ | ⟨hi, _⟩, hnj, hni⟩
      · have hsw_eq : swapOne i j (insert j s) = insert i s := by
          simp [swapOne, Finset.erase_insert hnj]
        have h10 : insert i s ∈ A := by
          by_contra hno
          exact hnot ⟨Finset.mem_insert_self j s, by simp [hij, hni], hsw_eq ▸ hno⟩
        exact ⟨⟨h10, hni, hnj⟩, ⟨hins, hnj, hni⟩⟩
      · exact absurd hi (by simp [hij, hni])
    · rintro ⟨⟨h10, hni, hnj⟩, ⟨h01, _, _⟩⟩
      refine ⟨Or.inl ⟨h01, fun h => h.2.2 ?_⟩, hnj, hni⟩
      simpa [swapOne, Finset.erase_insert hnj] using h10

private def cubeNeighWithout2 {N : ℕ} (i j : Fin N) (B : Finset (Finset (Fin N))) :
    Finset (Finset (Fin N)) :=
  (cubeNeigh B).filter fun t => i ∉ t ∧ j ∉ t

private theorem cubeNeighWithout2_comm {N : ℕ} (i j : Fin N) (B : Finset (Finset (Fin N))) :
    cubeNeighWithout2 j i B = cubeNeighWithout2 i j B := by
  ext s; simp only [cubeNeighWithout2, Finset.mem_filter]; tauto

private theorem cubeNeighWithout2_union {N : ℕ} (i j : Fin N)
    (A B : Finset (Finset (Fin N))) :
    cubeNeighWithout2 i j (A ∪ B) = cubeNeighWithout2 i j A ∪ cubeNeighWithout2 i j B := by
  simp only [cubeNeighWithout2, cubeNeigh_union, Finset.filter_union]

private theorem cubeNeighWithout2_inter_subset {N : ℕ} (i j : Fin N)
    (A B : Finset (Finset (Fin N))) :
    cubeNeighWithout2 i j (A ∩ B) ⊆ cubeNeighWithout2 i j A ∩ cubeNeighWithout2 i j B := by
  intro t ht
  have ⟨h1, h2⟩ := Finset.mem_filter.mp ht
  have ⟨ha, hb⟩ := Finset.mem_inter.mp (cubeNeigh_inter_subset A B h1)
  exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨ha, h2⟩, Finset.mem_filter.mpr ⟨hb, h2⟩⟩

private theorem s00_cubeNeigh {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    (A : Finset (Finset (Fin N))) :
    s00 i j (cubeNeigh A) = cubeNeighWithout2 i j (s00 i j A) ∪ s10 i j A ∪ s10 j i A := by
  ext t
  simp only [mem_s00, mem_cubeNeigh_iff, Finset.mem_union, cubeNeighWithout2, Finset.mem_filter,
    mem_s10 hij, mem_s10 hij.symm]
  constructor
  · rintro ⟨⟨s, hsA, hdist⟩, hti, htj⟩
    by_cases hsi : i ∈ s
    · by_cases hsj : j ∈ s
      · exfalso
        have hi : i ∈ symmDiff s t := Finset.mem_symmDiff.mpr (Or.inl ⟨hsi, hti⟩)
        have hj : j ∈ symmDiff s t := Finset.mem_symmDiff.mpr (Or.inl ⟨hsj, htj⟩)
        exact hij (Finset.card_le_one.mp hdist i hi j hj)
      · left; right
        have hsymm : i ∈ symmDiff s t := Finset.mem_symmDiff.mpr (Or.inl ⟨hsi, hti⟩)
        have heq : insert i t = s := by
          ext a
          by_cases ha : a = i
          · subst ha; simp [hsi]
          · simp [ha, (mem_iff_of_symmDiff_card_le_one hdist hsymm ha).symm]
        exact ⟨heq.symm ▸ hsA, hti, htj⟩
    · by_cases hsj : j ∈ s
      · right
        have hsymm : j ∈ symmDiff s t := Finset.mem_symmDiff.mpr (Or.inl ⟨hsj, htj⟩)
        have heq : insert j t = s := by
          ext a
          by_cases ha : a = j
          · subst ha; simp [hsj]
          · simp [ha, (mem_iff_of_symmDiff_card_le_one hdist hsymm ha).symm]
        exact ⟨heq.symm ▸ hsA, htj, hti⟩
      · exact Or.inl (Or.inl ⟨⟨s, ⟨hsA, hsi, hsj⟩, hdist⟩, hti, htj⟩)
  · rintro ((⟨⟨s, ⟨hsA, _, _⟩, hdist⟩, hti, htj⟩ | ⟨h10, hti, htj⟩) | ⟨h01, htj, hti⟩)
    · exact ⟨⟨s, hsA, hdist⟩, hti, htj⟩
    · refine ⟨⟨insert i t, h10, ?_⟩, hti, htj⟩
      rw [card_symmDiff_le_one_iff]
      exact Or.inr ⟨i, Or.inl ⟨Finset.mem_insert_self i t, (Finset.erase_insert hti).symm⟩⟩
    · refine ⟨⟨insert j t, h01, ?_⟩, hti, htj⟩
      rw [card_symmDiff_le_one_iff]
      exact Or.inr ⟨j, Or.inl ⟨Finset.mem_insert_self j t, (Finset.erase_insert htj).symm⟩⟩

private theorem s11_cubeNeigh {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    (A : Finset (Finset (Fin N))) :
    s11 i j (cubeNeigh A) = cubeNeighWithout2 i j (s11 i j A) ∪ s10 i j A ∪ s10 j i A := by
  ext t
  simp only [mem_s11 hij, mem_cubeNeigh_iff, Finset.mem_union, cubeNeighWithout2,
    Finset.mem_filter, mem_s10 hij, mem_s10 hij.symm]
  constructor
  · rintro ⟨⟨s, hsA, hdist⟩, hti, htj⟩
    by_cases hsi : i ∈ s
    · by_cases hsj : j ∈ s
      · left; left
        refine ⟨⟨(s.erase i).erase j, ?_, ?_⟩, hti, htj⟩
        · refine ⟨?_, fun h => Finset.notMem_erase i s (Finset.mem_of_mem_erase h),
            Finset.notMem_erase j _⟩
          have h1 : insert j ((s.erase i).erase j) = s.erase i :=
            Finset.insert_erase (Finset.mem_erase.mpr ⟨hij.symm, hsj⟩)
          rw [h1, Finset.insert_erase hsi]; exact hsA
        · have hsd : symmDiff ((s.erase i).erase j) t = symmDiff s (insert i (insert j t)) := by
            ext a
            by_cases hai : a = i
            · subst hai; simp [Finset.mem_symmDiff, hsi, hti]
            · by_cases haj : a = j
              · subst haj; simp [Finset.mem_symmDiff, hsj, htj, hij.symm]
              · simp [Finset.mem_symmDiff, hai, haj]
          rw [hsd]; exact hdist
      · left; right
        have hsymm : j ∈ symmDiff s (insert i (insert j t)) :=
          Finset.mem_symmDiff.mpr (Or.inr ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self j t),
            hsj⟩)
        have heq : insert i t = s := by
          ext a
          by_cases haj : a = j
          · subst haj; simp [hij.symm, htj, hsj]
          · simpa [haj] using (mem_iff_of_symmDiff_card_le_one hdist hsymm haj).symm
        exact ⟨heq.symm ▸ hsA, hti, htj⟩
    · by_cases hsj : j ∈ s
      · right
        have hsymm : i ∈ symmDiff s (insert i (insert j t)) :=
          Finset.mem_symmDiff.mpr (Or.inr ⟨Finset.mem_insert_self i _, hsi⟩)
        have heq : insert j t = s := by
          ext a
          by_cases hai : a = i
          · subst hai; simp [hij, hti, hsi]
          · simpa [hai] using (mem_iff_of_symmDiff_card_le_one hdist hsymm hai).symm
        exact ⟨heq.symm ▸ hsA, htj, hti⟩
      · exfalso
        have hi : i ∈ symmDiff s (insert i (insert j t)) :=
          Finset.mem_symmDiff.mpr (Or.inr ⟨Finset.mem_insert_self i _, hsi⟩)
        have hj : j ∈ symmDiff s (insert i (insert j t)) :=
          Finset.mem_symmDiff.mpr (Or.inr ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self j t),
            hsj⟩)
        exact hij (Finset.card_le_one.mp hdist i hi j hj)
  · rintro ((⟨⟨s, ⟨hins, hsi, hsj⟩, hdist⟩, hti, htj⟩ | ⟨h10, hti, htj⟩) | ⟨h01, htj, hti⟩)
    · refine ⟨⟨insert i (insert j s), hins, ?_⟩, hti, htj⟩
      have hsd : symmDiff (insert i (insert j s)) (insert i (insert j t)) = symmDiff s t := by
        ext a
        by_cases hai : a = i
        · subst hai; simp [Finset.mem_symmDiff, hsi, hti]
        · by_cases haj : a = j
          · subst haj; simp [Finset.mem_symmDiff, hsj, htj]
          · simp [Finset.mem_symmDiff, hai, haj]
      rw [hsd]; exact hdist
    · refine ⟨⟨insert i t, h10, ?_⟩, hti, htj⟩
      rw [card_symmDiff_le_one_iff]
      refine Or.inr ⟨j, Or.inr ⟨by simp [hij.symm, htj], ?_⟩⟩
      rw [Finset.insert_comm]
    · refine ⟨⟨insert j t, h01, ?_⟩, hti, htj⟩
      rw [card_symmDiff_le_one_iff]
      exact Or.inr ⟨i, Or.inr ⟨by simp [hij, hti], rfl⟩⟩

private theorem s10_cubeNeigh {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    (A : Finset (Finset (Fin N))) :
    s10 i j (cubeNeigh A) = cubeNeighWithout2 i j (s10 i j A) ∪ s00 i j A ∪ s11 i j A := by
  ext t
  simp only [mem_s10 hij, mem_cubeNeigh_iff, Finset.mem_union, cubeNeighWithout2,
    Finset.mem_filter, mem_s00, mem_s11 hij]
  constructor
  · rintro ⟨⟨s, hsA, hdist⟩, hti, htj⟩
    by_cases hsi : i ∈ s
    · by_cases hsj : j ∈ s
      · right
        have hsymm : j ∈ symmDiff s (insert i t) :=
          Finset.mem_symmDiff.mpr (Or.inl ⟨hsj, by simp [hij.symm, htj]⟩)
        have heq : insert i (insert j t) = s := by
          ext a
          by_cases haj : a = j
          · subst haj; simp [hsj]
          · simpa [haj] using (mem_iff_of_symmDiff_card_le_one hdist hsymm haj).symm
        exact ⟨heq.symm ▸ hsA, hti, htj⟩
      · left; left
        refine ⟨⟨s.erase i, ⟨by simpa [Finset.insert_erase hsi] using hsA,
            Finset.notMem_erase i s, fun h => hsj (Finset.mem_of_mem_erase h)⟩, ?_⟩, hti, htj⟩
        have hsd : symmDiff (s.erase i) t = symmDiff s (insert i t) := by
          ext a
          by_cases hai : a = i
          · subst hai; simp [Finset.mem_symmDiff, hsi, hti]
          · simp [Finset.mem_symmDiff, hai]
        rw [hsd]; exact hdist
    · by_cases hsj : j ∈ s
      · exfalso
        have hi : i ∈ symmDiff s (insert i t) :=
          Finset.mem_symmDiff.mpr (Or.inr ⟨Finset.mem_insert_self i t, hsi⟩)
        have hj : j ∈ symmDiff s (insert i t) :=
          Finset.mem_symmDiff.mpr (Or.inl ⟨hsj, by simp [hij.symm, htj]⟩)
        exact hij (Finset.card_le_one.mp hdist i hi j hj)
      · left; right
        have hsymm : i ∈ symmDiff s (insert i t) :=
          Finset.mem_symmDiff.mpr (Or.inr ⟨Finset.mem_insert_self i t, hsi⟩)
        have heq : s = t := by
          ext a
          by_cases hai : a = i
          · subst hai; simp [hsi, hti]
          · simpa [hai] using mem_iff_of_symmDiff_card_le_one hdist hsymm hai
        exact ⟨heq ▸ hsA, hti, htj⟩
  · rintro ((⟨⟨s, ⟨hins, hsi, _⟩, hdist⟩, hti, htj⟩ | ⟨h00, hti, htj⟩) | ⟨h11, hti, htj⟩)
    · refine ⟨⟨insert i s, hins, ?_⟩, hti, htj⟩
      have hsd : symmDiff (insert i s) (insert i t) = symmDiff s t := by
        ext a
        by_cases hai : a = i
        · subst hai; simp [Finset.mem_symmDiff, hsi, hti]
        · simp [Finset.mem_symmDiff, hai]
      rw [hsd]; exact hdist
    · refine ⟨⟨t, h00, ?_⟩, hti, htj⟩
      rw [card_symmDiff_le_one_iff]
      exact Or.inr ⟨i, Or.inr ⟨hti, rfl⟩⟩
    · refine ⟨⟨insert i (insert j t), h11, ?_⟩, hti, htj⟩
      rw [card_symmDiff_le_one_iff]
      refine Or.inr ⟨j, Or.inl ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self j t), ?_⟩⟩
      rw [Finset.insert_comm, Finset.erase_insert (by simp [hij.symm, htj])]

private theorem card_cubeNeigh_leftComp_le {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    (A : Finset (Finset (Fin N))) :
    #(cubeNeigh (leftComp i j A)) ≤ #(cubeNeigh A) := by
  rw [card_eq_four_slices hij (cubeNeigh (leftComp i j A)),
    card_eq_four_slices hij (cubeNeigh A),
    s00_cubeNeigh hij, s11_cubeNeigh hij, s10_cubeNeigh hij, s10_cubeNeigh hij.symm,
    s00_cubeNeigh hij, s11_cubeNeigh hij, s10_cubeNeigh hij, s10_cubeNeigh hij.symm]
  simp only [s00_comm i j, s11_comm hij, cubeNeighWithout2_comm i j]
  obtain ⟨h00, h11, h10, h01⟩ := slices_leftComp hij A
  rw [h00, h11, h10, h01]
  set B := s10 i j A
  set C := s10 j i A
  have e00 : cubeNeighWithout2 i j (s00 i j A) ∪ (B ∪ C) ∪ (B ∩ C) =
      cubeNeighWithout2 i j (s00 i j A) ∪ B ∪ C := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter]; tauto
  have e11 : cubeNeighWithout2 i j (s11 i j A) ∪ (B ∪ C) ∪ (B ∩ C) =
      cubeNeighWithout2 i j (s11 i j A) ∪ B ∪ C := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter]; tauto
  have hmid :
      #(cubeNeighWithout2 i j (B ∪ C) ∪ s00 i j A ∪ s11 i j A) +
      #(cubeNeighWithout2 i j (B ∩ C) ∪ s00 i j A ∪ s11 i j A) ≤
      #(cubeNeighWithout2 i j B ∪ s00 i j A ∪ s11 i j A) +
      #(cubeNeighWithout2 i j C ∪ s00 i j A ∪ s11 i j A) := by
    have hu : cubeNeighWithout2 i j (B ∪ C) ∪ s00 i j A ∪ s11 i j A =
        (cubeNeighWithout2 i j B ∪ s00 i j A ∪ s11 i j A) ∪
        (cubeNeighWithout2 i j C ∪ s00 i j A ∪ s11 i j A) := by
      rw [cubeNeighWithout2_union]; ext x; simp only [Finset.mem_union]; tauto
    have hi : cubeNeighWithout2 i j (B ∩ C) ∪ s00 i j A ∪ s11 i j A ⊆
        (cubeNeighWithout2 i j B ∪ s00 i j A ∪ s11 i j A) ∩
        (cubeNeighWithout2 i j C ∪ s00 i j A ∪ s11 i j A) := by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_inter] at hx ⊢
      rcases hx with (h | h0) | h1
      · have hbc := Finset.mem_inter.mp (cubeNeighWithout2_inter_subset i j B C h)
        exact ⟨Or.inl (Or.inl hbc.1), Or.inl (Or.inl hbc.2)⟩
      · exact ⟨Or.inl (Or.inr h0), Or.inl (Or.inr h0)⟩
      · exact ⟨Or.inr h1, Or.inr h1⟩
    rw [hu]
    calc #((cubeNeighWithout2 i j B ∪ s00 i j A ∪ s11 i j A) ∪
            (cubeNeighWithout2 i j C ∪ s00 i j A ∪ s11 i j A)) +
          #(cubeNeighWithout2 i j (B ∩ C) ∪ s00 i j A ∪ s11 i j A)
        ≤ #((cubeNeighWithout2 i j B ∪ s00 i j A ∪ s11 i j A) ∪
            (cubeNeighWithout2 i j C ∪ s00 i j A ∪ s11 i j A)) +
          #((cubeNeighWithout2 i j B ∪ s00 i j A ∪ s11 i j A) ∩
            (cubeNeighWithout2 i j C ∪ s00 i j A ∪ s11 i j A)) :=
          Nat.add_le_add_left (Finset.card_le_card hi) _
      _ = #(cubeNeighWithout2 i j B ∪ s00 i j A ∪ s11 i j A) +
          #(cubeNeighWithout2 i j C ∪ s00 i j A ∪ s11 i j A) :=
          Finset.card_union_add_card_inter _ _
  rw [e00, e11]
  omega

/-! ### Weight potential and compression termination -/

private def weightPot {N : ℕ} (A : Finset (Finset (Fin N))) : ℕ :=
  ∑ s ∈ A, ∑ x ∈ s, (x.val + 1)

private theorem weightPot_downComp_lt {N : ℕ} (i : Fin N) (A : Finset (Finset (Fin N)))
    (hne : downComp i A ≠ A) : weightPot (downComp i A) < weightPot A := by
  have hmoved : ∃ s ∈ slice1 i A, s ∉ slice0 i A := by
    by_contra hall
    push Not at hall
    apply hne
    ext t
    by_cases hit : i ∈ t
    · have h1 : t.erase i ∈ slice1 i (downComp i A) ↔ t.erase i ∈ slice1 i A := by
        rw [slice1_downComp, Finset.mem_inter]
        exact ⟨fun h => h.2, fun h => ⟨hall _ h, h⟩⟩
      simpa [mem_slice1, Finset.insert_erase hit, Finset.notMem_erase] using h1
    · have h0 : t ∈ slice0 i (downComp i A) ↔ t ∈ slice0 i A := by
        rw [slice0_downComp, Finset.mem_union]
        exact ⟨fun h => h.elim id (hall _), Or.inl⟩
      simpa [mem_slice0, hit] using h0
  have hpot (B : Finset (Finset (Fin N))) :
      weightPot B =
        (∑ s ∈ slice0 i B, ∑ x ∈ s, (x.val + 1)) +
        (∑ s ∈ slice1 i B, ∑ x ∈ s, (x.val + 1)) +
        #(slice1 i B) * (i.val + 1) := by
    unfold weightPot
    have hsplit := (Finset.sum_filter_add_sum_filter_not B (fun s => i ∉ s)
      (fun s => ∑ x ∈ s, (x.val + 1))).symm
    rw [hsplit]
    have hnot : B.filter (fun s => ¬ i ∉ s) = B.filter (fun s => i ∈ s) := by
      ext s; simp
    rw [hnot]
    have himg : ∑ s ∈ slice1 i B, (∑ x ∈ s, (x.val + 1)) + #(slice1 i B) * (i.val + 1) =
        ∑ t ∈ B.filter (fun s => i ∈ s), ∑ x ∈ t, (x.val + 1) := by
      unfold slice1
      rw [Finset.sum_image (injOn_erase_of_mem i B),
        Finset.card_image_of_injOn (injOn_erase_of_mem i B)]
      rw [show #(B.filter fun s => i ∈ s) * (i.val + 1) =
            ∑ _t ∈ B.filter (fun s => i ∈ s), (i.val + 1) by simp]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t ht => ?_
      exact Finset.sum_erase_add t (fun x : Fin N => x.val + 1) (Finset.mem_filter.mp ht).2
    change (∑ s ∈ slice0 i B, ∑ x ∈ s, (x.val + 1)) +
        (∑ t ∈ B.filter (fun s => i ∈ s), ∑ x ∈ t, (x.val + 1)) = _
    rw [← himg, Nat.add_assoc]
  rw [hpot (downComp i A), hpot A, slice0_downComp, slice1_downComp]
  have hsum := Finset.sum_union_inter (s₁ := slice0 i A) (s₂ := slice1 i A)
    (f := fun s => ∑ x ∈ s, (x.val + 1))
  have hlt_card : #(slice0 i A ∩ slice1 i A) < #(slice1 i A) := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.inter_subset_right, ?_⟩
    intro heq
    rcases hmoved with ⟨s, hs1, hs0⟩
    rw [← heq] at hs1
    exact hs0 (Finset.mem_inter.mp hs1).1
  have hmul_lt : #(slice0 i A ∩ slice1 i A) * (i.val + 1) < #(slice1 i A) * (i.val + 1) :=
    Nat.mul_lt_mul_of_pos_right hlt_card (Nat.succ_pos _)
  omega

private theorem weightPot_leftComp_lt {N : ℕ} {i j : Fin N} (hij : i < j)
    (A : Finset (Finset (Fin N))) (hne : leftComp i j A ≠ A) :
    weightPot (leftComp i j A) < weightPot A := by
  set f : Finset (Fin N) → Finset (Fin N) :=
    fun s => if j ∈ s ∧ i ∉ s ∧ swapOne i j s ∉ A then swapOne i j s else s
  have hinj : Set.InjOn f A := by
    intro s hs t ht heq
    dsimp only [f] at heq
    split_ifs at heq with hs' ht' ht'
    · have := congrArg (swapOne j i) heq
      rwa [swapOne_idem hij.ne hs'.1 hs'.2.1, swapOne_idem hij.ne ht'.1 ht'.2.1] at this
    · exact absurd (heq ▸ ht) hs'.2.2
    · exact absurd (heq.symm ▸ hs) ht'.2.2
    · exact heq
  have hpot : weightPot (leftComp i j A) = ∑ s ∈ A, ∑ x ∈ f s, (x.val + 1) :=
    Finset.sum_image hinj
  rw [hpot]
  unfold weightPot
  have hle : ∀ s ∈ A, (∑ x ∈ f s, (x.val + 1)) ≤ ∑ x ∈ s, (x.val + 1) := by
    intro s _
    dsimp only [f]
    split_ifs with h
    · rw [swapOne, Finset.sum_insert (by simp [hij.ne, h.2.1])]
      have := Finset.add_sum_erase s (fun x : Fin N => x.val + 1) h.1
      have : i.val < j.val := hij
      omega
    · exact le_rfl
  have hex : ∃ s ∈ A, (∑ x ∈ f s, (x.val + 1)) < ∑ x ∈ s, (x.val + 1) := by
    by_contra hall
    push Not at hall
    apply hne
    have hfix : ∀ s ∈ A, f s = s := by
      intro s hs
      dsimp only [f]
      split_ifs with h
      · exfalso
        have hfs : f s = swapOne i j s := by simp [f, h]
        have hlt : (∑ x ∈ f s, (x.val + 1)) < ∑ x ∈ s, (x.val + 1) := by
          rw [hfs, swapOne, Finset.sum_insert (by simp [hij.ne, h.2.1])]
          have := Finset.add_sum_erase s (fun x : Fin N => x.val + 1) h.1
          have : i.val < j.val := hij
          omega
        exact (hall s hs).not_gt hlt
      · rfl
    change A.image f = A
    ext t
    simp only [Finset.mem_image]
    exact ⟨fun ⟨s, hs, hst⟩ => by rw [← hst, hfix s hs]; exact hs, fun ht => ⟨t, ht, hfix t ht⟩⟩
  exact Finset.sum_lt_sum hle hex

private theorem exists_compressed {N : ℕ} (A : Finset (Finset (Fin N))) :
    ∃ B : Finset (Finset (Fin N)),
      #B = #A ∧
      #(cubeNeigh B) ≤ #(cubeNeigh A) ∧
      (∀ i : Fin N, downComp i B = B) ∧
      (∀ i j : Fin N, i < j → leftComp i j B = B) := by
  suffices ∀ w (B : Finset (Finset (Fin N))), weightPot B = w →
      ∃ C : Finset (Finset (Fin N)),
        #C = #B ∧ #(cubeNeigh C) ≤ #(cubeNeigh B) ∧
        (∀ i : Fin N, downComp i C = C) ∧
        (∀ i j : Fin N, i < j → leftComp i j C = C) from this (weightPot A) A rfl
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro B hw
    by_cases hd : ∀ i : Fin N, downComp i B = B
    · by_cases hl : ∀ i j : Fin N, i < j → leftComp i j B = B
      · exact ⟨B, rfl, le_rfl, hd, hl⟩
      · push Not at hl
        rcases hl with ⟨i, j, hij, hne⟩
        have hlt : weightPot (leftComp i j B) < w := hw ▸ weightPot_leftComp_lt hij B hne
        obtain ⟨C, hcard, hnb, hcd, hcl⟩ := ih _ hlt (leftComp i j B) rfl
        exact ⟨C, hcard.trans (card_leftComp hij.ne B),
          hnb.trans (card_cubeNeigh_leftComp_le hij.ne B), hcd, hcl⟩
    · push Not at hd
      rcases hd with ⟨i, hne⟩
      have hlt : weightPot (downComp i B) < w := hw ▸ weightPot_downComp_lt i B hne
      obtain ⟨C, hcard, hnb, hcd, hcl⟩ := ih _ hlt (downComp i B) rfl
      exact ⟨C, hcard.trans (card_downComp i B),
        hnb.trans (card_cubeNeigh_downComp_le i B), hcd, hcl⟩

/-! ### Induction on dimension `N` -/

private def liftSet {N : ℕ} (s : Finset (Fin N)) : Finset (Fin (N + 1)) :=
  s.map ⟨Fin.castSucc, Fin.castSucc_injective N⟩

private theorem liftSet_injective (N : ℕ) : Function.Injective (liftSet (N := N)) := by
  intro s t h
  ext x
  have := Finset.ext_iff.mp h x.castSucc
  simpa [liftSet] using this

private theorem last_notMem_liftSet {N : ℕ} (s : Finset (Fin N)) :
    Fin.last N ∉ liftSet s := by
  simp [liftSet, Fin.castSucc_ne_last]

private theorem symmDiff_liftSet {N : ℕ} (s t : Finset (Fin N)) :
    symmDiff (liftSet s) (liftSet t) = liftSet (symmDiff s t) := by
  ext x
  refine Fin.lastCases ?_ (fun i => ?_) x
  · simp [Finset.mem_symmDiff, last_notMem_liftSet]
  · simp [liftSet, Finset.mem_symmDiff]

private theorem card_symmDiff_liftSet {N : ℕ} (s t : Finset (Fin N)) :
    #(symmDiff (liftSet s) (liftSet t)) = #(symmDiff s t) := by
  rw [symmDiff_liftSet, liftSet, Finset.card_map]

/-- **Harper's Vertex Isoperimetric Inequality for Hamming Balls**: for any `N, k : ℕ` with
`k < N` and any family `A ⊆ Finset (Fin N)`, if `#A ≥ ballVol N k`, then
`#(cubeNeigh A) ≥ ballVol N (k + 1)`. -/
theorem harper_ball_isoperimetric :
    ∀ (N k : ℕ) (A : Finset (Finset (Fin N))),
      k < N → ballVol N k ≤ #A → ballVol N (k + 1) ≤ #(cubeNeigh A) := by
  intro N
  induction N with
  | zero => intro k _ hk; omega
  | succ N ih =>
    intro k A hk hA
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [ballVol_zero] at hA
      obtain ⟨s, hs⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.one_pos hA)
      let f : Option (Fin (N + 1)) → Finset (Fin (N + 1)) := fun o =>
        match o with
        | none => s
        | some i => if i ∈ s then s.erase i else insert i s
      have hinj : Function.Injective f := by
        intro o₁ o₂ heq
        cases o₁ <;> cases o₂
        · rfl
        · rename_i i
          dsimp only [f] at heq
          split_ifs at heq with hi
          · exact absurd (heq ▸ hi) (Finset.notMem_erase i s)
          · exact absurd (heq.symm ▸ Finset.mem_insert_self i s) hi
        · rename_i i
          dsimp only [f] at heq
          split_ifs at heq with hi
          · exact absurd (heq.symm ▸ hi) (Finset.notMem_erase i s)
          · exact absurd (heq ▸ Finset.mem_insert_self i s) hi
        · rename_i i j
          dsimp only [f] at heq
          by_contra hne
          have hne' : i ≠ j := fun h => hne (congrArg some h)
          have hdiff : i ∈ s ↔ i ∈ f (some j) := by
            dsimp only [f]; split_ifs <;> simp [hne']
          have hself : i ∈ s ↔ i ∉ f (some i) := by
            dsimp only [f]; split_ifs with hi <;> simp [hi]
          rw [show f (some i) = f (some j) from heq] at hself
          tauto
      have hsub : (Finset.univ : Finset (Option (Fin (N + 1)))).image f ⊆ cubeNeigh A := by
        intro t ht
        obtain ⟨o, _, rfl⟩ := Finset.mem_image.mp ht
        rw [mem_cubeNeigh_iff]
        refine ⟨s, hs, ?_⟩
        rw [card_symmDiff_le_one_iff]
        cases o with
        | none => exact Or.inl rfl
        | some i =>
          dsimp only [f]
          split_ifs with hi
          · exact Or.inr ⟨i, Or.inl ⟨hi, rfl⟩⟩
          · exact Or.inr ⟨i, Or.inr ⟨hi, rfl⟩⟩
      calc ballVol (N + 1) 1 = 1 + (N + 1) := ballVol_one (N + 1)
        _ = #((Finset.univ : Finset (Option (Fin (N + 1)))).image f) := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_option,
            Fintype.card_fin, Nat.add_comm]
        _ ≤ #(cubeNeigh A) := Finset.card_le_card hsub
    · obtain ⟨B, hcardB, hnbB, hdown, hleft⟩ := exists_compressed A
      rw [← hcardB] at hA
      refine le_trans ?_ hnbB
      let B₀ : Finset (Finset (Fin N)) := Finset.univ.filter fun s => liftSet s ∈ B
      let B₁ : Finset (Finset (Fin N)) :=
        Finset.univ.filter fun s => insert (Fin.last N) (liftSet s) ∈ B
      have hcard_split : #B = #B₀ + #B₁ := by
        rw [card_eq_slice0_add_slice1 (Fin.last N) B]
        congr 1
        · have heq : slice0 (Fin.last N) B = B₀.image liftSet := by
            ext t
            simp only [mem_slice0, Finset.mem_image, B₀, Finset.mem_filter, Finset.mem_univ,
              true_and]
            constructor
            · rintro ⟨htB, hlast⟩
              refine ⟨Finset.univ.filter fun i : Fin N => i.castSucc ∈ t, ?_, ?_⟩
              · have hrec : liftSet (Finset.univ.filter fun i : Fin N => i.castSucc ∈ t) = t := by
                  ext x
                  refine Fin.lastCases ?_ (fun i => ?_) x
                  · simp [last_notMem_liftSet, hlast]
                  · simp [liftSet]
                rwa [hrec]
              · ext x
                refine Fin.lastCases ?_ (fun i => ?_) x
                · simp [last_notMem_liftSet, hlast]
                · simp [liftSet]
            · rintro ⟨s, hs, rfl⟩
              exact ⟨hs, last_notMem_liftSet s⟩
          rw [heq, Finset.card_image_of_injective _ (liftSet_injective N)]
        · have heq : slice1 (Fin.last N) B = B₁.image liftSet := by
            ext t
            simp only [mem_slice1, Finset.mem_image, B₁, Finset.mem_filter, Finset.mem_univ,
              true_and]
            constructor
            · rintro ⟨htB, hlast⟩
              refine ⟨Finset.univ.filter fun i : Fin N => i.castSucc ∈ t, ?_, ?_⟩
              · have hrec : liftSet (Finset.univ.filter fun i : Fin N => i.castSucc ∈ t) = t := by
                  ext x
                  refine Fin.lastCases ?_ (fun i => ?_) x
                  · simp [last_notMem_liftSet, hlast]
                  · simp [liftSet]
                rwa [hrec]
              · ext x
                refine Fin.lastCases ?_ (fun i => ?_) x
                · simp [last_notMem_liftSet, hlast]
                · simp [liftSet]
            · rintro ⟨s, hs, rfl⟩
              exact ⟨hs, last_notMem_liftSet s⟩
          rw [heq, Finset.card_image_of_injective _ (liftSet_injective N)]
      have hN1_sub : cubeNeigh B₁ ⊆ B₀ := by
        intro t ht
        rw [mem_cubeNeigh_iff] at ht
        rcases ht with ⟨s, hs₁, hdist⟩
        have hsB : insert (Fin.last N) (liftSet s) ∈ B := (Finset.mem_filter.mp hs₁).2
        have hdown_mem : ∀ (u : Finset (Fin (N + 1))) (x : Fin (N + 1)),
            u ∈ B → x ∈ u → u.erase x ∈ B := by
          intro u x hu hx
          have h1 : u.erase x ∈ slice1 x B :=
            mem_slice1.mpr ⟨by simpa [Finset.insert_erase hx] using hu, Finset.notMem_erase x u⟩
          have h0 : u.erase x ∈ slice0 x (downComp x B) := by
            rw [slice0_downComp]; exact Finset.mem_union_right _ h1
          rw [hdown x] at h0
          exact (mem_slice0.mp h0).1
        have hleft_mem : ∀ (u : Finset (Fin (N + 1))) (i j : Fin (N + 1)),
            i < j → u ∈ B → j ∈ u → i ∉ u → swapOne i j u ∈ B := by
          intro u i j hij hu hj hi
          by_contra hno
          have hmem : swapOne i j u ∈ leftComp i j B := by
            rw [mem_leftComp hij.ne]
            refine Or.inr ⟨Finset.mem_insert_self i _, by simp [swapOne, hij.ne.symm], ?_, hno⟩
            rwa [swapOne_idem hij.ne hj hi]
          rw [hleft i j hij] at hmem
          exact hno hmem
        have hs0 : liftSet s ∈ B := by
          have := hdown_mem _ (Fin.last N) hsB (Finset.mem_insert_self _ _)
          simpa [Finset.erase_insert (last_notMem_liftSet s)] using this
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ t, ?_⟩
        rw [card_symmDiff_le_one_iff] at hdist
        rcases hdist with rfl | ⟨i, ⟨his, rfl⟩ | ⟨his, rfl⟩⟩
        · exact hs0
        · have heq : liftSet (s.erase i) = (liftSet s).erase i.castSucc := by
            ext x
            refine Fin.lastCases ?_ (fun a => ?_) x
            · simp [last_notMem_liftSet, (Fin.castSucc_ne_last i).symm]
            · simp [liftSet]
          rw [heq]
          exact hdown_mem (liftSet s) i.castSucc hs0 (by simp [liftSet, his])
        · have heq : liftSet (insert i s) = swapOne i.castSucc (Fin.last N)
              (insert (Fin.last N) (liftSet s)) := by
            rw [swapOne, Finset.erase_insert (last_notMem_liftSet s)]
            ext x
            refine Fin.lastCases ?_ (fun a => ?_) x
            · simp [last_notMem_liftSet, (Fin.castSucc_ne_last i).symm]
            · simp [liftSet]
          rw [heq]
          exact hleft_mem _ i.castSucc (Fin.last N) (Fin.castSucc_lt_last i) hsB
            (Finset.mem_insert_self _ _) (by simp [Fin.castSucc_ne_last, liftSet, his])
      have hnb_ge : #(cubeNeigh B₀) + #B₀ ≤ #(cubeNeigh B) := by
        have hdisj : Disjoint ((cubeNeigh B₀).image liftSet)
            (B₀.image fun s => insert (Fin.last N) (liftSet s)) := by
          rw [Finset.disjoint_left]
          intro t ht0 ht1
          obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp ht0
          obtain ⟨u, _, hu⟩ := Finset.mem_image.mp ht1
          exact last_notMem_liftSet s (hu ▸ Finset.mem_insert_self (Fin.last N) _)
        have hsub : (cubeNeigh B₀).image liftSet ∪
            B₀.image (fun s => insert (Fin.last N) (liftSet s)) ⊆ cubeNeigh B := by
          intro t ht
          rcases Finset.mem_union.mp ht with h0 | h1
          · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h0
            rw [mem_cubeNeigh_iff] at hu ⊢
            rcases hu with ⟨s, hs0, hdist⟩
            exact ⟨liftSet s, (Finset.mem_filter.mp hs0).2,
              by rw [card_symmDiff_liftSet]; exact hdist⟩
          · obtain ⟨s, hs0, rfl⟩ := Finset.mem_image.mp h1
            rw [mem_cubeNeigh_iff]
            refine ⟨liftSet s, (Finset.mem_filter.mp hs0).2, ?_⟩
            rw [card_symmDiff_le_one_iff]
            exact Or.inr ⟨Fin.last N, Or.inr ⟨last_notMem_liftSet s, rfl⟩⟩
        have hinj1 : Function.Injective (fun s : Finset (Fin N) =>
            insert (Fin.last N) (liftSet s)) := by
          intro s t heq
          have := congrArg (fun u => u.erase (Fin.last N)) heq
          simp only [Finset.erase_insert (last_notMem_liftSet _)] at this
          exact liftSet_injective N this
        calc #(cubeNeigh B₀) + #B₀
            = #((cubeNeigh B₀).image liftSet) +
              #(B₀.image fun s => insert (Fin.last N) (liftSet s)) := by
                rw [Finset.card_image_of_injective _ (liftSet_injective N),
                  Finset.card_image_of_injective _ hinj1]
          _ = #((cubeNeigh B₀).image liftSet ∪
              B₀.image fun s => insert (Fin.last N) (liftSet s)) :=
                (Finset.card_union_of_disjoint hdisj).symm
          _ ≤ #(cubeNeigh B) := Finset.card_le_card hsub
      have hB₀_ge : ballVol N k ≤ #B₀ := by
        by_contra hlt
        push Not at hlt
        obtain ⟨k', hk'⟩ := Nat.exists_eq_add_of_le' hkpos
        have hk1 : k = k' + 1 := by omega
        have hpas : ballVol (N + 1) (k' + 1) = ballVol N (k' + 1) + ballVol N k' :=
          ballVol_succ_succ N k'
        rw [hk1] at hA hlt hk
        have hB₁_ge : ballVol N k' ≤ #B₁ := by omega
        have hN1_ge : ballVol N (k' + 1) ≤ #(cubeNeigh B₁) := ih k' B₁ (by omega) hB₁_ge
        have hle_B₀ : #(cubeNeigh B₁) ≤ #B₀ := Finset.card_le_card hN1_sub
        omega
      have hpas_next : ballVol (N + 1) (k + 1) = ballVol N (k + 1) + ballVol N k :=
        ballVol_succ_succ N k
      by_cases hkN : k < N
      · have hN0_ge : ballVol N (k + 1) ≤ #(cubeNeigh B₀) := ih k B₀ hkN hB₀_ge
        omega
      · have hk_eq : k = N := by omega
        have hvolN : ballVol N N = 2 ^ N := ballVol_self N
        have hB₀_univ : B₀ = Finset.univ := by
          apply Finset.eq_univ_of_card
          have hcard_univ : Fintype.card (Finset (Fin N)) = 2 ^ N := by
            rw [Fintype.card_finset, Fintype.card_fin]
          have hle : #B₀ ≤ Fintype.card (Finset (Fin N)) := Finset.card_le_univ B₀
          rw [hk_eq, hvolN] at hB₀_ge
          omega
        have hN0_card : #(cubeNeigh B₀) = 2 ^ N := by
          have huniv : cubeNeigh B₀ = Finset.univ :=
            Finset.eq_univ_iff_forall.mpr fun x =>
              subset_cubeNeigh B₀ (hB₀_univ ▸ Finset.mem_univ x)
          rw [huniv, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
        have hvol_succ : ballVol (N + 1) (N + 1) = 2 ^ (N + 1) := ballVol_self (N + 1)
        have h2pow : 2 ^ (N + 1) = 2 ^ N + 2 ^ N := by rw [pow_succ]; ring
        rw [hk_eq, hvol_succ]
        rw [hk_eq, hvolN] at hB₀_ge
        omega

/-- Closed `1`-neighborhood in `Fin N → Bool` under `hammingDist`. -/
@[expose] def hammingNeigh {N : ℕ} (A : Finset (Fin N → Bool)) : Finset (Fin N → Bool) :=
  Finset.univ.filter fun y => ∃ x ∈ A, hammingDist x y ≤ 1

/-- Harper's vertex isoperimetric inequality for Hamming balls on `Fin N → Bool`. -/
theorem harper_hammingNeigh {N k : ℕ} (A : Finset (Fin N → Bool)) (hk : k < N)
    (hA : ballVol N k ≤ #A) : ballVol N (k + 1) ≤ #(hammingNeigh A) := by
  let e : (Fin N → Bool) ≃ Finset (Fin N) :=
    { toFun := fun x => Finset.univ.filter fun i => x i = true
      invFun := fun s i => decide (i ∈ s)
      left_inv := fun x => funext fun i => by cases hx : x i <;> simp [hx]
      right_inv := fun s => by ext i; simp }
  have hdist : ∀ x y : Fin N → Bool, #(symmDiff (e x) (e y)) = hammingDist x y := by
    intro x y
    rw [hammingDist]
    congr 1
    ext i
    simp only [e, Equiv.coe_fn_mk, Finset.mem_symmDiff, Finset.mem_filter, Finset.mem_univ,
      true_and]
    cases x i <;> cases y i <;> simp
  let A' : Finset (Finset (Fin N)) := A.map e.toEmbedding
  have hcardA' : #A' = #A := Finset.card_map _
  have hneigh : (hammingNeigh A).map e.toEmbedding = cubeNeigh A' := by
    ext t
    obtain ⟨y, rfl⟩ := e.surjective t
    simp only [Finset.mem_map, Equiv.toEmbedding_apply, EmbeddingLike.apply_eq_iff_eq,
      exists_eq_right, hammingNeigh, cubeNeigh, Finset.mem_filter, Finset.mem_univ, true_and, A']
    constructor
    · rintro ⟨x, hx, hd⟩
      exact ⟨e x, ⟨x, hx, rfl⟩, (hdist x y).trans_le hd⟩
    · rintro ⟨s, ⟨x, hx, rfl⟩, hd⟩
      exact ⟨x, hx, (hdist x y).symm.trans_le hd⟩
  have hcardN : #(hammingNeigh A) = #(cubeNeigh A') := by
    rw [← hneigh, Finset.card_map]
  rw [hcardN]
  exact harper_ball_isoperimetric N k A' hk (hcardA'.symm ▸ hA)

end CslibFrontier.Combinatorics
