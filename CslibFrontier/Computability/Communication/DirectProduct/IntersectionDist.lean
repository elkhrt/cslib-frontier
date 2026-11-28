module

public import Cslib.Foundations.Data.BitString
public import CslibFrontier.Computability.Communication.Functions
public import CslibFrontier.Computability.Communication.Randomized
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import CslibFrontier.Probability.PMF.Event
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fixed-Weight Intersection Distributions and Direct-Product Relations

Core relations and combinatorial fixed-weight distributions for two-party communication complexity
direct-product lower bounds on Disjointness and intersection search:

* `CslibFrontier.Computability.Communication.ndisj`,
  `CslibFrontier.Computability.Communication.ndisjK`,
  `CslibFrontier.Computability.Communication.disjK`: single and `k`-fold Nondisjointness and
  Disjointness on `BitString n`.
* `CslibFrontier.Computability.Communication.SearchKRel`,
  `CslibFrontier.Computability.Communication.SearchChooseRel`: `k`-fold intersection search
  `SEARCH_n^(k)` and `k`-subset intersection search `SEARCH_{C(N,k)}`.
* `CslibFrontier.Computability.Communication.SolvesWithSuccess`: worst-case success probability
  interface for `Cslib.Communication.PublicCoin` protocols.
* `CslibFrontier.Computability.Communication.S_set`,
  `CslibFrontier.Computability.Communication.T_set`,
  `CslibFrontier.Computability.Communication.muWeight`,
  `CslibFrontier.Computability.Communication.muRect`,
  `CslibFrontier.Computability.Communication.muPMF`: fixed-weight `k`-intersection distributions
  `μ_{k,n,m}` supported on weight-`m` pairs intersecting in exactly `k` coordinates.
* `CslibFrontier.Computability.Communication.removeCoords`,
  `CslibFrontier.Computability.Communication.insertOnes`,
  `CslibFrontier.Computability.Communication.restrictRect`: coordinate-removal bijections and
  exact weight-ratio identities for combinatorial rectangles.
-/

public section

namespace CslibFrontier.Computability.Communication

open Cslib Finset Cslib.Communication

/-! ### Bit-string supports, intersections, and direct-product relations -/

/-- The support `{i | x i = true}` of an `n`-bit string `x`. -/
@[expose] def supportSet {n : ℕ} (x : BitString n) : Finset (Fin n) :=
  univ.filter fun i => x i = true

/-- The common intersection `{i | x i = true ∧ y i = true}` of two `n`-bit strings. -/
@[expose] def interSet {n : ℕ} (x y : BitString n) : Finset (Fin n) :=
  univ.filter fun i => x i = true ∧ y i = true

/-- Membership in `supportSet`. -/
@[simp] theorem mem_supportSet {n : ℕ} {x : BitString n} {i : Fin n} :
    i ∈ supportSet x ↔ x i = true := by
  simp [supportSet]

/-- Membership in `interSet`. -/
@[simp] theorem mem_interSet {n : ℕ} {x y : BitString n} {i : Fin n} :
    i ∈ interSet x y ↔ x i = true ∧ y i = true := by
  simp [interSet]

/-- The common intersection `interSet x y` is the intersection of the two supports. -/
theorem interSet_eq_inter {n : ℕ} (x y : BitString n) :
    interSet x y = supportSet x ∩ supportSet y := by
  ext i
  simp

/-- The characteristic bit string of a subset `s : Finset (Fin n)`. -/
@[expose] def ofFinset {n : ℕ} (s : Finset (Fin n)) : BitString n :=
  fun i => decide (i ∈ s)

/-- The support of `ofFinset s` is `s`. -/
@[simp] theorem supportSet_ofFinset {n : ℕ} (s : Finset (Fin n)) :
    supportSet (ofFinset s) = s := by
  ext i
  simp [ofFinset]

/-- Converting the support of `x` back to a bit string recovers `x`. -/
@[simp] theorem ofFinset_supportSet {n : ℕ} (x : BitString n) :
    ofFinset (supportSet x) = x := by
  funext i
  cases hx : x i <;> simp [ofFinset, hx]

/-- Equivalence between `BitString n` and `Finset (Fin n)` via `supportSet`. -/
@[expose] def bitStringEquivFinset (n : ℕ) : BitString n ≃ Finset (Fin n) where
  toFun := supportSet
  invFun := ofFinset
  left_inv := ofFinset_supportSet
  right_inv := supportSet_ofFinset

/-- Single-instance Nondisjointness `NDISJ_n`, defined as the negation of
`Cslib.Communication.disjointness`. -/
@[expose] def ndisj {n : ℕ} (x y : BitString n) : Bool :=
  !disjointness x y

/-- `ndisj x y = true` iff `x` and `y` share a `true` coordinate. -/
theorem ndisj_eq_true_iff_exists {n : ℕ} {x y : BitString n} :
    ndisj x y = true ↔ ∃ i : Fin n, x i = true ∧ y i = true := by
  simp [ndisj, disjointness]

/-- `ndisj x y = true` iff `interSet x y` is nonempty. -/
theorem ndisj_eq_true_iff_nonempty {n : ℕ} {x y : BitString n} :
    ndisj x y = true ↔ (interSet x y).Nonempty := by
  rw [ndisj_eq_true_iff_exists, Finset.Nonempty]
  simp

/-- `ndisj x y = false` iff the supports of `x` and `y` are disjoint. -/
theorem ndisj_eq_false_iff_disjoint {n : ℕ} {x y : BitString n} :
    ndisj x y = false ↔ Disjoint (supportSet x) (supportSet y) := by
  rw [disjoint_left]
  simp only [ndisj, Bool.not_eq_false', disjointness, decide_eq_true_eq, mem_supportSet]
  constructor
  · intro h i hx hy
    have hi := h i
    rw [hx, hy] at hi
    exact Bool.noConfusion hi
  · intro h i
    cases hx : x i <;> cases hy : y i
    · rfl
    · rfl
    · rfl
    · exact absurd (h hx hy) False.elim

/-- `ndisj` with an all-false left string is `false`. -/
theorem ndisj_const_false_left {n : ℕ} (y : BitString n) :
    ndisj (fun _ => false) y = false := by
  rw [ndisj_eq_false_iff_disjoint, disjoint_left]
  intro i hi
  simp only [mem_supportSet, Bool.false_eq_true] at hi

/-- `ndisj` with an all-false right string is `false`. -/
theorem ndisj_const_false_right {n : ℕ} (x : BitString n) :
    ndisj x (fun _ => false) = false := by
  rw [ndisj_eq_false_iff_disjoint, disjoint_right]
  intro i hi
  simp only [mem_supportSet, Bool.false_eq_true] at hi

/-- The `k`-fold Nondisjointness function `NDISJ_n^(k)`,
evaluating `ndisj` coordinatewise on `k` pairs of `n`-bit strings. -/
@[expose] def ndisjK (n k : ℕ) (x y : Fin k → BitString n) : BitString k :=
  fun i => ndisj (x i) (y i)

/-- Coordinate evaluation of `ndisjK`. -/
theorem ndisjK_apply (n k : ℕ) (x y : Fin k → BitString n) (i : Fin k) :
    ndisjK n k x y i = ndisj (x i) (y i) := rfl

/-- The `k`-fold Disjointness function `DISJ_n^(k)`, evaluating `Cslib.Communication.disjointness`
coordinatewise on `k` pairs of `n`-bit strings. -/
@[expose] def disjK (n k : ℕ) (x y : Fin k → BitString n) : BitString k :=
  fun i => disjointness (x i) (y i)

/-- `disjK` is the coordinatewise negation of `ndisjK`. -/
theorem disjK_eq_not_ndisjK (n k : ℕ) (x y : Fin k → BitString n) (i : Fin k) :
    disjK n k x y i = !ndisjK n k x y i := by
  simp [disjK, ndisjK, ndisj]

/-- The `k`-fold search relation `SEARCH_n^(k)`.
For each coordinate `i`, a valid output gives an intersecting index `some j` when `x i` and `y i`
intersect, and `none` when they are disjoint. -/
@[expose] def SearchKRel (n k : ℕ) (x y : Fin k → BitString n) (out : Fin k →
  Option (Fin n)) : Prop :=
  ∀ i : Fin k, match out i with
    | none => Disjoint (supportSet (x i)) (supportSet (y i))
    | some j => x i j = true ∧ y i j = true

/-- The `k`-intersection search relation `SEARCH_{C(N,k)}`.
A valid output is a `k`-element subset `some I` of `x ∩ y` when `|x ∩ y| ≥ k`, and `none`
when `|x ∩ y| < k`. -/
@[expose] def SearchChooseRel (N k : ℕ) (x y : BitString N) (out : Option (Finset (Fin N)))
  : Prop :=
  match out with
  | none => (interSet x y).card < k
  | some I => I.card = k ∧ I ⊆ interSet x y

/-- Every valid `some I` output for `SearchChooseRel` forces `k ≤ |x ∩ y|`. -/
theorem SearchChooseRel.card_ge_of_some {N k : ℕ} {x y : BitString N} {I : Finset (Fin N)}
    (h : SearchChooseRel N k x y (some I)) : k ≤ (interSet x y).card :=
  h.1 ▸ card_le_card h.2

/-- On inputs with `|x ∩ y| = k`, `SearchChooseRel` accepts only `some (interSet x y)`. -/
theorem searchChooseRel_eq_card_iff {N k : ℕ} {x y : BitString N}
    (hcard : (interSet x y).card = k) {out : Option (Finset (Fin N))} :
    SearchChooseRel N k x y out ↔ out = some (interSet x y) := by
  cases out with
  | none => simp [SearchChooseRel, hcard]
  | some I =>
    simp only [SearchChooseRel, Option.some.injEq]
    constructor
    · rintro ⟨hI, hsub⟩
      exact eq_of_subset_of_card_le hsub (by omega)
    · rintro rfl
      exact ⟨hcard, Subset.rfl⟩

/-! ### Public-coin success probability -/

section SuccessProb

variable {X Y Z : Type*}

/-- The success probability of a public-coin protocol `μ` on input `(x, y)` for relation `R`. -/
noncomputable def successProb (μ : PublicCoin X Y Z) (R : X → Y → Z → Prop) (x : X) (y : Y) : ℝ :=
  1 - μ.errorProb R x y

/-- A public-coin protocol `μ` solves relation `R` with worst-case success probability at least `σ`.
-/
@[expose] def SolvesWithSuccess (μ : PublicCoin X Y Z) (σ : ℝ) (R : X → Y → Z → Prop) : Prop :=
  ∀ x y, σ ≤ successProb μ R x y

/-- Worst-case success probability at least `σ` is equivalent to worst-case error at most `1 - σ`.
-/
theorem solvesWithSuccess_iff_solves {μ : PublicCoin X Y Z} {σ : ℝ} {R : X → Y → Z → Prop} :
    SolvesWithSuccess μ σ R ↔ μ.Solves (1 - σ) R Set.univ Set.univ := by
  constructor
  · intro h x _ y _
    have hx := h x y
    unfold successProb at hx
    linarith
  · intro h x y
    have hx := h x trivial y trivial
    unfold successProb
    linarith

/-- Success probability equals the `PMF` outer measure of protocols succeeding on `(x, y)`. -/
theorem successProb_eq_toOuterMeasure (μ : PublicCoin X Y Z) (R : X → Y → Z → Prop)
    (x : X) (y : Y) :
    successProb μ R x y = (μ.toOuterMeasure {p | R x y (p.run x y)}).toReal := by
  have hcompl := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl μ {p | R x y (p.run x y)}
  have herr : μ.errorProb R x y = (μ.toOuterMeasure {p | R x y (p.run x y)}ᶜ).toReal := rfl
  unfold successProb
  linarith

/-- Success probability is nonnegative. -/
theorem successProb_nonneg (μ : PublicCoin X Y Z) (R : X → Y → Z → Prop) (x : X) (y : Y) :
    0 ≤ successProb μ R x y := by
  rw [successProb_eq_toOuterMeasure]
  exact ENNReal.toReal_nonneg

/-- Success probability is at most `1`. -/
theorem successProb_le_one (μ : PublicCoin X Y Z) (R : X → Y → Z → Prop) (x : X) (y : Y) :
    successProb μ R x y ≤ 1 := by
  unfold successProb
  linarith [PublicCoin.errorProb_nonneg (μ := μ) (R := R) (x := x) (y := y)]

/-- On nonempty domains, any achievable worst-case success probability is at most `1`. -/
theorem solvesWithSuccess_le_one [Nonempty X] [Nonempty Y] {μ : PublicCoin X Y Z} {σ : ℝ}
    {R : X → Y → Z → Prop} (h : SolvesWithSuccess μ σ R) : σ ≤ 1 := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨y⟩ := ‹Nonempty Y›
  exact (h x y).trans (successProb_le_one μ R x y)

end SuccessProb

/-! ### Fixed-weight `k`-intersection distributions -/

/-- The set `S_{I,n}` of pairs `(x, y)` with `x ∩ y = I`. -/
@[expose] def S_set {n : ℕ} (I : Finset (Fin n)) : Set (BitString n × BitString n) :=
  {p | interSet p.1 p.2 = I}

/-- The set `T_{k,n}` of pairs `(x, y)` with `|x ∩ y| = k`. -/
@[expose] def T_set (k n : ℕ) : Set (BitString n × BitString n) :=
  {p | (interSet p.1 p.2).card = k}

/-- `T_{k,n}` is the union of `S_{I,n}` over all `k`-element subsets `I`. -/
theorem T_set_eq_iUnion (k n : ℕ) :
    T_set k n = ⋃ (I : Finset (Fin n)) (_ : I.card = k), S_set I := by
  ext ⟨x, y⟩
  simp [T_set, S_set]

/-- The finite support of `μ_{k,n,m}`: pairs `(x, y)` with `|x| = |y| = m` and `|x ∩ y| = k`. -/
def weightPairs (k n m : ℕ) : Finset (BitString n × BitString n) :=
  univ.filter fun p =>
    (supportSet p.1).card = m ∧ (supportSet p.2).card = m ∧ (interSet p.1 p.2).card = k

/-- Membership in `weightPairs k n m`. -/
theorem mem_weightPairs {k n m : ℕ} {p : BitString n × BitString n} :
    p ∈ weightPairs k n m ↔
      (supportSet p.1).card = m ∧ (supportSet p.2).card = m ∧ (interSet p.1 p.2).card = k := by
  simp [weightPairs]

/-- The normalization constant `C(n, m) * C(m, k) * C(n - m, m - k)` of `μ_{k,n,m}`. -/
@[expose] def weightCard (k n m : ℕ) : ℕ :=
  n.choose m * m.choose k * (n - m).choose (m - k)

/-- Explicit binomial product formula for `weightCard`. -/
theorem weightCard_eq_choose (k n m : ℕ) :
    weightCard k n m = n.choose m * m.choose k * (n - m).choose (m - k) := rfl

/-- Exact cardinality of `weightPairs k n m`. -/
theorem card_weightPairs (k n m : ℕ) : (weightPairs k n m).card = weightCard k n m := by
  classical
  have hbij : (weightPairs k n m).card =
      ((univ : Finset (Fin n)).powersetCard m).sum fun A =>
        (A.powersetCard k).sum fun I => (Aᶜ.powersetCard (m - k)).card := by
    have hsigma :
        (((univ : Finset (Fin n)).powersetCard m).sum fun A =>
          (A.powersetCard k).sum fun _ => (Aᶜ.powersetCard (m - k)).card) =
        ((((univ : Finset (Fin n)).powersetCard m).sigma fun A => A.powersetCard k).sigma
          fun AI => AI.1ᶜ.powersetCard (m - k)).card := by
      rw [Finset.card_sigma, Finset.sum_sigma]
    rw [hsigma]
    refine Finset.card_bij
      (fun p _ => ⟨⟨supportSet p.1, interSet p.1 p.2⟩, supportSet p.2 \ supportSet p.1⟩)
      ?_ ?_ ?_
    · intro p hp
      obtain ⟨hx, hy, hxy⟩ := mem_weightPairs.mp hp
      refine mem_sigma.mpr ⟨mem_sigma.mpr ⟨?_, ?_⟩, ?_⟩
      · exact mem_powersetCard.mpr ⟨subset_univ _, hx⟩
      · rw [interSet_eq_inter] at hxy ⊢
        exact mem_powersetCard.mpr ⟨inter_subset_left, hxy⟩
      · refine mem_powersetCard.mpr ⟨?_, ?_⟩
        · intro i hi
          rw [mem_sdiff] at hi
          exact mem_compl.mpr hi.2
        · dsimp only
          have hcomm : (supportSet p.2 ∩ supportSet p.1).card = k := by
            rw [inter_comm, ← interSet_eq_inter]; exact hxy
          have hsdiff := card_sdiff_add_card_inter (supportSet p.2) (supportSet p.1)
          omega
    · intro p₁ hp₁ p₂ hp₂ heq
      have h1 : supportSet p₁.1 = supportSet p₂.1 := by
        simpa using congrArg (fun t => t.1.1) heq
      have h2 : interSet p₁.1 p₁.2 = interSet p₂.1 p₂.2 := by
        simpa using congrArg (fun t => t.1.2) heq
      have h3 : supportSet p₁.2 \ supportSet p₁.1 = supportSet p₂.2 \ supportSet p₂.1 := by
        simpa using congrArg Sigma.snd heq
      have hs2 : supportSet p₁.2 = supportSet p₂.2 := by
        calc supportSet p₁.2
            = (supportSet p₁.2 \ supportSet p₁.1) ∪ (supportSet p₁.1 ∩ supportSet p₁.2) := by
              rw [inter_comm, sdiff_union_inter]
          _ = (supportSet p₂.2 \ supportSet p₂.1) ∪ (supportSet p₂.1 ∩ supportSet p₂.2) := by
              rw [← interSet_eq_inter, ← interSet_eq_inter, h2, h3]
          _ = supportSet p₂.2 := by rw [inter_comm, sdiff_union_inter]
      ext i
      · exact congrFun (by rw [← ofFinset_supportSet p₁.1, ← ofFinset_supportSet p₂.1, h1]) i
      · exact congrFun (by rw [← ofFinset_supportSet p₁.2, ← ofFinset_supportSet p₂.2, hs2]) i
    · intro ⟨⟨A, I⟩, B⟩ hmem
      simp only [mem_sigma, mem_powersetCard, subset_univ, true_and] at hmem
      obtain ⟨⟨hA, hIA, hI⟩, hBA, hB⟩ := hmem
      have hdisj : Disjoint A B := disjoint_left.mpr fun i hiA hiB =>
        (mem_compl.mp (hBA hiB)) hiA
      have hdisjIB : Disjoint I B := hdisj.mono_left hIA
      refine ⟨(ofFinset A, ofFinset (I ∪ B)), ?_, ?_⟩
      · refine mem_weightPairs.mpr ⟨?_, ?_, ?_⟩
        · simp [hA]
        · rw [supportSet_ofFinset, card_union_of_disjoint hdisjIB, hI, hB]
          have : k ≤ m := by rw [← hI, ← hA]; exact card_le_card hIA
          omega
        · rw [interSet_eq_inter, supportSet_ofFinset, supportSet_ofFinset, inter_union_distrib_left,
            inter_eq_right.mpr hIA, Finset.disjoint_iff_inter_eq_empty.mp hdisj, union_empty, hI]
      · refine Sigma.ext (Sigma.ext ?_ (heq_of_eq ?_)) (heq_of_eq ?_)
        · simp
        · rw [interSet_eq_inter, supportSet_ofFinset, supportSet_ofFinset, inter_union_distrib_left,
            inter_eq_right.mpr hIA, Finset.disjoint_iff_inter_eq_empty.mp hdisj, union_empty]
        · rw [supportSet_ofFinset, supportSet_ofFinset, union_sdiff_distrib,
            sdiff_eq_empty_iff_subset.mpr hIA, empty_union, sdiff_eq_self_of_disjoint hdisj.symm]
  rw [hbij, weightCard]
  have hinner : ∀ A ∈ (univ : Finset (Fin n)).powersetCard m,
      (A.powersetCard k).sum (fun _ => (Aᶜ.powersetCard (m - k)).card) =
        m.choose k * (n - m).choose (m - k) := by
    intro A hA
    have hAc : A.card = m := (mem_powersetCard.mp hA).2
    rw [sum_const, card_powersetCard, hAc, card_powersetCard, card_compl, Fintype.card_fin, hAc,
      smul_eq_mul]
  rw [sum_congr rfl hinner, sum_const, card_powersetCard, card_univ, Fintype.card_fin,
    smul_eq_mul, mul_assoc]

/-- `weightCard k n m` is positive iff `k ≤ m` and `2 * m ≤ n + k`. -/
theorem weightCard_pos_iff {k n m : ℕ} :
    0 < weightCard k n m ↔ k ≤ m ∧ 2 * m ≤ n + k := by
  unfold weightCard
  constructor
  · intro h
    have h1 : 0 < n.choose m := by
      rcases Nat.eq_zero_or_pos (n.choose m) with h0 | hp <;> simp_all
    have h2 : 0 < m.choose k := by
      rcases Nat.eq_zero_or_pos (m.choose k) with h0 | hp <;> simp_all
    have h3 : 0 < (n - m).choose (m - k) := by
      rcases Nat.eq_zero_or_pos ((n - m).choose (m - k)) with h0 | hp <;> simp_all
    have hm : m ≤ n := by
      by_contra hlt; rw [Nat.choose_eq_zero_of_lt (by omega)] at h1; omega
    have hk : k ≤ m := by
      by_contra hlt; rw [Nat.choose_eq_zero_of_lt (by omega)] at h2; omega
    have hnm : m - k ≤ n - m := by
      by_contra hlt; rw [Nat.choose_eq_zero_of_lt (by omega)] at h3; omega
    omega
  · rintro ⟨hk, h2m⟩
    have hm : m ≤ n := by omega
    have hnm : m - k ≤ n - m := by omega
    exact Nat.mul_pos (Nat.mul_pos (Nat.choose_pos hm) (Nat.choose_pos hk)) (Nat.choose_pos hnm)

/-- Multinomial factorial identity for `weightCard k n m`. -/
theorem weightCard_mul_factorials {k n m : ℕ} (hk : k ≤ m) (h2m : 2 * m ≤ n + k) :
    weightCard k n m * (k.factorial * (m - k).factorial * (m - k).factorial *
      (n + k - 2 * m).factorial) = n.factorial := by
  have hm : m ≤ n := by omega
  have hnm : m - k ≤ n - m := by omega
  have hsub : n - m - (m - k) = n + k - 2 * m := by omega
  have h1 := Nat.choose_mul_factorial_mul_factorial hm
  have h2 := Nat.choose_mul_factorial_mul_factorial hk
  have h3 := Nat.choose_mul_factorial_mul_factorial hnm
  rw [hsub] at h3
  unfold weightCard
  calc
    n.choose m * m.choose k * (n - m).choose (m - k) *
        (k.factorial * (m - k).factorial * (m - k).factorial * (n + k - 2 * m).factorial)
      = n.choose m * (m.choose k * k.factorial * (m - k).factorial) *
          ((n - m).choose (m - k) * (m - k).factorial * (n + k - 2 * m).factorial) := by ring
    _ = n.choose m * m.factorial * (n - m).factorial := by rw [h2, h3]
    _ = n.factorial := h1

/-- The point mass `μ_{k,n,m}(x, y)` of the fixed-weight `k`-intersection distribution. -/
noncomputable def muWeight (k n m : ℕ) (x y : BitString n) : ℝ :=
  if (x, y) ∈ weightPairs k n m then ((weightCard k n m : ℝ))⁻¹ else 0

/-- `muWeight` is always nonnegative. -/
theorem muWeight_nonneg (k n m : ℕ) (x y : BitString n) : 0 ≤ muWeight k n m x y := by
  unfold muWeight
  split_ifs <;> positivity

/-- `muWeight` vanishes outside `weightPairs k n m`. -/
theorem muWeight_eq_zero_of_notMem {k n m : ℕ} {x y : BitString n}
    (h : (x, y) ∉ weightPairs k n m) : muWeight k n m x y = 0 := by
  simp [muWeight, h]

/-- `muWeight` equals `(weightCard k n m)⁻¹` on `weightPairs k n m`. -/
theorem muWeight_of_mem {k n m : ℕ} {x y : BitString n}
    (h : (x, y) ∈ weightPairs k n m) : muWeight k n m x y = ((weightCard k n m : ℝ))⁻¹ := by
  simp [muWeight, h]

/-- `muWeight` is symmetric in `x` and `y`. -/
theorem muWeight_comm (k n m : ℕ) (x y : BitString n) :
    muWeight k n m x y = muWeight k n m y x := by
  unfold muWeight
  have hiff : (x, y) ∈ weightPairs k n m ↔ (y, x) ∈ weightPairs k n m := by
    simp only [mem_weightPairs, interSet_eq_inter, inter_comm]
    tauto
  by_cases h : (x, y) ∈ weightPairs k n m
  · simp [h, hiff.mp h]
  · simp [h, mt hiff.mpr h]

/-- The total mass of `μ_{k,n,m}` over all pairs is `1` whenever `k ≤ m` and `2 * m ≤ n + k`. -/
theorem sum_muWeight {k n m : ℕ} (hk : k ≤ m) (h2m : 2 * m ≤ n + k) :
    ∑ x : BitString n, ∑ y : BitString n, muWeight k n m x y = 1 := by
  rw [← Fintype.sum_prod_type']
  have hpos : (weightCard k n m : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (weightCard_pos_iff.mpr ⟨hk, h2m⟩).ne'
  calc
    ∑ p : BitString n × BitString n, muWeight k n m p.1 p.2
      = ∑ p ∈ weightPairs k n m, ((weightCard k n m : ℝ))⁻¹ := by
        simp only [muWeight]
        rw [← sum_filter]
        refine sum_congr (by ext p; simp) fun p _ => rfl
    _ = (weightPairs k n m).card * ((weightCard k n m : ℝ))⁻¹ := by
        rw [sum_const, nsmul_eq_mul]
    _ = 1 := by
        rw [card_weightPairs]
        exact mul_inv_cancel₀ hpos

/-- The distribution `μ_{k,n,m}` as a genuine `PMF (BitString n × BitString n)`. -/
noncomputable def muPMF {k n m : ℕ} (hk : k ≤ m) (h2m : 2 * m ≤ n + k) :
    PMF (BitString n × BitString n) :=
  PMF.ofFintype (fun p => ENNReal.ofReal (muWeight k n m p.1 p.2)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => muWeight_nonneg k n m p.1 p.2),
      Fintype.sum_prod_type', sum_muWeight hk h2m, ENNReal.ofReal_one])

/-- Real-valued probability mass of `muPMF` agrees with `muWeight`. -/
theorem muPMF_apply_toReal {k n m : ℕ} (hk : k ≤ m) (h2m : 2 * m ≤ n + k)
    (p : BitString n × BitString n) : (muPMF hk h2m p).toReal = muWeight k n m p.1 p.2 := by
  rw [muPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (muWeight_nonneg k n m p.1 p.2)]

/-- The measure `μ_{k,n,m}(A × B)` of a combinatorial rectangle `A × B`. -/
@[expose] noncomputable def muRect (k n m : ℕ) (A B : Finset (BitString n)) : ℝ :=
  ∑ x ∈ A, ∑ y ∈ B, muWeight k n m x y

/-- Sum characterization of `muRect`. -/
theorem muRect_eq_sum (k n m : ℕ) (A B : Finset (BitString n)) :
    muRect k n m A B = ∑ x ∈ A, ∑ y ∈ B, muWeight k n m x y := rfl

/-- `muRect` is nonnegative. -/
theorem muRect_nonneg (k n m : ℕ) (A B : Finset (BitString n)) : 0 ≤ muRect k n m A B :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => muWeight_nonneg _ _ _ _ _

/-- `muRect` is monotone in both rectangle sides. -/
@[gcongr] theorem muRect_mono {k n m : ℕ} {A A' B B' : Finset (BitString n)}
    (hA : A ⊆ A') (hB : B ⊆ B') : muRect k n m A B ≤ muRect k n m A' B' := by
  refine (sum_le_sum_of_subset_of_nonneg hA fun _ _ _ =>
    sum_nonneg fun _ _ => muWeight_nonneg _ _ _ _ _).trans ?_
  exact sum_le_sum fun _ _ =>
    sum_le_sum_of_subset_of_nonneg hB fun _ _ _ => muWeight_nonneg _ _ _ _ _

/-- `muRect` is symmetric in `A` and `B`. -/
theorem muRect_comm (k n m : ℕ) (A B : Finset (BitString n)) :
    muRect k n m A B = muRect k n m B A := by
  unfold muRect
  rw [sum_comm]
  exact sum_congr rfl fun y _ => sum_congr rfl fun x _ => muWeight_comm k n m x y

/-- `muRect` over the full universe is `1` for valid parameters. -/
theorem muRect_univ {k n m : ℕ} (hk : k ≤ m) (h2m : 2 * m ≤ n + k) :
    muRect k n m univ univ = 1 :=
  sum_muWeight hk h2m

/-- `muRect` is always at most `1` for valid parameters. -/
theorem muRect_le_one {k n m : ℕ} (hk : k ≤ m) (h2m : 2 * m ≤ n + k)
    (A B : Finset (BitString n)) : muRect k n m A B ≤ 1 :=
  (muRect_mono (subset_univ A) (subset_univ B)).trans_eq (muRect_univ hk h2m)

/-- The rectangle measure agrees with the outer measure of `muPMF`. -/
theorem muRect_eq_toOuterMeasure {k n m : ℕ} (hk : k ≤ m) (h2m : 2 * m ≤ n + k)
    (A B : Finset (BitString n)) :
    muRect k n m A B = ((muPMF hk h2m).toOuterMeasure ((A : Set _) ×ˢ (B : Set _))).toReal := by
  rw [Cslib.Probability.PMF.toOuterMeasure_apply_toReal, Fintype.sum_prod_type]
  simp only [Set.mem_prod, mem_coe, muPMF_apply_toReal]
  unfold muRect
  calc
    ∑ x ∈ A, ∑ y ∈ B, muWeight k n m x y
      = ∑ x ∈ A, ∑ y : BitString n, if y ∈ B then muWeight k n m x y else 0 := by
        refine sum_congr rfl fun x _ => ?_
        rw [← sum_filter, filter_mem_eq_inter, univ_inter]
    _ = ∑ x : BitString n, ∑ y : BitString n,
          if x ∈ A ∧ y ∈ B then muWeight k n m x y else 0 := by
        have hrhs : ∀ x : BitString n,
            (∑ y : BitString n, if x ∈ A ∧ y ∈ B then muWeight k n m x y else 0) =
              if x ∈ A then ∑ y : BitString n, if y ∈ B then muWeight k n m x y else 0 else 0 := by
          intro x; by_cases hx : x ∈ A <;> simp [hx]
        simp_rw [hrhs]
        rw [← sum_filter, filter_mem_eq_inter, univ_inter]

/-! ### Coordinate removal and weight-ratio identities -/

/-- Canonical order-preserving embedding of `Fin (n - k)` onto the complement `Iᶜ` of a
`k`-element subset `I ⊆ Fin n`. -/
def complEmb {n k : ℕ} (I : Finset (Fin n)) (hI : I.card = k) : Fin (n - k) ↪o Fin n :=
  Iᶜ.orderEmbOfFin (by rw [card_compl, Fintype.card_fin, hI])

/-- Every element in the range of `complEmb I hI` lies outside `I`. -/
theorem complEmb_notMem {n k : ℕ} (I : Finset (Fin n)) (hI : I.card = k) (j : Fin (n - k)) :
    complEmb I hI j ∉ I := by
  have hmem : complEmb I hI j ∈ Iᶜ := orderEmbOfFin_mem Iᶜ _ j
  exact mem_compl.mp hmem

/-- `complEmb I hI` surjects onto `Iᶜ`: every `i ∉ I` has a unique preimage in `Fin (n - k)`. -/
theorem exists_complEmb_eq {n k : ℕ} {I : Finset (Fin n)} (hI : I.card = k) {i : Fin n}
    (hi : i ∉ I) : ∃ j : Fin (n - k), complEmb I hI j = i := by
  have hmem : i ∈ Set.range (complEmb I hI) := by
    rw [complEmb, range_orderEmbOfFin]
    exact mem_compl.mpr hi
  exact hmem

/-- Remove the `k` coordinates in `I` from an `n`-bit string `x`, yielding an `(n - k)`-bit string.
-/
def removeCoords {n k : ℕ} (I : Finset (Fin n)) (hI : I.card = k) (x : BitString n) :
    BitString (n - k) :=
  fun j => x (complEmb I hI j)

/-- Insert `true` at every coordinate in `I` into an `(n - k)`-bit string `x'`, recovering an
`n`-bit string whose support contains `I`. -/
noncomputable def insertOnes {n k : ℕ} (I : Finset (Fin n)) (hI : I.card = k)
    (x' : BitString (n - k)) : BitString n := by
  classical
  exact fun i =>
    if hi : i ∈ I then true else x' (exists_complEmb_eq hI hi).choose

/-- Removing coordinates `I` after inserting `true` at `I` recovers the original string. -/
@[simp] theorem removeCoords_insertOnes {n k : ℕ} (I : Finset (Fin n)) (hI : I.card = k)
    (x' : BitString (n - k)) : removeCoords I hI (insertOnes I hI x') = x' := by
  classical
  funext j
  have hnot : complEmb I hI j ∉ I := complEmb_notMem I hI j
  simp only [removeCoords, insertOnes, hnot, ↓reduceDIte]
  have hspec := (exists_complEmb_eq hI hnot).choose_spec
  rw [(complEmb I hI).injective hspec]

/-- On strings whose support contains `I`, inserting `true` at `I` after removing `I` recovers `x`.
-/
theorem insertOnes_removeCoords {n k : ℕ} {I : Finset (Fin n)} (hI : I.card = k)
    {x : BitString n} (hIx : I ⊆ supportSet x) :
    insertOnes I hI (removeCoords I hI x) = x := by
  classical
  funext i
  simp only [insertOnes, removeCoords]
  split_ifs with hi
  · exact (mem_supportSet.mp (hIx hi)).symm
  · rw [(exists_complEmb_eq hI hi).choose_spec]

/-- `insertOnes I hI x'` always has `true` on `I`. -/
theorem subset_supportSet_insertOnes {n k : ℕ} (I : Finset (Fin n)) (hI : I.card = k)
    (x' : BitString (n - k)) : I ⊆ supportSet (insertOnes I hI x') := by
  classical
  intro i hi
  simp [mem_supportSet, insertOnes, hi]

/-- `insertOnes I hI` is injective. -/
theorem insertOnes_injective {n k : ℕ} (I : Finset (Fin n)) (hI : I.card = k) :
    Function.Injective (insertOnes I hI) := by
  intro x' y' h
  have := congrArg (removeCoords I hI) h
  simpa using this

/-- Support cardinality after removing `I ⊆ supportSet x`. -/
theorem card_supportSet_removeCoords {n k : ℕ} {I : Finset (Fin n)} (hI : I.card = k)
    {x : BitString n} (hIx : I ⊆ supportSet x) :
    (supportSet (removeCoords I hI x)).card = (supportSet x).card - k := by
  have himg : (supportSet (removeCoords I hI x)).map (complEmb I hI).toEmbedding =
      supportSet x \ I := by
    ext i
    simp only [mem_map, mem_supportSet, removeCoords, RelEmbedding.coe_toEmbedding, mem_sdiff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hj, complEmb_notMem I hI j⟩
    · rintro ⟨hxi, hiI⟩
      obtain ⟨j, rfl⟩ := exists_complEmb_eq hI hiI
      exact ⟨j, hxi, rfl⟩
  have hcard := congrArg Finset.card himg
  rw [card_map, card_sdiff_of_subset hIx, hI] at hcard
  exact hcard

/-- Intersection cardinality after removing `I ⊆ interSet x y`. -/
theorem card_interSet_removeCoords {n k : ℕ} {I : Finset (Fin n)} (hI : I.card = k)
    {x y : BitString n} (hIxy : I ⊆ interSet x y) :
    (interSet (removeCoords I hI x) (removeCoords I hI y)).card = (interSet x y).card - k := by
  have himg : (interSet (removeCoords I hI x) (removeCoords I hI y)).map
      (complEmb I hI).toEmbedding = interSet x y \ I := by
    ext i
    simp only [mem_map, mem_interSet, removeCoords, RelEmbedding.coe_toEmbedding, mem_sdiff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hj, complEmb_notMem I hI j⟩
    · rintro ⟨hxyi, hiI⟩
      obtain ⟨j, rfl⟩ := exists_complEmb_eq hI hiI
      exact ⟨j, hxyi, rfl⟩
  have hcard := congrArg Finset.card himg
  rw [card_map, card_sdiff_of_subset hIxy, hI] at hcard
  exact hcard

/-- Support cardinality of `insertOnes I hI x'`. -/
theorem card_supportSet_insertOnes {n k : ℕ} (I : Finset (Fin n)) (hI : I.card = k)
    (x' : BitString (n - k)) :
    (supportSet (insertOnes I hI x')).card = (supportSet x').card + k := by
  have hsub := subset_supportSet_insertOnes I hI x'
  have h := card_supportSet_removeCoords hI hsub
  rw [removeCoords_insertOnes] at h
  have hge : k ≤ (supportSet (insertOnes I hI x')).card := hI.symm.trans_le (card_le_card hsub)
  omega

/-- Intersection cardinality of `insertOnes I hI x'` and `insertOnes I hI y'`. -/
theorem card_interSet_insertOnes {n k : ℕ} (I : Finset (Fin n)) (hI : I.card = k)
    (x' y' : BitString (n - k)) :
    (interSet (insertOnes I hI x') (insertOnes I hI y')).card = (interSet x' y').card + k := by
  have hsub : I ⊆ interSet (insertOnes I hI x') (insertOnes I hI y') := by
    rw [interSet_eq_inter]
    exact subset_inter (subset_supportSet_insertOnes I hI x')
      (subset_supportSet_insertOnes I hI y')
  have h := card_interSet_removeCoords hI hsub
  rw [removeCoords_insertOnes, removeCoords_insertOnes] at h
  have hge : k ≤ (interSet (insertOnes I hI x') (insertOnes I hI y')).card :=
    hI.symm.trans_le (card_le_card hsub)
  omega

/-- Cast an `(n + k - k)`-bit string cleanly to an `n`-bit string. -/
@[expose] def castAddSub {n k : ℕ} (x : BitString (n + k - k)) : BitString n :=
  fun i => x (i.cast (Nat.add_sub_cancel n k).symm)

/-- Support cardinality is preserved by `castAddSub`. -/
@[simp] theorem card_supportSet_castAddSub {n k : ℕ} (x : BitString (n + k - k)) :
    (supportSet (castAddSub x)).card = (supportSet x).card := by
  refine Finset.card_bij (fun i _ => i.cast (Nat.add_sub_cancel n k).symm)
    (fun i hi => by simpa [castAddSub] using hi)
    (fun i₁ _ i₂ _ h => Fin.ext (by simpa using congrArg Fin.val h))
    (fun j hj => ⟨j.cast (Nat.add_sub_cancel n k), by simpa [castAddSub] using hj,
      Fin.ext rfl⟩)

/-- Intersection cardinality is preserved by `castAddSub`. -/
@[simp] theorem card_interSet_castAddSub {n k : ℕ} (x y : BitString (n + k - k)) :
    (interSet (castAddSub x) (castAddSub y)).card = (interSet x y).card := by
  refine Finset.card_bij (fun i _ => i.cast (Nat.add_sub_cancel n k).symm)
    (fun i hi => by simpa [castAddSub] using hi)
    (fun i₁ _ i₂ _ h => Fin.ext (by simpa using congrArg Fin.val h))
    (fun j hj => ⟨j.cast (Nat.add_sub_cancel n k), by simpa [castAddSub] using hj,
      Fin.ext rfl⟩)

/-- Remove `k` coordinates `I` from an `(n + k)`-bit string, returning a `BitString n`. -/
def removeCoordsAdd {n k : ℕ} (I : Finset (Fin (n + k))) (hI : I.card = k)
    (x : BitString (n + k)) : BitString n :=
  castAddSub (removeCoords I hI x)

/-- Insert `true` at `k` coordinates `I ⊆ Fin (n + k)` into an `n`-bit string. -/
noncomputable def insertOnesAdd {n k : ℕ} (I : Finset (Fin (n + k))) (hI : I.card = k)
    (x' : BitString n) : BitString (n + k) :=
  insertOnes I hI (fun j => x' (j.cast (Nat.add_sub_cancel n k)))

/-- `removeCoordsAdd` cancels `insertOnesAdd`. -/
@[simp] theorem removeCoordsAdd_insertOnesAdd {n k : ℕ} (I : Finset (Fin (n + k)))
    (hI : I.card = k) (x' : BitString n) :
    removeCoordsAdd I hI (insertOnesAdd I hI x') = x' := by
  funext i
  simp [removeCoordsAdd, insertOnesAdd, castAddSub]

/-- `insertOnesAdd` cancels `removeCoordsAdd` when `I ⊆ supportSet x`. -/
theorem insertOnesAdd_removeCoordsAdd {n k : ℕ} {I : Finset (Fin (n + k))} (hI : I.card = k)
    {x : BitString (n + k)} (hIx : I ⊆ supportSet x) :
    insertOnesAdd I hI (removeCoordsAdd I hI x) = x := by
  have hfun : (fun j : Fin (n + k - k) =>
      removeCoordsAdd I hI x (j.cast (Nat.add_sub_cancel n k))) = removeCoords I hI x := by
    funext j
    simp [removeCoordsAdd, castAddSub]
  rw [insertOnesAdd, hfun, insertOnes_removeCoords hI hIx]

/-- Restrict a subset `A ⊆ BitString n` by fixing `I` to `true` and deleting `I`. -/
@[expose] noncomputable def restrictSide {n k : ℕ} (I : Finset (Fin n)) (hI : I.card = k)
    (A : Finset (BitString n)) : Finset (BitString (n - k)) :=
  univ.filter fun x' => insertOnes I hI x' ∈ A

/-- Restrict a subset `A ⊆ BitString (n + k)` by fixing `I` to `true` and deleting `I`. -/
@[expose] noncomputable def restrictSideAdd {n k : ℕ} (I : Finset (Fin (n + k))) (hI : I.card = k)
    (A : Finset (BitString (n + k))) : Finset (BitString n) :=
  univ.filter fun x' => insertOnesAdd I hI x' ∈ A

/-- The sub-side of `A` consisting of strings that are `true` on `I`. -/
@[expose] def sliceSide {n : ℕ} (I : Finset (Fin n)) (A : Finset (BitString n)) :
    Finset (BitString n) :=
  A.filter fun x => I ⊆ supportSet x

/-- First coordinate-removal weight identity:
`μ_{2k, n+k, m+k}(x, y) = (C(n, k) / C(n + k, 2k)) * μ_{k, n, m}(x', y')`
where `x', y'` result from removing `k` intersecting coordinates `I ⊆ x ∩ y`. -/
theorem muWeight_two_mul_add {n k m : ℕ} (hkn : k ≤ n) {I : Finset (Fin (n + k))}
    (hI : I.card = k) {x y : BitString (n + k)} (hIxy : I ⊆ interSet x y) :
    muWeight (2 * k) (n + k) (m + k) x y =
      ((n.choose k : ℝ) / ((n + k).choose (2 * k) : ℝ)) *
        muWeight k n m (removeCoordsAdd I hI x) (removeCoordsAdd I hI y) := by
  have hIx : I ⊆ supportSet x := by
    rw [interSet_eq_inter] at hIxy; exact hIxy.trans inter_subset_left
  have hIy : I ⊆ supportSet y := by
    rw [interSet_eq_inter] at hIxy; exact hIxy.trans inter_subset_right
  have hx' : (supportSet (removeCoordsAdd I hI x)).card = (supportSet x).card - k := by
    rw [removeCoordsAdd, card_supportSet_castAddSub, card_supportSet_removeCoords hI hIx]
  have hy' : (supportSet (removeCoordsAdd I hI y)).card = (supportSet y).card - k := by
    rw [removeCoordsAdd, card_supportSet_castAddSub, card_supportSet_removeCoords hI hIy]
  have hxy' : (interSet (removeCoordsAdd I hI x) (removeCoordsAdd I hI y)).card =
      (interSet x y).card - k := by
    rw [removeCoordsAdd, removeCoordsAdd, card_interSet_castAddSub,
      card_interSet_removeCoords hI hIxy]
  have hge_x : k ≤ (supportSet x).card := hI.symm.trans_le (card_le_card hIx)
  have hge_y : k ≤ (supportSet y).card := hI.symm.trans_le (card_le_card hIy)
  have hge_xy : k ≤ (interSet x y).card := hI.symm.trans_le (card_le_card hIxy)
  have hmem_iff : (x, y) ∈ weightPairs (2 * k) (n + k) (m + k) ↔
      (removeCoordsAdd I hI x, removeCoordsAdd I hI y) ∈ weightPairs k n m := by
    simp only [mem_weightPairs, hx', hy', hxy']
    omega
  by_cases hmem : (x, y) ∈ weightPairs (2 * k) (n + k) (m + k)
  · have hmem' : (removeCoordsAdd I hI x, removeCoordsAdd I hI y) ∈ weightPairs k n m :=
      hmem_iff.mp hmem
    rw [muWeight_of_mem hmem, muWeight_of_mem hmem']
    have hpos' : 0 < weightCard k n m := by
      rw [← card_weightPairs]
      exact Finset.card_pos.mpr ⟨_, hmem'⟩
    obtain ⟨hkm, h2m⟩ := weightCard_pos_iff.mp hpos'
    have hpos : 0 < weightCard (2 * k) (n + k) (m + k) :=
      weightCard_pos_iff.mpr ⟨by omega, by omega⟩
    have hchoose_pos : 0 < (n + k).choose (2 * k) := Nat.choose_pos (by omega)
    have hfact1 := weightCard_mul_factorials hkm h2m
    have hfact2 := weightCard_mul_factorials (k := 2 * k) (n := n + k) (m := m + k)
      (by omega) (by omega)
    have hc1 := Nat.choose_mul_factorial_mul_factorial hkn
    have hc2 := Nat.choose_mul_factorial_mul_factorial (show 2 * k ≤ n + k by omega)
    have hnat : weightCard k n m * (n + k).choose (2 * k) =
        weightCard (2 * k) (n + k) (m + k) * n.choose k := by
      have hmul : (weightCard k n m * (n + k).choose (2 * k)) *
          ((2 * k).factorial * k.factorial * (n - k).factorial *
            (m - k).factorial * (m - k).factorial * (n + k - 2 * m).factorial) =
          (weightCard (2 * k) (n + k) (m + k) * n.choose k) *
          ((2 * k).factorial * k.factorial * (n - k).factorial *
            (m - k).factorial * (m - k).factorial * (n + k - 2 * m).factorial) := by
        have hsub1 : n + k - 2 * k = n - k := by omega
        have hsub2 : m + k - 2 * k = m - k := by omega
        have hsub3 : n + k + 2 * k - 2 * (m + k) = n + k - 2 * m := by omega
        rw [hsub1] at hc2
        rw [hsub2, hsub3] at hfact2
        calc
          (weightCard k n m * (n + k).choose (2 * k)) *
              ((2 * k).factorial * k.factorial * (n - k).factorial *
                (m - k).factorial * (m - k).factorial * (n + k - 2 * m).factorial)
            = (weightCard k n m * (k.factorial * (m - k).factorial * (m - k).factorial *
                (n + k - 2 * m).factorial)) *
              ((n + k).choose (2 * k) * (2 * k).factorial * (n - k).factorial) := by ring
          _ = n.factorial * (n + k).factorial := by rw [hfact1, hc2]
          _ = (weightCard (2 * k) (n + k) (m + k) *
                ((2 * k).factorial * (m - k).factorial * (m - k).factorial *
                  (n + k - 2 * m).factorial)) *
              (n.choose k * k.factorial * (n - k).factorial) := by rw [hfact2, hc1]; ring
          _ = (weightCard (2 * k) (n + k) (m + k) * n.choose k) *
              ((2 * k).factorial * k.factorial * (n - k).factorial *
                (m - k).factorial * (m - k).factorial * (n + k - 2 * m).factorial) := by ring
      have hfac_pos : 0 < (2 * k).factorial * k.factorial * (n - k).factorial *
          (m - k).factorial * (m - k).factorial * (n + k - 2 * m).factorial := by positivity
      exact Nat.eq_of_mul_eq_mul_right hfac_pos hmul
    have hreal : (weightCard k n m : ℝ) * ((n + k).choose (2 * k) : ℝ) =
        (weightCard (2 * k) (n + k) (m + k) : ℝ) * (n.choose k : ℝ) := by
      exact_mod_cast hnat
    have h1 : (weightCard (2 * k) (n + k) (m + k) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    have h2 : (weightCard k n m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos'.ne'
    have h3 : ((n + k).choose (2 * k) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hchoose_pos.ne'
    field_simp
    linarith
  · rw [muWeight_eq_zero_of_notMem hmem, muWeight_eq_zero_of_notMem (mt hmem_iff.mpr hmem),
      mul_zero]

/-- Second coordinate-removal weight identity:
`μ_{k, n+k, m+k}(x, y) = (1 / C(n + k, k)) * μ_{0, n, m}(x', y')`
where `x', y'` result from removing `k` intersecting coordinates `I ⊆ x ∩ y`. -/
theorem muWeight_add {n k m : ℕ} {I : Finset (Fin (n + k))} (hI : I.card = k)
    {x y : BitString (n + k)} (hIxy : I ⊆ interSet x y) :
    muWeight k (n + k) (m + k) x y =
      (((n + k).choose k : ℝ))⁻¹ *
        muWeight 0 n m (removeCoordsAdd I hI x) (removeCoordsAdd I hI y) := by
  have hIx : I ⊆ supportSet x := by
    rw [interSet_eq_inter] at hIxy; exact hIxy.trans inter_subset_left
  have hIy : I ⊆ supportSet y := by
    rw [interSet_eq_inter] at hIxy; exact hIxy.trans inter_subset_right
  have hx' : (supportSet (removeCoordsAdd I hI x)).card = (supportSet x).card - k := by
    rw [removeCoordsAdd, card_supportSet_castAddSub, card_supportSet_removeCoords hI hIx]
  have hy' : (supportSet (removeCoordsAdd I hI y)).card = (supportSet y).card - k := by
    rw [removeCoordsAdd, card_supportSet_castAddSub, card_supportSet_removeCoords hI hIy]
  have hxy' : (interSet (removeCoordsAdd I hI x) (removeCoordsAdd I hI y)).card =
      (interSet x y).card - k := by
    rw [removeCoordsAdd, removeCoordsAdd, card_interSet_castAddSub,
      card_interSet_removeCoords hI hIxy]
  have hge_x : k ≤ (supportSet x).card := hI.symm.trans_le (card_le_card hIx)
  have hge_y : k ≤ (supportSet y).card := hI.symm.trans_le (card_le_card hIy)
  have hge_xy : k ≤ (interSet x y).card := hI.symm.trans_le (card_le_card hIxy)
  have hmem_iff : (x, y) ∈ weightPairs k (n + k) (m + k) ↔
      (removeCoordsAdd I hI x, removeCoordsAdd I hI y) ∈ weightPairs 0 n m := by
    simp only [mem_weightPairs, hx', hy', hxy']
    omega
  by_cases hmem : (x, y) ∈ weightPairs k (n + k) (m + k)
  · have hmem' : (removeCoordsAdd I hI x, removeCoordsAdd I hI y) ∈ weightPairs 0 n m :=
      hmem_iff.mp hmem
    rw [muWeight_of_mem hmem, muWeight_of_mem hmem']
    have hpos' : 0 < weightCard 0 n m := by
      rw [← card_weightPairs]; exact Finset.card_pos.mpr ⟨_, hmem'⟩
    obtain ⟨_, h2m⟩ := weightCard_pos_iff.mp hpos'
    have hpos : 0 < weightCard k (n + k) (m + k) :=
      weightCard_pos_iff.mpr ⟨by omega, by omega⟩
    have hchoose_pos : 0 < (n + k).choose k := Nat.choose_pos (by omega)
    have hfact1 := weightCard_mul_factorials (k := 0) (n := n) (m := m) (Nat.zero_le m) h2m
    have hfact2 := weightCard_mul_factorials (k := k) (n := n + k) (m := m + k)
      (by omega) (by omega)
    have hc := Nat.choose_mul_factorial_mul_factorial (show k ≤ n + k by omega)
    have hnat : weightCard 0 n m * (n + k).choose k = weightCard k (n + k) (m + k) := by
      have hsub1 : n + k - k = n := by omega
      have hsub2 : m + k - k = m := by omega
      have hsub3 : n + k + k - 2 * (m + k) = n - 2 * m := by omega
      rw [hsub1] at hc
      rw [hsub2, hsub3] at hfact2
      simp only [Nat.factorial_zero, Nat.sub_zero, Nat.add_zero, one_mul] at hfact1
      have hmul : (weightCard 0 n m * (n + k).choose k) *
          (k.factorial * m.factorial * m.factorial * (n - 2 * m).factorial) =
          weightCard k (n + k) (m + k) *
          (k.factorial * m.factorial * m.factorial * (n - 2 * m).factorial) := by
        calc
          (weightCard 0 n m * (n + k).choose k) *
              (k.factorial * m.factorial * m.factorial * (n - 2 * m).factorial)
            = (weightCard 0 n m * (m.factorial * m.factorial * (n - 2 * m).factorial)) *
              ((n + k).choose k * k.factorial) := by ring
          _ = n.factorial * ((n + k).choose k * k.factorial) := by rw [hfact1]
          _ = (n + k).choose k * k.factorial * n.factorial := by ring
          _ = (n + k).factorial := hc
          _ = weightCard k (n + k) (m + k) *
              (k.factorial * m.factorial * m.factorial * (n - 2 * m).factorial) := hfact2.symm
      have hfac_pos : 0 < k.factorial * m.factorial * m.factorial * (n - 2 * m).factorial := by
        positivity
      exact Nat.eq_of_mul_eq_mul_right hfac_pos hmul
    have hreal : (weightCard 0 n m : ℝ) * ((n + k).choose k : ℝ) =
        (weightCard k (n + k) (m + k) : ℝ) := by exact_mod_cast hnat
    have h1 : (weightCard k (n + k) (m + k) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    have h2 : (weightCard 0 n m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos'.ne'
    have h3 : ((n + k).choose k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hchoose_pos.ne'
    field_simp
    linarith
  · rw [muWeight_eq_zero_of_notMem hmem, muWeight_eq_zero_of_notMem (mt hmem_iff.mpr hmem),
      mul_zero]

/-- Third coordinate-removal weight identity:
`μ_{k, n, m}(x, y) = (1 / C(n, k)) * μ_{0, n - k, m - k}(x', y')`
where `x', y'` result from removing `k` intersecting coordinates `I ⊆ x ∩ y`. -/
theorem muWeight_sub {n k m : ℕ} (hkn : k ≤ n) (hkm : k ≤ m) {I : Finset (Fin n)}
    (hI : I.card = k) {x y : BitString n} (hIxy : I ⊆ interSet x y) :
    muWeight k n m x y =
      ((n.choose k : ℝ))⁻¹ *
        muWeight 0 (n - k) (m - k) (removeCoords I hI x) (removeCoords I hI y) := by
  have hIx : I ⊆ supportSet x := by
    rw [interSet_eq_inter] at hIxy; exact hIxy.trans inter_subset_left
  have hIy : I ⊆ supportSet y := by
    rw [interSet_eq_inter] at hIxy; exact hIxy.trans inter_subset_right
  have hx' := card_supportSet_removeCoords hI hIx
  have hy' := card_supportSet_removeCoords hI hIy
  have hxy' := card_interSet_removeCoords hI hIxy
  have hge_x : k ≤ (supportSet x).card := hI.symm.trans_le (card_le_card hIx)
  have hge_y : k ≤ (supportSet y).card := hI.symm.trans_le (card_le_card hIy)
  have hge_xy : k ≤ (interSet x y).card := hI.symm.trans_le (card_le_card hIxy)
  have hmem_iff : (x, y) ∈ weightPairs k n m ↔
      (removeCoords I hI x, removeCoords I hI y) ∈ weightPairs 0 (n - k) (m - k) := by
    simp only [mem_weightPairs, hx', hy', hxy']
    omega
  by_cases hmem : (x, y) ∈ weightPairs k n m
  · have hmem' : (removeCoords I hI x, removeCoords I hI y) ∈ weightPairs 0 (n - k) (m - k) :=
      hmem_iff.mp hmem
    rw [muWeight_of_mem hmem, muWeight_of_mem hmem']
    have hpos' : 0 < weightCard 0 (n - k) (m - k) := by
      rw [← card_weightPairs]; exact Finset.card_pos.mpr ⟨_, hmem'⟩
    obtain ⟨_, h2m'⟩ := weightCard_pos_iff.mp hpos'
    have hpos : 0 < weightCard k n m := weightCard_pos_iff.mpr ⟨hkm, by omega⟩
    have hchoose_pos : 0 < n.choose k := Nat.choose_pos hkn
    have hfact1 := weightCard_mul_factorials (k := 0) (n := n - k) (m := m - k)
      (Nat.zero_le _) h2m'
    have hfact2 := weightCard_mul_factorials hkm (show 2 * m ≤ n + k by omega)
    have hc := Nat.choose_mul_factorial_mul_factorial hkn
    have hnat : weightCard 0 (n - k) (m - k) * n.choose k = weightCard k n m := by
      have hsub : n - k - 2 * (m - k) = n + k - 2 * m := by omega
      simp only [Nat.factorial_zero, Nat.sub_zero, Nat.add_zero, one_mul, hsub] at hfact1
      have hmul : (weightCard 0 (n - k) (m - k) * n.choose k) *
          (k.factorial * (m - k).factorial * (m - k).factorial * (n + k - 2 * m).factorial) =
          weightCard k n m *
          (k.factorial * (m - k).factorial * (m - k).factorial * (n + k - 2 * m).factorial) := by
        calc
          (weightCard 0 (n - k) (m - k) * n.choose k) *
              (k.factorial * (m - k).factorial * (m - k).factorial * (n + k - 2 * m).factorial)
            = (weightCard 0 (n - k) (m - k) *
                ((m - k).factorial * (m - k).factorial * (n + k - 2 * m).factorial)) *
              (n.choose k * k.factorial) := by ring
          _ = (n - k).factorial * (n.choose k * k.factorial) := by rw [hfact1]
          _ = n.choose k * k.factorial * (n - k).factorial := by ring
          _ = n.factorial := hc
          _ = weightCard k n m * (k.factorial * (m - k).factorial * (m - k).factorial *
                (n + k - 2 * m).factorial) := hfact2.symm
      have hfac_pos : 0 < k.factorial * (m - k).factorial * (m - k).factorial *
          (n + k - 2 * m).factorial := by positivity
      exact Nat.eq_of_mul_eq_mul_right hfac_pos hmul
    have hreal : (weightCard 0 (n - k) (m - k) : ℝ) * (n.choose k : ℝ) =
        (weightCard k n m : ℝ) := by exact_mod_cast hnat
    have h1 : (weightCard k n m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    have h2 : (weightCard 0 (n - k) (m - k) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos'.ne'
    have h3 : (n.choose k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hchoose_pos.ne'
    field_simp
    linarith
  · rw [muWeight_eq_zero_of_notMem hmem, muWeight_eq_zero_of_notMem (mt hmem_iff.mpr hmem),
      mul_zero]

/-- Fourth coordinate-removal weight identity:
`μ_{k+1, n, m}(x, y) = ((n - k) / C(n, k + 1)) * μ_{1, n - k, m - k}(x', y')`
where `x', y'` result from removing `k` intersecting coordinates `I ⊆ x ∩ y`. -/
theorem muWeight_succ_sub {n k m : ℕ} (hkn : k + 1 ≤ n) (hkm : k ≤ m) {I : Finset (Fin n)}
    (hI : I.card = k) {x y : BitString n} (hIxy : I ⊆ interSet x y) :
    muWeight (k + 1) n m x y =
      (((n - k : ℕ) : ℝ) / (n.choose (k + 1) : ℝ)) *
        muWeight 1 (n - k) (m - k) (removeCoords I hI x) (removeCoords I hI y) := by
  have hIx : I ⊆ supportSet x := by
    rw [interSet_eq_inter] at hIxy; exact hIxy.trans inter_subset_left
  have hIy : I ⊆ supportSet y := by
    rw [interSet_eq_inter] at hIxy; exact hIxy.trans inter_subset_right
  have hx' := card_supportSet_removeCoords hI hIx
  have hy' := card_supportSet_removeCoords hI hIy
  have hxy' := card_interSet_removeCoords hI hIxy
  have hge_x : k ≤ (supportSet x).card := hI.symm.trans_le (card_le_card hIx)
  have hge_y : k ≤ (supportSet y).card := hI.symm.trans_le (card_le_card hIy)
  have hge_xy : k ≤ (interSet x y).card := hI.symm.trans_le (card_le_card hIxy)
  have hmem_iff : (x, y) ∈ weightPairs (k + 1) n m ↔
      (removeCoords I hI x, removeCoords I hI y) ∈ weightPairs 1 (n - k) (m - k) := by
    simp only [mem_weightPairs, hx', hy', hxy']
    omega
  by_cases hmem : (x, y) ∈ weightPairs (k + 1) n m
  · have hmem' : (removeCoords I hI x, removeCoords I hI y) ∈ weightPairs 1 (n - k) (m - k) :=
      hmem_iff.mp hmem
    rw [muWeight_of_mem hmem, muWeight_of_mem hmem']
    have hpos' : 0 < weightCard 1 (n - k) (m - k) := by
      rw [← card_weightPairs]; exact Finset.card_pos.mpr ⟨_, hmem'⟩
    obtain ⟨h1m', h2m'⟩ := weightCard_pos_iff.mp hpos'
    have hpos : 0 < weightCard (k + 1) n m := weightCard_pos_iff.mpr ⟨by omega, by omega⟩
    have hchoose_pos : 0 < n.choose (k + 1) := Nat.choose_pos hkn
    have hfact1 := weightCard_mul_factorials h1m' h2m'
    have hfact2 := weightCard_mul_factorials (k := k + 1) (n := n) (m := m)
      (by omega) (by omega)
    have hc := Nat.choose_mul_factorial_mul_factorial hkn
    have hfac_nk : (n - k).factorial = (n - k) * (n - (k + 1)).factorial := by
      have h : n - k = (n - (k + 1)) + 1 := by omega
      conv_lhs => rw [h, Nat.factorial_succ]
      rw [← h]
    have hnat : weightCard 1 (n - k) (m - k) * n.choose (k + 1) =
        weightCard (k + 1) n m * (n - k) := by
      have hsub1 : m - k - 1 = m - (k + 1) := by omega
      have hsub2 : n - k + 1 - 2 * (m - k) = n + (k + 1) - 2 * m := by omega
      simp only [Nat.factorial_one, one_mul, hsub1, hsub2] at hfact1
      have hmul : (weightCard 1 (n - k) (m - k) * n.choose (k + 1)) *
          ((k + 1).factorial * (n - (k + 1)).factorial *
            (m - (k + 1)).factorial * (m - (k + 1)).factorial *
            (n + (k + 1) - 2 * m).factorial) =
          (weightCard (k + 1) n m * (n - k)) *
          ((k + 1).factorial * (n - (k + 1)).factorial *
            (m - (k + 1)).factorial * (m - (k + 1)).factorial *
            (n + (k + 1) - 2 * m).factorial) := by
        calc
          (weightCard 1 (n - k) (m - k) * n.choose (k + 1)) *
              ((k + 1).factorial * (n - (k + 1)).factorial *
                (m - (k + 1)).factorial * (m - (k + 1)).factorial *
                (n + (k + 1) - 2 * m).factorial)
            = (weightCard 1 (n - k) (m - k) * ((m - (k + 1)).factorial *
                (m - (k + 1)).factorial * (n + (k + 1) - 2 * m).factorial)) *
              (n.choose (k + 1) * (k + 1).factorial * (n - (k + 1)).factorial) := by ring
          _ = (n - k).factorial * n.factorial := by rw [hfact1, hc]
          _ = (n - k) * (n - (k + 1)).factorial *
              (weightCard (k + 1) n m * ((k + 1).factorial * (m - (k + 1)).factorial *
                (m - (k + 1)).factorial * (n + (k + 1) - 2 * m).factorial)) := by
              rw [hfac_nk, hfact2]
          _ = (weightCard (k + 1) n m * (n - k)) *
              ((k + 1).factorial * (n - (k + 1)).factorial *
                (m - (k + 1)).factorial * (m - (k + 1)).factorial *
                (n + (k + 1) - 2 * m).factorial) := by ring
      have hfac_pos : 0 < (k + 1).factorial * (n - (k + 1)).factorial *
          (m - (k + 1)).factorial * (m - (k + 1)).factorial *
          (n + (k + 1) - 2 * m).factorial := by positivity
      exact Nat.eq_of_mul_eq_mul_right hfac_pos hmul
    have hreal : (weightCard 1 (n - k) (m - k) : ℝ) * (n.choose (k + 1) : ℝ) =
        (weightCard (k + 1) n m : ℝ) * ((n - k : ℕ) : ℝ) := by exact_mod_cast hnat
    have h1 : (weightCard (k + 1) n m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    have h2 : (weightCard 1 (n - k) (m - k) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos'.ne'
    have h3 : (n.choose (k + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hchoose_pos.ne'
    field_simp
    linarith
  · rw [muWeight_eq_zero_of_notMem hmem, muWeight_eq_zero_of_notMem (mt hmem_iff.mpr hmem),
      mul_zero]

/-! ### Rectangle-level coordinate-removal identities -/

/-- Summing a function over `sliceSide I A` equals summing an indicator over `A`. -/
theorem sum_sliceSide {n : ℕ} {M : Type*} [AddCommMonoid M] (I : Finset (Fin n))
    (A : Finset (BitString n)) (f : BitString n → M) :
    ∑ x ∈ sliceSide I A, f x = ∑ x ∈ A, if I ⊆ supportSet x then f x else 0 :=
  sum_filter _ _

/-- Summing a function over `sliceSide I A` equals summing over `restrictSide I hI A` via
`insertOnes I hI`. -/
theorem sum_sliceSide_eq_sum_restrictSide {n k : ℕ} {I : Finset (Fin n)} (hI : I.card = k)
    (A : Finset (BitString n)) {M : Type*} [AddCommMonoid M] (f : BitString n → M) :
    ∑ x ∈ sliceSide I A, f x = ∑ x' ∈ restrictSide I hI A, f (insertOnes I hI x') := by
  refine Finset.sum_nbij' (removeCoords I hI) (insertOnes I hI) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxA, hIx⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_univ _, by rwa [insertOnes_removeCoords hI hIx]⟩
  · intro x' hx'
    exact mem_filter.mpr ⟨(mem_filter.mp hx').2, subset_supportSet_insertOnes I hI x'⟩
  · intro x hx
    exact insertOnes_removeCoords hI (mem_filter.mp hx).2
  · intro x' _
    exact removeCoords_insertOnes I hI x'
  · intro x hx
    rw [insertOnes_removeCoords hI (mem_filter.mp hx).2]

/-- Summing a function over `sliceSide I A` (in `n + k` coordinates) equals summing over
`restrictSideAdd I hI A` via `insertOnesAdd I hI`. -/
theorem sum_sliceSide_eq_sum_restrictSideAdd {n k : ℕ} {I : Finset (Fin (n + k))}
    (hI : I.card = k) (A : Finset (BitString (n + k))) {M : Type*} [AddCommMonoid M]
    (f : BitString (n + k) → M) :
    ∑ x ∈ sliceSide I A, f x = ∑ x' ∈ restrictSideAdd I hI A, f (insertOnesAdd I hI x') := by
  refine Finset.sum_nbij' (removeCoordsAdd I hI) (insertOnesAdd I hI) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxA, hIx⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_univ _, by rwa [insertOnesAdd_removeCoordsAdd hI hIx]⟩
  · intro x' hx'
    exact mem_filter.mpr ⟨(mem_filter.mp hx').2, subset_supportSet_insertOnes I hI _⟩
  · intro x hx
    exact insertOnesAdd_removeCoordsAdd hI (mem_filter.mp hx).2
  · intro x' _
    exact removeCoordsAdd_insertOnesAdd I hI x'
  · intro x hx
    rw [insertOnesAdd_removeCoordsAdd hI (mem_filter.mp hx).2]

/-- First rectangle-level coordinate-removal identity: for `R = A × B` whose elements all
intersect on `I` (`|I| = k`),
`μ_{2k, n+k, m+k}(R) = (C(n, k) / C(n + k, 2k)) * μ_{k, n, m}(R')`. -/
theorem muRect_two_mul_add {n k m : ℕ} (hkn : k ≤ n) {I : Finset (Fin (n + k))}
    (hI : I.card = k) {A B : Finset (BitString (n + k))}
    (hA : ∀ x ∈ A, I ⊆ supportSet x) (hB : ∀ y ∈ B, I ⊆ supportSet y) :
    muRect (2 * k) (n + k) (m + k) A B =
      ((n.choose k : ℝ) / ((n + k).choose (2 * k) : ℝ)) *
        muRect k n m (restrictSideAdd I hI A) (restrictSideAdd I hI B) := by
  have hAs : sliceSide I A = A := filter_true_of_mem hA
  have hBs : sliceSide I B = B := filter_true_of_mem hB
  unfold muRect
  conv_lhs => rw [← hAs, sum_sliceSide_eq_sum_restrictSideAdd hI A]
  rw [mul_sum]
  refine sum_congr rfl fun x' _ => ?_
  conv_lhs => rw [← hBs, sum_sliceSide_eq_sum_restrictSideAdd hI B]
  rw [mul_sum]
  refine sum_congr rfl fun y' _ => ?_
  have hIxy : I ⊆ interSet (insertOnesAdd I hI x') (insertOnesAdd I hI y') := by
    rw [interSet_eq_inter]
    exact subset_inter (subset_supportSet_insertOnes I hI _)
      (subset_supportSet_insertOnes I hI _)
  have h := muWeight_two_mul_add hkn hI hIxy (m := m)
  rwa [removeCoordsAdd_insertOnesAdd, removeCoordsAdd_insertOnesAdd] at h

/-- Second rectangle-level coordinate-removal identity: for `R = A × B` whose elements all
intersect on `I` (`|I| = k`),
`μ_{k, n+k, m+k}(R) = (1 / C(n + k, k)) * μ_{0, n, m}(R')`. -/
theorem muRect_add {n k m : ℕ} {I : Finset (Fin (n + k))} (hI : I.card = k)
    {A B : Finset (BitString (n + k))}
    (hA : ∀ x ∈ A, I ⊆ supportSet x) (hB : ∀ y ∈ B, I ⊆ supportSet y) :
    muRect k (n + k) (m + k) A B =
      (((n + k).choose k : ℝ))⁻¹ *
        muRect 0 n m (restrictSideAdd I hI A) (restrictSideAdd I hI B) := by
  have hAs : sliceSide I A = A := filter_true_of_mem hA
  have hBs : sliceSide I B = B := filter_true_of_mem hB
  unfold muRect
  conv_lhs => rw [← hAs, sum_sliceSide_eq_sum_restrictSideAdd hI A]
  rw [mul_sum]
  refine sum_congr rfl fun x' _ => ?_
  conv_lhs => rw [← hBs, sum_sliceSide_eq_sum_restrictSideAdd hI B]
  rw [mul_sum]
  refine sum_congr rfl fun y' _ => ?_
  have hIxy : I ⊆ interSet (insertOnesAdd I hI x') (insertOnesAdd I hI y') := by
    rw [interSet_eq_inter]
    exact subset_inter (subset_supportSet_insertOnes I hI _)
      (subset_supportSet_insertOnes I hI _)
  have h := muWeight_add hI hIxy (m := m)
  rwa [removeCoordsAdd_insertOnesAdd, removeCoordsAdd_insertOnesAdd] at h

/-- Third rectangle-level coordinate-removal identity: for `R_I = sliceSide I A × sliceSide I B`
(`|I| = k`),
`μ_{k, n, m}(R_I) = (1 / C(n, k)) * μ_{0, n - k, m - k}(R_I')`. -/
theorem muRect_slice_sub {n k m : ℕ} (hkn : k ≤ n) (hkm : k ≤ m) {I : Finset (Fin n)}
    (hI : I.card = k) (A B : Finset (BitString n)) :
    muRect k n m (sliceSide I A) (sliceSide I B) =
      ((n.choose k : ℝ))⁻¹ *
        muRect 0 (n - k) (m - k) (restrictSide I hI A) (restrictSide I hI B) := by
  unfold muRect
  rw [sum_sliceSide_eq_sum_restrictSide hI A, mul_sum]
  refine sum_congr rfl fun x' _ => ?_
  rw [sum_sliceSide_eq_sum_restrictSide hI B, mul_sum]
  refine sum_congr rfl fun y' _ => ?_
  have hIxy : I ⊆ interSet (insertOnes I hI x') (insertOnes I hI y') := by
    rw [interSet_eq_inter]
    exact subset_inter (subset_supportSet_insertOnes I hI x')
      (subset_supportSet_insertOnes I hI y')
  have h := muWeight_sub hkn hkm hI hIxy
  rwa [removeCoords_insertOnes, removeCoords_insertOnes] at h

/-- Fourth rectangle-level coordinate-removal identity: for `R_I = sliceSide I A × sliceSide I B`
(`|I| = k`),
`μ_{k + 1, n, m}(R_I) = ((n - k) / C(n, k + 1)) * μ_{1, n - k, m - k}(R_I')`. -/
theorem muRect_slice_succ_sub {n k m : ℕ} (hkn : k + 1 ≤ n) (hkm : k ≤ m) {I : Finset (Fin n)}
    (hI : I.card = k) (A B : Finset (BitString n)) :
    muRect (k + 1) n m (sliceSide I A) (sliceSide I B) =
      (((n - k : ℕ) : ℝ) / (n.choose (k + 1) : ℝ)) *
        muRect 1 (n - k) (m - k) (restrictSide I hI A) (restrictSide I hI B) := by
  unfold muRect
  rw [sum_sliceSide_eq_sum_restrictSide hI A, mul_sum]
  refine sum_congr rfl fun x' _ => ?_
  rw [sum_sliceSide_eq_sum_restrictSide hI B, mul_sum]
  refine sum_congr rfl fun y' _ => ?_
  have hIxy : I ⊆ interSet (insertOnes I hI x') (insertOnes I hI y') := by
    rw [interSet_eq_inter]
    exact subset_inter (subset_supportSet_insertOnes I hI x')
      (subset_supportSet_insertOnes I hI y')
  have h := muWeight_succ_sub hkn hkm hI hIxy
  rwa [removeCoords_insertOnes, removeCoords_insertOnes] at h

end CslibFrontier.Computability.Communication
