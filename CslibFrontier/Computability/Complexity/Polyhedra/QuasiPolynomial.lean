module

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.DPi
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.ZMod.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement

/-!
# Piecewise Quasi-Polynomials, Faulhaber Summation, and Polynomial-Time Evaluation

This module defines quasi-polynomials, rational polyhedral chambers, and piecewise
quasi-polynomials on `ℤ^d`, establishes their algebraic closure laws and Faulhaber summation over
arbitrary integer intervals, and proves that any fixed integer-valued piecewise quasi-polynomial
is computable in polynomial time on a multi-tape Turing machine from binary-encoded inputs
(`Turing.MultiTapeTM.ComputableInPolyTime`) with positivity decidable in `Cslib.Complexity.P`.
-/

public section

namespace CslibFrontier.Complexity.Polyhedra

open scoped BigOperators

/-! ### 1. Quasi-polynomials -/

/-- A quasi-polynomial on `ℤ^d`: a finite-index sublattice `sublattice ≤ (Fin d → ℤ)` together
with a rational multivariate polynomial `poly z ∈ ℚ[X₁, …, X_d]` for each coset
`z ∈ (Fin d → ℤ) ⧸ sublattice`. -/
structure QuasiPolynomial (d : ℕ) where
  /-- Finite-index sublattice `L ⊆ ℤ^d` of periodicity. -/
  sublattice : AddSubgroup (Fin d → ℤ)
  /-- The quotient `ℤ^d / L` is finite. -/
  finiteQuot : Finite ((Fin d → ℤ) ⧸ sublattice)
  /-- Rational polynomial assigned to each coset `z ∈ ℤ^d / L`. -/
  poly : ((Fin d → ℤ) ⧸ sublattice) → MvPolynomial (Fin d) ℚ

namespace QuasiPolynomial

/-- Evaluate a quasi-polynomial at an integer vector `y : Fin d → ℤ`. -/
@[expose] noncomputable def eval {d : ℕ} (q : QuasiPolynomial d) (y : Fin d → ℤ) : ℚ :=
  MvPolynomial.eval (fun i ↦ (y i : ℚ)) (q.poly (QuotientAddGroup.mk y))

/-- The zero quasi-polynomial. -/
noncomputable def zero (d : ℕ) : QuasiPolynomial d where
  sublattice := ⊤
  finiteQuot := by
    have : Subsingleton ((Fin d → ℤ) ⧸ (⊤ : AddSubgroup (Fin d → ℤ))) :=
      ⟨fun a b ↦ QuotientAddGroup.induction_on a fun x ↦ QuotientAddGroup.induction_on b fun y ↦
        (QuotientAddGroup.eq).2 trivial⟩
    infer_instance
  poly := fun _ ↦ 0

@[simp]
theorem eval_zero {d : ℕ} (y : Fin d → ℤ) : (zero d).eval y = 0 := by
  simp [eval, zero]

/-- A constant rational quasi-polynomial. -/
noncomputable def const (d : ℕ) (c : ℚ) : QuasiPolynomial d where
  sublattice := ⊤
  finiteQuot := (zero d).finiteQuot
  poly := fun _ ↦ MvPolynomial.C c

@[simp]
theorem eval_const {d : ℕ} (c : ℚ) (y : Fin d → ℤ) : (const d c).eval y = c := by
  simp [eval, const]

/-- A pure multivariate polynomial viewed as a quasi-polynomial with trivial period. -/
noncomputable def ofMvPolynomial {d : ℕ} (p : MvPolynomial (Fin d) ℚ) : QuasiPolynomial d where
  sublattice := ⊤
  finiteQuot := (zero d).finiteQuot
  poly := fun _ ↦ p

@[simp]
theorem eval_ofMvPolynomial {d : ℕ} (p : MvPolynomial (Fin d) ℚ) (y : Fin d → ℤ) :
    (ofMvPolynomial p).eval y = MvPolynomial.eval (fun i ↦ (y i : ℚ)) p := by
  simp [eval, ofMvPolynomial]

/-- The sublattice `M • ℤ^d` of integer vectors divisible entrywise by `M`. -/
def mulSublattice (d : ℕ) (M : ℕ) : AddSubgroup (Fin d → ℤ) where
  carrier := {y | ∀ i, (M : ℤ) ∣ y i}
  add_mem' ha hb i := dvd_add (ha i) (hb i)
  zero_mem' _ := dvd_zero _
  neg_mem' ha i := dvd_neg.2 (ha i)

theorem mem_mulSublattice_iff {d M : ℕ} {y : Fin d → ℤ} :
    y ∈ mulSublattice d M ↔ ∀ i, (M : ℤ) ∣ y i := Iff.rfl

theorem finite_quotient_mulSublattice (d : ℕ) {M : ℕ} (hM : 0 < M) :
    Finite ((Fin d → ℤ) ⧸ mulSublattice d M) := by
  let φ : (Fin d → ℤ) →+ (Fin d → ZMod M) :=
    { toFun := fun y i ↦ (y i : ZMod M)
      map_zero' := by ext i; simp
      map_add' := fun x y ↦ by ext i; simp }
  have hker : φ.ker = mulSublattice d M := by
    ext y
    simp only [AddMonoidHom.mem_ker, funext_iff, Pi.zero_apply, mem_mulSublattice_iff]
    constructor
    · intro h i
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (y i) M).1 (h i)
    · intro h i
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (y i) M).2 (h i)
  have : NeZero M := ⟨hM.ne'⟩
  have hinj : Function.Injective (QuotientAddGroup.lift (mulSublattice d M) φ (by
      intro x hx; rw [← hker] at hx; exact hx)) := by
    rw [← AddMonoidHom.ker_eq_bot_iff, QuotientAddGroup.ker_lift]
    simp [hker]
  exact Finite.of_injective _ hinj

/-- Construct a quasi-polynomial from an explicit positive modulus `M` and polynomials indexed by
`Fin d → ZMod M`. -/
noncomputable def ofPeriod {d M : ℕ} (hM : 0 < M)
    (P : (Fin d → ZMod M) → MvPolynomial (Fin d) ℚ) : QuasiPolynomial d where
  sublattice := mulSublattice d M
  finiteQuot := finite_quotient_mulSublattice d hM
  poly := Quotient.lift (fun y ↦ P (fun i ↦ (y i : ZMod M))) (by
    intro a b hab
    have hmem : -a + b ∈ mulSublattice d M := QuotientAddGroup.leftRel_apply.1 hab
    have heq : (fun i ↦ (a i : ZMod M)) = (fun i ↦ (b i : ZMod M)) := by
      ext i
      have hdiv : (M : ℤ) ∣ b i - a i := by
        simpa [sub_eq_neg_add] using hmem i
      have h0 : ((b i - a i : ℤ) : ZMod M) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (b i - a i) M).2 hdiv
      push_cast at h0
      exact (sub_eq_zero.1 h0).symm
    rw [heq])

@[simp]
theorem eval_ofPeriod {d M : ℕ} (hM : 0 < M)
    (P : (Fin d → ZMod M) → MvPolynomial (Fin d) ℚ) (y : Fin d → ℤ) :
    (ofPeriod hM P).eval y =
      MvPolynomial.eval (fun i ↦ (y i : ℚ)) (P (fun i ↦ (y i : ZMod M))) := by
  simp [eval, ofPeriod]

/-- Every quasi-polynomial has a positive integer period `M` such that `M • ℤ^d ≤ q.sublattice`. -/
theorem exists_pos_period {d : ℕ} (q : QuasiPolynomial d) :
    ∃ M : ℕ, 0 < M ∧ mulSublattice d M ≤ q.sublattice := by
  have := q.finiteQuot
  let M : ℕ := Nat.card ((Fin d → ℤ) ⧸ q.sublattice)
  have hM : 0 < M := Nat.card_pos
  refine ⟨M, hM, fun y hy ↦ ?_⟩
  have hcoord : ∀ i, ∃ k : ℤ, y i = (M : ℤ) * k := fun i ↦ hy i
  choose k hk using hcoord
  have hy_eq : y = (M : ℤ) • k := by
    ext i; simp [hk i]
  rw [hy_eq]
  have hq0 : (M : ℤ) • (QuotientAddGroup.mk k : (Fin d → ℤ) ⧸ q.sublattice) = 0 := by
    rw [natCast_zsmul]
    let x : Multiplicative ((Fin d → ℤ) ⧸ q.sublattice) :=
      Multiplicative.ofAdd (QuotientAddGroup.mk k)
    have hcard : Nat.card (Multiplicative ((Fin d → ℤ) ⧸ q.sublattice)) = M :=
      Nat.card_congr Multiplicative.ofAdd.symm
    have hdvd : orderOf x ∣ M := hcard ▸ orderOf_dvd_natCard x
    obtain ⟨r, hr⟩ := hdvd
    have hpow : x ^ M = 1 := by
      rw [hr, pow_mul, pow_orderOf_eq_one, one_pow]
    exact Multiplicative.ofAdd.injective (by simpa [x, ofAdd_nsmul] using hpow)
  rw [← QuotientAddGroup.mk_zsmul] at hq0
  exact (QuotientAddGroup.eq_zero_iff _).1 hq0

/-- Refine the sublattice of a quasi-polynomial to a smaller finite-index sublattice `L' ≤ L`. -/
noncomputable def restrictSublattice {d : ℕ} (q : QuasiPolynomial d)
    (L' : AddSubgroup (Fin d → ℤ)) (hL' : L' ≤ q.sublattice)
    (hfin : Finite ((Fin d → ℤ) ⧸ L')) : QuasiPolynomial d where
  sublattice := L'
  finiteQuot := hfin
  poly := fun z ↦ q.poly (QuotientAddGroup.map L' q.sublattice (AddMonoidHom.id _)
    (by simpa using hL') z)

@[simp]
theorem eval_restrictSublattice {d : ℕ} (q : QuasiPolynomial d)
    (L' : AddSubgroup (Fin d → ℤ)) (hL' : L' ≤ q.sublattice)
    (hfin : Finite ((Fin d → ℤ) ⧸ L')) (y : Fin d → ℤ) :
    (q.restrictSublattice L' hL' hfin).eval y = q.eval y := by
  simp [eval, restrictSublattice]

private theorem finite_quotient_inf {G : Type*} [AddCommGroup G] (L₁ L₂ : AddSubgroup G)
    [Finite (G ⧸ L₁)] [Finite (G ⧸ L₂)] : Finite (G ⧸ (L₁ ⊓ L₂)) := by
  let φ : G →+ (G ⧸ L₁) × (G ⧸ L₂) :=
    (QuotientAddGroup.mk' L₁).prod (QuotientAddGroup.mk' L₂)
  have hker : φ.ker = L₁ ⊓ L₂ := by
    ext x
    simp [φ, Prod.ext_iff, QuotientAddGroup.eq_zero_iff]
  have hinj : Function.Injective (QuotientAddGroup.lift (L₁ ⊓ L₂) φ (by
      intro x hx; rw [← hker] at hx; exact hx)) := by
    rw [← AddMonoidHom.ker_eq_bot_iff, QuotientAddGroup.ker_lift]
    simp [hker]
  exact Finite.of_injective _ hinj

/-- Pointwise sum of two quasi-polynomials. -/
noncomputable def add {d : ℕ} (q₁ q₂ : QuasiPolynomial d) : QuasiPolynomial d :=
  let L := q₁.sublattice ⊓ q₂.sublattice
  have := q₁.finiteQuot
  have := q₂.finiteQuot
  have hfin : Finite ((Fin d → ℤ) ⧸ L) := finite_quotient_inf q₁.sublattice q₂.sublattice
  { sublattice := L
    finiteQuot := hfin
    poly := fun z ↦
      (q₁.restrictSublattice L inf_le_left hfin).poly z +
        (q₂.restrictSublattice L inf_le_right hfin).poly z }

@[simp]
theorem eval_add {d : ℕ} (q₁ q₂ : QuasiPolynomial d) (y : Fin d → ℤ) :
    (q₁.add q₂).eval y = q₁.eval y + q₂.eval y := by
  simp [add, eval, restrictSublattice]

/-- Pointwise scalar multiplication of a quasi-polynomial by a rational scalar. -/
noncomputable def smul {d : ℕ} (c : ℚ) (q : QuasiPolynomial d) : QuasiPolynomial d where
  sublattice := q.sublattice
  finiteQuot := q.finiteQuot
  poly := fun z ↦ c • q.poly z

@[simp]
theorem eval_smul {d : ℕ} (c : ℚ) (q : QuasiPolynomial d) (y : Fin d → ℤ) :
    (q.smul c).eval y = c * q.eval y := by
  simp [smul, eval]

/-- Expansion of an integer linear map `B : (Fin d → ℤ) →+ (Fin k → ℤ)` in coordinates. -/
theorem addMonoidHom_fin_apply {d k : ℕ} (B : (Fin d → ℤ) →+ (Fin k → ℤ))
    (y : Fin d → ℤ) (j : Fin k) :
    B y j = ∑ i : Fin d, B (Pi.single i 1) j * y i := by
  have hy : y = ∑ i : Fin d, y i • Pi.single i (1 : ℤ) := by
    ext m; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hy]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_zsmul, Pi.smul_apply, zsmul_eq_mul, Int.cast_id, mul_comm]

/-- Pull back a quasi-polynomial along an affine map `y ↦ B y + c`. -/
noncomputable def compAffine {d k : ℕ} (q : QuasiPolynomial k)
    (B : (Fin d → ℤ) →+ (Fin k → ℤ)) (c : Fin k → ℤ) : QuasiPolynomial d :=
  let L : AddSubgroup (Fin d → ℤ) := q.sublattice.comap B
  have := q.finiteQuot
  have hfin : Finite ((Fin d → ℤ) ⧸ L) := by
    let ψ : (Fin d → ℤ) →+ ((Fin k → ℤ) ⧸ q.sublattice) :=
      (QuotientAddGroup.mk' q.sublattice).comp B
    have hker : ψ.ker = L := by
      ext x; simp [ψ, L, QuotientAddGroup.eq_zero_iff]
    have hinj : Function.Injective (QuotientAddGroup.lift L ψ (by
        intro x hx; rw [← hker] at hx; exact hx)) := by
      rw [← AddMonoidHom.ker_eq_bot_iff, QuotientAddGroup.ker_lift]
      simp [hker]
    exact Finite.of_injective _ hinj
  let affPoly : Fin k → MvPolynomial (Fin d) ℚ := fun j ↦
    (∑ i : Fin d, MvPolynomial.C ((B (Pi.single i 1) j : ℤ) : ℚ) * MvPolynomial.X i) +
      MvPolynomial.C (c j : ℚ)
  { sublattice := L
    finiteQuot := hfin
    poly := Quotient.lift (fun y ↦
        MvPolynomial.aeval affPoly (q.poly (QuotientAddGroup.mk (B y + c)))) (by
      intro a b hab
      have hmem : -a + b ∈ L := QuotientAddGroup.leftRel_apply.1 hab
      have hBc : QuotientAddGroup.mk (s := q.sublattice) (B a + c) =
          QuotientAddGroup.mk (s := q.sublattice) (B b + c) := by
        rw [QuotientAddGroup.eq]
        have : -(B a + c) + (B b + c) = B (-a + b) := by
          rw [map_add, map_neg]; abel
        rw [this]
        exact hmem
      rw [hBc]) }

@[simp]
theorem eval_compAffine {d k : ℕ} (q : QuasiPolynomial k)
    (B : (Fin d → ℤ) →+ (Fin k → ℤ)) (c : Fin k → ℤ) (y : Fin d → ℤ) :
    (q.compAffine B c).eval y = q.eval (B y + c) := by
  simp only [compAffine, eval]
  have hcomp : MvPolynomial.eval (fun i ↦ (y i : ℚ))
      (MvPolynomial.aeval (fun j : Fin k ↦
        (∑ i : Fin d, MvPolynomial.C ((B (Pi.single i 1) j : ℤ) : ℚ) * MvPolynomial.X i) +
          MvPolynomial.C (c j : ℚ)) (q.poly (QuotientAddGroup.mk (B y + c)))) =
      MvPolynomial.eval (fun j ↦ ((B y + c) j : ℚ)) (q.poly (QuotientAddGroup.mk (B y + c))) := by
    let p := q.poly (QuotientAddGroup.mk (B y + c))
    change (MvPolynomial.aeval (fun i ↦ (y i : ℚ))).comp
      (MvPolynomial.aeval (fun j : Fin k ↦
        (∑ i : Fin d, MvPolynomial.C ((B (Pi.single i 1) j : ℤ) : ℚ) * MvPolynomial.X i) +
          MvPolynomial.C (c j : ℚ))) p =
      MvPolynomial.aeval (fun j ↦ ((B y + c) j : ℚ)) p
    congr 1
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, map_add, map_sum, map_mul,
      MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply, Pi.add_apply, Int.cast_add]
    congr 1
    rw [addMonoidHom_fin_apply B y j, Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ ↦ by push_cast; rfl
  exact hcomp

/-- Multiply a quasi-polynomial by a periodic `{0, 1}` indicator
`pred : (Fin d → ZMod M) → Prop`. -/
noncomputable def mulPeriodicIndicator {d M : ℕ} (hM : 0 < M)
    (pred : (Fin d → ZMod M) → Prop) [DecidablePred pred]
    (q : QuasiPolynomial d) : QuasiPolynomial d :=
  let L := q.sublattice ⊓ mulSublattice d M
  have := q.finiteQuot
  have := finite_quotient_mulSublattice d hM
  have hfin : Finite ((Fin d → ℤ) ⧸ L) :=
    finite_quotient_inf q.sublattice (mulSublattice d M)
  { sublattice := L
    finiteQuot := hfin
    poly := Quotient.lift (fun y ↦
        if pred (fun i ↦ (y i : ZMod M)) then q.poly (QuotientAddGroup.mk y) else 0) (by
      intro a b hab
      have hmem : -a + b ∈ L := QuotientAddGroup.leftRel_apply.1 hab
      have h1 : QuotientAddGroup.mk (s := q.sublattice) a =
          QuotientAddGroup.mk (s := q.sublattice) b :=
        (QuotientAddGroup.eq).2 hmem.1
      have h2 : (fun i ↦ (a i : ZMod M)) = (fun i ↦ (b i : ZMod M)) := by
        ext i
        have hdiv : (M : ℤ) ∣ b i - a i := by
          simpa [sub_eq_neg_add] using hmem.2 i
        have h0 : ((b i - a i : ℤ) : ZMod M) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (b i - a i) M).2 hdiv
        push_cast at h0
        exact (sub_eq_zero.1 h0).symm
      rw [h1, h2]) }

@[simp]
theorem eval_mulPeriodicIndicator {d M : ℕ} (hM : 0 < M)
    (pred : (Fin d → ZMod M) → Prop) [DecidablePred pred]
    (q : QuasiPolynomial d) (y : Fin d → ℤ) :
    (q.mulPeriodicIndicator hM pred).eval y =
      if pred (fun i ↦ (y i : ZMod M)) then q.eval y else 0 := by
  unfold mulPeriodicIndicator eval
  dsimp only
  split_ifs with h <;> simp [h]

end QuasiPolynomial

/-! ### 2. Polyhedral Chambers and Piecewise Quasi-Polynomials -/

/-- A rational polyhedral chamber in `ℤ^d`, defined as the intersection of finitely many closed
rational half-spaces `{y ∈ ℤ^d : ∑ i, a i * y i ≤ c}`. -/
structure PolyhedralChamber (d : ℕ) where
  /-- List of linear inequality constraints `(a, c)` representing `∑ i, a i * y i ≤ c`. -/
  ineqs : List ((Fin d → ℤ) × ℤ)

namespace PolyhedralChamber

/-- The set of integer lattice points belonging to a polyhedral chamber. -/
def carrier {d : ℕ} (C : PolyhedralChamber d) : Set (Fin d → ℤ) :=
  {y | ∀ p ∈ C.ineqs, (∑ i : Fin d, p.1 i * y i) ≤ p.2}

/-- The underlying real rational convex polyhedron `{x ∈ ℝ^d : ∀ (a, c) ∈ ineqs, a · x ≤ c}`. -/
def carrierReal {d : ℕ} (C : PolyhedralChamber d) : Set (Fin d → ℝ) :=
  {x | ∀ p ∈ C.ineqs, (∑ i : Fin d, (p.1 i : ℝ) * x i) ≤ (p.2 : ℝ)}

theorem mem_carrier_iff {d : ℕ} {C : PolyhedralChamber d} {y : Fin d → ℤ} :
    y ∈ C.carrier ↔ ∀ p ∈ C.ineqs, (∑ i : Fin d, p.1 i * y i) ≤ p.2 := Iff.rfl

/-- Every polyhedral chamber's real locus is a convex polyhedron. -/
theorem convex_carrierReal {d : ℕ} (C : PolyhedralChamber d) : Convex ℝ C.carrierReal := by
  intro x hx y hy a b ha hb hab p hp
  have h1 := hx p hp
  have h2 := hy p hp
  have hlin : (∑ i : Fin d, (p.1 i : ℝ) * (a • x + b • y) i) =
      a * (∑ i : Fin d, (p.1 i : ℝ) * x i) + b * (∑ i : Fin d, (p.1 i : ℝ) * y i) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hlin]
  calc
    a * (∑ i, (p.1 i : ℝ) * x i) + b * (∑ i, (p.1 i : ℝ) * y i)
        ≤ a * (p.2 : ℝ) + b * (p.2 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
    _ = (p.2 : ℝ) := by rw [← add_mul, hab, one_mul]

/-- The whole space `ℤ^d` as a chamber with no constraints. -/
def univ (d : ℕ) : PolyhedralChamber d := ⟨[]⟩

@[simp]
theorem carrier_univ (d : ℕ) : (univ d).carrier = Set.univ := by
  ext y; simp [univ, carrier]

/-- Intersection of two polyhedral chambers. -/
def inter {d : ℕ} (C₁ C₂ : PolyhedralChamber d) : PolyhedralChamber d :=
  ⟨C₁.ineqs ++ C₂.ineqs⟩

@[simp]
theorem carrier_inter {d : ℕ} (C₁ C₂ : PolyhedralChamber d) :
    (C₁.inter C₂).carrier = C₁.carrier ∩ C₂.carrier := by
  ext y
  simp only [inter, carrier, List.mem_append, Set.mem_ofPred_eq, Set.mem_inter_iff]
  exact ⟨fun h ↦ ⟨fun p hp ↦ h p (Or.inl hp), fun p hp ↦ h p (Or.inr hp)⟩,
    fun ⟨h₁, h₂⟩ p hp ↦ hp.elim (h₁ p) (h₂ p)⟩

/-- Add a single linear inequality `a · y ≤ c` to a chamber. -/
def addIneq {d : ℕ} (C : PolyhedralChamber d) (a : Fin d → ℤ) (c : ℤ) : PolyhedralChamber d :=
  ⟨(a, c) :: C.ineqs⟩

theorem mem_addIneq_iff {d : ℕ} {C : PolyhedralChamber d} {a : Fin d → ℤ} {c : ℤ}
    {y : Fin d → ℤ} :
    y ∈ (C.addIneq a c).carrier ↔ (∑ i, a i * y i) ≤ c ∧ y ∈ C.carrier := by
  simp [addIneq, carrier]

/-- Pull back a chamber along an affine map `y ↦ B y + c`. -/
def preimageAffine {d k : ℕ} (C : PolyhedralChamber k)
    (B : (Fin d → ℤ) →+ (Fin k → ℤ)) (c : Fin k → ℤ) : PolyhedralChamber d :=
  ⟨C.ineqs.map fun p ↦
    (fun i ↦ ∑ j : Fin k, p.1 j * B (Pi.single i 1) j,
      p.2 - ∑ j : Fin k, p.1 j * c j)⟩

theorem mem_preimageAffine_iff {d k : ℕ} {C : PolyhedralChamber k}
    {B : (Fin d → ℤ) →+ (Fin k → ℤ)} {c : Fin k → ℤ} {y : Fin d → ℤ} :
    y ∈ (C.preimageAffine B c).carrier ↔ B y + c ∈ C.carrier := by
  simp only [preimageAffine, carrier, List.mem_map, Set.mem_ofPred_eq, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun p _ ↦ ?_
  have hsum : (∑ i : Fin d, (∑ j : Fin k, p.1 j * B (Pi.single i 1) j) * y i) +
      (∑ j : Fin k, p.1 j * c j) = ∑ j : Fin k, p.1 j * (B y + c) j := by
    calc
      (∑ i : Fin d, (∑ j : Fin k, p.1 j * B (Pi.single i 1) j) * y i) +
          (∑ j : Fin k, p.1 j * c j)
          = (∑ j : Fin k, p.1 j * (∑ i : Fin d, B (Pi.single i 1) j * y i)) +
              (∑ j : Fin k, p.1 j * c j) := by
            congr 1
            simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
            exact Finset.sum_comm
      _ = ∑ j : Fin k, p.1 j * (B y + c) j := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [← QuasiPolynomial.addMonoidHom_fin_apply B y j, Pi.add_apply, mul_add]
  omega

/-- Decidable check whether `y : Fin d → ℤ` belongs to a polyhedral chamber. -/
def decideMem {d : ℕ} (C : PolyhedralChamber d) (y : Fin d → ℤ) : Bool :=
  C.ineqs.all fun p ↦ decide ((∑ i : Fin d, p.1 i * y i) ≤ p.2)

theorem decideMem_eq_true_iff {d : ℕ} (C : PolyhedralChamber d) (y : Fin d → ℤ) :
    C.decideMem y = true ↔ y ∈ C.carrier := by
  simp [decideMem, carrier, List.all_eq_true]

/-- Decidability of membership in a rational polyhedral chamber. -/
instance instDecidableMemCarrier {d : ℕ} (C : PolyhedralChamber d) (y : Fin d → ℤ) :
    Decidable (y ∈ C.carrier) :=
  decidable_of_iff (C.decideMem y = true) (C.decideMem_eq_true_iff y)

end PolyhedralChamber

/-- A piecewise quasi-polynomial function on `ℤ^d`: a finite partition of `ℤ^d` into pairwise
disjoint rational polyhedral chambers together with a quasi-polynomial on each chamber. -/
structure PiecewiseQuasiPolynomial (d : ℕ) where
  /-- Finite list of `(chamber, quasiPolynomial)` pieces. -/
  pieces : List (PolyhedralChamber d × QuasiPolynomial d)
  /-- The chambers cover `ℤ^d`. -/
  cover : ∀ y : Fin d → ℤ, ∃ piece ∈ pieces, y ∈ piece.1.carrier
  /-- The chambers are pairwise disjoint on `ℤ^d`. -/
  disjoint : pieces.Pairwise fun a b ↦ Disjoint a.1.carrier b.1.carrier

namespace PiecewiseQuasiPolynomial

/-- Evaluate a piecewise quasi-polynomial at `y : Fin d → ℤ`. -/
noncomputable def eval {d : ℕ} (f : PiecewiseQuasiPolynomial d) (y : Fin d → ℤ) : ℚ :=
  let h := f.cover y
  h.choose.2.eval y

private theorem eq_of_mem_pieces {d : ℕ} (f : PiecewiseQuasiPolynomial d)
    {p₁ p₂ : PolyhedralChamber d × QuasiPolynomial d}
    (hp₁ : p₁ ∈ f.pieces) (hp₂ : p₂ ∈ f.pieces)
    {y : Fin d → ℤ} (hy₁ : y ∈ p₁.1.carrier) (hy₂ : y ∈ p₂.1.carrier) :
    p₁ = p₂ := by
  by_contra hne
  have hdisj : Disjoint p₁.1.carrier p₂.1.carrier := by
    have hpw := List.pairwise_iff_getElem.1 f.disjoint
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp₁
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp₂
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact hpw i j hi hj hij
    · exact (hne rfl).elim
    · exact (hpw j i hj hi hij).symm
  exact Set.disjoint_left.1 hdisj hy₁ hy₂

theorem eval_eq_of_mem {d : ℕ} (f : PiecewiseQuasiPolynomial d)
    {p : PolyhedralChamber d × QuasiPolynomial d} (hp : p ∈ f.pieces)
    {y : Fin d → ℤ} (hy : y ∈ p.1.carrier) :
    f.eval y = p.2.eval y := by
  dsimp only [eval]
  have hspec := (f.cover y).choose_spec
  have heq := f.eq_of_mem_pieces hspec.1 hp hspec.2 hy
  rw [heq]

/-- A single quasi-polynomial viewed as a piecewise quasi-polynomial on `ℤ^d`. -/
noncomputable def ofQuasiPolynomial {d : ℕ} (q : QuasiPolynomial d) :
    PiecewiseQuasiPolynomial d where
  pieces := [(PolyhedralChamber.univ d, q)]
  cover := fun y ↦ ⟨(PolyhedralChamber.univ d, q), by simp, by simp⟩
  disjoint := by simp

@[simp]
theorem eval_ofQuasiPolynomial {d : ℕ} (q : QuasiPolynomial d) (y : Fin d → ℤ) :
    (ofQuasiPolynomial q).eval y = q.eval y :=
  eval_eq_of_mem (ofQuasiPolynomial q) (p := (PolyhedralChamber.univ d, q))
    (by simp [ofQuasiPolynomial]) (by simp)

/-- The zero piecewise quasi-polynomial. -/
noncomputable def zero (d : ℕ) : PiecewiseQuasiPolynomial d :=
  ofQuasiPolynomial (QuasiPolynomial.zero d)

@[simp]
theorem eval_zero {d : ℕ} (y : Fin d → ℤ) : (zero d).eval y = 0 := by
  simp [zero]

/-- Scalar multiplication of a piecewise quasi-polynomial by a rational scalar. -/
noncomputable def smul {d : ℕ} (c : ℚ) (f : PiecewiseQuasiPolynomial d) :
    PiecewiseQuasiPolynomial d where
  pieces := f.pieces.map fun p ↦ (p.1, p.2.smul c)
  cover := fun y ↦ by
    obtain ⟨p, hp, hy⟩ := f.cover y
    exact ⟨(p.1, p.2.smul c), List.mem_map_of_mem hp, hy⟩
  disjoint := List.pairwise_map.2 (f.disjoint.imp fun h ↦ h)

@[simp]
theorem eval_smul {d : ℕ} (c : ℚ) (f : PiecewiseQuasiPolynomial d) (y : Fin d → ℤ) :
    (f.smul c).eval y = c * f.eval y := by
  obtain ⟨p, hp, hy⟩ := f.cover y
  rw [eval_eq_of_mem (f.smul c) (p := (p.1, p.2.smul c)) (List.mem_map_of_mem hp) hy,
    eval_eq_of_mem f hp hy, QuasiPolynomial.eval_smul]

/-- Pointwise sum of two piecewise quasi-polynomials on the common refinement of their chambers. -/
noncomputable def add {d : ℕ} (f₁ f₂ : PiecewiseQuasiPolynomial d) :
    PiecewiseQuasiPolynomial d where
  pieces := f₁.pieces.flatMap fun p₁ ↦ f₂.pieces.map fun p₂ ↦ (p₁.1.inter p₂.1, p₁.2.add p₂.2)
  cover := fun y ↦ by
    obtain ⟨p₁, hp₁, hy₁⟩ := f₁.cover y
    obtain ⟨p₂, hp₂, hy₂⟩ := f₂.cover y
    exact ⟨(p₁.1.inter p₂.1, p₁.2.add p₂.2),
      List.mem_flatMap.2 ⟨p₁, hp₁, List.mem_map_of_mem hp₂⟩, by simp [hy₁, hy₂]⟩
  disjoint := by
    refine List.pairwise_flatMap.2 ⟨?_, ?_⟩
    · intro p₁ _
      refine List.pairwise_map.2 (f₂.disjoint.imp fun h ↦ ?_)
      simp only [PolyhedralChamber.carrier_inter]
      exact h.mono Set.inter_subset_right Set.inter_subset_right
    · refine f₁.disjoint.imp fun {p₁ p₁'} hdisj a ha b hb ↦ ?_
      obtain ⟨p₂, _, rfl⟩ := List.mem_map.1 ha
      obtain ⟨p₂', _, rfl⟩ := List.mem_map.1 hb
      simp only [PolyhedralChamber.carrier_inter]
      exact hdisj.mono Set.inter_subset_left Set.inter_subset_left

@[simp]
theorem eval_add {d : ℕ} (f₁ f₂ : PiecewiseQuasiPolynomial d) (y : Fin d → ℤ) :
    (f₁.add f₂).eval y = f₁.eval y + f₂.eval y := by
  obtain ⟨p₁, hp₁, hy₁⟩ := f₁.cover y
  obtain ⟨p₂, hp₂, hy₂⟩ := f₂.cover y
  have hmem : (p₁.1.inter p₂.1, p₁.2.add p₂.2) ∈ (f₁.add f₂).pieces :=
    List.mem_flatMap.2 ⟨p₁, hp₁, List.mem_map_of_mem hp₂⟩
  rw [eval_eq_of_mem (f₁.add f₂) hmem (by simp [hy₁, hy₂]), eval_eq_of_mem f₁ hp₁ hy₁,
    eval_eq_of_mem f₂ hp₂ hy₂, QuasiPolynomial.eval_add]

/-- Pull back a piecewise quasi-polynomial along an affine map `y ↦ B y + c`. -/
noncomputable def compAffine {d k : ℕ} (f : PiecewiseQuasiPolynomial k)
    (B : (Fin d → ℤ) →+ (Fin k → ℤ)) (c : Fin k → ℤ) : PiecewiseQuasiPolynomial d where
  pieces := f.pieces.map fun p ↦ (p.1.preimageAffine B c, p.2.compAffine B c)
  cover := fun y ↦ by
    obtain ⟨p, hp, hy⟩ := f.cover (B y + c)
    exact ⟨(p.1.preimageAffine B c, p.2.compAffine B c), List.mem_map_of_mem hp,
      PolyhedralChamber.mem_preimageAffine_iff.2 hy⟩
  disjoint := List.pairwise_map.2 (f.disjoint.imp fun {a b} h ↦ by
    rw [Set.disjoint_left]
    intro y hya hyb
    exact Set.disjoint_left.1 h (PolyhedralChamber.mem_preimageAffine_iff.1 hya)
      (PolyhedralChamber.mem_preimageAffine_iff.1 hyb))

@[simp]
theorem eval_compAffine {d k : ℕ} (f : PiecewiseQuasiPolynomial k)
    (B : (Fin d → ℤ) →+ (Fin k → ℤ)) (c : Fin k → ℤ) (y : Fin d → ℤ) :
    (f.compAffine B c).eval y = f.eval (B y + c) := by
  obtain ⟨p, hp, hy⟩ := f.cover (B y + c)
  rw [eval_eq_of_mem (f.compAffine B c) (p := (p.1.preimageAffine B c, p.2.compAffine B c))
      (List.mem_map_of_mem hp) (PolyhedralChamber.mem_preimageAffine_iff.2 hy),
    eval_eq_of_mem f hp hy, QuasiPolynomial.eval_compAffine]

/-- Multiply a piecewise quasi-polynomial by a periodic `{0, 1}` indicator. -/
noncomputable def mulPeriodicIndicator {d M : ℕ} (hM : 0 < M)
    (pred : (Fin d → ZMod M) → Prop) [DecidablePred pred]
    (f : PiecewiseQuasiPolynomial d) : PiecewiseQuasiPolynomial d where
  pieces := f.pieces.map fun p ↦ (p.1, p.2.mulPeriodicIndicator hM pred)
  cover := fun y ↦ by
    obtain ⟨p, hp, hy⟩ := f.cover y
    exact ⟨(p.1, p.2.mulPeriodicIndicator hM pred), List.mem_map_of_mem hp, hy⟩
  disjoint := List.pairwise_map.2 (f.disjoint.imp fun h ↦ h)

@[simp]
theorem eval_mulPeriodicIndicator {d M : ℕ} (hM : 0 < M)
    (pred : (Fin d → ZMod M) → Prop) [DecidablePred pred]
    (f : PiecewiseQuasiPolynomial d) (y : Fin d → ℤ) :
    (f.mulPeriodicIndicator hM pred).eval y =
      if pred (fun i ↦ (y i : ZMod M)) then f.eval y else 0 := by
  obtain ⟨p, hp, hy⟩ := f.cover y
  rw [eval_eq_of_mem (f.mulPeriodicIndicator hM pred)
      (p := (p.1, p.2.mulPeriodicIndicator hM pred)) (List.mem_map_of_mem hp) hy,
    eval_eq_of_mem f hp hy, QuasiPolynomial.eval_mulPeriodicIndicator]

/-- Split a chamber partition by a single linear inequality `a · y ≤ c` and its complement
`(-a) · y ≤ -c - 1`. -/
def splitPartition {d : ℕ} (chambers : List (PolyhedralChamber d))
    (a : Fin d → ℤ) (c : ℤ) : List (PolyhedralChamber d) :=
  chambers.flatMap fun C ↦ [C.addIneq a c, C.addIneq (-a) (-c - 1)]

theorem splitPartition_cover {d : ℕ} {chambers : List (PolyhedralChamber d)}
    (hcov : ∀ y, ∃ C ∈ chambers, y ∈ C.carrier) (a : Fin d → ℤ) (c : ℤ) (y : Fin d → ℤ) :
    ∃ C ∈ splitPartition chambers a c, y ∈ C.carrier := by
  obtain ⟨C, hC, hy⟩ := hcov y
  by_cases h : (∑ i, a i * y i) ≤ c
  · exact ⟨C.addIneq a c, List.mem_flatMap.2 ⟨C, hC, by simp⟩,
      PolyhedralChamber.mem_addIneq_iff.2 ⟨h, hy⟩⟩
  · refine ⟨C.addIneq (-a) (-c - 1), List.mem_flatMap.2 ⟨C, hC, by simp⟩,
      PolyhedralChamber.mem_addIneq_iff.2 ⟨?_, hy⟩⟩
    have hneg : (∑ i, (-a) i * y i) = -(∑ i, a i * y i) := by
      simp [Finset.sum_neg_distrib]
    rw [hneg]
    omega

theorem splitPartition_disjoint {d : ℕ} {chambers : List (PolyhedralChamber d)}
    (hdisj : chambers.Pairwise fun C₁ C₂ ↦ Disjoint C₁.carrier C₂.carrier)
    (a : Fin d → ℤ) (c : ℤ) :
    (splitPartition chambers a c).Pairwise fun C₁ C₂ ↦ Disjoint C₁.carrier C₂.carrier := by
  refine List.pairwise_flatMap.2 ⟨?_, ?_⟩
  · intro C _
    simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.Pairwise.nil, and_true]
    refine ⟨?_, by simp⟩
    rw [Set.disjoint_left]
    intro y h1 h2
    have h1' := (PolyhedralChamber.mem_addIneq_iff.1 h1).1
    have h2' := (PolyhedralChamber.mem_addIneq_iff.1 h2).1
    have hneg : (∑ i, (-a) i * y i) = -(∑ i, a i * y i) := by
      simp [Finset.sum_neg_distrib]
    rw [hneg] at h2'
    omega
  · refine hdisj.imp fun {C₁ C₂} h C₁' h₁' C₂' h₂' ↦ ?_
    have hs₁ : C₁'.carrier ⊆ C₁.carrier := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h₁'
      rcases h₁' with h₁ | h₁ <;> rw [h₁] <;> intro y hy <;>
        exact (PolyhedralChamber.mem_addIneq_iff.1 hy).2
    have hs₂ : C₂'.carrier ⊆ C₂.carrier := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h₂'
      rcases h₂' with h₂ | h₂ <;> rw [h₂] <;> intro y hy <;>
        exact (PolyhedralChamber.mem_addIneq_iff.1 hy).2
    exact h.mono hs₁ hs₂

/-- Split a chamber partition successively by a finite list of linear inequalities. -/
def splitPartitionList {d : ℕ} (chambers : List (PolyhedralChamber d))
    (ineqs : List ((Fin d → ℤ) × ℤ)) : List (PolyhedralChamber d) :=
  ineqs.foldl (fun acc p ↦ splitPartition acc p.1 p.2) chambers

theorem splitPartitionList_cover {d : ℕ} {chambers : List (PolyhedralChamber d)}
    (hcov : ∀ y, ∃ C ∈ chambers, y ∈ C.carrier) (ineqs : List ((Fin d → ℤ) × ℤ)) :
    ∀ y, ∃ C ∈ splitPartitionList chambers ineqs, y ∈ C.carrier := by
  induction ineqs generalizing chambers with
  | nil => exact hcov
  | cons p ps ih => exact ih (splitPartition_cover hcov p.1 p.2)

theorem splitPartitionList_disjoint {d : ℕ} {chambers : List (PolyhedralChamber d)}
    (hdisj : chambers.Pairwise fun C₁ C₂ ↦ Disjoint C₁.carrier C₂.carrier)
    (ineqs : List ((Fin d → ℤ) × ℤ)) :
    (splitPartitionList chambers ineqs).Pairwise fun C₁ C₂ ↦ Disjoint C₁.carrier C₂.carrier := by
  induction ineqs generalizing chambers with
  | nil => exact hdisj
  | cons p ps ih => exact ih (splitPartition_disjoint hdisj p.1 p.2)

/-- Every chamber in `splitPartitionList` decides every inequality in `ineqs` uniformly. -/
theorem splitPartitionList_decides {d : ℕ} (chambers : List (PolyhedralChamber d))
    (ineqs : List ((Fin d → ℤ) × ℤ)) :
    ∀ C ∈ splitPartitionList chambers ineqs, ∀ p ∈ ineqs,
      (∀ y ∈ C.carrier, (∑ i, p.1 i * y i) ≤ p.2) ∨
        (∀ y ∈ C.carrier, ¬ (∑ i, p.1 i * y i) ≤ p.2) := by
  induction ineqs generalizing chambers with
  | nil => intro _ _ _ hp; cases hp
  | cons p₀ ps ih =>
    intro C hC p hp
    change C ∈ splitPartitionList (splitPartition chambers p₀.1 p₀.2) ps at hC
    have hdec_step : ∀ D ∈ splitPartition chambers p₀.1 p₀.2,
        (∀ y ∈ D.carrier, (∑ i, p₀.1 i * y i) ≤ p₀.2) ∨
          (∀ y ∈ D.carrier, ¬ (∑ i, p₀.1 i * y i) ≤ p₀.2) := by
      intro D hD
      obtain ⟨E, _, hDE⟩ := List.mem_flatMap.1 hD
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hDE
      rcases hDE with hD_eq | hD_eq
      · rw [hD_eq]; left; intro y hy; exact (PolyhedralChamber.mem_addIneq_iff.1 hy).1
      · rw [hD_eq]; right; intro y hy
        have h2 := (PolyhedralChamber.mem_addIneq_iff.1 hy).1
        have hneg : (∑ i, (-p₀.1) i * y i) = -(∑ i, p₀.1 i * y i) := by
          simp [Finset.sum_neg_distrib]
        rw [hneg] at h2
        omega
    have hsub : ∀ {L : List (PolyhedralChamber d)} {qs : List ((Fin d → ℤ) × ℤ)}
        {D : PolyhedralChamber d}, D ∈ splitPartitionList L qs →
          ∃ E ∈ L, D.carrier ⊆ E.carrier := by
      intro L qs
      induction qs generalizing L with
      | nil => intro D hD; exact ⟨D, hD, Set.Subset.rfl⟩
      | cons q qs' ih' =>
        intro D hD
        obtain ⟨E, hE, hDE⟩ := ih' hD
        obtain ⟨F, hF, hEF⟩ := List.mem_flatMap.1 hE
        refine ⟨F, hF, hDE.trans ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hEF
        rcases hEF with hE_eq | hE_eq <;> rw [hE_eq] <;> intro y hy <;>
          exact (PolyhedralChamber.mem_addIneq_iff.1 hy).2
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp'
    · obtain ⟨D, hD, hCD⟩ := hsub hC
      rcases hdec_step D hD with h | h
      · left; exact fun y hy ↦ h y (hCD hy)
      · right; exact fun y hy ↦ h y (hCD hy)
    · exact ih (splitPartition chambers p₀.1 p₀.2) C hC p hp'

/-- Predicate stating that a function `g : (Fin d → ℤ) → ℚ` is piecewise quasi-polynomial. -/
@[expose] def IsPiecewiseQuasiPolynomial {d : ℕ} (g : (Fin d → ℤ) → ℚ) : Prop :=
  ∃ f : PiecewiseQuasiPolynomial d, ∀ y, f.eval y = g y

theorem isPiecewiseQuasiPolynomial_zero (d : ℕ) :
    IsPiecewiseQuasiPolynomial (fun _ : Fin d → ℤ ↦ (0 : ℚ)) :=
  ⟨zero d, fun _ ↦ eval_zero _⟩

theorem isPiecewiseQuasiPolynomial_add {d : ℕ} {g₁ g₂ : (Fin d → ℤ) → ℚ}
    (h₁ : IsPiecewiseQuasiPolynomial g₁) (h₂ : IsPiecewiseQuasiPolynomial g₂) :
    IsPiecewiseQuasiPolynomial (fun y ↦ g₁ y + g₂ y) := by
  obtain ⟨f₁, hf₁⟩ := h₁
  obtain ⟨f₂, hf₂⟩ := h₂
  exact ⟨f₁.add f₂, fun y ↦ by simp [hf₁, hf₂]⟩

theorem isPiecewiseQuasiPolynomial_smul {d : ℕ} (c : ℚ) {g : (Fin d → ℤ) → ℚ}
    (h : IsPiecewiseQuasiPolynomial g) :
    IsPiecewiseQuasiPolynomial (fun y ↦ c * g y) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f.smul c, fun y ↦ by simp [hf]⟩

theorem isPiecewiseQuasiPolynomial_sum {d : ℕ} {ι : Type*} (s : Finset ι)
    (g : ι → (Fin d → ℤ) → ℚ) (hg : ∀ i ∈ s, IsPiecewiseQuasiPolynomial (g i)) :
    IsPiecewiseQuasiPolynomial (fun y ↦ ∑ i ∈ s, g i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPiecewiseQuasiPolynomial_zero d
  | insert a s ha ih =>
    have h1 := hg a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi ↦ hg i (Finset.mem_insert_of_mem hi)
    simpa [Finset.sum_insert ha] using isPiecewiseQuasiPolynomial_add h1 h2

theorem isPiecewiseQuasiPolynomial_compAffine {d k : ℕ} {g : (Fin k → ℤ) → ℚ}
    (h : IsPiecewiseQuasiPolynomial g) (B : (Fin d → ℤ) →+ (Fin k → ℤ)) (c : Fin k → ℤ) :
    IsPiecewiseQuasiPolynomial (fun y ↦ g (B y + c)) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f.compAffine B c, fun y ↦ by simp [hf]⟩

theorem isPiecewiseQuasiPolynomial_mulPeriodicIndicator {d M : ℕ} (hM : 0 < M)
    (pred : (Fin d → ZMod M) → Prop) [DecidablePred pred] {g : (Fin d → ℤ) → ℚ}
    (h : IsPiecewiseQuasiPolynomial g) :
    IsPiecewiseQuasiPolynomial
      (fun y ↦ if pred (fun i ↦ (y i : ZMod M)) then g y else 0) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f.mulPeriodicIndicator hM pred, fun y ↦ by simp [hf]⟩

end PiecewiseQuasiPolynomial

/-! ### 3. Faulhaber Polynomial Summation over Arbitrary Integer Intervals -/

section Faulhaber

open Polynomial

/-- For each degree `j : ℕ`, there exists a rational polynomial `Q : ℚ[X]` satisfying the
forward-difference identity `Q(X + 1) - Q(X) = X ^ j`. -/
theorem exists_forwardDiff_poly (j : ℕ) :
    ∃ Q : Polynomial ℚ, Q.comp (X + 1) - Q = X ^ j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    choose Q hQ using fun (r : Fin j) ↦ ih r.1 r.2
    let S : Polynomial ℚ :=
      ∑ r : Fin j, ((Nat.choose (j + 1) r.1 : ℚ) • Q r)
    let P : Polynomial ℚ :=
      ((j + 1 : ℚ)⁻¹) • (X ^ (j + 1) - S)
    refine ⟨P, ?_⟩
    have hS : S.comp (X + 1) - S =
        ∑ r : Fin j, (Nat.choose (j + 1) r.1 : ℚ) • X ^ r.1 := by
      simp only [S, sum_comp, smul_comp, ← Finset.sum_sub_distrib, ← smul_sub]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [hQ r]
    have hbin : (X + 1 : Polynomial ℚ) ^ (j + 1) - X ^ (j + 1) =
        (j + 1 : ℚ) • X ^ j +
          ∑ r : Fin j, (Nat.choose (j + 1) r.1 : ℚ) • X ^ r.1 := by
      rw [add_pow]
      have hsplit : ∑ m ∈ Finset.range (j + 1 + 1),
            X ^ m * (1 : Polynomial ℚ) ^ (j + 1 - m) * (((j + 1).choose m : ℕ) : Polynomial ℚ) =
          (∑ r : Fin j, (Nat.choose (j + 1) r.1 : ℚ) • X ^ r.1) +
            (j + 1 : ℚ) • X ^ j + X ^ (j + 1) := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one,
          Nat.choose_succ_self_right, Finset.sum_range]
        congr 1
        · congr 1
          · refine Finset.sum_congr rfl fun r _ ↦ ?_
            rw [Algebra.smul_def, mul_comm]
            simp
          · rw [Algebra.smul_def, mul_comm]
            simp
      rw [hsplit]
      ring
    have hP : P.comp (X + 1) - P =
        ((j + 1 : ℚ)⁻¹) • ((X + 1) ^ (j + 1) - X ^ (j + 1) - (S.comp (X + 1) - S)) := by
      simp only [P, smul_comp, sub_comp, pow_comp, X_comp]
      rw [← smul_sub]
      congr 1
      ring
    rw [hP, hbin, hS]
    simp only [add_sub_cancel_right]
    rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

/-- Chosen Faulhaber antiderivative polynomial satisfying `Q(X + 1) - Q(X) = X ^ j`. -/
noncomputable def faulhaberPoly (j : ℕ) : Polynomial ℚ :=
  (exists_forwardDiff_poly j).choose

theorem faulhaberPoly_diff (j : ℕ) :
    (faulhaberPoly j).comp (X + 1) - faulhaberPoly j = X ^ j :=
  (exists_forwardDiff_poly j).choose_spec

theorem faulhaberPoly_eval_succ_sub (j : ℕ) (x : ℚ) :
    (faulhaberPoly j).eval (x + 1) - (faulhaberPoly j).eval x = x ^ j := by
  have h := congrArg (Polynomial.eval x) (faulhaberPoly_diff j)
  simpa [Polynomial.eval_comp] using h

/-- Summing `m ^ j` over any integer interval `Finset.Icc a b` with `a ≤ b + 1` equals
`faulhaberPoly j (b + 1) - faulhaberPoly j a`. -/
theorem sum_Icc_pow_eq_faulhaber (j : ℕ) {a b : ℤ} (hab : a ≤ b + 1) :
    (∑ m ∈ Finset.Icc a b, (m : ℚ) ^ j) =
      (faulhaberPoly j).eval ((b + 1 : ℤ) : ℚ) - (faulhaberPoly j).eval (a : ℚ) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b + 1 = a + n := ⟨(b + 1 - a).toNat, by omega⟩
  induction n generalizing b with
  | zero =>
    have hb : b < a := by omega
    rw [Finset.Icc_eq_empty (not_le.2 hb), Finset.sum_empty]
    have : b + 1 = a := by omega
    rw [this, sub_self]
  | succ n ih =>
    have hsplit : Finset.Icc a b = insert b (Finset.Icc a (b - 1)) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem : b ∉ Finset.Icc a (b - 1) := by simp
    rw [hsplit, Finset.sum_insert hnotmem, ih (by omega) (by omega)]
    have hstep := faulhaberPoly_eval_succ_sub j (b : ℚ)
    have hcast1 : ((b - 1 + 1 : ℤ) : ℚ) = (b : ℚ) := by push_cast; ring
    have hcast2 : ((b + 1 : ℤ) : ℚ) = (b : ℚ) + 1 := by push_cast; ring
    rw [hcast1, hcast2]
    linarith

/-- Summing a multivariate polynomial `P(b - m • v)` over `m ∈ Finset.Icc lo hi` (`lo ≤ hi + 1`)
yields a multivariate polynomial in `(b, lo, hi)`. -/
theorem exists_mvPoly_sum_Icc_ray {k : ℕ} (P : MvPolynomial (Fin k) ℚ) (v : Fin k → ℤ) :
    ∃ Q : MvPolynomial (Fin (k + 2)) ℚ,
      ∀ (b : Fin k → ℤ) (lo hi : ℤ), lo ≤ hi + 1 →
        (∑ m ∈ Finset.Icc lo hi,
          MvPolynomial.eval (fun i ↦ ((b i - m * v i : ℤ) : ℚ)) P) =
        MvPolynomial.eval
          (fun j : Fin (k + 2) ↦
            if h : j.1 < k then (b ⟨j.1, h⟩ : ℚ)
            else if j.1 = k then (lo : ℚ) else (hi : ℚ)) Q := by
  induction P using MvPolynomial.induction_on' with
  | monomial s c =>
    let polyT : Polynomial (MvPolynomial (Fin k) ℚ) :=
      Polynomial.C (MvPolynomial.C c) *
        ∏ i ∈ s.support,
          (Polynomial.C (MvPolynomial.X i) -
            Polynomial.C (MvPolynomial.C (v i : ℚ)) * Polynomial.X) ^ (s i)
    let emb : Fin k → Fin (k + 2) := fun i ↦ ⟨i.1, by omega⟩
    let Xlo : MvPolynomial (Fin (k + 2)) ℚ := MvPolynomial.X ⟨k, by omega⟩
    let Xhi : MvPolynomial (Fin (k + 2)) ℚ := MvPolynomial.X ⟨k + 1, by omega⟩
    let Q : MvPolynomial (Fin (k + 2)) ℚ :=
      ∑ r ∈ polyT.support,
        (MvPolynomial.rename emb (polyT.coeff r)) *
          ((faulhaberPoly r).aeval (Xhi + 1) - (faulhaberPoly r).aeval Xlo)
    refine ⟨Q, fun b lo hi hle ↦ ?_⟩
    let env : Fin (k + 2) → ℚ := fun j ↦
      if h : j.1 < k then (b ⟨j.1, h⟩ : ℚ)
      else if j.1 = k then (lo : ℚ) else (hi : ℚ)
    have henv_emb : env ∘ emb = fun i ↦ (b i : ℚ) := by
      ext i; simp [env, emb]
    have henv_lo : env ⟨k, by omega⟩ = (lo : ℚ) := by simp [env]
    have henv_hi : env ⟨k + 1, by omega⟩ = (hi : ℚ) := by simp [env]
    have hterm : ∀ m : ℤ,
        MvPolynomial.eval (fun i ↦ ((b i - m * v i : ℤ) : ℚ)) (MvPolynomial.monomial s c) =
          ∑ r ∈ polyT.support,
            MvPolynomial.eval (fun i ↦ (b i : ℚ)) (polyT.coeff r) * (m : ℚ) ^ r := by
      intro m
      have heval : (polyT.map (MvPolynomial.eval (fun i ↦ (b i : ℚ)))).eval (m : ℚ) =
          MvPolynomial.eval (fun i ↦ ((b i - m * v i : ℤ) : ℚ)) (MvPolynomial.monomial s c) := by
        simp only [polyT, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod,
          Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_pow,
          Polynomial.eval_sub, Polynomial.eval_X, MvPolynomial.eval_C, MvPolynomial.eval_X,
          MvPolynomial.eval_monomial]
        congr 1
        rw [Finsupp.prod]
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        push_cast
        ring
      rw [← heval, Polynomial.eval_map, Polynomial.eval₂_eq_sum]
      rfl
    simp_rw [hterm]
    rw [Finset.sum_comm]
    change _ = MvPolynomial.eval env Q
    simp only [Q, map_sum, map_mul, map_sub, MvPolynomial.eval_rename, henv_emb]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [← Finset.mul_sum, sum_Icc_pow_eq_faulhaber r hle]
    congr 1
    have hfaul : ∀ (e : MvPolynomial (Fin (k + 2)) ℚ),
        MvPolynomial.eval env ((faulhaberPoly r).aeval e) =
          (faulhaberPoly r).eval (MvPolynomial.eval env e) := by
      intro e
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.eval_eq_sum,
        Polynomial.sum_def, Polynomial.sum_def, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp
    rw [hfaul (Xhi + 1), hfaul Xlo]
    simp only [Xhi, Xlo, map_add, MvPolynomial.eval_X, map_one, henv_hi, henv_lo]
    push_cast
    rfl
  | add p₁ p₂ ih₁ ih₂ =>
    obtain ⟨Q₁, hQ₁⟩ := ih₁
    obtain ⟨Q₂, hQ₂⟩ := ih₂
    refine ⟨Q₁ + Q₂, fun b lo hi hle ↦ ?_⟩
    simp only [map_add, Finset.sum_add_distrib, hQ₁ b lo hi hle, hQ₂ b lo hi hle]

end Faulhaber

/-! ### 4. Polynomial-Time Evaluation on Multi-Tape Turing Machines -/

section PolyTimeEval

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

private theorem computableInPolyTime_congr {α β : Type*} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f g : α → β}
    (hf : ComputableInPolyTime f encIn encOut) (h : ∀ a, f a = g a) :
    ComputableInPolyTime g encIn encOut := by
  have : f = g := funext h
  rwa [← this]

private theorem computableInPolyTime_fin_apply {d : ℕ} (i : Fin d) :
    ComputableInPolyTime (fun y : Fin d → ℤ ↦ y i) (encFinFn d encIntBin) encIntBin := by
  let e : Fin d ≃ Fin d := (Fintype.equivFin (Fin d)).trans (finCongr (Fintype.card_fin d))
  have hreidx : ComputableInPolyTime (fun y : Fin d → ℤ ↦ fun j : Fin d ↦ y (e j))
      (encFinFn d encIntBin) (encPi encIntBin) :=
    ComputableInPolyTime.of_eq fun y ↦ by
      simp [encPi_apply, encFinFn_apply, e]
  exact computableInPolyTime_congr
    ((pi_apply (Index := Fin d) encIntBin (e.symm i)).comp hreidx)
    fun y ↦ by simp [e]

private theorem computableInPolyTime_int_mul_const {α : Type} {enc : α ↪ List Bool}
    {f : α → ℤ} (hf : ComputableInPolyTime f enc encIntBin) (c : ℤ) :
    ComputableInPolyTime (fun a ↦ c * f a) enc encIntBin :=
  intBin_mul' (const c) hf

private theorem computableInPolyTime_linearForm {d : ℕ} (a : Fin d → ℤ) :
    ComputableInPolyTime (fun y : Fin d → ℤ ↦ ∑ i : Fin d, a i * y i)
      (encFinFn d encIntBin) encIntBin := by
  suffices ∀ (s : Finset (Fin d)),
      ComputableInPolyTime (fun y : Fin d → ℤ ↦ ∑ i ∈ s, a i * y i)
        (encFinFn d encIntBin) encIntBin from this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using (const (0 : ℤ))
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact intBin_add' (computableInPolyTime_int_mul_const (computableInPolyTime_fin_apply i) (a i))
      ih

/-- Deciding membership in a fixed polyhedral chamber `C` is computable in polynomial time. -/
theorem PolyhedralChamber.computableInPolyTime_decideMem {d : ℕ} (C : PolyhedralChamber d) :
    ComputableInPolyTime C.decideMem (encFinFn d encIntBin) encBool := by
  unfold PolyhedralChamber.decideMem
  induction C.ineqs with
  | nil => simpa using (const true)
  | cons p ps ih =>
    have h1 : ComputableInPolyTime (fun y : Fin d → ℤ ↦ decide ((∑ i, p.1 i * y i) ≤ p.2))
        (encFinFn d encIntBin) encBool :=
      intBin_le.comp ((computableInPolyTime_linearForm p.1).prod (const p.2))
    have hand : ComputableInPolyTime
        (fun y : Fin d → ℤ ↦ decide ((∑ i, p.1 i * y i) ≤ p.2) &&
          ps.all fun q ↦ decide ((∑ i, q.1 i * y i) ≤ q.2))
        (encFinFn d encIntBin) encBool :=
      computableInPolyTime_congr (ite' h1 ih (const false)) fun y ↦ by
        cases decide ((∑ i, p.1 i * y i) ≤ p.2) <;> rfl
    simpa [List.all_cons] using hand

/-- Evaluating a fixed integer multivariate polynomial `P : MvPolynomial (Fin d) ℤ` at binary
integer inputs `y : Fin d → ℤ` is computable in polynomial time. -/
theorem computableInPolyTime_mvPoly_eval {d : ℕ} (P : MvPolynomial (Fin d) ℤ) :
    ComputableInPolyTime (fun y : Fin d → ℤ ↦ MvPolynomial.eval y P)
      (encFinFn d encIntBin) encIntBin := by
  induction P using MvPolynomial.induction_on' with
  | monomial s c =>
    have hpow : ∀ (i : Fin d) (e : ℕ),
        ComputableInPolyTime (fun y : Fin d → ℤ ↦ (y i) ^ e)
          (encFinFn d encIntBin) encIntBin := by
      intro i e
      induction e with
      | zero => simpa using (const (1 : ℤ))
      | succ e ihe =>
        simp_rw [pow_succ]
        exact intBin_mul' ihe (computableInPolyTime_fin_apply i)
    have hprod : ∀ (t : Finset (Fin d)),
        ComputableInPolyTime (fun y : Fin d → ℤ ↦ ∏ i ∈ t, (y i) ^ (s i))
          (encFinFn d encIntBin) encIntBin := by
      intro t
      induction t using Finset.induction_on with
      | empty => simpa using (const (1 : ℤ))
      | insert i t hi iht =>
        simp_rw [Finset.prod_insert hi]
        exact intBin_mul' (hpow i (s i)) iht
    have hmon := intBin_mul' (const c) (hprod s.support)
    refine computableInPolyTime_congr hmon fun y ↦ ?_
    simp [MvPolynomial.eval_monomial, Finsupp.prod]
  | add p₁ p₂ ih₁ ih₂ =>
    simpa [map_add] using intBin_add' ih₁ ih₂

private theorem computableInPolyTime_int_emod_toNat {M : ℕ} (hM : 0 < M) :
    ComputableInPolyTime (fun z : ℤ ↦ (z % (M : ℤ)).toNat) encIntBin encNat := by
  have hrem : ComputableInPolyTime (fun z : ℤ ↦ z.natAbs % M) encIntBin encNat :=
    binary_mod' intBin_natAbs (const M)
  have hneg : ComputableInPolyTime (fun z : ℤ ↦ decide (z < 0)) encIntBin encBool :=
    intBin_isNeg
  have hrem0 : ComputableInPolyTime (fun z : ℤ ↦ decide (z.natAbs % M = 0)) encIntBin encBool :=
    computableInPolyTime_congr (intBin_isZero.comp (intBin_natCast.comp hrem)) fun z ↦ by
      simp only [Function.comp_apply, Int.natCast_eq_zero]
  have hsub : ComputableInPolyTime (fun z : ℤ ↦ M - z.natAbs % M) encIntBin encNat :=
    binary_sub' (const M) hrem
  have hbranch := ite' hneg (ite' hrem0 (const (0 : ℕ)) hsub) hrem
  refine computableInPolyTime_congr hbranch fun z ↦ ?_
  by_cases hz : z < 0
  · simp only [hz, decide_true, ↓reduceIte]
    have hz_eq : z = -(z.natAbs : ℤ) := by omega
    by_cases hr0 : z.natAbs % M = 0
    · simp only [hr0, decide_true, ↓reduceIte]
      have hdvd : (M : ℤ) ∣ z := by
        rw [hz_eq]; exact dvd_neg.2 (Int.natCast_dvd_natCast.2 (Nat.dvd_of_mod_eq_zero hr0))
      rw [Int.emod_eq_zero_of_dvd hdvd]; rfl
    · simp only [hr0, decide_false, Bool.false_eq_true, ↓reduceIte]
      have h1 : 0 < z.natAbs % M := Nat.pos_of_ne_zero hr0
      have h2 : z.natAbs % M < M := Nat.mod_lt _ hM
      have hq : z = (M : ℤ) * (-(z.natAbs / M : ℕ) - 1) + ((M - z.natAbs % M : ℕ) : ℤ) := by
        have hdm : (z.natAbs : ℤ) = (M : ℤ) * (z.natAbs / M : ℕ) + (z.natAbs % M : ℕ) := by
          exact_mod_cast (Nat.div_add_mod z.natAbs M).symm
        have hsub' : ((M - z.natAbs % M : ℕ) : ℤ) = (M : ℤ) - (z.natAbs % M : ℕ) := by omega
        linarith
      have hmod : z % (M : ℤ) = ((M - z.natAbs % M : ℕ) : ℤ) := by
        conv_lhs => rw [hq]
        rw [Int.mul_add_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
      rw [hmod, Int.toNat_natCast]
  · simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hz_eq : z = (z.natAbs : ℤ) := by omega
    rw [hz_eq]
    have hnat : ((z.natAbs : ℤ) % (M : ℤ)).toNat = z.natAbs % M := by
      rw [← Int.natCast_emod, Int.toNat_natCast]
    exact hnat

private theorem computableInPolyTime_int_exactDiv {α : Type} {enc : α ↪ List Bool}
    {f : α → ℤ} (hf : ComputableInPolyTime f enc encIntBin) (D : ℕ) :
    ComputableInPolyTime
      (fun a ↦ if decide (f a < 0) then -(((f a).natAbs / D : ℕ) : ℤ)
        else (((f a).natAbs / D : ℕ) : ℤ))
      enc encIntBin :=
  intBin_signMagnitude' (intBin_isNeg.comp hf) (binary_div' (intBin_natAbs.comp hf) (const D))

private theorem exists_clearDenom_mvPoly {d : ℕ} (p : MvPolynomial (Fin d) ℚ) :
    ∃ (D : ℕ) (P : MvPolynomial (Fin d) ℤ), 0 < D ∧
      ∀ y : Fin d → ℤ, (D : ℚ) * MvPolynomial.eval (fun i ↦ (y i : ℚ)) p =
        (MvPolynomial.eval y P : ℚ) := by
  let D : ℕ := ∏ s ∈ p.support, (p.coeff s).den
  have hD : 0 < D := Finset.prod_pos fun s _ ↦ (p.coeff s).pos
  let P : MvPolynomial (Fin d) ℤ :=
    ∑ s ∈ p.support,
      MvPolynomial.monomial s ((p.coeff s).num * ((D / (p.coeff s).den : ℕ) : ℤ))
  refine ⟨D, P, hD, fun y ↦ ?_⟩
  rw [MvPolynomial.eval_eq', Finset.mul_sum, map_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [MvPolynomial.eval_monomial]
  have hdvd : (p.coeff s).den ∣ D := Finset.dvd_prod_of_mem _ hs
  have hmul : (p.coeff s).den * (D / (p.coeff s).den) = D := Nat.mul_div_cancel' hdvd
  have hden_ne : ((p.coeff s).den : ℚ) ≠ 0 := by positivity
  have hcoeff : (D : ℚ) * p.coeff s =
      (((p.coeff s).num * ((D / (p.coeff s).den : ℕ) : ℤ) : ℤ) : ℚ) := by
    have hq := (Rat.num_div_den (p.coeff s)).symm
    have hmulQ : ((p.coeff s).den : ℚ) * ((D / (p.coeff s).den : ℕ) : ℚ) = (D : ℚ) := by
      exact_mod_cast hmul
    simp only [Int.cast_mul, Int.cast_natCast]
    calc
      (D : ℚ) * p.coeff s
          = ((p.coeff s).den : ℚ) * ((D / (p.coeff s).den : ℕ) : ℚ) *
              (((p.coeff s).num : ℚ) / ((p.coeff s).den : ℚ)) := by rw [hmulQ, ← hq]
      _ = ((p.coeff s).num : ℚ) * ((D / (p.coeff s).den : ℕ) : ℚ) := by
            field_simp [hden_ne]
  rw [← mul_assoc, hcoeff]
  simp only [Finsupp.prod, Int.cast_mul, Int.cast_prod, Int.cast_pow]
  congr 1
  exact (Finset.prod_subset (Finset.subset_univ s.support) fun i _ hi ↦ by
    simp [Finsupp.notMem_support_iff.1 hi]).symm

/-- **Polynomial-Time Evaluation of Fixed Piecewise Quasi-Polynomials**:
any integer-valued function `g : (Fin d → ℤ) → ℤ` given by a fixed
piecewise quasi-polynomial is computable in polynomial time on a multi-tape Turing machine from
binary-encoded inputs. -/
theorem PiecewiseQuasiPolynomial.computableInPolyTime_int {d : ℕ}
    {g : (Fin d → ℤ) → ℤ} (hg : PiecewiseQuasiPolynomial.IsPiecewiseQuasiPolynomial
      (fun y ↦ (g y : ℚ))) :
    ComputableInPolyTime g (encFinFn d encIntBin) encIntBin := by
  obtain ⟨f, hf⟩ := hg
  have hpiece_pt : ∀ piece ∈ f.pieces,
      ∃ evalPiece : (Fin d → ℤ) → ℤ,
        ComputableInPolyTime evalPiece (encFinFn d encIntBin) encIntBin ∧
        ∀ y ∈ piece.1.carrier, evalPiece y = g y := by
    intro piece hpiece
    obtain ⟨M, hM, hML⟩ := piece.2.exists_pos_period
    have : NeZero M := ⟨hM.ne'⟩
    let rVec (r : Fin d → Fin M) : Fin d → ℤ := fun i ↦ (r i).1
    have hclear : ∀ r : Fin d → Fin M,
        ∃ (D : ℕ) (P : MvPolynomial (Fin d) ℤ), 0 < D ∧
          ∀ y : Fin d → ℤ,
            (D : ℚ) * MvPolynomial.eval (fun i ↦ (y i : ℚ))
              (piece.2.poly (QuotientAddGroup.mk (rVec r))) = (MvPolynomial.eval y P : ℚ) :=
      fun r ↦ exists_clearDenom_mvPoly _
    choose Dr Pr hDr hPr using hclear
    let evalRes (r : Fin d → Fin M) (y : Fin d → ℤ) : ℤ :=
      let v := MvPolynomial.eval y (Pr r)
      if decide (v < 0) then -((v.natAbs / Dr r : ℕ) : ℤ) else ((v.natAbs / Dr r : ℕ) : ℤ)
    have hevalRes_pt : ∀ r : Fin d → Fin M,
        ComputableInPolyTime (evalRes r) (encFinFn d encIntBin) encIntBin :=
      fun r ↦ computableInPolyTime_int_exactDiv (computableInPolyTime_mvPoly_eval (Pr r)) (Dr r)
    let eqRes (r : Fin d → Fin M) (y : Fin d → ℤ) : Bool :=
      (List.finRange d).all fun i ↦ decide (((y i % (M : ℤ)).toNat : ℤ) = ((r i).1 : ℤ))
    have heqRes_pt : ∀ r : Fin d → Fin M,
        ComputableInPolyTime (eqRes r) (encFinFn d encIntBin) encBool := by
      intro r
      suffices ∀ (l : List (Fin d)),
          ComputableInPolyTime
            (fun y : Fin d → ℤ ↦
              l.all fun i ↦ decide (((y i % (M : ℤ)).toNat : ℤ) = ((r i).1 : ℤ)))
            (encFinFn d encIntBin) encBool from this (List.finRange d)
      intro l
      induction l with
      | nil => simpa using (const true)
      | cons i ls ih =>
        have hi : ComputableInPolyTime
            (fun y : Fin d → ℤ ↦ decide (((y i % (M : ℤ)).toNat : ℤ) = ((r i).1 : ℤ)))
            (encFinFn d encIntBin) encBool :=
          computableInPolyTime_congr (intBin_isZero.comp (intBin_sub'
            (intBin_natCast.comp ((computableInPolyTime_int_emod_toNat hM).comp
              (computableInPolyTime_fin_apply i)))
            (const ((r i).1 : ℤ)))) fun y ↦ by
            simp [sub_eq_zero]
        have hand := ite' hi ih (const false)
        refine computableInPolyTime_congr hand fun y ↦ ?_
        simp only [List.all_cons]
        cases decide (((y i % (M : ℤ)).toNat : ℤ) = ((r i).1 : ℤ)) <;> rfl
    let resList : List (Fin d → Fin M) := (Finset.univ : Finset (Fin d → Fin M)).toList
    let evalPiece : (Fin d → ℤ) → ℤ := fun y ↦
      resList.foldr (fun r acc ↦ if eqRes r y then evalRes r y else acc) 0
    have hevalPiece_pt : ComputableInPolyTime evalPiece (encFinFn d encIntBin) encIntBin := by
      suffices ∀ (l : List (Fin d → Fin M)),
          ComputableInPolyTime
            (fun y : Fin d → ℤ ↦ l.foldr (fun r acc ↦ if eqRes r y then evalRes r y else acc) 0)
            (encFinFn d encIntBin) encIntBin from this resList
      intro l
      induction l with
      | nil => simpa using (const (0 : ℤ))
      | cons r ls ih =>
        simpa [List.foldr_cons] using ite' (heqRes_pt r) (hevalRes_pt r) ih
    refine ⟨evalPiece, hevalPiece_pt, fun y hy ↦ ?_⟩
    let r₀ : Fin d → Fin M := fun i ↦
      ⟨(y i % (M : ℤ)).toNat, by
        have h0 := Int.emod_nonneg (y i) (by positivity : (M : ℤ) ≠ 0)
        have hlt := Int.emod_lt_of_pos (y i) (by positivity : (0 : ℤ) < M)
        omega⟩
    have heqRes_iff : ∀ r : Fin d → Fin M, eqRes r y = true ↔ r = r₀ := by
      intro r
      simp only [eqRes, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq,
        funext_iff, Fin.ext_iff, r₀]
      refine forall_congr' fun i ↦ ?_
      omega
    have hfold : ∀ (l : List (Fin d → Fin M)), r₀ ∈ l →
        l.foldr (fun r acc ↦ if eqRes r y then evalRes r y else acc) 0 = evalRes r₀ y := by
      intro l hl
      induction l with
      | nil => cases hl
      | cons r ls ih =>
        simp only [List.foldr_cons]
        by_cases hrr : r = r₀
        · rw [hrr]
          have htrue : eqRes r₀ y = true := (heqRes_iff r₀).2 rfl
          simp only [htrue, ↓reduceIte]
        · have hfalse : eqRes r y = false := Bool.eq_false_iff.2 fun h ↦ hrr ((heqRes_iff r).1 h)
          simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
          exact ih ((List.mem_cons.1 hl).resolve_left (Ne.symm hrr))
    have hr₀_mem : r₀ ∈ resList := Finset.mem_toList.2 (Finset.mem_univ r₀)
    change resList.foldr _ 0 = g y
    rw [hfold resList hr₀_mem]
    have hcoset : QuotientAddGroup.mk (s := piece.2.sublattice) y =
        QuotientAddGroup.mk (s := piece.2.sublattice) (rVec r₀) := by
      rw [QuotientAddGroup.eq]
      apply hML
      intro i
      have h0 := Int.emod_nonneg (y i) (by positivity : (M : ℤ) ≠ 0)
      have hdm := Int.mul_ediv_add_emod (y i) (M : ℤ)
      have hr0_val : rVec r₀ i = y i % (M : ℤ) := by
        simp only [rVec, r₀]; omega
      change (M : ℤ) ∣ -(y i) + rVec r₀ i
      rw [hr0_val]
      exact ⟨-(y i / (M : ℤ)), by linarith⟩
    have hval_q : (MvPolynomial.eval y (Pr r₀) : ℚ) = (Dr r₀ : ℚ) * (g y : ℚ) := by
      rw [← hPr r₀ y, ← hcoset]
      have hg_eq := hf y
      dsimp only at hg_eq
      rw [PiecewiseQuasiPolynomial.eval_eq_of_mem f hpiece hy] at hg_eq
      rw [← hg_eq]
      rfl
    have hval_z : MvPolynomial.eval y (Pr r₀) = (Dr r₀ : ℤ) * g y := by exact_mod_cast hval_q
    simp only [evalRes, hval_z]
    have hDpos : 0 < Dr r₀ := hDr r₀
    by_cases hneg : (Dr r₀ : ℤ) * g y < 0
    · simp only [hneg, decide_true, ↓reduceIte]
      have hgn : g y < 0 := by nlinarith
      have habs : ((Dr r₀ : ℤ) * g y).natAbs = Dr r₀ * (g y).natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [habs, Nat.mul_div_cancel_left _ hDpos]
      omega
    · simp only [hneg, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hgn : 0 ≤ g y := by nlinarith
      have habs : ((Dr r₀ : ℤ) * g y).natAbs = Dr r₀ * (g y).natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [habs, Nat.mul_div_cancel_left _ hDpos]
      omega
  classical
  let evalOf (p : PolyhedralChamber d × QuasiPolynomial d) : (Fin d → ℤ) → ℤ :=
    if h : p ∈ f.pieces then (hpiece_pt p h).choose else fun _ ↦ 0
  let evalAll : (Fin d → ℤ) → ℤ := fun y ↦
    f.pieces.foldr (fun p acc ↦ if p.1.decideMem y then evalOf p y else acc) 0
  have hevalAll_pt : ComputableInPolyTime evalAll (encFinFn d encIntBin) encIntBin := by
    suffices ∀ (l : List (PolyhedralChamber d × QuasiPolynomial d)),
        (∀ p ∈ l, p ∈ f.pieces) →
        ComputableInPolyTime
          (fun y : Fin d → ℤ ↦
            l.foldr (fun p acc ↦ if p.1.decideMem y then evalOf p y else acc) 0)
          (encFinFn d encIntBin) encIntBin from this f.pieces (fun _ h ↦ h)
    intro l hl
    induction l with
    | nil => simpa using (const (0 : ℤ))
    | cons p ps ih =>
      have hp : p ∈ f.pieces := hl p (List.mem_cons_self ..)
      have hev : ComputableInPolyTime (evalOf p) (encFinFn d encIntBin) encIntBin := by
        simp only [evalOf, hp, ↓reduceDIte]
        exact (hpiece_pt p hp).choose_spec.1
      simpa [List.foldr_cons] using
        ite' p.1.computableInPolyTime_decideMem hev (ih fun q hq ↦ hl q (List.mem_cons_of_mem _ hq))
  have hevalAll_eq : ∀ y : Fin d → ℤ, evalAll y = g y := by
    intro y
    suffices ∀ (l : List (PolyhedralChamber d × QuasiPolynomial d)),
        (∀ p ∈ l, p ∈ f.pieces) → (∃ p ∈ l, y ∈ p.1.carrier) →
        l.foldr (fun p acc ↦ if p.1.decideMem y then evalOf p y else acc) 0 = g y from
      this f.pieces (fun _ h ↦ h) (f.cover y)
    intro l hl hex
    induction l with
    | nil => rcases hex with ⟨_, h, _⟩; cases h
    | cons p ps ih =>
      simp only [List.foldr_cons]
      by_cases hy : y ∈ p.1.carrier
      · have htrue : p.1.decideMem y = true := (p.1.decideMem_eq_true_iff y).2 hy
        have hp : p ∈ f.pieces := hl p (List.mem_cons_self ..)
        simp only [htrue, ↓reduceIte, evalOf, hp, ↓reduceDIte]
        exact (hpiece_pt p hp).choose_spec.2 y hy
      · have hfalse : p.1.decideMem y = false :=
          Bool.eq_false_iff.2 fun h ↦ hy ((p.1.decideMem_eq_true_iff y).1 h)
        simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨q, hq, hyq⟩ := hex
        have hqps : q ∈ ps := by
          rcases List.mem_cons.1 hq with rfl | hq'
          · exact (hy hyq).elim
          · exact hq'
        exact ih (fun r hr ↦ hl r (List.mem_cons_of_mem _ hr)) ⟨q, hqps, hyq⟩
  exact computableInPolyTime_congr hevalAll_pt hevalAll_eq

/-- Polynomial-time evaluation of a nonnegative-integer-valued piecewise quasi-polynomial,
outputting binary natural numbers (`encNat`). -/
theorem PiecewiseQuasiPolynomial.computableInPolyTime_nat {d : ℕ}
    {g : (Fin d → ℤ) → ℕ}
    (hg : PiecewiseQuasiPolynomial.IsPiecewiseQuasiPolynomial (fun y ↦ (g y : ℚ))) :
    ComputableInPolyTime g (encFinFn d encIntBin) encNat := by
  have hint : ComputableInPolyTime (fun y ↦ (g y : ℤ)) (encFinFn d encIntBin) encIntBin :=
    PiecewiseQuasiPolynomial.computableInPolyTime_int (by simpa using hg)
  exact computableInPolyTime_congr (intBin_toNat.comp hint) fun y ↦ by simp

/-- **Polynomial-Time Positivity Decision**:
deciding whether a fixed integer-valued piecewise quasi-polynomial is strictly positive lies in
`Cslib.Complexity.P`. -/
theorem PiecewiseQuasiPolynomial.positivity_mem_P {d : ℕ}
    {g : (Fin d → ℤ) → ℤ}
    (hg : PiecewiseQuasiPolynomial.IsPiecewiseQuasiPolynomial (fun y ↦ (g y : ℚ))) :
    {y : Fin d → ℤ | 0 < g y} ∈ Cslib.Complexity.P (encFinFn d encIntBin) := by
  rw [Cslib.Complexity.mem_P]
  refine ⟨fun y ↦ decide (0 < g y), intBin_isPos.comp
    (PiecewiseQuasiPolynomial.computableInPolyTime_int hg), fun y ↦ by simp⟩

end PolyTimeEval

end CslibFrontier.Complexity.Polyhedra
