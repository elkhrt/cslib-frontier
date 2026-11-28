module
-- upstream: candidate

public import Cslib.Computability.QueryComplexity.Measures
public import CslibFrontier.Computability.DecisionTree.Certificate
public import CslibFrontier.Computability.QueryComplexity.OneSided
public import CslibFrontier.Computability.QueryComplexity.Randomized
import CslibFrontier.Computability.QueryComplexity.Randomized.Nisan
import CslibFrontier.Computability.QueryComplexity.Relations
import Mathlib.Tactic.Ring

/-!
# Unambiguous Certificate Complexity and Classical Polynomial Relations

Defines unambiguous certificate families and unambiguous certificate complexity for total Boolean
functions, proves that unambiguous certificate complexity upper-bounds ordinary certificate
complexity, and establishes the quadratic bound `C(f) ≤ 9 R_{1/3}(f)²` relating certificate
complexity to bounded-error randomized query complexity.

## Main definitions

* `CslibFrontier.QueryComplexity.IsUnambiguousCertFamily`: predicate stating that a finite family
  of partial assignments forces `f` to `b`, covers `f⁻¹(b)`, and assigns pairwise incompatible
  partial assignments so no input agrees with two distinct members.
* `CslibFrontier.QueryComplexity.unambiguousCertificateComplexityFor`: one-sided unambiguous
  certificate complexity `UC_b(f)`.
* `CslibFrontier.QueryComplexity.unambiguousCertificateComplexity`: two-sided unambiguous
  certificate complexity `UC(f) = max(UC_0(f), UC_1(f))`.

## Main results

* `CslibFrontier.QueryComplexity.isUnambiguousCertFamily_truthTable`: the full truth-table
  partial assignments for `f⁻¹(b)` form an unambiguous `b`-certificate family.
* `CslibFrontier.QueryComplexity.exists_isUnambiguousCertFamily_eq`: an unambiguous `b`-certificate
  family attaining `UC_b(f)` always exists.
* `CslibFrontier.QueryComplexity.certificateComplexityFor_le_unambiguousCertificateComplexityFor`:
  `C_b(f) ≤ UC_b(f)`.
* `CslibFrontier.QueryComplexity.certificateComplexity_le_unambiguousCertificateComplexity`:
  `C(f) ≤ UC(f)`.
* `CslibFrontier.QueryComplexity.certificateComplexity_le_nine_mul_randomizedComplexity_sq`:
  `C(f) ≤ 9 R_{1/3}(f)²`.
-/

public section

namespace CslibFrontier.QueryComplexity

open Cslib Cslib.BitString Cslib.QueryComplexity Finset

/-- A finite collection `ℱ` of partial assignments is an unambiguous `b`-certificate family for `f`
when every member forces `f` to `b`, every `b`-input agrees with some member of `ℱ`, and no input
agrees with two distinct members of `ℱ`. -/
@[expose]
public def IsUnambiguousCertFamily {n : ℕ} (f : BooleanFunction n) (b : Bool)
    (ℱ : Finset (PartialAssignment n)) : Prop :=
  (∀ C ∈ ℱ, Forces f C b) ∧
    (∀ x : BitString n, f x = b → ∃ C ∈ ℱ, Agrees C x) ∧
    ∀ C₁ ∈ ℱ, ∀ C₂ ∈ ℱ, ∀ x : BitString n, Agrees C₁ x → Agrees C₂ x → C₁ = C₂

/-- The full truth-table assignments for `f⁻¹(b)` always form an unambiguous `b`-certificate
family. -/
public theorem isUnambiguousCertFamily_truthTable {n : ℕ} (f : BooleanFunction n) (b : Bool) :
    IsUnambiguousCertFamily f b ((univ.filter fun x => f x = b).image ofBitString) := by
  refine ⟨fun C hC y hy => ?_, fun x hx => ?_, fun C₁ hC₁ C₂ hC₂ x h₁ h₂ => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := mem_image.mp hC
    rw [agrees_ofBitString_iff.mp hy, (mem_filter.mp hx).2]
  · refine ⟨ofBitString x, ?_, agrees_ofBitString_iff.mpr rfl⟩
    exact mem_image.mpr ⟨x, mem_filter.mpr ⟨mem_univ x, hx⟩, rfl⟩
  · obtain ⟨x₁, -, rfl⟩ := mem_image.mp hC₁
    obtain ⟨x₂, -, rfl⟩ := mem_image.mp hC₂
    rw [← agrees_ofBitString_iff.mp h₁, ← agrees_ofBitString_iff.mp h₂]

/-- One-sided unambiguous certificate complexity `UC_b(f)`: the minimum maximum certificate size
among all unambiguous `b`-certificate families for `f`. -/
public noncomputable def unambiguousCertificateComplexityFor {n : ℕ} (f : BooleanFunction n)
    (b : Bool) : ℕ :=
  sInf {k : ℕ | ∃ ℱ : Finset (PartialAssignment n),
    IsUnambiguousCertFamily f b ℱ ∧ ℱ.sup size ≤ k}

/-- Two-sided unambiguous certificate complexity `UC(f) = max(UC_0(f), UC_1(f))`. -/
public noncomputable def unambiguousCertificateComplexity {n : ℕ} (f : BooleanFunction n) : ℕ :=
  max (unambiguousCertificateComplexityFor f false) (unambiguousCertificateComplexityFor f true)

/-- Upper-bound rule for `UC_b(f)` from exhibiting an unambiguous `b`-certificate family. -/
public theorem unambiguousCertificateComplexityFor_le {n : ℕ} {f : BooleanFunction n} {b : Bool}
    {ℱ : Finset (PartialAssignment n)} (hℱ : IsUnambiguousCertFamily f b ℱ) {k : ℕ}
    (hk : ∀ C ∈ ℱ, size C ≤ k) : unambiguousCertificateComplexityFor f b ≤ k :=
  Nat.sInf_le ⟨ℱ, hℱ, Finset.sup_le hk⟩

/-- Some unambiguous `b`-certificate family attains `UC_b(f)`. -/
public theorem exists_isUnambiguousCertFamily_eq {n : ℕ} (f : BooleanFunction n) (b : Bool) :
    ∃ ℱ : Finset (PartialAssignment n),
      IsUnambiguousCertFamily f b ℱ ∧ ℱ.sup size ≤ unambiguousCertificateComplexityFor f b := by
  let S : Set ℕ := {k : ℕ | ∃ ℱ : Finset (PartialAssignment n),
    IsUnambiguousCertFamily f b ℱ ∧ ℱ.sup size ≤ k}
  have hne : S.Nonempty := ⟨n, (univ.filter fun x => f x = b).image ofBitString,
    isUnambiguousCertFamily_truthTable f b, Finset.sup_le fun C hC => by
      obtain ⟨x, -, rfl⟩ := mem_image.mp hC
      simp⟩
  exact Nat.sInf_mem hne

/-- Every unambiguous `b`-certificate family supplies a `b`-certificate for each `b`-input, so
`C_b(f) ≤ UC_b(f)`. -/
public theorem certificateComplexityFor_le_unambiguousCertificateComplexityFor {n : ℕ}
    (f : BooleanFunction n) (b : Bool) :
    certificateComplexityFor f b ≤ unambiguousCertificateComplexityFor f b := by
  obtain ⟨ℱ, ⟨hforce, hcov, -⟩, hsup⟩ := exists_isUnambiguousCertFamily_eq f b
  refine Finset.sup_le fun x hx => ?_
  have hfx : f x = b := (mem_filter.mp hx).2
  obtain ⟨C, hC, hAg⟩ := hcov x hfx
  have hCert : IsCertificate f x (support C) :=
    (forces_iff_isCertificate_support hAg).mp (hfx ▸ hforce C hC)
  exact (certificateComplexityAt_le hCert).trans ((le_sup (f := size) hC).trans hsup)

/-- Two-sided certificate complexity is bounded by two-sided unambiguous certificate complexity:
`C(f) ≤ UC(f)`. -/
public theorem certificateComplexity_le_unambiguousCertificateComplexity {n : ℕ}
    (f : BooleanFunction n) :
    certificateComplexity f ≤ unambiguousCertificateComplexity f := by
  refine Finset.sup_le fun x _ => ?_
  cases hfx : f x
  · exact (le_sup (s := univ.filter fun y => f y = false)
      (f := certificateComplexityAt f) (mem_filter.mpr ⟨mem_univ x, hfx⟩)).trans
      ((certificateComplexityFor_le_unambiguousCertificateComplexityFor f false).trans
        (le_max_left _ _))
  · exact (le_sup (s := univ.filter fun y => f y = true)
      (f := certificateComplexityAt f) (mem_filter.mpr ⟨mem_univ x, hfx⟩)).trans
      ((certificateComplexityFor_le_unambiguousCertificateComplexityFor f true).trans
        (le_max_right _ _))

/-- Certificate complexity is at most quadratic in bounded-error randomized query complexity:
`C(f) ≤ 9 R_{1/3}(f)²`. -/
public theorem certificateComplexity_le_nine_mul_randomizedComplexity_sq {n : ℕ}
    (f : BooleanFunction n) :
    certificateComplexity f ≤ 9 * randomizedComplexity (1 / 3) f ^ 2 := by
  calc
    certificateComplexity f ≤ blockSensitivity f ^ 2 :=
      certificateComplexity_le_blockSensitivity_sq f
    _ ≤ (3 * randomizedComplexity (1 / 3) f) ^ 2 :=
      Nat.pow_le_pow_left (blockSensitivity_le_three_mul_randomizedComplexity f) 2
    _ = 9 * randomizedComplexity (1 / 3) f ^ 2 := by ring

end CslibFrontier.QueryComplexity
