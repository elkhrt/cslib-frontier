module

public import CslibFrontier.Foundations.LinearAlgebra.FreeAlgebra
public import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Characteristic-Free Multilinearization and the Amitsur–Levitzki Degree Lower Bound

Characteristic-free partial linearization of noncommutative polynomial identities over arbitrary
commutative rings, together with the staircase matrix-unit proof that the $k \times k$ matrix
algebra $M_k(R)$ over any nontrivial commutative ring $R$ satisfies no nonzero polynomial identity
of degree strictly less than $2k$.

## Main definitions

* `CslibFrontier.Algebra.noncommSupport`, `CslibFrontier.Algebra.noncommDegree`: monomial
  support and total degree in `FreeAlgebra R X`.
* `CslibFrontier.Algebra.IsPolyIdentity`: vanishing of a noncommutative polynomial on all tuples
  in an $R$-algebra $A$.
* `CslibFrontier.Algebra.IsMultilinear`: every variable occurs with multiplicity exactly $1$ in
  every monomial of the support.
* `CslibFrontier.Algebra.staircaseMatrix`: staircase matrix units
  $e_{0,0}, e_{0,1}, e_{1,1}, e_{1,2}, \dots, e_{k-1,k-1} \in M_k(R)$.

## Main results

* `CslibFrontier.Algebra.exists_multilinear_identity_le`: any $R$-algebra satisfying a nonzero
  polynomial identity of degree at most $k$ satisfies a nonzero multilinear identity of degree at
  most $k$.
* `CslibFrontier.Algebra.exists_multilinear_identity_exact`: any $R$-algebra satisfying a nonzero
  polynomial identity of degree at most $k$ satisfies a nonzero multilinear identity of exact
  degree $k$.
* `CslibFrontier.Algebra.matrix_no_identity_lt_two_mul_dim`: over any nontrivial commutative ring
  $R$, $M_k(R)$ satisfies no nonzero polynomial identity of degree strictly less than $2k$.
-/

public section

namespace CslibFrontier.Algebra

/-- The support of a noncommutative polynomial $f \in R\{x_1,\dots,x_n\}$: the finite set of
monomials with nonzero coefficient. -/
noncomputable def noncommSupport {R X : Type*} [CommSemiring R]
    (f : FreeAlgebra R X) : Finset (FreeMonoid X) :=
  ((FreeAlgebra.basisFreeMonoid R X).repr f).support

/-- Membership in `noncommSupport f` holds iff the monomial has nonzero coefficient in `f`. -/
theorem mem_noncommSupport_iff {R X : Type*} [CommSemiring R]
    {f : FreeAlgebra R X} {w : FreeMonoid X} :
    w ∈ noncommSupport f ↔ FreeAlgebra.coeff w f ≠ 0 := by
  rw [noncommSupport, Finsupp.mem_support_iff, FreeAlgebra.coeff_def]
  rfl

/-- Number of nonzero monomials (sparsity) of a noncommutative polynomial. -/
noncomputable def noncommSparsity {R X : Type*} [CommSemiring R]
    (f : FreeAlgebra R X) : ℕ :=
  (noncommSupport f).card

/-- Sparsity equals the cardinality of the support. -/
theorem noncommSparsity_eq_card {R X : Type*} [CommSemiring R] (f : FreeAlgebra R X) :
    noncommSparsity f = (noncommSupport f).card := by
  simp [noncommSparsity]

/-- Total degree of a noncommutative polynomial (0 for the zero polynomial). -/
noncomputable def noncommDegree {R X : Type*} [CommSemiring R]
    (f : FreeAlgebra R X) : ℕ :=
  (noncommSupport f).sup fun w ↦ w.toList.length

/-- Every monomial in the support has length at most `noncommDegree f`. -/
theorem length_le_noncommDegree {R X : Type*} [CommSemiring R]
    {f : FreeAlgebra R X} {w : FreeMonoid X} (hw : w ∈ noncommSupport f) :
    w.toList.length ≤ noncommDegree f :=
  Finset.le_sup (f := fun u : FreeMonoid X ↦ u.toList.length) hw

/-- `noncommDegree f ≤ d` iff every monomial in the support of `f` has length at most `d`. -/
theorem noncommDegree_le_iff {R X : Type*} [CommSemiring R]
    {f : FreeAlgebra R X} {d : ℕ} :
    noncommDegree f ≤ d ↔ ∀ w ∈ noncommSupport f, w.toList.length ≤ d := by
  simp [noncommDegree]

/-- The support of a noncommutative polynomial is empty iff the polynomial is zero. -/
theorem noncommSupport_eq_empty_iff {R X : Type*} [CommSemiring R]
    {f : FreeAlgebra R X} :
    noncommSupport f = ∅ ↔ f = 0 := by
  rw [noncommSupport, Finsupp.support_eq_empty]
  exact (FreeAlgebra.basisFreeMonoid R X).repr.map_eq_zero_iff

/-- Support expansion of a noncommutative polynomial over its monomials. -/
theorem freeAlgebra_eq_sum_support {R X : Type*} [CommSemiring R] (f : FreeAlgebra R X) :
    f = ∑ w ∈ noncommSupport f,
      FreeAlgebra.coeff w f • (FreeMonoid.lift (FreeAlgebra.ι R) w : FreeAlgebra R X) := by
  classical
  apply FreeAlgebra.ext_coeff
  intro u
  rw [map_sum]
  simp only [map_smul, FreeAlgebra.coeff_lift_ι, smul_eq_mul, Finsupp.single_apply]
  by_cases hu : u ∈ noncommSupport f
  · rw [Finset.sum_eq_single u]
    · simp
    · intro w _ hwu
      simp [hwu]
    · intro h
      exact absurd hu h
  · rw [Finset.sum_eq_zero]
    · exact not_not.mp ((not_congr mem_noncommSupport_iff).mp hu)
    · intro w hw
      have hwu : w ≠ u := fun h ↦ hu (h ▸ hw)
      simp [hwu]

/-- A noncommutative polynomial $f \in R\{x_1,\dots,x_n\}$ is a polynomial identity for an
$R$-algebra $A$ if it vanishes under every evaluation $x : \mathrm{Fin}\,n \to A$. -/
@[expose] def IsPolyIdentity {R : Type*} [CommRing R] (A : Type*) [Ring A] [Algebra R A]
    {n : ℕ} (f : FreeAlgebra R (Fin n)) : Prop :=
  ∀ x : Fin n → A, FreeAlgebra.lift R x f = 0

/-- A noncommutative polynomial $f \in R\{x_1,\dots,x_n\}$ is *multilinear* if every variable
occurs with multiplicity exactly $1$ in every monomial of its support. -/
@[expose] def IsMultilinear {R : Type*} [CommRing R] {n : ℕ} (f : FreeAlgebra R (Fin n)) : Prop :=
  ∀ w ∈ noncommSupport f, ∀ i : Fin n, w.toList.count i = 1

/-- Helper: lifting an algebra map on a monomial equals the list product of images. -/
theorem freeAlgebra_lift_monomial {R A X : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] (g : X → A) (w : FreeMonoid X) :
    FreeAlgebra.lift R g (FreeMonoid.lift (FreeAlgebra.ι R) w) = (w.toList.map g).prod := by
  have hhom :
      (FreeAlgebra.lift R g).toRingHom.toMonoidHom.comp
          (FreeMonoid.lift (FreeAlgebra.ι R : X → FreeAlgebra R X)) =
        FreeMonoid.lift g := by
    apply FreeMonoid.hom_eq
    intro x
    simp
  have h1 : FreeAlgebra.lift R g (FreeMonoid.lift (FreeAlgebra.ι R) w) = FreeMonoid.lift g w :=
    congrArg (fun h : FreeMonoid X →* A ↦ h w) hhom
  rw [h1]
  have hof : ∀ l : List X, FreeMonoid.lift g (FreeMonoid.ofList l) = (l.map g).prod := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      have hcons : FreeMonoid.ofList (x :: l) = FreeMonoid.of x * FreeMonoid.ofList l := rfl
      rw [hcons, map_mul, FreeMonoid.lift_eval_of, ih]
      simp
  simpa using hof w.toList

/-- Step 1 of multilinearization: eliminate any variable not occurring in every monomial by
substituting `0`, obtaining a nonzero identity in `m ≤ noncommDegree f` variables where every
variable occurs at least once in every monomial. -/
private theorem exists_all_vars_occur_identity {R : Type*} [CommRing R]
    (A : Type*) [Ring A] [Algebra R A] :
    ∀ {n : ℕ} {f : FreeAlgebra R (Fin n)},
      f ≠ 0 → IsPolyIdentity A f →
      ∃ (m : ℕ) (g : FreeAlgebra R (Fin m)),
        g ≠ 0 ∧ IsPolyIdentity A g ∧ noncommDegree g ≤ noncommDegree f ∧
        ∀ w ∈ noncommSupport g, ∀ i : Fin m, 1 ≤ w.toList.count i := by
  classical
  intro n
  induction n with
  | zero =>
    intro f hf hid
    exact ⟨0, f, hf, hid, le_rfl, fun _ _ i ↦ Fin.elim0 i⟩
  | succ n ih =>
    intro f hf hid
    by_cases hall : ∀ w ∈ noncommSupport f, ∀ i : Fin (n + 1), 1 ≤ w.toList.count i
    · exact ⟨n + 1, f, hf, hid, le_rfl, hall⟩
    · push Not at hall
      obtain ⟨w₀, hw₀, i₀, hi₀_lt⟩ := hall
      have hi₀_zero : w₀.toList.count i₀ = 0 := by omega
      -- Substitute `i₀ ↦ 0` and `i₀.succAbove j ↦ ι R j`
      let subst : FreeAlgebra R (Fin (n + 1)) →ₐ[R] FreeAlgebra R (Fin n) :=
        FreeAlgebra.lift R (fun i : Fin (n + 1) ↦
          if h : ∃ j : Fin n, i₀.succAbove j = i then
            FreeAlgebra.ι R (Classical.choose h)
          else 0)
      have hsubst_succAbove : ∀ j : Fin n,
          subst (FreeAlgebra.ι R (i₀.succAbove j)) = FreeAlgebra.ι R j := by
        intro j
        simp only [subst, FreeAlgebra.lift_ι_apply]
        have hex : ∃ j' : Fin n, i₀.succAbove j' = i₀.succAbove j := ⟨j, rfl⟩
        simp only [hex, ↓reduceDIte]
        congr 1
        exact Fin.succAbove_right_injective (Classical.choose_spec hex)
      let f' : FreeAlgebra R (Fin n) := subst f
      have hcoeff_f' : ∀ u : FreeMonoid (Fin n),
          FreeAlgebra.coeff u f' =
            FreeAlgebra.coeff (FreeMonoid.ofList (u.toList.map i₀.succAbove)) f := by
        intro u
        dsimp [f']
        conv_lhs => rw [freeAlgebra_eq_sum_support f]
        rw [map_sum, map_sum]
        have hmon_coeff : ∀ w : FreeMonoid (Fin (n + 1)),
            FreeAlgebra.coeff u (subst (FreeMonoid.lift (FreeAlgebra.ι R) w)) =
              if w = FreeMonoid.ofList (u.toList.map i₀.succAbove) then 1 else 0 := by
          intro w
          by_cases hmem : i₀ ∈ w.toList
          · have h0 : subst (FreeMonoid.lift (FreeAlgebra.ι R) w) = 0 := by
              rw [freeAlgebra_lift_monomial]
              obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hmem
              rw [hl, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
              have hz : (if h : ∃ j : Fin n, i₀.succAbove j = i₀ then
                  FreeAlgebra.ι R (Classical.choose h) else (0 : FreeAlgebra R (Fin n))) = 0 := by
                have hnot : ¬ ∃ j : Fin n, i₀.succAbove j = i₀ := fun ⟨j, hj⟩ ↦
                  Fin.succAbove_ne i₀ j hj
                simp only [hnot, ↓reduceDIte]
              simp only [hz, mul_zero, zero_mul]
            have hne : w ≠ FreeMonoid.ofList (u.toList.map i₀.succAbove) := by
              intro heq
              rw [heq] at hmem
              simp only [List.mem_map] at hmem
              obtain ⟨j, _, hj⟩ := hmem
              exact Fin.succAbove_ne i₀ j hj
            rw [h0, map_zero]
            simp only [hne, ↓reduceIte]
          · have hex_l : ∃ l : List (Fin n), w.toList = l.map i₀.succAbove := by
              generalize w.toList = wl at hmem
              induction wl with
              | nil => exact ⟨[], rfl⟩
              | cons x xs ihw =>
                have hx_ne : x ≠ i₀ := fun h ↦ hmem (h ▸ List.mem_cons_self ..)
                obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hx_ne
                obtain ⟨l, hl⟩ := ihw fun hm ↦ hmem (List.mem_cons_of_mem _ hm)
                exact ⟨j :: l, by simp [hl]⟩
            obtain ⟨l, hl⟩ := hex_l
            have hw_eq : w = FreeMonoid.ofList (l.map i₀.succAbove) := by
              simpa using congrArg FreeMonoid.ofList hl
            have hsub_w : subst (FreeMonoid.lift (FreeAlgebra.ι R) w) =
                FreeMonoid.lift (FreeAlgebra.ι R) (FreeMonoid.ofList l) := by
              rw [freeAlgebra_lift_monomial, hl, List.map_map]
              have hfun : (fun x : Fin (n + 1) ↦
                  if h : ∃ j : Fin n, i₀.succAbove j = x then
                    FreeAlgebra.ι R (Classical.choose h) else (0 : FreeAlgebra R (Fin n))) ∘
                  i₀.succAbove = FreeAlgebra.ι R := by
                funext j
                simp [Function.comp_apply]
              rw [hfun]
              have hof : ∀ xs : List (Fin n),
                  (xs.map (FreeAlgebra.ι R : Fin n → FreeAlgebra R (Fin n))).prod =
                    FreeMonoid.lift (FreeAlgebra.ι R) (FreeMonoid.ofList xs) := by
                intro xs
                induction xs with
                | nil => simp
                | cons a xs ihx =>
                  have hcons : FreeMonoid.ofList (a :: xs) =
                      FreeMonoid.of a * FreeMonoid.ofList xs := rfl
                  rw [hcons, map_mul, FreeMonoid.lift_eval_of, ← ihx]
                  simp
              exact hof l
            rw [hsub_w, FreeAlgebra.coeff_lift_ι, Finsupp.single_apply]
            have hiff : FreeMonoid.ofList l = u ↔
                w = FreeMonoid.ofList (u.toList.map i₀.succAbove) := by
              rw [hw_eq]
              constructor
              · rintro rfl; simp
              · intro h
                have hlist := congrArg FreeMonoid.toList h
                have hl_eq : l = u.toList := List.map_injective_iff.mpr
                  Fin.succAbove_right_injective hlist
                simpa using congrArg FreeMonoid.ofList hl_eq
            by_cases h : FreeMonoid.ofList l = u
            · simp [h, hiff.mp h]
            · simp [h, mt hiff.mpr h]
        simp only [map_smul, hmon_coeff, smul_eq_mul, mul_ite, mul_one, mul_zero]
        let w_u := FreeMonoid.ofList (u.toList.map i₀.succAbove)
        by_cases hwu : w_u ∈ noncommSupport f
        · rw [Finset.sum_eq_single w_u]
          · simp [w_u]
          · intro w _ hne; simp [w_u] at hne; simp [hne]
          · intro h; exact absurd hwu h
        · rw [Finset.sum_eq_zero]
          · exact (not_not.mp (mem_noncommSupport_iff.not.mp hwu)).symm
          · intro w hw
            have hne : w ≠ w_u := fun h ↦ hwu (h ▸ hw)
            simp [w_u] at hne
            simp [hne]
      have hf'_ne : f' ≠ 0 := by
        have hnot_mem : i₀ ∉ w₀.toList := by
          intro hm
          have := List.count_pos_iff.mpr hm
          omega
        have hex_l : ∃ l : List (Fin n), w₀.toList = l.map i₀.succAbove := by
          generalize w₀.toList = wl at hnot_mem
          induction wl with
          | nil => exact ⟨[], rfl⟩
          | cons x xs ihw =>
            have hx_ne : x ≠ i₀ := fun h ↦ hnot_mem (h ▸ List.mem_cons_self ..)
            obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hx_ne
            obtain ⟨l, hl⟩ := ihw fun hm ↦ hnot_mem (List.mem_cons_of_mem _ hm)
            exact ⟨j :: l, by simp [hl]⟩
        obtain ⟨l₀, hl₀⟩ := hex_l
        intro h0
        have hc := congrArg (FreeAlgebra.coeff (FreeMonoid.ofList l₀)) h0
        rw [hcoeff_f', map_zero] at hc
        have hw₀_eq : FreeMonoid.ofList ((FreeMonoid.ofList l₀).toList.map i₀.succAbove) = w₀ := by
          simp [← hl₀]
        rw [hw₀_eq] at hc
        exact (mem_noncommSupport_iff.mp hw₀) hc
      have hf'_id : IsPolyIdentity A f' := by
        intro y
        let x : Fin (n + 1) → A := fun i ↦
          if h : ∃ j : Fin n, i₀.succAbove j = i then y (Classical.choose h) else 0
        have hcomp : (FreeAlgebra.lift R y).comp subst = FreeAlgebra.lift R x := by
          apply FreeAlgebra.hom_ext
          funext i
          simp only [Function.comp_apply, AlgHom.comp_apply, subst, FreeAlgebra.lift_ι_apply, x]
          split_ifs with h
          · simp
          · simp
        change ((FreeAlgebra.lift R y).comp subst) f = 0
        rw [hcomp]
        exact hid x
      have hf'_deg : noncommDegree f' ≤ noncommDegree f := by
        rw [noncommDegree_le_iff]
        intro u hu
        have hc_ne : FreeAlgebra.coeff (FreeMonoid.ofList (u.toList.map i₀.succAbove)) f ≠ 0 := by
          rw [← hcoeff_f']
          exact mem_noncommSupport_iff.mp hu
        have hle := length_le_noncommDegree (mem_noncommSupport_iff.mpr hc_ne)
        simpa using hle
      obtain ⟨m, g, hg_ne, hg_id, hg_deg, hg_occ⟩ := ih hf'_ne hf'_id
      exact ⟨m, g, hg_ne, hg_id, hg_deg.trans hf'_deg, hg_occ⟩

/-- Helper for partial linearization: collapsing `Fin.last n ↦ i₀` on `Fin (n + 1) → Fin n`. -/
private def collapseVar {n : ℕ} (i₀ : Fin n) : Fin (n + 1) → Fin n :=
  Fin.lastCases i₀ id

private theorem collapseVar_castSucc {n : ℕ} (i₀ i : Fin n) :
    collapseVar i₀ i.castSucc = i := by
  simp [collapseVar]

private theorem collapseVar_last {n : ℕ} (i₀ : Fin n) :
    collapseVar i₀ (Fin.last n) = i₀ := by
  simp [collapseVar]

/-- Step 2 of multilinearization: partial linearization of `f` at a variable `i₀` occurring at
least twice in some monomial of `f`, producing a nonzero identity in `n + 1` variables with the
same or smaller degree where all `n + 1` variables occur in every monomial. -/
private theorem partial_linearize_step {R : Type*} [CommRing R]
    (A : Type*) [Ring A] [Algebra R A] {n : ℕ} {f : FreeAlgebra R (Fin n)}
    (hid : IsPolyIdentity A f)
    (hocc : ∀ w ∈ noncommSupport f, ∀ i : Fin n, 1 ≤ w.toList.count i)
    {w₀ : FreeMonoid (Fin n)} (hw₀ : w₀ ∈ noncommSupport f)
    {i₀ : Fin n} (hi₀ : 2 ≤ w₀.toList.count i₀) :
    ∃ g : FreeAlgebra R (Fin (n + 1)),
      g ≠ 0 ∧ IsPolyIdentity A g ∧ noncommDegree g ≤ noncommDegree f ∧
      ∀ u ∈ noncommSupport g, ∀ j : Fin (n + 1), 1 ≤ u.toList.count j := by
  classical
  let φ_sum : FreeAlgebra R (Fin n) →ₐ[R] FreeAlgebra R (Fin (n + 1)) :=
    FreeAlgebra.lift R fun i ↦
      if i = i₀ then FreeAlgebra.ι R i₀.castSucc + FreeAlgebra.ι R (Fin.last n)
      else FreeAlgebra.ι R i.castSucc
  let φ_left : FreeAlgebra R (Fin n) →ₐ[R] FreeAlgebra R (Fin (n + 1)) :=
    FreeAlgebra.lift R fun i ↦ FreeAlgebra.ι R i.castSucc
  let φ_right : FreeAlgebra R (Fin n) →ₐ[R] FreeAlgebra R (Fin (n + 1)) :=
    FreeAlgebra.lift R fun i ↦
      if i = i₀ then FreeAlgebra.ι R (Fin.last n) else FreeAlgebra.ι R i.castSucc
  let g : FreeAlgebra R (Fin (n + 1)) := φ_sum f - φ_left f - φ_right f
  -- Exact coefficient formula for each of the three maps on any monomial `w`
  have hcoeff_sum_mon : ∀ (w : FreeMonoid (Fin n)) (u : FreeMonoid (Fin (n + 1))),
      FreeAlgebra.coeff u (φ_sum (FreeMonoid.lift (FreeAlgebra.ι R) w)) =
        if u.toList.map (collapseVar i₀) = w.toList then 1 else 0 := by
    intro w u
    rw [freeAlgebra_lift_monomial]
    generalize w.toList = wl
    induction wl generalizing u with
    | nil =>
      simp only [List.map_nil, List.prod_nil]
      change FreeAlgebra.coeff u
          (FreeMonoid.lift (FreeAlgebra.ι R) (1 : FreeMonoid (Fin (n + 1)))) = _
      rw [FreeAlgebra.coeff_lift_ι, Finsupp.single_apply]
      by_cases hu : u = 1
      · subst hu; simp
      · have hne : u.toList ≠ [] := fun h ↦ hu (by simpa using congrArg FreeMonoid.ofList h)
        have hmap_ne : u.toList.map (collapseVar i₀) ≠ [] := by simp [hne]
        simp [Ne.symm hu, hmap_ne]
    | cons a wl ih =>
      simp only [List.map_cons, List.prod_cons]
      have hmul_ι : ∀ (j : Fin (n + 1)) (p : FreeAlgebra R (Fin (n + 1))),
          FreeAlgebra.coeff u (FreeAlgebra.ι R j * p) =
            match u.toList with
            | [] => 0
            | b :: bs => if b = j then FreeAlgebra.coeff (FreeMonoid.ofList bs) p else 0 := by
        intro j p
        conv_lhs => rw [freeAlgebra_eq_sum_support p]
        rw [Finset.mul_sum, map_sum]
        have hterm : ∀ v : FreeMonoid (Fin (n + 1)),
            FreeAlgebra.coeff u (FreeAlgebra.ι R j *
              (FreeAlgebra.coeff v p • FreeMonoid.lift (FreeAlgebra.ι R) v)) =
              if u = FreeMonoid.of j * v then FreeAlgebra.coeff v p else 0 := by
          intro v
          rw [mul_smul_comm, map_smul]
          have hprod : FreeAlgebra.ι R j * FreeMonoid.lift (FreeAlgebra.ι R) v =
              FreeMonoid.lift (FreeAlgebra.ι R) (FreeMonoid.of j * v) := by
            rw [map_mul, FreeMonoid.lift_eval_of]
          rw [hprod, FreeAlgebra.coeff_lift_ι, Finsupp.single_apply, smul_eq_mul, mul_ite,
            mul_one, mul_zero]
          by_cases h : FreeMonoid.of j * v = u
          · rw [h]
          · simp [h, Ne.symm h]
        simp_rw [hterm]
        cases hul : u.toList with
        | nil =>
          refine Finset.sum_eq_zero fun v _ ↦ ?_
          have hne : u ≠ FreeMonoid.of j * v := fun h ↦ by
            have hl := congrArg FreeMonoid.toList h
            rw [hul] at hl; simp at hl
          simp [hne]
        | cons b bs =>
          by_cases hbj : b = j
          · subst hbj
            have hu_eq : u = FreeMonoid.of b * FreeMonoid.ofList bs := by
              have : u.toList = (FreeMonoid.of b * FreeMonoid.ofList bs).toList := by simp [hul]
              simpa using congrArg FreeMonoid.ofList this
            simp only [↓reduceIte]
            by_cases hbs : FreeMonoid.ofList bs ∈ noncommSupport p
            · rw [Finset.sum_eq_single (FreeMonoid.ofList bs)]
              · simp [hu_eq]
              · intro v _ hne
                have hne' : u ≠ FreeMonoid.of b * v := fun h ↦ hne (by
                  rw [hu_eq] at h
                  have hl := congrArg FreeMonoid.toList h
                  simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append,
                    List.cons.injEq, true_and] at hl
                  simpa using congrArg FreeMonoid.ofList hl.symm)
                simp [hne']
              · intro h; exact absurd hbs h
            · rw [Finset.sum_eq_zero]
              · exact (not_not.mp (mem_noncommSupport_iff.not.mp hbs)).symm
              · intro v hv
                have hne' : u ≠ FreeMonoid.of b * v := fun h ↦ hbs (by
                  rw [hu_eq] at h
                  have hl := congrArg FreeMonoid.toList h
                  simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append,
                    List.cons.injEq, true_and] at hl
                  have hv_eq : FreeMonoid.ofList bs = v := by
                    simpa using congrArg FreeMonoid.ofList hl
                  rwa [hv_eq])
                simp [hne']
          · simp only [hbj, ↓reduceIte]
            refine Finset.sum_eq_zero fun v _ ↦ ?_
            have hne : u ≠ FreeMonoid.of j * v := fun h ↦ hbj (by
              have hl := congrArg FreeMonoid.toList h
              rw [hul] at hl
              simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append,
                List.cons.injEq] at hl
              exact hl.1)
            simp [hne]
      by_cases ha : a = i₀
      · subst ha
        simp only [↓reduceIte, add_mul, map_add, hmul_ι]
        cases hul : u.toList with
        | nil => simp
        | cons b bs =>
          dsimp only
          rw [ih (FreeMonoid.ofList bs), FreeMonoid.toList_ofList]
          by_cases hb1 : b = a.castSucc
          · subst hb1
            have hne : a.castSucc ≠ Fin.last n := Fin.castSucc_ne_last a
            simp [hne, collapseVar_castSucc]
          · by_cases hb2 : b = Fin.last n
            · subst hb2
              have hne : Fin.last n ≠ a.castSucc := (Fin.castSucc_ne_last a).symm
              simp [hne, collapseVar_last]
            · have hcol_ne : collapseVar a b ≠ a := by
                revert hb1 hb2
                refine Fin.lastCases (fun _ hb2 _ ↦ absurd rfl hb2) (fun j hb1 _ h ↦ ?_) b
                rw [collapseVar_castSucc] at h
                exact hb1 (congrArg Fin.castSucc h)
              simp [hb1, hb2, hcol_ne]
      · simp only [ha, ↓reduceIte, hmul_ι]
        cases hul : u.toList with
        | nil => simp
        | cons b bs =>
          dsimp only
          rw [ih (FreeMonoid.ofList bs), FreeMonoid.toList_ofList]
          by_cases hb : b = a.castSucc
          · subst hb
            simp [collapseVar_castSucc]
          · have hcol_ne : collapseVar i₀ b ≠ a := by
              revert hb
              refine Fin.lastCases ?_ ?_ b
              · intro _; rw [collapseVar_last]; exact Ne.symm ha
              · intro j hb h
                rw [collapseVar_castSucc] at h
                exact hb (congrArg Fin.castSucc h)
            simp [hb, hcol_ne]
  have hcoeff_left_mon : ∀ (w : FreeMonoid (Fin n)) (u : FreeMonoid (Fin (n + 1))),
      FreeAlgebra.coeff u (φ_left (FreeMonoid.lift (FreeAlgebra.ι R) w)) =
        if u = FreeMonoid.ofList (w.toList.map Fin.castSucc) then 1 else 0 := by
    intro w u
    have hmap : φ_left (FreeMonoid.lift (FreeAlgebra.ι R) w) =
        FreeMonoid.lift (FreeAlgebra.ι R) (FreeMonoid.ofList (w.toList.map Fin.castSucc)) := by
      rw [freeAlgebra_lift_monomial]
      have hof : ∀ l : List (Fin n),
          (l.map fun i ↦ (FreeAlgebra.ι R (i.castSucc) : FreeAlgebra R (Fin (n + 1)))).prod =
            FreeMonoid.lift (FreeAlgebra.ι R) (FreeMonoid.ofList (l.map Fin.castSucc)) := by
        intro l
        induction l with
        | nil => simp
        | cons x l ihl =>
          have hcons : FreeMonoid.ofList (x.castSucc :: l.map Fin.castSucc) =
              FreeMonoid.of x.castSucc * FreeMonoid.ofList (l.map Fin.castSucc) := rfl
          simp only [List.map_cons, List.prod_cons, hcons, map_mul, FreeMonoid.lift_eval_of, ← ihl]
      exact hof w.toList
    rw [hmap, FreeAlgebra.coeff_lift_ι, Finsupp.single_apply]
    by_cases h : FreeMonoid.ofList (w.toList.map Fin.castSucc) = u
    · rw [h]
    · simp [h, Ne.symm h]
  let rightVar : Fin n → Fin (n + 1) := fun i ↦ if i = i₀ then Fin.last n else i.castSucc
  have hcoeff_right_mon : ∀ (w : FreeMonoid (Fin n)) (u : FreeMonoid (Fin (n + 1))),
      FreeAlgebra.coeff u (φ_right (FreeMonoid.lift (FreeAlgebra.ι R) w)) =
        if u = FreeMonoid.ofList (w.toList.map rightVar) then 1 else 0 := by
    intro w u
    have hmap : φ_right (FreeMonoid.lift (FreeAlgebra.ι R) w) =
        FreeMonoid.lift (FreeAlgebra.ι R) (FreeMonoid.ofList (w.toList.map rightVar)) := by
      rw [freeAlgebra_lift_monomial]
      have hof : ∀ l : List (Fin n),
          (l.map fun i ↦ (if i = i₀ then FreeAlgebra.ι R (Fin.last n)
              else FreeAlgebra.ι R i.castSucc : FreeAlgebra R (Fin (n + 1)))).prod =
            FreeMonoid.lift (FreeAlgebra.ι R) (FreeMonoid.ofList (l.map rightVar)) := by
        intro l
        induction l with
        | nil => simp
        | cons x l ihl =>
          have hcons : FreeMonoid.ofList (rightVar x :: l.map rightVar) =
              FreeMonoid.of (rightVar x) * FreeMonoid.ofList (l.map rightVar) := rfl
          simp only [List.map_cons, List.prod_cons, hcons, map_mul, FreeMonoid.lift_eval_of, ← ihl]
          by_cases hx : x = i₀ <;> simp [rightVar, hx]
      exact hof w.toList
    rw [hmap, FreeAlgebra.coeff_lift_ι, Finsupp.single_apply]
    by_cases h : FreeMonoid.ofList (w.toList.map rightVar) = u
    · rw [h]
    · simp [h, Ne.symm h]
  -- Combine to get exact coefficient of `u` in `g`!
  have hcoeff_g : ∀ u : FreeMonoid (Fin (n + 1)),
      FreeAlgebra.coeff u g =
        if 1 ≤ u.toList.count i₀.castSucc ∧ 1 ≤ u.toList.count (Fin.last n) then
          FreeAlgebra.coeff (FreeMonoid.ofList (u.toList.map (collapseVar i₀))) f
        else 0 := by
    intro u
    let wu : FreeMonoid (Fin n) := FreeMonoid.ofList (u.toList.map (collapseVar i₀))
    have hsum_val : FreeAlgebra.coeff u (φ_sum f) = FreeAlgebra.coeff wu f := by
      conv_lhs => rw [freeAlgebra_eq_sum_support f]
      rw [map_sum, map_sum]
      simp only [map_smul, hcoeff_sum_mon, smul_eq_mul, mul_ite, mul_one, mul_zero]
      have hiff : ∀ w : FreeMonoid (Fin n), u.toList.map (collapseVar i₀) = w.toList ↔ w = wu := by
        intro w
        constructor
        · intro h
          have := congrArg FreeMonoid.ofList h
          simpa [wu] using this.symm
        · rintro rfl; simp [wu]
      simp_rw [hiff]
      by_cases hmem : wu ∈ noncommSupport f
      · rw [Finset.sum_eq_single wu]
        · simp
        · intro w _ hne; simp [hne]
        · intro h; exact absurd hmem h
      · rw [Finset.sum_eq_zero]
        · exact (not_not.mp (mem_noncommSupport_iff.not.mp hmem)).symm
        · intro w hw
          have hne : w ≠ wu := fun h ↦ hmem (h ▸ hw)
          simp [hne]
    have hleft_val : FreeAlgebra.coeff u (φ_left f) =
        if u.toList.count (Fin.last n) = 0 then FreeAlgebra.coeff wu f else 0 := by
      conv_lhs => rw [freeAlgebra_eq_sum_support f]
      rw [map_sum, map_sum]
      simp only [map_smul, hcoeff_left_mon, smul_eq_mul, mul_ite, mul_one, mul_zero]
      have hiff : ∀ w : FreeMonoid (Fin n),
          u = FreeMonoid.ofList (w.toList.map Fin.castSucc) ↔
            u.toList.count (Fin.last n) = 0 ∧ w = wu := by
        intro w
        constructor
        · intro h
          have hl := congrArg FreeMonoid.toList h
          refine ⟨?_, ?_⟩
          · rw [List.count_eq_zero, hl, List.mem_map]
            rintro ⟨j, _, hj⟩
            exact Fin.castSucc_ne_last j hj
          · apply congrArg FreeMonoid.ofList
            rw [hl, List.map_map]
            have hcomp : collapseVar i₀ ∘ Fin.castSucc = id := funext (collapseVar_castSucc i₀)
            simp [hcomp]
        · rintro ⟨hcnt, rfl⟩
          have hnot : Fin.last n ∉ u.toList := List.count_eq_zero.mp hcnt
          apply congrArg FreeMonoid.ofList
          simp only [wu, List.map_map]
          conv_lhs => rw [← List.map_id u.toList]
          refine List.map_congr_left fun b hb ↦ ?_
          revert hb
          refine Fin.lastCases (fun hb ↦ absurd hb hnot) (fun j _ ↦ ?_) b
          simp [collapseVar_castSucc]
      by_cases hcnt : u.toList.count (Fin.last n) = 0
      · simp only [hcnt, true_and, ↓reduceIte] at hiff ⊢
        simp_rw [hiff]
        by_cases hmem : wu ∈ noncommSupport f
        · rw [Finset.sum_eq_single wu]
          · simp
          · intro w _ hne; simp [hne]
          · intro h; exact absurd hmem h
        · rw [Finset.sum_eq_zero]
          · exact (not_not.mp (mem_noncommSupport_iff.not.mp hmem)).symm
          · intro w hw; have hne : w ≠ wu := fun h ↦ hmem (h ▸ hw); simp [hne]
      · simp only [hcnt, false_and, ↓reduceIte] at hiff ⊢
        simp_rw [hiff]
        simp
    have hright_val : FreeAlgebra.coeff u (φ_right f) =
        if u.toList.count i₀.castSucc = 0 then FreeAlgebra.coeff wu f else 0 := by
      conv_lhs => rw [freeAlgebra_eq_sum_support f]
      rw [map_sum, map_sum]
      simp only [map_smul, hcoeff_right_mon, smul_eq_mul, mul_ite, mul_one, mul_zero]
      have hiff : ∀ w : FreeMonoid (Fin n),
          u = FreeMonoid.ofList (w.toList.map rightVar) ↔
            u.toList.count i₀.castSucc = 0 ∧ w = wu := by
        intro w
        constructor
        · intro h
          have hl := congrArg FreeMonoid.toList h
          refine ⟨?_, ?_⟩
          · rw [List.count_eq_zero, hl, List.mem_map]
            rintro ⟨j, _, hj⟩
            by_cases hji : j = i₀
            · simp [rightVar, hji] at hj
              exact Fin.castSucc_ne_last i₀ hj.symm
            · simp [rightVar, hji] at hj
          · apply congrArg FreeMonoid.ofList
            rw [hl, List.map_map]
            have hcomp : collapseVar i₀ ∘ rightVar = id := by
              funext j
              by_cases hj : j = i₀
              · subst hj; simp [rightVar, collapseVar_last]
              · simp [rightVar, hj, collapseVar_castSucc]
            simp [hcomp]
        · rintro ⟨hcnt, rfl⟩
          have hnot : i₀.castSucc ∉ u.toList := List.count_eq_zero.mp hcnt
          apply congrArg FreeMonoid.ofList
          simp only [wu, List.map_map]
          conv_lhs => rw [← List.map_id u.toList]
          refine List.map_congr_left fun b hb ↦ ?_
          revert hb
          refine Fin.lastCases ?_ (fun j hb ↦ ?_) b
          · intro _; simp [collapseVar_last, rightVar]
          · have hjne : j ≠ i₀ := fun h ↦ hnot (h ▸ hb)
            simp [collapseVar_castSucc, rightVar, hjne]
      by_cases hcnt : u.toList.count i₀.castSucc = 0
      · simp only [hcnt, true_and, ↓reduceIte] at hiff ⊢
        simp_rw [hiff]
        by_cases hmem : wu ∈ noncommSupport f
        · rw [Finset.sum_eq_single wu]
          · simp
          · intro w _ hne; simp [hne]
          · intro h; exact absurd hmem h
        · rw [Finset.sum_eq_zero]
          · exact (not_not.mp (mem_noncommSupport_iff.not.mp hmem)).symm
          · intro w hw; have hne : w ≠ wu := fun h ↦ hmem (h ▸ hw); simp [hne]
      · simp only [hcnt, false_and, ↓reduceIte] at hiff ⊢
        simp_rw [hiff]
        simp
    dsimp only [g]
    rw [map_sub, map_sub, hsum_val, hleft_val, hright_val]
    by_cases hc1 : u.toList.count i₀.castSucc = 0
    · by_cases hc2 : u.toList.count (Fin.last n) = 0
      · -- Both counts are 0, so `i₀` has count 0 in `wu`, hence `wu ∉ noncommSupport f`!
        have hwu_cnt0 : wu.toList.count i₀ = 0 := by
          rw [List.count_eq_zero]
          simp only [wu, List.mem_map]
          rintro ⟨b, hb, hcol⟩
          revert hb hcol
          refine Fin.lastCases (fun hb _ ↦ List.count_eq_zero.mp hc2 hb) (fun j hb h ↦ ?_) b
          rw [collapseVar_castSucc] at h
          subst h
          exact List.count_eq_zero.mp hc1 hb
        have hwu_not : wu ∉ noncommSupport f := fun hm ↦ by
          have := hocc wu hm i₀; omega
        have hfwu : FreeAlgebra.coeff wu f = 0 :=
          not_not.mp (mem_noncommSupport_iff.not.mp hwu_not)
        simp [hc1, hc2, hfwu]
      · simp [hc1, hc2]
    · by_cases hc2 : u.toList.count (Fin.last n) = 0
      · simp [hc1, hc2]
      · have h1 : 1 ≤ u.toList.count i₀.castSucc := by omega
        have h2 : 1 ≤ u.toList.count (Fin.last n) := by omega
        simp [hc1, hc2, h1, h2, wu]
  -- Construct witness `u₀` by replacing the first occurrence of `i₀` in `w₀` by `Fin.last n`
  have hex_u₀ : ∃ u₀ : FreeMonoid (Fin (n + 1)),
      u₀.toList.map (collapseVar i₀) = w₀.toList ∧
      1 ≤ u₀.toList.count i₀.castSucc ∧ 1 ≤ u₀.toList.count (Fin.last n) := by
    have hmem : i₀ ∈ w₀.toList := List.count_pos_iff.mp (by omega)
    obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hmem
    let u₀ : FreeMonoid (Fin (n + 1)) :=
      FreeMonoid.ofList (l₁.map Fin.castSucc ++ Fin.last n :: l₂.map Fin.castSucc)
    refine ⟨u₀, ?_, ?_, ?_⟩
    · simp only [u₀, List.map_append, List.map_cons, List.map_map,
        collapseVar_last, hl]
      have hcomp : collapseVar i₀ ∘ Fin.castSucc = id := funext (collapseVar_castSucc i₀)
      simp [hcomp]
    · have hcnt_tot : l₁.count i₀ + l₂.count i₀ + 1 = w₀.toList.count i₀ := by
        rw [hl, List.count_append, List.count_cons_self]
        omega
      have hmap_cnt : ∀ l : List (Fin n), (l.map Fin.castSucc).count i₀.castSucc = l.count i₀ := by
        intro l
        induction l with
        | nil => simp
        | cons x l ihl =>
          simp only [List.map_cons, List.count_cons, ihl, beq_iff_eq,
            (Fin.castSucc_injective n).eq_iff]
      have hne : Fin.last n ≠ i₀.castSucc := (Fin.castSucc_ne_last i₀).symm
      simp only [u₀, List.count_append, List.count_cons, hmap_cnt,
        beq_eq_false_iff_ne.mpr hne]
      omega
    · simp only [u₀, List.count_append, List.count_cons_self]
      omega
  obtain ⟨u₀, hu₀_col, hu₀_c1, hu₀_c2⟩ := hex_u₀
  have hg_ne : g ≠ 0 := by
    intro h0
    have hc := congrArg (FreeAlgebra.coeff u₀) h0
    rw [hcoeff_g, map_zero] at hc
    simp only [hu₀_c1, hu₀_c2, and_self, ↓reduceIte] at hc
    have hw₀_eq : FreeMonoid.ofList (u₀.toList.map (collapseVar i₀)) = w₀ := by
      rw [hu₀_col]
    rw [hw₀_eq] at hc
    exact (mem_noncommSupport_iff.mp hw₀) hc
  have hg_id : IsPolyIdentity A g := by
    intro y
    have h1 : FreeAlgebra.lift R y (φ_sum f) = 0 := by
      let x : Fin n → A := fun i ↦ if i = i₀ then y i₀.castSucc + y (Fin.last n) else y i.castSucc
      have hcomp : (FreeAlgebra.lift R y).comp φ_sum = FreeAlgebra.lift R x := by
        apply FreeAlgebra.hom_ext; funext i
        simp only [Function.comp_apply, AlgHom.comp_apply, φ_sum, FreeAlgebra.lift_ι_apply, x]
        split_ifs <;> simp
      change ((FreeAlgebra.lift R y).comp φ_sum) f = 0
      rw [hcomp]; exact hid x
    have h2 : FreeAlgebra.lift R y (φ_left f) = 0 := by
      let x : Fin n → A := fun i ↦ y i.castSucc
      have hcomp : (FreeAlgebra.lift R y).comp φ_left = FreeAlgebra.lift R x := by
        apply FreeAlgebra.hom_ext; funext i; simp [φ_left, x]
      change ((FreeAlgebra.lift R y).comp φ_left) f = 0
      rw [hcomp]; exact hid x
    have h3 : FreeAlgebra.lift R y (φ_right f) = 0 := by
      let x : Fin n → A := fun i ↦ if i = i₀ then y (Fin.last n) else y i.castSucc
      have hcomp : (FreeAlgebra.lift R y).comp φ_right = FreeAlgebra.lift R x := by
        apply FreeAlgebra.hom_ext; funext i
        simp only [Function.comp_apply, AlgHom.comp_apply, φ_right, FreeAlgebra.lift_ι_apply, x]
        split_ifs <;> simp
      change ((FreeAlgebra.lift R y).comp φ_right) f = 0
      rw [hcomp]; exact hid x
    dsimp only [g]
    rw [map_sub, map_sub, h1, h2, h3, sub_zero, sub_zero]
  have hg_deg : noncommDegree g ≤ noncommDegree f := by
    rw [noncommDegree_le_iff]
    intro u hu
    have hc_ne : FreeAlgebra.coeff u g ≠ 0 := mem_noncommSupport_iff.mp hu
    rw [hcoeff_g] at hc_ne
    split_ifs at hc_ne with hcond
    · have hle := length_le_noncommDegree (mem_noncommSupport_iff.mpr hc_ne)
      simpa using hle
    · exact absurd rfl hc_ne
  have hg_occ : ∀ u ∈ noncommSupport g, ∀ j : Fin (n + 1), 1 ≤ u.toList.count j := by
    intro u hu j
    have hc_ne : FreeAlgebra.coeff u g ≠ 0 := mem_noncommSupport_iff.mp hu
    rw [hcoeff_g] at hc_ne
    split_ifs at hc_ne with hcond
    · refine Fin.lastCases hcond.2 (fun i ↦ ?_) j
      by_cases hi : i = i₀
      · subst hi; exact hcond.1
      · have hwu_occ := hocc _ (mem_noncommSupport_iff.mpr hc_ne) i
        have hcnt_eq : (u.toList.map (collapseVar i₀)).count i = u.toList.count i.castSucc := by
          generalize u.toList = ul
          induction ul with
          | nil => simp
          | cons b bs ihb =>
            simp only [List.map_cons, List.count_cons, ihb, beq_iff_eq]
            have hiff : collapseVar i₀ b = i ↔ b = i.castSucc := by
              refine Fin.lastCases ?_ ?_ b
              · simp [collapseVar_last, Ne.symm hi, (Fin.castSucc_ne_last i).symm]
              · intro k
                simp [collapseVar_castSucc, (Fin.castSucc_injective n).eq_iff]
            by_cases hb : b = i.castSucc
            · simp [hb, collapseVar_castSucc]
            · simp [hb, mt hiff.mp hb]
        simpa [hcnt_eq] using hwu_occ
    · exact absurd rfl hc_ne
  exact ⟨g, hg_ne, hg_id, hg_deg, hg_occ⟩

/-- Characteristic-free partial multilinearization over any commutative ring $R$:
if an $R$-algebra $A$ satisfies a nonzero polynomial identity of degree at most $k$, then it
satisfies a nonzero multilinear identity of degree $m \le k$. -/
theorem exists_multilinear_identity_le {R : Type*} [CommRing R]
    (A : Type*) [Ring A] [Algebra R A] {n k : ℕ} {f : FreeAlgebra R (Fin n)}
    (hf : f ≠ 0) (hid : IsPolyIdentity A f) (hdeg : noncommDegree f ≤ k) :
    ∃ (m : ℕ) (g : FreeAlgebra R (Fin m)),
      m ≤ k ∧ g ≠ 0 ∧ IsMultilinear g ∧ IsPolyIdentity A g := by
  obtain ⟨m₀, g₀, hg₀_ne, hg₀_id, hg₀_deg, hg₀_occ⟩ :=
    exists_all_vars_occur_identity A hf hid
  have hg₀_k : noncommDegree g₀ ≤ k := hg₀_deg.trans hdeg
  -- Induct on `rem = k - m`
  have hstep : ∀ rem m (g : FreeAlgebra R (Fin m)),
      k - m ≤ rem → g ≠ 0 → IsPolyIdentity A g → noncommDegree g ≤ k →
      (∀ w ∈ noncommSupport g, ∀ i : Fin m, 1 ≤ w.toList.count i) →
      ∃ (m' : ℕ) (g' : FreeAlgebra R (Fin m')),
        m' ≤ k ∧ g' ≠ 0 ∧ IsMultilinear g' ∧ IsPolyIdentity A g' := by
    intro rem
    induction rem with
    | zero =>
      intro m g hrem hg_ne hg_id hg_k hg_occ
      have hsupp_ne : (noncommSupport g).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr fun he ↦ hg_ne (noncommSupport_eq_empty_iff.mp he)
      obtain ⟨w₀, hw₀⟩ := hsupp_ne
      have hm_le_len : ∀ w ∈ noncommSupport g, m ≤ w.toList.length := by
        intro w hw
        calc
          m = ∑ _i : Fin m, 1 := by simp
          _ ≤ ∑ i : Fin m, w.toList.count i := Finset.sum_le_sum fun i _ ↦ hg_occ w hw i
          _ = w.toList.length := by
              clear hg_occ hg_k hg_id hg_ne hw hw₀ w₀ hrem
              induction w.toList with
              | nil => simp
              | cons a l ihl =>
                simp only [List.count_cons, List.length_cons, Finset.sum_add_distrib, ihl]
                have h1 : ∑ i : Fin m, (if a == i then 1 else 0) = 1 := by
                  rw [Finset.sum_eq_single a]
                  · simp
                  · intro i _ hia; simp [Ne.symm hia]
                  · intro h; exact absurd (Finset.mem_univ a) h
                omega
      have hm_le_k : m ≤ k := (hm_le_len w₀ hw₀).trans ((length_le_noncommDegree hw₀).trans hg_k)
      have hm_eq_k : m = k := by omega
      refine ⟨m, g, hm_le_k, hg_ne, ?_, hg_id⟩
      intro w hw i
      have hsum : ∑ j : Fin m, w.toList.count j = w.toList.length := by
        clear hg_occ hg_k hg_id hg_ne hw hw₀ w₀ hrem hm_le_len hm_le_k hm_eq_k
        induction w.toList with
        | nil => simp
        | cons a l ihl =>
          simp only [List.count_cons, List.length_cons, Finset.sum_add_distrib, ihl]
          have h1 : ∑ j : Fin m, (if a == j then 1 else 0) = 1 := by
            rw [Finset.sum_eq_single a]
            · simp
            · intro j _ hja; simp [Ne.symm hja]
            · intro h; exact absurd (Finset.mem_univ a) h
          omega
      have hlen_le : w.toList.length ≤ m := by
        have := (length_le_noncommDegree hw).trans hg_k
        omega
      have hge := hg_occ w hw i
      by_contra hne1
      have hge2 : 2 ≤ w.toList.count i := by omega
      have hsum_gt : m < ∑ j : Fin m, w.toList.count j := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        have hrest : m - 1 ≤ ∑ j ∈ Finset.univ.erase i, w.toList.count j := by
          calc
            m - 1 = (Finset.univ.erase i).card := by simp
            _ = ∑ _j ∈ Finset.univ.erase i, 1 := by simp
            _ ≤ ∑ j ∈ Finset.univ.erase i, w.toList.count j :=
                Finset.sum_le_sum fun j _ ↦ hg_occ w hw j
        have hm_pos : 1 ≤ m := by
          have := i.isLt; omega
        omega
      omega
    | succ rem ih =>
      intro m g hrem hg_ne hg_id hg_k hg_occ
      have hsupp_ne : (noncommSupport g).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr fun he ↦ hg_ne (noncommSupport_eq_empty_iff.mp he)
      obtain ⟨w₀, hw₀⟩ := hsupp_ne
      have hm_le_len : ∀ w ∈ noncommSupport g, m ≤ w.toList.length := by
        intro w hw
        calc
          m = ∑ _i : Fin m, 1 := by simp
          _ ≤ ∑ i : Fin m, w.toList.count i := Finset.sum_le_sum fun i _ ↦ hg_occ w hw i
          _ = w.toList.length := by
              clear hg_occ hg_k hg_id hg_ne hw hw₀ w₀ hrem
              induction w.toList with
              | nil => simp
              | cons a l ihl =>
                simp only [List.count_cons, List.length_cons, Finset.sum_add_distrib, ihl]
                have h1 : ∑ i : Fin m, (if a == i then 1 else 0) = 1 := by
                  rw [Finset.sum_eq_single a]
                  · simp
                  · intro i _ hia; simp [Ne.symm hia]
                  · intro h; exact absurd (Finset.mem_univ a) h
                omega
      have hm_le_k : m ≤ k := (hm_le_len w₀ hw₀).trans ((length_le_noncommDegree hw₀).trans hg_k)
      by_cases hml : IsMultilinear g
      · exact ⟨m, g, hm_le_k, hg_ne, hml, hg_id⟩
      · unfold IsMultilinear at hml
        push Not at hml
        obtain ⟨w₁, hw₁, i₁, hi₁_ne⟩ := hml
        have hi₁_ge2 : 2 ≤ w₁.toList.count i₁ := by
          have := hg_occ w₁ hw₁ i₁; omega
        obtain ⟨g', hg'_ne, hg'_id, hg'_deg, hg'_occ⟩ :=
          partial_linearize_step A hg_id hg_occ hw₁ hi₁_ge2
        exact ih (m + 1) g' (by omega) hg'_ne hg'_id (hg'_deg.trans hg_k) hg'_occ
  exact hstep (k - m₀) m₀ g₀ le_rfl hg₀_ne hg₀_id hg₀_k hg₀_occ

/-- if an $R$-algebra $A$ satisfies a
nonzero polynomial identity of degree at most $k$, then it satisfies a nonzero multilinear identity
of exact degree $k$ (obtained by right-multiplying by $k - m$ fresh variables). -/
theorem exists_multilinear_identity_exact {R : Type*} [CommRing R]
    (A : Type*) [Ring A] [Algebra R A] {n k : ℕ} {f : FreeAlgebra R (Fin n)}
    (hf : f ≠ 0) (hid : IsPolyIdentity A f) (hdeg : noncommDegree f ≤ k) :
    ∃ g : FreeAlgebra R (Fin k),
      g ≠ 0 ∧ IsMultilinear g ∧ IsPolyIdentity A g := by
  classical
  obtain ⟨m, h, hmk, hh_ne, hh_ml, hh_id⟩ := exists_multilinear_identity_le A hf hid hdeg
  -- Embed `Fin m` into `Fin k` via `Fin.castLE hmk` and right-multiply by `ι m * … * ι (k - 1)`
  let emb : FreeAlgebra R (Fin m) →ₐ[R] FreeAlgebra R (Fin k) :=
    FreeAlgebra.lift R fun i : Fin m ↦ FreeAlgebra.ι R (Fin.castLE hmk i)
  let tailList : List (Fin k) :=
    (List.finRange (k - m)).map fun j ↦ ⟨m + j.val, by omega⟩
  let tailMon : FreeMonoid (Fin k) := FreeMonoid.ofList tailList
  let g : FreeAlgebra R (Fin k) := emb h * FreeMonoid.lift (FreeAlgebra.ι R) tailMon
  have hcoeff_g : ∀ u : FreeMonoid (Fin k),
      FreeAlgebra.coeff u g =
        if hsplit : ∃ w : FreeMonoid (Fin m),
            u = FreeMonoid.ofList (w.toList.map (Fin.castLE hmk)) * tailMon then
          FreeAlgebra.coeff (Classical.choose hsplit) h
        else 0 := by
    intro u
    dsimp only [g]
    conv_lhs => rw [freeAlgebra_eq_sum_support h]
    rw [map_sum, Finset.sum_mul, map_sum]
    have hterm : ∀ w : FreeMonoid (Fin m),
        FreeAlgebra.coeff u (emb (FreeAlgebra.coeff w h • FreeMonoid.lift (FreeAlgebra.ι R) w) *
          FreeMonoid.lift (FreeAlgebra.ι R) tailMon) =
          if u = FreeMonoid.ofList (w.toList.map (Fin.castLE hmk)) * tailMon then
            FreeAlgebra.coeff w h else 0 := by
      intro w
      rw [map_smul, smul_mul_assoc, map_smul]
      have hemb_w : emb (FreeMonoid.lift (FreeAlgebra.ι R) w) =
          FreeMonoid.lift (FreeAlgebra.ι R)
            (FreeMonoid.ofList (w.toList.map (Fin.castLE hmk))) := by
        rw [freeAlgebra_lift_monomial]
        have hof : ∀ l : List (Fin m),
            (l.map fun i ↦ (FreeAlgebra.ι R (Fin.castLE hmk i) : FreeAlgebra R (Fin k))).prod =
              FreeMonoid.lift (FreeAlgebra.ι R) (FreeMonoid.ofList (l.map (Fin.castLE hmk))) := by
          intro l
          induction l with
          | nil => simp
          | cons x l ihl =>
            have hcons : FreeMonoid.ofList (Fin.castLE hmk x :: l.map (Fin.castLE hmk)) =
                FreeMonoid.of (Fin.castLE hmk x) * FreeMonoid.ofList (l.map (Fin.castLE hmk)) := rfl
            simp only [List.map_cons, List.prod_cons, hcons, map_mul,
              FreeMonoid.lift_eval_of, ← ihl]
        exact hof w.toList
      rw [hemb_w, ← map_mul, FreeAlgebra.coeff_lift_ι, Finsupp.single_apply, smul_eq_mul,
        mul_ite, mul_one, mul_zero]
      by_cases heq : FreeMonoid.ofList (w.toList.map (Fin.castLE hmk)) * tailMon = u
      · rw [heq]
      · simp [heq, Ne.symm heq]
    simp_rw [hterm]
    split_ifs with hsplit
    · let w₁ := Classical.choose hsplit
      have hw₁ : u = FreeMonoid.ofList (w₁.toList.map (Fin.castLE hmk)) * tailMon :=
        Classical.choose_spec hsplit
      have hinj : ∀ w : FreeMonoid (Fin m),
          u = FreeMonoid.ofList (w.toList.map (Fin.castLE hmk)) * tailMon → w = w₁ := by
        intro w hw
        rw [hw₁] at hw
        have hl := congrArg FreeMonoid.toList hw
        simp only [FreeMonoid.toList_mul, List.append_cancel_right_eq] at hl
        have hleq : w₁.toList = w.toList :=
          List.map_injective_iff.mpr (Fin.castLE_injective hmk) hl
        simpa using congrArg FreeMonoid.ofList hleq.symm
      by_cases hmem : w₁ ∈ noncommSupport h
      · rw [Finset.sum_eq_single w₁]
        · exact ite_eq_left hw₁
        · intro w _ hne
          have : ¬ u = FreeMonoid.ofList (w.toList.map (Fin.castLE hmk)) * tailMon :=
            fun he ↦ hne (hinj w he)
          simp [this]
        · intro hnot; exact absurd hmem hnot
      · rw [Finset.sum_eq_zero]
        · exact (not_not.mp (mem_noncommSupport_iff.not.mp hmem)).symm
        · intro w hw
          have : ¬ u = FreeMonoid.ofList (w.toList.map (Fin.castLE hmk)) * tailMon :=
            fun he ↦ hmem (hinj w he ▸ hw)
          simp [this]
    · refine Finset.sum_eq_zero fun w _ ↦ ?_
      have : ¬ u = FreeMonoid.ofList (w.toList.map (Fin.castLE hmk)) * tailMon :=
        fun he ↦ hsplit ⟨w, he⟩
      simp [this]
  have hg_ne : g ≠ 0 := by
    obtain ⟨w₀, hw₀⟩ := FreeAlgebra.exists_coeff_ne_zero hh_ne
    let u₀ : FreeMonoid (Fin k) := FreeMonoid.ofList (w₀.toList.map (Fin.castLE hmk)) * tailMon
    intro h0
    have hc := congrArg (FreeAlgebra.coeff u₀) h0
    rw [hcoeff_g, map_zero] at hc
    have hsplit : ∃ w : FreeMonoid (Fin m),
        u₀ = FreeMonoid.ofList (w.toList.map (Fin.castLE hmk)) * tailMon := ⟨w₀, rfl⟩
    simp only [hsplit, ↓reduceDIte] at hc
    have hch : Classical.choose hsplit = w₀ := by
      have hl := congrArg FreeMonoid.toList (Classical.choose_spec hsplit)
      simp only [u₀, FreeMonoid.toList_mul, List.append_cancel_right_eq] at hl
      have hleq : (Classical.choose hsplit).toList = w₀.toList :=
        List.map_injective_iff.mpr (Fin.castLE_injective hmk) hl.symm
      exact (FreeMonoid.ofList_toList _).symm.trans
        ((congrArg FreeMonoid.ofList hleq).trans (FreeMonoid.ofList_toList _))
    rw [hch] at hc
    exact hw₀ hc
  have hg_ml : IsMultilinear g := by
    intro u hu j
    have hc := mem_noncommSupport_iff.mp hu
    rw [hcoeff_g] at hc
    split_ifs at hc with hsplit
    · let w := Classical.choose hsplit
      have hw_eq := Classical.choose_spec hsplit
      have hw_supp : w ∈ noncommSupport h := mem_noncommSupport_iff.mpr hc
      rw [hw_eq, FreeMonoid.toList_mul, FreeMonoid.toList_ofList, FreeMonoid.toList_ofList,
        List.count_append]
      by_cases hj : j.val < m
      · let jm : Fin m := ⟨j.val, hj⟩
        have hjm : Fin.castLE hmk jm = j := Fin.ext rfl
        have hleft : (w.toList.map (Fin.castLE hmk)).count j = w.toList.count jm := by
          rw [← hjm]
          generalize w.toList = wl
          induction wl with
          | nil => simp
          | cons x xs ihx =>
            simp only [List.map_cons, List.count_cons, ihx, beq_iff_eq,
              (Fin.castLE_injective hmk).eq_iff]
        have hright : tailList.count j = 0 := by
          rw [List.count_eq_zero, List.mem_map]
          rintro ⟨t, _, ht⟩
          have hv := congrArg Fin.val ht
          dsimp at hv; omega
        rw [hleft, hright, add_zero]
        exact hh_ml w hw_supp jm
      · have hleft : (w.toList.map (Fin.castLE hmk)).count j = 0 := by
          rw [List.count_eq_zero, List.mem_map]
          rintro ⟨t, _, ht⟩
          have hv := congrArg Fin.val ht
          dsimp at hv; omega
        have hright : tailList.count j = 1 := by
          let jt : Fin (k - m) := ⟨j.val - m, by omega⟩
          have hjt : (⟨m + jt.val, by omega⟩ : Fin k) = j := Fin.ext (by dsimp [jt]; omega)
          have hnodup : tailList.Nodup := by
            refine List.Nodup.map ?_ (List.nodup_finRange (k - m))
            intro a b hab
            have hv := congrArg Fin.val hab; dsimp at hv
            exact Fin.ext (by omega)
          have hmem : j ∈ tailList := List.mem_map.mpr ⟨jt, List.mem_finRange jt, hjt⟩
          exact (hnodup.count (a := j)).trans (by simp [hmem])
        rw [hleft, hright, zero_add]
    · exact absurd rfl hc
  have hg_id : IsPolyIdentity A g := by
    intro y
    dsimp only [g]
    rw [map_mul]
    have h1 : FreeAlgebra.lift R y (emb h) = 0 := by
      have hcomp : (FreeAlgebra.lift R y).comp emb =
          FreeAlgebra.lift R (fun i : Fin m ↦ y (Fin.castLE hmk i)) := by
        apply FreeAlgebra.hom_ext; funext i; simp [emb]
      change ((FreeAlgebra.lift R y).comp emb) h = 0
      rw [hcomp]
      exact hh_id _
    rw [h1, zero_mul]
  exact ⟨g, hg_ne, hg_ml, hg_id⟩


/-- The `j`-th staircase matrix unit:
$e_{0,0}, e_{0,1}, e_{1,1}, e_{1,2}, \dots, e_{k-2,k-1}, e_{k-1,k-1} \in M_k(R)$. -/
def staircaseMatrix {R : Type*} [Semiring R] (k : ℕ)
    (j : Fin (2 * k - 1)) : Matrix (Fin k) (Fin k) R :=
  Matrix.of fun r s ↦
    if r.val = j.val / 2 ∧ s.val = (j.val + 1) / 2 then 1 else 0

private theorem matrix_unit_mul {R : Type*} [Semiring R] {k : ℕ}
    (a b c d : Fin k) :
    (Matrix.of fun r s : Fin k ↦ if r = a ∧ s = b then (1 : R) else 0) *
      (Matrix.of fun r s : Fin k ↦ if r = c ∧ s = d then (1 : R) else 0) =
      if b = c then Matrix.of fun r s : Fin k ↦ if r = a ∧ s = d then (1 : R) else 0
      else 0 := by
  ext r s
  rw [Matrix.mul_apply]
  by_cases hbc : b = c
  · subst hbc
    simp only [↓reduceIte, Matrix.of_apply]
    rw [Finset.sum_eq_single b]
    · by_cases hra : r = a <;> by_cases hsd : s = d <;> simp [hra, hsd]
    · intro t _ htb; simp [htb]
    · intro h; exact absurd (Finset.mem_univ b) h
  · simp only [hbc, ↓reduceIte, Matrix.zero_apply, Matrix.of_apply]
    refine Finset.sum_eq_zero fun t _ ↦ ?_
    by_cases htb : t = b
    · subst htb; simp [hbc]
    · simp [htb]

/-- Product of the ordered staircase matrix units $e_{0,0} e_{0,1} \cdots e_{k-1,k-1}$ equals
$e_{0, k-1}$. -/
private theorem staircaseMatrix_ordered_prod {R : Type*} [Semiring R]
    (k : ℕ) (hk : 1 ≤ k) :
    ∀ m (hm : m ≤ 2 * k - 1), 1 ≤ m →
      ((List.finRange m).map fun t ↦
        staircaseMatrix (R := R) k ⟨t.val, by omega⟩).prod =
        Matrix.of fun r s : Fin k ↦ if r.val = 0 ∧ s.val = m / 2 then 1 else 0 := by
  intro m
  induction m with
  | zero => intro _ hm1; omega
  | succ m ih =>
    intro hm _
    by_cases hm0 : m = 0
    · subst hm0
      simp [staircaseMatrix, List.finRange]
    · have hfin : List.finRange (m + 1) =
          (List.finRange m).map Fin.castSucc ++ [Fin.last m] := List.finRange_succ_last
      rw [hfin, List.map_append, List.map_map, List.map_singleton, List.prod_append,
        List.prod_singleton]
      have hprev := ih (by omega) (by omega)
      have heq_prev : (List.finRange m).map ((fun t : Fin (m + 1) ↦
          staircaseMatrix (R := R) k ⟨t.val, by omega⟩) ∘ Fin.castSucc) =
          (List.finRange m).map fun t : Fin m ↦
            staircaseMatrix (R := R) k ⟨t.val, by omega⟩ := rfl
      rw [heq_prev, hprev]
      let a : Fin k := ⟨0, by omega⟩
      let b : Fin k := ⟨m / 2, by omega⟩
      let d : Fin k := ⟨(m + 1) / 2, by omega⟩
      have hM1 : (Matrix.of fun r s : Fin k ↦ if r.val = 0 ∧ s.val = m / 2 then (1 : R) else 0) =
          Matrix.of fun r s : Fin k ↦ if r = a ∧ s = b then (1 : R) else 0 := by
        ext r s; simp [a, b, Fin.ext_iff]
      have hM2 : staircaseMatrix (R := R) k ⟨(Fin.last m).val, by omega⟩ =
          Matrix.of fun r s : Fin k ↦ if r = b ∧ s = d then (1 : R) else 0 := by
        ext r s; simp [staircaseMatrix, b, d, Fin.ext_iff]
      rw [hM1, hM2, matrix_unit_mul]
      ext r s
      simp [a, d, Fin.ext_iff]

/-- Any product of staircase matrices indexed by a non-identity permutation of `Fin (2 * k - 1)`
equals `0`. -/
private theorem staircaseMatrix_perm_prod_eq_zero {R : Type*} [Semiring R]
    (k : ℕ) (hk : 1 ≤ k) (τ : Equiv.Perm (Fin (2 * k - 1))) (hτ : τ ≠ 1) :
    ((List.finRange (2 * k - 1)).map fun t ↦ staircaseMatrix (R := R) k (τ t)).prod = 0 := by
  -- If `τ ≠ 1`, there is some `r < 2 * k - 2` where `¬ (τ r < τ (r + 1))`
  have hex_drop : ∃ r : ℕ, ∃ hr : r + 1 < 2 * k - 1,
      ((τ ⟨r, by omega⟩).val + 1) / 2 ≠ (τ ⟨r + 1, hr⟩).val / 2 := by
    by_contra hall
    push Not at hall
    -- Then `τ` is strictly increasing on `Fin (2 * k - 1)`!
    have hstrict : ∀ (r : ℕ) (hr : r + 1 < 2 * k - 1),
        (τ ⟨r, by omega⟩).val < (τ ⟨r + 1, hr⟩).val := by
      intro r hr
      have heq := hall r hr
      have hne : (τ ⟨r, by omega⟩).val ≠ (τ ⟨r + 1, hr⟩).val := fun h ↦ by
        have hfin : (⟨r, by omega⟩ : Fin (2 * k - 1)) = ⟨r + 1, hr⟩ := τ.injective (Fin.ext h)
        have hval := congrArg Fin.val hfin
        dsimp only at hval
        omega
      omega
    have hge : ∀ r : Fin (2 * k - 1), r.val ≤ (τ r).val := by
      intro r
      obtain ⟨rv, hrv⟩ := r
      induction rv with
      | zero => exact Nat.zero_le _
      | succ rv ihr =>
        have h1 : rv ≤ (τ ⟨rv, by omega⟩).val := ihr (by omega)
        have h2 : (τ ⟨rv, by omega⟩).val < (τ ⟨rv + 1, hrv⟩).val := hstrict rv hrv
        change rv + 1 ≤ (τ ⟨rv + 1, hrv⟩).val
        omega
    have hle : ∀ r : Fin (2 * k - 1), (τ r).val ≤ r.val := by
      intro r
      have hsum : ∑ i : Fin (2 * k - 1), (τ i).val = ∑ i : Fin (2 * k - 1), i.val :=
        Equiv.sum_comp τ (fun i : Fin (2 * k - 1) ↦ i.val)
      by_contra hgt
      have hlt : r.val < (τ r).val := Nat.lt_of_not_le hgt
      have hsum_gt : ∑ i : Fin (2 * k - 1), i.val < ∑ i : Fin (2 * k - 1), (τ i).val :=
        Finset.sum_lt_sum (fun i _ ↦ hge i) ⟨r, Finset.mem_univ r, hlt⟩
      omega
    apply hτ
    ext r
    have h1 := hge r
    have h2 := hle r
    simp only [Equiv.Perm.coe_one, id_eq]
    omega
  obtain ⟨r, hr, hne_div⟩ := hex_drop
  let L := (List.finRange (2 * k - 1)).map fun t ↦ staircaseMatrix (R := R) k (τ t)
  have hlen : L.length = 2 * k - 1 := by simp [L]
  have hsplit : L = L.take r ++ [L[r]'(by omega), L[r + 1]'(by omega)] ++ L.drop (r + 2) := by
    have h1 := (List.take_append_drop r L).symm
    have h2 : L.drop r = L[r]'(by omega) :: L.drop (r + 1) := List.drop_eq_getElem_cons (by omega)
    have h3 : L.drop (r + 1) = L[r + 1]'(by omega) :: L.drop (r + 2) :=
      List.drop_eq_getElem_cons (by omega)
    conv_lhs => rw [h1, h2, h3]
    simp
  have hmul0 : L[r]'(by omega) * L[r + 1]'(by omega) = 0 := by
    simp only [L, List.getElem_map, List.getElem_finRange, Fin.cast_mk]
    let a : Fin k := ⟨(τ ⟨r, by omega⟩).val / 2, by omega⟩
    let b : Fin k := ⟨((τ ⟨r, by omega⟩).val + 1) / 2, by omega⟩
    let c : Fin k := ⟨(τ ⟨r + 1, hr⟩).val / 2, by omega⟩
    let d : Fin k := ⟨((τ ⟨r + 1, hr⟩).val + 1) / 2, by omega⟩
    have hM1 : staircaseMatrix (R := R) k (τ ⟨r, by omega⟩) =
        Matrix.of fun i j : Fin k ↦ if i = a ∧ j = b then (1 : R) else 0 := by
      ext i j; simp [staircaseMatrix, a, b, Fin.ext_iff]
    have hM2 : staircaseMatrix (R := R) k (τ ⟨r + 1, hr⟩) =
        Matrix.of fun i j : Fin k ↦ if i = c ∧ j = d then (1 : R) else 0 := by
      ext i j; simp [staircaseMatrix, c, d, Fin.ext_iff]
    have hbc : b ≠ c := fun h ↦ hne_div (congrArg Fin.val h)
    rw [hM1, hM2, matrix_unit_mul, ite_eq_right_iff.mpr fun h ↦ absurd h hbc]
  change L.prod = 0
  rw [hsplit, List.prod_append, List.prod_append, List.prod_cons, List.prod_singleton, hmul0,
    mul_zero, zero_mul]

/-- Over any nontrivial commutative ring $R$ (in particular any field
or any nontrivial finite commutative ring), the $k \times k$ matrix algebra $M_k(R)$ does not
satisfy any nonzero noncommutative polynomial identity of degree strictly less than $2k$. -/
theorem matrix_no_identity_lt_two_mul_dim {R : Type*} [CommRing R]
    {n k : ℕ} (hk : 1 ≤ k) {f : FreeAlgebra R (Fin n)}
    (hf : f ≠ 0) (hdeg : noncommDegree f < 2 * k) :
    ∃ M : Fin n → Matrix (Fin k) (Fin k) R, FreeAlgebra.lift R M f ≠ 0 := by
  classical
  by_contra hall
  push Not at hall
  have hid : IsPolyIdentity (Matrix (Fin k) (Fin k) R) f := hall
  obtain ⟨g, hg_ne, hg_ml, hg_id⟩ :=
    exists_multilinear_identity_exact (Matrix (Fin k) (Fin k) R) hf hid
      (by omega : noncommDegree f ≤ 2 * k - 1)
  obtain ⟨w₀, hw₀_coeff⟩ := FreeAlgebra.exists_coeff_ne_zero hg_ne
  have hw₀_supp : w₀ ∈ noncommSupport g := mem_noncommSupport_iff.mpr hw₀_coeff
  -- Every `w ∈ noncommSupport g` has `w.toList = List.ofFn σ` for a unique `σ`
  have hex_perm : ∀ w ∈ noncommSupport g,
      ∃ σ : Equiv.Perm (Fin (2 * k - 1)), w.toList = List.ofFn σ := by
    intro w hw
    have hlen : w.toList.length = 2 * k - 1 := by
      have hsum : ∑ i : Fin (2 * k - 1), w.toList.count i = w.toList.length := by
        clear hg_ml hw hg_id hg_ne hw₀_supp hw₀_coeff w₀
        induction w.toList with
        | nil => simp
        | cons a l ihl =>
          simp only [List.count_cons, List.length_cons, Finset.sum_add_distrib, ihl]
          have h1 : ∑ i : Fin (2 * k - 1), (if a == i then 1 else 0) = 1 := by
            rw [Finset.sum_eq_single a]
            · simp
            · intro i _ hia; simp [Ne.symm hia]
            · intro h; exact absurd (Finset.mem_univ a) h
          omega
      rw [← hsum]
      calc
        ∑ i : Fin (2 * k - 1), w.toList.count i = ∑ _i : Fin (2 * k - 1), 1 :=
          Finset.sum_congr rfl fun i _ ↦ hg_ml w hw i
        _ = 2 * k - 1 := by simp
    let fn : Fin (2 * k - 1) → Fin (2 * k - 1) := fun j ↦ w.toList[j.val]'(by omega)
    have hsurj : Function.Surjective fn := by
      intro i
      have hmem : i ∈ w.toList := List.count_pos_iff.mp (by rw [hg_ml w hw i]; omega)
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
      exact ⟨⟨j, by omega⟩, rfl⟩
    have hbij : Function.Bijective fn := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
    refine ⟨Equiv.ofBijective fn hbij, ?_⟩
    apply List.ext_getElem
    · simp [hlen]
    · intro j hj1 hj2
      simp [fn]
  obtain ⟨σ₀, hσ₀⟩ := hex_perm w₀ hw₀_supp
  let X : Fin (2 * k - 1) → Matrix (Fin k) (Fin k) R :=
    fun i ↦ staircaseMatrix (R := R) k (σ₀.symm i)
  have heval_zero : FreeAlgebra.lift R X g = 0 := hg_id X
  -- Compute `(FreeAlgebra.lift R X g) ⟨0, _⟩ ⟨k - 1, _⟩ = FreeAlgebra.coeff w₀ g`
  have hentry : FreeAlgebra.lift R X g ⟨0, by omega⟩ ⟨k - 1, by omega⟩ =
      FreeAlgebra.coeff w₀ g := by
    conv_lhs => rw [freeAlgebra_eq_sum_support g]
    rw [map_sum, Matrix.sum_apply]
    rw [Finset.sum_eq_single w₀]
    · rw [map_smul, freeAlgebra_lift_monomial, hσ₀, List.map_ofFn]
      have hcomp : (List.ofFn (X ∘ σ₀)).prod =
          ((List.finRange (2 * k - 1)).map fun t ↦ staircaseMatrix (R := R) k t).prod := by
        rw [List.ofFn_eq_map]
        congr 1
        refine List.map_congr_left fun t _ ↦ ?_
        simp [X]
      rw [hcomp, staircaseMatrix_ordered_prod k hk (2 * k - 1) le_rfl (by omega)]
      have hdiv : (2 * k - 1) / 2 = k - 1 := by omega
      simp [hdiv]
    · intro w hw hne
      obtain ⟨σ, hσ⟩ := hex_perm w hw
      let τ : Equiv.Perm (Fin (2 * k - 1)) := σ.trans σ₀.symm
      have hτ_ne : τ ≠ 1 := by
        intro h1
        apply hne
        have hσ_eq : σ = σ₀ := by
          ext j
          have := congrArg (fun e : Equiv.Perm (Fin (2 * k - 1)) ↦ (σ₀ (e j)).val) h1
          simpa [τ, Equiv.Perm.coe_one] using this
        have hlist : w.toList = w₀.toList := by rw [hσ, hσ₀, hσ_eq]
        simpa using congrArg FreeMonoid.ofList hlist
      rw [map_smul, freeAlgebra_lift_monomial, hσ, List.map_ofFn]
      have hcomp : (List.ofFn (X ∘ σ)).prod =
          ((List.finRange (2 * k - 1)).map fun t ↦ staircaseMatrix (R := R) k (τ t)).prod := by
        rw [List.ofFn_eq_map]
        congr 1
      rw [hcomp, staircaseMatrix_perm_prod_eq_zero k hk τ hτ_ne, smul_zero, Matrix.zero_apply]
    · intro hnot; exact absurd hw₀_supp hnot
  rw [heval_zero, Matrix.zero_apply] at hentry
  exact hw₀_coeff hentry.symm

end CslibFrontier.Algebra
