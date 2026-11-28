module

public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Complexity.Reduction
public import Mathlib.CategoryTheory.Topos.Sheaf

import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import Cslib.Foundations.Data.Nat.PolynomialBound
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import Mathlib.Data.Set.Finite.Basic

/-!
# Finite-Perturbation Stability and the Presheaf Category of Feasible Computations

This module establishes two general structural properties of deterministic (`P`) and
nondeterministic (`NP`) polynomial-time complexity classes over arbitrary injectively binary-encoded
types `(α, enc : α ↪ List Bool)`:

1. **Finite-perturbation and asymptotic-length invariance**: modifying a Boolean function or
   decision problem on finitely many inputs—in particular, on all inputs of encoded bit-length
   strictly below a threshold `N₀`—preserves `Turing.MultiTapeTM.ComputableInPolyTime`,
   `Cslib.Complexity.P`, and `Cslib.Complexity.NP`.
2. **Categorical and presheaf characterization of `P` vs `NP`**: encoded types and polynomial-time
   computable maps form a category `FeasibleCat` whose presheaf topos `FeasibleTopos` carries
   contravariant subobject presheaves `detPresheaf` (`P`) and `ndetPresheaf` (`NP`). The complexity
   collapse `P = NP` across all encoded types holds if and only if the induced product
   endofunctors `detFunctor` and `existFunctor` on `FeasibleTopos` are naturally isomorphic.
-/

public section

open CategoryTheory

namespace CslibFrontier.Complexity

section FinitePerturbation

/-- For every natural bound `N₀`, only finitely many Boolean lists have length `< N₀`. -/
theorem finite_list_length_lt (N₀ : ℕ) : {l : List Bool | l.length < N₀}.Finite := by
  induction N₀ with
  | zero =>
    exact Set.finite_empty.subset (by simp)
  | succ k ih =>
    have hsub : {l : List Bool | l.length < k + 1} ⊆
        {[]} ∪ (List.cons false '' {l : List Bool | l.length < k}) ∪
          (List.cons true '' {l : List Bool | l.length < k}) := by
      intro l hl
      cases l with
      | nil =>
        left
        left
        rfl
      | cons b tail =>
        have htail : tail.length < k := Nat.lt_of_succ_lt_succ hl
        cases b
        · left
          right
          exact ⟨tail, htail, rfl⟩
        · right
          exact ⟨tail, htail, rfl⟩
    have h0 : ({([] : List Bool)} : Set (List Bool)).Finite := Set.finite_singleton []
    exact ((h0.union (ih.image _)).union (ih.image _)).subset hsub

/-- Under any injective binary encoding `enc : α ↪ List Bool`, at most finitely many elements have
encoded length strictly below `N₀`. -/
theorem finite_encoded_length_lt {α : Type*} (enc : α ↪ List Bool) (N₀ : ℕ) :
    {a : α | (enc a).length < N₀}.Finite :=
  (finite_list_length_lt N₀).preimage enc.injective.injOn

private theorem indicator_eq_true_iff {α : Type*} {L : Set α} {a : α} :
    Turing.MultiTapeTM.indicator L a = true ↔ a ∈ L :=
  (Turing.MultiTapeTM.indicator_eq_iff.mp rfl a).symm

private theorem indicator_eq_false_iff {α : Type*} {L : Set α} {a : α} :
    Turing.MultiTapeTM.indicator L a = false ↔ a ∉ L := by
  rw [← Bool.not_eq_true, indicator_eq_true_iff]

/-- Polynomial-time computability of Boolean functions is invariant under modifying finitely many
inputs. -/
theorem computableInPolyTime_of_finite_ne {α : Type} {enc : α ↪ List Bool}
    {f g : α → Bool}
    (hg : Turing.MultiTapeTM.ComputableInPolyTime g enc Turing.MultiTapeTM.encBool)
    (hfin : {a : α | f a ≠ g a}.Finite) :
    Turing.MultiTapeTM.ComputableInPolyTime f enc Turing.MultiTapeTM.encBool := by
  classical
  let S : Finset α := hfin.toFinset
  let diffMask : α → Bool := fun a ↦ f a != g a
  have hout : ∀ a ∉ S, Turing.MultiTapeTM.encBool (diffMask a) =
      Turing.MultiTapeTM.encBool false := by
    intro a ha
    have hfg : f a = g a := by
      by_contra hne
      exact ha (hfin.mem_toFinset.mpr hne)
    simp [diffMask, hfg]
  let c : ℕ := Turing.MultiTapeTM.almostConstTime enc Turing.MultiTapeTM.encBool
    diffMask S (Turing.MultiTapeTM.encBool false)
  have htime : Turing.MultiTapeTM.ComputableInTimeAndSpace diffMask enc
      Turing.MultiTapeTM.encBool (fun _ ↦ c) (fun _ ↦ 0) :=
    Turing.MultiTapeTM.computableInTimeAndSpace_almostConstTime diffMask S
      (Turing.MultiTapeTM.encBool false) hout
  have hdec : Turing.MultiTapeTM.DecidableInTimeAndSpace {a : α | diffMask a = true} enc
      (fun _ ↦ c) (fun _ ↦ 0) :=
    Turing.MultiTapeTM.decidableInTimeAndSpace_iff.mpr ⟨diffMask, htime, fun _ ↦ Iff.rfl⟩
  have hpoly_c : Cslib.PolynomiallyBounded (fun _ : ℕ ↦ c) :=
    Cslib.polynomiallyBounded_iff_le.mpr ⟨c, 0, fun _ ↦ by simp⟩
  have hmemP : {a : α | diffMask a = true} ∈ Cslib.Complexity.P enc :=
    Cslib.Complexity.mem_P_of_decidableInTimeAndSpace hpoly_c hdec
  obtain ⟨d, hd_poly, hd_iff⟩ := Cslib.Complexity.mem_P.mp hmemP
  have hd_eq : d = diffMask := by
    funext a
    have hiff := hd_iff a
    cases h1 : diffMask a <;> cases h2 : d a <;> simp_all
  rw [hd_eq] at hd_poly
  have hbne : Turing.MultiTapeTM.ComputableInPolyTime (fun a ↦ g a != diffMask a) enc
      Turing.MultiTapeTM.encBool :=
    Turing.MultiTapeTM.ComputableInPolyTime.bne hg hd_poly
  have hfeq : (fun a ↦ g a != diffMask a) = f := by
    funext a
    dsimp [diffMask]
    cases f a <;> cases g a <;> rfl
  rwa [hfeq] at hbne

/-- Membership in `Cslib.Complexity.P enc` is preserved under finite modifications. -/
theorem mem_P_of_finite_diff {α : Type} {enc : α ↪ List Bool} {A B : Set α}
    (hB : B ∈ Cslib.Complexity.P enc)
    (hfin : {a : α | ¬ (a ∈ A ↔ a ∈ B)}.Finite) :
    A ∈ Cslib.Complexity.P enc := by
  obtain ⟨g, hg_poly, hg_iff⟩ := Cslib.Complexity.mem_P.mp hB
  have hfin_ind : {a : α | Turing.MultiTapeTM.indicator A a ≠ g a}.Finite := by
    refine hfin.subset fun a hne hiff ↦ hne ?_
    have hA := (indicator_eq_true_iff (L := A) (a := a)).symm
    have hBg := hg_iff a
    cases h1 : Turing.MultiTapeTM.indicator A a <;> cases h2 : g a <;> simp_all
  have hind_poly : Turing.MultiTapeTM.ComputableInPolyTime
      (Turing.MultiTapeTM.indicator A) enc Turing.MultiTapeTM.encBool :=
    computableInPolyTime_of_finite_ne hg_poly hfin_ind
  exact Cslib.Complexity.mem_P.mpr
    ⟨Turing.MultiTapeTM.indicator A, hind_poly, fun a ↦ (indicator_eq_true_iff).symm⟩

/-- Membership in `Cslib.Complexity.P enc` depends only on inputs of encoded length `≥ N₀`. -/
theorem mem_P_of_eventually_length {α : Type} {enc : α ↪ List Bool} {A B : Set α}
    (hB : B ∈ Cslib.Complexity.P enc) {N₀ : ℕ}
    (hagree : ∀ a : α, N₀ ≤ (enc a).length → (a ∈ A ↔ a ∈ B)) :
    A ∈ Cslib.Complexity.P enc := by
  refine mem_P_of_finite_diff hB ((finite_encoded_length_lt enc N₀).subset fun a hnot ↦ ?_)
  by_contra hge
  exact hnot (hagree a (Nat.le_of_not_lt hge))

/-- Membership in `Cslib.Complexity.NP enc` is preserved under finite modifications. -/
theorem mem_NP_of_finite_diff {α : Type} {enc : α ↪ List Bool} {A B : Set α}
    (hB : B ∈ Cslib.Complexity.NP enc)
    (hfin : {a : α | ¬ (a ∈ A ↔ a ∈ B)}.Finite) :
    A ∈ Cslib.Complexity.NP enc := by
  obtain ⟨p, V, hV_poly, hVer⟩ := Cslib.Complexity.mem_NP.mp hB
  have hpos_fin : {a : α | Turing.MultiTapeTM.indicator (A \ B) a ≠ false}.Finite := by
    refine hfin.subset fun a hne hiff ↦ ?_
    have hne' : Turing.MultiTapeTM.indicator (A \ B) a ≠ false := hne
    have htrue : Turing.MultiTapeTM.indicator (A \ B) a = true := by
      cases hb : Turing.MultiTapeTM.indicator (A \ B) a
      · exact False.elim (hne' hb)
      · rfl
    have hmem : a ∈ A \ B := indicator_eq_true_iff.mp htrue
    exact hmem.2 (hiff.mp hmem.1)
  have hneg_fin : {a : α | Turing.MultiTapeTM.indicator (Bᶜ ∪ A) a ≠ true}.Finite := by
    refine hfin.subset fun a hne hiff ↦ ?_
    have hne' : Turing.MultiTapeTM.indicator (Bᶜ ∪ A) a ≠ true := hne
    have hfalse : Turing.MultiTapeTM.indicator (Bᶜ ∪ A) a = false := by
      cases hb : Turing.MultiTapeTM.indicator (Bᶜ ∪ A) a
      · rfl
      · exact False.elim (hne' hb)
    have hnot : a ∉ Bᶜ ∪ A := indicator_eq_false_iff.mp hfalse
    have haB : a ∈ B := by
      by_contra hnB
      exact hnot (Or.inl hnB)
    exact hnot (Or.inr (hiff.mpr haB))
  have hpos_poly : Turing.MultiTapeTM.ComputableInPolyTime
      (Turing.MultiTapeTM.indicator (A \ B)) enc Turing.MultiTapeTM.encBool :=
    computableInPolyTime_of_finite_ne (Turing.MultiTapeTM.ComputableInPolyTime.const false)
      hpos_fin
  have hneg_poly : Turing.MultiTapeTM.ComputableInPolyTime
      (Turing.MultiTapeTM.indicator (Bᶜ ∪ A)) enc Turing.MultiTapeTM.encBool :=
    computableInPolyTime_of_finite_ne (Turing.MultiTapeTM.ComputableInPolyTime.const true)
      hneg_fin
  have hfst : Turing.MultiTapeTM.ComputableInPolyTime (fun x : α × List Bool ↦ x.1)
      (Turing.MultiTapeTM.encPair enc Turing.MultiTapeTM.encBits) enc :=
    Turing.MultiTapeTM.ComputableInPolyTime.fst enc Turing.MultiTapeTM.encBits
  have hpos_pair : Turing.MultiTapeTM.ComputableInPolyTime
      (fun x : α × List Bool ↦ Turing.MultiTapeTM.indicator (A \ B) x.1)
      (Turing.MultiTapeTM.encPair enc Turing.MultiTapeTM.encBits) Turing.MultiTapeTM.encBool :=
    Turing.MultiTapeTM.ComputableInPolyTime.comp' hpos_poly hfst
  have hneg_pair : Turing.MultiTapeTM.ComputableInPolyTime
      (fun x : α × List Bool ↦ Turing.MultiTapeTM.indicator (Bᶜ ∪ A) x.1)
      (Turing.MultiTapeTM.encPair enc Turing.MultiTapeTM.encBits) Turing.MultiTapeTM.encBool :=
    Turing.MultiTapeTM.ComputableInPolyTime.comp' hneg_poly hfst
  let V' : α × List Bool → Bool := fun x ↦
    Turing.MultiTapeTM.indicator (A \ B) x.1 ||
      (Turing.MultiTapeTM.indicator (Bᶜ ∪ A) x.1 && V x)
  have hV'_poly : Turing.MultiTapeTM.ComputableInPolyTime V'
      (Turing.MultiTapeTM.encPair enc Turing.MultiTapeTM.encBits) Turing.MultiTapeTM.encBool :=
    Turing.MultiTapeTM.ComputableInPolyTime.bool_or' hpos_pair
      (Turing.MultiTapeTM.ComputableInPolyTime.bool_and' hneg_pair hV_poly)
  refine Cslib.Complexity.mem_NP.mpr ⟨p, V', hV'_poly, fun a ↦ ?_⟩
  constructor
  · intro haA
    by_cases haB : a ∈ B
    · obtain ⟨w, hw_len, hw_V⟩ := (hVer a).mp haB
      refine ⟨w, hw_len, ?_⟩
      have hguard : Turing.MultiTapeTM.indicator (Bᶜ ∪ A) a = true :=
        indicator_eq_true_iff.mpr (Or.inr haA)
      simp [V', hguard, hw_V]
    · refine ⟨List.replicate (p.eval (enc a).length) false, List.length_replicate, ?_⟩
      have hpos : Turing.MultiTapeTM.indicator (A \ B) a = true :=
        indicator_eq_true_iff.mpr ⟨haA, haB⟩
      simp [V', hpos]
  · rintro ⟨w, hw_len, hw_V'⟩
    dsimp [V'] at hw_V'
    rw [Bool.or_eq_true, Bool.and_eq_true] at hw_V'
    rcases hw_V' with hpos | ⟨hguard, hw_V⟩
    · exact (indicator_eq_true_iff.mp hpos).1
    · have haB : a ∈ B := (hVer a).mpr ⟨w, hw_len, hw_V⟩
      rcases indicator_eq_true_iff.mp hguard with hnB | haA
      · exact False.elim (hnB haB)
      · exact haA

/-- Membership in `Cslib.Complexity.NP enc` depends only on inputs of encoded length `≥ N₀`. -/
theorem mem_NP_of_eventually_length {α : Type} {enc : α ↪ List Bool} {A B : Set α}
    (hB : B ∈ Cslib.Complexity.NP enc) {N₀ : ℕ}
    (hagree : ∀ a : α, N₀ ≤ (enc a).length → (a ∈ A ↔ a ∈ B)) :
    A ∈ Cslib.Complexity.NP enc := by
  refine mem_NP_of_finite_diff hB ((finite_encoded_length_lt enc N₀).subset fun a hnot ↦ ?_)
  by_contra hge
  exact hnot (hagree a (Nat.le_of_not_lt hge))

end FinitePerturbation

section FeasibleCategory

/-- Category of injectively binary-encoded data types. -/
structure FeasibleCat : Type 1 where
  /-- Underlying type. -/
  carrier : Type
  /-- Injective binary encoding into `List Bool`. -/
  enc : carrier ↪ List Bool

instance : Inhabited FeasibleCat :=
  ⟨⟨Unit, Turing.MultiTapeTM.encUnit⟩⟩

/-- Polynomial-time computable morphisms between encoded types. -/
@[ext]
structure FeasibleHom (X Y : FeasibleCat) : Type where
  /-- Underlying function. -/
  fn : X.carrier → Y.carrier
  /-- Polynomial-time computability witness. -/
  polyTime : Turing.MultiTapeTM.ComputableInPolyTime fn X.enc Y.enc

instance instCategoryFeasibleCat : Category.{0, 1} FeasibleCat where
  Hom := FeasibleHom
  id _ := ⟨fun x ↦ x, Turing.MultiTapeTM.ComputableInPolyTime.id'⟩
  comp f g := ⟨fun x ↦ g.fn (f.fn x),
    Turing.MultiTapeTM.ComputableInPolyTime.comp' g.polyTime f.polyTime⟩
  id_comp _ := by ext; rfl
  comp_id _ := by ext; rfl
  assoc _ _ _ := by ext; rfl

/-- Terminal one-point encoded object `(Unit, encUnit)`. -/
@[expose]
def unitFeasibleObj : FeasibleCat :=
  ⟨Unit, Turing.MultiTapeTM.encUnit⟩

/-- Constant polynomial-time morphism `() ↦ x₀` into `X`. -/
def constFeasibleHom (X : FeasibleCat) (x₀ : X.carrier) : unitFeasibleObj ⟶ X where
  fn _ := x₀
  polyTime := Turing.MultiTapeTM.ComputableInPolyTime.const x₀

@[simp]
theorem constFeasibleHom_fn (X : FeasibleCat) (x₀ : X.carrier) (u : Unit) :
    (constFeasibleHom X x₀).fn u = x₀ := by
  rfl

/-- Every `FeasibleHom` induces a polynomial-time many-one reduction under preimages. -/
theorem polyTimeReducible_preimage {X Y : FeasibleCat} (f : X ⟶ Y) (L : Set Y.carrier) :
    Cslib.Complexity.PolyTimeReducible X.enc Y.enc (f.fn ⁻¹' L) L :=
  Cslib.Complexity.polyTimeReducible_iff_manyOneReducibleBy.mpr
    ⟨f.fn, f.polyTime, fun _ ↦ Set.mem_preimage⟩

/-- Presheaf category `FeasibleCatᵒᵖ ⥤ Type 1` over encoded polynomial-time computations. -/
abbrev FeasibleTopos : Type 2 :=
  FeasibleCatᵒᵖ ⥤ Type 1

/-- Contravariant presheaf of `P` languages on `FeasibleCat`. -/
@[expose]
def detPresheaf : FeasibleTopos where
  obj X := ULift.{1} {L : Set (Opposite.unop X).carrier //
    L ∈ Cslib.Complexity.P (Opposite.unop X).enc}
  map f := TypeCat.ofHom fun s ↦
    ULift.up ⟨f.unop.fn ⁻¹' s.down.1,
      (polyTimeReducible_preimage f.unop s.down.1).mem_P s.down.2⟩
  map_id _ := by apply ConcreteCategory.hom_ext; intro _; rfl
  map_comp _ _ := by apply ConcreteCategory.hom_ext; intro _; rfl

/-- Contravariant presheaf of `NP` languages on `FeasibleCat`. -/
@[expose]
def ndetPresheaf : FeasibleTopos where
  obj X := ULift.{1} {L : Set (Opposite.unop X).carrier //
    L ∈ Cslib.Complexity.NP (Opposite.unop X).enc}
  map f := TypeCat.ofHom fun s ↦
    ULift.up ⟨f.unop.fn ⁻¹' s.down.1,
      Cslib.Complexity.PolyTimeReducible.mem_NP
        (polyTimeReducible_preimage f.unop s.down.1) s.down.2⟩
  map_id _ := by apply ConcreteCategory.hom_ext; intro _; rfl
  map_comp _ _ := by apply ConcreteCategory.hom_ext; intro _; rfl

/-- Pointwise Cartesian product endofunctor `G ↦ P × G` on `FeasibleTopos`. -/
@[expose]
def presheafProdEndofunctor (P : FeasibleTopos) : FeasibleTopos ⥤ FeasibleTopos where
  obj G :=
    { obj := fun X ↦ P.obj X × G.obj X
      map := fun f ↦ TypeCat.ofHom fun pg ↦ (P.map f pg.1, G.map f pg.2)
      map_id := fun _ ↦ by apply ConcreteCategory.hom_ext; intro _; ext <;> simp
      map_comp := fun _ _ ↦ by apply ConcreteCategory.hom_ext; intro _; ext <;> simp }
  map α :=
    { app := fun X ↦ TypeCat.ofHom fun pg ↦ (pg.1, α.app X pg.2)
      naturality := fun _ _ _ ↦ by
        apply ConcreteCategory.hom_ext
        intro _
        ext : 1
        · rfl
        · simp }
  map_id _ := by ext _ <;> simp
  map_comp _ _ := by ext _ <;> simp

/-- Deterministic polynomial-time product endofunctor on `FeasibleTopos`. -/
@[expose]
def detFunctor : FeasibleTopos ⥤ FeasibleTopos :=
  presheafProdEndofunctor detPresheaf

/-- Nondeterministic polynomial-time product endofunctor on `FeasibleTopos`. -/
@[expose]
def existFunctor : FeasibleTopos ⥤ FeasibleTopos :=
  presheafProdEndofunctor ndetPresheaf

/-- Terminal presheaf on `FeasibleCat` valued in `Type 1`. -/
@[expose]
def terminalFeasiblePresheaf : FeasibleTopos where
  obj _ := PUnit.{2}
  map _ := TypeCat.ofHom fun _ ↦ PUnit.unit
  map_id _ := by apply ConcreteCategory.hom_ext; intro u; cases u; rfl
  map_comp _ _ := by apply ConcreteCategory.hom_ext; intro u; cases u; rfl

/-- Natural isomorphism `(presheafProdEndofunctor P).obj terminalFeasiblePresheaf ≅ P`. -/
def presheafProdTerminalIso (P : FeasibleTopos) :
    (presheafProdEndofunctor P).obj terminalFeasiblePresheaf ≅ P :=
  NatIso.ofComponents
    (fun _ ↦
      { hom := TypeCat.ofHom Prod.fst
        inv := TypeCat.ofHom fun p ↦ (p, PUnit.unit)
        hom_inv_id := by
          apply ConcreteCategory.hom_ext
          intro pq
          rcases pq with ⟨_, ⟨⟩⟩
          rfl
        inv_hom_id := by apply ConcreteCategory.hom_ext; intro _; rfl })
    (fun _ ↦ by apply ConcreteCategory.hom_ext; intro _; rfl)

/-- `Cslib.Complexity.P = Cslib.Complexity.NP` across all encoded types holds if and only if
`detFunctor` and `existFunctor` are naturally isomorphic endofunctors on `FeasibleTopos`. -/
theorem P_eq_NP_iff_detFunctor_iso_existFunctor :
    (∀ {α : Type} (enc : α ↪ List Bool),
      Cslib.Complexity.P enc = Cslib.Complexity.NP enc) ↔
    Nonempty (detFunctor ≅ existFunctor) := by
  constructor
  · intro heq
    let hpresheaf : detPresheaf ≅ ndetPresheaf :=
      NatIso.ofComponents
        (fun X ↦
          { hom := TypeCat.ofHom fun s ↦
              ULift.up ⟨s.down.1, Cslib.Complexity.P_subset_NP s.down.2⟩
            inv := TypeCat.ofHom fun s ↦
              ULift.up ⟨s.down.1, by rw [heq (Opposite.unop X).enc]; exact s.down.2⟩
            hom_inv_id := by apply ConcreteCategory.hom_ext; intro _; rfl
            inv_hom_id := by apply ConcreteCategory.hom_ext; intro _; rfl })
        (fun _ ↦ by apply ConcreteCategory.hom_ext; intro _; rfl)
    refine ⟨NatIso.ofComponents
      (fun _ ↦ NatIso.ofComponents
        (fun X ↦
          { hom := TypeCat.ofHom fun pg ↦ (hpresheaf.hom.app X pg.1, pg.2)
            inv := TypeCat.ofHom fun pg ↦ (hpresheaf.inv.app X pg.1, pg.2)
            hom_inv_id := by
              apply ConcreteCategory.hom_ext
              intro ⟨_, _⟩
              apply Prod.ext <;> rfl
            inv_hom_id := by
              apply ConcreteCategory.hom_ext
              intro ⟨_, _⟩
              apply Prod.ext <;> rfl })
        (fun _ ↦ by
          apply ConcreteCategory.hom_ext
          intro ⟨_, _⟩
          apply Prod.ext <;> rfl))
      (fun _ ↦ by ext _; rfl)⟩
  · classical
    rintro ⟨iso⟩
    have θ : detPresheaf ≅ ndetPresheaf :=
      (presheafProdTerminalIso detPresheaf).symm ≪≫
        iso.app terminalFeasiblePresheaf ≪≫
        presheafProdTerminalIso ndetPresheaf
    intro α enc
    let X : FeasibleCat := ⟨α, enc⟩
    apply Set.Subset.antisymm Cslib.Complexity.P_subset_NP
    intro M hM
    let uUnit := Opposite.op unitFeasibleObj
    let uX := Opposite.op X
    let empUnit : detPresheaf.obj uUnit := ULift.up ⟨∅, Cslib.Complexity.empty_mem_P⟩
    let univUnit : detPresheaf.obj uUnit := ULift.up ⟨Set.univ, Cslib.Complexity.univ_mem_P⟩
    have hne_unit : empUnit ≠ univUnit := by
      intro h
      have hset : (∅ : Set unitFeasibleObj.carrier) = Set.univ :=
        congrArg Subtype.val (congrArg ULift.down h)
      have hmem : (() : unitFeasibleObj.carrier) ∈ (∅ : Set unitFeasibleObj.carrier) := by
        rw [hset]
        trivial
      exact hmem
    have hinj_unit : Function.Injective (θ.hom.app uUnit) := by
      intro a b hab
      have hleft := ConcreteCategory.congr_hom (θ.hom_inv_id_app uUnit) a
      have hright := ConcreteCategory.congr_hom (θ.hom_inv_id_app uUnit) b
      simp only [comp_apply, ConcreteCategory.id_apply] at hleft hright
      rw [← hleft, hab, hright]
    have hθ_ne : θ.hom.app uUnit empUnit ≠ θ.hom.app uUnit univUnit :=
      fun h ↦ hne_unit (hinj_unit h)
    let mElem : ndetPresheaf.obj uX := ULift.up ⟨M, hM⟩
    let lElem : detPresheaf.obj uX := θ.inv.app uX mElem
    have hl_hom : θ.hom.app uX lElem = mElem := by
      have hinv := ConcreteCategory.congr_hom (θ.inv_hom_id_app uX) mElem
      simpa only [comp_apply, ConcreteCategory.id_apply, lElem] using hinv
    have hpull_eq : ∀ x₀ : X.carrier,
        detPresheaf.map (constFeasibleHom X x₀).op lElem =
          if x₀ ∈ lElem.down.1 then univUnit else empUnit := by
      intro x₀
      change ULift.up ⟨(constFeasibleHom X x₀).fn ⁻¹' lElem.down.1, _⟩ =
        if x₀ ∈ lElem.down.1 then univUnit else empUnit
      by_cases hx : x₀ ∈ lElem.down.1
      · simp only [hx, ↓reduceIte]
        apply ULift.ext
        apply Subtype.ext
        ext u
        exact iff_of_true hx trivial
      · simp only [hx, ↓reduceIte]
        apply ULift.ext
        apply Subtype.ext
        ext u
        exact iff_of_false hx (Set.notMem_empty u)
    have hmem_iff : ∀ x₀ : X.carrier,
        x₀ ∈ M ↔
          (() : unitFeasibleObj.carrier) ∈
            (θ.hom.app uUnit (if x₀ ∈ lElem.down.1 then univUnit else empUnit)).down.1 := by
      intro x₀
      have hsq := ConcreteCategory.congr_hom
        (θ.hom.naturality (constFeasibleHom X x₀).op) lElem
      have hsq' : ndetPresheaf.map (constFeasibleHom X x₀).op mElem =
          θ.hom.app uUnit (detPresheaf.map (constFeasibleHom X x₀).op lElem) := by
        simp only [comp_apply] at hsq
        rw [hl_hom] at hsq
        exact hsq.symm
      rw [hpull_eq x₀] at hsq'
      have hset : (constFeasibleHom X x₀).fn ⁻¹' M =
          (θ.hom.app uUnit (if x₀ ∈ lElem.down.1 then univUnit else empUnit)).down.1 :=
        congrArg (Subtype.val ∘ ULift.down) hsq'
      exact Eq.to_iff (congrArg (fun S ↦ (() : unitFeasibleObj.carrier) ∈ S) hset)
    by_cases huniv : (() : unitFeasibleObj.carrier) ∈ (θ.hom.app uUnit univUnit).down.1
    · have hemp : (() : unitFeasibleObj.carrier) ∉ (θ.hom.app uUnit empUnit).down.1 := by
        intro hemp_in
        apply hθ_ne
        apply ULift.ext
        apply Subtype.ext
        ext u
        cases u
        exact iff_of_true hemp_in huniv
      have hM_eq : M = lElem.down.1 := by
        ext x₀
        have hx := hmem_iff x₀
        by_cases hxl : x₀ ∈ lElem.down.1
        · simp only [hxl, ↓reduceIte] at hx
          exact iff_of_true (hx.mpr huniv) hxl
        · simp only [hxl, ↓reduceIte] at hx
          exact iff_of_false (fun hm ↦ hemp (hx.mp hm)) hxl
      rw [hM_eq]
      exact lElem.down.2
    · have hemp : (() : unitFeasibleObj.carrier) ∈ (θ.hom.app uUnit empUnit).down.1 := by
        by_contra hemp_out
        apply hθ_ne
        apply ULift.ext
        apply Subtype.ext
        ext u
        cases u
        exact iff_of_false hemp_out huniv
      have hM_eq : M = lElem.down.1ᶜ := by
        ext x₀
        have hx := hmem_iff x₀
        by_cases hxl : x₀ ∈ lElem.down.1
        · simp only [hxl, ↓reduceIte] at hx
          exact iff_of_false (fun hm ↦ huniv (hx.mp hm)) (not_not.mpr hxl)
        · simp only [hxl, ↓reduceIte] at hx
          exact iff_of_true (hx.mpr hemp) hxl
      rw [hM_eq]
      exact Cslib.Complexity.compl_mem_P lElem.down.2

end FeasibleCategory

end CslibFrontier.Complexity
