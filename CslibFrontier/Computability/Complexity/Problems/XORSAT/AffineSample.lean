/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.XORSAT.Dense
public import CslibFrontier.Computability.Probabilistic.Sampling
public import CslibFrontier.Foundations.Data.BitString.List.Operations
public import CslibFrontier.Foundations.Data.BitString.Parity

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.EncLen
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial-Time Affine Gaussian Elimination and Uniform Sampling over `𝔽₂`

This module constructs deterministic polynomial-time affine Gaussian elimination and uniform
strict probabilistic polynomial-time (`IsPPTOn`) affine solution sampling for dense `𝔽₂` linear
systems (`Cslib.Complexity.XORSAT.Dense.Input`).

Given a declared variable width `n` and a list of dense equations `a_r ⬝ x = b_r` over `Bool`
(`𝔽₂`), `affineSolve` maintains a particular vector `particular` together with `n` spanning
vectors `basis` of the common homogeneous kernel of the processed equations, starting from `0`
and the standard unit vectors `Cslib.BitString.listSingles n`. Each elimination step preserves
vector widths and never increases the encoded state length, certifying deterministic
polynomial-time computability on multi-tape Turing machines via `ComputableInPolyTime.foldl'`.

Pairing `affineSolve` with `n` uniform fair coins (`Cslib.BitString.sampleList`) via
`Cslib.Probability.IsPPTOn.of_seeded` yields `sampleAffineSolution`, whose pushforward under any
additive group homomorphism `BitString n →+ G` is uniform on the image of the affine solution
space (`card_addHom_fiber_mul_image`).
-/

public section

namespace CslibFrontier.Complexity.XORSAT.Dense

open Cslib Cslib.BitString Cslib.Complexity.XORSAT.Dense Cslib.Probability Turing.MultiTapeTM

/-- Polynomial-time Boolean inner product on bit lists, padding missing entries with `false`. -/
@[expose] def listDot (u v : List Bool) : Bool :=
  (u.zipWith Bool.and v).foldl Bool.xor false

/-- `listDot` is computable in deterministic polynomial time on raw bit strings. -/
@[fun_prop]
theorem isPolyTime_listDot {α : Type} {input : α ↪ List Bool} {u v : α → List Bool}
    (hu : ComputableInPolyTime u input encBits)
    (hv : ComputableInPolyTime v input encBits) :
    ComputableInPolyTime (fun x => listDot (u x) (v x)) input encBool := by
  unfold listDot
  exact ComputableInPolyTime.bitsFoldlWithInput Bool.xor
    (ComputableInPolyTime.bitsZipWithInput Bool.and hu hv) (.const false)

/-- On bit lists of length `n`, `listDot` agrees with the `BitString n` dot product `⬝ᵥ`. -/
theorem listDot_eq_dotProduct {n : ℕ} {u v : List Bool} (hu : u.length = n) (hv : v.length = n) :
    listDot u v = ofList n u ⬝ᵥ ofList n v := by
  have h := dotProduct_eq_foldl (ofList n u) (ofList n v)
  rw [ofFn_ofList hu, ofFn_ofList hv] at h
  exact h.symm

/-- `listDot` distributes over bitwise `xor` on lists of equal length `n`. -/
theorem listDot_zipWith_xor_right {n : ℕ} {a u v : List Bool} (ha : a.length = n)
    (hu : u.length = n) (hv : v.length = n) :
    listDot a (u.zipWith Bool.xor v) = xor (listDot a u) (listDot a v) := by
  have hlen : (u.zipWith Bool.xor v).length = n := by simp [hu, hv]
  have hof : ofList n (u.zipWith Bool.xor v) = ofList n u + ofList n v := by
    have hfn := ofFn_add (ofList n u) (ofList n v)
    rw [ofFn_ofList hu, ofFn_ofList hv] at hfn
    rw [← hfn, ofList_ofFn]
  rw [listDot_eq_dotProduct ha hlen, hof, dotProduct_add,
    ← listDot_eq_dotProduct ha hu, ← listDot_eq_dotProduct ha hv, Bool.add_eq_xor]

/-- Parametric representation `(particular, basis)` of an affine subspace `v₀ + span(basis)` of
`{0, 1}^n`. -/
@[ext]
structure AffineBasis where
  /-- Particular vector `v₀` of the affine subspace. -/
  particular : List Bool
  /-- Spanning vectors `u_1, ..., u_n` of the associated linear direction. -/
  basis : List (List Bool)
  deriving DecidableEq

/-- Multi-tape Turing machine encoding of `AffineBasis`. -/
def encAffineBasis : AffineBasis ↪ List Bool :=
  ⟨fun b => encPair encBits (encList encBits) (b.particular, b.basis),
   fun b₁ b₂ h => by
     have h' := (encPair encBits (encList encBits)).injective h
     exact AffineBasis.ext (congrArg Prod.fst h') (congrArg Prod.snd h')⟩

@[simp]
private theorem encAffineBasis_apply (b : AffineBasis) :
    encAffineBasis b = encPair encBits (encList encBits) (b.particular, b.basis) := rfl

/-- Constructing an `AffineBasis` from polynomial-time fields runs in polynomial time. -/
@[fun_prop]
theorem AffineBasis.isPolyTime_mk {α : Type} {input : α ↪ List Bool}
    {part : α → List Bool} {bas : α → List (List Bool)}
    (hp : ComputableInPolyTime part input encBits)
    (hb : ComputableInPolyTime bas input (encList encBits)) :
    ComputableInPolyTime (fun x => AffineBasis.mk (part x) (bas x)) input encAffineBasis :=
  (hp.prod hb).of_enc_eq fun _ => rfl

/-- Reading `particular` from an `AffineBasis` runs in polynomial time. -/
@[fun_prop]
theorem AffineBasis.isPolyTime_particular {α : Type} {input : α ↪ List Bool}
    {st : α → AffineBasis} (h : ComputableInPolyTime st input encAffineBasis) :
    ComputableInPolyTime (fun x => (st x).particular) input encBits :=
  ((ComputableInPolyTime.of_eq (encIn := encAffineBasis)
    (encOut := encPair encBits (encList encBits))
    (f := fun b : AffineBasis => (b.particular, b.basis)) fun _ => rfl).fst').comp h

/-- Reading `basis` from an `AffineBasis` runs in polynomial time. -/
@[fun_prop]
theorem AffineBasis.isPolyTime_basis {α : Type} {input : α ↪ List Bool}
    {st : α → AffineBasis} (h : ComputableInPolyTime st input encAffineBasis) :
    ComputableInPolyTime (fun x => (st x).basis) input (encList encBits) :=
  ((ComputableInPolyTime.of_eq (encIn := encAffineBasis)
    (encOut := encPair encBits (encList encBits))
    (f := fun b : AffineBasis => (b.particular, b.basis)) fun _ => rfl).snd').comp h

/-- One row step of affine Gaussian elimination over `𝔽₂`: find a kernel spanning vector `p` with
`a ⬝ p = 1`; if found, adjust `particular` when needed and clear `a ⬝ u` across `basis`. -/
@[expose] def affineRowStep (st : AffineBasis) (e : Row) : AffineBasis :=
  let opt := st.basis.find? (fun u => listDot e.coeffs u)
  let p := opt.getD []
  if opt.isSome then
    { particular :=
        if xor (listDot e.coeffs st.particular) e.rhs then
          st.particular.zipWith Bool.xor p
        else st.particular
      basis := st.basis.map (fun u =>
        if listDot e.coeffs u then u.zipWith Bool.xor p else u) }
  else st

/-- `affineRowStep` runs in deterministic polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_affineRowStep :
    ComputableInPolyTime (fun q : AffineBasis × Row => affineRowStep q.1 q.2)
      (encPair encAffineBasis encRow) encAffineBasis := by
  have hopt : ComputableInPolyTime
      (fun q : AffineBasis × Row => q.1.basis.find? (fun u => listDot q.2.coeffs u))
      (encPair encAffineBasis encRow) (encOption encBits) :=
    ComputableInPolyTime.findWithInput (by fun_prop) (by fun_prop)
  have hp : ComputableInPolyTime
      (fun q : AffineBasis × Row => (q.1.basis.find? (fun u => listDot q.2.coeffs u)).getD [])
      (encPair encAffineBasis encRow) encBits :=
    ComputableInPolyTime.optionGetDWithInput hopt (.const [])
  have hpart : ComputableInPolyTime
      (fun q : AffineBasis × Row =>
        if xor (listDot q.2.coeffs q.1.particular) q.2.rhs then
          q.1.particular.zipWith Bool.xor
            ((q.1.basis.find? (fun u => listDot q.2.coeffs u)).getD [])
        else q.1.particular)
      (encPair encAffineBasis encRow) encBits :=
    ComputableInPolyTime.ite (by fun_prop)
      (ComputableInPolyTime.bitsZipWithInput Bool.xor (by fun_prop) hp) (by fun_prop)
  have hbas : ComputableInPolyTime
      (fun q : AffineBasis × Row =>
        q.1.basis.map (fun u =>
          if listDot q.2.coeffs u then
            u.zipWith Bool.xor ((q.1.basis.find? (fun u => listDot q.2.coeffs u)).getD [])
          else u))
      (encPair encAffineBasis encRow) (encList encBits) := by
    refine ComputableInPolyTime.mapWithInput (by fun_prop) ?_
    refine ComputableInPolyTime.ite (by fun_prop) ?_ (by fun_prop)
    exact ComputableInPolyTime.bitsZipWithInput Bool.xor (by fun_prop)
      (hp.comp (ComputableInPolyTime.fst _ _))
  unfold affineRowStep
  exact ComputableInPolyTime.ite (ComputableInPolyTime.optionIsSome hopt)
    (AffineBasis.isPolyTime_mk hpart hbas) (by fun_prop)

private theorem length_encList_bits_map_le (f : List Bool → List Bool)
    (hf : ∀ u, (f u).length ≤ u.length) (l : List (List Bool)) :
    (encList encBits (l.map f)).length ≤ (encList encBits l).length := by
  induction l with
  | nil => rfl
  | cons u l ih =>
    have hu := hf u
    enc_len [List.map_cons] at *

/-- `affineRowStep` never increases the encoded bit length of `AffineBasis`. -/
theorem length_encAffineBasis_step_le (st : AffineBasis) (e : Row) :
    (encAffineBasis (affineRowStep st e)).length ≤ (encAffineBasis st).length := by
  unfold affineRowStep
  dsimp only
  split_ifs with hsome herr
  · have hp : (st.particular.zipWith Bool.xor
        ((st.basis.find? (fun u => listDot e.coeffs u)).getD [])).length ≤
        st.particular.length := by
      rw [List.length_zipWith]; exact Nat.min_le_left _ _
    have hbas := length_encList_bits_map_le
      (fun u => if listDot e.coeffs u then
        u.zipWith Bool.xor ((st.basis.find? (fun u => listDot e.coeffs u)).getD []) else u)
      (fun u => by split_ifs <;> simp [List.length_zipWith])
      st.basis
    rw [encAffineBasis_apply, encAffineBasis_apply]
    enc_len
  · have hbas := length_encList_bits_map_le
      (fun u => if listDot e.coeffs u then
        u.zipWith Bool.xor ((st.basis.find? (fun u => listDot e.coeffs u)).getD []) else u)
      (fun u => by split_ifs <;> simp [List.length_zipWith])
      st.basis
    rw [encAffineBasis_apply, encAffineBasis_apply]
    enc_len
  · exact le_rfl

/-- Initial `AffineBasis` of width `n`: zero particular vector and standard unit basis vectors. -/
@[expose] def initAffineBasis (n : ℕ) : AffineBasis where
  particular := List.replicate n false
  basis := listSingles n

/-- Full affine Gaussian elimination over `𝔽₂` on a dense `XORSAT.Dense.Input`. -/
@[expose] def affineSolve (q : Input) : AffineBasis :=
  q.rows.foldl affineRowStep (initAffineBasis q.width)

private theorem length_foldl_affineRowStep_le (rows : List Row) (st : AffineBasis) :
    (encAffineBasis (rows.foldl affineRowStep st)).length ≤ (encAffineBasis st).length := by
  induction rows generalizing st with
  | nil => exact le_rfl
  | cons e rs ih =>
    rw [List.foldl_cons]
    exact (ih (affineRowStep st e)).trans (length_encAffineBasis_step_le st e)

/-- `affineSolve` runs in deterministic polynomial time on multi-tape Turing machines. -/
@[fun_prop]
theorem computableInPolyTime_affineSolve :
    ComputableInPolyTime affineSolve encInput encAffineBasis := by
  have hinit : ComputableInPolyTime (fun q : Input => initAffineBasis q.width)
      encInput encAffineBasis := by
    unfold initAffineBasis
    exact AffineBasis.isPolyTime_mk
      ((ComputableInPolyTime.bitsReplicate false).comp (by fun_prop))
      (ComputableInPolyTime.bitsSingles.comp (by fun_prop))
  unfold affineSolve
  exact ComputableInPolyTime.foldl' (by fun_prop) hinit computableInPolyTime_affineRowStep
    hinit.polyBounded_length fun q i _ =>
      length_foldl_affineRowStep_le (q.rows.take i) (initAffineBasis q.width)

/-- Algebraic invariant stating that `st : AffineBasis` has width `n`, `st.particular` satisfies
every equation in `R`, `st.basis` lies in the homogeneous kernel of `R`, and every solution in
`BitString n` to `R` lies in the affine span of `st`. -/
@[expose] def IsAffineSpanning (n : ℕ) (R : List Row) (st : AffineBasis) : Prop :=
  st.particular.length = n ∧
  st.basis.length = n ∧
  (∀ u ∈ st.basis, u.length = n) ∧
  (∀ r ∈ R, ofList n r.coeffs ⬝ᵥ ofList n st.particular = r.rhs) ∧
  (∀ r ∈ R, ∀ u ∈ st.basis, ofList n r.coeffs ⬝ᵥ ofList n u = false) ∧
  (∀ x : BitString n,
    (∀ r ∈ R, ofList n r.coeffs ⬝ᵥ x = r.rhs) →
    ∃ w : BitString n,
      x = ofList n st.particular +
        ∑ i : Fin n, if w i then ofList n (st.basis.getD i.1 []) else 0)

/-- `initAffineBasis n` satisfies `IsAffineSpanning n []`. -/
theorem isAffineSpanning_init (n : ℕ) : IsAffineSpanning n [] (initAffineBasis n) := by
  refine ⟨by simp [initAffineBasis], by simp [initAffineBasis, listSingles], ?_,
    by simp, by simp, fun x _ => ⟨x, ?_⟩⟩
  · intro u hu
    simp only [initAffineBasis, listSingles, List.mem_map, List.mem_range] at hu
    obtain ⟨i, _, rfl⟩ := hu
    simp [listSingle]
  · have hzero : ofList n (initAffineBasis n).particular = 0 := by
      funext i
      simp [initAffineBasis, ofList, Bool.zero_eq_false]
    rw [hzero, zero_add]
    funext j
    rw [Finset.sum_apply]
    have hget : ∀ i : Fin n,
        ofList n ((initAffineBasis n).basis.getD i.1 []) = Pi.single i true := by
      intro i
      have heq : (listSingles n).getD i.1 [] = listSingle n i.1 := by
        simp [listSingles, List.getD_eq_getElem?_getD, i.2]
      rw [initAffineBasis, heq, listSingle_eq_ofFn_single i, ofList_ofFn]
    simp_rw [hget]
    have hterm : ∀ i : Fin n,
        (if x i = true then (Pi.single i true : BitString n) else 0) j =
          if i = j then x j else 0 := by
      intro i
      by_cases hij : i = j
      · subst hij
        cases x i <;> simp [Bool.zero_eq_false]
      · cases x i <;> simp [hij, Bool.zero_eq_false]
    simp_rw [hterm]
    simp

/-- `affineRowStep` preserves `IsAffineSpanning` whenever the extended system `R ++ [e]` admits at
least one solution `x₀ : BitString n` and `e.coeffs.length = n`. -/
theorem IsAffineSpanning.step {n : ℕ} {R : List Row} {st : AffineBasis} {e : Row}
    (hst : IsAffineSpanning n R st) (he : e.coeffs.length = n)
    {x₀ : BitString n} (hx₀R : ∀ r ∈ R, ofList n r.coeffs ⬝ᵥ x₀ = r.rhs)
    (hx₀e : ofList n e.coeffs ⬝ᵥ x₀ = e.rhs) :
    IsAffineSpanning n (R ++ [e]) (affineRowStep st e) := by
  rcases hst with ⟨hplen, hblen, humem, hpartR, hbasR, hspan⟩
  unfold affineRowStep
  cases hfind : st.basis.find? (fun u => listDot e.coeffs u) with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    have hbas_e : ∀ u ∈ st.basis, ofList n e.coeffs ⬝ᵥ ofList n u = false := by
      intro u hu
      have hnot := List.find?_eq_none.mp hfind u hu
      rw [listDot_eq_dotProduct he (humem u hu)] at hnot
      exact Bool.eq_false_iff.mpr hnot
    have hget_e : ∀ i : Fin n,
        ofList n e.coeffs ⬝ᵥ ofList n (st.basis.getD i.1 []) = false := by
      intro i
      have hi : i.1 < st.basis.length := by simp [hblen]
      have hmem : st.basis.getD i.1 [] ∈ st.basis := by
        have hg : st.basis.getD i.1 [] = st.basis[i.1] := by
          simp [List.getD_eq_getElem?_getD, hi]
        rw [hg]
        exact List.getElem_mem hi
      exact hbas_e _ hmem
    obtain ⟨w₀, hw₀⟩ := hspan x₀ hx₀R
    have hpart_e : ofList n e.coeffs ⬝ᵥ ofList n st.particular = e.rhs := by
      have hdot := congrArg (fun v => ofList n e.coeffs ⬝ᵥ v) hw₀
      rw [hx₀e, dotProduct_add, dotProduct_sum] at hdot
      have hsum0 : (∑ i : Fin n,
          ofList n e.coeffs ⬝ᵥ (if w₀ i = true then ofList n (st.basis.getD i.1 []) else 0)) =
          false := by
        refine Finset.sum_eq_zero fun i _ => ?_
        split_ifs
        · exact hget_e i
        · simp [Bool.zero_eq_false]
      rw [hsum0, show (false : Bool) = 0 from rfl, add_zero] at hdot
      exact hdot.symm
    refine ⟨hplen, hblen, humem, ?_, ?_, fun x hx => hspan x fun r hr =>
      hx r (List.mem_append_left _ hr)⟩
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hpartR r hr
      · rw [List.mem_singleton.mp hr]; exact hpart_e
    · intro r hr u hu
      rcases List.mem_append.mp hr with hr | hr
      · exact hbasR r hr u hu
      · rw [List.mem_singleton.mp hr]; exact hbas_e u hu
  | some p =>
    simp only [Option.isSome_some, ↓reduceIte, Option.getD_some]
    have hpmem : p ∈ st.basis := List.mem_of_find?_eq_some hfind
    have hp_len : p.length = n := humem p hpmem
    have hp_dot : ofList n e.coeffs ⬝ᵥ ofList n p = true := by
      have hs := List.find?_some hfind
      rwa [listDot_eq_dotProduct he hp_len] at hs
    let err : Bool := xor (listDot e.coeffs st.particular) e.rhs
    let part' : List Bool := if err then st.particular.zipWith Bool.xor p else st.particular
    let f : List Bool → List Bool := fun u =>
      if listDot e.coeffs u then u.zipWith Bool.xor p else u
    have hpart'_len : part'.length = n := by
      dsimp [part']
      split_ifs <;> simp [hplen, hp_len]
    have hf_len : ∀ u ∈ st.basis, (f u).length = n := by
      intro u hu
      dsimp [f]
      split_ifs <;> simp [humem u hu, hp_len]
    have hof_part' : ofList n part' =
        ofList n st.particular + (if err then ofList n p else 0) := by
      dsimp [part']
      split_ifs with h
      · have hfn := ofFn_add (ofList n st.particular) (ofList n p)
        rw [ofFn_ofList hplen, ofFn_ofList hp_len] at hfn
        rw [← hfn, ofList_ofFn]
      · rw [add_zero]
    have hof_f : ∀ u ∈ st.basis,
        ofList n (f u) = ofList n u + (if listDot e.coeffs u then ofList n p else 0) := by
      intro u hu
      dsimp [f]
      split_ifs with h
      · have hfn := ofFn_add (ofList n u) (ofList n p)
        rw [ofFn_ofList (humem u hu), ofFn_ofList hp_len] at hfn
        rw [← hfn, ofList_ofFn]
      · rw [add_zero]
    have hpart'_e : ofList n e.coeffs ⬝ᵥ ofList n part' = e.rhs := by
      rw [hof_part', dotProduct_add]
      have hd0 : listDot e.coeffs st.particular = ofList n e.coeffs ⬝ᵥ ofList n st.particular :=
        listDot_eq_dotProduct he hplen
      dsimp [err]
      simp only [hd0]
      cases h1 : ofList n e.coeffs ⬝ᵥ ofList n st.particular <;> cases h2 : e.rhs <;>
        simp [hp_dot, Bool.add_eq_xor, Bool.zero_eq_false]
    have hf_e : ∀ u ∈ st.basis, ofList n e.coeffs ⬝ᵥ ofList n (f u) = false := by
      intro u hu
      rw [hof_f u hu, dotProduct_add]
      have hdu : listDot e.coeffs u = ofList n e.coeffs ⬝ᵥ ofList n u :=
        listDot_eq_dotProduct he (humem u hu)
      simp only [hdu]
      cases h1 : ofList n e.coeffs ⬝ᵥ ofList n u <;>
        simp [hp_dot, Bool.add_eq_xor, Bool.zero_eq_false]
    refine ⟨hpart'_len, by simp [hblen], ?_, ?_, ?_, ?_⟩
    · intro u' hu'
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hu'
      exact hf_len u hu
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · rw [hof_part', dotProduct_add, hpartR r hr]
        split_ifs
        · rw [hbasR r hr p hpmem, show (false : Bool) = 0 from rfl, add_zero]
        · simp
      · rw [List.mem_singleton.mp hr]; exact hpart'_e
    · intro r hr u' hu'
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hu'
      rcases List.mem_append.mp hr with hr | hr
      · rw [hof_f u hu, dotProduct_add, hbasR r hr u hu]
        split_ifs
        · rw [hbasR r hr p hpmem, show (false : Bool) = 0 from rfl, add_zero]
        · simp
      · rw [List.mem_singleton.mp hr]; exact hf_e u hu
    · intro x hx
      obtain ⟨w, hw⟩ := hspan x (fun r hr => hx r (List.mem_append_left _ hr))
      refine ⟨w, ?_⟩
      have hget_map : ∀ i : Fin n,
          (st.basis.map f).getD i.1 [] = f (st.basis.getD i.1 []) := by
        intro i
        have hi : i.1 < st.basis.length := by simp [hblen]
        simp [List.getD_eq_getElem?_getD, hi]
      have hmem_i : ∀ i : Fin n, st.basis.getD i.1 [] ∈ st.basis := by
        intro i
        have hi : i.1 < st.basis.length := by simp [hblen]
        have hg : st.basis.getD i.1 [] = st.basis[i.1] := by
          simp [List.getD_eq_getElem?_getD, hi]
        rw [hg]
        exact List.getElem_mem hi
      let rhsVec : BitString n :=
        ofList n part' + ∑ i : Fin n, if w i then ofList n ((st.basis.map f).getD i.1 []) else 0
      let β : Bool := err + ∑ i : Fin n,
        if w i then listDot e.coeffs (st.basis.getD i.1 []) else 0
      have hdiff : x = rhsVec + (if β then ofList n p else 0) := by
        have hscale : ∀ b : Bool, (if b then ofList n p else (0 : BitString n)) =
            fun j => b * ofList n p j := by
          intro b; funext j
          cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Pi.zero_apply] <;>
            (generalize ofList n p j = v; cases v <;> rfl)
        rw [hw]
        dsimp [rhsVec, β]
        rw [hof_part']
        simp_rw [hget_map]
        have hsum_split : (∑ i : Fin n,
            if w i = true then ofList n (f (st.basis.getD i.1 [])) else 0) =
            (∑ i : Fin n, if w i = true then ofList n (st.basis.getD i.1 []) else 0) +
            ∑ i : Fin n,
              if (if w i = true then listDot e.coeffs (st.basis.getD i.1 []) else (0 : Bool)) =
                true then ofList n p else 0 := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hof_f _ (hmem_i i)]
          cases w i <;> cases listDot e.coeffs (st.basis.getD i.1 []) <;>
            simp [Bool.zero_eq_false]
        rw [hsum_split]
        funext j
        simp only [Pi.add_apply, Finset.sum_apply, hscale, ← Finset.sum_mul]
        rw [add_mul]
        generalize ofList n st.particular j = A
        generalize (∑ c : Fin n, (if w c = true then ofList n (st.basis.getD c.1 []) else 0) j) = B
        generalize (∑ i : Fin n,
          if w i = true then listDot e.coeffs (st.basis.getD i.1 []) else 0) = S
        generalize ofList n p j = P
        cases A <;> cases B <;> cases err <;> cases S <;> cases P <;> decide
      have hxe : ofList n e.coeffs ⬝ᵥ x = e.rhs :=
        hx e (List.mem_append_right _ (List.mem_singleton_self e))
      have hrhs_e : ofList n e.coeffs ⬝ᵥ rhsVec = e.rhs := by
        dsimp [rhsVec]
        rw [dotProduct_add, hpart'_e, dotProduct_sum]
        have hz : (∑ x_1 : Fin n, ofList n e.coeffs ⬝ᵥ
            if w x_1 = true then ofList n ((st.basis.map f).getD x_1.1 []) else 0) = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [hget_map]
          split_ifs
          · exact hf_e _ (hmem_i i)
          · simp [Bool.zero_eq_false]
        rw [hz, add_zero]
      have hβ : β = false := by
        have hdot := congrArg (fun v => ofList n e.coeffs ⬝ᵥ v) hdiff
        rw [hxe, dotProduct_add, hrhs_e] at hdot
        cases hβv : β
        · rfl
        · simp only [hβv, ↓reduceIte, hp_dot] at hdot
          cases hr : e.rhs <;> simp [hr, Bool.add_eq_xor] at hdot
      have hzero_ite :
          (if (false : Bool) = true then ofList n p else 0) = (0 : BitString n) := rfl
      rw [hdiff, hβ, hzero_ite, add_zero]

/-- On any dense `𝔽₂` system `q` of width `q.width` admitting a solution `x₀ : BitString q.width`,
`affineSolve q` satisfies `IsAffineSpanning q.width q.rows`. -/
theorem isAffineSpanning_affineSolve {q : Input} (hw : Width q.width q.rows)
    {x₀ : BitString q.width} (hx₀ : ∀ r ∈ q.rows, ofList q.width r.coeffs ⬝ᵥ x₀ = r.rhs) :
    IsAffineSpanning q.width q.rows (affineSolve q) := by
  unfold affineSolve
  have hgen : ∀ (rows : List Row),
      (∀ r ∈ rows, r.coeffs.length = q.width) →
      (∀ r ∈ rows, ofList q.width r.coeffs ⬝ᵥ x₀ = r.rhs) →
      IsAffineSpanning q.width rows (rows.foldl affineRowStep (initAffineBasis q.width)) := by
    intro rows
    induction rows using List.reverseRecOn with
    | nil => intros; exact isAffineSpanning_init q.width
    | append_singleton R e ih =>
      intro hw' hx'
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact (ih (fun r hr => hw' r (List.mem_append_left _ hr))
        (fun r hr => hx' r (List.mem_append_left _ hr))).step
        (hw' e (List.mem_append_right _ (List.mem_singleton_self e)))
        (fun r hr => hx' r (List.mem_append_left _ hr))
        (hx' e (List.mem_append_right _ (List.mem_singleton_self e)))
  exact hgen q.rows hw hx₀

/-- On any homogeneous dense `𝔽₂` system `q` (`∀ r ∈ q.rows, r.rhs = false`) of width `q.width`,
`affineSolve q` satisfies `IsAffineSpanning` unconditionally. -/
theorem isAffineSpanning_affineSolve_homogeneous {q : Input} (hw : Width q.width q.rows)
    (hhom : ∀ r ∈ q.rows, r.rhs = false) :
    IsAffineSpanning q.width q.rows (affineSolve q) :=
  isAffineSpanning_affineSolve hw (x₀ := 0) fun r hr => by
    rw [hhom r hr]
    simp [Bool.zero_eq_false]

/-- Reconstruct an affine combination `particular ⊕ ⨁_{i : w_i = 1} basis_i` as a `List Bool` of
length `q.width`. -/
@[expose] def evalAffineBasis (width : ℕ) (st : AffineBasis) (w : List Bool) : List Bool :=
  st.particular.zipWith Bool.xor (listXorSelected width w st.basis)

/-- `evalAffineBasis` runs in deterministic polynomial time. -/
@[fun_prop]
theorem isPolyTime_evalAffineBasis {α : Type} {input : α ↪ List Bool}
    {width : α → ℕ} {st : α → AffineBasis} {w : α → List Bool}
    (hw : ComputableInPolyTime width input encUnary)
    (hst : ComputableInPolyTime st input encAffineBasis)
    (hsel : ComputableInPolyTime w input encBits) :
    ComputableInPolyTime (fun x => evalAffineBasis (width x) (st x) (w x)) input encBits := by
  unfold evalAffineBasis
  exact ComputableInPolyTime.bitsZipWithInput Bool.xor (by fun_prop)
    (ComputableInPolyTime.bitsXorSelected.comp (hw.prod (hsel.prod (by fun_prop))))

/-- On an `AffineBasis` of width `n` and selector `w : BitString n`, `evalAffineBasis` produces
the exact `List.ofFn` serialization of `v₀ + ∑ i, if w i then u_i else 0`. -/
theorem evalAffineBasis_eq_ofFn {n : ℕ} {st : AffineBasis} (hplen : st.particular.length = n)
    (hblen : st.basis.length = n) (humem : ∀ u ∈ st.basis, u.length = n) (w : BitString n) :
    evalAffineBasis n st (List.ofFn w) =
      List.ofFn (ofList n st.particular +
        ∑ i : Fin n, if w i then ofList n (st.basis.getD i.1 []) else 0) := by
  have hbas_ofFn : st.basis =
      List.ofFn (fun i : Fin n => List.ofFn (ofList n (st.basis.getD i.1 []))) := by
    apply List.ext_getElem (by simp [hblen])
    intro i hi _
    have hmem : st.basis[i] ∈ st.basis := List.getElem_mem hi
    have hg : st.basis.getD i [] = st.basis[i] := by
      simp [List.getD_eq_getElem?_getD, hi]
    simp only [List.getElem_ofFn, hg]
    exact (ofFn_ofList (humem _ hmem)).symm
  unfold evalAffineBasis
  conv_lhs => rw [hbas_ofFn]
  rw [listXorSelected_eq_ofFn_sum, ← ofFn_ofList hplen, ← ofFn_add, ofList_ofFn]

/-- Uniform strict-PPT sampler for solutions of a dense `𝔽₂` linear system: solve via `affineSolve`
and combine `basis` with `q.width` uniform fair bits. -/
@[expose] noncomputable def sampleAffineSolution (q : Input) : ProbComp (List Bool) :=
  (fun w => evalAffineBasis q.width (affineSolve q) w) <$> sampleList q.width

/-- `sampleAffineSolution` is a uniform strict probabilistic polynomial-time program (`IsPPTOn`).
-/
@[fun_prop]
theorem isPPTOn_sampleAffineSolution :
    IsPPTOn encInput encBits sampleAffineSolution := by
  unfold sampleAffineSolution
  exact IsPPTOn.of_seeded (count := Input.width) (by fun_prop)
    (isPolyTime_evalAffineBasis
      (width := fun p : Input × List Bool => p.1.width)
      (st := fun p : Input × List Bool => affineSolve p.1)
      (w := Prod.snd)
      (by fun_prop)
      (computableInPolyTime_affineSolve.comp (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.snd _ _))

/-- Fiber uniformity for additive group homomorphisms out of `BitString n`: for every
`θ : BitString n →+ G` into a finite additive group with decidable equality and every `y` in the
image of `θ`, `|{w | θ w = y}| * |(univ.image θ)| = 2 ^ n`. -/
theorem card_addHom_fiber_mul_image {n : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]
    (θ : BitString n →+ G) {y : G} (hy : y ∈ (Finset.univ : Finset (BitString n)).image θ) :
    ((Finset.univ : Finset (BitString n)).filter (fun w => θ w = y)).card *
      ((Finset.univ : Finset (BitString n)).image θ).card = 2 ^ n := by
  obtain ⟨w₀, _, rfl⟩ := Finset.mem_image.mp hy
  have hfib_eq : ∀ z ∈ (Finset.univ : Finset (BitString n)).image θ,
      ((Finset.univ : Finset (BitString n)).filter (fun w => θ w = z)).card =
        ((Finset.univ : Finset (BitString n)).filter (fun w => θ w = θ w₀)).card := by
    intro z hz
    obtain ⟨w₁, _, rfl⟩ := Finset.mem_image.mp hz
    exact AddMonoidHom.card_fiber_eq_of_mem_range θ ⟨w₁, rfl⟩ ⟨w₀, rfl⟩
  have hpart : (Finset.univ : Finset (BitString n)).card =
      ∑ z ∈ (Finset.univ : Finset (BitString n)).image θ,
        ((Finset.univ : Finset (BitString n)).filter (fun w => θ w = z)).card :=
    Finset.card_eq_sum_card_image θ Finset.univ
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at hpart
  rw [Finset.sum_congr rfl hfib_eq, Finset.sum_const, smul_eq_mul, mul_comm] at hpart
  exact hpart.symm

end CslibFrontier.Complexity.XORSAT.Dense
