module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Determinant
public import CslibFrontier.Computability.Circuit.Arithmetic.VNP
import CslibFrontier.Computability.Circuit.Arithmetic.Permanent.TreePlace
import CslibFrontier.Computability.Circuit.Arithmetic.Permanent
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# VNP-Completeness of the Permanent

Proves that over any field `K` of characteristic other than `2`, the generic permanent family
`permFamily K` is `VNP`-complete under `p`-projections (`Cslib.Circuits.Arithmetic.IsVNPComplete`),
combining homogeneous circuit decomposition and interval-tree clause-sum encoding with inverse
parse-tree extraction.

## Main results

* `CslibFrontier.Computability.Circuit.Arithmetic.Permanent.permFamily_isVNPComplete`: over any
  field `K` with `(2 : K) ≠ 0`, `permFamily K` is `VNP`-complete under `p`-projections.
-/

public section

namespace CslibFrontier.Computability.Circuit.Arithmetic.Permanent

open Cslib Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial Finset

universe u

section TreeExtraction

variable {K : Type u} [CommSemiring K] {n m s d : ℕ}

/-- Extract the unique `PTree` from a valid assignment `F` on an active interval `[lo, lo + k]`. -/
private def extractPTree (p : Program (arithSignature K) (n + m) s) (v_out : Wire (n + m) s)
    (F : ∀ x : TreeDom m d, TreeVal (n + m) s d x) (hF : IsValidAssign p v_out F) :
    ∀ (k lo : ℕ) (hhi : lo + k < d),
      F (.par ⟨lo, by omega⟩ ⟨lo + k, hhi⟩) ≠ .none → PTree (n + m) s k
  | 0, lo, hhi, hact =>
      let loF : Fin d := ⟨lo, by omega⟩
      have hsome : F (.leafVar loF) ≠ none := fun h => hact ((hF.2.2.2.2.2.2.2.1 loF).2 h)
      .leaf (Option.get _ (Option.isSome_iff_ne_none.2 hsome))
  | k + 1, lo, hhi, hact =>
      let loF : Fin d := ⟨lo, by omega⟩
      let hiF : Fin d := ⟨lo + k + 1, hhi⟩
      have hlt : loF.1 < hiF.1 := by dsimp [loF, hiF]; omega
      have hsne : F (.split loF hiF) ≠ none := fun h => hact ((hF.2.2.2.1 loF hiF hlt).2 h)
      have hgne : F (.gate loF hiF) ≠ none := fun h => hact ((hF.2.2.2.2.2.1 loF hiF hlt).2 h)
      let q : Fin d := Option.get _ (Option.isSome_iff_ne_none.2 hsne)
      let g : Fin s := Option.get _ (Option.isSome_iff_ne_none.2 hgne)
      have hqeq : F (.split loF hiF) = some q := (Option.some_get _).symm
      have hqrange : lo ≤ q.1 ∧ q.1 < lo + k + 1 :=
        hF.2.2.2.2.2.2.2.2.2.2.2.1 loF hiF q hqeq
      let a : Fin (k + 1) := ⟨q.1 - lo, by omega⟩
      have hLact : F (.par ⟨lo, by omega⟩ ⟨lo + a.1, by omega⟩) ≠ .none := by
        have hpl := (hF.2.2.2.2.2.2.2.2.2.2.2.2.1 loF hiF q hqrange.1 hqrange.2).1 hqeq
        have hqf : (⟨lo + a.1, by omega⟩ : Fin d) = q := Fin.ext (by dsimp [a]; omega)
        rw [hqf, hpl]; simp
      have hRact :
          F (.par ⟨lo + a.1 + 1, by omega⟩ ⟨lo + a.1 + 1 + (k - a.1), by omega⟩) ≠ .none := by
        have hpr := (hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1 loF hiF q hqrange.2 hqrange.1).1 hqeq
        have hl : (⟨lo + a.1 + 1, by omega⟩ : Fin d) = ⟨q.1 + 1, by omega⟩ :=
          Fin.ext (by dsimp [a]; omega)
        have hr : (⟨lo + a.1 + 1 + (k - a.1), by omega⟩ : Fin d) = hiF :=
          Fin.ext (by dsimp [a, hiF]; omega)
        rw [hl, hr, hpr]; simp
      .node g a
        (extractPTree p v_out F hF a.1 lo (by omega) hLact)
        (extractPTree p v_out F hF (k - a.1) (lo + a.1 + 1) (by omega) hRact)
termination_by k => k
decreasing_by
  · exact a.2
  · omega

omit [CommSemiring K] in
/-- Every valid assignment `F` with `F .rootDeg = 0` equals `assignZero`. -/
private theorem eq_assignZero_of_rootDeg_zero (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (F : ∀ x : TreeDom m d, TreeVal (n + m) s d x)
    (hF : IsValidAssign p v_out F) (h0 : F .rootDeg = 0) :
    F = assignZero (fun b => F (.boolVar b)) := by
  have hpar_none : ∀ gap : ℕ, ∀ l r : Fin d, d - (r.1 - l.1) = gap → F (.par l r) = .none := by
    intro gap
    induction gap using Nat.strong_induction_on with
    | ind gap ih =>
        intro l r hgap
        by_cases hrl : r.1 < l.1
        · exact hF.2.2.2.2.2.2.2.2.1 l r hrl
        · cases hp : F (.par l r) with
          | none => rfl
          | root =>
              have hr := ((hF.1 l r).1 hp).2
              rw [h0] at hr; simp at hr
          | leftOf r' =>
              have hlt : r.1 < r'.1 := hF.2.2.2.2.2.2.2.2.2.1 l r r' hp
              have hsp := (hF.2.2.2.2.2.2.2.2.2.2.2.2.1 l r' r (by omega) hlt).2 hp
              have hpar' : F (.par l r') = .none := ih (d - (r'.1 - l.1)) (by omega) l r' rfl
              have hsp_none := (hF.2.2.2.1 l r' (by omega)).1 hpar'
              rw [hsp_none] at hsp; cases hsp
          | rightOf l' =>
              have hlt : l'.1 < l.1 := hF.2.2.2.2.2.2.2.2.2.2.1 l r l' hp
              let q : Fin d := ⟨l.1 - 1, by omega⟩
              have hq1 : l'.1 ≤ q.1 := by dsimp [q]; omega
              have hq2 : q.1 < r.1 := by dsimp [q]; omega
              have hleq : (⟨q.1 + 1, by omega⟩ : Fin d) = l := Fin.ext (by dsimp [q]; omega)
              have hsp := (hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1 l' r q hq2 hq1).2 (by rwa [hleq])
              have hpar' : F (.par l' r) = .none := ih (d - (r.1 - l'.1)) (by omega) l' r rfl
              have hsp_none := (hF.2.2.2.1 l' r (by omega)).1 hpar'
              rw [hsp_none] at hsp; cases hsp
  have hpn : ∀ l r : Fin d, F (.par l r) = .none := fun l r => hpar_none _ l r rfl
  funext x
  cases x with
  | boolVar b => rfl
  | rootDeg => exact h0
  | par l r => exact hpn l r
  | wire l r => exact (hF.2.2.1 l r).1 (hpn l r)
  | split l r =>
      by_cases hlr : l.1 < r.1
      · exact (hF.2.2.2.1 l r hlr).1 (hpn l r)
      · exact hF.2.2.2.2.1 l r hlr
  | gate l r =>
      by_cases hlr : l.1 < r.1
      · exact (hF.2.2.2.2.2.1 l r hlr).1 (hpn l r)
      · exact hF.2.2.2.2.2.2.1 l r hlr
  | leafVar l => exact (hF.2.2.2.2.2.2.2.1 l).1 (hpn l l)

omit [CommSemiring K] in
/-- On any valid assignment `F`, `extractPTree` recovers a legal `PTree` matching `F` inside
`[lo, lo + k]` on all fields, given the laminar invariant on active intervals. -/
private theorem extractPTree_spec (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (F : ∀ x : TreeDom m d, TreeVal (n + m) s d x)
    (hF : IsValidAssign p v_out F) :
    ∀ (k lo : ℕ) (hhi : lo + k < d) (pk : ParKind d) (w : Wire (n + m) s)
      (hpar : F (.par ⟨lo, by omega⟩ ⟨lo + k, hhi⟩) = pk) (hpk : pk ≠ .none)
      (_hw : F (.wire ⟨lo, by omega⟩ ⟨lo + k, hhi⟩) = some w)
      (_hlam : ∀ l r : Fin d, F (.par l r) ≠ .none →
        (l.1 ≤ lo ∧ lo + k ≤ r.1) ∨ (lo ≤ l.1 ∧ r.1 ≤ lo + k) ∨ r.1 < lo ∨ lo + k < l.1)
      (_hanc : ∀ l r : Fin d, l.1 ≤ lo → lo + k ≤ r.1 → ¬ (l.1 = lo ∧ r.1 = lo + k) →
        ∀ q : Fin d, F (.split l r) = some q → q.1 < lo ∨ lo + k ≤ q.1)
      (_hroot : ∀ l r : Fin d, lo ≤ l.1 → r.1 ≤ lo + k → ¬ (l.1 = lo ∧ r.1 = lo + k) →
        F (.par l r) ≠ .root),
      let T := extractPTree p v_out F hF k lo hhi (by rw [hpar]; exact hpk)
      T.IsLegal p (fun b => F (.boolVar b)) ∧
      (∀ l r : Fin d, lo ≤ l.1 → r.1 ≤ lo + k →
        F (.par l r) = placePar p d lo hhi pk T l r ∧
        F (.wire l r) = placeWire p d lo hhi w T l r ∧
        F (.split l r) = placeSplit d lo hhi T l r ∧
        F (.gate l r) = placeGate d lo hhi T l r) ∧
      (∀ l : Fin d, lo ≤ l.1 → l.1 ≤ lo + k →
        F (.leafVar l) = placeLeaf d lo hhi T l) := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
      intro lo hhi pk w hpar hpk hw hlam hanc hroot
      cases k with
      | zero =>
          let loF : Fin d := ⟨lo, by omega⟩
          have hact : F (.par loF loF) ≠ .none := by simpa [loF] using hpar ▸ hpk
          have hsome : F (.leafVar loF) ≠ none := fun h => hact ((hF.2.2.2.2.2.2.2.1 loF).2 h)
          let j := Option.get _ (Option.isSome_iff_ne_none.2 hsome)
          have hj : F (.leafVar loF) = some j := (Option.some_get _).symm
          have hT_eq : extractPTree p v_out F hF 0 lo hhi hact = .leaf j := by
            unfold extractPTree; rfl
          rw [hT_eq]
          refine ⟨fun b hb => hF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 loF b (hb ▸ hj), ?_, ?_⟩
          · intro l r h1 h2
            by_cases hlr : l.1 = lo ∧ r.1 = lo
            · have hl : l = loF := Fin.ext hlr.1
              have hr : r = loF := Fin.ext hlr.2
              subst hl; subst hr
              refine ⟨?_, ?_, ?_, ?_⟩
              · simpa [loF] using hpar
              · simpa [loF] using hw
              · exact hF.2.2.2.2.1 loF loF (by omega)
              · exact hF.2.2.2.2.2.2.1 loF loF (by omega)
            · have hrl : r.1 < l.1 := by omega
              have hpn : F (.par l r) = .none := hF.2.2.2.2.2.2.2.2.1 l r hrl
              refine ⟨?_, ?_, ?_, ?_⟩
              · simpa [hlr] using hpn
              · simpa [hlr] using (hF.2.2.1 l r).1 hpn
              · exact hF.2.2.2.2.1 l r (by omega)
              · exact hF.2.2.2.2.2.2.1 l r (by omega)
          · intro l h1 h2
            have hl : l = loF := Fin.ext (by dsimp [loF]; omega)
            subst hl
            simpa [loF] using hj
      | succ k =>
          let loF : Fin d := ⟨lo, by omega⟩
          let hiF : Fin d := ⟨lo + k + 1, hhi⟩
          have hact : F (.par loF hiF) ≠ .none := by simpa [loF, hiF] using hpar ▸ hpk
          have hlt : loF.1 < hiF.1 := by dsimp [loF, hiF]; omega
          have hsne : F (.split loF hiF) ≠ none := fun h =>
            hact ((hF.2.2.2.1 loF hiF hlt).2 h)
          have hgne : F (.gate loF hiF) ≠ none := fun h =>
            hact ((hF.2.2.2.2.2.1 loF hiF hlt).2 h)
          let q : Fin d := Option.get _ (Option.isSome_iff_ne_none.2 hsne)
          let g : Fin s := Option.get _ (Option.isSome_iff_ne_none.2 hgne)
          have hqeq : F (.split loF hiF) = some q := (Option.some_get _).symm
          have hgeq : F (.gate loF hiF) = some g := (Option.some_get _).symm
          have hqrange : lo ≤ q.1 ∧ q.1 < lo + k + 1 :=
            hF.2.2.2.2.2.2.2.2.2.2.2.1 loF hiF q hqeq
          let a : Fin (k + 1) := ⟨q.1 - lo, by omega⟩
          have hqval : lo + a.1 = q.1 := by dsimp [a]; omega
          have hgmul : isMulGate p g = true := hF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 loF hiF g hgeq
          cases hmw : mulWires (p.lines g) with
          | none => simp [isMulGate_eq_isSome, hmw] at hgmul
          | some uv =>
              have hu : mulLeftWire p g = some uv.1 := by simp [mulLeftWire_eq_map, hmw]
              have hv : mulRightWire p g = some uv.2 := by simp [mulRightWire_eq_map, hmw]
              have hLpar : F (.par ⟨lo, by omega⟩ ⟨lo + a.1, by omega⟩) = .leftOf hiF := by
                have hpl := (hF.2.2.2.2.2.2.2.2.2.2.2.2.1 loF hiF q hqrange.1 hqrange.2).1 hqeq
                have hqf : (⟨lo + a.1, by omega⟩ : Fin d) = q := Fin.ext hqval
                rwa [hqf]
              have hRpar :
                  F (.par ⟨lo + a.1 + 1, by omega⟩ ⟨lo + a.1 + 1 + (k - a.1), by omega⟩) =
                    .rightOf loF := by
                have hpr := (hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1 loF hiF q hqrange.2 hqrange.1).1 hqeq
                have hl : (⟨lo + a.1 + 1, by omega⟩ : Fin d) = ⟨q.1 + 1, by omega⟩ :=
                  Fin.ext (by change lo + a.1 + 1 = q.1 + 1; omega)
                have hr : (⟨lo + a.1 + 1 + (k - a.1), by omega⟩ : Fin d) = hiF :=
                  Fin.ext (by dsimp [hiF]; omega)
                rwa [hl, hr]
              have hLw : F (.wire ⟨lo, by omega⟩ ⟨lo + a.1, by omega⟩) = some uv.1 := by
                have h := hF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 loF hiF q g hqrange.1 hqrange.2
                  hqeq hgeq
                have hqf : (⟨lo + a.1, by omega⟩ : Fin d) = q := Fin.ext hqval
                rw [hqf, h, hu]
              have hRw :
                  F (.wire ⟨lo + a.1 + 1, by omega⟩ ⟨lo + a.1 + 1 + (k - a.1), by omega⟩) =
                    some uv.2 := by
                have h := hF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 loF hiF q g hqrange.2 hqrange.1
                  hqeq hgeq
                have hl : (⟨lo + a.1 + 1, by omega⟩ : Fin d) = ⟨q.1 + 1, by omega⟩ :=
                  Fin.ext (by change lo + a.1 + 1 = q.1 + 1; omega)
                have hr : (⟨lo + a.1 + 1 + (k - a.1), by omega⟩ : Fin d) = hiF :=
                  Fin.ext (by dsimp [hiF]; omega)
                rw [hl, hr, h, hv]
              have hcross : ∀ gap : ℕ, ∀ l r : Fin d,
                  d - (r.1 - l.1) = gap →
                  lo ≤ l.1 → r.1 ≤ lo + k + 1 →
                  ¬ (l.1 = lo ∧ r.1 = lo + k + 1) →
                  l.1 ≤ lo + a.1 → lo + a.1 < r.1 →
                  F (.par l r) = .none := by
                intro gap
                induction gap using Nat.strong_induction_on with
                | ind gap ihg =>
                    intro l r hgap h1 h2 hnt h3 h4
                    cases hp : F (.par l r) with
                    | none => rfl
                    | root => exact absurd hp (hroot l r h1 h2 hnt)
                    | leftOf r' =>
                        have hlt' := hF.2.2.2.2.2.2.2.2.2.1 l r r' hp
                        have hsp := (hF.2.2.2.2.2.2.2.2.2.2.2.2.1 l r' r (by omega) hlt').2 hp
                        have hact' : F (.par l r') ≠ .none := fun h0 => by
                          have := (hF.2.2.2.1 l r' (by omega)).1 h0
                          rw [this] at hsp; cases hsp
                        rcases hlam l r' hact' with hbig | hin | hdisj1 | hdisj2
                        · by_cases htop' : l.1 = lo ∧ r'.1 = lo + k + 1
                          · have hle : l = loF := Fin.ext htop'.1
                            have hre : r' = hiF := Fin.ext htop'.2
                            rw [hle, hre, hqeq] at hsp
                            injection hsp with hqr
                            omega
                          · rcases hanc l r' hbig.1 hbig.2 htop' r hsp with hlt_lo | hge_hi
                            · omega
                            · exact absurd ⟨by omega, by omega⟩ hnt
                        · by_cases htop' : l.1 = lo ∧ r'.1 = lo + k + 1
                          · have hle : l = loF := Fin.ext htop'.1
                            have hre : r' = hiF := Fin.ext htop'.2
                            rw [hle, hre, hqeq] at hsp
                            injection hsp with hqr
                            omega
                          · exact absurd (ihg (d - (r'.1 - l.1)) (by omega) l r' rfl h1 hin.2 htop'
                              h3 (by omega)) hact'
                        · omega
                        · omega
                    | rightOf l' =>
                        have hlt' := hF.2.2.2.2.2.2.2.2.2.2.1 l r l' hp
                        let q' : Fin d := ⟨l.1 - 1, by omega⟩
                        have hq1' : l'.1 ≤ q'.1 := by dsimp [q']; omega
                        have hq2' : q'.1 < r.1 := by dsimp [q']; omega
                        have hleq : (⟨q'.1 + 1, by omega⟩ : Fin d) = l :=
                          Fin.ext (by dsimp [q']; omega)
                        have hsp := (hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1 l' r q' hq2' hq1').2
                          (by rwa [hleq])
                        have hact' : F (.par l' r) ≠ .none := fun h0 => by
                          have := (hF.2.2.2.1 l' r (by omega)).1 h0
                          rw [this] at hsp; cases hsp
                        rcases hlam l' r hact' with hbig | hin | hdisj1 | hdisj2
                        · by_cases htop' : l'.1 = lo ∧ r.1 = lo + k + 1
                          · have hle : l' = loF := Fin.ext htop'.1
                            have hre : r = hiF := Fin.ext htop'.2
                            rw [hle, hre, hqeq] at hsp
                            injection hsp with hqq'
                            have hq'v : q.1 = q'.1 := congrArg Fin.val hqq'
                            dsimp [q'] at hq'v; omega
                          · rcases hanc l' r hbig.1 hbig.2 htop' q' hsp with hlt_lo | hge_hi
                            · dsimp [q'] at hlt_lo; exact absurd ⟨by omega, by omega⟩ hnt
                            · dsimp [q'] at hge_hi; omega
                        · by_cases htop' : l'.1 = lo ∧ r.1 = lo + k + 1
                          · have hle : l' = loF := Fin.ext htop'.1
                            have hre : r = hiF := Fin.ext htop'.2
                            rw [hle, hre, hqeq] at hsp
                            injection hsp with hqq'
                            have hq'v : q.1 = q'.1 := congrArg Fin.val hqq'
                            dsimp [q'] at hq'v; omega
                          · exact absurd (ihg (d - (r.1 - l'.1)) (by omega) l' r rfl hin.1 h2 htop'
                              (by omega) h4) hact'
                        · omega
                        · omega
              have hlamL : ∀ l r : Fin d, F (.par l r) ≠ .none →
                  (l.1 ≤ lo ∧ lo + a.1 ≤ r.1) ∨ (lo ≤ l.1 ∧ r.1 ≤ lo + a.1) ∨
                    r.1 < lo ∨ lo + a.1 < l.1 := by
                intro l r hact'
                rcases hlam l r hact' with hbig | hin | hdisj1 | hdisj2
                · exact Or.inl ⟨hbig.1, by omega⟩
                · by_cases htop' : l.1 = lo ∧ r.1 = lo + k + 1
                  · exact Or.inl ⟨by omega, by omega⟩
                  · by_cases hr : r.1 ≤ lo + a.1
                    · exact Or.inr (Or.inl ⟨hin.1, hr⟩)
                    · by_cases hl : lo + a.1 < l.1
                      · exact Or.inr (Or.inr (Or.inr hl))
                      · exact absurd (hcross _ l r rfl hin.1 hin.2 htop' (by omega) (by omega))
                          hact'
                · exact Or.inr (Or.inr (Or.inl hdisj1))
                · exact Or.inr (Or.inr (Or.inr (by omega)))
              have hancL : ∀ l r : Fin d, l.1 ≤ lo → lo + a.1 ≤ r.1 →
                  ¬ (l.1 = lo ∧ r.1 = lo + a.1) →
                  ∀ q' : Fin d, F (.split l r) = some q' → q'.1 < lo ∨ lo + a.1 ≤ q'.1 := by
                intro l r hl hr hne q' hsp
                by_cases htop' : l.1 = lo ∧ r.1 = lo + k + 1
                · have hle : l = loF := Fin.ext htop'.1
                  have hre : r = hiF := Fin.ext htop'.2
                  rw [hle, hre, hqeq] at hsp
                  injection hsp with hqq'
                  right; rw [← hqq']; omega
                · have hact' : F (.par l r) ≠ .none := fun h0 => by
                    have hqr := hF.2.2.2.2.2.2.2.2.2.2.2.1 l r q' hsp
                    have := (hF.2.2.2.1 l r (by omega)).1 h0
                    rw [this] at hsp; cases hsp
                  rcases hlam l r hact' with hbig | hin | hdisj1 | hdisj2
                  · rcases hanc l r hbig.1 hbig.2 htop' q' hsp with h1 | h2
                    · exact Or.inl h1
                    · exact Or.inr (by omega)
                  · exact absurd (hcross _ l r rfl hin.1 hin.2 htop' (by omega) (by omega)) hact'
                  · omega
                  · omega
              have hlamR : ∀ l r : Fin d, F (.par l r) ≠ .none →
                  (l.1 ≤ lo + a.1 + 1 ∧ lo + a.1 + 1 + (k - a.1) ≤ r.1) ∨
                    (lo + a.1 + 1 ≤ l.1 ∧ r.1 ≤ lo + a.1 + 1 + (k - a.1)) ∨
                    r.1 < lo + a.1 + 1 ∨ lo + a.1 + 1 + (k - a.1) < l.1 := by
                intro l r hact'
                rcases hlam l r hact' with hbig | hin | hdisj1 | hdisj2
                · exact Or.inl ⟨by omega, by omega⟩
                · by_cases htop' : l.1 = lo ∧ r.1 = lo + k + 1
                  · exact Or.inl ⟨by omega, by omega⟩
                  · by_cases hl : lo + a.1 + 1 ≤ l.1
                    · exact Or.inr (Or.inl ⟨hl, by omega⟩)
                    · by_cases hr : r.1 < lo + a.1 + 1
                      · exact Or.inr (Or.inr (Or.inl hr))
                      · exact absurd (hcross _ l r rfl hin.1 hin.2 htop' (by omega) (by omega))
                          hact'
                · exact Or.inr (Or.inr (Or.inl (by omega)))
                · exact Or.inr (Or.inr (Or.inr (by omega)))
              have hancR : ∀ l r : Fin d, l.1 ≤ lo + a.1 + 1 → lo + a.1 + 1 + (k - a.1) ≤ r.1 →
                  ¬ (l.1 = lo + a.1 + 1 ∧ r.1 = lo + a.1 + 1 + (k - a.1)) →
                  ∀ q' : Fin d, F (.split l r) = some q' →
                    q'.1 < lo + a.1 + 1 ∨ lo + a.1 + 1 + (k - a.1) ≤ q'.1 := by
                intro l r hl hr hne q' hsp
                by_cases htop' : l.1 = lo ∧ r.1 = lo + k + 1
                · have hle : l = loF := Fin.ext htop'.1
                  have hre : r = hiF := Fin.ext htop'.2
                  rw [hle, hre, hqeq] at hsp
                  injection hsp with hqq'
                  left; rw [← hqq']; omega
                · have hact' : F (.par l r) ≠ .none := fun h0 => by
                    have hqr := hF.2.2.2.2.2.2.2.2.2.2.2.1 l r q' hsp
                    have := (hF.2.2.2.1 l r (by omega)).1 h0
                    rw [this] at hsp; cases hsp
                  rcases hlam l r hact' with hbig | hin | hdisj1 | hdisj2
                  · rcases hanc l r hbig.1 hbig.2 htop' q' hsp with h1 | h2
                    · exact Or.inl (by omega)
                    · exact Or.inr (by omega)
                  · exact absurd (hcross _ l r rfl hin.1 hin.2 htop' (by omega) (by omega)) hact'
                  · omega
                  · omega
              have hIHL := ih a.1 (by omega) lo (by omega) (.leftOf hiF) uv.1 hLpar (by simp) hLw
                hlamL hancL (fun l r h1 h2 _ => hroot l r h1 (by omega) (by omega))
              have hIHR := ih (k - a.1) (by omega) (lo + a.1 + 1) (by omega) (.rightOf loF) uv.2
                hRpar (by simp) hRw hlamR hancR
                (fun l r h1 h2 _ => hroot l r (by omega) (by omega) (by omega))
              obtain ⟨hLleg, hLall, hLleaf⟩ := hIHL
              obtain ⟨hRleg, hRall, hRleaf⟩ := hIHR
              have hT_eq : extractPTree p v_out F hF (k + 1) lo hhi hact =
                  .node g a
                    (extractPTree p v_out F hF a.1 lo (by omega) (by rw [hLpar]; simp))
                    (extractPTree p v_out F hF (k - a.1) (lo + a.1 + 1) (by omega)
                      (by rw [hRpar]; simp)) := by
                conv_lhs => unfold extractPTree
              rw [hT_eq]
              refine ⟨⟨hgmul, hLleg, hRleg⟩, ?_, ?_⟩
              · intro l r h1 h2
                by_cases htop' : l.1 = lo ∧ r.1 = lo + k + 1
                · have hle : l = loF := Fin.ext htop'.1
                  have hre : r = hiF := Fin.ext htop'.2
                  subst hle; subst hre
                  have hhiF : (⟨lo + k + 1, hhi⟩ : Fin d) = ⟨lo + (k + 1), hhi⟩ :=
                    Fin.ext (Nat.add_assoc lo k 1)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · simp only [placePar_node, loF, hiF, and_self, ↓reduceIte]
                    rw [hhiF]; exact hpar
                  · simp only [placeWire_node, loF, hiF, and_self, ↓reduceIte]
                    rw [hhiF]; exact hw
                  · simp only [placeSplit_node, loF, hiF, and_self, ↓reduceIte]
                    rw [hqeq]; congr 1; exact Fin.ext hqval.symm
                  · simpa [loF, hiF] using hgeq
                · by_cases hr : r.1 ≤ lo + a.1
                  · simp only [placePar_node, placeWire_node, placeSplit_node, placeGate_node,
                      htop', hr, ↓reduceIte, hu]
                    exact hLall l r h1 hr
                  · by_cases hl : lo + a.1 + 1 ≤ l.1
                    · simp only [placePar_node, placeWire_node, placeSplit_node, placeGate_node,
                        htop', hr, hl, ↓reduceIte, hv]
                      exact hRall l r hl (by omega)
                    · have hpn : F (.par l r) = .none :=
                        hcross _ l r rfl h1 h2 htop' (by omega) (by omega)
                      simp only [placePar_node, placeWire_node, placeSplit_node, placeGate_node,
                        htop', hr, hl, ↓reduceIte]
                      refine ⟨hpn, (hF.2.2.1 l r).1 hpn, ?_, ?_⟩
                      · by_cases hlr : l.1 < r.1
                        · exact (hF.2.2.2.1 l r hlr).1 hpn
                        · exact hF.2.2.2.2.1 l r hlr
                      · by_cases hlr : l.1 < r.1
                        · exact (hF.2.2.2.2.2.1 l r hlr).1 hpn
                        · exact hF.2.2.2.2.2.2.1 l r hlr
              · intro l h1 h2
                simp only [placeLeaf_node]
                by_cases hl : l.1 ≤ lo + a.1
                · rw [ite_eq_left hl]; exact hLleaf l h1 hl
                · rw [ite_eq_right hl]; exact hRleaf l (by omega) (by omega)

omit [CommSemiring K] in
/-- Every valid assignment `F` with `F .rootDeg = k + 1` equals `assignOfPTree` of its extracted
tree. -/
private theorem exists_pTree_of_valid_succ (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (F : ∀ x : TreeDom m d, TreeVal (n + m) s d x)
    (hF : IsValidAssign p v_out F) {k : ℕ} (hk : k < d) (hdeg : (F .rootDeg).1 = k + 1) :
    ∃ T : PTree (n + m) s k,
      T.IsLegal p (fun b => F (.boolVar b)) ∧
      F = assignOfPTree p v_out (fun b => F (.boolVar b)) hk T := by
  have hout : ∀ gap : ℕ, ∀ l r : Fin d, d - (r.1 - l.1) = gap → k < r.1 →
      F (.par l r) = .none := by
    intro gap
    induction gap using Nat.strong_induction_on with
    | ind gap ih =>
        intro l r hgap hrk
        by_cases hrl : r.1 < l.1
        · exact hF.2.2.2.2.2.2.2.2.1 l r hrl
        · cases hp : F (.par l r) with
          | none => rfl
          | root =>
              have := ((hF.1 l r).1 hp).2
              omega
          | leftOf r' =>
              have hlt' := hF.2.2.2.2.2.2.2.2.2.1 l r r' hp
              have hsp := (hF.2.2.2.2.2.2.2.2.2.2.2.2.1 l r' r (by omega) hlt').2 hp
              have hpn := ih (d - (r'.1 - l.1)) (by omega) l r' rfl (by omega)
              have hsp0 := (hF.2.2.2.1 l r' (by omega)).1 hpn
              rw [hsp0] at hsp; cases hsp
          | rightOf l' =>
              have hlt' := hF.2.2.2.2.2.2.2.2.2.2.1 l r l' hp
              let q' : Fin d := ⟨l.1 - 1, by omega⟩
              have hq1 : l'.1 ≤ q'.1 := by dsimp [q']; omega
              have hq2 : q'.1 < r.1 := by dsimp [q']; omega
              have hleq : (⟨q'.1 + 1, by omega⟩ : Fin d) = l := Fin.ext (by dsimp [q']; omega)
              have hsp := (hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1 l' r q' hq2 hq1).2 (by rwa [hleq])
              have hpn := ih (d - (r.1 - l'.1)) (by omega) l' r rfl hrk
              have hsp0 := (hF.2.2.2.1 l' r (by omega)).1 hpn
              rw [hsp0] at hsp; cases hsp
  have hrootPar : F (.par ⟨0, by omega⟩ ⟨0 + k, by omega⟩) = .root :=
    (hF.1 ⟨0, by omega⟩ ⟨0 + k, by omega⟩).2 ⟨rfl, by simp [hdeg]⟩
  have hrootW : F (.wire ⟨0, by omega⟩ ⟨0 + k, by omega⟩) = some v_out :=
    hF.2.1 _ _ hrootPar
  have hlam : ∀ l r : Fin d, F (.par l r) ≠ .none →
      (l.1 ≤ 0 ∧ 0 + k ≤ r.1) ∨ (0 ≤ l.1 ∧ r.1 ≤ 0 + k) ∨ r.1 < 0 ∨ 0 + k < l.1 := by
    intro l r hact
    by_cases hrk : k < r.1
    · exact absurd (hout _ l r rfl hrk) hact
    · exact Or.inr (Or.inl ⟨Nat.zero_le _, by omega⟩)
  have hanc : ∀ l r : Fin d, l.1 ≤ 0 → 0 + k ≤ r.1 → ¬ (l.1 = 0 ∧ r.1 = 0 + k) →
      ∀ q' : Fin d, F (.split l r) = some q' → q'.1 < 0 ∨ 0 + k ≤ q'.1 := by
    intro l r hl hr hne q' hsp
    have hrk : k < r.1 := by omega
    have hpn := hout _ l r rfl hrk
    have hqr := hF.2.2.2.2.2.2.2.2.2.2.2.1 l r q' hsp
    have hsp0 := (hF.2.2.2.1 l r (by omega)).1 hpn
    rw [hsp0] at hsp; cases hsp
  have hnr : ∀ l r : Fin d, 0 ≤ l.1 → r.1 ≤ 0 + k → ¬ (l.1 = 0 ∧ r.1 = 0 + k) →
      F (.par l r) ≠ .root := by
    intro l r _ _ hne hp
    have := (hF.1 l r).1 hp
    exact hne ⟨this.1, by omega⟩
  have hspec := extractPTree_spec p v_out F hF k 0 (by omega) .root v_out
    hrootPar (by simp) hrootW hlam hanc hnr
  obtain ⟨hTleg, hTall, hTleaf⟩ := hspec
  refine ⟨extractPTree p v_out F hF k 0 (by omega) (by rw [hrootPar]; simp), hTleg, ?_⟩
  funext x
  cases x with
  | boolVar b => rfl
  | rootDeg => exact Fin.ext hdeg
  | par l r =>
      by_cases hr : r.1 ≤ k
      · exact (hTall l r (Nat.zero_le _) (by omega)).1
      · simp only [assignOfPTree_par]
        rw [hout _ l r rfl (by omega),
          placePar_outside p (lo := 0) (k := k) (by omega) _ _ l r (Or.inr (by omega))]
  | wire l r =>
      by_cases hr : r.1 ≤ k
      · exact (hTall l r (Nat.zero_le _) (by omega)).2.1
      · simp only [assignOfPTree_wire]
        rw [(hF.2.2.1 l r).1 (hout _ l r rfl (by omega)),
          placeWire_outside p (lo := 0) (k := k) (by omega) _ _ l r (Or.inr (by omega))]
  | split l r =>
      by_cases hr : r.1 ≤ k
      · exact (hTall l r (Nat.zero_le _) (by omega)).2.2.1
      · simp only [assignOfPTree_split]
        rw [placeSplit_outside (lo := 0) (k := k) (by omega) _ l r (Or.inr (by omega))]
        by_cases hlr : l.1 < r.1
        · exact (hF.2.2.2.1 l r hlr).1 (hout _ l r rfl (by omega))
        · exact hF.2.2.2.2.1 l r hlr
  | gate l r =>
      by_cases hr : r.1 ≤ k
      · exact (hTall l r (Nat.zero_le _) (by omega)).2.2.2
      · simp only [assignOfPTree_gate]
        rw [placeGate_outside (lo := 0) (k := k) (by omega) _ l r (Or.inr (by omega))]
        by_cases hlr : l.1 < r.1
        · exact (hF.2.2.2.2.2.1 l r hlr).1 (hout _ l r rfl (by omega))
        · exact hF.2.2.2.2.2.2.1 l r hlr
  | leafVar l =>
      by_cases hl : l.1 ≤ k
      · exact hTleaf l (Nat.zero_le _) (by omega)
      · simp only [assignOfPTree_leafVar]
        rw [(hF.2.2.2.2.2.2.2.1 l).1 (hout _ l l rfl (by omega)),
          placeLeaf_outside (lo := 0) (k := k) (by omega) _ l (Or.inr (by omega))]

private theorem placeSplit_of_r_lt_l {d k lo : ℕ} (hhi : lo + k < d) (T : PTree (n + m) s k)
    (l r : Fin d) (hrl : r.1 < l.1) : placeSplit d lo hhi T l r = none := by
  induction T generalizing lo with
  | leaf _ => rfl
  | @node _ k' a L R ihL ihR =>
      simp only [placeSplit_node]
      split_ifs with h1 h2 h3
      · omega
      · exact ihL (by omega)
      · exact ihR (by omega)
      · rfl

private theorem placeGate_of_r_lt_l {d k lo : ℕ} (hhi : lo + k < d) (T : PTree (n + m) s k)
    (l r : Fin d) (hrl : r.1 < l.1) : placeGate d lo hhi T l r = none := by
  induction T generalizing lo with
  | leaf _ => rfl
  | @node _ k' a L R ihL ihR =>
      simp only [placeGate_node]
      split_ifs with h1 h2 h3
      · omega
      · exact ihL (by omega)
      · exact ihR (by omega)
      · rfl

omit [CommSemiring K] in
/-- Injectivity of `assignOfPTree` on `PTree`s. -/
private theorem assignOfPTree_injective (p : Program (arithSignature K) (n + m) s)
    (v_out : Wire (n + m) s) (e : Fin m → Bool) {k : ℕ} (hk : k < d) :
    Function.Injective (assignOfPTree p v_out e hk) := by
  have hinj : ∀ (k lo : ℕ) (hhi : lo + k < d) (T₁ T₂ : PTree (n + m) s k),
      (∀ l r : Fin d, placeSplit d lo hhi T₁ l r = placeSplit d lo hhi T₂ l r) →
      (∀ l r : Fin d, placeGate d lo hhi T₁ l r = placeGate d lo hhi T₂ l r) →
      (∀ l : Fin d, placeLeaf d lo hhi T₁ l = placeLeaf d lo hhi T₂ l) →
      T₁ = T₂ := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
        intro lo hhi T₁ T₂ hsp hga hlf
        cases k with
        | zero =>
            cases T₁ with
            | leaf j₁ =>
                cases T₂ with
                | leaf j₂ =>
                    have h := hlf ⟨lo, by omega⟩
                    simp only [placeLeaf_leaf, ↓reduceIte, Option.some.injEq] at h
                    rw [h]
        | succ k' =>
            cases T₁ with
            | node g₁ a₁ L₁ R₁ =>
                cases T₂ with
                | node g₂ a₂ L₂ R₂ =>
                    have hg := hga ⟨lo, by omega⟩ ⟨lo + k' + 1, hhi⟩
                    simp only [placeGate_node, and_self, ↓reduceIte, Option.some.injEq] at hg
                    subst hg
                    have ha := hsp ⟨lo, by omega⟩ ⟨lo + k' + 1, hhi⟩
                    simp only [placeSplit_node, and_self, ↓reduceIte, Option.some.injEq] at ha
                    have haeq : a₁ = a₂ := Fin.ext (by
                      have := congrArg Fin.val ha; dsimp at this; omega)
                    subst haeq
                    congr 1
                    · refine ih a₁.1 (by omega) lo (by omega) L₁ L₂ ?_ ?_ ?_
                      · intro l r
                        by_cases hr : r.1 ≤ lo + a₁.1
                        · have h := hsp l r
                          have hnt : ¬ (l.1 = lo ∧ r.1 = lo + k' + 1) := by omega
                          simpa [hnt, hr] using h
                        · rw [placeSplit_outside (lo := lo) (k := a₁.1) (by omega) L₁ l r
                            (Or.inr (by omega)),
                            placeSplit_outside (lo := lo) (k := a₁.1) (by omega) L₂ l r
                            (Or.inr (by omega))]
                      · intro l r
                        by_cases hr : r.1 ≤ lo + a₁.1
                        · have h := hga l r
                          have hnt : ¬ (l.1 = lo ∧ r.1 = lo + k' + 1) := by omega
                          simpa [hnt, hr] using h
                        · rw [placeGate_outside (lo := lo) (k := a₁.1) (by omega) L₁ l r
                            (Or.inr (by omega)),
                            placeGate_outside (lo := lo) (k := a₁.1) (by omega) L₂ l r
                            (Or.inr (by omega))]
                      · intro l
                        by_cases hl : l.1 ≤ lo + a₁.1
                        · simpa [hl] using hlf l
                        · rw [placeLeaf_outside (lo := lo) (k := a₁.1) (by omega) L₁ l
                            (Or.inr (by omega)),
                            placeLeaf_outside (lo := lo) (k := a₁.1) (by omega) L₂ l
                            (Or.inr (by omega))]
                    · refine ih (k' - a₁.1) (by omega) (lo + a₁.1 + 1) (by omega) R₁ R₂ ?_ ?_ ?_
                      · intro l r
                        by_cases hl : lo + a₁.1 + 1 ≤ l.1
                        · by_cases hrl : r.1 < l.1
                          · rw [placeSplit_of_r_lt_l (by omega) R₁ l r hrl,
                              placeSplit_of_r_lt_l (by omega) R₂ l r hrl]
                          · have h := hsp l r
                            have hnt : ¬ (l.1 = lo ∧ r.1 = lo + k' + 1) := by omega
                            simpa [hnt, show ¬ (r.1 ≤ lo + a₁.1) by omega, hl] using h
                        · rw [placeSplit_outside (lo := lo + a₁.1 + 1) (by omega) R₁ l r
                            (Or.inl (by omega)),
                            placeSplit_outside (lo := lo + a₁.1 + 1) (by omega) R₂ l r
                            (Or.inl (by omega))]
                      · intro l r
                        by_cases hl : lo + a₁.1 + 1 ≤ l.1
                        · by_cases hrl : r.1 < l.1
                          · rw [placeGate_of_r_lt_l (by omega) R₁ l r hrl,
                              placeGate_of_r_lt_l (by omega) R₂ l r hrl]
                          · have h := hga l r
                            have hnt : ¬ (l.1 = lo ∧ r.1 = lo + k' + 1) := by omega
                            simpa [hnt, show ¬ (r.1 ≤ lo + a₁.1) by omega, hl] using h
                        · rw [placeGate_outside (lo := lo + a₁.1 + 1) (by omega) R₁ l r
                            (Or.inl (by omega)),
                            placeGate_outside (lo := lo + a₁.1 + 1) (by omega) R₂ l r
                            (Or.inl (by omega))]
                      · intro l
                        by_cases hl : l.1 ≤ lo + a₁.1
                        · rw [placeLeaf_outside (lo := lo + a₁.1 + 1) (by omega) R₁ l
                            (Or.inl (by omega)),
                            placeLeaf_outside (lo := lo + a₁.1 + 1) (by omega) R₂ l
                            (Or.inl (by omega))]
                        · simpa [hl] using hlf l
  intro T₁ T₂ h
  refine hinj k 0 (by omega) T₁ T₂ ?_ ?_ ?_
  · intro l r; exact congrFun h (.split l r)
  · intro l r; exact congrFun h (.gate l r)
  · intro l; exact congrFun h (.leafVar l)

/-- **Interval-tree domain clause sum identity**: the finite-domain clause sum of `(treeLits,
treeWeights)` equals `booleanSum m (c.polynomial 0)` whenever `(c.polynomial 0).totalDegree ≤ d`. -/
private theorem domainClauseSum_tree (c : Circuit (arithSignature K) (n + m) 1)
    {d : ℕ} (hd : (c.polynomial 0).totalDegree ≤ d) :
    domainClauseSum (treeLits (n := n) (m := m) (s := c.size) (d := d) c.program (c.outputs 0))
      (treeWeights c.program (c.outputs 0)) Empty.elim =
    booleanSum m (c.polynomial 0) := by
  classical
  let p := c.program
  let v_out := c.outputs 0
  have hsum_deg : ∀ e : Fin m → Bool,
      projection (booleanAssignment e) (c.polynomial 0) =
        C (wireConst p v_out) +
          ∑ k : Fin d, ∑ T : PTree (n + m) c.size k.1, T.eval p e v_out := by
    intro e
    have hcomp : c.polynomial 0 =
        ∑ i ∈ Finset.range (d + 1), homogeneousComponent i (wirePoly p v_out) := by
      have h1 := (sum_homogeneousComponent (φ := c.polynomial 0)).symm
      rw [h1]
      refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hd)) ?_
      intro i hi hnot
      simp only [Finset.mem_range] at hi hnot
      exact homogeneousComponent_eq_zero (n := i) (φ := c.polynomial 0) (by omega)
    rw [hcomp, map_sum, Finset.sum_range_succ', homogeneousComponent_zero_wirePoly,
      projection_C, add_comm]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun k => ∑ T : PTree (n + m) c.size k, T.eval p e v_out)]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (sum_pTree_eval p e k v_out).symm
  have hdcs :
      domainClauseSum (treeLits (n := n) (m := m) (s := c.size) (d := d) p v_out)
        (treeWeights p v_out) Empty.elim =
      ∑ F : ∀ x : TreeDom m d, TreeVal (n + m) c.size d x,
        if IsValidAssign p v_out F then assignWeight p v_out F else 0 := by
    unfold domainClauseSum
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [Fintype.prod_sum_type]
    refine (congrArg₂ (· * ·)
      ((Finset.prod_congr rfl fun κ _ => by
        split_ifs with h1 h2 h3
        · rfl
        · exact absurd h1 h2
        · exact absurd h3 h1
        · rfl).trans (check_prod_eq_ite p v_out F))
      rfl).trans ?_
    split_ifs with hF
    · rw [one_mul, ← weight_prod_eq_assignWeight p v_out F hF]
      exact Finset.prod_congr rfl fun κ _ => by
        split_ifs with h1 h2 h3
        · rfl
        · exact absurd h1 h2
        · exact absurd h3 h1
        · rfl
    · rw [zero_mul]
  rw [hdcs, booleanSum]
  simp_rw [hsum_deg]
  have hpart :
      (∑ F : ∀ x : TreeDom m d, TreeVal (n + m) c.size d x,
        if IsValidAssign p v_out F then assignWeight p v_out F else 0) =
      ∑ e : Fin m → Bool, ∑ deg : Fin (d + 1),
        ∑ F ∈ Finset.univ.filter
            (fun F : ∀ x : TreeDom m d, TreeVal (n + m) c.size d x =>
              (fun b => F (.boolVar b)) = e ∧ F .rootDeg = deg),
          if IsValidAssign p v_out F then assignWeight p v_out F else 0 := by
    let g : (∀ x : TreeDom m d, TreeVal (n + m) c.size d x) → (Fin m → Bool) × Fin (d + 1) :=
      fun F => (fun b => F (.boolVar b), F .rootDeg)
    rw [← Fintype.sum_prod_type']
    symm
    have hfib := Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := g)
      (f := fun F => if IsValidAssign p v_out F then assignWeight p v_out F else 0)
      (fun _ _ => Finset.mem_univ _)
    rw [← hfib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr ?_ (fun _ _ => rfl)
    ext F
    simp [g, Prod.ext_iff]
  rw [hpart]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Fin.sum_univ_succ]
  congr 1
  · rw [Finset.sum_eq_single (assignZero e)]
    · rw [ite_eq_left (isValidAssign_assignZero p v_out e), assignWeight_eq_prod]
      simp
    · intro F hFmem hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hFmem
      refine ite_eq_right fun hv => ?_
      have heq := eq_assignZero_of_rootDeg_zero p v_out F hv hFmem.2
      rw [hFmem.1] at heq
      exact absurd heq hne
    · intro hnot
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, rfl⟩) hnot
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hlegal_sum :
        (∑ T : PTree (n + m) c.size k.1, T.eval p e v_out) =
        ∑ T : PTree (n + m) c.size k.1, if T.IsLegal p e then T.eval p e v_out else 0 := by
      refine Finset.sum_congr rfl fun T _ => ?_
      split_ifs with hL
      · rfl
      · exact PTree.eval_eq_zero_of_not_isLegal p e v_out T hL
    rw [hlegal_sum]
    symm
    refine Finset.sum_of_injOn (assignOfPTree p v_out e k.2)
      (assignOfPTree_injective p v_out e k.2).injOn ?_ ?_ ?_
    · intro T _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨rfl, Fin.ext rfl⟩
    · intro F hFmem hnotimg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hFmem
      refine ite_eq_right fun hv => ?_
      obtain ⟨T, hTleg, hFeq⟩ := exists_pTree_of_valid_succ p v_out F hv k.2
        (by rw [hFmem.2]; rfl)
      rw [hFmem.1] at hFeq
      exact hnotimg ⟨T, Finset.mem_univ T, hFeq.symm⟩
    · intro T _
      by_cases hL : T.IsLegal p e
      · rw [ite_eq_left hL, ite_eq_left (isValidAssign_assignOfPTree p v_out e k.2 T hL),
          assignWeight_assignOfPTree p v_out e k.2 T hL]
      · rw [ite_eq_right hL]
        symm
        refine ite_eq_right fun hv => hL ?_
        obtain ⟨T', hT'leg, hFeq⟩ := exists_pTree_of_valid_succ p v_out _ hv k.2 rfl
        have hTeq : T = T' := assignOfPTree_injective p v_out e k.2 hFeq
        exact hTeq ▸ hT'leg

end TreeExtraction

/-! ### Valiant's Theorem (`permFamily_isVNPComplete`) -/

section ValiantMain

variable {K : Type u} [Field K]

/-- Explicit polynomial dimension bound for a single `booleanSum` of an arithmetic circuit. -/
private def valiantMatDim (n m s d : ℕ) : ℕ :=
  let N := n + m
  let numBits := 2 * m + (d + 1) + d * d * (5 + 3 * d + N + 2 * s) + d * (1 + N)
  let numCheck :=
    3 * d + 9 * d * d + 7 * d * d * d + d * d * s + 2 * d * d * d * s + d * m
  let numWeight := 1 + d * d * (N + s) * s + d * (N + s) * N + d * n
  let totalLits := 3 * (numCheck + numWeight) + numBits + 2 * numBits * numBits
  let S := 3 * totalLits + 1
  S + S * S

/-- Every Boolean sum of a polynomial computed by an arithmetic circuit `c` of degree `≤ d` is a
projection of `(genericMatrix K (valiantMatDim n m c.size d)).permanent` over any field `K` with
`(2 : K) ≠ 0`. -/
private theorem isProjection_booleanSum_circuit_permanent (h2 : (2 : K) ≠ 0) {n m d : ℕ}
    (c : Circuit (arithSignature K) (n + m) 1) (hd : (c.polynomial 0).totalDegree ≤ d) :
    IsProjection (booleanSum m (c.polynomial 0))
      (genericMatrix K (valiantMatDim n m c.size d)).permanent := by
  classical
  let p := c.program
  let v_out := c.outputs 0
  let s := c.size
  let N := n + m
  let V := Σ x : TreeDom m d, TreeVal N s d x
  let Θ₀ := TreeCheck n m s d ⊕ TreeWeight n m s d
  let lits₀ := treeLits (n := n) (m := m) (s := s) (d := d) p v_out
  let wt₀ := treeWeights (d := d) p v_out
  let Θ₁ := Θ₀ ⊕ TreeDom m d ⊕ (V × V)
  let strip : (Empty ⊕ V) × Bool → V × Bool := fun lb => (Sum.elim Empty.elim id lb.1, lb.2)
  let lits₁ : Θ₁ → List (V × Bool) := fun κ => (oneHotLits lits₀ κ).map strip
  let wt₁ : Θ₁ → MvPolynomial (Fin n) K := oneHotWeights wt₀
  have hcs_eq : clauseSum lits₁ wt₁ = booleanSum m (c.polynomial 0) := by
    rw [← domainClauseSum_tree c hd, domainClauseSum_eq_clauseSumWith]
    unfold clauseSum clauseSumWith
    refine Finset.sum_congr rfl fun a _ => Finset.prod_congr rfl fun κ _ => ?_
    have hiff : (∀ l ∈ lits₁ κ, a l.1 = l.2) ↔
        (∀ l ∈ oneHotLits lits₀ κ, Sum.elim Empty.elim a l.1 = l.2) := by
      simp only [lits₁, List.forall_mem_map]
      refine forall₂_congr fun l _ => ?_
      rcases l with ⟨e | v, b⟩
      · exact Empty.elim e
      · rfl
    split_ifs with ha hb hc
    · rfl
    · exact absurd (hiff.1 ha) hb
    · exact absurd (hiff.2 hc) ha
    · rfl
  have hne₁ : ∀ κ : Θ₁, lits₁ κ ≠ [] := by
    rintro (κ₀ | x | ⟨p₁, p₂⟩)
    · simp only [lits₁, oneHotLits, ne_eq, List.map_eq_nil_iff]
      rcases κ₀ with ck | wk
      · exact checkLits_ne_nil p v_out ck
      · exact weightLits_ne_nil wk
    · obtain ⟨v⟩ := (inferInstance : Nonempty (TreeVal N s d x))
      intro hnil
      have hmem : (⟨x, v⟩, false) ∈ lits₁ (.inr (.inl x)) := by
        simp [lits₁, oneHotLits, strip]
      rw [hnil] at hmem
      simp at hmem
    · simp [lits₁, oneHotLits]
  have hocc₁ : ∀ b : V, ∃ κ : Θ₁, ∃ l ∈ lits₁ κ, l.1 = b := fun b =>
    ⟨.inr (.inr (b, b)), (b, true), by simp [lits₁, oneHotLits, strip], rfl⟩
  have hwt₁ : ∀ κ : Θ₁, (∃ i, wt₁ κ = X i) ∨ ∃ a, wt₁ κ = C a := by
    rintro (κ₀ | _ | ⟨p₁, p₂⟩)
    · exact treeWeights_var_or_const p v_out κ₀
    · exact Or.inr ⟨0, map_zero C |>.symm⟩
    · dsimp [wt₁, oneHotWeights]
      split_ifs
      · exact Or.inr ⟨0, map_zero C |>.symm⟩
      · exact Or.inr ⟨1, map_one C |>.symm⟩
  have hcard_V : Fintype.card V ≤
      2 * m + (d + 1) + d * d * (5 + 3 * d + N + 2 * s) + d * (1 + N) :=
    card_sigma_treeVal N s d m
  have hsum_lits : ∑ κ : Θ₁, (lits₁ κ).length ≤
      3 * ((3 * d + 9 * d * d + 7 * d * d * d + d * d * s + 2 * d * d * d * s + d * m) +
        (1 + d * d * (N + s) * s + d * (N + s) * N + d * n)) +
      (2 * m + (d + 1) + d * d * (5 + 3 * d + N + 2 * s) + d * (1 + N)) +
      2 * (2 * m + (d + 1) + d * d * (5 + 3 * d + N + 2 * s) + d * (1 + N)) *
        (2 * m + (d + 1) + d * d * (5 + 3 * d + N + 2 * s) + d * (1 + N)) := by
    simp only [lits₁, List.length_map]
    rw [Fintype.sum_sum_type (f := fun κ : Θ₁ => (oneHotLits lits₀ κ).length),
      Fintype.sum_sum_type (f := fun y : TreeDom m d ⊕ V × V => (oneHotLits lits₀ (.inr y)).length)]
    have hA : ∑ κ : Θ₀, (oneHotLits lits₀ (.inl κ)).length ≤
        3 * (Fintype.card (TreeCheck n m s d) + Fintype.card (TreeWeight n m s d)) := by
      rw [Fintype.sum_sum_type]
      have h1 : ∑ κ : TreeCheck n m s d, (checkLits p v_out κ).length ≤
          3 * Fintype.card (TreeCheck n m s d) := by
        calc ∑ κ : TreeCheck n m s d, (checkLits p v_out κ).length
            ≤ ∑ _κ : TreeCheck n m s d, 3 :=
              Finset.sum_le_sum fun κ _ => checkLits_length_le p v_out κ
          _ = 3 * Fintype.card (TreeCheck n m s d) := by simp [mul_comm]
      have h2 : ∑ κ : TreeWeight n m s d,
          (weightLits (n := n) (m := m) (s := s) (d := d) κ).length ≤
          3 * Fintype.card (TreeWeight n m s d) := by
        calc ∑ κ : TreeWeight n m s d,
              (weightLits (n := n) (m := m) (s := s) (d := d) κ).length
            ≤ ∑ _κ : TreeWeight n m s d, 3 :=
              Finset.sum_le_sum fun κ _ => (weightLits_length_le κ).trans (by omega)
          _ = 3 * Fintype.card (TreeWeight n m s d) := by simp [mul_comm]
      simp only [oneHotLits, lits₀, treeLits_inl, treeLits_inr]
      omega
    have hB : ∑ x : TreeDom m d, (oneHotLits lits₀ (.inr (.inl x))).length = Fintype.card V := by
      simp only [oneHotLits, List.length_map, Finset.length_toList, Finset.card_univ]
      exact (Fintype.card_sigma).symm
    have hC : ∑ pq : V × V, (oneHotLits lits₀ (.inr (.inr pq))).length =
        2 * Fintype.card V * Fintype.card V := by
      simp only [oneHotLits, List.length_cons, List.length_nil, Finset.sum_const,
        Finset.card_univ, Fintype.card_prod, smul_eq_mul]
      ring
    rw [hB, hC]
    rw [card_treeCheck, card_treeWeight] at hA
    have hsq : 2 * Fintype.card V * Fintype.card V ≤
        2 * (2 * m + (d + 1) + d * d * (5 + 3 * d + N + 2 * s) + d * (1 + N)) *
          (2 * m + (d + 1) + d * d * (5 + 3 * d + N + 2 * s) + d * (1 + N)) := by
      gcongr
    dsimp only [N, s] at hcard_V hA hsq ⊢
    omega
  rw [← hcs_eq]
  have hbound : 3 * ∑ κ : Θ₁, (lits₁ κ).length + 1 ≤
      3 * (3 * ((3 * d + 9 * d * d + 7 * d * d * d + d * d * c.size + 2 * d * d * d * c.size +
          d * m) +
        (1 + d * d * (n + m + c.size) * c.size + d * (n + m + c.size) * (n + m) + d * n)) +
        (2 * m + (d + 1) + d * d * (5 + 3 * d + (n + m) + 2 * c.size) + d * (1 + (n + m))) +
        2 * (2 * m + (d + 1) + d * d * (5 + 3 * d + (n + m) + 2 * c.size) + d * (1 + (n + m))) *
          (2 * m + (d + 1) + d * d * (5 + 3 * d + (n + m) + 2 * c.size) +
            d * (1 + (n + m)))) + 1 := by
    dsimp only [N, s] at hsum_lits
    omega
  exact isProjection_clauseSum_permanent h2 lits₁ hne₁ hocc₁ wt₁ hwt₁ hbound

/-- **Valiant's Theorem**: over any field `K` of
characteristic other than `2`, the generic permanent family `permFamily K` is `VNP`-complete under
`p`-projections. -/
public theorem permFamily_isVNPComplete (h2 : (2 : K) ≠ 0) : IsVNPComplete (permFamily K) := by
  refine ⟨permFamily_mem_VNP (R := K), fun f hf => ?_⟩
  obtain ⟨m, g, ⟨⟨hvars, hdeg⟩, c, hcsize, hcpoly⟩, hfg⟩ := hf
  dsimp only at hcpoly
  have hn : PolynomiallyBounded f.vars := hvars.mono_of_le fun n => Nat.le_add_right _ _
  have hm : PolynomiallyBounded m := hvars.mono_of_le fun n => Nat.le_add_left _ _
  let t : ℕ → ℕ := fun n => valiantMatDim (f.vars n) (m n) (c n).size (g n).totalDegree
  have ht : PolynomiallyBounded t := by
    dsimp only [t, valiantMatDim]
    fun_prop
  refine ⟨t, ht, fun n => ?_⟩
  rw [hfg n, ← hcpoly n]
  exact isProjection_booleanSum_circuit_permanent h2 (c n) (by rw [hcpoly n])

end ValiantMain

end CslibFrontier.Computability.Circuit.Arithmetic.Permanent
