/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.EvenNilHecke
import OddMath.QuiverHecke.DividedPowerGrading
import Categorification.Algebra.NilHeckeDemazure
import Categorification.KLR.GradeTransfer
import Categorification.KLR.DividedPowerDecomposition

/-!
# Even divided-power projectives in `H_n`

BE2, arXiv:1701.04133v2, Lemma 11.1, for an even colour `i`:
`H_n 1_{i^n} ≅ ⊕ (H_n 1_{i^{(n)}})` over `[n]!_{q_i}` shifted copies.

For an even colour BE2's divided-power idempotent is `1_{i^{(n)}} = D_{w_0}` with
`D_r = -T_r X_r`. Numbering the strands from the left, `D` at position `j` is the Demazure
operator `π_j = -∂_j x_{j+1}` of categorification-lean, so `1_{i^{(n)}}` is the image of
`Categorification.NilHecke.demIdem ℤ n` (along the reduced word `w0Word n`) under the even
same-colour map `evenNilHecke`.

The decomposition is assembled from three proved inputs, without injectivity of the
nilHecke map:

* the graded splitting of `1 ∈ R(n·i) ≅ NH_n` into `n!` copies of KL's idempotent
  `e_n = x^δ ∂_{w_0}` (`Categorification.KLR.exists_gradedSplitting_e`, KL I §2.2, §2.5), with
  degree generating function `q^{-n(n-1)/2} [n]!`;
* the equivalence of `e_n` with `π_{w_0}` through `a = x^δ π_{w_0}` (degree `n(n-1)`) and
  `b = ∂_{w_0}` (`Categorification.NilHecke.demA_mul_ddw`, `ddw_mul_demA`);
* the transfer of KLR degrees along `R(n·i) ≅ NH_n → End(i^n)`
  (`Categorification.KLR.grade_transfer`): a dot has degree `2 d_i`, a crossing `-2 d_i`.

In KL degree units the shifts `evenShift` have generating function `q^{n(n-1)/2} [n]!`
(`sum_T_evenShift`), the same normalization as the odd case
(`OddMath.SKM.DividedPowerDecomposition.sum_shift_monomial`).

## Main declarations

* `evenPhi`: the algebra map `R(n·i) → End(i^n)`, with `evenPhi_mem_degree`.
* `evenIdempotent D Sc i hi r : Hn D Sc r` and `evenProjective`, the principal module.
* `evenDecompositionInHn : wordProjective ≃ (evenIndex r → evenProjective)`, with
  `card_evenIndex`, `sum_T_evenShift`, `evenDecompositionInHn_degree` and
  `evenDecompositionInHn_symm_degree`.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
variable {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-! ### Degrees of the even same-colour map -/

private theorem evenFunctor_mem_degree {A : Type*} [AddCommMonoid A]
    (i : I) (hi : D.parity i = 0) (deg : (sig D).Gen → A)
    {a b : Obj Categorification.NilHecke.Diagram.sig}
    {f : (Categorification.NilHecke.Diagram.pres k).obj a ⟶
      (Categorification.NilHecke.Diagram.pres k).obj b}
    {d : A}
    (hf : f ∈ (Categorification.NilHecke.Diagram.pres k).homDeg
      (fun g => deg ((evenColour D i).gen g)) a b d) :
    (evenFunctor D Sc i hi).map f ∈ (pres D Sc).homDeg deg
      ((evenColour D i).obj a) ((evenColour D i).obj b) d :=
  LayerMap.lift_mem_homDeg (evenColour D i).whiskerData (fun _ => trivial)
    (fun _ => evenColour_rel D Sc i hi)
    (fun _ _ hx => (evenColour D i).toPresented_interchange (pres D Sc)
      (fun _ => 1) (evenColour_odd D i hi) hx) () (fun _ => rfl) hf

private theorem evenCorner_mem_degree {A : Type*} [AddCommMonoid A]
    (i : I) (hi : D.parity i = 0) (r : ℕ) (deg : (sig D).Gen → A)
    {f : End ((Categorification.NilHecke.Diagram.pres k).obj
      (Categorification.NilHecke.Diagram.strands r))}
    {d : A}
    (hf : f ∈ (Categorification.NilHecke.Diagram.pres k).homDeg
      (fun g => deg ((evenColour D i).gen g)) _ _ d) :
    evenCorner D Sc i hi r f ∈ (pres D Sc).homDeg deg
      (ob D (List.replicate r i)) (ob D (List.replicate r i)) d := by
  dsimp only [evenCorner, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  simpa only [zero_add, add_zero, Category.assoc] using
    Presentation.comp_mem_homDeg
      (Presentation.comp_mem_homDeg (Presentation.eqToHom_mem_homDeg deg _)
        (evenFunctor_mem_degree D Sc i hi deg hf))
      (Presentation.eqToHom_mem_homDeg deg _)

/-- The homogeneous elements of a given degree in the same-colour corner. -/
abbrev cornerDeg {A : Type*} [AddCommMonoid A] (deg : (sig D).Gen → A) (i : I) (r : ℕ)
    (d : A) : Submodule k (Corner D Sc i r) :=
  (pres D Sc).homDeg deg (ob D (List.replicate r i)) (ob D (List.replicate r i)) d

theorem one_mem_cornerDeg {A : Type*} [AddCommMonoid A] (deg : (sig D).Gen → A) (i : I)
    (r : ℕ) : (1 : Corner D Sc i r) ∈ cornerDeg D Sc deg i r 0 :=
  (pres D Sc).id_mem_homDeg deg _

theorem mul_mem_cornerDeg {A : Type*} [AddCommMonoid A] (deg : (sig D).Gen → A) {i : I}
    {r : ℕ} {d d' : A} {y z : Corner D Sc i r} (hy : y ∈ cornerDeg D Sc deg i r d)
    (hz : z ∈ cornerDeg D Sc deg i r d') : y * z ∈ cornerDeg D Sc deg i r (d + d') := by
  rw [add_comm]
  exact Presentation.comp_mem_homDeg hz hy

theorem evenNilHecke_mulX_mem {A : Type*} [AddCommMonoid A] (i : I) (hi : D.parity i = 0)
    (r : ℕ) (deg : (sig D).Gen → A) (a : Fin r) :
    evenNilHecke D Sc i hi r ⟨Categorification.NilHecke.mulX ℤ r a,
      Categorification.NilHecke.mulX_mem a⟩ ∈ cornerDeg D Sc deg i r (deg (.dot i)) := by
  rw [evenNilHecke_mulX]
  apply evenCorner_mem_degree D Sc i hi r deg
  rw [Categorification.NilHecke.Diagram.x_def k a.isLt]
  apply Presentation.diag_mem_homDeg'
  simp [Diagram.degree, Categorification.NilHecke.Diagram.layers_dlay,
    Categorification.NilHecke.Diagram.lay, evenColour]

theorem evenNilHecke_dd_mem {A : Type*} [AddCommMonoid A] (i : I) (hi : D.parity i = 0)
    (r j : ℕ) (deg : (sig D).Gen → A) :
    evenNilHecke D Sc i hi r ⟨Categorification.NilHecke.dd ℤ r j,
      Categorification.NilHecke.dd_mem j⟩ ∈ cornerDeg D Sc deg i r (deg (.cross i i)) := by
  rw [evenNilHecke_dd]
  by_cases h : j + 1 < r
  · apply evenCorner_mem_degree D Sc i hi r deg
    rw [Categorification.NilHecke.Diagram.ψ_def k h]
    apply Presentation.diag_mem_homDeg'
    simp [Diagram.degree, Categorification.NilHecke.Diagram.layers_dlay,
      Categorification.NilHecke.Diagram.lay, evenColour]
  · rw [Categorification.NilHecke.Diagram.ψ_of_le k (by omega), map_zero]
    exact zero_mem _

/-! ### Degrees of nilHecke elements in the corner -/

section NilHeckeDegrees

open Categorification.NilHecke

variable {A : Type*} [AddCommGroup A] (deg : (sig D).Gen → A) (δ : A) (i : I)
  (hi : D.parity i = 0) (r : ℕ)

/-- Polynomials in the dots, as an algebra map to the corner. -/
def evenDots : MvPolynomial (Fin r) ℤ →ₐ[ℤ] Corner D Sc i r :=
  (evenNilHecke D Sc i hi r).comp ((mulPoly ℤ r).codRestrict (nilHecke ℤ r) mulPoly_mem)

theorem evenDots_apply (p : MvPolynomial (Fin r) ℤ) :
    evenDots D Sc i hi r p = evenNilHecke D Sc i hi r ⟨mulPoly ℤ r p, mulPoly_mem p⟩ := rfl

variable {deg δ i} (hd : deg (.dot i) = (2 : ℤ) • δ) (hc : deg (.cross i i) = (-2 : ℤ) • δ)
include hd

theorem evenDots_prod_mem (e : Fin r → ℕ) (s : Finset (Fin r)) :
    evenDots D Sc i hi r (∏ a ∈ s, MvPolynomial.X a ^ e a) ∈
      cornerDeg D Sc deg i r ((∑ a ∈ s, 2 * (e a : ℤ)) • δ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_cornerDeg D Sc deg i r
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb, add_smul, map_mul, map_pow]
    refine mul_mem_cornerDeg D Sc deg ?_ ih
    have hX : evenDots D Sc i hi r (MvPolynomial.X b) ∈ cornerDeg D Sc deg i r ((2 : ℤ) • δ) :=
      hd ▸ evenNilHecke_mulX_mem D Sc i hi r deg b
    clear ih hb
    induction e b with
    | zero => simpa using one_mem_cornerDeg D Sc deg i r
    | succ n ihn =>
      rw [pow_succ, show 2 * ((n + 1 : ℕ) : ℤ) = 2 * (n : ℤ) + 2 by push_cast; ring, add_smul]
      exact mul_mem_cornerDeg D Sc deg ihn hX

omit hd in
include hc in
theorem evenNilHecke_ddw_mem (ρ : List ℕ) :
    evenNilHecke D Sc i hi r ⟨ddw ρ, ddw_mem ρ⟩ ∈
      cornerDeg D Sc deg i r ((-2 * (ρ.length : ℤ)) • δ) := by
  induction ρ with
  | nil =>
    have : (⟨ddw [], ddw_mem []⟩ : nilHecke ℤ r) = 1 := rfl
    rw [this, map_one, List.length_nil, Nat.cast_zero, mul_zero, zero_smul]
    exact one_mem_cornerDeg D Sc deg i r
  | cons j ρ ih =>
    have : (⟨ddw (j :: ρ), ddw_mem _⟩ : nilHecke ℤ r) =
        ⟨dd ℤ r j, dd_mem j⟩ * ⟨ddw ρ, ddw_mem ρ⟩ := Subtype.ext (ddw_cons j ρ)
    rw [this, map_mul, List.length_cons,
      show -2 * ((ρ.length + 1 : ℕ) : ℤ) = -2 + -2 * (ρ.length : ℤ) by push_cast; ring, add_smul]
    exact mul_mem_cornerDeg D Sc deg (hc ▸ evenNilHecke_dd_mem D Sc i hi r j deg) ih

theorem evenDots_xDelta_mem :
    evenDots D Sc i hi r (xDelta r) ∈ cornerDeg D Sc deg i r ((2 * (r.choose 2 : ℤ)) • δ) := by
  have h := evenDots_prod_mem D Sc hi r hd (fun a => r - 1 - a) Finset.univ
  rw [← Finset.mul_sum, ← Nat.cast_sum,
    Categorification.KLR.KLRAlgebra.sum_fin_sub_one_sub] at h
  exact h

theorem evenDots_yDelta_mem :
    evenDots D Sc i hi r (yDelta r) ∈ cornerDeg D Sc deg i r ((2 * (r.choose 2 : ℤ)) • δ) := by
  have h := evenDots_prod_mem D Sc hi r hd
    (fun a => if (a : ℕ) < r then (a : ℕ) else 0) Finset.univ
  have hs : ∑ a : Fin r, (if (a : ℕ) < r then (a : ℕ) else 0) = r.choose 2 := by
    simp only [Fin.is_lt, ite_true]
    rw [Fin.sum_univ_eq_sum_range (fun a => a) r, Finset.sum_range_id, Nat.choose_two_right]
  rw [← Finset.mul_sum, ← Nat.cast_sum, hs] at h
  exact h

include hc in
/-- The even divided-power idempotent `π_{w_0}` has degree `0`. -/
theorem evenNilHecke_demIdem_mem :
    evenNilHecke D Sc i hi r ⟨demIdem ℤ r, demIdem_mem⟩ ∈ cornerDeg D Sc deg i r 0 := by
  have : (⟨demIdem ℤ r, demIdem_mem⟩ : nilHecke ℤ r) =
      ⟨ddw (w0Word r), ddw_mem _⟩ * ⟨mulPoly ℤ r (yDeltaSign r), mulPoly_mem _⟩ :=
    Subtype.ext demIdem_eq
  have hy : evenDots D Sc i hi r (yDeltaSign r) ∈
      cornerDeg D Sc deg i r ((2 * (r.choose 2 : ℤ)) • δ) := by
    have h := evenDots_yDelta_mem D Sc hi r hd
    rcases neg_one_pow_eq_or ℤ (r.choose 2) with he | he
    · simpa only [yDeltaSign, he, one_smul] using h
    · simpa only [yDeltaSign, he, neg_smul, one_smul, map_neg] using neg_mem h
  rw [evenDots_apply] at hy
  rw [this, map_mul]
  have h := mul_mem_cornerDeg D Sc deg (evenNilHecke_ddw_mem D Sc hi r hc (w0Word r)) hy
  rw [length_w0Word, ← add_smul, show -2 * (r.choose 2 : ℤ) + 2 * (r.choose 2 : ℤ) = 0 by ring,
    zero_smul] at h
  exact h

include hc in
/-- `a = x^δ π_{w_0}` has degree `r(r-1)` (in units of `δ`). -/
theorem evenNilHecke_demA_mem :
    evenNilHecke D Sc i hi r ⟨demA ℤ r, demA_mem⟩ ∈
      cornerDeg D Sc deg i r ((2 * (r.choose 2 : ℤ)) • δ) := by
  have : (⟨demA ℤ r, demA_mem⟩ : nilHecke ℤ r) =
      ⟨mulPoly ℤ r (xDelta r), mulPoly_mem _⟩ * ⟨demIdem ℤ r, demIdem_mem⟩ := rfl
  rw [this, map_mul]
  have hx := evenDots_xDelta_mem D Sc hi r hd
  rw [evenDots_apply] at hx
  simpa using mul_mem_cornerDeg D Sc deg hx (evenNilHecke_demIdem_mem D Sc hi r hd hc)

omit hd in
include hc in
/-- `b = ∂_{w_0}` has degree `-r(r-1)` (in units of `δ`). -/
theorem evenNilHecke_ddw_w0Word_mem :
    evenNilHecke D Sc i hi r ⟨ddw (w0Word r), ddw_mem _⟩ ∈
      cornerDeg D Sc deg i r ((-(2 * (r.choose 2 : ℤ))) • δ) := by
  have h := evenNilHecke_ddw_mem D Sc hi r hc (w0Word r)
  rw [length_w0Word, show -2 * (r.choose 2 : ℤ) = -(2 * (r.choose 2 : ℤ)) by ring] at h
  exact h

end NilHeckeDegrees

/-! ### The KLR algebra `R(r·i)` and its map to the corner -/

section KLRTransfer

open Categorification Categorification.KLR Categorification.KLR.KLRAlgebra
  Categorification.NilHecke

/-- The KL I quiver Hecke algebra `R(r·i)` on one vertex, over `ℤ` (`≅ NH_r`). -/
abbrev KLRr (r : ℕ) := R1 ℤ (⊥ : SimpleGraph Unit) (Multiset.replicate r ())

/-- The algebra map `R(r·i) ≅ NH_r → End(i^r)`. -/
def evenPhi (i : I) (hi : D.parity i = 0) (r : ℕ) : KLRr r →ₐ[ℤ] Corner D Sc i r :=
  (evenNilHecke D Sc i hi r).comp
    (nilHeckeEquiv (klQ (k := ℤ) (⊥ : SimpleGraph Unit)) () r).toAlgHom

theorem evenPhi_apply (i : I) (hi : D.parity i = 0) (r : ℕ) (z : KLRr r) :
    evenPhi D Sc i hi r z = evenNilHecke D Sc i hi r (nilHeckeEquiv _ () r z) := rfl

/-- **Transfer of degrees** to the corner: an element of degree `d` of `R(r·i)` (KL I grading,
`deg x = 2`, `deg ψ = -2`) maps to degree `d • δ` whenever a dot has degree `2 • δ` and a
crossing `-2 • δ`. -/
theorem evenPhi_mem_degree {A : Type*} [AddCommGroup A] {deg : (sig D).Gen → A} {δ : A}
    {i : I} (hi : D.parity i = 0) (r : ℕ)
    (hd : deg (.dot i) = (2 : ℤ) • δ) (hc : deg (.cross i i) = (-2 : ℤ) • δ)
    {d : ℤ} {z : KLRr r} (hz : z ∈ (klGradingDatum ℤ (⊥ : SimpleGraph Unit)).grade _ d) :
    evenPhi D Sc i hi r z ∈ cornerDeg D Sc deg i r (d • δ) := by
  refine grade_transfer (klGradingDatum ℤ (⊥ : SimpleGraph Unit))
    (fun d => (cornerDeg D Sc deg i r (d • δ)).restrictScalars ℤ) ?_ ?_
    (evenPhi D Sc i hi r) ?_ ?_ ?_ hz
  · simpa using one_mem_cornerDeg D Sc deg i r
  · intro d d' y z hy hz
    have h := mul_mem_cornerDeg D Sc deg hy hz
    rwa [← add_smul] at h
  · intro t
    simpa [evenPhi_apply] using one_mem_cornerDeg D Sc deg i r
  · intro a t
    have h := evenNilHecke_mulX_mem D Sc i hi r deg (Fin.cast (Multiset.card_replicate r ()) a)
    rw [hd] at h
    simpa [evenPhi_apply, klGradingDatum] using h
  · intro j t
    by_cases hj : j + 1 < Multiset.card (Multiset.replicate r ())
    · have h := evenNilHecke_dd_mem D Sc i hi r j deg
      rw [hc] at h
      rw [GradingDatum.dψ_of_lt _ hj]
      simpa [evenPhi_apply, klGradingDatum, cartan_self] using h
    · have h0 : dd ℤ r j = 0 := dd_eq_zero (by simpa using hj)
      have h0' : (⟨0, zero_mem _⟩ : nilHecke ℤ r) = 0 := rfl
      simp [evenPhi_apply, h0, h0']

end KLRTransfer

/-! ### The splitting in the corner -/

section CornerSplitting

open Categorification Categorification.KLR Categorification.KLR.KLRAlgebra
  Categorification.NilHecke

theorem expandDiv_single (r : ℕ) :
    ((expandDiv [((), r)] : List Unit) : Multiset Unit) = Multiset.replicate r () := by
  simp [expandDiv, Multiset.coe_replicate]

/-- The unique sequence of `R(r·i)`, written as the expansion of `i^{(r)}`. -/
abbrev evenSeq (r : ℕ) : Seq (Multiset.replicate r ()) := Seq.ofList _ (expandDiv_single r)

/-- KL's graded splitting of `1_{i^r}` through `e_r` in `R(r·i)` (KL I §2.2, §2.5). -/
def evenKLRSplitting (r : ℕ) :
    GradedSplitting ℤ (⊥ : SimpleGraph Unit) (e (evenSeq r)) (divIdem (evenSeq r) [(0, r)]) :=
  Classical.choose (exists_gradedSplitting_e (k := ℤ) (Γ := (⊥ : SimpleGraph Unit))
    (isBlocks_ofList [((), r)] (expandDiv_single r)))

theorem evenKLRSplitting_spec (r : ℕ) :
    (evenKLRSplitting r).genFun = blockFactorLP r ∧
      Fintype.card (evenKLRSplitting r).ι = r.factorial := by
  have h := Classical.choose_spec (exists_gradedSplitting_e (k := ℤ)
    (Γ := (⊥ : SimpleGraph Unit)) (isBlocks_ofList [((), r)] (expandDiv_single r)))
  unfold evenKLRSplitting
  simpa [blocksDiv] using h

private theorem card_replicate_unit (r : ℕ) : Multiset.card (Multiset.replicate r ()) = r :=
  Multiset.card_replicate r ()

theorem nilHeckeEquiv_pol (r : ℕ) (p : MvPolynomial (Fin (Multiset.card
    (Multiset.replicate r ()))) ℤ) :
    nilHeckeEquiv (klQ (k := ℤ) (⊥ : SimpleGraph Unit)) () r (pol p) =
      ⟨mulPoly ℤ r (MvPolynomial.rename (Fin.cast (card_replicate_unit r)) p), mulPoly_mem _⟩ := by
  have h : ((nilHeckeEquiv (klQ (k := ℤ) (⊥ : SimpleGraph Unit)) () r).toAlgHom.comp pol) =
      ((mulPoly ℤ r).codRestrict (nilHecke ℤ r) mulPoly_mem).comp
        (MvPolynomial.rename (Fin.cast (card_replicate_unit r))) := by
    refine MvPolynomial.algHom_ext fun a => ?_
    apply Subtype.ext
    simp [nilHeckeEquiv_x, mulPoly_X]
  exact congrArg (fun f => f p) h

theorem nilHeckeEquiv_ψw (r : ℕ) (ρ : List ℕ) :
    nilHeckeEquiv (klQ (k := ℤ) (⊥ : SimpleGraph Unit)) () r (ψw ρ) = ⟨ddw ρ, ddw_mem ρ⟩ := by
  induction ρ with
  | nil => rw [ψw_nil, map_one]; rfl
  | cons j ρ ih =>
    rw [ψw_cons, map_mul, ih, nilHeckeEquiv_ψ]
    exact Subtype.ext (ddw_cons j ρ).symm

theorem rename_blockDelta (r : ℕ) :
    MvPolynomial.rename (Fin.cast (card_replicate_unit r))
      (blockDelta 0 r : MvPolynomial (Fin (Multiset.card (Multiset.replicate r ()))) ℤ) =
        xDelta r := by
  rw [blockDelta, xDelta, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [dite_eq_left (show 0 + (a : ℕ) < Multiset.card (Multiset.replicate r ()) by simp)]
  simp only [map_pow, MvPolynomial.rename_X]
  congr 2
  exact Fin.ext (by simp)

/-- `1_{i^{(r)}}` of KL I is the nilHecke idempotent `e_r = x^δ ∂_{w_0}`. -/
theorem nilHeckeEquiv_divIdem (r : ℕ) :
    nilHeckeEquiv (klQ (k := ℤ) (⊥ : SimpleGraph Unit)) () r (divIdem (evenSeq r) [(0, r)]) =
      ⟨idemNH ℤ r, idemNH_mem⟩ := by
  have hw : blockWord 0 r = w0Word r := by simp [blockWord]
  rw [divIdem, blocksElt_cons, blocksElt_nil, mul_one, map_mul, nilHeckeEquiv_e, mul_one,
    blockElt, map_mul, nilHeckeEquiv_pol, nilHeckeEquiv_ψw, rename_blockDelta, hw]
  rfl

private theorem isSplitting_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S) {ι : Type*}
    [Fintype ι] [DecidableEq ι] {E' : R} {E a b : ι → R} {F' : S} {F : ι → S}
    (h : Graded.IsSplitting E' E a b) (hE' : f E' = F') (hE : ∀ j, f (E j) = F j) :
    Graded.IsSplitting F' F (fun j => f (a j)) (fun j => f (b j)) where
  mul_eq i j := by
    rw [← map_mul, h.mul_eq]
    split_ifs with hij
    · exact hE j
    · exact map_zero f
  sum_eq := by
    rw [← hE', ← h.sum_eq, map_sum]
    simp only [map_mul]

variable (i : I) (hi : D.parity i = 0)

/-- BE2's even divided-power idempotent `1_{i^{(r)}} = D_{w_0}` in the corner. -/
def evenCornerProjector (r : ℕ) : Corner D Sc i r :=
  evenNilHecke D Sc i hi r ⟨demIdem ℤ r, demIdem_mem⟩

theorem evenCornerProjector_idempotent (r : ℕ) :
    IsIdempotentElem (evenCornerProjector D Sc i hi r) := by
  rw [IsIdempotentElem, evenCornerProjector, ← map_mul]
  exact congrArg _ (Subtype.ext isIdempotentElem_demIdem.eq)

/-- The index set of the even splitting: KL's `r!` summands. -/
abbrev evenIndex (r : ℕ) := (evenKLRSplitting r).ι × Unit

/-- The inclusion splitters `a_j x^δ π_{w_0}`. -/
def evenSigma (r : ℕ) (j : evenIndex r) : Corner D Sc i r :=
  evenPhi D Sc i hi r ((evenKLRSplitting r).a j.1) *
    evenNilHecke D Sc i hi r ⟨demA ℤ r, demA_mem⟩

/-- The projection splitters `∂_{w_0} b_j`. -/
def evenLam (r : ℕ) (j : evenIndex r) : Corner D Sc i r :=
  evenNilHecke D Sc i hi r ⟨ddw (w0Word r), ddw_mem _⟩ *
    evenPhi D Sc i hi r ((evenKLRSplitting r).b j.1)

theorem isSplitting_even (r : ℕ) :
    Graded.IsSplitting (1 : Corner D Sc i r) (fun _ => evenCornerProjector D Sc i hi r)
      (evenSigma D Sc i hi r) (evenLam D Sc i hi r) := by
  have T1 := isSplitting_map (evenPhi D Sc i hi r).toRingHom (evenKLRSplitting r).split
    (F' := 1) (F := fun _ => evenNilHecke D Sc i hi r ⟨idemNH ℤ r, idemNH_mem⟩)
    (by simp [evenPhi_apply])
    (fun _ => by simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, evenPhi_apply,
      nilHeckeEquiv_divIdem])
  have T2 : Graded.IsSplitting (evenNilHecke D Sc i hi r ⟨idemNH ℤ r, idemNH_mem⟩)
      (fun _ : Unit => evenCornerProjector D Sc i hi r)
      (fun _ => evenNilHecke D Sc i hi r ⟨demA ℤ r, demA_mem⟩)
      (fun _ => evenNilHecke D Sc i hi r ⟨ddw (w0Word r), ddw_mem _⟩) :=
    { mul_eq := fun a b => by
        rw [show a = b from Subsingleton.elim _ _, ite_eq_left rfl, evenCornerProjector,
          ← map_mul]
        exact congrArg _ (Subtype.ext ddw_mul_demA)
      sum_eq := by
        rw [Fintype.sum_unique, ← map_mul]
        exact congrArg _ (Subtype.ext demA_mul_ddw) }
  exact T1.trans T2 (evenCornerProjector_idempotent D Sc i hi r) IsIdempotentElem.one

/-- The splitting of the corner unit into `r!` copies of `1_{i^{(r)}}`. -/
def evenCornerSplitting (r : ℕ) :
    OddMath.Frontier.Categorification.Splitting (1 : Corner D Sc i r)
      (evenCornerProjector D Sc i hi r) (evenIndex r) where
  σ := evenSigma D Sc i hi r
  lam := evenLam D Sc i hi r
  sum_eq := (isSplitting_even D Sc i hi r).sum_eq
  orth a b := (isSplitting_even D Sc i hi r).mul_eq a b
  mul_sigma _ := one_mul _
  lam_mul _ := mul_one _

theorem card_evenIndex (r : ℕ) : Fintype.card (evenIndex r) = r.factorial := by
  rw [Fintype.card_prod, Fintype.card_unit, mul_one, (evenKLRSplitting_spec r).2]

/-- The degree shifts of the summands, in KL units (`deg x = 2`). -/
def evenShift (r : ℕ) (j : evenIndex r) : ℤ := (evenKLRSplitting r).dg j.1 + 2 * (r.choose 2 : ℤ)

/-- **The multiplicity**: `∑_j q^{evenShift j} = q^{r(r-1)/2} [r]!`. -/
theorem sum_T_evenShift (r : ℕ) :
    ∑ j : evenIndex r, (LaurentPolynomial.T (evenShift r j) : LaurentPolynomial ℤ) =
      LaurentPolynomial.T (r.choose 2 : ℤ) * QuantumGroup.qfact qUnitLP r := by
  have h := (evenKLRSplitting_spec r).1
  rw [GradedSplitting.genFun, blockFactorLP] at h
  simp only [evenShift, Fintype.sum_prod_type, Fintype.sum_unique, LaurentPolynomial.T_add,
    ← Finset.sum_mul, h]
  rw [mul_comm, ← mul_assoc, ← LaurentPolynomial.T_add]
  congr 2
  ring

variable {A : Type*} [AddCommGroup A] {deg : (sig D).Gen → A} {δ : A}
  (hd : deg (.dot i) = (2 : ℤ) • δ) (hc : deg (.cross i i) = (-2 : ℤ) • δ)
include hd hc

theorem evenSigma_mem (r : ℕ) (j : evenIndex r) :
    evenSigma D Sc i hi r j ∈ cornerDeg D Sc deg i r (evenShift r j • δ) := by
  rw [evenShift, add_smul]
  exact mul_mem_cornerDeg D Sc deg
    (evenPhi_mem_degree D Sc hi r hd hc ((evenKLRSplitting r).mem_a _))
    (evenNilHecke_demA_mem D Sc hi r hd hc)

theorem evenLam_mem (r : ℕ) (j : evenIndex r) :
    evenLam D Sc i hi r j ∈ cornerDeg D Sc deg i r ((-evenShift r j) • δ) := by
  rw [evenShift, show -((evenKLRSplitting r).dg j.1 + 2 * (r.choose 2 : ℤ)) =
    -(2 * (r.choose 2 : ℤ)) + -(evenKLRSplitting r).dg j.1 by ring, add_smul]
  exact mul_mem_cornerDeg D Sc deg (evenNilHecke_ddw_w0Word_mem D Sc hi r hc)
    (evenPhi_mem_degree D Sc hi r hd hc ((evenKLRSplitting r).mem_b _))

end CornerSplitting

/-! ### Integer degree and parity -/

section Bidegree

variable (sy : SKM.Symmetrizer D) {i : I}

theorem gdeg_dot_eq : gdeg D sy (.dot i) = (2 : ℤ) • sy.d i := by
  simp [gdeg]

theorem gdeg_cross_self_eq : gdeg D sy (.cross i i) = (-2 : ℤ) • sy.d i := by
  simp [gdeg, D.d_self, mul_comm]

variable {D} in
theorem parityDeg_dot_eq (hi : D.parity i = 0) :
    Presentation.parityDeg (sig D) (.dot i) = (2 : ℤ) • (0 : ZMod 2) := by
  simp [Presentation.parityDeg, sig, Shape.parity, hi]

variable {D} in
theorem parityDeg_cross_self_eq (hi : D.parity i = 0) :
    Presentation.parityDeg (sig D) (.cross i i) = (-2 : ℤ) • (0 : ZMod 2) := by
  simp [Presentation.parityDeg, sig, Shape.parity, hi]

end Bidegree

end OddMath.QuiverHecke

/-! ### The decomposition in `H_n` -/

namespace OddMath.QuiverHecke.DividedPowerModules
open CategoryTheory StringDiagrams OddMath.Frontier

universe u' v' w'
variable {I : Type u'} {X : Type v'} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w'} [CommRing k] (Sc : SKM.Scalars D k)

/-- BE2's even divided-power idempotent `1_{i^{(r)}} = D_{w_0}` of `H_r`. -/
def evenIdempotent (i : I) (hi : D.parity i = 0) (r : ℕ) : Hn D Sc r :=
  Hn.sameColourInclusion i r (evenCornerProjector D Sc i hi r)

theorem evenIdempotent_idempotent (i : I) (hi : D.parity i = 0) (r : ℕ) :
    evenIdempotent D Sc i hi r * evenIdempotent D Sc i hi r = evenIdempotent D Sc i hi r := by
  simp only [evenIdempotent, ← map_mul, (evenCornerProjector_idempotent D Sc i hi r).eq]

/-- The unshifted even divided-power projective `H_r 1_{i^{(r)}}`. -/
abbrev evenProjective (i : I) (hi : D.parity i = 0) (r : ℕ) :=
  principal D Sc (evenIdempotent D Sc i hi r)

instance evenProjective_projective (i : I) (hi : D.parity i = 0) (r : ℕ) :
    Module.Projective (ModuleRing D Sc r) (evenProjective D Sc i hi r) :=
  projective_leftIdeal _ (by rw [← Unitization.inr_mul, evenIdempotent_idempotent])

/-- The corner splitting, included into `H_r`. -/
def evenSplittingInHn (i : I) (hi : D.parity i = 0) (r : ℕ) :
    Categorification.Splitting (Hn.wordIdempotent (D := D) (Sc := Sc) (repeatedWord i r) :
      ModuleRing D Sc r) (evenIdempotent D Sc i hi r) (evenIndex r) where
  σ j := cornerMap D Sc i r (evenSigma D Sc i hi r j)
  lam j := cornerMap D Sc i r (evenLam D Sc i hi r j)
  sum_eq := ((mapSplitting (evenCornerSplitting D Sc i hi r) (cornerMap D Sc i r)).sum_eq).trans
    (cornerMap_one D Sc i r)
  orth a b := (mapSplitting (evenCornerSplitting D Sc i hi r) (cornerMap D Sc i r)).orth a b
  mul_sigma j := by
    exact (mapSplitting (evenCornerSplitting D Sc i hi r) (cornerMap D Sc i r)).mul_sigma j
  lam_mul j := by
    exact (mapSplitting (evenCornerSplitting D Sc i hi r) (cornerMap D Sc i r)).lam_mul j

/-- **BE2 Lemma 11.1, even colours, as modules**: `H_r 1_{i^r}` is the direct sum of `r!`
copies of `H_r 1_{i^{(r)}}`. The degree shifts are `evenShift` (`sum_T_evenShift`,
`evenDecompositionInHn_degree`). -/
def evenDecompositionInHn (i : I) (hi : D.parity i = 0) (r : ℕ) :
    wordProjective D Sc i r ≃ₗ[ModuleRing D Sc r] (evenIndex r → evenProjective D Sc i hi r) :=
  (evenSplittingInHn D Sc i hi r).equiv

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

private theorem evenCorner_mem_bidegree (i : I) (r : ℕ) {d : ℤ}
    {f : Corner D Sc i r} (hint : f ∈ cornerDeg D Sc (gdeg D sy) i r (d • sy.d i))
    (hpar : f ∈ cornerDeg D Sc (Presentation.parityDeg (sig D)) i r (d • (0 : ZMod 2))) :
    Hn.sameColourInclusion i r f ∈ Hn.bidegree D Sc sy hc r (sy.d i * d, 0) := by
  rw [smul_zero] at hpar
  rw [smul_eq_mul, mul_comm] at hint
  exact Hn.single_mem_bidegree D Sc sy hc _ _ _ hint hpar

/-- `1_{i^{(r)}}` is even of degree zero. -/
theorem evenIdempotent_mem_bidegree (i : I) (hi : D.parity i = 0) (r : ℕ) :
    evenIdempotent D Sc i hi r ∈ Hn.bidegree D Sc sy hc r (0, 0) := by
  have h1 := evenNilHecke_demIdem_mem D Sc hi r (gdeg_dot_eq D sy) (gdeg_cross_self_eq D sy)
  have h2 := evenNilHecke_demIdem_mem D Sc hi r (parityDeg_dot_eq hi)
    (parityDeg_cross_self_eq hi)
  have h := evenCorner_mem_bidegree D Sc sy hc i r (d := 0)
    (by rw [zero_smul]; exact h1) (by rw [zero_smul]; exact h2)
  rw [mul_zero] at h
  exact h

theorem evenSigmaInHn_mem_bidegree (i : I) (hi : D.parity i = 0) (r : ℕ) (j : evenIndex r) :
    Hn.sameColourInclusion i r (evenSigma D Sc i hi r j) ∈
      Hn.bidegree D Sc sy hc r (sy.d i * evenShift r j, 0) :=
  evenCorner_mem_bidegree D Sc sy hc i r
    (evenSigma_mem D Sc i hi (gdeg_dot_eq D sy) (gdeg_cross_self_eq D sy) r j)
    (evenSigma_mem D Sc i hi (parityDeg_dot_eq hi) (parityDeg_cross_self_eq hi) r j)

theorem evenLamInHn_mem_bidegree (i : I) (hi : D.parity i = 0) (r : ℕ) (j : evenIndex r) :
    Hn.sameColourInclusion i r (evenLam D Sc i hi r j) ∈
      Hn.bidegree D Sc sy hc r (sy.d i * (-evenShift r j), 0) :=
  evenCorner_mem_bidegree D Sc sy hc i r
    (evenLam_mem D Sc i hi (gdeg_dot_eq D sy) (gdeg_cross_self_eq D sy) r j)
    (evenLam_mem D Sc i hi (parityDeg_dot_eq hi) (parityDeg_cross_self_eq hi) r j)

private theorem evenSplittingInHn_sigma (i : I) (hi : D.parity i = 0) (r : ℕ)
    (j : evenIndex r) :
    (evenSplittingInHn D Sc i hi r).σ j =
      (Hn.sameColourInclusion i r (evenSigma D Sc i hi r j) : ModuleRing D Sc r) := rfl

private theorem evenSplittingInHn_lam (i : I) (hi : D.parity i = 0) (r : ℕ)
    (j : evenIndex r) :
    (evenSplittingInHn D Sc i hi r).lam j =
      (Hn.sameColourInclusion i r (evenLam D Sc i hi r j) : ModuleRing D Sc r) := rfl

/-- The forward equivalence raises the integer degree of the `j`-th component by
`d_i · evenShift j` and preserves parity. -/
theorem evenDecompositionInHn_degree (i : I) (hi : D.parity i = 0) {r : ℕ}
    {d : ℤ × ZMod 2} (x : wordProjective D Sc i r) (hx : PrincipalDegree D Sc sy hc d x)
    (j : evenIndex r) :
    PrincipalDegree D Sc sy hc (d + (sy.d i * evenShift r j, 0))
      (evenDecompositionInHn D Sc i hi r x j) := by
  have h := Hn.mul_mem_bidegree D Sc sy hc hx (evenSigmaInHn_mem_bidegree D Sc sy hc i hi r j)
  change ((x : ModuleRing D Sc r) * (evenSplittingInHn D Sc i hi r).σ j).snd ∈ _
  rw [evenSplittingInHn_sigma, Unitization.snd_mul, Unitization.fst_inr,
    Unitization.snd_inr, principal_fst_zero D Sc x, zero_smul, zero_smul, zero_add, zero_add]
  exact h

private theorem moduleRing_snd_sum' {r : ℕ} {J : Type*} [Fintype J]
    (f : J → ModuleRing D Sc r) : (∑ j, f j).snd = ∑ j, (f j).snd :=
  map_sum (Unitization.sndHom k k (Hn D Sc r)) f Finset.univ

/-- The inverse equivalence sends tuples whose `j`-th component has degree
`d + (d_i · evenShift j, 0)` to degree `d`. -/
theorem evenDecompositionInHn_symm_degree (i : I) (hi : D.parity i = 0) {r : ℕ}
    {d : ℤ × ZMod 2} (y : evenIndex r → evenProjective D Sc i hi r)
    (hy : ∀ j, PrincipalDegree D Sc sy hc (d + (sy.d i * evenShift r j, 0)) (y j)) :
    PrincipalDegree D Sc sy hc d ((evenDecompositionInHn D Sc i hi r).symm y) := by
  have h : (∑ j, (y j : ModuleRing D Sc r).snd *
      Hn.sameColourInclusion i r (evenLam D Sc i hi r j)) ∈ Hn.bidegree D Sc sy hc r d := by
    apply Submodule.sum_mem
    intro j _
    have h := Hn.mul_mem_bidegree D Sc sy hc (hy j)
      (evenLamInHn_mem_bidegree D Sc sy hc i hi r j)
    have he : (d + (sy.d i * evenShift r j, (0 : ZMod 2))) +
        (sy.d i * (-evenShift r j), 0) = d := by
      apply Prod.ext <;> simp
    exact he ▸ h
  change (∑ j, (y j : ModuleRing D Sc r) * (evenSplittingInHn D Sc i hi r).lam j).snd ∈ _
  rw [moduleRing_snd_sum']
  simpa only [evenSplittingInHn_lam, Unitization.snd_mul, Unitization.fst_inr,
    Unitization.snd_inr, principal_fst_zero D Sc, zero_smul, zero_add] using h

#print axioms evenDecompositionInHn
#print axioms evenIdempotent_mem_bidegree
#print axioms evenDecompositionInHn_degree
#print axioms evenDecompositionInHn_symm_degree
#print axioms card_evenIndex
#print axioms sum_T_evenShift

end OddMath.QuiverHecke.DividedPowerModules
