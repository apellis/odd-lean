/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleCoefficientGenerators
import OddMath.SKM.SpanBubbleProd

/-!
# Full coefficient parity and bubble placement

The polynomial/exterior basis defines an involution on `SYM`. Its evaluated
basis vectors have their actual exterior parity, so super interchange moves
arbitrary coefficients across a homogeneous diagram by this involution.
No coefficient independence or oriented nondegeneracy is assumed.
-/

noncomputable section
open CategoryTheory StringDiagrams Presentation
namespace OddMath.SKM
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
namespace SYM
variable (D) (k : Type w) [CommRing k]
def parityTwist (q : ZMod 2) : SYM D k →ₗ[k] SYM D k :=
  (coefficientBasis D k).constr k
    (fun a => zsign k (q * (a.2.card : ZMod 2)) • coefficientBasis D k a)
@[simp] theorem parityTwist_basis (q : ZMod 2) (a : CoefficientIndex D) :
    parityTwist D k q (coefficientBasis D k a) =
      zsign k (q * (a.2.card : ZMod 2)) • coefficientBasis D k a := by
  exact (coefficientBasis D k).constr_basis k _ a
theorem parityTwist_comp (q : ZMod 2) :
    (parityTwist D k q).comp (parityTwist D k q) = LinearMap.id := by
  apply (coefficientBasis D k).ext
  intro a
  simp only [LinearMap.comp_apply, parityTwist_basis, map_smul, smul_smul,
    zsign_mul_self', one_smul, LinearMap.id_apply]
@[simp] theorem parityTwist_involutive (q : ZMod 2) (c : SYM D k) :
    parityTwist D k q (parityTwist D k q c) = c :=
  LinearMap.congr_fun (parityTwist_comp D k q) c
end SYM
variable {k : Type w} [CommRing k] {Sc : Scalars D k}
variable (cs : CScalars Sc) (μ : X)

private theorem beta_one_mem :
    (1 : End ((pres D Sc).obj (ob D μ []))) ∈ closedPar D Sc μ 0 := by
  simpa only [cl_nil, parsum_nil, End.one_def] using
    (cl_mem_closedPar (D := D) (Sc := Sc) (μ := μ) (L := []) (by rfl) rfl)

theorem beta_polynomialInclude_mem (p : MvPolynomial (I × ℕ) k) :
    betaSYM cs μ (SYM.polynomialInclude D k p) ∈ closedPar D Sc μ 0 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes,
        Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ a (beta_one_mem (D := D) (Sc := Sc) μ)
  | add p q hp hq =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hp hq
  | mul_X p a hp =>
      rw [map_mul, map_mul, SYM.polynomialInclude_X]
      have he : betaSYM cs μ (SYM.e D k a.1 a.2) ∈ closedPar D Sc μ 0 := by
        rw [SYM.e, betaSYM_ι]
        exact betaSYMGen_polynomial_mem cs μ a
      simpa only [End.mul_def, zero_add] using comp_mem_closedPar he hp

theorem beta_delta_product_mem (l : List {i : I // D.parity i = 1}) :
    betaSYM cs μ ((l.map (SYM.delta D k)).prod) ∈
      closedPar D Sc μ (l.length : ZMod 2) := by
  induction l with
  | nil => simpa using beta_one_mem (D := D) (Sc := Sc) μ
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, betaSYM_delta,
        List.length_cons, Nat.cast_add, Nat.cast_one]
      have hi : oddBubble cs i μ ∈ closedPar D Sc μ 1 := by
        simpa only [i.property] using oddBubble_mem cs i μ
      simpa only [End.mul_def] using comp_mem_closedPar ih hi

theorem beta_oddExteriorBasis_mem (s : Finset {i : I // D.parity i = 1}) :
    betaSYM cs μ (SYM.exteriorInclude D k (SYM.oddExteriorBasis D k s)) ∈
      closedPar D Sc μ (s.card : ZMod 2) := by
  let : LinearOrder {i : I // D.parity i = 1} := WellOrderingRel.isWellOrder.linearOrder
  let b : Module.Basis _ k (SYM.OddModule D k) := Finsupp.basisSingleOne
  change betaSYM cs μ (SYM.exteriorInclude D k (b.ExteriorAlgebra s)) ∈ _
  rw [ExteriorAlgebra.basis_apply_ofCard b (rfl : s.card = s.card)]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply]
  let f := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (rfl : s.card = s.card))
  have he : SYM.exteriorInclude D k
      ((List.ofFn fun j => ExteriorAlgebra.ι k (b (f j))).prod) =
      ((List.ofFn f).map (SYM.delta D k)).prod := by
    rw [map_list_prod, List.map_ofFn, List.map_ofFn]
    congr 2
    funext j
    simp [b, SYM.exteriorInclude_ι]
  change betaSYM cs μ (SYM.exteriorInclude D k
    ((List.ofFn fun j => ExteriorAlgebra.ι k (b (f j))).prod)) ∈ _
  rw [he]
  simpa only [List.length_ofFn] using beta_delta_product_mem cs μ (List.ofFn f)

theorem beta_coefficientBasis_mem (a : SYM.CoefficientIndex D) :
    betaSYM cs μ (SYM.coefficientBasis D k a) ∈
      closedPar D Sc μ (a.2.card : ZMod 2) := by
  have he : SYM.coefficientBasis D k a =
      SYM.polynomialInclude D k (MvPolynomial.monomial a.1 1) *
        SYM.exteriorInclude D k (SYM.oddExteriorBasis D k a.2) := by
    have h := congrArg (SYM.polynomialExteriorEquiv D k).symm
      (SYM.coefficientBasis_projection D k a)
    simpa only [AlgEquiv.symm_apply_apply, SYM.polynomialExteriorEquiv,
      AlgEquiv.ofAlgHom_symm_apply, SYM.polynomialExteriorInclude_tmul] using h
  rw [he, map_mul]
  simpa only [End.mul_def, add_zero] using
    comp_mem_closedPar (beta_oddExteriorBasis_mem cs μ a.2)
      (beta_polynomialInclude_mem cs μ (MvPolynomial.monomial a.1 1))

/-- Moving arbitrary coefficients past a homogeneous diagram applies the parity
involution; this retains every exterior monomial. -/
theorem source_target_twist {s t : List (Letter I)} {q : ZMod 2}
    {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    (hf : f ∈ homPar D Sc μ s t q) (c : SYM D k) :
    bubAt D Sc μ s (betaSYM cs μ (SYM.parityTwist D k q c)) ≫ f =
      f ≫ bubAt D Sc μ t (betaSYM cs μ c) := by
  let L : SYM D k →ₗ[k] ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :=
    { toFun := fun p => bubAt D Sc μ s (betaSYM cs μ (SYM.parityTwist D k q p)) ≫ f
      map_add' := fun p r => by simp only [map_add, Preadditive.add_comp]
      map_smul' := fun r p => by simp only [map_smul, Linear.smul_comp, RingHom.id_apply] }
  let R : SYM D k →ₗ[k] ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :=
    { toFun := fun p => f ≫ bubAt D Sc μ t (betaSYM cs μ p)
      map_add' := fun p r => by simp only [map_add, Preadditive.comp_add]
      map_smul' := fun r p => by simp only [map_smul, Linear.comp_smul, RingHom.id_apply] }
  have he : L = R := by
    apply (SYM.coefficientBasis D k).ext
    intro a
    change bubAt D Sc μ s (betaSYM cs μ (SYM.parityTwist D k q
      (SYM.coefficientBasis D k a))) ≫ f = _
    rw [SYM.parityTwist_basis, map_smul, map_smul, Linear.smul_comp]
    exact (comp_bubAt hf (beta_coefficientBasis_mem cs μ a)).symm
  exact LinearMap.congr_fun he c
end OddMath.SKM
