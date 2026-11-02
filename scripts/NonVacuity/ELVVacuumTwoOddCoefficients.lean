import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientAnnihilation
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSupport
import OddMath.QuiverHecke.CyclotomicAction.ELVParabolicSpan
import OddMath.SKM.BubbleSubstitution

/-! The actual empty old representable distinguishes the order of two
different odd coefficients. Both operators are applied to its identity vector.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open scoped TensorProduct
namespace NonVacuity.ELVVacuumTwoOddCoefficients

private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 4
private abbrev C := OldCategory D Sc cutoff
private def v : C := ⟨[]⟩
private def M := oldRepresentable D Sc cutoff v
private def delta (i : Bool) : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff :=
  SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D ℚ ⟨i, rfl⟩)
private def coeff (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff) : v ⟶ v :=
  coefficientEndomorphism D Sc cutoff [] a

private abbrev OddColour := {i : Bool // D.parity i = 1}
private def i₀ : OddColour := ⟨false, rfl⟩
private def i₁ : OddColour := ⟨true, rfl⟩

private theorem exterior_product_ne_zero :
    SKM.SYM.oddExteriorBasis D ℚ {i₀} * SKM.SYM.oddExteriorBasis D ℚ {i₁} ≠ 0 := by
  classical
  let : LinearOrder OddColour := WellOrderingRel.isWellOrder.linearOrder
  let ss := Set.powersetCard.ofCard (Finset.card_singleton i₀)
  let tt := Set.powersetCard.ofCard (Finset.card_singleton i₁)
  have hd : Disjoint ss.val tt.val := by
    change Disjoint ({i₀} : Finset OddColour) {i₁}
    simp only [Finset.disjoint_singleton]
    intro he
    have := congrArg Subtype.val he
    cases this
  have he := ExteriorAlgebra.basis_mul_of_disjoint
    (Finsupp.basisSingleOne : Module.Basis OddColour ℚ (SKM.SYM.OddModule D ℚ)) ss tt hd
  have hb := (Finsupp.basisSingleOne :
    Module.Basis OddColour ℚ (SKM.SYM.OddModule D ℚ)).ExteriorAlgebra.ne_zero
      (Set.powersetCard.disjUnion hd)
  intro hz
  change (Finsupp.basisSingleOne :
      Module.Basis OddColour ℚ (SKM.SYM.OddModule D ℚ)).ExteriorAlgebra ss *
    (Finsupp.basisSingleOne :
      Module.Basis OddColour ℚ (SKM.SYM.OddModule D ℚ)).ExteriorAlgebra tt = 0 at hz
  have hh := he.symm.trans hz
  rw [Units.smul_def] at hh
  exact hb ((Units.isUnit (Set.powersetCard.permOfDisjoint hd).sign).smul_eq_zero.mp hh)

private theorem source_product_ne_zero :
    SKM.SYM.delta D ℚ i₀ * SKM.SYM.delta D ℚ i₁ ≠ 0 := by
  intro hz
  have he := congrArg (SKM.SYM.exteriorProjection D ℚ) hz
  simp only [map_mul, SKM.SYM.exteriorProjection_delta, map_zero] at he
  apply exterior_product_ne_zero
  simpa only [SKM.SYM.oddExteriorBasis_singleton] using he

private theorem quotient_product_ne_zero : delta false * delta true ≠ 0 := by
  have hm := SKM.SYM.coefficientAtMost_mul D ℚ
    (SKM.SYM.delta_mem_coefficientAtMost D ℚ i₀)
    (SKM.SYM.delta_mem_coefficientAtMost D ℚ i₁)
  intro hz
  have he : SKM.SYM.elvCoefficientQuotient D cutoff
      (SKM.SYM.delta D ℚ i₀ * SKM.SYM.delta D ℚ i₁) = 0 := by
    simpa only [map_mul, delta, i₀, i₁] using hz
  have hi := SKM.SYM.elvCoefficient_quotient_injective D ℚ
    (cutoff := cutoff) (d := 2) (fun _ => by change 2 ≤ 4; decide)
  have hh := hi (a₁ := ⟨_, hm⟩) (a₂ := 0) he
  exact source_product_ne_zero (congrArg Subtype.val hh)

private def vacuumNF : NFIdx ([] : List Bool) [] := by
  have hc : Categorification.TypeA.canWord 0 (1 : Equiv.Perm (Fin 0)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, List.length_nil, hc, cw, List.reverse_nil, List.nil_append,
    pl, SChain]

private def affineVacuumCoordinate :
    ((pres D Sc).obj (ob D []) ⟶ (pres D Sc).obj (ob D [])) →ₗ[ℚ] ℚ :=
  (basisNF D Sc [] []).coord vacuumNF

private theorem affineVacuumCoordinate_id : affineVacuumCoordinate (𝟙 _) = 1 := by
  rw [← vacuum_nf D Sc vacuumNF, affineVacuumCoordinate, ← basisNF_apply]
  change ((basisNF D Sc [] []).repr ((basisNF D Sc [] []) vacuumNF)) vacuumNF = 1
  simp only [Module.Basis.repr_self, Finsupp.single_eq_same]

private theorem coeff_ne_zero
    (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff) (ha : a ≠ 0) :
    coeff a ≠ 0 := by
  intro hz
  have hm := (Submodule.Quotient.mk_eq_zero (ideal D Sc cutoff [] [])).mp hz
  have hr : ELVPScalar.scalar D Sc cutoff [] a = 0 := by
    simpa only [ideal_nil, Submodule.mem_bot] using hm
  let extract := (TensorProduct.rid ℚ
    (SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff)).toLinearMap.comp
      (TensorProduct.map LinearMap.id affineVacuumCoordinate)
  have hh := congrArg extract hr
  have he : extract (a ⊗ₜ[ℚ] (𝟙 ((pres D Sc).obj (ob D [])))) = a := by
    change (TensorProduct.rid ℚ (SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff))
      (a ⊗ₜ[ℚ] affineVacuumCoordinate (𝟙 _)) = a
    rw [affineVacuumCoordinate_id, TensorProduct.rid_tmul, one_smul]
  change extract (a ⊗ₜ[ℚ] (𝟙 ((pres D Sc).obj (ob D [])))) = extract 0 at hh
  apply ha
  simpa only [he, map_zero] using hh

private theorem action_order
    (a b : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff) :
    M.map (coeff b) (M.map (coeff a) (𝟙 v)) = coeff (b * a) := by
  change ((𝟙 v) ≫ coeff a) ≫ coeff b = _
  rw [Category.id_comp]
  exact coefficientEndomorphism_comp D Sc cutoff [] a b

example : M.map (coeff (delta true)) (M.map (coeff (delta false)) (𝟙 v)) =
    coeff (delta true * delta false) := action_order _ _

example : M.map (coeff (delta false)) (M.map (coeff (delta true)) (𝟙 v)) =
    coeff (delta false * delta true) := action_order _ _

/-- The product survives both coefficient and old cyclotomic quotients. -/
example : M.map (coeff (delta false)) (M.map (coeff (delta true)) (𝟙 v)) ≠ 0 := by
  rw [action_order]
  exact coeff_ne_zero _ quotient_product_ne_zero

private theorem delta_anticommute : delta false * delta true = -(delta true * delta false) := by
  change SKM.SYM.elvCoefficientQuotient D cutoff _ *
    SKM.SYM.elvCoefficientQuotient D cutoff _ = -(_ * _)
  rw [← map_mul, SKM.SYM.delta_anticommute, map_neg, map_mul]
  rfl

/-- Reversing the two actual odd coefficient actions changes the sign. -/
example : M.map (coeff (delta true)) (M.map (coeff (delta false)) (𝟙 v)) =
    -(M.map (coeff (delta false)) (M.map (coeff (delta true)) (𝟙 v))) := by
  rw [action_order, action_order]
  have hh := congrArg coeff delta_anticommute
  have hn (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff) :
      coeff (-a) = -coeff a := by
    simp only [coeff, coefficientEndomorphism, map_neg]
  rw [hn] at hh
  simpa only [neg_neg] using congrArg Neg.neg hh.symm

end NonVacuity.ELVVacuumTwoOddCoefficients
