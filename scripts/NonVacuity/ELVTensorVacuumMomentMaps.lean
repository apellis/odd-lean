import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumMomentMaps
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerCoefficients
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.SKM.BubbleSubstitution
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open scoped TensorProduct
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor ELVOld.PowerVacuumCoefficient
open ELVOld.ProbeVacuumCap
namespace NonVacuity.ELVTensorVacuumMomentMaps
private theorem nonzero_of_linear_image {U V : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V] (f : U →ₗ[ℚ] V) (u : U) (v : V)
    (hv : v ≠ 0) (he : f u = v) : u ≠ 0 := by
  intro hu
  exact hv (he.symm.trans ((congrArg f hu).trans f.map_zero))
private theorem module_map_nonzero
    {C : Type*} [Category* C] [Preadditive C] [Linear ℚ C] [Supercategory ℚ C]
    {M N : Superfunctor ℚ C (SVec ℚ)} (f : M ⟶ N) (w : C)
    (u : M.obj w) (v : N.obj w) (hv : v ≠ 0) (he : f.total w u = v) : f ≠ 0 := by
  intro hf
  have hz : f.total w u = 0 := by
    rw [hf]
    simp only [SuperNatTrans.total, Superfunctor.zero_app, zero_add, SVec.zero_apply]
  exact hv (he.symm.trans hz)
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (_ : Bool) : ℕ := 2
private def cutoff (i : Bool) : ℕ := if i then 5 else 4
private def L (_ : Bool × ℕ) : ℕ := 4
private abbrev bound := SKM.SYM.elvPowerWeightBound D cutoff L + 1
private abbrev R₀ := contentModuleTarget D Sc cutoff bound (0 : Multiset Bool)
private abbrev W : ContentModules D Sc cutoff bound 0 :=
  (restriction (contentInclusion D Sc cutoff bound 0)).obj (weightedVacuum D Sc cutoff L)
private def H : modulePiCategory D Sc m ⟶ R₀ := VacuumTensor.probeFunctor D Sc m cutoff bound W
private abbrev N₀ := probeOldVacuumRegular D Sc m
private abbrev star : ContentCategory D Sc cutoff bound 0 := ⟨⟨[]⟩, rfl⟩
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private theorem large (i : Bool) : 4 ≤ cutoff i := by cases i <;> decide
private theorem powers_high (a : Bool × ℕ) : 4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega
private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private def deltaClass : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨false, rfl⟩)
private theorem delta_ne_zero : deltaClass ≠ 0 := by
  intro hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 1 4 (by decide) large powers_high
  have he := hi (a₁ := ⟨_, SKM.SYM.delta_mem_coefficientAtMost D ℚ ⟨false, rfl⟩⟩) (a₂ := 0)
    (by simpa only [deltaClass, ZeroMemClass.coe_zero, map_zero] using hz)
  have hδ : SKM.SYM.delta D ℚ ⟨false, rfl⟩ ≠ 0 := by
    rw [← SKM.SYM.coefficientBasis_delta]
    exact (SKM.SYM.coefficientBasis D ℚ).ne_zero _
  exact hδ (congrArg Subtype.val he)
private def occupied : (H.obj N₀).obj star :=
  (weightedEmptyEquiv D Sc cutoff L deltaClass) ⊗ₜ[ℚ] (probeVacuumScalarEquiv D Sc m 1)
private abbrev e := VacuumTensor.probeVacuumIso D Sc m cutoff bound W
private theorem vacuum_vector_nonzero : weightedEmptyEquiv D Sc cutoff L deltaClass ≠ 0 := by
  intro hz
  exact delta_ne_zero ((weightedEmptyEquiv D Sc cutoff L).injective (hz.trans (map_zero _).symm))
private theorem image_occupied : e.hom.total star occupied = weightedEmptyEquiv D Sc cutoff L deltaClass :=
  VacuumTensor.probeVacuumIso_hom_tmul D Sc m cutoff bound W star _

private abbrev K (i : Bool) := contentAppendTo D Sc cutoff bound (0 : Multiset Bool) [i]
  ((0 : Multiset Bool) + ([i] : Multiset Bool)) (contentBlockCanonicalSum 0 [i])
private abbrev hDot (i : Bool) := contentBlockMatrixDot_supernatural D Sc cutoff bound 0 i
private theorem reservoir_positive (i : Bool) : 0 < cutoff i := by have := large i; omega
private def inverse (i : Bool) := Classical.choice
  (contentAbsentUnitInverse_nonempty D Sc cutoff bound 0 i (by simp) (H.obj N₀))
private theorem module_id_ne_zero
    {C : Type*} [Category* C] [Preadditive C] [Linear ℚ C] [Supercategory ℚ C]
    (M : Superfunctor ℚ C (SVec ℚ)) (w : C) (z : M.obj w) (hz : z ≠ 0) : (𝟙 M : M ⟶ M) ≠ 0 := by
  intro h
  have hh := congrArg (fun f : M ⟶ M => f.total w z) h
  simp only [SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one,
    Superfunctor.zero_app, add_zero] at hh
  change z = 0 at hh
  exact hz hh
private theorem row_ne_zero {C : Type*} [Category* C] [Preadditive C]
    {A B : C} (g : A ⟶ B) (r : B ⟶ A) (hr : g ≫ r = 𝟙 A)
    (hid : (𝟙 A : A ⟶ A) ≠ 0) : r ≠ 0 := by
  intro h
  rw [h, Limits.comp_zero] at hr
  exact hid hr.symm
private theorem occupied_ne_zero : occupied ≠ 0 :=
  nonzero_of_linear_image (SVec.toLinearMap (e.hom.total star)) occupied _ vacuum_vector_nonzero image_occupied

/-- The polynomial exponent is the actual probe multiplicity: one
colour has height zero and the other has negative external height. -/
example : 2 * m false = cutoff false := rfl
example : 2 * m true < cutoff true := by decide
example : occupied ≠ 0 := occupied_ne_zero
example : deltaClass ≠ 0 := delta_ne_zero

/-- Whole actual module squares and every native vector are retained. -/
example (i : Bool) (n : ℕ) := tensorPowerVacuumCap_moment_square D Sc m cutoff L i
  (reservoir_positive i) n
example (i : Bool) (n : ℕ) (z : (H.obj N₀).obj star) :=
  tensorPowerVacuumCap_moment_weighted D Sc m cutoff L i (reservoir_positive i) n z
example (i : Bool) (n : ℕ) (z : (H.obj N₀).obj star) :=
  tensorPowerVacuumCap_moment_apply D Sc m cutoff L i (reservoir_positive i) n z
example (i : Bool) (r : ℕ) (z : (H.obj N₀).obj star) :=
  tensorPowerVacuumCap_moment_even D Sc m cutoff L i rfl (reservoir_positive i) r z
example (i : Bool) (r : ℕ) (z : (H.obj N₀).obj star) :=
  tensorPowerVacuumCap_moment_odd D Sc m cutoff L i rfl (reservoir_positive i) r z
example (a : AQ) := tensorVacuumDecode_input D Sc m cutoff L a
example (z : (H.obj N₀).obj star) := tensorVacuumInput_decode D Sc m cutoff L z

/-- All polynomial closures are literal module maps on arbitrary vectors. -/
example (i : Bool) (M n : ℕ) (z : (H.obj N₀).obj star) :=
  tensorPolynomialCap_moment_apply D Sc m cutoff L i (reservoir_positive i) M n z
example (i : Bool) (M : ℕ) (hMN : 2 * M ≤ cutoff i) (z : (H.obj N₀).obj star) :=
  tensorPolynomialCap_nonpositive_first_odd D Sc m cutoff L i rfl
    (reservoir_positive i) M hMN z
example (z : (H.obj N₀).obj star) := tensorPolynomialCap_zero_height_odd D Sc m cutoff L
  false rfl (reservoir_positive false) 2 rfl z

/-- The higher complete coefficient retains the prescribed plus-one
probe polynomial on every original coefficient vector. -/
example (a : AQ) : tensorVacuumDecodeLinear D Sc m cutoff L
    ((tensorPolynomialClosure D Sc m cutoff L false (reservoir_positive false) 2 1).total star
      (tensorVacuumInputLinear D Sc m cutoff L a)) =
    (coefficientPowerQuotientMap D cutoff L (SKM.SYM.e D ℚ false 0) + 2) * a := by
  rw [tensorPolynomialCap_moment_apply, tensorVacuumDecode_input,
    weightedPolynomialCapMoment_second_four D Sc cutoff L false rfl (reservoir_positive false) rfl]
  rfl

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

private def secondDelta : AQ :=
  coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D ℚ i₁)
private theorem product_ne_zero : deltaClass * secondDelta ≠ 0 := by
  intro hz
  have hm : SKM.SYM.delta D ℚ i₀ * SKM.SYM.delta D ℚ i₁ ∈
      SKM.SYM.CoefficientAtMost D ℚ 2 :=
    SKM.SYM.coefficientAtMost_mul D ℚ (m := 1) (n := 1)
      (x := SKM.SYM.delta D ℚ i₀) (y := SKM.SYM.delta D ℚ i₁)
      (SKM.SYM.delta_mem_coefficientAtMost D ℚ i₀) (SKM.SYM.delta_mem_coefficientAtMost D ℚ i₁)
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 2 4 (by decide) large powers_high
  have he := hi (a₁ := ⟨_, hm⟩) (a₂ := 0) (by
    change coefficientPowerQuotientMap D cutoff L _ = _
    rw [map_mul]
    exact hz.trans (map_zero _).symm)
  exact source_product_ne_zero (congrArg Subtype.val he)

/-- Independent odd directions detect left multiplication order in
the actual polynomial cap, and the resulting native output is nonzero. -/
private theorem decoded_product : tensorVacuumDecodeLinear D Sc m cutoff L
    ((tensorPolynomialClosure D Sc m cutoff L false (reservoir_positive false) 2 0).total star
      (tensorVacuumInputLinear D Sc m cutoff L secondDelta)) = -(deltaClass * secondDelta) := by
  rw [tensorPolynomialCap_zero_height_odd D Sc m cutoff L false rfl
    (reservoir_positive false) 2 rfl, tensorVacuumDecode_input]
  change -deltaClass * secondDelta = _
  exact neg_mul _ _
example :
    (tensorPolynomialClosure D Sc m cutoff L false (reservoir_positive false) 2 0).total star
      (tensorVacuumInputLinear D Sc m cutoff L secondDelta) ≠ 0 := by
  exact nonzero_of_linear_image (tensorVacuumDecodeLinear D Sc m cutoff L) _ _
    (neg_ne_zero.mpr product_ne_zero) decoded_product

/-- An inhomogeneous input is included without a parity premise. -/
example : tensorVacuumDecodeLinear D Sc m cutoff L
    ((tensorPolynomialClosure D Sc m cutoff L false (reservoir_positive false) 2 0).total star
      (tensorVacuumInputLinear D Sc m cutoff L (1 + secondDelta))) =
    -deltaClass - deltaClass * secondDelta := by
  rw [tensorPolynomialCap_zero_height_odd D Sc m cutoff L false rfl
    (reservoir_positive false) 2 rfl, tensorVacuumDecode_input]
  change -deltaClass * (1 + secondDelta) = _
  noncomm_ring

/-- The negative-height colour retains the opposite cutoff sign. -/
example (a : AQ) : tensorVacuumDecodeLinear D Sc m cutoff L
    ((tensorPolynomialClosure D Sc m cutoff L true (reservoir_positive true) 2 (cutoff true - 2 * 2)).total star
      (tensorVacuumInputLinear D Sc m cutoff L a)) = secondDelta * a := by
  rw [tensorPolynomialCap_nonpositive_first_odd D Sc m cutoff L true rfl
      (reservoir_positive true) 2 (by decide), tensorVacuumDecode_input]
  change (((-1 : ℚ) ^ 6) • secondDelta) * a = secondDelta * a
  rw [show (-1 : ℚ) ^ 6 = 1 by norm_num, one_smul]

private def mixedDatum : SKM.Datum Bool (Bool → ℤ) :=
  { D with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => D.even_of_odd i j rfl }
private def mixedScalars : SKM.Scalars mixedDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num

/-- The same all-vector formula includes an even moving colour inside
a mixed datum, with every original coefficient input. -/
example (n : ℕ) (a : CoefficientPowerQuotient (k := ℚ) mixedDatum cutoff L) :=
  tensorPowerVacuumCap_moment_apply mixedDatum mixedScalars m cutoff L false
    (reservoir_positive false) n (tensorVacuumInputLinear mixedDatum mixedScalars m cutoff L a)

end NonVacuity.ELVTensorVacuumMomentMaps
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumMomentMaps
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
