import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumTensorCoefficientMaps
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor PowerVacuumCoefficient
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
open VacuumTensorCoefficientMaps
namespace NonVacuity.ELVVacuumTensorCoefficientMaps
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev originalSc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 10
private theorem positive (i : Bool) : 0 < cutoff i := by cases i <;> decide
private theorem large (i : Bool) : 4 ≤ cutoff i := by cases i <;> decide
private theorem powers_high (a : Bool × ℕ) :
    4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 10 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega
private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private def deltaClass (i : Bool) : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨i, rfl⟩)
private def elementaryClass (i : Bool) : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.e D ℚ i 0)

private theorem window_ne_zero {d : ℕ} (hd : d < 4) (a : SKM.SYM D ℚ)
    (ha : a ∈ SKM.SYM.CoefficientAtMost D ℚ d) (h0 : a ≠ 0) :
    coefficientPowerQuotientMap D cutoff L a ≠ 0 := by
  intro hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L d 4 hd large powers_high
  have he := hi (a₁ := ⟨a, ha⟩) (a₂ := 0)
    (by simpa only [ZeroMemClass.coe_zero, map_zero] using hz)
  exact h0 (congrArg Subtype.val he)

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

private theorem product_ne_zero : deltaClass false * deltaClass true ≠ 0 := by
  change coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D ℚ i₀) *
    coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D ℚ i₁) ≠ 0
  rw [← map_mul]
  have hm : SKM.SYM.delta D ℚ i₀ * SKM.SYM.delta D ℚ i₁ ∈
      SKM.SYM.CoefficientAtMost D ℚ 2 :=
    SKM.SYM.coefficientAtMost_mul D ℚ (m := 1) (n := 1)
      (x := SKM.SYM.delta D ℚ i₀) (y := SKM.SYM.delta D ℚ i₁)
      (SKM.SYM.delta_mem_coefficientAtMost D ℚ i₀) (SKM.SYM.delta_mem_coefficientAtMost D ℚ i₁)
  exact window_ne_zero (by decide : 2 < 4) _ hm source_product_ne_zero

private def deltaCoefficient (i : Bool) : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff :=
  SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D ℚ ⟨i, rfl⟩)
private theorem delta_odd (i : Bool) : deltaCoefficient i ∈ SKM.SYM.elvCoefficientParity D cutoff 1 :=
by
  have h := SKM.SYM.elvModelQuotient_mem D (cutoff := cutoff)
    (SKM.SYM.coefficientBasis_mem_parity D ℚ (0, {⟨i, rfl⟩}))
  change SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D ℚ ⟨i, rfl⟩) ∈
    SKM.SYM.elvCoefficientParity D cutoff 1
  simpa only [SKM.SYM.elvModelQuotient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply, Finset.card_singleton, Nat.cast_one,
    ← SKM.SYM.delta_eq_coefficientBasis] using h

private def m (i : Bool) : ℕ := if i then 2 else 1
private abbrev Λ : Bool → ℤ := 0
private abbrev N := PowerWordContent.powerBound D cutoff L
private abbrev W := ReservoirWordValue.initialValue D Λ Sc cutoff L
private abbrev Z := WeightTensorVacuum.selectedHom D Sc m cutoff Λ Λ L
private abbrev P₀ := WeightTensorVacuum.regularProbe D Sc m Λ
private abbrev e := WeightTensorVacuum.selectedIso D Sc m cutoff Λ Λ L
private def β : WeightBlocks D Λ (ReservoirWord.weight D Λ 0) :=
  ⟨0, by simp [ReservoirWord.weight]⟩
private def star : ContentCategory D Sc cutoff N (0 : Multiset Bool) := ⟨⟨[]⟩, rfl⟩
private abbrev empty : OldCategory D Sc cutoff := ⟨[]⟩
private abbrev E := coefficientPowerVacuumEmptyEquiv D Sc cutoff L
private def oddTensor : ((Z.obj P₀) β).obj star :=
  WeightTensorVacuum.tensorVector D Sc m cutoff N Λ Λ W β star (E (deltaClass true))
private def actedTensor : ((Z.obj P₀) β).obj star :=
  (((sourceCoefficientAction D Sc m cutoff L Λ Λ (SKM.SYM.delta D ℚ i₀)).total P₀) β).total star oddTensor

private theorem actedTensor_chart : (e.hom β).total star actedTensor = E (deltaClass false * deltaClass true) := by
  rw [actedTensor, oddTensor, sourceCoefficientAction_tensorVector]
  change (vacuumCoefficientAction D Sc cutoff L (deltaClass false)).total empty
    (E (deltaClass true)) = E (deltaClass false * deltaClass true)
  exact vacuumCoefficientAction_empty D Sc cutoff L _ _

/-- One odd coefficient acts on a vector containing the other odd colour
inside the literal full-input tensor functor, and the product survives. -/
example : actedTensor ≠ 0 := by
  intro hz
  have h := actedTensor_chart
  rw [hz, map_zero] at h
  exact product_ne_zero (E.injective (h.symm.trans E.map_zero.symm))

example : (e.hom β).total star actedTensor = E (deltaClass false * deltaClass true) := actedTensor_chart

/-- The homogeneous action remains odd on the entire functor. -/
example (i : Bool) : coefficientAction D Sc m cutoff L Λ Λ (deltaCoefficient i) ∈
    parity (R := ℚ) Z Z 1 :=
  coefficientAction_mem D Sc m cutoff L Λ Λ (delta_odd i)

example (a b : SKM.SYM D ℚ) :
    sourceCoefficientAction D Sc m cutoff L Λ Λ (a * b) =
      sourceCoefficientAction D Sc m cutoff L Λ Λ a * sourceCoefficientAction D Sc m cutoff L Λ Λ b :=
  map_mul _ a b

/-- Reversing independent odd source coefficients changes the whole-input map by a sign. -/
example : sourceCoefficientAction D Sc m cutoff L Λ Λ
    (SKM.SYM.delta D ℚ i₀ * SKM.SYM.delta D ℚ i₁) =
    -sourceCoefficientAction D Sc m cutoff L Λ Λ
      (SKM.SYM.delta D ℚ i₁ * SKM.SYM.delta D ℚ i₀) := by
  rw [SKM.SYM.delta_anticommute, map_neg]

example {l : List (SKM.Col Bool (Bool → ℤ))} {c : Bool →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true)
    (G : probeOldWeightSpace D Sc m Λ (-Λ) ⟶
      elvWeightSpace D Sc cutoff N Λ (ReservoirWord.weight D Λ c))
    (a : SKM.SYM D ℚ) (f : G ⟶ TensorReservoirWords.pathHom D Sc m cutoff L Λ Λ p hl) :
    pathHomCoefficientAction D Sc m cutoff L Λ Λ p hl G a f =
      f ≫ pathCoefficientAction D Sc m cutoff L Λ Λ p hl a :=
  pathHomCoefficientAction_apply D Sc m cutoff L Λ Λ p hl G a f

/-- Inhomogeneous coefficients and arbitrary reservoir vectors keep the same chart square. -/
example (a : SKM.SYM D ℚ) (v : (W β).obj star) :=
  sourceCoefficientAction_tensorVector D Sc m cutoff L Λ Λ a β star v

end NonVacuity.ELVVacuumTensorCoefficientMaps
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVVacuumTensorCoefficientMaps
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
