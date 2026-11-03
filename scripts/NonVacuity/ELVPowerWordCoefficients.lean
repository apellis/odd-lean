import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordCoefficients
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor PowerVacuumCoefficient
namespace NonVacuity.ELVPowerWordCoefficients
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
private abbrev M := coefficientPowerVacuum D Sc cutoff L
private abbrev E := coefficientPowerVacuumEmptyEquiv D Sc cutoff L
private abbrev empty : OldCategory D Sc cutoff := ⟨[]⟩
private def phi (i : Bool) : End M := vacuumCoefficientAction D Sc cutoff L (deltaClass i)
private theorem phi_eq (i : Bool) : phi i = coefficientModuleAction D Sc cutoff M (deltaCoefficient i) := rfl

example (i : Bool) : phi i ∈ parity (R := ℚ) M M 1 := by
  rw [phi_eq]
  exact coefficientModuleAction_mem D Sc cutoff M (delta_odd i)

example (a b : AQ) : vacuumCoefficientAction D Sc cutoff L (a * b) =
    vacuumCoefficientAction D Sc cutoff L a * vacuumCoefficientAction D Sc cutoff L b :=
  map_mul _ a b

example (a z : AQ) : (vacuumCoefficientAction D Sc cutoff L a).total empty (E z) = E (a * z) :=
  vacuumCoefficientAction_empty D Sc cutoff L a z

example : (phi false).total empty (E (deltaClass true)) ≠ 0 := by
  rw [phi, vacuumCoefficientAction_empty]
  exact fun hz => product_ne_zero (E.injective (hz.trans E.map_zero.symm))

example : (vacuumCoefficientAction D Sc cutoff L (1 + deltaClass false)).total empty
    (E (1 + deltaClass true)) = E (1 + deltaClass true + deltaClass false +
      deltaClass false * deltaClass true) := by
  rw [vacuumCoefficientAction_empty]
  congr 1
  noncomm_ring

private theorem deltaClass_anticommute (i j : Bool) :
    deltaClass i * deltaClass j = -(deltaClass j * deltaClass i) := by
  have hh := congrArg (coefficientPowerQuotientMap (k := ℚ) D cutoff L)
    (SKM.SYM.delta_anticommute D ℚ (⟨i, rfl⟩ : OddColour) (⟨j, rfl⟩ : OddColour))
  simpa only [map_mul, map_neg] using hh

private abbrev Λ : Bool → ℤ := 0
private abbrev ν : List Bool := [false, true]
private abbrev σ := ν.reverse
private abbrev N := PowerWordContent.powerBound D cutoff L
private abbrev V := PowerWordEvaluation.value D Sc cutoff L Λ ν
private abbrev β := PowerWordWeight.wordBlock D Λ ν
private def w : ContentCategory D Sc cutoff N (ν : Multiset Bool) := ⟨⟨ν⟩, rfl⟩
private theorem powers_high_16 (a : Bool × ℕ) : 16 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 16 ≤ 10 * (2 * (a.2 + 1))
  omega
private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D originalSc σ σ 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 16 ≤ 20)) powers_high_16 (by decide)
private def identityNF : NFIdx σ σ := by
  have hc : Categorification.TypeA.canWord σ.length (1 : Equiv.Perm (Fin σ.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]
private def oddIndex : SKM.SYM.CoefficientIndex D := (0, {⟨false, rfl⟩, ⟨true, rfl⟩})
private def occupied : ExtendedAtMost D originalSc σ σ 2 :=
  ⟨extensionBasis D originalSc σ σ (oddIndex, identityNF),
    Submodule.subset_span ⟨(oddIndex, identityNF), by decide, rfl⟩⟩
private def contentVector : (PowerWordWeight.wordAt D Sc cutoff L ν (ν : Multiset Bool)).obj w :=
  powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val
private theorem contentVector_ne_zero : contentVector ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D originalSc σ σ 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc σ σ).ne_zero (oddIndex, identityNF) (congrArg Subtype.val hh)
private abbrev chosenEquiv := moduleIsoLinearEquiv
  (Pi.isoApp (PowerWordEvaluation.chart D Sc cutoff L Λ ν) β) w
private def chosenVector := chosenEquiv.symm contentVector
/-- The actual iterated E-word value carries independent surviving odd coefficients. -/
example : chosenVector ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have hh := congrArg chosenEquiv hz
  simpa only [chosenVector, LinearEquiv.apply_symm_apply, map_zero] using hh

/-- All coefficient and affine tails are kept inside the same total parity twist. -/
example (a b : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff) (p : ZMod 2)
    (z : OldCategory D Sc cutoff) (h : (OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ z) :=
  PowerWordCoefficients.coefficient_tensor D Sc cutoff L ν a b p z h
example (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff) :=
  PowerWordCoefficients.coefficient_fromArrow D Sc cutoff L ν a

/-- The native regular AQ insertion on an occupied literal two-E value. -/
example (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff) :=
  congrArg (fun f : V ⟶ PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) ν =>
    (f β).total w chosenVector) (PowerWordCoefficients.coefficient_value D Sc cutoff L Λ a ν)
/-- Inhomogeneous input coefficients use the same map comparison. -/
example := congrArg (fun f : V ⟶
    PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) ν =>
      (f β).total w chosenVector)
  (PowerWordCoefficients.coefficient_value D Sc cutoff L Λ (1 + deltaCoefficient false) ν)

/-- The chronological product order is explicit for both distinct odd colours. -/
example : PowerWordCoefficients.coefficientValue D Sc cutoff L Λ (deltaClass false * deltaClass true) ν =
    PowerWordCoefficients.coefficientValue D Sc cutoff L Λ (deltaClass true) ν ≫
      PowerWordCoefficients.coefficientValue D Sc cutoff L Λ (deltaClass false) ν :=
  PowerWordCoefficients.coefficientValue_mul D Sc cutoff L Λ _ _ ν
/-- Reversing the two genuine native insertions has the required minus sign. -/
example :
    PowerWordCoefficients.coefficientValue D Sc cutoff L Λ (deltaClass false) ν ≫
      PowerWordCoefficients.coefficientValue D Sc cutoff L Λ (deltaClass true) ν =
    -(PowerWordCoefficients.coefficientValue D Sc cutoff L Λ (deltaClass true) ν ≫
      PowerWordCoefficients.coefficientValue D Sc cutoff L Λ (deltaClass false) ν) := by
  rw [← PowerWordCoefficients.coefficientValue_mul D Sc cutoff L Λ (deltaClass true) (deltaClass false) ν,
    ← PowerWordCoefficients.coefficientValue_mul D Sc cutoff L Λ (deltaClass false) (deltaClass true) ν,
    deltaClass_anticommute true false, PowerWordCoefficients.coefficientValue_neg]

namespace Context
private abbrev η : List Bool := [false, true]
private abbrev x := PowerWordWeight.wordWeight D Λ []
private abbrev finalWeight := PowerWordWeightContexts.contextWeight D x η
private def β : WeightBlocks D Λ finalWeight :=
  ⟨ν, (PowerWordWeightContexts.context_weight_word D Λ [] η x rfl).symm⟩
private def w : ContentCategory D Sc cutoff N (ν : Multiset Bool) := ⟨⟨ν⟩, rfl⟩
private def modelVector : (PowerWordWeight.wordAt D Sc cutoff L ν (ν : Multiset Bool)).obj w :=
  powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val
private def selectedChart := PowerWordWeightContexts.contextChart D Sc cutoff L Λ [] η x rfl
  (PowerWordEvaluation.chart D Sc cutoff L Λ [])
private abbrev selectedEquiv := moduleIsoLinearEquiv (Pi.isoApp selectedChart β) w
private def nativeVector := selectedEquiv.symm modelVector
example : nativeVector ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have hh := congrArg selectedEquiv hz
  simpa only [nativeVector, LinearEquiv.apply_symm_apply, map_zero, modelVector, contentVector] using hh
private abbrev source := (PowerWordWeightContexts.contextFunctor D Sc cutoff L Λ x η).obj
  (PowerWordEvaluation.value D Sc cutoff L Λ [])
/-- Coefficient insertion at the vacuum, inside a chosen two-E right context. -/
example (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff) :=
  congrArg (fun f : source ⟶ PowerWordWeight.wordFamily D Sc cutoff L Λ finalWeight ν =>
    (f β).total w nativeVector) (PowerWordCoefficients.coefficient_in_context D Sc cutoff L Λ a [] η)
end Context

end NonVacuity.ELVPowerWordCoefficients

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordCoefficients
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
