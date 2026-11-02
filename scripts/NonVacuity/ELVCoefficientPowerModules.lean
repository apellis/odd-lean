import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerModules
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendDot
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld.CoefficientAnnihilationFixture
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
def truncatedRepresentableFunctor (v : TruncatedCategory D Sc cutoff N) :
    TruncatedCategory D Sc cutoff N ⥤ SVec k where
  obj := Supercategory.homSVec k (TruncatedCategory D Sc cutoff N) v
  map f :=
    { toFun := fun h => h ≫ f
      map_add' := fun h h' => Preadditive.add_comp _ _ _ _ _ _
      map_smul' := fun r h => Linear.smul_comp _ _ _ _ _ _ }
  map_id w := by ext h; exact Category.comp_id h
  map_comp f g := by ext h; exact (Category.assoc h f g).symm

instance truncatedRepresentableFunctor_additive (v : TruncatedCategory D Sc cutoff N) :
    (truncatedRepresentableFunctor D Sc cutoff N v).Additive where
  map_add {w z} f g := by
    apply LinearMap.ext
    intro h
    exact Preadditive.comp_add v w z h f g

instance truncatedRepresentableFunctor_linear (v : TruncatedCategory D Sc cutoff N) :
    (truncatedRepresentableFunctor D Sc cutoff N v).Linear k where
  map_smul {w z} f r := by
    apply LinearMap.ext
    intro h
    exact Linear.comp_smul v w z h r f

instance truncatedRepresentableFunctor_super (v : TruncatedCategory D Sc cutoff N) :
    IsSuperfunctor k (truncatedRepresentableFunctor D Sc cutoff N v) where
  map_mem := by
    intro w z p f hf
    apply SVec.mem_parityHom_of_apply_mem
    intro q h hh
    change h ∈ (Supercategory.homSVec k (TruncatedCategory D Sc cutoff N) v w).part q at hh
    change h ≫ f ∈ (Supercategory.homSVec k (TruncatedCategory D Sc cutoff N) v z).part (q + p)
    exact (Supercategory.mem_homSVec_part_iff k).2
      (comp_mem ((Supercategory.mem_homSVec_part_iff k).1 hh) hf)

def truncatedRepresentable (v : TruncatedCategory D Sc cutoff N) :
    Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k) :=
  ⟨truncatedRepresentableFunctor D Sc cutoff N v⟩

@[simp] theorem truncatedRepresentable_map (v w z : TruncatedCategory D Sc cutoff N)
    (f : w ⟶ z) (h : v ⟶ w) :
    (truncatedRepresentable D Sc cutoff N v).map f h = h ≫ f := rfl

end OddMath.QuiverHecke.ELVOld.CoefficientAnnihilationFixture

namespace NonVacuity.ELVCoefficientPowerModules
open OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CoefficientAnnihilationFixture
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 4
private def rep := truncatedRepresentable D Sc cutoff 4
  (⟨[]⟩ : TruncatedCategory D Sc cutoff 4)
private def pulled := weightedRestriction D Sc cutoff 4 rep
private def evenCoefficient : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff :=
  SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.e D ℚ false 0)
private def powerIndex : SKM.SYM.CoefficientIndex D :=
  (Finsupp.single (false, 0) 2, ∅)

private theorem evenCoefficient_mem :
    evenCoefficient ∈ SKM.SYM.elvCoefficientParity D cutoff 0 := by
  have h := SKM.SYM.elvModelQuotient_mem D (cutoff := cutoff)
    (SKM.SYM.polynomialExterior_e_mem_even D (k := ℚ) false 0)
  simpa only [SKM.SYM.elvModelQuotient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply, evenCoefficient] using h

private theorem basis_power : SKM.SYM.coefficientBasis D ℚ powerIndex =
    (SKM.SYM.e D ℚ false 0) ^ 2 := by
  apply (SKM.SYM.polynomialExteriorEquiv D ℚ).injective
  rw [SKM.SYM.coefficientBasis_projection]
  simp only [powerIndex]
  rw [SKM.SYM.oddExteriorBasis_empty, map_pow]
  have he : SKM.SYM.polynomialExteriorEquiv D ℚ (SKM.SYM.e D ℚ false 0) =
      MvPolynomial.X (R := ℚ) (false, 0) ⊗ₜ[ℚ]
        (1 : ExteriorAlgebra ℚ (SKM.SYM.OddModule D ℚ)) :=
    SKM.SYM.polynomialExteriorProjection_e D ℚ false 0
  rw [he, Algebra.TensorProduct.tmul_pow, MvPolynomial.X_pow_eq_monomial, one_pow]

private theorem pulled_kills_power : KillsCoefficient D Sc cutoff pulled (evenCoefficient ^ 2) := by
  intro v
  have h := weightedRestriction_kills D Sc cutoff 4 rep v powerIndex
    (by norm_num [powerIndex, SKM.SYM.coefficientWeight, SKM.SYM.elementaryWeight, D,
      CyclotomicAction.AsymmetricParameters.datum])
  have he : evenCoefficient ^ 2 = SKM.SYM.elvCoefficientQuotient D cutoff
      (SKM.SYM.coefficientBasis D ℚ powerIndex) := by
    rw [basis_power, map_pow]
    rfl
  rw [he]
  exact h

private def coefficients (_ : Unit) := evenCoefficient
private def powers (_ : Unit) : ℕ := 2
private theorem coefficients_even (j : Unit) :
    coefficients j ∈ SKM.SYM.elvCoefficientParity D cutoff 0 := evenCoefficient_mem
private def powerVacuum : CoefficientPowerModules D Sc cutoff coefficients powers :=
  ⟨pulled, (coefficientPowerProperty_iff D Sc cutoff coefficients powers pulled).mpr
    (fun _ => pulled_kills_power)⟩

/-- The object condition annihilates every element of the literal
two-sided power ideal, not merely a selected collection of vectors. -/
example (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff)
    (ha : a ∈ coefficientPowerIdeal D cutoff coefficients powers) :
    KillsCoefficient D Sc cutoff powerVacuum.obj a :=
  (mem_coefficientAnnihilator D Sc cutoff powerVacuum.obj a).mp (powerVacuum.property ha)

/-- Restriction to the power-annihilated category leaves the actual old
balanced induction object unchanged. -/
example (i : Bool) :
    ((CoefficientPowerModules.induction D Sc cutoff coefficients powers coefficients_even i).obj
      powerVacuum).obj =
      (BalancedInduction.induction (ELVOld.CyclotomicCrossingTensor.append D Sc cutoff i)).obj
        powerVacuum.obj := rfl

example (i : Bool) :
    ((CoefficientPowerModules.restriction D Sc cutoff coefficients powers i).obj powerVacuum).obj =
      (BalancedInduction.restriction (ELVOld.CyclotomicCrossingTensor.append D Sc cutoff i)).obj
        powerVacuum.obj := rfl

/-- The chosen ordinary unit/counit components are retained literally. -/
example (i : Bool) :
    ((CoefficientPowerModules.adjunction D Sc cutoff coefficients powers coefficients_even i).unit.app
      powerVacuum).hom =
    (BalancedInduction.adjunction (ELVOld.CyclotomicCrossingTensor.append D Sc cutoff i)).unit.app
      powerVacuum.obj := rfl

example (i : Bool) :
    ((CoefficientPowerModules.adjunction D Sc cutoff coefficients powers coefficients_even i).counit.app
      powerVacuum).hom =
    (BalancedInduction.adjunction (ELVOld.CyclotomicCrossingTensor.append D Sc cutoff i)).counit.app
      powerVacuum.obj := rfl

/-- Both actual odd induction dots restrict with their original
supernatural parity on this power-annihilated module category. -/
example (i : Bool) :
    (CoefficientPowerModules.inductionDot D Sc cutoff coefficients powers coefficients_even i).IsHomogeneous 1 :=
  CoefficientPowerModules.inductionDot_homogeneous D Sc cutoff coefficients powers coefficients_even i

private def scalarIso : powerVacuum.obj ≅ powerVacuum.obj where
  hom := (2 : ℚ) • 𝟙 _
  inv := (1 / 2 : ℚ) • 𝟙 _
  hom_inv_id := by
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
    norm_num
  inv_hom_id := by
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
    norm_num

/-- A chosen nonidentity scalar inverse restricts with the same two maps,
without reconstructing an inverse in the power category. -/
example :
    (CoefficientPowerModules.restrictIso D Sc cutoff coefficients powers
      powerVacuum powerVacuum scalarIso).hom.hom = scalarIso.hom := rfl

example :
    (CoefficientPowerModules.restrictIso D Sc cutoff coefficients powers
      powerVacuum powerVacuum scalarIso).inv.hom = scalarIso.inv := rfl

end NonVacuity.ELVCoefficientPowerModules

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerModules | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"

