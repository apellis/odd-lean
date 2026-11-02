import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientAnnihilation
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

namespace NonVacuity.ELVCoefficientAnnihilation
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

/-- The actual even coefficient square is killed in a pulled-back
weighted representable; actual old E preserves its own annihilator. -/
example (i : Bool) : KillsCoefficient D Sc cutoff
    (BalancedInduction.induced (ELVOld.CyclotomicCrossingTensor.append D Sc cutoff i) pulled)
    (evenCoefficient ^ 2) :=
  induced_killsEvenPower D Sc cutoff i pulled evenCoefficient_mem 2 pulled_kills_power

/-- Old F preserves the same coefficient square; no equality of the
power quotient with the weighted quotient is asserted. -/
example (i : Bool) : KillsCoefficient D Sc cutoff
    ((BalancedInduction.restriction (ELVOld.CyclotomicCrossingTensor.append D Sc cutoff i)).obj
      pulled) (evenCoefficient ^ 2) :=
  restriction_killsCoefficient D Sc cutoff i pulled _ pulled_kills_power

/-- Even coefficients also commute with a sum of the identity and the
chosen odd induction-dot transformation, so the map need not be even. -/
example (i : Bool) :
    let J := ELVOld.CyclotomicCrossingTensor.append D Sc cutoff i
    let M := BalancedInduction.induced J pulled
    let f : M ⟶ M := 𝟙 M + BalancedInduction.transformComponent
      (ELVOld.CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) pulled
    M.map (X := ⟨[false, true]⟩) (Y := ⟨[false, true]⟩)
        (coefficientEndomorphism D Sc cutoff [false, true] evenCoefficient) ≫
      f.total ⟨[false, true]⟩ =
    f.total ⟨[false, true]⟩ ≫ M.map (X := ⟨[false, true]⟩) (Y := ⟨[false, true]⟩)
      (coefficientEndomorphism D Sc cutoff [false, true] evenCoefficient) := by
  dsimp only
  exact moduleMap_evenCoefficient D Sc cutoff _ _ _ _ evenCoefficient_mem

end NonVacuity.ELVCoefficientAnnihilation

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientAnnihilation | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"
