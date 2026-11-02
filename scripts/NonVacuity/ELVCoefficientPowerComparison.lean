import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerComparison
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
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

namespace NonVacuity.ELVCoefficientPowerComparison
open OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CoefficientAnnihilationFixture
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 4
private def rep := truncatedRepresentable D Sc cutoff 4
  (⟨[]⟩ : TruncatedCategory D Sc cutoff 4)
private def pulled := weightedRestriction D Sc cutoff 4 rep

-- A concrete auxiliary generator family tests the generic comparison
-- functors, including odd coefficients. It is not the paper's even-power T.
private abbrev WeightedIndex := {a : SKM.SYM.CoefficientIndex D //
  4 ≤ SKM.SYM.coefficientWeight D a}
private def coefficients (a : WeightedIndex) :
    SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff :=
  SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.coefficientBasis D ℚ a.val)
private def powers (_ : WeightedIndex) : ℕ := 1
private theorem fixtureIdeal : coefficientPowerIdeal D cutoff coefficients powers =
    coefficientWeightedIdeal D cutoff 4 := by
  apply congrArg TwoSidedIdeal.span
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.val, a.property, by simp only [coefficients, powers, pow_one]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, by simp only [coefficients, powers, pow_one]⟩

private def down := weightedToPower D Sc cutoff coefficients powers 4 fixtureIdeal.le
private def up := powerToWeighted D Sc cutoff coefficients powers 4 fixtureIdeal.ge

/-- Both comparison functors keep the actual module vector spaces,
including the vacuum coefficient component. -/
example : (down.obj rep).obj.obj (⟨[]⟩ : OldCategory D Sc cutoff) =
    rep.obj (⟨[]⟩ : TruncatedCategory D Sc cutoff 4) := rfl

example : (up.obj (down.obj rep)).obj (⟨[]⟩ : TruncatedCategory D Sc cutoff 4) =
    rep.obj (⟨[]⟩ : TruncatedCategory D Sc cutoff 4) := rfl

/-- The odd comparison of the actual parity-shifted weighted
representable survives both literal functors with its exact component. -/
example (p : ZMod 2) :
    ((down ⋙ up).map (supermoduleParityIso rep).hom).app p
      (⟨[]⟩ : TruncatedCategory D Sc cutoff 4) =
      (supermoduleParityIso rep).hom.app p ⟨[]⟩ := rfl

example :
    down.map (supermoduleParityIso rep).hom ∈ parity (R := ℚ)
      (down.obj (supermoduleParityObj rep)) (down.obj rep) 1 :=
  IsSuperfunctor.map_mem
    (F := weightedToPower D Sc cutoff coefficients powers 4 fixtureIdeal.le)
    (supermoduleParityIso_hom_mem rep)

/-- A chosen isomorphism is carried with its exact inverse component. -/
example (p : ZMod 2) :
    ((down ⋙ up).mapIso (supermoduleParityIso rep)).inv.app p
      (⟨[]⟩ : TruncatedCategory D Sc cutoff 4) =
      (supermoduleParityIso rep).inv.app p ⟨[]⟩ := rfl

end NonVacuity.ELVCoefficientPowerComparison

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerComparison | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"
