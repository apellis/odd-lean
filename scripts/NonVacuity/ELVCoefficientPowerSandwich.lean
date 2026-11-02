import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerSandwich
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

namespace NonVacuity.ELVCoefficientPowerSandwich
open OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CoefficientAnnihilationFixture
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 4
private def rep := truncatedRepresentable D Sc cutoff 4
  (⟨[]⟩ : TruncatedCategory D Sc cutoff 4)
private def pulled := weightedRestriction D Sc cutoff 4 rep

private def L (_ : Bool × ℕ) : ℕ := 4
private theorem powers_high (a : Bool × ℕ) :
    4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega

private theorem keys : SKM.SYM.elvPolynomialKeys D cutoff =
    {(false, 0), (false, 1), (true, 0), (true, 1)} := by
  ext ⟨i, r⟩
  rw [SKM.SYM.mem_elvPolynomialKeys]
  cases i <;> simp [SKM.SYM.elvElementaryRank, cutoff, D,
    CyclotomicAction.AsymmetricParameters.datum] <;> omega
private theorem weightBound : SKM.SYM.elvPowerWeightBound D cutoff L = 38 := by
  rw [SKM.SYM.elvPowerWeightBound, keys]
  norm_num [SKM.SYM.elementaryWeight, L, D, CyclotomicAction.AsymmetricParameters.datum]

/-- Both ideal containments now hold in the actual ELV coefficient
quotient with the literal paper's even elementary fourth powers. -/
example : coefficientPowerIdeal D cutoff (elementaryCoefficients (k := ℚ) D cutoff) L ≤
    coefficientWeightedIdeal D cutoff 4 :=
  elementaryPowerIdeal_le_weighted D cutoff L 4 powers_high

example : coefficientWeightedIdeal (k := ℚ) D cutoff 39 ≤
    coefficientPowerIdeal D cutoff (elementaryCoefficients (k := ℚ) D cutoff) L := by
  simpa only [weightBound] using weighted_le_elementaryPowerIdeal (k := ℚ) D cutoff L

private def lowToPower := elementaryWeightedToPower D Sc cutoff L 4 powers_high
private def toHigh := elementaryPowerToWeighted D Sc cutoff L

/-- The resulting paper-power object and its upper-weight descent retain
the literal actual vacuum component. -/
example : (lowToPower.obj rep).obj.obj (⟨[]⟩ : OldCategory D Sc cutoff) =
    rep.obj (⟨[]⟩ : TruncatedCategory D Sc cutoff 4) := rfl

example : (toHigh.obj (lowToPower.obj rep)).obj
      (⟨[]⟩ : TruncatedCategory D Sc cutoff (SKM.SYM.elvPowerWeightBound D cutoff L + 1)) =
    rep.obj (⟨[]⟩ : TruncatedCategory D Sc cutoff 4) := rfl

/-- The actual odd parity comparison and its inverse pass through the
two module functors with unchanged components. -/
example (p : ZMod 2) :
    ((lowToPower ⋙ toHigh).map (supermoduleParityIso rep).hom).app p
      (⟨[]⟩ : TruncatedCategory D Sc cutoff (SKM.SYM.elvPowerWeightBound D cutoff L + 1)) =
    (supermoduleParityIso rep).hom.app p ⟨[]⟩ := rfl

example (p : ZMod 2) :
    ((lowToPower ⋙ toHigh).mapIso (supermoduleParityIso rep)).inv.app p
      (⟨[]⟩ : TruncatedCategory D Sc cutoff (SKM.SYM.elvPowerWeightBound D cutoff L + 1)) =
    (supermoduleParityIso rep).inv.app p ⟨[]⟩ := rfl

end NonVacuity.ELVCoefficientPowerSandwich

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerSandwich | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"
