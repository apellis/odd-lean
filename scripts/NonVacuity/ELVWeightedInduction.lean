import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedModuleDescent
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundedSourceDetection
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Mathlib.Tactic.NormNum
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.WeightedModuleFixture
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

end OddMath.QuiverHecke.ELVOld.WeightedModuleFixture
namespace OddMath.QuiverHecke.ELVOld.WeightedInductionExamples
open WeightedModuleFixture
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def rep (N : ℕ) := truncatedRepresentable D Sc (fun _ => N) N
  (⟨[false,true]⟩ : TruncatedCategory D Sc (fun _ => N) N)
private def pulled (N : ℕ) := weightedRestriction D Sc (fun _ => N) N (rep N)

example (N : ℕ) : KillsWeightedCoefficients D Sc (fun _ => N) N
    (BalancedInduction.induced (CyclotomicCrossingTensor.append D Sc (fun _ => N) false)
      (pulled N)) :=
  induced_killsWeightedCoefficients D Sc (fun _ => N) N false (pulled N)
    (weightedRestriction_kills D Sc (fun _ => N) N (rep N))

private def mixedD : SKM.Datum Bool (Bool → ℤ) :=
  { D with
    parity := fun i => if i then 0 else 1
    even_of_odd := fun i j _ => D.even_of_odd i j rfl }

private def mixedSc : SKM.Scalars mixedD ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num

private def mixedRep (N : ℕ) := truncatedRepresentable mixedD mixedSc (fun _ => N) N
  (⟨[false,true]⟩ : TruncatedCategory mixedD mixedSc (fun _ => N) N)
private def mixedPulled (N : ℕ) := weightedRestriction mixedD mixedSc (fun _ => N) N
  (mixedRep N)

private def oddIndex (N : ℕ) : SKM.SYM.CoefficientIndex mixedD :=
  (Finsupp.single (true,0) N, {⟨false,rfl⟩})

/-- An even moving colour still kills the prescribed high-weight odd
coefficient monomials from another colour. -/
example (N : ℕ) :
    (BalancedInduction.induced
      (CyclotomicCrossingTensor.append mixedD mixedSc (fun _ => N) true)
      (mixedPulled N)).map
      (oldCoefficientBasis mixedD mixedSc (fun _ => N) [true,false] (oddIndex N)) = 0 := by
  apply induced_killsWeightedCoefficients mixedD mixedSc (fun _ => N) N true
    (mixedPulled N)
    (weightedRestriction_kills mixedD mixedSc (fun _ => N) N (mixedRep N))
  simp [oddIndex, SKM.SYM.coefficientWeight, SKM.SYM.elementaryWeight, mixedD]


/-- The actual induced vector space carries the descended quotient action. -/
example (N : ℕ) :
    (weightedInducedModule mixedD mixedSc (fun _ => N) N true (mixedPulled N)
      (weightedRestriction_kills mixedD mixedSc (fun _ => N) N (mixedRep N))).obj
      (⟨[true,false]⟩ : TruncatedCategory mixedD mixedSc (fun _ => N) N) =
    (BalancedInduction.induced
      (CyclotomicCrossingTensor.append mixedD mixedSc (fun _ => N) true)
      (mixedPulled N)).obj ⟨[true,false]⟩ := rfl

end OddMath.QuiverHecke.ELVOld.WeightedInductionExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedInduction
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
