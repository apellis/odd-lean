import OddMath.QuiverHecke.CyclotomicAction.ELVAppendQuotientComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations
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


noncomputable section
open CategoryTheory StringDiagrams
open OddMath OddMath.QuiverHecke
namespace OddMath.QuiverHecke.AppendQuotientComparisonExamples
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev U := SKM.SYM.CoefficientAtMost D ℚ 3
private abbrev H :=
  (pres D Sc).obj (ob D [false, true, false]) ⟶ (pres D Sc).obj (ob D [true, false, false])

private theorem crossingTarget :
    tgt [false, true, false] (cw (Categorification.TypeA.canWord 3 (Equiv.swap 0 1))) = [true, false, false] := by
  apply List.ext_getElem (by simp)
  intro n hn hm
  have hn3 : n < 3 := by simpa using hn
  let q : Fin 3 := ⟨n, hn3⟩
  have he := tgt_cw_getElem
    (Categorification.TypeA.validWord_canWord 3 (Equiv.swap 0 1))
    (t := [false, true, false]) rfl q
  rw [Categorification.TypeA.wordProd_canWord] at he
  rw [he]
  interval_cases n <;> norm_num [q, Equiv.swap_apply_def, Fin.ext_iff]

private def crossingIndex : NFIdx [false, true, false] [true, false, false] := by
  refine ⟨([], Equiv.swap 0 1), by simp, by simp, ?_⟩
  change SChain [false, true, false]
    (pl [false, true, false] (cw (Categorification.TypeA.canWord 3 (Equiv.swap 0 1)))) [true, false, false]
  have ht := crossingTarget
  simpa only [ht] using
    sChain_pl [false, true, false] (cw (Categorification.TypeA.canWord 3 (Equiv.swap 0 1)))


private def exteriorIndex : SKM.SYM.CoefficientIndex D :=
  (0, {⟨false, rfl⟩})

private def oddCoefficient : U :=
  ⟨SKM.SYM.coefficientBasis D ℚ exteriorIndex,
    Submodule.subset_span ⟨exteriorIndex, by
      simp [exteriorIndex, SKM.SYM.coefficientWeight], rfl⟩⟩

private def crossing : H := basisNF D Sc [false, true, false] [true, false, false] crossingIndex

private def testTensor : coefficientWindowTensor D Sc 3 [false, true, false] [true, false, false] :=
  oddCoefficient ⊗ₜ[ℚ] crossing

private theorem testTensor_ne_zero : testTensor ≠ 0 := by
  let φ : U →ₗ[ℚ] ℚ :=
    ((SKM.SYM.coefficientBasis D ℚ).coord exteriorIndex).comp
      (SKM.SYM.CoefficientAtMost D ℚ 3).subtype
  have hφ : φ oddCoefficient = 1 := by
    change ((SKM.SYM.coefficientBasis D ℚ).repr
      (SKM.SYM.coefficientBasis D ℚ exteriorIndex)) exteriorIndex = 1
    simp
  intro hz
  have he : (TensorProduct.lid ℚ H)
      (TensorProduct.map φ (LinearMap.id : H →ₗ[ℚ] H) testTensor) = 0 := by
    rw [hz, map_zero, map_zero]
  change (TensorProduct.lid ℚ H) (φ oddCoefficient ⊗ₜ[ℚ] crossing) = 0 at he
  rw [hφ] at he
  have hf : crossing = 0 := by simpa using he
  exact (basisNF D Sc [false, true, false] [true, false, false]).ne_zero crossingIndex hf

open ELVOld
private def B : ℤ :=
  SKM.SYM.coefficientDegree D CyclotomicAction.AsymmetricParameters.symmetrizer exteriorIndex +
    crossingIndex.deg D CyclotomicAction.AsymmetricParameters.symmetrizer + 1

private def point :
    jointPBWWindow D CyclotomicAction.AsymmetricParameters.symmetrizer Sc
      3 [false,true,false] [true,false,false] B :=
  ⟨sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D ℚ exteriorIndex)
      crossingIndex.nf,
    Submodule.subset_span ⟨(exteriorIndex, crossingIndex), ⟨by
      simp [exteriorIndex, SKM.SYM.coefficientWeight], by
      dsimp only [Prod.fst, Prod.snd, B]
      omega⟩, rfl⟩⟩

private theorem point_ne_zero : point ≠ 0 := by
  intro hz
  have hp : sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D ℚ exteriorIndex)
      crossingIndex.nf = 0 := congrArg Subtype.val hz
  have hq : coefficientWindowMap D Sc (fun _ => 8) 3 [false,true,false] [true,false,false]
      testTensor = 0 := by
    rw [← elvHomQuotient_coefficientWindowSourceMap]
    simp only [testTensor, coefficientWindowSourceMap_tmul, oddCoefficient,
      crossing, basisNF_apply]
    rw [hp, map_zero]
  exact testTensor_ne_zero
    (coefficientWindowMap_injective D Sc (fun _ => 8) 3 (fun _ => by decide) _ _
      (hq.trans (map_zero _).symm))


private def recoveryPoint : ExtendedAtMost D Sc [false,true,false] [true,false,false] 3 :=
  ⟨point.val, by
    change sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D ℚ exteriorIndex)
      crossingIndex.nf ∈ _
    rw [← extensionBasis_apply]
    apply Submodule.subset_span
    refine ⟨(exteriorIndex,crossingIndex), ?_, rfl⟩
    norm_num [extensionDegree, exteriorIndex, SKM.SYM.coefficientWeight,
      crossingIndex]⟩

private theorem recoveryPoint_ne_zero : recoveryPoint ≠ 0 := by
  intro h
  apply point_ne_zero
  apply Subtype.ext
  exact congrArg (fun z : ExtendedAtMost D Sc [false,true,false] [true,false,false] 3 => z.val) h


open WeightedModuleFixture
private def rep (N : ℕ) := truncatedRepresentable D Sc (fun _ => N) N
  (⟨[false,true,false]⟩ : TruncatedCategory D Sc (fun _ => N) N)

private def pulled (N : ℕ) := weightedRestriction D Sc (fun _ => N) N (rep N)
private theorem killed (N : ℕ) :
    KillsWeightedCoefficients D Sc (fun _ => N) N (pulled N) :=
  weightedRestriction_kills D Sc (fun _ => N) N (rep N)

private def negation (N : ℕ) : pulled N ≅ pulled N where
  hom := -𝟙 _
  inv := -𝟙 _
  hom_inv_id := by simp
  inv_hom_id := by simp

private def descendedNegation (N : ℕ) :=
  weightedModuleIso D Sc (fun _ => N) N (pulled N) (pulled N)
    (killed N) (killed N) (negation N)

private def vector (N : ℕ) :
    (rep N).obj (⟨[true,false,false]⟩ : TruncatedCategory D Sc (fun _ => N) N) :=
  (truncatedIdeal D Sc (fun _ => N) N [false,true,false] [true,false,false]).mkQ
    (elvHomQuotient D Sc (fun _ => N) [false,true,false] [true,false,false] recoveryPoint.val)


private def input (N : ℕ) :=
  (BalancedInduction.restriction (truncatedAppend D Sc (fun _ => N) N [false])).obj (rep N)
private def comparison (N : ℕ) :=
  appendWeightedModuleIso D Sc (fun _ => N) N false (input N)
private def target (N : ℕ) : TruncatedCategory D Sc (fun _ => N) N :=
  ⟨[true,false,false]⟩
private def unitVector (N : ℕ) :
    (BalancedInduction.induced (truncatedAppend D Sc (fun _ => N) N [false])
      (input N)).obj (target N) :=
  BalancedInduction.unit (truncatedAppend D Sc (fun _ => N) N [false])
    ((truncatedAppend D Sc (fun _ => N) N [false]) ⋙ (rep N).toFunctor)
    (⟨[true,false]⟩ : TruncatedCategory D Sc (fun _ => N) N) (vector N)

/-- Both inverse products use the prescribed old/truncated induction maps. -/
example (N : ℕ) : (comparison N).hom ≫ (comparison N).inv = 𝟙 _ :=
  (comparison N).hom_inv_id

example (N : ℕ) : (comparison N).inv ≫ (comparison N).hom = 𝟙 _ :=
  (comparison N).inv_hom_id

private theorem equiv_symm_ne_zero {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] [Module ℚ A] [Module ℚ B]
    (e : A ≃ₗ[ℚ] B) (b : B) (hb : b ≠ 0) : e.symm b ≠ 0 := by
  intro h
  exact hb (e.symm.injective (h.trans e.symm.map_zero.symm))

/-- The module comparison is tested on a cofinally nonzero induced vector:
the existing counit sends its unit tensor to the odd mixed-crossing vector. -/
example : ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
    (moduleIsoLinearEquiv (comparison N) (target N)).symm (unitVector N) ≠ 0 := by
  obtain ⟨K, hK⟩ := extendedAtMost_detected_at_high_cutoffs D
    CyclotomicAction.AsymmetricParameters.symmetrizer Sc
    CyclotomicAction.AsymmetricParameters.homogeneous
    [false,true,false] [true,false,false] 3
  refine ⟨K, fun N hN hz => ?_⟩
  have hv : vector N ≠ 0 := by
    intro h
    apply recoveryPoint_ne_zero
    apply hK (fun _ => N) N (fun _ => hN) hN
    exact h.trans (map_zero _).symm
  have hu : unitVector N ≠ 0 := by
    intro h
    have he := congrArg (fun f => f (vector N))
      (BalancedInduction.counit_unit (truncatedAppend D Sc (fun _ => N) N [false])
        (rep N).toFunctor (⟨[true,false]⟩ : TruncatedCategory D Sc (fun _ => N) N))
    change BalancedInduction.counit (truncatedAppend D Sc (fun _ => N) N [false])
      (rep N).toFunctor (target N) (unitVector N) = vector N at he
    rw [h, map_zero] at he
    exact hv he.symm
  exact equiv_symm_ne_zero (moduleIsoLinearEquiv (comparison N) (target N))
    (unitVector N) hu hz

end OddMath.QuiverHecke.AppendQuotientComparisonExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVAppendQuotientComparison
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
