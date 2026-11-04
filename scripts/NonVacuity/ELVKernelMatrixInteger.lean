import OddMath.QuiverHecke.CyclotomicAction.ELVKernelMatrixInteger
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDetection
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedCategory
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory GradedSupercategory OddMath
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld CyclotomicCrossingTensor
namespace NonVacuity.KernelMatrixInteger
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev sy := CyclotomicAction.AsymmetricParameters.symmetrizer
private theorem hc : Sc.Homogeneous := CyclotomicAction.AsymmetricParameters.homogeneous
private def cutoff (_ : Bool) : ℕ := 8
private def t : OldCategory D Sc cutoff := ⟨[false,true,false]⟩
private def hzero (i : Bool) : OldCategory D Sc cutoff :=
  ⟨if i then [true,true,true,true] else [false,false,false,false]⟩
private theorem positive_height (i : Bool) :
    0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset Bool) := by
  cases i <;> norm_num [contentCrossingHeight, cutoff, t, D,
    CyclotomicAction.AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private theorem zero_height (i : Bool) :
    contentCrossingHeight D cutoff i ((hzero i).word : Multiset Bool) = 0 := by
  cases i <;> norm_num [contentCrossingHeight, cutoff, hzero, D,
    CyclotomicAction.AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]

-- Both unequal symmetrizer degrees are tested on the actual positive inverse.
example (i : Bool) : positiveKernelPrincipalInverse D Sc cutoff i t t (positive_height i)
    (𝟙 ((append D Sc cutoff i).obj t)) ∈
      representedKernelDegree D Sc cutoff sy hc i t t (0 + 2 * sy.d i) :=
  positiveKernelPrincipalInverse_degree D Sc cutoff sy hc i t t (positive_height i)
    ((oldCategoryGradedSupercategory D Sc cutoff sy hc).id_mem_degree _)

-- At height zero both actual finite matrices have only their principal coordinate.
example (i : Bool) : positiveKernelPrincipalInverse D Sc cutoff i (hzero i) (hzero i)
    (by rw [zero_height]) (𝟙 ((append D Sc cutoff i).obj (hzero i))) ∈
      representedKernelDegree D Sc cutoff sy hc i (hzero i) (hzero i) (0 + 2 * sy.d i) :=
  positiveKernelPrincipalInverse_degree D Sc cutoff sy hc i _ _ (by rw [zero_height])
    ((oldCategoryGradedSupercategory D Sc cutoff sy hc).id_mem_degree _)
example (i : Bool) : negativeKernelPrincipalInverse D Sc cutoff i (hzero i) (hzero i)
    (by rw [zero_height]) (𝟙 ((append D Sc cutoff i).obj (hzero i))) ∈
      representedKernelDegree D Sc cutoff sy hc i (hzero i) (hzero i) (0 + 2 * sy.d i) :=
  negativeKernelPrincipalInverse_degree D Sc cutoff sy hc i _ _ (by rw [zero_height])
    ((oldCategoryGradedSupercategory D Sc cutoff sy hc).id_mem_degree _)
example : 2 * sy.d false = 4 := rfl
example : 2 * sy.d true = 2 := rfl

-- A strictly negative height exercises the cap rows as well as the principal coordinate.
private def negative : OldCategory D Sc cutoff := ⟨[true,true,true,true,true,true]⟩
private theorem negative_height :
    contentCrossingHeight D cutoff true (negative.word : Multiset Bool) ≤ 0 := by
  norm_num [contentCrossingHeight, cutoff, negative, D,
    CyclotomicAction.AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
example : negativeKernelPrincipalInverse D Sc cutoff true negative negative negative_height
    (𝟙 ((append D Sc cutoff true).obj negative)) ∈
      representedKernelDegree D Sc cutoff sy hc true negative negative (0 + 2 * sy.d true) :=
  negativeKernelPrincipalInverse_degree D Sc cutoff sy hc true _ _ negative_height
    ((oldCategoryGradedSupercategory D Sc cutoff sy hc).id_mem_degree _)

-- An off-content source is retained; no equality of formal contents was added.
private def different : OldCategory D Sc cutoff := ⟨[]⟩
example := positiveKernelEquiv D Sc cutoff false different t (positive_height false)
example := negativeKernelEquiv D Sc cutoff true different negative negative_height
example (i : Bool) := (positiveKernelIntegerCoordinates D Sc cutoff sy hc i 3 t t).internal
example (i : Bool) := (negativeKernelIntegerCoordinates D Sc cutoff sy hc i 3 t t).internal

-- Independently detected occupied odd input for the actual positive inverse.
private def O : SKM.Datum Unit ℤ where
  cd := {
    root := fun _ => 2
    coroot := fun _ => LinearMap.id
    coroot_root_self := fun _ => rfl }
  isGCM := {
    diag := fun _ => rfl
    offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
    zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 1
  even_of_odd := fun _ _ _ => even_two
private def Os : SKM.Scalars O ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)
private def Oy : SKM.Symmetrizer O where
  d := fun _ => 1
  pos := fun _ => by decide
  symm := fun _ _ => rfl
private theorem Oh : Os.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim
private def Oc (_ : Unit) : ℕ := 2
private def vacuum : OldCategory O Os Oc := ⟨[]⟩
private abbrev strand := (append O Os Oc ()).obj vacuum
private def truncStrand : TruncatedCategory O Os Oc 3 := ⟨[()]⟩
private theorem occupied_identity : (𝟙 strand : strand ⟶ strand) ≠ 0 := by
  have hz := truncatedSingle_delta_ne_zero O Os rfl
  have ht : (𝟙 truncStrand : truncStrand ⟶ truncStrand) ≠ 0 := by
    intro h
    apply hz
    calc
      _ = (𝟙 truncStrand) ≫ truncatedSingle O Os Oc 3 () (SKM.SYM.delta O ℚ ⟨(),rfl⟩) 0 :=
        (Category.id_comp _).symm
      _ = 0 := by rw [h, Limits.zero_comp]
  intro h
  apply ht
  exact congrArg (truncateOld O Os Oc 3 [()] [()]) h
private theorem occupied_height : 0 ≤ contentCrossingHeight O Oc () (vacuum.word : Multiset Unit) := by
  norm_num [contentCrossingHeight, vacuum, Oc]
private theorem inverse_nonzero {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℚ V] [Module ℚ W] (E : V ≃ₗ[ℚ] W) {y : W} (hy : y ≠ 0) : E.symm y ≠ 0 := by
  intro h
  exact hy (E.symm.map_eq_zero_iff.mp h)
example : (positiveKernelEquiv O Os Oc () vacuum vacuum occupied_height).symm (𝟙 strand) ≠ 0 :=
  inverse_nonzero _ occupied_identity
example : (positiveKernelEquiv O Os Oc () vacuum vacuum occupied_height).symm (𝟙 strand) ∈
    (positiveKernelIntegerCoordinates O Os Oc Oy Oh ()
      (contentUnitCount O Oc () (vacuum.word : Multiset Unit)) vacuum vacuum).degree 0 :=
  positiveKernelEquiv_inverse_degree O Os Oc Oy Oh () vacuum vacuum occupied_height
    ((oldCategoryGradedSupercategory O Os Oc Oy Oh).id_mem_degree _)
end NonVacuity.KernelMatrixInteger

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.Algebra.IntegerMatrixGrading,
      `OddMath.QuiverHecke.CyclotomicAction.ELVKernelMatrixInteger] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
