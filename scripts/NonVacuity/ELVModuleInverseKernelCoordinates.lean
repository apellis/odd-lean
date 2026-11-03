import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInverseKernelCoordinates
import NonVacuity.ELVWeightedAppendFixture
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDetection
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
namespace NonVacuity.ModuleInverseKernelCoordinates
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 2
private abbrev C := OldCategory D Sc cut
private abbrev vacuum : C := ⟨[]⟩
private abbrev J (i : Bool) := append D Sc cut i
private abbrev R (i : Bool) := oldRepresentable D Sc cut ((J i).obj vacuum)
private abbrev M (i : Bool) := (BalancedInduction.restriction (J i)).obj (R i)
private theorem positive (i : Bool) :
    0 ≤ contentCrossingHeight D cut i (vacuum.word : Multiset Bool) := by
  cases i <;> decide

/-- Both moving parities retain the specified raw principal coefficient. -/
example (i : Bool) := moduleUnitMatrixIso_principal_inv_tensor D Sc cut (M i) i vacuum
  (positive i) vacuum (𝟙 ((J i).obj vacuum)) (𝟙 ((J i).obj vacuum))
example (i : Bool) := moduleUnitMatrixIso_inv_tensor D Sc cut (M i) i vacuum
  (positive i) vacuum (𝟙 ((J i).obj vacuum)) (𝟙 ((J i).obj vacuum))

private abbrev zword (i : Bool) : C := ⟨[i]⟩
private theorem zeroheight (i : Bool) :
    contentCrossingHeight D cut i ((zword i).word : Multiset Bool) = 0 := by
  cases i <;> decide
example (i : Bool) := moduleUnitMatrixIso_principal_inv_tensor D Sc cut ((BalancedInduction.restriction (J i)).obj
    (oldRepresentable D Sc cut ((J i).obj (zword i)))) i (zword i)
  (by rw [zeroheight]) (zword i) (𝟙 _) (𝟙 ((J i).obj (zword i)))
example (i : Bool) := moduleCapMatrixIso_principal_inv_tensor D Sc cut ((BalancedInduction.restriction (J i)).obj
    (oldRepresentable D Sc cut ((J i).obj (zword i)))) i (zword i)
  (by rw [zeroheight]) (zword i) (𝟙 _) (𝟙 ((J i).obj (zword i)))
private abbrev negword (i : Bool) : C := ⟨[i,i]⟩
private theorem negative (i : Bool) :
    contentCrossingHeight D cut i ((negword i).word : Multiset Bool) ≤ 0 := by
  cases i <;> decide
example (i : Bool) := moduleCapMatrixIso_principal_inv_tensor D Sc cut ((BalancedInduction.restriction (J i)).obj
    (oldRepresentable D Sc cut ((J i).obj (negword i)))) i (negword i)
  (negative i) (negword i) (𝟙 _) (𝟙 ((J i).obj (negword i)))
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
private def Oc (_ : Unit) : ℕ := 2
private def ovacuum : OldCategory O Os Oc := ⟨[]⟩
private abbrev strand := (append O Os Oc ()).obj ovacuum
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
private theorem occupied_height : 0 ≤ contentCrossingHeight O Oc () (ovacuum.word : Multiset Unit) := by
  norm_num [contentCrossingHeight, ovacuum, Oc]
private abbrev OJ := append O Os Oc ()
private abbrev OR := oldRepresentable O Os Oc strand
private abbrev OM := (BalancedInduction.restriction OJ).obj OR
private def point : mateTargetSpace O Os Oc () OM ovacuum :=
  BalancedInduction.tensor OJ OM.toFunctor ovacuum (𝟙 _) (𝟙 _)
private theorem point_nonzero : point ≠ 0 := by
  intro h
  have he := congrArg (BalancedInduction.counit OJ OR.toFunctor strand) h
  rw [map_zero] at he
  have ht := BalancedInduction.counit_tensor OJ OR.toFunctor strand ovacuum
    (𝟙 strand) (𝟙 strand)
  change (BalancedInduction.counit OJ OR.toFunctor strand) point = _ at ht
  have hi : OR.map (𝟙 strand) (𝟙 strand) = 𝟙 strand := by
    change (𝟙 strand) ≫ (𝟙 strand) = _
    exact Category.id_comp _
  exact occupied_identity (hi.symm.trans (ht.symm.trans he))
example := moduleUnitMatrixIso_principal_inv_tensor O Os Oc OM () ovacuum
  occupied_height ovacuum (𝟙 strand) (𝟙 strand)
/-- The inverse is evaluated on an independently detected nonzero tensor. -/
example : (moduleUnitMatrixIso O Os Oc OM () ovacuum occupied_height).inv point ≠ 0 := by
  intro h
  have he := congrArg (fun z => (moduleUnitMatrixIso O Os Oc OM () ovacuum
    occupied_height).hom z) h
  rw [map_zero] at he
  have hi := congrArg (fun f : mateTargetSpace O Os Oc () OM ovacuum ⟶
      mateTargetSpace O Os Oc () OM ovacuum => f point)
    (moduleUnitMatrixIso O Os Oc OM () ovacuum occupied_height).inv_hom_id
  exact point_nonzero (hi.symm.trans he)
end NonVacuity.ModuleInverseKernelCoordinates
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVModuleInverseKernelCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
