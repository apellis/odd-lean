import OddMath.QuiverHecke.CyclotomicAction.ELVContentPrincipalInverseCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDetection
import OddMath.QuiverHecke.CyclotomicAction.ELVCategoryCoefficientFaithful
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction CyclotomicCrossingTensor BalancedInduction
namespace ContentPrincipalInverseCoordinatesConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def M (v : List Bool) : ContentModules D Sc cut 8 (v : Multiset Bool) :=
  supermoduleParityObj ((restriction (contentInclusion D Sc cut 8 (v : Multiset Bool))).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨v⟩)))
private theorem positive (i : Bool) : 0 ≤ contentCrossingHeight D cut i ([i] : Multiset Bool) := by
  cases i <;> norm_num [contentCrossingHeight, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private theorem negative (i : Bool) : contentCrossingHeight D cut i ([i,i,i] : Multiset Bool) ≤ 0 := by
  cases i <;> norm_num [contentCrossingHeight, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private theorem middle (i : Bool) : contentCrossingHeight D cut i ([i,i] : Multiset Bool) = 0 := by
  cases i <;> norm_num [contentCrossingHeight, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private def fromInverse (i : Bool) := Classical.choice
  (contentSupportedLocalInverseFrom_nonempty D Sc cut 8 0 i (M [i]) (positive i))
private def toInverse (i : Bool) := Classical.choice
  (contentSupportedLocalInverseTo_nonempty D Sc cut 8 [i,i] i (M [i,i,i]) (negative i))
private def zeroFrom (i : Bool) := Classical.choice
  (contentSupportedLocalInverseFrom_nonempty D Sc cut 8 [i] i (M [i,i]) (le_of_eq (middle i).symm))
private def zeroTo (i : Bool) := Classical.choice
  (contentSupportedLocalInverseTo_nonempty D Sc cut 8 [i] i (M [i,i]) (le_of_eq (middle i)))
/-- Both moving parities retain the exact weighted principal in the selected charts. -/
example (i : Bool) := contentSupportedLocalInverseFrom_principal D Sc cut 8 0 i
  (M [i]) (fromInverse i) (positive i)
example (i : Bool) := contentSupportedLocalInverseTo_principal D Sc cut 8 [i,i] i
  (M [i,i,i]) (toInverse i) (negative i)
example (i : Bool) := contentSupportedLocalInverseFrom_principal D Sc cut 8 [i] i
  (M [i,i]) (zeroFrom i) (le_of_eq (middle i).symm)
example (i : Bool) := contentSupportedLocalInverseTo_principal D Sc cut 8 [i] i
  (M [i,i]) (zeroTo i) (le_of_eq (middle i))
/-- Stored lower and upper successor contents keep the same principal. -/
example (i : Bool) := contentTargetsLocalInverseFrom_principal D Sc cut 8 0 i
  [i] [i,i] rfl rfl (M [i]) (fromInverse i) (positive i)
example (i : Bool) := contentTargetsLocalInverseTo_principal D Sc cut 8 [i,i] i
  [i,i,i] [i,i,i,i] rfl rfl (M [i,i,i]) (toInverse i) (negative i)
end ContentPrincipalInverseCoordinatesConsumer

namespace ContentPrincipalInverseCoordinatesNonzero
private def D : SKM.Datum Unit ℤ where
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
private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)
private abbrev cut : Unit → ℕ := fun _ => 2
private def v : ContentCategory D Sc cut 3 ([()] : Multiset Unit) := ⟨⟨[()]⟩, rfl⟩
private def R := contentRepresentable D Sc cut 3 ([()] : Multiset Unit) v
private def z : R.obj v := truncatedSingle D Sc cut 3 () (SKM.SYM.delta D ℚ ⟨(), rfl⟩) 0
private theorem z_ne_zero : z ≠ 0 := truncatedSingle_delta_ne_zero D Sc rfl
private theorem height : contentCrossingHeight D cut () ([()] : Multiset Unit) = 0 := by
  decide
private def fromInverse := Classical.choice
  (contentTargetsLocalInverseFrom_nonempty D Sc cut 3 0 () [()] [(),()] rfl rfl R
    (le_of_eq height.symm))
private def toInverse := Classical.choice
  (contentTargetsLocalInverseTo_nonempty D Sc cut 3 0 () [()] [(),()] rfl rfl R
    (le_of_eq height))
/-- Both height-zero orientations are tested on an occupied positive-content module. -/
example : z ≠ 0 := z_ne_zero
example := contentTargetsLocalInverseFrom_principal D Sc cut 3 0 ()
  [()] [(),()] rfl rfl R fromInverse (le_of_eq height.symm)
example := contentTargetsLocalInverseTo_principal D Sc cut 3 0 ()
  [()] [(),()] rfl rfl R toInverse (le_of_eq height)
end ContentPrincipalInverseCoordinatesNonzero


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentPrincipalInverseCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
