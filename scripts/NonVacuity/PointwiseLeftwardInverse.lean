import NonVacuity.PointwiseLeftwardFixture
import OddMath.QuiverHecke.SwappedAssembly.SupportedAugmentedInverse
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.PointwiseLeftwardInverse
open PointwiseLeftwardFixture
local instance tensorHomPi (A C : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
private theorem positive_height : D.h false (P.wt t) = 2 := by
  change D.h false ((Λ-contentWeight D 0)+(-Λ+contentWeight D (SPath.wordContent labels+0))) = 2
  norm_num [labels,wd,SPath.wordContent,contentWeight,Finsupp.weight_apply,
    SKM.Datum.h,SKM.Datum.α,D,collisionDatum,Λ]
private theorem negative_height : D.h true (P.wt t) = -2 := by
  change D.h true ((Λ-contentWeight D 0)+(-Λ+contentWeight D (SPath.wordContent labels+0))) = -2
  norm_num [labels,wd,SPath.wordContent,contentWeight,Finsupp.weight_apply,
    SKM.Datum.h,SKM.Datum.α,D,collisionDatum,Λ]

-- A nonzero actual supported input has a two-row positive window and
-- a two-column negative window, with no supplied raw-global inverse.
private theorem positive : P.PosInverseAt chosen false (P.wt t) t t supportedPath.obj
    (fun q p => leftward.lcrossSame false (P.wt t) q p supportedPath.obj)
    (fun n r p => leftward.dcup false n (P.wt t) r p supportedPath.obj) := by
  exact SupportedSectors.centralPointwiseLeftward_posInverseAt D originalSc m cutoff N Λ Λ
    probePairing reservoirPairing sy homogeneous false t supportedPath (by rw [positive_height]; decide)
private theorem negative : P.NegInverseAt chosen true (P.wt t) t t supportedPath.obj
    (fun q p => leftward.lcrossSame true (P.wt t) q p supportedPath.obj)
    (fun n q r => leftward.dcap true n (P.wt t) q r supportedPath.obj) := by
  exact SupportedSectors.centralPointwiseLeftward_negInverseAt D originalSc m cutoff N Λ Λ
    probePairing reservoirPairing sy homogeneous true t supportedPath (by rw [negative_height]; decide)

-- All ten matrix identities are used at the proved nonzero input.
example := positive.1
example := positive.2.1
example := positive.2.2.1 0 (by rw [positive_height]; decide)
example := positive.2.2.2.1 1 (by rw [positive_height]; decide)
example := positive.2.2.2.2 1 0 (by rw [positive_height]; decide) (by rw [positive_height]; decide)
example := negative.1
example := negative.2.1
example := negative.2.2.1 0 (by rw [negative_height]; decide)
example := negative.2.2.2.1 1 (by rw [negative_height]; decide)
example := negative.2.2.2.2 1 0 (by rw [negative_height]; decide) (by rw [negative_height]; decide)
example : ¬Limits.IsZero supportedPath.obj := supportedPath_nonzero

-- The nonempty inverse cup and cap families cannot collapse to zero.
example : ¬∀ p : SPath (wd D (P.wt t) [up false,dn false]) t t,
    leftward.dcup false 0 (P.wt t) (SPath.nil t) p supportedPath.obj = 0 := by
  intro hz
  have h := positive.2.2.2.2 0 0 (by rw [positive_height]; decide)
    (by rw [positive_height]; decide) (SPath.nil t) (SPath.nil t)
  simp only [hz, Limits.zero_comp, Finset.sum_const_zero,
    famDelta_self] at h
  exact supportedPath_nonzero ((Limits.IsZero.iff_id_eq_zero _).mpr h.symm)
example : ¬∀ q : SPath (wd D (P.wt t) [dn true,up true]) t t,
    leftward.dcap true 1 (P.wt t) q (SPath.nil t) supportedPath.obj = 0 := by
  intro hz
  have h := negative.2.2.2.2 1 1 (by rw [negative_height]; decide)
    (by rw [negative_height]; decide) (SPath.nil t) (SPath.nil t)
  simp only [hz, Limits.comp_zero, Finset.sum_const_zero,
    famDelta_self] at h
  exact supportedPath_nonzero ((Limits.IsZero.iff_id_eq_zero _).mpr h.symm)

example := P.leftwardOfPointwiseAugmentedInverse_vanishesOffWeight chosen

-- All outer sectors of this nonzero input satisfy the local presentation identities.
example :
    leftward.IsInverseAt chosen t supportedPath.obj :=
  SupportedSectors.pointwiseLeftward_isInverseAt D originalSc m cutoff N Λ Λ
    probePairing reservoirPairing sy homogeneous t supportedPath
end NonVacuity.PointwiseLeftwardInverse

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.SwappedAssembly.PointwiseLeftwardInverse,
      `OddMath.QuiverHecke.SwappedAssembly.SupportedPointwiseLeftwardInverse,
      `OddMath.QuiverHecke.SwappedAssembly.SupportedAugmentedInverse] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned declarations"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"Auditing {names.size} owned declarations in {owner}"
