import NonVacuity.PointwiseLeftwardFixture
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.RestrictedLeftward
import OddMath.QuiverHecke.SwappedAssembly.SupportedSupernaturality
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.RestrictedLeftward
open PointwiseLeftwardFixture
local instance homPi (A C : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
private abbrev Input := SupportedSectors.H D Sc m cutoff N Λ Λ t
private abbrev J : Input ⥤ P.H t := SupportedSectors.inclusion D Sc m cutoff N Λ Λ t
local instance : J.Additive := SupportedSectors.inclusion_additive D Sc m cutoff N Λ Λ t
local instance : J.Linear ℚ := SupportedSectors.inclusion_linear D Sc m cutoff N Λ Λ t
local instance : IsSuperfunctor ℚ J := SupportedSectors.inclusion_super D Sc m cutoff N Λ Λ t
private theorem positive_height : D.h false (P.wt t) = 2 := by
  change D.h false ((Λ-contentWeight D 0)+(-Λ+contentWeight D (SPath.wordContent labels+0))) = 2
  norm_num [labels,wd,SPath.wordContent,contentWeight,Finsupp.weight_apply,
    SKM.Datum.h,SKM.Datum.α,D,collisionDatum,Λ]
private theorem negative_height : D.h true (P.wt t) = -2 := by
  change D.h true ((Λ-contentWeight D 0)+(-Λ+contentWeight D (SPath.wordContent labels+0))) = -2
  norm_num [labels,wd,SPath.wordContent,contentWeight,Finsupp.weight_apply,
    SKM.Datum.h,SKM.Datum.α,D,collisionDatum,Λ]
private theorem hC : chosen.IsSupernatural :=
  elvProbeCrossCoeff_isSupernatural D originalSc m cutoff N Λ Λ
    probePairing reservoirPairing sy homogeneous

private theorem positive_nat :
    (∀ (q : SPath (wd D (P.wt t) [dn false,up false]) t t)
      (p : SPath (wd D (P.wt t) [up false,dn false]) t t),
      IsSupernatural ℚ (D.parity false * D.parity false)
        (F := J ⋙ P.pathFunctor q) (G := J ⋙ P.pathFunctor p)
        (fun Z => leftward.lcrossSame false (P.wt t) q p Z.obj)) ∧
    (∀ (n : Fin (D.h false (P.wt t)).toNat) (r : SPath (wd D (P.wt t) []) t t)
      (p : SPath (wd D (P.wt t) [up false,dn false]) t t),
      IsSupernatural ℚ (((n : ℕ) : ZMod 2) * D.parity false)
        (F := J ⋙ P.pathFunctor r) (G := J ⋙ P.pathFunctor p)
        (fun Z => leftward.dcup false n (P.wt t) r p Z.obj)) :=
  ProbeReservoir.leftward_supernatural_of_posInverseAt_comp chosen leftward hC false (P.wt t) t t J
    (fun Z => SupportedSectors.centralPointwiseLeftward_posInverseAt D originalSc m cutoff N Λ Λ
      probePairing reservoirPairing sy homogeneous false t Z (by rw [positive_height]; decide))

private theorem negative_nat :
    (∀ (q : SPath (wd D (P.wt t) [dn true,up true]) t t)
      (p : SPath (wd D (P.wt t) [up true,dn true]) t t),
      IsSupernatural ℚ (D.parity true * D.parity true)
        (F := J ⋙ P.pathFunctor q) (G := J ⋙ P.pathFunctor p)
        (fun Z => leftward.lcrossSame true (P.wt t) q p Z.obj)) ∧
    (∀ (n : Fin (-D.h true (P.wt t)).toNat) (q : SPath (wd D (P.wt t) [dn true,up true]) t t)
      (r : SPath (wd D (P.wt t) []) t t),
      IsSupernatural ℚ (((n : ℕ) : ZMod 2) * D.parity true)
        (F := J ⋙ P.pathFunctor q) (G := J ⋙ P.pathFunctor r)
        (fun Z => leftward.dcap true n (P.wt t) q r Z.obj)) :=
  ProbeReservoir.leftward_supernatural_of_negInverseAt_comp chosen leftward hC true (P.wt t) t t J
    (fun Z => SupportedSectors.centralPointwiseLeftward_negInverseAt D originalSc m cutoff N Λ Λ
      probePairing reservoirPairing sy homogeneous true t Z (by rw [negative_height]; decide))

local instance inputPi : PiSupercategory ℚ Input := SupportedSectors.homPi D Sc m cutoff N Λ Λ t
private def oddInput : (PiSupercategory.pi (R := ℚ)).obj supportedPath ⟶ supportedPath :=
  (PiSupercategory.ζ (R := ℚ) supportedPath).hom
private theorem oddInput_mem : oddInput ∈ parity (R := ℚ) _ _ 1 :=
  PiSupercategory.ζ_hom_mem (R := ℚ) supportedPath
private theorem oddInput_ne_zero : oddInput ≠ 0 := by
  intro hz
  have h := (PiSupercategory.ζ (R := ℚ) supportedPath).inv_hom_id
  change _ ≫ oddInput = 𝟙 supportedPath at h
  rw [hz,Limits.comp_zero] at h
  have hh := congrArg (fun f : End supportedPath => f.hom) h.symm
  change (𝟙 supportedPath.obj : End supportedPath.obj) = 0 at hh
  exact supportedPath_nonzero ((Limits.IsZero.iff_id_eq_zero _).mpr hh)

-- The restricted inverse entries have their prescribed parity at a nonzero input.
example (q : SPath (wd D (P.wt t) [dn false,up false]) t t)
    (p : SPath (wd D (P.wt t) [up false,dn false]) t t) := (positive_nat.1 q p).mem supportedPath
example (q : SPath (wd D (P.wt t) [dn true,up true]) t t)
    (p : SPath (wd D (P.wt t) [up true,dn true]) t t) := (negative_nat.1 q p).mem supportedPath
example (r : SPath (wd D (P.wt t) []) t t)
    (p : SPath (wd D (P.wt t) [up false,dn false]) t t) :=
  (positive_nat.2 ⟨1,by rw [positive_height]; decide⟩ r p).mem supportedPath
example (q : SPath (wd D (P.wt t) [dn true,up true]) t t)
    (r : SPath (wd D (P.wt t) []) t t) :=
  (negative_nat.2 ⟨1,by rw [negative_height]; decide⟩ q r).mem supportedPath

-- Naturality is tested on a nonzero odd input isomorphism, in both orientations.
example (r : SPath (wd D (P.wt t) []) t t)
    (p : SPath (wd D (P.wt t) [up false,dn false]) t t) :=
  (positive_nat.2 ⟨1,by rw [positive_height]; decide⟩ r p).naturality oddInput_mem
example (q : SPath (wd D (P.wt t) [dn true,up true]) t t)
    (r : SPath (wd D (P.wt t) []) t t) :=
  (negative_nat.2 ⟨1,by rw [negative_height]; decide⟩ q r).naturality oddInput_mem
example : oddInput ≠ 0 := oddInput_ne_zero
example : ¬Limits.IsZero supportedPath.obj := supportedPath_nonzero

-- The chosen supported attachment discharges every local inverse input.
example (a : Sector Bool) (q : SPath (wd D (P.wt t) [dn false,up false]) a t)
    (p : SPath (wd D (P.wt t) [up false,dn false]) a t) :=
  (SupportedSectors.pointwiseLeftward_lcrossSame_supernatural D originalSc m cutoff N Λ Λ
    probePairing reservoirPairing sy homogeneous false (P.wt t) q p).mem supportedPath
example (a : Sector Bool) (q : SPath (wd D (P.wt t) [dn true,up true]) a t)
    (p : SPath (wd D (P.wt t) [up true,dn true]) a t) :=
  (SupportedSectors.pointwiseLeftward_lcrossSame_supernatural D originalSc m cutoff N Λ Λ
    probePairing reservoirPairing sy homogeneous true (P.wt t) q p).naturality oddInput_mem
example (p : SPath (wd D (P.wt t) [up false,dn false]) t t) :=
  (SupportedSectors.pointwiseLeftward_dcup_supernatural D originalSc m cutoff N Λ Λ
    probePairing reservoirPairing sy homogeneous false 1 (P.wt t)
      (by rw [positive_height]; decide) (SPath.nil t) p).naturality oddInput_mem
example (q : SPath (wd D (P.wt t) [dn true,up true]) t t) :=
  (SupportedSectors.pointwiseLeftward_dcap_supernatural D originalSc m cutoff N Λ Λ
    probePairing reservoirPairing sy homogeneous true 1 (P.wt t)
      (by rw [negative_height]; decide) q (SPath.nil t)).naturality oddInput_mem
end NonVacuity.RestrictedLeftward

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.SwappedAssembly.Supernatural.RestrictedLeftward,
      `OddMath.QuiverHecke.SwappedAssembly.SupportedSupernaturality] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned declarations"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"Auditing {names.size} owned declarations in {owner}"
