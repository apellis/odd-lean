import OddMath.Frontier.EQHalfGradedUnitDerivedParityCoherence

/-!
# Derived restriction and the original parity involutions

At every rank, the original `restrictParityIso` intertwines the original
`parityShiftDIso` involutions. The proof pastes their published `Q` component
formulas with the actual module involution square, then descends by localization.
The source derived Hom universe equals the module universe, as required by the
original comparison; the target derived Hom universe remains independent.
-/

noncomputable section
open CategoryTheory DG
set_option backward.isDefEq.respectTransparency false
universe w w₂
namespace OddMath.Frontier.EQHalfGradedUnit
open CatModule.DerivedCategory RestrictionCoherence

variable (N : ℕ)
  [CatModule.HasDerivedCategory.{w, w} (WeightCategory source.Regraded)]
  [CatModule.HasDerivedCategory.{w₂, w} (WeightCategory (target N).Regraded)]

/-- The two actual derived restriction-involution composites agree on localized modules. -/
theorem Q_restrictParityIso_involution
    (M : CatModule.{w} (WeightCategory (target N).Regraded)) :
    (HalfGradedDGRing.parityShiftD source).map
        ((restrictParityIso N).hom.app (Q.obj M)) ≫
      (restrictParityIso N).hom.app
        ((HalfGradedDGRing.parityShiftD (target N)).obj (Q.obj M)) ≫
      (restrict (weightFunctor N)).map
        ((HalfGradedDGRing.parityShiftDIso (target N)).hom.app (Q.obj M)) =
    (HalfGradedDGRing.parityShiftDIso source).hom.app
      ((restrict (weightFunctor N)).obj (Q.obj M)) := by
  let R := restrict (weightFunctor N)
  let Ps := HalfGradedDGRing.parityShiftD source
  let Pt := HalfGradedDGRing.parityShiftD (target N)
  let Rm := CatModule.precomp (weightFunctor N)
  let Psm := HalfGradedDGRing.parityShift source
  let Ptm := HalfGradedDGRing.parityShift (target N)
  let α := (restrictParityIso N).hom
  let αm := (precompParityIso N).hom
  let qR := (QCompRestrictIso (weightFunctor N)).hom
  let qS := (HalfGradedDGRing.QCompParityShiftDIso source).hom
  let qT := (HalfGradedDGRing.QCompParityShiftDIso (target N)).hom
  let iS := (HalfGradedDGRing.parityShiftDIso source).hom
  let iT := (HalfGradedDGRing.parityShiftDIso (target N)).hom
  let imS := (HalfGradedDGRing.parityShiftIso source).hom
  let imT := (HalfGradedDGRing.parityShiftIso (target N)).hom
  have hα (L : CatModule.{w} (WeightCategory (target N).Regraded)) :
      Ps.map (qR.app L) ≫ qS.app (Rm.obj L) ≫ Q.map (αm.app L) =
        α.app (Q.obj L) ≫ R.map (qT.app L) ≫ qR.app (Ptm.obj L) :=
    Q_restrictParityIso_hom_app N L
  have hS : iS.app (Q.obj (Rm.obj M)) =
      Ps.map (qS.app (Rm.obj M)) ≫ qS.app (Psm.obj (Rm.obj M)) ≫
        Q.map (imS.app (Rm.obj M)) :=
    Q_parityShiftDIso_hom_app source (Rm.obj M)
  have hT : iT.app (Q.obj M) =
      Pt.map (qT.app M) ≫ qT.app (Ptm.obj M) ≫ Q.map (imT.app M) :=
    Q_parityShiftDIso_hom_app (target N) M
  change Ps.map (α.app (Q.obj M)) ≫ α.app (Pt.obj (Q.obj M)) ≫
    R.map (iT.app (Q.obj M)) = iS.app (R.obj (Q.obj M))
  apply (cancel_mono (qR.app M)).mp
  simp only [hT, Functor.map_comp, Category.assoc]
  have hnα : Ps.map (R.map (qT.app M)) ≫ α.app (Q.obj (Ptm.obj M)) =
      α.app (Pt.obj (Q.obj M)) ≫ R.map (Pt.map (qT.app M)) :=
    α.naturality (qT.app M)
  rw [← reassoc_of% hnα]
  have hnR : R.map (Q.map (imT.app M)) ≫ qR.app M =
      qR.app (Ptm.obj (Ptm.obj M)) ≫ Q.map (Rm.map (imT.app M)) :=
    qR.naturality (imT.app M)
  rw [hnR]
  rw [← reassoc_of% (hα (Ptm.obj M))]
  have hαPs := congrArg Ps.map (hα M)
  simp only [Functor.map_comp] at hαPs
  rw [← reassoc_of% hαPs]
  have hnqS : Ps.map (Q.map (αm.app M)) ≫ qS.app (Rm.obj (Ptm.obj M)) =
      qS.app (Psm.obj (Rm.obj M)) ≫ Q.map (Psm.map (αm.app M)) :=
    qS.naturality (αm.app M)
  rw [reassoc_of% hnqS]
  have hm : Q.map (Psm.map (αm.app M)) ≫ Q.map (αm.app (Ptm.obj M)) ≫
      Q.map (Rm.map (imT.app M)) = Q.map (imS.app (Rm.obj M)) :=
    Q_map_precompParityIso_involution N M
  rw [hm]
  have hniS : Ps.map (Ps.map (qR.app M)) ≫ iS.app (Q.obj (Rm.obj M)) =
      iS.app (R.obj (Q.obj M)) ≫ qR.app M := iS.naturality (qR.app M)
  rw [← hniS, hS]

/-- The full natural-isomorphism square for the original comparison and involutions.
Descent uses the localization universal property, with no rank restriction. -/
theorem restrictParityIso_involution_natIso :
    (Functor.associator (restrict (weightFunctor N))
        (HalfGradedDGRing.parityShiftD source)
        (HalfGradedDGRing.parityShiftD source)).symm ≪≫
      Functor.isoWhiskerRight (restrictParityIso N) (HalfGradedDGRing.parityShiftD source) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (HalfGradedDGRing.parityShiftD (target N))
        (restrictParityIso N) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (HalfGradedDGRing.parityShiftDIso (target N))
        (restrict (weightFunctor N)) ≪≫
      Functor.leftUnitor (restrict (weightFunctor N)) =
    Functor.isoWhiskerLeft (restrict (weightFunctor N))
        (HalfGradedDGRing.parityShiftDIso source) ≪≫
      Functor.rightUnitor (restrict (weightFunctor N)) := by
  apply Iso.ext
  apply Localization.natTrans_ext Q (CatModule.quasiIso (WeightCategory (target N).Regraded))
  intro M
  simpa using Q_restrictParityIso_involution N M

/-- Restriction intertwines the actual derived parity involutions on every derived object. -/
theorem restrictParityIso_involution
    (X : CatModule.DerivedCategory.{w₂, w} (WeightCategory (target N).Regraded)) :
    (HalfGradedDGRing.parityShiftD source).map ((restrictParityIso N).hom.app X) ≫
      (restrictParityIso N).hom.app ((HalfGradedDGRing.parityShiftD (target N)).obj X) ≫
      (restrict (weightFunctor N)).map
        ((HalfGradedDGRing.parityShiftDIso (target N)).hom.app X) =
    (HalfGradedDGRing.parityShiftDIso source).hom.app
      ((restrict (weightFunctor N)).obj X) := by
  simpa using NatTrans.congr_app
    (congrArg Iso.hom (restrictParityIso_involution_natIso N)) X

end OddMath.Frontier.EQHalfGradedUnit
