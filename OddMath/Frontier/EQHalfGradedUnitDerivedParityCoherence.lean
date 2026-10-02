import OddMath.Frontier.EQHalfGradedRestrictionCoherence

/-!
# Localization coherence of the existing integral-unit parity comparison

All comparisons below are the original restriction and parity comparisons.
The source derived Hom universe equals the module universe, as required by
`restrictParityIso`; the target derived Hom universe is independent. We prove
its actual `Q` comparison and the localized component formula for the original
`parityShiftDIso`. The full derived restriction-involution square is not proved
here; these are bounded prerequisites, not a replacement comparison or involution.
-/

noncomputable section
open CategoryTheory DG
set_option backward.isDefEq.respectTransparency false
universe w w₂
namespace OddMath.Frontier.EQHalfGradedUnit
open CatModule.DerivedCategory
open RestrictionCoherence

variable (N : ℕ)
  [CatModule.HasDerivedCategory.{w, w} (WeightCategory source.Regraded)]
  [CatModule.HasDerivedCategory.{w₂, w} (WeightCategory (target N).Regraded)]

/-- The original internal-shift comparison computes through the original `Q` comparisons. -/
theorem Q_restrictInternalShiftIso_hom_app (s : ℤ)
    (M : CatModule.{w} (WeightCategory (target N).Regraded)) :
    (internalShift source.Regraded s).map ((QCompRestrictIso (weightFunctor N)).hom.app M) ≫
        (QCompInternalShiftIso source.Regraded s).hom.app
          ((CatModule.precomp (weightFunctor N)).obj M) ≫
        Q.map ((precompInternalShiftIso N s).hom.app M) =
      (restrictInternalShiftIso N s).hom.app (Q.obj M) ≫
        (restrict (weightFunctor N)).map
          ((QCompInternalShiftIso (target N).Regraded s).hom.app M) ≫
        (QCompRestrictIso (weightFunctor N)).hom.app
          ((HalfGradedDGRing.internalShiftFunctor (target N) s).obj M) := by
  apply (cancel_epi ((restrictCompIso
    (WeightCategory.shiftFunctor source.Regraded s) (weightFunctor N)).hom.app
      (Q.obj M))).mp
  simp only [restrictInternalShiftIso, precompInternalShiftIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Q.map_comp, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [Q_restrictCompIso_hom_app, Q_restrictCompIso_hom_app]
  simp only [QCompInternalShiftIso, internalShift,
    HalfGradedDGRing.internalShiftFunctor, Category.assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [(restrict (WeightCategory.shiftFunctor source.Regraded s)).map_id,
    (restrict (weightFunctor N)).map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  erw [← Q.map_comp_assoc, Iso.hom_inv_id_app, Q.map_id]
  simp only [Category.id_comp]
  erw [Category.comp_id, Category.comp_id, Category.comp_id]
  rfl

/-- Shift compatibility for the original restriction-localization comparison. -/
theorem QCompRestrictIso_shift_inv (n : ℤ)
    (M : CatModule.{w} (WeightCategory (target N).Regraded)) :
    ((QCompRestrictIso (weightFunctor N)).hom.app M)⟦n⟧' ≫
        (Q.commShiftIso n).inv.app ((CatModule.precomp (weightFunctor N)).obj M) ≫
        Q.map (((CatModule.precomp (weightFunctor N)).commShiftIso n).inv.app M) =
      ((restrict (weightFunctor N)).commShiftIso n).inv.app (Q.obj M) ≫
        (restrict (weightFunctor N)).map ((Q.commShiftIso n).inv.app M) ≫
        (QCompRestrictIso (weightFunctor N)).hom.app (M⟦n⟧) := by
  rw [NatTrans.shift_app]
  simp only [Functor.commShiftIso_comp_inv_app, Functor.commShiftIso_comp_hom_app,
    Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  erw [Q.map_id, Category.comp_id]

/-- The requested `Q`-whiskering square for the existing parity comparison. -/
theorem Q_restrictParityIso_hom_app
    (M : CatModule.{w} (WeightCategory (target N).Regraded)) :
    (HalfGradedDGRing.parityShiftD source).map
        ((QCompRestrictIso (weightFunctor N)).hom.app M) ≫
        (HalfGradedDGRing.QCompParityShiftDIso source).hom.app
          ((CatModule.precomp (weightFunctor N)).obj M) ≫
        Q.map ((precompParityIso N).hom.app M) =
      (restrictParityIso N).hom.app (Q.obj M) ≫
        (restrict (weightFunctor N)).map
          ((HalfGradedDGRing.QCompParityShiftDIso (target N)).hom.app M) ≫
        (QCompRestrictIso (weightFunctor N)).hom.app
          ((HalfGradedDGRing.parityShift (target N)).obj M) := by
  have hm : (precompParityIso N).hom.app M =
      ((precompInternalShiftIso N (-2)).hom.app M)⟦(1 : ℤ)⟧' ≫
        ((CatModule.precomp (weightFunctor N)).commShiftIso (1 : ℤ)).inv.app
          ((HalfGradedDGRing.internalShiftFunctor (target N) (-2)).obj M) := by
    simp [precompParityIso]
    exact Category.id_comp _
  rw [hm]
  simp only [HalfGradedDGRing.parityShiftD, HalfGradedDGRing.QCompParityShiftDIso,
    restrictParityIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
    Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  erw [← Q.commShiftIso_inv_naturality_assoc
    ((precompInternalShiftIso N (-2)).hom.app M) (1 : ℤ)]
  have h := congrArg
    ((shiftFunctor (CatModule.DerivedCategory.{w, w}
      (WeightCategory source.Regraded)) (1 : ℤ)).map)
    (Q_restrictInternalShiftIso_hom_app N (-2) M)
  simp only [Functor.map_comp] at h
  rw [reassoc_of% h]
  erw [QCompRestrictIso_shift_inv N (1 : ℤ)
    ((HalfGradedDGRing.internalShiftFunctor (target N) (-2)).obj M)]
  rw [← Functor.commShiftIso_inv_naturality_assoc]
  rfl

end OddMath.Frontier.EQHalfGradedUnit

namespace OddMath.Frontier.RestrictionCoherence
universe wD wM u
open CatModule.DerivedCategory

/-- The pre-existing derived parity involution computes to its original module involution.
This lemma does not yet identify the two derived restriction-involution composites. -/
theorem Q_parityShiftDIso_hom_app {A : Type u} [Ring A] {k : ℤ}
    (H : HalfGradedDGRing A k)
    [CatModule.HasDerivedCategory.{wD, wM} (WeightCategory H.Regraded)]
    (M : CatModule.{wM} (WeightCategory H.Regraded)) :
    (HalfGradedDGRing.parityShiftDIso H).hom.app (Q.obj M) =
      (HalfGradedDGRing.parityShiftD H).map
          ((HalfGradedDGRing.QCompParityShiftDIso H).hom.app M) ≫
        (HalfGradedDGRing.QCompParityShiftDIso H).hom.app
          ((HalfGradedDGRing.parityShift H).obj M) ≫
        Q.map ((HalfGradedDGRing.parityShiftIso H).hom.app M) := by
  have h : Functor.isoWhiskerLeft Q (HalfGradedDGRing.parityShiftDIso H) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (HalfGradedDGRing.QCompParityShiftDIso H) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (HalfGradedDGRing.QCompParityShiftDIso H) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (HalfGradedDGRing.parityShiftIso H) _ ≪≫
        Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm := by
    apply Iso.ext
    exact (Localization.whiskeringLeftFunctor' Q
      (CatModule.quasiIso (WeightCategory H.Regraded)) _).map_preimage _
  simpa using NatTrans.congr_app (congrArg Iso.hom h) M

end OddMath.Frontier.RestrictionCoherence
