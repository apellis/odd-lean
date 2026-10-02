import OddMath.Frontier.EQHalfGradedUnitDerivedParityInvolution

/-!
# Low-rank induction and the original parity involutions

The comparison here is the original `derivedEquivalenceParityIso`, formed from
Keller's unit and counit and the original restriction comparison. No parity
functor, involution, or comparison is replaced by transport.
-/

noncomputable section
open CategoryTheory DG
set_option backward.isDefEq.respectTransparency false
universe w w₂
namespace OddMath.Frontier.EQHalfGradedUnit

variable {N : ℕ}
  [CatModule.HasDerivedCategory.{w, w} (WeightCategory source.Regraded)]
  [CatModule.HasDerivedCategory.{w₂, w} (WeightCategory (target N).Regraded)]

/-- The original forward comparison satisfies the unit mate identity. -/
theorem forwardComparison_unit (hN : N ≤ 1)
    (S : CatModule.DerivedCategory.{w, w} (WeightCategory source.Regraded) ⥤
      CatModule.DerivedCategory.{w, w} (WeightCategory source.Regraded))
    (T : CatModule.DerivedCategory.{w₂, w} (WeightCategory (target N).Regraded) ⥤
      CatModule.DerivedCategory.{w₂, w} (WeightCategory (target N).Regraded))
    (e : (derivedEquivalence hN).inverse ⋙ S ≅ T ⋙ (derivedEquivalence hN).inverse)
    (X : CatModule.DerivedCategory.{w, w} (WeightCategory source.Regraded)) :
    S.map ((derivedEquivalence hN).unitIso.hom.app X) ≫
      e.hom.app ((derivedEquivalence hN).functor.obj X) ≫
      (derivedEquivalence hN).inverse.map ((forwardComparison hN S T e).hom.app X) =
    (derivedEquivalence hN).unitIso.hom.app (S.obj X) := by
  let E := derivedEquivalence hN
  have hb : (forwardComparison hN S T e).hom.app X =
      E.counitIso.inv.app (T.obj (E.functor.obj X)) ≫
        E.functor.map (e.inv.app (E.functor.obj X)) ≫
        E.functor.map (S.map (E.unitIso.inv.app X)) := by
    simp [forwardComparison, E]
  rw [hb]
  change S.map (E.unit.app X) ≫ e.hom.app (E.functor.obj X) ≫
    E.inverse.map (_ ≫ _ ≫ _) = E.unit.app (S.obj X)
  simp only [Functor.map_comp, ← E.unit_app_inverse]
  rw [reassoc_of% (E.unit_naturality (e.inv.app (E.functor.obj X)))]
  have hn := E.unit_naturality (S.map (E.unitIso.inv.app X))
  dsimp only [Functor.comp_obj] at hn
  rw [hn]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, ← S.map_comp]
  simp only [Equivalence.unit, Iso.hom_inv_id_app, Functor.id_obj]
  erw [S.map_id, Category.id_comp]

/-- Actual low-rank derived induction intertwines the original parity involutions. -/
theorem derivedEquivalenceParityIso_involution (hN : N ≤ 1)
    (X : CatModule.DerivedCategory.{w, w} (WeightCategory source.Regraded)) :
    (HalfGradedDGRing.parityShiftD (target N)).map
        ((derivedEquivalenceParityIso hN).hom.app X) ≫
      (derivedEquivalenceParityIso hN).hom.app
        ((HalfGradedDGRing.parityShiftD source).obj X) ≫
      (derivedEquivalence hN).functor.map
        ((HalfGradedDGRing.parityShiftDIso source).hom.app X) =
    (HalfGradedDGRing.parityShiftDIso (target N)).hom.app
      ((derivedEquivalence hN).functor.obj X) := by
  let E := derivedEquivalence hN
  let S := HalfGradedDGRing.parityShiftD source
  let T := HalfGradedDGRing.parityShiftD (target N)
  let α := (restrictParityIso N).hom
  let β := (derivedEquivalenceParityIso hN).hom
  let u := E.unitIso.hom
  let iS := (HalfGradedDGRing.parityShiftDIso source).hom
  let iT := (HalfGradedDGRing.parityShiftDIso (target N)).hom
  have hm (Y : CatModule.DerivedCategory.{w, w} (WeightCategory source.Regraded)) :
      S.map (u.app Y) ≫ α.app (E.functor.obj Y) ≫ E.inverse.map (β.app Y) =
        u.app (S.obj Y) := forwardComparison_unit hN S T (restrictParityIso N) Y
  have hn : S.map (E.inverse.map (β.app X)) ≫ α.app (E.functor.obj (S.obj X)) =
      α.app (T.obj (E.functor.obj X)) ≫ E.inverse.map (T.map (β.app X)) :=
    α.naturality (β.app X)
  have hr : S.map (α.app (E.functor.obj X)) ≫
      α.app (T.obj (E.functor.obj X)) ≫ E.inverse.map (iT.app (E.functor.obj X)) =
        iS.app (E.inverse.obj (E.functor.obj X)) :=
    restrictParityIso_involution N (E.functor.obj X)
  change T.map (β.app X) ≫ β.app (S.obj X) ≫ E.functor.map (iS.app X) =
    iT.app (E.functor.obj X)
  apply E.inverse.map_injective
  apply (cancel_epi (S.map (S.map (u.app X)) ≫ S.map (α.app (E.functor.obj X)) ≫
    α.app (T.obj (E.functor.obj X)))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  have hSm := congrArg S.map (hm X)
  simp only [Functor.map_comp] at hSm
  rw [reassoc_of% hSm, reassoc_of% (hm (S.obj X))]
  have hu := E.unit_naturality (iS.app X)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hu
  rw [hu, hr]
  exact (iS.naturality (u.app X)).symm

/-- The full natural-isomorphism square for the original induction comparison. -/
theorem derivedEquivalenceParityIso_involution_natIso (hN : N ≤ 1) :
    (Functor.associator (derivedEquivalence hN).functor
        (HalfGradedDGRing.parityShiftD (target N))
        (HalfGradedDGRing.parityShiftD (target N))).symm ≪≫
      Functor.isoWhiskerRight (derivedEquivalenceParityIso hN)
        (HalfGradedDGRing.parityShiftD (target N)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (HalfGradedDGRing.parityShiftD source)
        (derivedEquivalenceParityIso hN) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (HalfGradedDGRing.parityShiftDIso source)
        (derivedEquivalence hN).functor ≪≫
      Functor.leftUnitor (derivedEquivalence hN).functor =
    Functor.isoWhiskerLeft (derivedEquivalence hN).functor
        (HalfGradedDGRing.parityShiftDIso (target N)) ≪≫
      Functor.rightUnitor (derivedEquivalence hN).functor := by
  apply Iso.ext
  ext X
  simpa using derivedEquivalenceParityIso_involution hN X

end OddMath.Frontier.EQHalfGradedUnit
