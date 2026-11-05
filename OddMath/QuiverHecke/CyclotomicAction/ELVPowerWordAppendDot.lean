import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordMorphisms
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionWhiskering
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendQuotientTensors

/-! The selected regular-power word append comparison and its actual dot. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordAppend
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ν : List I) (i : I)

/-- The literal total map of the selected word-append isomorphism. -/
def appendLinear (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (append D Sc cutoff i)
      (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L)).toFunctor w →ₗ[k]
      BalancedInduction.Obj (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
        (liftedPowerRegular D cutoff L).toFunctor w :=
  (powerWordAppendIso D Sc cutoff L ν i).hom.total w

private theorem functorEq_tensor {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J K : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K] (h : J = K)
    (R : Superfunctor k C (SVec k)) (v : C) (w : B) (g : J.obj v ⟶ w) (m : R.obj v) :
    ((BalancedInduction.inductionFunctorIsoOfEq J K h).hom.app R).total w
      (BalancedInduction.tensor J R.toFunctor v g m) =
      BalancedInduction.tensor K R.toFunctor v
        (eqToHom (congrArg (fun F : C ⥤ B => F.obj v) h).symm ≫ g) m := by
  subst K
  simp only [BalancedInduction.inductionFunctorIsoOfEq, Iso.refl_hom, NatTrans.id_app,
    SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one,
    add_zero, eqToHom_refl, Category.id_comp]
  rfl

private theorem comparison_tensor {C B A : Type u}
    [Category.{u} C] [Category.{u} B] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ B) (K : B ⥤ A) (P : C ⥤ A)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    [P.Additive] [P.Linear k] [IsSuperfunctor k P] (he : J ⋙ K = P)
    (R : Superfunctor k C (SVec k)) (v : C) (s : B) (w : A)
    (g : K.obj s ⟶ w) (h : J.obj v ⟶ s) (a : R.obj v) :
    (((BalancedInduction.inductionComp J K).app R ≪≫
      (BalancedInduction.inductionFunctorIsoOfEq _ _ he).app R).hom.total w)
        (BalancedInduction.tensor K (BalancedInduction.induced J R).toFunctor s g
          (BalancedInduction.tensor J R.toFunctor v h a)) =
      BalancedInduction.tensor P R.toFunctor v
        (eqToHom (congrArg (fun F : C ⥤ A => F.obj v) he).symm ≫ (K.map h ≫ g)) a := by
  rw [Iso.trans_hom, Superfunctor.comp_total]
  change (((BalancedInduction.inductionFunctorIsoOfEq _ _ he).hom.app R).total w)
    ((((BalancedInduction.inductionComp J K).hom.app R).total w)
      (BalancedInduction.tensor K (BalancedInduction.induced J R).toFunctor s g
        (BalancedInduction.tensor J R.toFunctor v h a))) = _
  have hc : (((BalancedInduction.inductionComp J K).hom.app R).total w) =
      (((BalancedInduction.inductionComp J K).hom.app R).app 0 w) := by
    rw [SuperNatTrans.total, BalancedInduction.inductionComp_hom_app_one, add_zero]
  rw [hc, BalancedInduction.inductionComp_hom_tensor, functorEq_tensor]

/-- The selected comparison on every nested vector, including arbitrary
full regular-power coefficient classes. -/
theorem appendLinear_tensor (s w : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ w)
    (h : (OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ s)
    (a : CoefficientPowerQuotient (k := k) D cutoff L) :
    appendLinear D Sc cutoff L ν i w
      (BalancedInduction.tensor (append D Sc cutoff i)
        (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L)).toFunctor s g
        (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff ν)
          (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) h a)) =
      BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
        (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff)
        ((append D Sc cutoff i).map h ≫ g) a := by
  have hh := comparison_tensor (powerWordCoefficientSource D Sc cutoff ν)
    (append D Sc cutoff i) (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
    (powerWordCoefficientSource_append D Sc cutoff ν i) (liftedPowerRegular D cutoff L)
    (powerCoefficientStar D cutoff) s w g h a
  have he : eqToHom (congrArg (fun F : PowerCoefficientCategory (k := k) D cutoff ⥤
      OldCategory D Sc cutoff => F.obj (powerCoefficientStar D cutoff))
        (powerWordCoefficientSource_append D Sc cutoff ν i)).symm =
      (𝟙 (OldCategory.mk (ν ++ [i]) : OldCategory D Sc cutoff)) := rfl
  erw [he, Category.id_comp] at hh
  unfold appendLinear powerWordAppendIso powerWordModule
  exact hh

private theorem transform_component_tensor {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J K : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {p : ZMod 2} {α : ∀ z, J.obj z ⟶ K.obj z} (hα : IsSupernatural k p α)
    (R : Superfunctor k C (SVec k)) (z : C) (w : B) (h : K.obj z ⟶ w) (m : R.obj z) :
    (BalancedInduction.transformComponent hα R).app p w
      (BalancedInduction.tensor K R.toFunctor z h m) =
      BalancedInduction.tensor J R.toFunctor z (α z ≫ twist k p h) m := by
  rw [BalancedInduction.transformComponent_apply, ite_eq_left rfl,
    BalancedInduction.transformLinear_tensor]
private theorem native_tensor {p : ZMod 2}
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s)
    (hg : g ∈ parity (R := k) _ _ p) (w : OldCategory D Sc cutoff)
    (h : (OldCategory.mk s : OldCategory D Sc cutoff) ⟶ w)
    (a : CoefficientPowerQuotient (k := k) D cutoff L) :
    (PowerWordMorphisms.fromArrow D Sc cutoff L s t g).app p w
      (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff s)
        (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) h a) =
    BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff t)
      (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff)
      (g ≫ twist k p h) a := by
  have he := PowerWordMorphisms.fromArrow_eq_transform D Sc cutoff L s t g hg
  have hx := congrArg (fun f : powerWordModule D Sc cutoff L s ⟶ powerWordModule D Sc cutoff L t =>
    f.app p w (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff s)
      (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) h a)) he
  exact hx.trans (transform_component_tensor _ _
    (PowerWordMorphisms.coefficientSourceNatural D Sc cutoff s t g hg)
      (liftedPowerRegular D cutoff L) (powerCoefficientStar D cutoff) w h a)
/-- Native dot on the actual next-word module, using the literal old dot. -/
def nativeDot : BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
      (liftedPowerRegular D cutoff L) ⟶
    BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
      (liftedPowerRegular D cutoff L) :=
  PowerWordMorphisms.fromArrow D Sc cutoff L (ν ++ [i]) (ν ++ [i])
    (oldAppendDotComponent D Sc cutoff i (OldCategory.mk ν))

/-- The selected append comparison intertwines the actual chosen induction
dot with the native Hom dot, on every nested full-coefficient vector. -/
theorem appendLinear_dot_tensor (s w : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ w)
    (h : (OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ s)
    (a : CoefficientPowerQuotient (k := k) D cutoff L) :
    appendLinear D Sc cutoff L ν i w
      (inductionDot D Sc cutoff i (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L)) w
        (BalancedInduction.tensor (append D Sc cutoff i)
          (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L)).toFunctor s g
          (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff ν)
            (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) h a))) =
    (nativeDot D Sc cutoff L ν i).app (D.parity i) w
      (appendLinear D Sc cutoff L ν i w
        (BalancedInduction.tensor (append D Sc cutoff i)
          (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L)).toFunctor s g
          (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff ν)
            (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) h a))) := by
  rw [inductionDot_tensor, appendLinear_tensor, appendLinear_tensor]
  unfold nativeDot
  erw [native_tensor D Sc cutoff L (s := ν ++ [i]) (t := ν ++ [i])
    (oldAppendDotComponent D Sc cutoff i (OldCategory.mk ν))
    ((oldAppendDot_supernatural D Sc cutoff i).mem (OldCategory.mk ν))]
  change BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
    (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff)
      ((append D Sc cutoff i).map h ≫
        (oldAppendDotComponent D Sc cutoff i s ≫ twist k (D.parity i) g)) a =
    BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
      (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff)
      (oldAppendDotComponent D Sc cutoff i (OldCategory.mk ν) ≫
        twist k (D.parity i) ((append D Sc cutoff i).map h ≫ g)) a
  rw [twist_comp, ← map_twist, ← Category.assoc,
    (oldAppendDot_supernatural D Sc cutoff i).naturality_twist h, Category.assoc]

/-- The dot square is an equality of linear maps on the entire actual
induced word module, not only on its cyclic unit. -/
theorem appendLinear_dot (w : OldCategory D Sc cutoff) :
    appendLinear D Sc cutoff L ν i w ∘ₗ
      inductionDot D Sc cutoff i (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L)) w =
    (nativeDot D Sc cutoff L ν i).app (D.parity i) w ∘ₗ
      appendLinear D Sc cutoff L ν i w := by
  apply BalancedInduction.nested_hom_ext (powerWordCoefficientSource D Sc cutoff ν)
    (append D Sc cutoff i) (liftedPowerRegular D cutoff L) w
  intro z s g h a
  obtain rfl : z = powerCoefficientStar D cutoff := by
    rcases z with ⟨z⟩
    cases z
    rfl
  exact appendLinear_dot_tensor D Sc cutoff L ν i s w g h a

end OddMath.QuiverHecke.ELVOld.PowerWordAppend

