import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendParity
import OddMath.QuiverHecke.CyclotomicAction.ELVOldMateTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionAssociativity

/-! The selected twice-appended word comparison and the actual signed
same-colour crossing, retaining all regular-power coefficient vectors. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordPair
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ν : List I) (i : I)

private theorem functorEq_even {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J K : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K] (h : J = K)
    (R : Superfunctor k C (SVec k)) :
    ((BalancedInduction.inductionFunctorIsoOfEq J K h).hom.app R) ∈ parity (R := k) _ _ 0 := by
  subst K
  exact id_mem _

/-- The same selected isomorphism, with its actual raw coend endpoints fixed. -/
def selectedAppendIso :
    BalancedInduction.induced (append D Sc cutoff i)
      (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L)) ≅
    BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
      (liftedPowerRegular D cutoff L) := powerWordAppendIso D Sc cutoff L ν i

private theorem comparison_even {C B A : Type u}
    [Category.{u} C] [Category.{u} B] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ B) (K : B ⥤ A) (P : C ⥤ A)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    [P.Additive] [P.Linear k] [IsSuperfunctor k P] (he : J ⋙ K = P)
    (R : Superfunctor k C (SVec k)) :
    ((BalancedInduction.inductionComp J K).app R ≪≫
      (BalancedInduction.inductionFunctorIsoOfEq _ _ he).app R).hom ∈ parity (R := k) _ _ 0 :=
  comp_mem (BalancedInduction.inductionComp_hom_mem _ _ _) (functorEq_even _ _ _ _)

/-- Both selected word comparisons are even. -/
theorem appendIso_even : (selectedAppendIso D Sc cutoff L ν i).hom ∈ parity (R := k) _ _ 0 := by
  unfold selectedAppendIso powerWordAppendIso powerWordModule
  exact comparison_even _ _ _ _ _

private theorem total_zero {C : Type u} [Category.{u} C] [Preadditive C]
    [Linear k C] [Supercategory k C] {P Q : Superfunctor k C (SVec k)}
    (f : P ⟶ Q) (hf : f ∈ parity (R := k) _ _ 0) (w : C) : f.total w = f.app 0 w := by
  rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem (q := 1) hf (by decide), add_zero]

/-- Iterate exactly the selected single-word comparison, using the actual
induction map on its even homogeneous component. -/
def pairLinear (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (append D Sc cutoff i)
      (BalancedInduction.induced (append D Sc cutoff i)
        (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
          (liftedPowerRegular D cutoff L))).toFunctor w →ₗ[k]
    BalancedInduction.Obj (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))
      (liftedPowerRegular D cutoff L).toFunctor w :=
  PowerWordAppend.appendLinear D Sc cutoff L (ν ++ [i]) i w ∘ₗ
    BalancedInduction.mapComponent (append D Sc cutoff i)
      (selectedAppendIso D Sc cutoff L ν i).hom 0 w

private theorem selected_total (w : OldCategory D Sc cutoff) :
    (selectedAppendIso D Sc cutoff L ν i).hom.total w =
      PowerWordAppend.appendLinear D Sc cutoff L ν i w := rfl

private theorem induced_even_tensor {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (P Q : Superfunctor k C (SVec k)) (e : P ⟶ Q) (he : e ∈ parity (R := k) _ _ 0)
    (v : C) (w : B) (g : J.obj v ⟶ w) (x : P.obj v) :
    BalancedInduction.mapComponent J e 0 w (BalancedInduction.tensor J P.toFunctor v g x) =
      BalancedInduction.tensor J Q.toFunctor v g (e.total v x) := by
  rw [BalancedInduction.mapComponent_tensor, twist_zero, total_zero e he]

private theorem selected_component_tensor (r s : OldCategory D Sc cutoff)
    (h : (append D Sc cutoff i).obj r ⟶ s)
    (f : (OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ r)
    (a : CoefficientPowerQuotient (k := k) D cutoff L) :
    (selectedAppendIso D Sc cutoff L ν i).hom.app 0 s
      (BalancedInduction.tensor (append D Sc cutoff i)
        (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
          (liftedPowerRegular D cutoff L)).toFunctor r h
        (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff ν)
          (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) f a)) =
      BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
        (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff)
        ((append D Sc cutoff i).map f ≫ h) a := by
  have he := total_zero (selectedAppendIso D Sc cutoff L ν i).hom
    (appendIso_even D Sc cutoff L ν i) s
  have ht := congrArg (fun m => m (BalancedInduction.tensor (append D Sc cutoff i)
      (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L)).toFunctor r h
      (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) f a))) he.symm
  exact ht.trans (PowerWordAppend.appendLinear_tensor D Sc cutoff L ν i r s h f a)

/-- The selected recursive comparison on every triple coend tensor. -/
private theorem pairLinear_first_tensor (r s w : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ w)
    (h : (append D Sc cutoff i).obj r ⟶ s)
    (f : (OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ r)
    (a : CoefficientPowerQuotient (k := k) D cutoff L) :
    pairLinear D Sc cutoff L ν i w
      (BalancedInduction.tensor (append D Sc cutoff i)
        (BalancedInduction.induced (append D Sc cutoff i)
          (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
            (liftedPowerRegular D cutoff L))).toFunctor s g
        (BalancedInduction.tensor (append D Sc cutoff i)
          (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
            (liftedPowerRegular D cutoff L)).toFunctor r h
          (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff ν)
            (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) f a))) =
      PowerWordAppend.appendLinear D Sc cutoff L (ν ++ [i]) i w
        (BalancedInduction.tensor (append D Sc cutoff i)
          (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
            (liftedPowerRegular D cutoff L)).toFunctor s g
          (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
            (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff)
            ((append D Sc cutoff i).map f ≫ h) a)) := by
  unfold pairLinear
  rw [LinearMap.comp_apply, BalancedInduction.mapComponent_tensor, twist_zero,
    selected_component_tensor]

/-- The selected recursive comparison on every triple coend tensor. -/
theorem pairLinear_tensor (r s w : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ w)
    (h : (append D Sc cutoff i).obj r ⟶ s)
    (f : (OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ r)
    (a : CoefficientPowerQuotient (k := k) D cutoff L) :
    pairLinear D Sc cutoff L ν i w
      (BalancedInduction.tensor (append D Sc cutoff i)
        (BalancedInduction.induced (append D Sc cutoff i)
          (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
            (liftedPowerRegular D cutoff L))).toFunctor s g
        (BalancedInduction.tensor (append D Sc cutoff i)
          (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
            (liftedPowerRegular D cutoff L)).toFunctor r h
          (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff ν)
            (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) f a))) =
      BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))
        (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff)
        ((append D Sc cutoff i).map ((append D Sc cutoff i).map f ≫ h) ≫ g) a := by
  let b : (OldCategory.mk (ν ++ [i]) : OldCategory D Sc cutoff) ⟶ s :=
    (append D Sc cutoff i).map f ≫ h
  have hfirst := pairLinear_first_tensor D Sc cutoff L ν i r s w g h f a
  have hlast := PowerWordAppend.appendLinear_tensor D Sc cutoff L (ν ++ [i]) i s w g b a
  exact hfirst.trans hlast



private theorem native_tensor {s t : List I} {p : ZMod 2}
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
  obtain ⟨b, rfl⟩ := RingCon.mkₐ_surjective (α := k)
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon a
  rw [PowerWordMorphisms.fromArrow_tensor, proj_of_mem hg, PowerWordYoneda.tensor_eq_generator]
  have hn := (PowerWordMorphisms.coefficientSourceNatural D Sc cutoff s t g hg).naturality_twist
    (show powerCoefficientStar D cutoff ⟶ powerCoefficientStar D cutoff from b)
  rw [map_twist] at hn
  change coefficientEndomorphism D Sc cutoff t b ≫ g =
    g ≫ twist k p (coefficientEndomorphism D Sc cutoff s b) at hn
  rw [twist_comp, ← Category.assoc, ← hn, Category.assoc]


/-- The native equal-colour crossing has the same prescribed extra minus. -/
def nativeCrossLinear (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))
      (liftedPowerRegular D cutoff L).toFunctor w →ₗ[k]
    BalancedInduction.Obj (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))
      (liftedPowerRegular D cutoff L).toFunctor w :=
  -(PowerWordMorphisms.fromArrow D Sc cutoff L (ν ++ [i] ++ [i]) (ν ++ [i] ++ [i])
    (equalCrossComponent D Sc cutoff i (OldCategory.mk ν))).app (D.parity i * D.parity i) w

/-- The actual signed crossing is preserved by the recursively selected
word comparisons on every triple tensor and every coefficient vector. -/
theorem pairLinear_cross_tensor (r s w : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ w)
    (h : (append D Sc cutoff i).obj r ⟶ s)
    (f : (OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ r)
    (a : CoefficientPowerQuotient (k := k) D cutoff L) :
    pairLinear D Sc cutoff L ν i w
      (((signedEqualInductionCross D Sc cutoff i).app (D.parity i * D.parity i)
        (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
          (liftedPowerRegular D cutoff L))).total w
        (BalancedInduction.tensor (append D Sc cutoff i)
          (BalancedInduction.induced (append D Sc cutoff i)
            (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
              (liftedPowerRegular D cutoff L))).toFunctor s g
          (BalancedInduction.tensor (append D Sc cutoff i)
            (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
              (liftedPowerRegular D cutoff L)).toFunctor r h
            (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff ν)
              (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) f a)))) =
    nativeCrossLinear D Sc cutoff L ν i w
      (pairLinear D Sc cutoff L ν i w
        (BalancedInduction.tensor (append D Sc cutoff i)
          (BalancedInduction.induced (append D Sc cutoff i)
            (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
              (liftedPowerRegular D cutoff L))).toFunctor s g
          (BalancedInduction.tensor (append D Sc cutoff i)
            (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
              (liftedPowerRegular D cutoff L)).toFunctor r h
            (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff ν)
              (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) f a)))) := by
  rw [signedEqualInductionCross_total_tensor, map_neg, pairLinear_tensor, pairLinear_tensor]
  unfold nativeCrossLinear
  erw [LinearMap.neg_apply]
  erw [native_tensor D Sc cutoff L
    (equalCrossComponent D Sc cutoff i (OldCategory.mk ν))
    ((equalCross_supernatural D Sc cutoff i).mem (OldCategory.mk ν))]
  apply congrArg Neg.neg
  have hn := (equalCross_supernatural D Sc cutoff i).naturality_twist f
  rw [map_twist] at hn
  have hh := congrArg (fun b => b ≫ twist k (D.parity i * D.parity i)
    ((append D Sc cutoff i).map h ≫ g)) hn
  change ((append D Sc cutoff i).map ((append D Sc cutoff i).map f) ≫
      equalCrossComponent D Sc cutoff i r) ≫
      twist k (D.parity i * D.parity i) ((append D Sc cutoff i).map h ≫ g) =
    (equalCrossComponent D Sc cutoff i (OldCategory.mk ν) ≫
      twist k (D.parity i * D.parity i) ((append D Sc cutoff i).map ((append D Sc cutoff i).map f))) ≫
      twist k (D.parity i * D.parity i) ((append D Sc cutoff i).map h ≫ g) at hh
  have he :
      (append D Sc cutoff i).map ((append D Sc cutoff i).map f ≫ 𝟙 _) ≫
        (equalCrossComponent D Sc cutoff i r ≫
          twist k (D.parity i * D.parity i) ((append D Sc cutoff i).map h ≫ g)) =
      equalCrossComponent D Sc cutoff i (OldCategory.mk ν) ≫
        twist k (D.parity i * D.parity i)
          ((append D Sc cutoff i).map ((append D Sc cutoff i).map f ≫ h) ≫ g) := by
    simpa only [Functor.map_comp, Functor.map_id, Category.comp_id, Category.assoc,
      twist_comp] using hh
  exact congrArg (fun b => BalancedInduction.tensor
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))
    (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) b a) he


/-- Equality of linear maps on the entire actual twice-induced word module.
The signed crossing and the recursively selected comparisons are unchanged. -/
theorem pairLinear_cross (w : OldCategory D Sc cutoff) :
    pairLinear D Sc cutoff L ν i w ∘ₗ
      (((signedEqualInductionCross D Sc cutoff i).app (D.parity i * D.parity i)
        (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
          (liftedPowerRegular D cutoff L))).total w) =
    nativeCrossLinear D Sc cutoff L ν i w ∘ₗ pairLinear D Sc cutoff L ν i w := by
  apply BalancedInduction.triple_hom_ext (powerWordCoefficientSource D Sc cutoff ν)
    (append D Sc cutoff i) (append D Sc cutoff i) (liftedPowerRegular D cutoff L) w
  intro z r s g h f a
  obtain rfl : z = powerCoefficientStar D cutoff := by
    rcases z with ⟨z⟩
    cases z
    rfl
  exact pairLinear_cross_tensor D Sc cutoff L ν i r s w g h f a

end OddMath.QuiverHecke.ELVOld.PowerWordPair
