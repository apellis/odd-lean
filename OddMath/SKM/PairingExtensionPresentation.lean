import OddMath.SKM.PairingExtensionDiagrams
import StringDiagrams.Transport

/-! # Presentation functor for the original weights in the pairing extension

`SwappedNondegeneracy.md` §2 pulls back the combined Hom action along the
original-region embedding. The defining relations and superinterchange
descend through `SigMap.lift`; no faithfulness assumption is needed.
-/
noncomputable section
namespace OddMath.SKM.PairingExtension
open CategoryTheory StringDiagrams OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
  {k : Type w} [CommRing k] (Sc : Scalars D k)
local notation "Dₑ" => ReservoirWeights.pairingExtension D
local notation "Scₑ" => ReservoirWeights.pairingExtensionScalars D Sc

/-- The normal-form linear map is the signature map followed by its boundary casts. -/
theorem linear_eq_cast (μ : X) (s t : List (Letter I))
    (f : LinDiagram k (ob D μ s) (ob D μ t)) :
    linear D μ s t f = LinDiagram.cast ((inclusion D).toLayerMap.lin f)
      (inclusion_ob D μ s) (inclusion_ob D μ t) := by
  change Finsupp.mapDomain (diagram D) f =
    Finsupp.mapDomain (fun g => Diagram.cast g (inclusion_ob D μ s) (inclusion_ob D μ t))
      (Finsupp.mapDomain (inclusion D).toLayerMap.map f)
  exact Finsupp.mapDomain_comp (v := f) (f := (inclusion D).toLayerMap.map)
    (g := fun g => Diagram.cast g (inclusion_ob D μ s) (inclusion_ob D μ t))

private theorem lin_eq_zero_of_cast {a b a' b' : Obj (sig Dₑ)}
    (f : LinDiagram k a b) (ha : a = a') (hb : b = b')
    (hf : (pres Dₑ Scₑ).lin (LinDiagram.cast f ha hb) = 0) :
    (pres Dₑ Scₑ).lin f = 0 := by
  subst ha hb
  simpa only [LinDiagram.cast_rfl] using hf

private theorem lin_eq_zero_of_heq {a b a' b' : Obj (sig Dₑ)}
    (ha : a = a') (hb : b = b') (f : LinDiagram k a b) (g : LinDiagram k a' b')
    (h : HEq f g) (hg : (pres Dₑ Scₑ).lin g = 0) : (pres Dₑ Scₑ).lin f = 0 := by
  subst ha hb
  cases h
  exact hg

/-- Every transported defining relation vanishes in the target presentation. -/
theorem linear_relation_zero (r : Rel D) :
    (pres Dₑ Scₑ).lin (linear D r.ν r.dom r.cod (relation D Sc r)) = 0 := by
  have hz : (pres Dₑ Scₑ).lin (relation Dₑ Scₑ (relationLabel D r)) = 0 :=
    (pres Dₑ Scₑ).lin_rel_self (relationLabel D r)
  exact lin_eq_zero_of_heq D Sc
    (by simp only [relationLabel_region, relationLabel_dom])
    (by simp only [relationLabel_region, relationLabel_cod])
    _ _ (linear_relation D Sc r) hz

/-- The literal unweighted signature interpretation kills all user relations. -/
theorem inclusion_relation (r : Rel D) :
    (freeLift k ((inclusion D).toLayerMap.toPresented (pres Dₑ Scₑ) (fun _ => 1))).map
      ((pres D Sc).rel r) = 0 := by
  rw [LayerMap.freeLift_toPresented_one]
  apply lin_eq_zero_of_cast D Sc _ (inclusion_ob D r.ν r.dom) (inclusion_ob D r.ν r.cod)
  rw [← linear_eq_cast]
  exact linear_relation_zero D Sc r

/-- The complete SKM presentation functor retaining the original weights. -/
def presentationFunctor : (pres D Sc).Presented ⥤ (pres Dₑ Scₑ).Presented :=
  (inclusion D).lift (pres D Sc) (inclusion_odd D) (inclusion_relation D Sc)

instance presentationFunctor_additive : (presentationFunctor D Sc).Additive := by
  unfold presentationFunctor
  infer_instance

instance presentationFunctor_linear : (presentationFunctor D Sc).Linear k := by
  unfold presentationFunctor
  infer_instance

@[simp] theorem presentationFunctor_obj (a : Obj (sig D)) :
    (presentationFunctor D Sc).obj ((pres D Sc).obj a) =
      (pres Dₑ Scₑ).obj ((inclusion D).obj a) := rfl

/-- All generators, including the inverse entries, retain their diagrams and coefficients. -/
theorem presentationFunctor_diag {a b : Obj (sig D)} (f : a ⟶ b) :
    (presentationFunctor D Sc).map ((pres D Sc).diag f) =
      (pres Dₑ Scₑ).diag ((inclusion D).toLayerMap.map f) := by
  simp only [presentationFunctor, SigMap.lift_diag, Diagram.weight_one, one_smul]

/-- The linear Hom map at fixed original region and unchanged signed boundary words. -/
def homMap (μ : X) (s t : List (Letter I)) :
    ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) →ₗ[k]
      ((pres Dₑ Scₑ).obj (ob Dₑ (μ, 0) s) ⟶ (pres Dₑ Scₑ).obj (ob Dₑ (μ, 0) t)) :=
  ((pres Dₑ Scₑ).castLinearEquiv (inclusion_ob D μ s) (inclusion_ob D μ t)).toLinearMap.comp
    ((presentationFunctor D Sc).mapLinearMap k)

theorem homMap_apply (μ : X) (s t : List (Letter I))
    (f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :
    homMap D Sc μ s t f = (pres Dₑ Scₑ).castHom (inclusion_ob D μ s) (inclusion_ob D μ t)
      ((presentationFunctor D Sc).map f) := rfl

@[simp] theorem homMap_id (μ : X) (s : List (Letter I)) :
    homMap D Sc μ s s (𝟙 _) = 𝟙 _ := by
  exact (congrArg ((pres Dₑ Scₑ).castHom (inclusion_ob D μ s) (inclusion_ob D μ s))
    ((presentationFunctor D Sc).map_id _)).trans ((pres Dₑ Scₑ).castHom_id _)

theorem homMap_comp (μ : X) {s t r : List (Letter I)}
    (f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t))
    (g : (pres D Sc).obj (ob D μ t) ⟶ (pres D Sc).obj (ob D μ r)) :
    homMap D Sc μ s r (f ≫ g) = homMap D Sc μ s t f ≫ homMap D Sc μ t r g := by
  exact (congrArg ((pres Dₑ Scₑ).castHom (inclusion_ob D μ s) (inclusion_ob D μ r))
    ((presentationFunctor D Sc).map_comp f g)).trans
      ((pres Dₑ Scₑ).castHom_comp (inclusion_ob D μ s) (inclusion_ob D μ t)
        (inclusion_ob D μ r) _ _)

@[simp] theorem homMap_diag {μ : X} {s t : List (Letter I)} (f : ob D μ s ⟶ ob D μ t) :
    homMap D Sc μ s t ((pres D Sc).diag f) = (pres Dₑ Scₑ).diag (diagram D f) := by
  rw [homMap_apply, presentationFunctor_diag, Presentation.castHom_diag]
  rfl

end OddMath.SKM.PairingExtension
