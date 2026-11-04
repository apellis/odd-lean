import OddMath.SKM.PairingExtensionPresentation
import OddMath.QuiverHecke.Alpha

/-! # Affine diagrams and upward labelling in the pairing extension

Brundan–Ellis §11, equation (11.7), and `SwappedVacuumCoordinates.md` §7.
The pairing extension retains the entire affine diagram and every scalar
parameter. Its SKM presentation map commutes with upward weight labelling.
-/
noncomputable section
namespace OddMath.QuiverHecke.PairingExtension
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)
local notation "Dₑ" => ReservoirWeights.pairingExtension D
local notation "Scₑ" => ReservoirWeights.pairingExtensionScalars D Sc

/-- The affine signature is unchanged, including the odd generators. -/
def inclusion : SigMap (sig D) (sig Dₑ) := SigMap.id (sig D)

theorem inclusion_map {a b : Obj (sig D)} (f : a ⟶ b) :
    (inclusion D).toLayerMap.map f = f := by
  apply Diagram.ext
  simp only [LayerMap.layers_map]
  have h : (inclusion D).layer = id := by funext L; cases L; rfl
  change List.map (inclusion D).layer (Diagram.layers f) = Diagram.layers f
  rw [h, List.map_id]

theorem inclusion_lin {a b : Obj (sig D)} (f : LinDiagram k a b) :
    (inclusion D).toLayerMap.lin f = f := by
  simp only [LayerMap.lin, inclusion_map]
  exact Finsupp.mapDomain_id

/-- The same affine relation label, with the unchanged Cartan entry. -/
def relationLabel : Rel D → Rel Dₑ
  | .quadEq i => .quadEq i
  | .quadZero i j hij hd => .quadZero i j hij (by simpa using hd)
  | .quadNe i j hij hd => .quadNe i j hij (by simpa using hd)
  | .slideL i j hij => .slideL i j hij
  | .slideLEq i => .slideLEq i
  | .slideR i j hij => .slideR i j hij
  | .slideREq i => .slideREq i
  | .braid i j l h => .braid i j l h
  | .braidEq i j hij => .braidEq i j hij

@[simp] theorem relationLabel_dom (r : Rel D) : (relationLabel D r).dom = r.dom := by
  cases r <;> rfl
@[simp] theorem relationLabel_cod (r : Rel D) : (relationLabel D r).cod = r.cod := by
  cases r <;> rfl

theorem relation_heq (r : Rel D) : HEq (relation D Sc r) (relation Dₑ Scₑ (relationLabel D r)) := by
  cases r <;> apply heq_of_eq <;>
    simp [relation, relationLabel, ReservoirWeights.pairingExtensionScalars,
      ReservoirWeights.pairingExtension_dn, ReservoirWeights.pairingExtension_parity] <;> rfl

private theorem lin_eq_zero_of_heq {a b a' b' : Obj (sig D)}
    (ha : a = a') (hb : b = b') (f : LinDiagram k a b) (g : LinDiagram k a' b')
    (h : HEq f g) (hg : (pres Dₑ Scₑ).lin g = 0) : (pres Dₑ Scₑ).lin f = 0 := by
  subst ha hb
  cases h
  exact hg

theorem inclusion_relation (r : Rel D) :
    (freeLift k ((inclusion D).toLayerMap.toPresented (pres Dₑ Scₑ) (fun _ => 1))).map
      ((pres D Sc).rel r) = 0 := by
  rw [LayerMap.freeLift_toPresented_one, inclusion_lin]
  have hz : (pres Dₑ Scₑ).lin (relation Dₑ Scₑ (relationLabel D r)) = 0 :=
    (pres Dₑ Scₑ).lin_rel_self (relationLabel D r)
  exact lin_eq_zero_of_heq D Sc (by simp only [relationLabel_dom]; rfl)
    (by simp only [relationLabel_cod]; rfl) _ _ (relation_heq D Sc r) hz

/-- The affine presentation map is identity on raw dots and crossings. -/
def presentationFunctor : (pres D Sc).Presented ⥤ (pres Dₑ Scₑ).Presented :=
  (inclusion D).lift (pres D Sc) (fun _ => rfl) (inclusion_relation D Sc)

instance presentationFunctor_additive : (presentationFunctor D Sc).Additive := by
  unfold presentationFunctor
  infer_instance
instance presentationFunctor_linear : (presentationFunctor D Sc).Linear k := by
  unfold presentationFunctor
  infer_instance

theorem presentationFunctor_diag {a b : Obj (sig D)} (f : a ⟶ b) :
    (presentationFunctor D Sc).map ((pres D Sc).diag f) = (pres Dₑ Scₑ).diag f := by
  simp only [presentationFunctor, SigMap.lift_diag, Diagram.weight_one, one_smul, inclusion_map]

theorem labelled_diagram (μ : X) {s t : List I} (f : ob D s ⟶ ob D t) :
    SKM.PairingExtension.diagram D ((label D μ).map f) = (label Dₑ (μ, 0)).map f := by
  apply Diagram.ext
  simp only [SKM.PairingExtension.diagram, Diagram.layers_cast, LayerMap.layers_map, List.map_map]
  apply List.map_congr_left
  intro L _
  exact SKM.PairingExtension.inclusion_lay D μ (upWord L.left) L.gen.toSKM (upWord L.right)

/-- The original upward functor followed by region inclusion is extended upward labelling. -/
theorem alpha_map (μ : X) {s t : List I}
    (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)) :
    SKM.PairingExtension.homMap D Sc μ (upWord s) (upWord t) ((alpha D Sc μ).map f) =
      (alpha Dₑ Scₑ (μ, 0)).map ((presentationFunctor D Sc).map f) := by
  obtain ⟨F, rfl⟩ := (pres D Sc).lin_surjective f
  induction F using Finsupp.induction_linear with
  | zero => simp only [Presentation.lin_zero, Functor.map_zero, map_zero]
  | add f g hf hg =>
    erw [(pres D Sc).lin_add f g, (alpha D Sc μ).map_add,
      (SKM.PairingExtension.homMap D Sc μ (upWord s) (upWord t)).map_add,
      (presentationFunctor D Sc).map_add, (alpha Dₑ Scₑ (μ, 0)).map_add]
    exact congrArg₂ (fun x y => x + y) hf hg
  | single f r =>
    simp only [Presentation.lin_single, Functor.map_smul, map_smul, alpha_diag,
      SKM.PairingExtension.homMap_diag, presentationFunctor_diag, labelled_diagram]

end OddMath.QuiverHecke.PairingExtension
