import OddMath.QuiverHecke.HalfTurn.ContextualOldGenerators

/-! # Source classes after the actual contextual old layer maps

SwappedVacuumCoordinates §§5–7: construct the physical old dot/crossing
operator, with both append contexts, and attach it to the exact source
quotient coordinates. The source-class square is proved for every affine
generator shape, every observation source word, and every actual vector.
No abstract action-comparison or faithfulness hypothesis is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.PowerWordLayerClasses
open ELVOld ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- Original source word of a layer whose reservoir append contexts are `ν,η`. -/
abbrev domWord (ν η : List I) (g : Shape I) := η.reverse ++ g.dom ++ ν.reverse
/-- Original target word of that layer. -/
abbrev codWord (ν η : List I) (g : Shape I) := η.reverse ++ g.cod ++ ν.reverse

/-- The actual contextual old generator: the old append dot or normalized
physical crossing, followed by the given append functors. -/
def oldLayer (ν η : List I) : (g : Shape I) →
    ((OldCategory.mk (codWord ν η g).reverse : OldCategory D (parameterTwist D Sc) cutoff) ⟶
      OldCategory.mk (domWord ν η g).reverse)
  | .dot i => ContextualOldGenerators.transport D (parameterTwist D Sc) cutoff
      (by simp [PowerWordContexts.extendedWord_eq, List.reverse_append, List.append_assoc, Shape.cod])
      (by simp [PowerWordContexts.extendedWord_eq, List.reverse_append, List.append_assoc, Shape.dom])
      (PowerWordContexts.extendedArrow D (parameterTwist D Sc) cutoff (ν ++ [i]) (ν ++ [i]) η
        (oldAppendDotComponent D (parameterTwist D Sc) cutoff i (OldCategory.mk ν)))
  | .cross i j => ContextualOldGenerators.transport D (parameterTwist D Sc) cutoff
      (by simp [PowerWordContexts.extendedWord_eq, List.reverse_append, List.append_assoc, Shape.cod])
      (by simp [PowerWordContexts.extendedWord_eq, List.reverse_append, List.append_assoc, Shape.dom])
      (PowerWordContexts.extendedArrow D (parameterTwist D Sc) cutoff ((ν ++ [j]) ++ [i]) ((ν ++ [i]) ++ [j]) η
        (PowerWordContentCross.normalizedOldCross D (parameterTwist D Sc) cutoff ν i j))

/-- The physical old generator has its original source half-turn image.
This equality is proved from the contextual generator table. -/
theorem oldLayer_eq (ν η : List I) (g : Shape I) :
    oldLayer D Sc cutoff ν η g = halfTurnOldHom D Sc cutoff (domWord ν η g) (codWord ν η g)
      (sourceCoefficientHom D Sc 1 (ContextualOldGenerators.layerDiagram D Sc η.reverse g ν.reverse)) := by
  cases g with
  | dot i => exact (ContextualOldGenerators.dot D Sc cutoff ν η i).symm
  | cross i j => exact (ContextualOldGenerators.cross D Sc cutoff ν η i j).symm

/-- The actual full-coefficient word-module map of the physical old layer. -/
def layerMap (ν η : List I) (g : Shape I) :
    powerWordModule D (parameterTwist D Sc) cutoff L (domWord ν η g).reverse ⟶
      powerWordModule D (parameterTwist D Sc) cutoff L (codWord ν η g).reverse :=
  PowerWordMorphisms.fromArrow D (parameterTwist D Sc) cutoff L
    (domWord ν η g).reverse (codWord ν η g).reverse (oldLayer D Sc cutoff ν η g)

/-- The physical layer map is the existing actual sourceMap, retaining all
parity components and coefficients, rather than an action defined by coordinates. -/
theorem layerMap_eq (ν η : List I) (g : Shape I) :
    layerMap D Sc cutoff L ν η g =
      PowerWordComposition.sourceMap D Sc cutoff L (domWord ν η g) (codWord ν η g)
        (sourceCoefficientHom D Sc 1 (ContextualOldGenerators.layerDiagram D Sc η.reverse g ν.reverse)) := by
  rw [layerMap, oldLayer_eq, PowerWordComposition.sourceMap_apply]

/-- The concrete quotient-class square of every affine generator layer
with both contexts, for an arbitrary observation source word and vector.
The only premise specifies that vector's input quotient class. -/
theorem class_square (s ν η : List I) (g : Shape I)
    (v : (powerWordModule D (parameterTwist D Sc) cutoff L (domWord ν η g).reverse).obj
      (OldCategory.mk s.reverse))
    (y : coefficientObj D Sc s ⟶ coefficientObj D Sc (domWord ν η g))
    (hy : PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (domWord ν η g) v =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s (domWord ν η g)).mkQ y) :
    PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (codWord ν η g)
      ((layerMap D Sc cutoff L ν η g).total (OldCategory.mk s.reverse) v) =
    (PowerWordQuotientCoordinates.kernel D Sc cutoff L s (codWord ν η g)).mkQ
      (y ≫ sourceCoefficientHom D Sc 1 (ContextualOldGenerators.layerDiagram D Sc η.reverse g ν.reverse)) := by
  rw [layerMap_eq]
  exact PowerWordQuotientCoordinates.coordinate_action D Sc cutoff L _ _ _ hy

private theorem boundary_dom (A : Layer (QuiverHecke.sig D)) : A.dom = ob D A.dom.word :=
  Obj.ext (Subsingleton.elim _ _) rfl
private theorem boundary_cod (A : Layer (QuiverHecke.sig D)) : A.cod = ob D A.cod.word :=
  Obj.ext (Subsingleton.elim _ _) rfl

/-- The actual affine presentation layer, with only its unique region
and the two word-object endpoint equalities transported. -/
def affineLayer (A : Layer (QuiverHecke.sig D)) (hA : A.Valid) :
    (pres D Sc).obj (ob D A.dom.word) ⟶ (pres D Sc).obj (ob D A.cod.word) :=
  (pres D Sc).diag (Diagram.cast (Diagram.ofLayer A hA) (boundary_dom D A) (boundary_cod D A))

/-- The literal presentation image of a layer is its given contextual
generator; no replacement layer interpretation is introduced. -/
theorem affineLayer_eq (A : Layer (QuiverHecke.sig D)) (hA : A.Valid) :
    affineLayer D Sc A hA = ContextualOldGenerators.layerDiagram D Sc A.left A.gen A.right := by
  apply Presentation.diag_eq_of_layers_eq
  rcases A with ⟨start,u,g,v⟩
  cases start
  rfl

/-- The physical map of an actual affine layer, transporting only the
double reversal equalities of its two word boundaries. -/
private def reindexMap {s t s' t' : List I} (hs : s = s') (ht : t = t')
    (f : powerWordModule D (parameterTwist D Sc) cutoff L s.reverse ⟶
      powerWordModule D (parameterTwist D Sc) cutoff L t.reverse) :
    powerWordModule D (parameterTwist D Sc) cutoff L s'.reverse ⟶
      powerWordModule D (parameterTwist D Sc) cutoff L t'.reverse := by
  subst s'
  subst t'
  exact f

private theorem reindexMap_source {s t s' t' : List I} (hs : s = s') (ht : t = t')
    (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t))
    (f' : (pres D Sc).obj (ob D s') ⟶ (pres D Sc).obj (ob D t')) (hf : HEq f f') :
    reindexMap D Sc cutoff L hs ht (PowerWordComposition.sourceMap D Sc cutoff L s t
      (sourceCoefficientHom D Sc 1 f)) =
      PowerWordComposition.sourceMap D Sc cutoff L s' t' (sourceCoefficientHom D Sc 1 f') := by
  subst s'
  subst t'
  have he : f = f' := eq_of_heq hf
  subst f'
  rfl

private theorem context_diagram_heq {u u' v v' : List I} (hu : u = u') (hv : v = v') (g : Shape I) :
    HEq (ContextualOldGenerators.layerDiagram D Sc u g v)
      (ContextualOldGenerators.layerDiagram D Sc u' g v') := by
  subst u'
  subst v'
  rfl

private theorem dom_word_eq (A : Layer (QuiverHecke.sig D)) :
    domWord A.right.reverse A.left.reverse A.gen = A.dom.word := by
  simp only [domWord, List.reverse_reverse, Layer.dom_word, QuiverHecke.sig]
private theorem cod_word_eq (A : Layer (QuiverHecke.sig D)) :
    codWord A.right.reverse A.left.reverse A.gen = A.cod.word := by
  simp only [codWord, List.reverse_reverse, Layer.cod_word, QuiverHecke.sig]

/-- The physical map of an actual affine layer, with the canonical
double-reversal word equalities transported explicitly. -/
def literalLayerMap (A : Layer (QuiverHecke.sig D)) :
    powerWordModule D (parameterTwist D Sc) cutoff L A.dom.word.reverse ⟶
      powerWordModule D (parameterTwist D Sc) cutoff L A.cod.word.reverse :=
  reindexMap D Sc cutoff L (dom_word_eq D A) (cod_word_eq D A)
    (layerMap D Sc cutoff L A.right.reverse A.left.reverse A.gen)

/-- The actual presentation layer and the physical old generator give the
same full module map, with no separately supplied generator square. -/
theorem literalLayerMap_eq (A : Layer (QuiverHecke.sig D)) (hA : A.Valid) :
    literalLayerMap D Sc cutoff L A =
      PowerWordComposition.sourceMap D Sc cutoff L A.dom.word A.cod.word
        (sourceCoefficientHom D Sc 1 (affineLayer D Sc A hA)) := by
  unfold literalLayerMap
  rw [layerMap_eq]
  apply reindexMap_source
  exact (context_diagram_heq D Sc (List.reverse_reverse A.left) (List.reverse_reverse A.right) A.gen).trans
    (heq_of_eq (affineLayer_eq D Sc A hA).symm)

/-- The literal affine-layer quotient square on every actual word vector,
for any observation source word. The input-class equality is the only premise. -/
theorem affine_class_square (A : Layer (QuiverHecke.sig D)) (hA : A.Valid) (s : List I)
    (v : (powerWordModule D (parameterTwist D Sc) cutoff L A.dom.word.reverse).obj (OldCategory.mk s.reverse))
    (y : coefficientObj D Sc s ⟶ coefficientObj D Sc A.dom.word)
    (hy : PowerWordQuotientCoordinates.coordinate D Sc cutoff L s A.dom.word v =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s A.dom.word).mkQ y) :
    PowerWordQuotientCoordinates.coordinate D Sc cutoff L s A.cod.word
      ((literalLayerMap D Sc cutoff L A).total (OldCategory.mk s.reverse) v) =
    (PowerWordQuotientCoordinates.kernel D Sc cutoff L s A.cod.word).mkQ
      (y ≫ sourceCoefficientHom D Sc 1 (affineLayer D Sc A hA)) := by
  rw [literalLayerMap_eq D Sc cutoff L A hA]
  exact PowerWordQuotientCoordinates.coordinate_action D Sc cutoff L _ _ _ hy

end OddMath.QuiverHecke.PowerWordLayerClasses
