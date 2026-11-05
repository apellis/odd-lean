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

end OddMath.QuiverHecke.PowerWordLayerClasses
