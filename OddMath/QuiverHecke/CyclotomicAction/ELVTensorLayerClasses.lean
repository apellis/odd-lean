import OddMath.QuiverHecke.HalfTurn.PowerWordLayerClasses
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorHomContexts

/-! # Source classes of contextual tensor-Hom layer entries

SwappedVacuumCoordinates §§2–7: evaluate the unchanged chosen ELV
tensor-Hom entries at the regular probe, on every vector in the specified
source-content block, and identify their signed original layer quotient
classes. No complete swapped factor or faithfulness premise is needed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.TensorLayerClasses
open CyclotomicAction SwappedAssembly CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private def reindex {s t : List I} (h : s = t) (w : OldCategory D Sc cutoff) :
    (powerWordModule D Sc cutoff L s).obj w →ₗ[k] (powerWordModule D Sc cutoff L t).obj w := by
  subst t
  exact LinearMap.id

private theorem reindex_fromArrow {s t s' t' : List I} (hs : s = s') (ht : t = t')
    (g : (OldCategory.mk t' : OldCategory D Sc cutoff) ⟶ OldCategory.mk s')
    (w : OldCategory D Sc cutoff) (v : (powerWordModule D Sc cutoff L s').obj w) :
    reindex D Sc cutoff L ht.symm w ((PowerWordMorphisms.fromArrow D Sc cutoff L s' t' g).total w v) =
      (PowerWordMorphisms.fromArrow D Sc cutoff L s t
        (ContextualOldGenerators.transport D Sc cutoff ht hs g)).total w
          (reindex D Sc cutoff L hs.symm w v) := by
  subst s' t'
  simp only [ContextualOldGenerators.transport, eqToHom_refl, Category.id_comp,
    Category.comp_id, reindex, LinearMap.id_apply]

omit [AddCommGroup X] [CommRing k] in
private theorem dot_word (ν η : List I) (i : I) :
    (PowerWordLayerClasses.domWord ν η (.dot i)).reverse =
      PowerWordContexts.extendedWord (ν ++ [i]) η := by
  simp [PowerWordLayerClasses.domWord, Shape.dom, List.reverse_append,
    PowerWordContexts.extendedWord_eq, List.append_assoc]

omit [AddCommGroup X] [CommRing k] in
private theorem cross_word_source (ν η : List I) (i j : I) :
    (PowerWordLayerClasses.domWord ν η (.cross i j)).reverse =
      PowerWordContexts.extendedWord ((ν ++ [j]) ++ [i]) η := by
  simp [PowerWordLayerClasses.domWord, Shape.dom, List.reverse_append,
    PowerWordContexts.extendedWord_eq, List.append_assoc]

omit [AddCommGroup X] [CommRing k] in
private theorem cross_word_target (ν η : List I) (i j : I) :
    (PowerWordLayerClasses.codWord ν η (.cross i j)).reverse =
      PowerWordContexts.extendedWord ((ν ++ [i]) ++ [j]) η := by
  simp [PowerWordLayerClasses.codWord, Shape.cod, List.reverse_append,
    PowerWordContexts.extendedWord_eq, List.append_assoc]

section Tensor
variable [Fintype I] (m : I → ℕ) (ΛP ΛR : X)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "R₀" => WeightTensorVacuum.regularProbe D Tw m ΛP
local notation "W" => elvRouquierData D Tw cutoff N ΛR

private def observation (s : List I) {x : X} (β : WeightBlocks D ΛR x)
    (hs : (s.reverse : Multiset I) = β.1) : ContentCategory D Tw cutoff N β.1 :=
  ⟨⟨s.reverse⟩, hs⟩

/-- An actual contextual dot Hom entry, evaluated on its specified source
vector and normalized only by the canonical reversed word equality. -/
def dotVector (ν η : List I) (i : I)
    (G : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR
      (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η))
    (f : G ⟶ TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ≫
      (W).E i (PowerWordWeight.wordWeight_append D ΛR ν i) ≫
      TensorHomContexts.context D Tw cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η)
    (s : List I)
    (β : WeightBlocks D ΛR (PowerWordWeightContexts.contextWeight D
      (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η))
    (hs : (s.reverse : Multiset I) = β.1)
    (z : ((G.obj R₀) β).obj (observation D Sc cutoff L ΛR s β hs)) :
    (powerWordModule D Tw cutoff L (PowerWordLayerClasses.domWord ν η (.dot i)).reverse).obj
      (OldCategory.mk s.reverse) :=
  reindex D Tw cutoff L (dot_word ν η i).symm (OldCategory.mk s.reverse)
    ((((TensorHomContexts.dotChart D Tw m cutoff L ΛP ΛR ν η i).hom β).total
      (observation D Sc cutoff L ΛR s β hs))
        (((f.total R₀) β).total (observation D Sc cutoff L ΛR s β hs) z))

/-- The literal chosen dot in the actual tensor-Hom entry is the physical
signed old layer map on every evaluated vector. -/
theorem dot_vector (ν η : List I) (i : I)
    (G : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR
      (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η))
    (f : G ⟶ TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ≫
      (W).E i (PowerWordWeight.wordWeight_append D ΛR ν i) ≫
      TensorHomContexts.context D Tw cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η)
    (s : List I)
    (β : WeightBlocks D ΛR (PowerWordWeightContexts.contextWeight D
      (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η))
    (hs : (s.reverse : Multiset I) = β.1)
    (z : ((G.obj R₀) β).obj (observation D Sc cutoff L ΛR s β hs)) :
    dotVector D Sc cutoff L m ΛP ΛR ν η i G
      (f ≫ ((TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ◁
        (W).dot i (PowerWordWeight.wordWeight_append D ΛR ν i)) ▷
        TensorHomContexts.context D Tw cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η))
      s β hs z =
    (PowerWordLayerClasses.layerMap D Sc cutoff L ν η (.dot i)).total (OldCategory.mk s.reverse)
      (dotVector D Sc cutoff L m ΛP ΛR ν η i G f s β hs z) := by
  have h := TensorHomContexts.dot_apply D Tw m cutoff L ΛP ΛR ν η i G f β
    (observation D Sc cutoff L ΛR s β hs) z
  exact (congrArg (reindex D Tw cutoff L (dot_word ν η i).symm (OldCategory.mk s.reverse)) h).trans
    (reindex_fromArrow D Tw cutoff L (dot_word ν η i) (dot_word ν η i)
      (PowerWordContexts.extendedArrow D Tw cutoff (ν ++ [i]) (ν ++ [i]) η
        (oldAppendDotComponent D Tw cutoff i (OldCategory.mk ν))) (OldCategory.mk s.reverse) _)

/-- The quotient class after the actual contextual tensor-Hom dot is
right composition with the original coefficient-one affine layer.
The only class premise specifies the input vector's class. -/
theorem dot_class_square (ν η : List I) (i : I)
    (G : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR
      (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η))
    (f : G ⟶ TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ≫
      (W).E i (PowerWordWeight.wordWeight_append D ΛR ν i) ≫
      TensorHomContexts.context D Tw cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η)
    (s : List I)
    (β : WeightBlocks D ΛR (PowerWordWeightContexts.contextWeight D
      (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η))
    (hs : (s.reverse : Multiset I) = β.1)
    (z : ((G.obj R₀) β).obj (observation D Sc cutoff L ΛR s β hs))
    (y : coefficientObj D Sc s ⟶ coefficientObj D Sc (PowerWordLayerClasses.domWord ν η (.dot i)))
    (hy : PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (PowerWordLayerClasses.domWord ν η (.dot i))
      (dotVector D Sc cutoff L m ΛP ΛR ν η i G f s β hs z) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s (PowerWordLayerClasses.domWord ν η (.dot i))).mkQ y) :
    PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (PowerWordLayerClasses.codWord ν η (.dot i))
      (dotVector D Sc cutoff L m ΛP ΛR ν η i G
        (f ≫ ((TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ◁
          (W).dot i (PowerWordWeight.wordWeight_append D ΛR ν i)) ▷
          TensorHomContexts.context D Tw cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η))
        s β hs z) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s (PowerWordLayerClasses.codWord ν η (.dot i))).mkQ
        (y ≫ sourceCoefficientHom D Sc 1 (ContextualOldGenerators.layerDiagram D Sc η.reverse (.dot i) ν.reverse)) := by
  rw [dot_vector]
  exact PowerWordLayerClasses.class_square D Sc cutoff L s ν η (.dot i) _ y hy

/-- The actual contextual pair entry at its regular-probe source vector,
normalized only by the canonical reversed source-word equality. -/
def crossVector (ν η : List I) (i j : I) {xj xu : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu)
    (G : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR
      (PowerWordWeightContexts.contextWeight D xu η))
    (f : G ⟶ TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ≫
      (W).E j h₁ ≫ (W).E i h₂ ≫ TensorHomContexts.context D Tw cutoff L ΛR xu η)
    (s : List I) (β : WeightBlocks D ΛR (PowerWordWeightContexts.contextWeight D xu η))
    (hs : (s.reverse : Multiset I) = β.1)
    (z : ((G.obj R₀) β).obj (observation D Sc cutoff L ΛR s β hs)) :
    (powerWordModule D Tw cutoff L (PowerWordLayerClasses.domWord ν η (.cross i j)).reverse).obj
      (OldCategory.mk s.reverse) :=
  reindex D Tw cutoff L (cross_word_source ν η i j).symm (OldCategory.mk s.reverse)
    ((((TensorHomContexts.pairChart D Tw m cutoff L ΛP ΛR ν η i j h₁ h₂).hom β).total
      (observation D Sc cutoff L ΛR s β hs))
        (((f.total R₀) β).total (observation D Sc cutoff L ΛR s β hs) z))

/-- The chosen crossing in an arbitrary actual tensor-Hom entry is the
physical signed old layer map on every evaluated vector. -/
theorem cross_vector (ν η : List I) (i j : I) {xj xu xi : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu)
    (h₃ : PowerWordWeight.wordWeight D ΛR ν + D.α i = xi) (h₄ : xi + D.α j = xu)
    (G : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR
      (PowerWordWeightContexts.contextWeight D xu η))
    (f : G ⟶ TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ≫
      (W).E j h₁ ≫ (W).E i h₂ ≫ TensorHomContexts.context D Tw cutoff L ΛR xu η)
    (s : List I) (β : WeightBlocks D ΛR (PowerWordWeightContexts.contextWeight D xu η))
    (hs : (s.reverse : Multiset I) = β.1)
    (z : ((G.obj R₀) β).obj (observation D Sc cutoff L ΛR s β hs)) :
    crossVector D Sc cutoff L m ΛP ΛR ν η j i h₃ h₄ G
      (f ≫ ((TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ◁
        (W).cross i j h₁ h₂ h₃ h₄) ▷ TensorHomContexts.context D Tw cutoff L ΛR xu η)) s β hs z =
    (PowerWordLayerClasses.layerMap D Sc cutoff L ν η (.cross i j)).total (OldCategory.mk s.reverse)
      (crossVector D Sc cutoff L m ΛP ΛR ν η i j h₁ h₂ G f s β hs z) := by
  have h := TensorHomContexts.cross_apply D Tw m cutoff L ΛP ΛR ν η i j h₁ h₂ h₃ h₄ G f β
    (observation D Sc cutoff L ΛR s β hs) z
  exact (congrArg (reindex D Tw cutoff L (cross_word_target ν η i j).symm (OldCategory.mk s.reverse)) h).trans
    (reindex_fromArrow D Tw cutoff L (cross_word_source ν η i j) (cross_word_target ν η i j)
      (PowerWordContexts.extendedArrow D Tw cutoff ((ν ++ [j]) ++ [i]) ((ν ++ [i]) ++ [j]) η
        (PowerWordContentCross.normalizedOldCross D Tw cutoff ν i j)) (OldCategory.mk s.reverse) _)

/-- The output quotient class after the actual contextual tensor-Hom
crossing is composition with the original coefficient-one affine layer,
including its equal-colour half-turn sign. -/
theorem cross_class_square (ν η : List I) (i j : I) {xj xu xi : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu)
    (h₃ : PowerWordWeight.wordWeight D ΛR ν + D.α i = xi) (h₄ : xi + D.α j = xu)
    (G : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶ elvWeightSpace D Tw cutoff N ΛR
      (PowerWordWeightContexts.contextWeight D xu η))
    (f : G ⟶ TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ≫
      (W).E j h₁ ≫ (W).E i h₂ ≫ TensorHomContexts.context D Tw cutoff L ΛR xu η)
    (s : List I) (β : WeightBlocks D ΛR (PowerWordWeightContexts.contextWeight D xu η))
    (hs : (s.reverse : Multiset I) = β.1)
    (z : ((G.obj R₀) β).obj (observation D Sc cutoff L ΛR s β hs))
    (y : coefficientObj D Sc s ⟶ coefficientObj D Sc (PowerWordLayerClasses.domWord ν η (.cross i j)))
    (hy : PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (PowerWordLayerClasses.domWord ν η (.cross i j))
      (crossVector D Sc cutoff L m ΛP ΛR ν η i j h₁ h₂ G f s β hs z) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s (PowerWordLayerClasses.domWord ν η (.cross i j))).mkQ y) :
    PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (PowerWordLayerClasses.codWord ν η (.cross i j))
      (crossVector D Sc cutoff L m ΛP ΛR ν η j i h₃ h₄ G
        (f ≫ ((TensorVacuumWords.wordHom D Tw m cutoff L ΛP ΛR ν ◁
          (W).cross i j h₁ h₂ h₃ h₄) ▷ TensorHomContexts.context D Tw cutoff L ΛR xu η)) s β hs z) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s (PowerWordLayerClasses.codWord ν η (.cross i j))).mkQ
        (y ≫ sourceCoefficientHom D Sc 1 (ContextualOldGenerators.layerDiagram D Sc η.reverse (.cross i j) ν.reverse)) := by
  rw [cross_vector]
  exact PowerWordLayerClasses.class_square D Sc cutoff L s ν η (.cross i j) _ y hy

end Tensor
end OddMath.QuiverHecke.ELVOld.TensorLayerClasses
