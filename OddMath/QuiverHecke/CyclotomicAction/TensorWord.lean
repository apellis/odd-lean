import OddMath.QuiverHecke.HalfTurn.PowerWordLayerClasses
import OddMath.QuiverHecke.CyclotomicAction.TensorWords
import OddMath.QuiverHecke.CyclotomicAction.VacuumTensorFaithful
import OddMath.QuiverHecke.CyclotomicAction.WeightedPower
import OddMath.QuiverHecke.CyclotomicAction.InductionTripleBraid

/-!
# Tensor word

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Source classes of contextual tensor-Hom layer entries

SwappedVacuumCoordinates §§2–7: evaluate the unchanged chosen ELV
tensor-Hom entries at the regular probe, on every vector in the specified
source-content block, and identify their signed original layer quotient
classes. No complete swapped factor or faithfulness premise is needed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.TensorLayerClasses
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
end OddMath.QuiverHecke.ELV.TensorLayerClasses
end

end

section

/-! # Append coherence of the prescribed tensor word chart

SwappedVacuumCoordinates §§2–5: the global selected tensor-word chart
agrees with its prescribed single-letter append chart through the literal
whole-functor append equality. This is the first coherence input for an
observation independent of the chosen local layer decomposition.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.TensorVacuumWords
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "R" => WeightTensorVacuum.regularProbe D Sc m ΛP

/-- The global whole-Hom word chart is exactly its given append chart,
including the original tensor-Hom word equality. -/
theorem chart_append_hom (ν : List I) (i : I) :
    (chart D Sc m cutoff L ΛP ΛR (ν ++ [i])).hom =
      eqToHom (congrArg (fun F => F.obj R) (wordHom_append D Sc m cutoff L ΛP ΛR ν i)) ≫
        (dotChart D Sc m cutoff L ΛP ΛR ν i).hom := by
  simp only [chart,dotChart,valueIso,List.reverseRecOn_concat,
    PowerWordEvaluation.chart_append, PowerWordEvaluation.appendChart,
    Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom, Iso.symm_hom]
  simp only [eqToIso.inv, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end OddMath.QuiverHecke.ELV.TensorVacuumWords
end

end

section

/-! # Pair coherence of the prescribed tensor word chart

SwappedVacuumCoordinates §§2–5: compare the global whole-word chart
with the prescribed two-letter chart at the canonical successive weights.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.TensorVacuumWords
open CyclotomicAction SwappedAssembly
private theorem eqToHom_comp_heq {C : Type*} [Category* C]
    {A B T : C} (h : A = B) (f : B ⟶ T) : HEq (eqToHom h ≫ f) f := by
  subst B
  simp only [eqToHom_refl, Category.id_comp]
  rfl

universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "R" => WeightTensorVacuum.regularProbe D Sc m ΛP
local notation "W" => elvRouquierData D Sc cutoff (PowerWordContent.powerBound D cutoff L) ΛR

/-- The global whole tensor Hom retains the two chronological appends. -/
theorem wordHom_pair (ν : List I) (i j : I) :
    wordHom D Sc m cutoff L ΛP ΛR ((ν ++ [j]) ++ [i]) =
      wordHom D Sc m cutoff L ΛP ΛR ν ≫
        (W).E j (PowerWordWeight.wordWeight_append D ΛR ν j) ≫
          (W).E i (PowerWordWeight.wordWeight_append D ΛR (ν ++ [j]) i) := by
  rw [wordHom_append, wordHom_append]
  rfl

/-- The prescribed global chart equals the pair chart through the equality
of the entire tensor Hom, before any generator is applied. -/
theorem chart_pair_hom (ν : List I) (i j : I) :
    (chart D Sc m cutoff L ΛP ΛR ((ν ++ [j]) ++ [i])).hom =
      eqToHom (congrArg (fun F => F.obj R) (wordHom_pair D Sc m cutoff L ΛP ΛR ν i j)) ≫
        (pairChart D Sc m cutoff L ΛP ΛR ν i j
          (PowerWordWeight.wordWeight_append D ΛR ν j)
          (PowerWordWeight.wordWeight_append D ΛR (ν ++ [j]) i)).hom := by
  simp only [chart, pairChart, valueIso, List.reverseRecOn_concat,
    PowerWordEvaluation.chart_append, PowerWordEvaluation.pairChart,
    PowerWordWeightCross.recursivePairIso, PowerWordWeightCross.appendIsoAtWeights,
    Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map, Functor.map_comp,
    Iso.symm_hom, eqToIso.hom, eqToIso.inv]
  simp only [eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rfl

/-- Reading the canonical source-functor equality as a transport gives
one and the same append chart on the entire value Hom. -/
theorem chart_append_heq (ν : List I) (i : I) :
    HEq (chart D Sc m cutoff L ΛP ΛR (ν ++ [i])).hom
      (dotChart D Sc m cutoff L ΛP ΛR ν i).hom :=
  (heq_of_eq (chart_append_hom D Sc m cutoff L ΛP ΛR ν i)).trans
    (eqToHom_comp_heq _ _)

/-- The two-letter local chart has the same whole-map value as the global
word chart, including both equal and distinct colours. -/
theorem chart_pair_heq (ν : List I) (i j : I) :
    HEq (chart D Sc m cutoff L ΛP ΛR ((ν ++ [j]) ++ [i])).hom
      (pairChart D Sc m cutoff L ΛP ΛR ν i j
        (PowerWordWeight.wordWeight_append D ΛR ν j)
        (PowerWordWeight.wordWeight_append D ΛR (ν ++ [j]) i)).hom :=
  (heq_of_eq (chart_pair_hom D Sc m cutoff L ΛP ΛR ν i j)).trans
    (eqToHom_comp_heq _ _)

end OddMath.QuiverHecke.ELV.TensorVacuumWords
end

end

section

/-! # Global tensor word charts in arbitrary outer contexts

SwappedVacuumCoordinates §§2–5: the prescribed recursive outer E charts
retain the same global concatenated-word chart on whole regular-probe
values. All comparisons in the final dot and pair statements are supplied
by the actual word constructions.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.TensorVacuumWords
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "R" => WeightTensorVacuum.regularProbe D Sc m ΛP

private theorem postValue_heq (i : I) {x y x' y' : X} (hx : x = x') (hy : y = y')
    (h : x + D.α i = y) (h' : x' + D.α i = y')
    {A : ELVWeightProduct D Sc cutoff N ΛR x} {A' : ELVWeightProduct D Sc cutoff N ΛR x'}
    (hA : HEq A A') :
    HEq ((elvE D Sc cutoff N i ΛR h).obj A) ((elvE D Sc cutoff N i ΛR h').obj A') := by
  cases hx
  cases hy
  cases hA
  rfl

private theorem appendChart_heq (ν : List I) (i : I) {x y : X}
    (hx : x = PowerWordWeight.wordWeight D ΛR ν)
    (hy : y = PowerWordWeight.wordWeight D ΛR (ν ++ [i])) (h : x + D.α i = y)
    (A : ELVWeightProduct D Sc cutoff N ΛR x)
    (hA : HEq A ((wordHom D Sc m cutoff L ΛP ΛR ν).obj R))
    (e : A ≅ PowerWordWeight.wordFamily D Sc cutoff L ΛR x ν)
    (he : HEq e.hom (chart D Sc m cutoff L ΛP ΛR ν).hom) :
    HEq (((elvE D Sc cutoff N i ΛR h).toFunctor.mapIso e ≪≫
      PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L ΛR ν i x y hx hy h).hom)
      (chart D Sc m cutoff L ΛP ΛR (ν ++ [i])).hom := by
  cases hx
  cases hy
  cases hA
  have heq : e = chart D Sc m cutoff L ΛP ΛR ν := Iso.ext (eq_of_heq he)
  subst e
  have hd : (((elvE D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ν i)).toFunctor.mapIso
      (chart D Sc m cutoff L ΛP ΛR ν) ≪≫ PowerWordWeight.weightAppendIso D Sc cutoff L ΛR ν i).hom) =
      (dotChart D Sc m cutoff L ΛP ΛR ν i).hom := by
    simp only [chart, dotChart, PowerWordEvaluation.appendChart, Iso.trans_hom,
      Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  exact (heq_of_eq hd).trans (chart_append_heq D Sc m cutoff L ΛP ΛR ν i).symm

/-- Intermediate transport lemma. Its base comparisons are supplied by
whole-word and global-chart identities in the final context statements. -/
private theorem contextChart_heq (ν η : List I) (x : X)
    (hx : x = PowerWordWeight.wordWeight D ΛR ν)
    (A : ELVWeightProduct D Sc cutoff N ΛR x)
    (hA : HEq A ((wordHom D Sc m cutoff L ΛP ΛR ν).obj R))
    (e : A ≅ PowerWordWeight.wordFamily D Sc cutoff L ΛR x ν)
    (he : HEq e.hom (chart D Sc m cutoff L ΛP ΛR ν).hom) :
    HEq (PowerWordWeightContexts.contextChart D Sc cutoff L ΛR ν η x hx e).hom
      (chart D Sc m cutoff L ΛP ΛR (PowerWordContexts.extendedWord ν η)).hom := by
  induction η generalizing ν x with
  | nil =>
    cases hx
    cases hA
    have heq : e = chart D Sc m cutoff L ΛP ΛR ν := Iso.ext (eq_of_heq he)
    subst e
    simp only [PowerWordWeightContexts.contextChart, PowerWordWeightContexts.contextFunctor,
      PowerWordWeightContexts.contextIso, Functor.mapIso_hom, Functor.id_map, Iso.trans_hom,
      Iso.refl_hom, Category.comp_id, PowerWordContexts.extendedWord]
    rfl
  | cons i η ih =>
    cases hx
    cases hA
    have heq : e = chart D Sc m cutoff L ΛP ΛR ν := Iso.ext (eq_of_heq he)
    subst e
    let y := PowerWordWeight.wordWeight D ΛR ν + D.α i
    have hy : y = PowerWordWeight.wordWeight D ΛR (ν ++ [i]) :=
      PowerWordWeight.wordWeight_append D ΛR ν i
    let A' := (elvE D Sc cutoff N i ΛR (rfl : PowerWordWeight.wordWeight D ΛR ν + D.α i = y)).obj
      ((wordHom D Sc m cutoff L ΛP ΛR ν).obj R)
    have hA' : HEq A' ((wordHom D Sc m cutoff L ΛP ΛR (ν ++ [i])).obj R) :=
      (postValue_heq D Sc cutoff L ΛR i rfl hy rfl
        (PowerWordWeight.wordWeight_append D ΛR ν i) (HEq.rfl : HEq
          ((wordHom D Sc m cutoff L ΛP ΛR ν).obj R) _)).trans
            (heq_of_eq (congrArg (fun F => F.obj R) (wordHom_append D Sc m cutoff L ΛP ΛR ν i)).symm)
    let e' := (elvE D Sc cutoff N i ΛR (rfl : PowerWordWeight.wordWeight D ΛR ν + D.α i = y)).toFunctor.mapIso
      (chart D Sc m cutoff L ΛP ΛR ν) ≪≫
        PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L ΛR ν i _ y rfl hy rfl
    have he' : HEq e'.hom (chart D Sc m cutoff L ΛP ΛR (ν ++ [i])).hom :=
      appendChart_heq D Sc m cutoff L ΛP ΛR ν i rfl hy rfl _ HEq.rfl _ HEq.rfl
    have hc : (PowerWordWeightContexts.contextChart D Sc cutoff L ΛR ν (i :: η) _ rfl
        (chart D Sc m cutoff L ΛP ΛR ν)).hom =
        (PowerWordWeightContexts.contextChart D Sc cutoff L ΛR (ν ++ [i]) η y hy e').hom := by
      simp only [PowerWordWeightContexts.contextChart, PowerWordWeightContexts.contextFunctor,
        PowerWordWeightContexts.contextIso, e', Iso.trans_hom, Functor.mapIso_hom,
        Functor.comp_map, Functor.map_comp, Category.assoc]
      rfl
    exact (heq_of_eq hc).trans (ih (ν ++ [i]) y hy A' hA' e' he')

private theorem chart_word_heq {ν ρ : List I} (h : ν = ρ) :
    HEq (chart D Sc m cutoff L ΛP ΛR ν).hom (chart D Sc m cutoff L ΛP ΛR ρ).hom := by
  cases h
  rfl

/-- The given local dot chart in every outer context is the single global
chart of its concatenated word. No comparison premise is supplied. -/
theorem dotContextChart_global_heq (ν η : List I) (i : I) :
    HEq (TensorHomContexts.dotChart D Sc m cutoff L ΛP ΛR ν η i).hom
      (chart D Sc m cutoff L ΛP ΛR ((ν ++ [i]) ++ η)).hom := by
  have hA := heq_of_eq (congrArg (fun F => F.obj R) (wordHom_append D Sc m cutoff L ΛP ΛR ν i)).symm
  exact (contextChart_heq D Sc m cutoff L ΛP ΛR (ν ++ [i]) η _ rfl _ hA
      (dotChart D Sc m cutoff L ΛP ΛR ν i) (chart_append_heq D Sc m cutoff L ΛP ΛR ν i).symm).trans
    (chart_word_heq D Sc m cutoff L ΛP ΛR (PowerWordContexts.extendedWord_eq (ν ++ [i]) η))

/-- The given local pair chart in every outer context is the single global
chart, including equal and distinct colours and all original intermediate weights. -/
theorem pairContextChart_global_heq (ν η : List I) (i j : I) {xj xu : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu) :
    HEq (TensorHomContexts.pairChart D Sc m cutoff L ΛP ΛR ν η i j h₁ h₂).hom
      (chart D Sc m cutoff L ΛP ΛR (((ν ++ [j]) ++ [i]) ++ η)).hom := by
  have hxj : xj = PowerWordWeight.wordWeight D ΛR (ν ++ [j]) :=
    h₁.symm.trans (PowerWordWeight.wordWeight_append D ΛR ν j)
  have hxu : xu = PowerWordWeight.wordWeight D ΛR ((ν ++ [j]) ++ [i]) :=
    h₂.symm.trans ((congrArg (fun x => x + D.α i) hxj).trans
      (PowerWordWeight.wordWeight_append D ΛR (ν ++ [j]) i))
  cases hxj
  cases hxu
  have hA := heq_of_eq (congrArg (fun F => F.obj R) (wordHom_pair D Sc m cutoff L ΛP ΛR ν i j)).symm
  exact (contextChart_heq D Sc m cutoff L ΛP ΛR ((ν ++ [j]) ++ [i]) η _ rfl _ hA
      (pairChart D Sc m cutoff L ΛP ΛR ν i j
        (PowerWordWeight.wordWeight_append D ΛR ν j)
        (PowerWordWeight.wordWeight_append D ΛR (ν ++ [j]) i))
      (chart_pair_heq D Sc m cutoff L ΛP ΛR ν i j).symm).trans
    (chart_word_heq D Sc m cutoff L ΛP ΛR
      (PowerWordContexts.extendedWord_eq ((ν ++ [j]) ++ [i]) η))

end OddMath.QuiverHecke.ELV.TensorVacuumWords
end

end

section

/-! # Source coefficients on the whole tensor E-word

SwappedVacuumCoordinates §§2–6: the source coefficient endomorphism is
whiskered through each prescribed E functor on the full tensor Hom. The
normalizing word equalities are transported by their specified isomorphisms.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.TensorWordCoefficientAction
open CyclotomicAction SwappedAssembly VacuumTensorCoefficientMaps
universe u
section Generic
variable {k : Type*} [CommRing k] {C : Type*} [Category* C] [Preadditive C] [Linear k C]
private def eqEndAction {F G : C} (h : F = G) : End F →ₐ[k] End G := by
  subst G
  exact AlgHom.id k (End F)
private theorem eqEndAction_apply {F G : C} (h : F = G) (f : End F) :
    eqEndAction (k := k) h f = eqToHom h.symm ≫ f ≫ eqToHom h := by
  subst G
  simp only [eqEndAction, AlgHom.id_apply, eqToHom_refl, Category.id_comp, Category.comp_id]
end Generic
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "R" => WeightTensorVacuum.regularProbe D Sc m ΛP
local notation "W" => elvRouquierData D Sc cutoff N ΛR
local notation "Z" => WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L

private def reindexAction {x y : X} (h : x = y)
    (F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x)
    (a : SKM.SYM D k →ₐ[k] End F) :
    SKM.SYM D k →ₐ[k] End (h ▸ F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶
      elvWeightSpace D Sc cutoff N ΛR y) := by
  subst y
  exact a

private def initialAction : SKM.SYM D k →ₐ[k] End (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR []) :=
  (eqEndAction (TensorReservoirWords.pathHomAt_eq_wordHom D Sc m cutoff L ΛP ΛR
    (SPath.nil (0,0)) (by simp))).comp
      (reindexAction D Sc m cutoff L ΛP ΛR
        (TensorReservoirWords.path_weight D ΛR (SPath.nil (0,0)) (by simp))
        (TensorReservoirWords.pathHom D Sc m cutoff L ΛP ΛR (SPath.nil (0,0)) (by simp))
        (pathCoefficientAction D Sc m cutoff L ΛP ΛR (SPath.nil (0,0)) (by simp)))

/-- The source action on a whole E-word is literal right whiskering of
the selected full-input tensor action at every append step. -/
def wordAction (ν : List I) : SKM.SYM D k →ₐ[k]
    End (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν) :=
  ν.reverseRecOn (initialAction D Sc m cutoff L ΛP ΛR)
    (fun ρ i a =>
      (eqEndAction (TensorVacuumWords.wordHom_append D Sc m cutoff L ΛP ΛR ρ i).symm).comp
        ((postwhiskerEndAction (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ρ)
          (elvE D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ρ i))).comp a))

/-- Append preserves the literal full supernatural coefficient, with
only the given whole-Hom equality inserted around the map. -/
theorem wordAction_append (ν : List I) (i : I) (a : SKM.SYM D k) :
    wordAction D Sc m cutoff L ΛP ΛR (ν ++ [i]) a =
      eqToHom (TensorVacuumWords.wordHom_append D Sc m cutoff L ΛP ΛR ν i) ≫
        Superfunctor.whiskerRight (wordAction D Sc m cutoff L ΛP ΛR ν a)
          (elvE D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ν i)) ≫
            eqToHom (TensorVacuumWords.wordHom_append D Sc m cutoff L ΛP ΛR ν i).symm := by
  simp only [wordAction, List.reverseRecOn_concat, AlgHom.comp_apply, eqEndAction_apply]
  rfl

end OddMath.QuiverHecke.ELV.TensorWordCoefficientAction
end

end

section

/-! # Coefficient maps along tensor reservoir paths

SwappedVacuumCoordinates §§2–6: comparison of the direct reservoir-path
coefficient with the recursive whole-word coefficient, before evaluation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.TensorPathCoefficientCoherence
open CyclotomicAction SwappedAssembly VacuumTensorCoefficientMaps TensorWordCoefficientAction
universe u
section Generic
variable {k : Type*} [CommRing k] {C : Type*} [Category* C] [Preadditive C] [Linear k C]
private def eqAction {F G : C} (h : F = G) : End F →ₐ[k] End G := by
  subst G
  exact AlgHom.id k (End F)
private theorem eqAction_heq {F G : C} (h : F = G) (f : End F) :
    HEq (eqAction (k := k) h f) f := by
  subst G
  rfl
end Generic
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "W" => elvRouquierData D Sc cutoff N ΛR
private def reindexAction {x y : X} (h : x = y)
    (F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x)
    (a : SKM.SYM D k →ₐ[k] End F) :
    SKM.SYM D k →ₐ[k] End (h ▸ F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶
      elvWeightSpace D Sc cutoff N ΛR y) := by
  subst y
  exact a
private theorem reindexAction_heq {x y : X} (h : x = y)
    (F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x)
    (φ : SKM.SYM D k →ₐ[k] End F) (a : SKM.SYM D k) :
    HEq (reindexAction D Sc m cutoff L ΛP ΛR h F φ a) (φ a) := by
  subst y
  rfl

/-- Empty-word normalization retains the entire coefficient map. -/
theorem wordAction_nil_heq (a : SKM.SYM D k) :
    HEq (wordAction D Sc m cutoff L ΛP ΛR [] a)
      (pathCoefficientAction D Sc m cutoff L ΛP ΛR (SPath.nil (0,0)) (by simp) a) := by
  simp only [wordAction, List.reverseRecOn_nil]
  change HEq (eqAction (k := k)
    (TensorReservoirWords.pathHomAt_eq_wordHom D Sc m cutoff L ΛP ΛR (SPath.nil (0,0)) (by simp))
    (reindexAction D Sc m cutoff L ΛP ΛR
      (TensorReservoirWords.path_weight D ΛR (SPath.nil (0,0)) (by simp))
      (TensorReservoirWords.pathHom D Sc m cutoff L ΛP ΛR (SPath.nil (0,0)) (by simp))
      (pathCoefficientAction D Sc m cutoff L ΛP ΛR (SPath.nil (0,0)) (by simp)) a)) _
  exact (eqAction_heq (k := k) _ _).trans (reindexAction_heq D Sc m cutoff L ΛP ΛR _ _ _ _)

private theorem conjugate_heq {C : Type*} [Category* C] {F G : C}
    (h : F = G) (f : End F) : HEq (eqToHom h.symm ≫ f ≫ eqToHom h) f := by
  subst G
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- Append normalization changes no coefficient map. -/
theorem wordAction_append_heq (ν : List I) (i : I) (a : SKM.SYM D k) :
    HEq (wordAction D Sc m cutoff L ΛP ΛR (ν ++ [i]) a)
      (Superfunctor.whiskerRight (wordAction D Sc m cutoff L ΛP ΛR ν a)
        (elvE D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ν i))) := by
  rw [wordAction_append]
  exact conjugate_heq _ _

private theorem postE_map_heq (i : I) {x y x' y' : X} (hx : x = x') (hy : y = y')
    (h : x + D.α i = y) (h' : x' + D.α i = y')
    {F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x}
    {F' : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x'}
    (hF : HEq F F') {f : End F} {f' : End F'} (hf : HEq f f') :
    HEq (Superfunctor.whiskerRight f (elvE D Sc cutoff N i ΛR h))
      (Superfunctor.whiskerRight f' (elvE D Sc cutoff N i ΛR h')) := by
  cases hx
  cases hy
  cases hF
  cases hf
  rfl

omit [Fintype I] in
private theorem edge (i : I) (c : I →₀ ℕ) (hc : 1 ≤ c i) :
    ReservoirWord.weight D ΛR (c - Finsupp.single i 1) + D.α i = ReservoirWord.weight D ΛR c := by
  simp only [ReservoirWord.weight]
  rw [add_assoc, contentWeight_sub_single hc]

private theorem pathAction_cons_heq (i : I) (r : X) {l : List (SKM.Col I X)}
    {c : I →₀ ℕ} (hc : 1 ≤ c i) (p : SPath l (0,c - Finsupp.single i 1) (0,0))
    (hl : ∀ b ∈ l, b.l.1 = true) (a : SKM.SYM D k) :
    HEq (pathCoefficientAction D Sc m cutoff L ΛP ΛR
      (SPath.cons ⟨(true,i),r⟩ false (0,c) hc p) (by
        simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨True.intro,hl⟩) a)
      (Superfunctor.whiskerRight (pathCoefficientAction D Sc m cutoff L ΛP ΛR p hl a)
        (elvE D Sc cutoff N i ΛR (edge D ΛR i c hc))) := by
  have hh := ReservoirWord.word_cons W ΛR i r hc p hl
  have hg : ∀ (G G' : elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR 0) ⟶
      elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR c)), G = G' →
      HEq (Superfunctor.whiskerRight
        (sourceCoefficientAction D Sc m cutoff L ΛP ΛR a) G)
        (Superfunctor.whiskerRight
          (sourceCoefficientAction D Sc m cutoff L ΛP ΛR a) G') := by
    intro G G' h
    subst G'
    rfl
  apply (hg _ _ hh).trans
  apply heq_of_eq
  apply Superfunctor.hom_ext
  intro q M
  rfl

private theorem wordAction_word_heq {ν τ : List I} (h : ν = τ) (a : SKM.SYM D k) :
    HEq (wordAction D Sc m cutoff L ΛP ΛR ν a) (wordAction D Sc m cutoff L ΛP ΛR τ a) := by
  subst τ
  rfl

/-- The direct path coefficient agrees with the recursive normalized word
coefficient on the entire input Hom, at their proved equal original weights. -/
theorem pathAction_heq {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true) (a : SKM.SYM D k) :
    HEq (pathCoefficientAction D Sc m cutoff L ΛP ΛR p hl a)
      (wordAction D Sc m cutoff L ΛP ΛR ((l.map (fun b => b.l.2)).reverse) a) := by
  induction l generalizing c with
  | nil =>
    cases p
    exact (wordAction_nil_heq D Sc m cutoff L ΛP ΛR a).symm
  | cons b l ih =>
    cases p with
    | cons b side s hv p =>
      have hb := hl b List.mem_cons_self
      have ht : ∀ d ∈ l, d.l.1 = true := fun d hd => hl d (List.mem_cons_of_mem _ hd)
      rcases b with ⟨⟨up,i⟩,r⟩
      cases up with
      | false => cases hb
      | true =>
        have hs := SPath.side_eq_false_of_upward_probe_zero i side p ht rfl
        subst side
        change SPath l (0,c - Finsupp.single i 1) (0,0) at p
        have hw := TensorReservoirWords.path_weight D ΛR p ht
        have hy : ReservoirWord.weight D ΛR c = PowerWordWeight.wordWeight D ΛR
            (((l.map (fun b => b.l.2)).reverse) ++ [i]) :=
          (edge D ΛR i c hv).symm.trans ((congrArg (fun x => x + D.α i) hw).trans
            (PowerWordWeight.wordWeight_append D ΛR ((l.map (fun b => b.l.2)).reverse) i))
        have hf := postE_map_heq D Sc m cutoff L ΛP ΛR i hw hy (edge D ΛR i c hv)
          (PowerWordWeight.wordWeight_append D ΛR ((l.map (fun b => b.l.2)).reverse) i)
          (TensorReservoirWords.pathHom_heq D Sc m cutoff L ΛP ΛR p ht) (ih p ht)
        have hwords : ((l.map (fun b => b.l.2)).reverse) ++ [i] =
            (((⟨(true,i),r⟩ :: l).map (fun b => b.l.2)).reverse) := by
          rw [List.map_cons, List.reverse_cons]
        exact (pathAction_cons_heq D Sc m cutoff L ΛP ΛR i r hv p ht a).trans
          (hf.trans ((wordAction_append_heq D Sc m cutoff L ΛP ΛR
            ((l.map (fun b => b.l.2)).reverse) i a).symm.trans
              (wordAction_word_heq D Sc m cutoff L ΛP ΛR hwords a)))
end OddMath.QuiverHecke.ELV.TensorPathCoefficientCoherence
end

end

section

/-! # Tensor coefficients as output-module arrows

SwappedVacuumCoordinates §6: the full tensor-vacuum coefficient acts by
the coefficient arrow of the actual output content category. Even module
charts therefore intertwine both odd and even source coefficients.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.TensorCoefficientNaturality
open VacuumTensorCoefficientMaps CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "A" => SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff
local notation "Z" => WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L

/-- The full coefficient arrow in an actual truncated content category. -/
def contentCoefficientArrow {β : Multiset I}
    (c : ContentCategory D Sc cutoff N β) (a : A) : c ⟶ c :=
  (truncatedIdeal D Sc cutoff N c.obj.word c.obj.word).mkQ
    (ELVPScalar.scalar D Sc cutoff c.obj.word a)

/-- The reservoir block action is its own module action on this arrow. -/
theorem vacuumBlockAction_total
    (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0)) (a : A)
    (c : ContentCategory D Sc cutoff N β.1) :
    (vacuumBlockAction D Sc cutoff L ΛR β a).total c =
      (ReservoirWordValue.initialValue D ΛR Sc cutoff L β).map
        (contentCoefficientArrow D Sc cutoff L c a) := by
  change (coefficientModuleAction D Sc cutoff (powerWordModule D Sc cutoff L []) a).total
    (OldCategory.mk c.obj.word) = _
  rw [coefficientModuleAction_total]
  rfl

/-- The whole-input coefficient is the output module's coefficient map. -/
theorem coefficientAction_output
    (a : A) (M : probeOldWeightSpace D Sc m ΛP (-ΛP))
    (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0))
    (c : ContentCategory D Sc cutoff N β.1) :
    (((VacuumTensorCoefficientMaps.coefficientAction D Sc m cutoff L ΛP ΛR a).total M) β).total c =
      (((Z).obj M) β).map (contentCoefficientArrow D Sc cutoff L c a) := by
  rw [coefficientAction_total, vacuumBlockAction_total]
  rfl

end OddMath.QuiverHecke.ELV.TensorCoefficientNaturality
end

end

section

/-! # Tensor word charts and full source coefficients

SwappedVacuumCoordinates §6: the prescribed global tensor-word chart
intertwines the full source coefficient with its signed old-Hom arrow.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.TensorWordCoefficientChart
open CyclotomicAction SwappedAssembly VacuumTensorCoefficientMaps TensorWordCoefficientAction
open TensorPathCoefficientCoherence TensorCoefficientNaturality
universe u
private theorem mapped_square {C B : Type*} [Category* C] [Category* B]
    (F : C ⥤ B) {A P : C} {E : B} (e : A ≅ P) (f : F.obj P ≅ E)
    (x : End A) (y : End P) (z : End E)
    (hx : x ≫ e.hom = e.hom ≫ y) (hf : F.map y ≫ f.hom = f.hom ≫ z) :
    F.map x ≫ (F.mapIso e ≪≫ f).hom = (F.mapIso e ≪≫ f).hom ≫ z := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, ← F.map_comp, hx, F.map_comp, Category.assoc, hf]
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "P₀" => WeightTensorVacuum.regularProbe D Sc m ΛP
local notation "Z" => WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L
local notation "A" => SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff

/-- The signed old-Hom coefficient arrow acts by the same output coefficient. -/
theorem wordFamilyArrow_total (x : X) (ν : List I) (a : A)
    (β : WeightBlocks D ΛR x) (c : ContentCategory D Sc cutoff N β.1) :
    (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L ΛR x ν ν
      (coefficientEndomorphism D Sc cutoff ν a) β).total c =
    (PowerWordWeight.wordFamily D Sc cutoff L ΛR x ν β).map
      (contentCoefficientArrow D Sc cutoff L c a) := by
  change (PowerWordContentCross.contentWordArrow D Sc cutoff L β.1 ν ν
    (coefficientEndomorphism D Sc cutoff ν a)).total c = _
  rw [PowerWordContentCross.contentWordArrow_total, ← PowerWordCoefficients.coefficient_fromArrow,
    coefficientModuleAction_total]
  rfl

private theorem nilHom_heq :
    HEq (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR []) Z := by
  apply (TensorReservoirWords.pathHom_heq D Sc m cutoff L ΛP ΛR (SPath.nil (0,0)) (by simp)).symm.trans
  change HEq (Z ≫ ReservoirWord.word (elvRouquierData D Sc cutoff N ΛR) ΛR
    (SPath.nil (0,0)) (by simp)) Z
  rw [ReservoirWord.word_nil]
  rfl

private theorem nilAction_heq (a : SKM.SYM D k) :
    HEq (wordAction D Sc m cutoff L ΛP ΛR [] a)
      (sourceCoefficientAction D Sc m cutoff L ΛP ΛR a) := by
  apply (wordAction_nil_heq D Sc m cutoff L ΛP ΛR a).trans
  have hg : ∀ (G : elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR 0) ⟶
      elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR 0)), G = 𝟙 _ →
      HEq (Superfunctor.whiskerRight (sourceCoefficientAction D Sc m cutoff L ΛP ΛR a) G)
        (sourceCoefficientAction D Sc m cutoff L ΛP ΛR a) := by
    intro G h
    subst G
    apply heq_of_eq
    apply Superfunctor.hom_ext
    intro q M
    rfl
  exact hg _ (ReservoirWord.word_nil _ ΛR 0)

private theorem output_transport {x y : X} (h : x = y)
    {F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x}
    {F' : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR y}
    (hF : HEq F F') {f : End F} {f' : End F'} (hf : HEq f f') (a : A)
    (hout : ∀ (β : WeightBlocks D ΛR x) (c : ContentCategory D Sc cutoff N β.1),
      ((f.total P₀) β).total c = ((F.obj P₀) β).map (contentCoefficientArrow D Sc cutoff L c a)) :
    ∀ (β : WeightBlocks D ΛR y) (c : ContentCategory D Sc cutoff N β.1),
      ((f'.total P₀) β).total c = ((F'.obj P₀) β).map (contentCoefficientArrow D Sc cutoff L c a) := by
  cases h
  cases hF
  cases hf
  exact hout

/-- The normalized empty-word action is still the output coefficient action. -/
theorem wordAction_nil_output (a : SKM.SYM D k)
    (β : WeightBlocks D ΛR (PowerWordWeight.wordWeight D ΛR []))
    (c : ContentCategory D Sc cutoff N β.1) :
    (((wordAction D Sc m cutoff L ΛP ΛR [] a).total P₀) β).total c =
      (((TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR []).obj P₀) β).map
        (contentCoefficientArrow D Sc cutoff L c (SKM.SYM.elvCoefficientQuotient D cutoff a)) := by
  exact output_transport D Sc m cutoff L ΛP ΛR
    (TensorReservoirWords.path_weight D ΛR (SPath.nil (0,0)) (by simp))
    (nilHom_heq D Sc m cutoff L ΛP ΛR).symm (nilAction_heq D Sc m cutoff L ΛP ΛR a).symm
    (SKM.SYM.elvCoefficientQuotient D cutoff a)
    (fun β c => coefficientAction_output D Sc m cutoff L ΛP ΛR
      (SKM.SYM.elvCoefficientQuotient D cutoff a) P₀ β c) β c

/-- The global empty-word chart intertwines every raw source coefficient. -/
theorem chart_nil_square (a : SKM.SYM D k) :
    (wordAction D Sc m cutoff L ΛP ΛR [] a).total P₀ ≫
      (TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR []).hom =
    (TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR []).hom ≫
      PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L ΛR
        (PowerWordWeight.wordWeight D ΛR []) [] []
        (coefficientEndomorphism D Sc cutoff [] (SKM.SYM.elvCoefficientQuotient D cutoff a)) := by
  funext β
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro c
  change (((wordAction D Sc m cutoff L ΛP ΛR [] a).total P₀) β ≫
    (TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR []).hom β).total c = _
  rw [Superfunctor.comp_total, wordAction_nil_output]
  change _ = (((TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR []).hom β ≫
    PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L ΛR
      (PowerWordWeight.wordWeight D ΛR []) [] []
      (coefficientEndomorphism D Sc cutoff [] (SKM.SYM.elvCoefficientQuotient D cutoff a)) β).total c)
  rw [Superfunctor.comp_total, wordFamilyArrow_total]
  let f := (TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR []).hom β
  have hf : f ∈ parity (R := k) _ _ 0 := TensorVacuumWords.chart_even D Sc m cutoff L ΛP ΛR [] β
  have htotal : f.total c = f.app 0 c := by
    rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  change _ ≫ f.total c = f.total c ≫ _
  rw [htotal]
  exact ((Superfunctor.toSuperNatTrans f).isSupernatural 0).naturality_zero _

private theorem square_transport
    {x : X}
    {F G : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x}
    (h : F = G) {f : End F} {g : End G} (hf : HEq f g)
    {T : ELVWeightProduct D Sc cutoff N ΛR x}
    (cF : F.obj P₀ ⟶ T) (cG : G.obj P₀ ⟶ T) (hc : HEq cF cG) (z : End T)
    (hs : f.total P₀ ≫ cF = cF ≫ z) : g.total P₀ ≫ cG = cG ≫ z := by
  cases h
  cases hf
  cases hc
  exact hs

private theorem dotChart_hom (ν : List I) (i : I) :
    (TensorVacuumWords.dotChart D Sc m cutoff L ΛP ΛR ν i).hom =
      (elvE D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ν i)).map
        (TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR ν).hom ≫
          (PowerWordWeight.weightAppendIso D Sc cutoff L ΛR ν i).hom := by
  simp only [TensorVacuumWords.dotChart, TensorVacuumWords.chart, PowerWordEvaluation.appendChart,
    Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]

/-- The prescribed global word chart intertwines the entire raw source
coefficient action with the signed original coefficient arrow. -/
theorem chart_square (ν : List I) (a : SKM.SYM D k) :
    (wordAction D Sc m cutoff L ΛP ΛR ν a).total P₀ ≫
      (TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR ν).hom =
    (TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR ν).hom ≫
      PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L ΛR
        (PowerWordWeight.wordWeight D ΛR ν) ν ν
        (coefficientEndomorphism D Sc cutoff ν (SKM.SYM.elvCoefficientQuotient D cutoff a)) := by
  induction ν using List.reverseRecOn with
  | nil => exact chart_nil_square D Sc m cutoff L ΛP ΛR a
  | append_singleton ν i ih =>
    let E := elvE D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ν i)
    let f := wordAction D Sc m cutoff L ΛP ΛR ν a
    have ha := PowerWordWeightWhiskering.append_family_arrow D Sc cutoff L ΛR ν ν i
      (PowerWordWeight.wordWeight D ΛR ν) (PowerWordWeight.wordWeight D ΛR (ν ++ [i]))
      rfl rfl rfl rfl (PowerWordWeight.wordWeight_append D ΛR ν i) rfl
      (coefficientEndomorphism D Sc cutoff ν (SKM.SYM.elvCoefficientQuotient D cutoff a))
    rw [append_coefficientEndomorphism] at ha
    have hs : E.map (f.total P₀) ≫ (TensorVacuumWords.dotChart D Sc m cutoff L ΛP ΛR ν i).hom =
        (TensorVacuumWords.dotChart D Sc m cutoff L ΛP ΛR ν i).hom ≫
          PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L ΛR
            (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) (ν ++ [i]) (ν ++ [i])
            (coefficientEndomorphism D Sc cutoff (ν ++ [i])
              (SKM.SYM.elvCoefficientQuotient D cutoff a)) := by
      rw [dotChart_hom]
      simpa only [Iso.trans_hom, Functor.mapIso_hom] using
        (mapped_square E.toFunctor (TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR ν)
          (PowerWordWeight.weightAppendIso D Sc cutoff L ΛR ν i) _ _ _ ih ha)
    have ht : (Superfunctor.whiskerRight f E).total P₀ = E.map (f.total P₀) := by
      change E.map (f.app 0 P₀) + E.map (f.app 1 P₀) = E.map (f.app 0 P₀ + f.app 1 P₀)
      exact E.toFunctor.map_add.symm
    rw [← ht] at hs
    exact square_transport D Sc m cutoff L ΛP ΛR
      (TensorVacuumWords.wordHom_append D Sc m cutoff L ΛP ΛR ν i).symm
      (wordAction_append_heq D Sc m cutoff L ΛP ΛR ν i a).symm
      (TensorVacuumWords.dotChart D Sc m cutoff L ΛP ΛR ν i).hom
      (TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR (ν ++ [i])).hom
      (TensorVacuumWords.chart_append_heq D Sc m cutoff L ΛP ΛR ν i).symm _ hs

end OddMath.QuiverHecke.ELV.TensorWordCoefficientChart
end

end

section

/-! # The normalized inverse cap on the tensor vacuum

SwappedVacuumCoordinates §6: transport the prescribed regular power-vacuum
cap through the actual even tensor-vacuum isomorphism. Inverse-row
uniqueness identifies the result with the given native boundary inverse.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor
universe u v w

private theorem inverseRow_even_iso
    {k : Type u} {C : Type v} [CommRing k] [Category.{w} C] [Preadditive C]
    [Linear k C] [Supercategory k C] {A₀ A₁ B Z₀ Z₁ : C}
    {g₀ : ℕ → (Z₀ ⟶ A₀)} {g₁ : ℕ → (Z₁ ⟶ A₁)}
    {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
    (J₀ : SKM.SuperSumInvFrom (k := k) (0 : B ⟶ A₀) g₀ p q n)
    (J₁ : SKM.SuperSumInvFrom (k := k) (0 : B ⟶ A₁) g₁ p q n)
    (a : A₀ ≅ A₁) (z : Z₀ ≅ Z₁)
    (hg : ∀ m, m < n → g₀ m ≫ a.hom = z.hom ≫ g₁ m)
    (r : ℕ) (hr : r < n) :
    J₀.g' r = a.hom ≫ J₁.g' r ≫ z.inv := by
  have h := J₀.row_intertwine J₁ a.hom (𝟙 B) z.hom 0
    (by simp only [Limits.zero_comp, Limits.comp_zero, smul_zero])
    (fun m hm => by simpa only [koszulSign_zero_right, one_smul] using hg m hm) r hr
  simp only [koszulSign_zero_right, one_smul] at h
  have hc := congrArg (fun f => f ≫ z.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hc.symm

private theorem chronological_pow_intertwine
    {C : Type v} [Category.{w} C] {A B : C} (x : End A) (y : End B) (f : A ⟶ B)
    (h : x ≫ f = f ≫ y) (n : ℕ) : (x ^ n) ≫ f = f ≫ (y ^ n) := by
  induction n with
  | zero => simp only [pow_zero, End.one_def, Category.id_comp, Category.comp_id]
  | succ n ih =>
    calc
      (x ^ (n + 1)) ≫ f = x ≫ ((x ^ n) ≫ f) := by
        rw [pow_succ, End.mul_def, Category.assoc]
      _ = x ≫ (f ≫ (y ^ n)) := congrArg (fun g => x ≫ g) ih
      _ = (x ≫ f) ≫ (y ^ n) := (Category.assoc _ _ _).symm
      _ = (f ≫ y) ≫ (y ^ n) := congrArg (fun g => g ≫ (y ^ n)) h
      _ = f ≫ (y ^ (n + 1)) := by rw [pow_succ, End.mul_def, Category.assoc]

private theorem unitDotColumn_input_even
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    {M P : Superfunctor k C (SVec k)} (f : M ⟶ P)
    (hf : f ∈ parity (R := k) M P 0) (n : ℕ) :
    unitDotColumn J hα M n ≫ (restriction J).map ((induction J).map f) =
      f ≫ unitDotColumn J hα P n := by
  have hd := (transformComponent_supernatural hα).naturality hf
  rw [mul_zero, sign_zero, one_smul] at hd
  change (induction J).map f ≫ dotEnd J hα P = dotEnd J hα M ≫ (induction J).map f at hd
  have hp := chronological_pow_intertwine (dotEnd J hα M) (dotEnd J hα P)
    ((induction J).map f) hd.symm n
  have hu := (adjunction J).unit.naturality f
  change f ≫ (adjunction J).unit.app P =
    (adjunction J).unit.app M ≫ (restriction J).map ((induction J).map f) at hu
  unfold unitDotColumn
  rw [Category.assoc, ← Functor.map_comp, hp, Functor.map_comp, ← Category.assoc, ← hu,
    Category.assoc]

private theorem inverseIso_cancel_right
    {C : Type v} [Category.{w} C] {A B V W : C} (a : V ≅ B) (f : A ⟶ W) (g : W ⟶ B) :
    (f ≫ g ≫ a.inv) ≫ a.hom = f ≫ g := by
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem unit_column_window_to_powers
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (ell : (restriction J).obj (induced J M) ⟶ M)
    (n : ℕ) (t : M ⟶ M) (h : unitDotColumn J hα M n ≫ ell = t) :
    (adjunction J).unit.app M ≫ (restrictedDotEnd J hα M ^ n) ≫ ell = t := by
  rw [← Category.assoc, ← unitDotColumn_eq_restrictedDotEnd J hα M n]
  exact h

namespace PowerVacuumCoefficient
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (m : I → ℕ) (cutoff : I → ℕ) (L : I × ℕ → ℕ) (i : I)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "WM" => weightedVacuum D Sc cutoff L
local notation "Q₀" => contentInclusion D Sc cutoff bound (0 : Multiset I)
local notation "W₀" => Functor.obj (restriction Q₀) WM
local notation "H" => VacuumTensor.probeFunctor D Sc m cutoff bound W₀
local notation "V" => Superfunctor.obj H (probeOldVacuumRegular D Sc m)
local notation "K" => contentAppendTo D Sc cutoff bound (0 : Multiset I) [i]
  ((0 : Multiset I) + ([i] : Multiset I)) (contentBlockCanonicalSum 0 [i])
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff bound 0 i
local notation "G" => induction K ⋙ restriction K
local notation "e" => VacuumTensor.probeVacuumIso D Sc m cutoff bound W₀

/-- The normalized cap on the exact tensor-vacuum carrier, using the even
evaluation isomorphism and the original regular power-vacuum cap. -/
def tensorPowerVacuumCap (hN : 0 < cutoff i) : (G).obj V ⟶ V :=
  (G).map (e).hom ≫ contentPowerVacuumCap D Sc cutoff i L hN ≫ (e).inv

/-- This transported cap is literally the final row of the constructed
native unit-column inverse on H(N0), rather than an arbitrary extractor. -/
theorem tensorPowerVacuumCap_eq_inverseRow (hN : 0 < cutoff i)
    (J : SKM.SuperSumInvFrom (k := k)
      (0 : elvZeroModule D Sc cutoff bound (0 : Multiset I) ⟶ (G).obj V)
      (unitDotColumn K hDot V) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i 0)) :
    tensorPowerVacuumCap D Sc m cutoff L i hN = J.g' (cutoff i - 1) := by
  let JW := Classical.choice (contentAbsentUnitInverse_nonempty D Sc cutoff bound 0 i (by simp) W₀)
  have hr : cutoff i - 1 < contentUnitCount D cutoff i 0 := by
    simp only [contentUnitCount, contentCrossingHeight, Multiset.map_zero,
      Multiset.sum_zero, sub_zero, Int.toNat_natCast]
    omega
  have hc := inverseRow_even_iso J JW ((G).mapIso e) e
    (fun a _ => unitDotColumn_input_even K hDot (e).hom
      (VacuumTensor.probeVacuumIso_hom_mem D Sc m cutoff bound W₀) a) (cutoff i - 1) hr
  have hW := contentPowerVacuumCap_eq_inverseRow D Sc cutoff i L hN JW
  rw [← hW] at hc
  exact hc.symm

/-- The native inverse cap commutes with the genuine evaluation coordinate
as a whole module square. Thus its scalar decoding is the same literal-T
lambda already attached to the regular power vacuum. -/
theorem tensorPowerVacuumCap_compare (hN : 0 < cutoff i) :
    tensorPowerVacuumCap D Sc m cutoff L i hN ≫ (e).hom =
      (G).map (e).hom ≫ contentPowerVacuumCap D Sc cutoff i L hN :=
  inverseIso_cancel_right e ((G).map (e).hom) (contentPowerVacuumCap D Sc cutoff i L hN)

/-- The prescribed tensor-vacuum unit/dot columns have the exact normalized
cap window on every coefficient vector. -/
theorem tensorPowerVacuumCap_unitDotColumn (hN : 0 < cutoff i)
    (a : ℕ) (ha : a < cutoff i) :
    unitDotColumn K hDot V a ≫ tensorPowerVacuumCap D Sc m cutoff L i hN =
      if a + 1 = cutoff i then 𝟙 V else 0 := by
  let J := Classical.choice (contentAbsentUnitInverse_nonempty D Sc cutoff bound 0 i (by simp) V)
  rw [tensorPowerVacuumCap_eq_inverseRow D Sc m cutoff L i hN J]
  have hc : contentUnitCount D cutoff i (0 : Multiset I) = cutoff i := by
    simp only [contentUnitCount, contentCrossingHeight, Multiset.map_zero,
      Multiset.sum_zero, sub_zero, Int.toNat_natCast]
  have hw := J.gg a (cutoff i - 1) (by omega) (by omega)
  exact hw.trans (if_congr (by omega) rfl rfl)

/-- The exact unit/dot/extractor window required by InverseCapMoments,
now on the same tensor-vacuum module as the evaluated mixed bend. -/
theorem tensorPowerVacuumCap_window (hN : 0 < cutoff i)
    (a : ℕ) (ha : a < cutoff i) :
    (adjunction K).unit.app V ≫ (restrictedDotEnd K hDot V ^ a) ≫
      tensorPowerVacuumCap D Sc m cutoff L i hN =
      if a + 1 = cutoff i then 𝟙 V else 0 :=
  unit_column_window_to_powers K hDot V _ a _
    (tensorPowerVacuumCap_unitDotColumn D Sc m cutoff L i hN a ha)

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELV
end

end

section

/-! # All-power moments on the prescribed tensor vacuum

SwappedVacuumNonpositiveBubbles §2 (7) and §§3–4 (11): attach the
full coefficient moments to the given tensor-vacuum unit, restricted dot
and normalized native inverse cap. The even vacuum and content charts
are retained; no mixed inverse or normalized bubble identification is
assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor
universe u v w

private theorem restriction_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (w : C) :
    ((restriction J).map f).total w = f.total (J.obj w) := rfl

private theorem transport_end_value
    {k C U : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [AddCommGroup U] [Module k U]
    (F G : Superfunctor k C (SVec k)) (w : C) (e : F ≅ G) (c : U ≃ₗ[k] G.obj w)
    (f : End F) (g : End G) (h : f ≫ e.hom = e.hom ≫ g)
    (T : Module.End k U) (hg : ∀ a, c.symm (g.total w (c a)) = T a) (z : F.obj w) :
    c.symm (e.hom.total w (f.total w z)) = T (c.symm (e.hom.total w z)) := by
  have hv := congrArg (fun t => t.total w z) h
  simp only [Superfunctor.comp_total, SVec.comp_apply] at hv
  rw [hv]
  have ht := hg (c.symm (e.hom.total w z))
  simpa only [LinearEquiv.apply_symm_apply] using ht

private def endValueLinear
    {k C U : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [AddCommGroup U] [Module k U]
    (F : Superfunctor k C (SVec k)) (w : C) (decode : F.obj w →ₗ[k] U) (z : F.obj w) :
    End F →ₗ[k] U :=
  decode.comp ((LinearMap.applyₗ (R := k) (M := F.obj w) (M₂ := F.obj w) z).comp
    ((svecEndEvaluation (F.obj w)).toLinearMap.comp (supernaturalTotalLinearMap F F w)))

private theorem column_input_even
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    {M P : Superfunctor k C (SVec k)} (f : M ⟶ P)
    (hf : f ∈ parity (R := k) M P 0) (n : ℕ) :
    unitDotColumn J hα M n ≫ (restriction J).map ((induction J).map f) =
      f ≫ unitDotColumn J hα P n := by
  have hd := (transformComponent_supernatural hα).naturality hf
  rw [mul_zero, sign_zero, one_smul] at hd
  change (induction J).map f ≫ dotEnd J hα P =
    dotEnd J hα M ≫ (induction J).map f at hd
  have hp (a : ℕ) : (dotEnd J hα M ^ a) ≫ (induction J).map f =
      (induction J).map f ≫ (dotEnd J hα P ^ a) := by
    induction a with
    | zero => simp only [pow_zero, End.one_def, Category.id_comp, Category.comp_id]
    | succ a ih =>
      calc
        (dotEnd J hα M ^ (a + 1)) ≫ (induction J).map f =
            dotEnd J hα M ≫ ((dotEnd J hα M ^ a) ≫ (induction J).map f) := by
          rw [pow_succ, End.mul_def, Category.assoc]
        _ = dotEnd J hα M ≫ ((induction J).map f ≫ (dotEnd J hα P ^ a)) :=
          congrArg (fun g => dotEnd J hα M ≫ g) ih
        _ = (dotEnd J hα M ≫ (induction J).map f) ≫ (dotEnd J hα P ^ a) :=
          (Category.assoc _ _ _).symm
        _ = ((induction J).map f ≫ dotEnd J hα P) ≫ (dotEnd J hα P ^ a) :=
          congrArg (fun g => g ≫ (dotEnd J hα P ^ a)) hd.symm
        _ = (induction J).map f ≫ (dotEnd J hα P ^ (a + 1)) := by
          rw [pow_succ, End.mul_def, Category.assoc]
  have hu := (adjunction J).unit.naturality f
  change f ≫ (adjunction J).unit.app P =
    (adjunction J).unit.app M ≫ (restriction J).map ((induction J).map f) at hu
  unfold unitDotColumn
  rw [Category.assoc, ← Functor.map_comp, hp, Functor.map_comp, ← Category.assoc,
    ← hu, Category.assoc]

namespace PowerVacuumCoefficient
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (m cutoff : I → ℕ) (L : I × ℕ → ℕ)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "WM" => weightedVacuum D Sc cutoff L
local notation "Q₀" => contentInclusion D Sc cutoff bound (0 : Multiset I)
local notation "W₀" => Functor.obj (restriction Q₀) WM
local notation "H" => VacuumTensor.probeFunctor D Sc m cutoff bound W₀
private def tensorVacuumValue : ContentModules D Sc cutoff bound 0 :=
  Superfunctor.obj H (probeOldVacuumRegular D Sc m)
local notation "V" => tensorVacuumValue D Sc m cutoff L
private abbrev vacuumPoint : ContentCategory D Sc cutoff bound 0 := ⟨⟨[]⟩, rfl⟩
local notation "star" => vacuumPoint D Sc cutoff L
private def tensorVacuumIso : tensorVacuumValue D Sc m cutoff L ≅ W₀ :=
  VacuumTensor.probeVacuumIso D Sc m cutoff bound W₀
local notation "e" => tensorVacuumIso D Sc m cutoff L
local notation "AQ" => CoefficientPowerQuotient (k := k) D cutoff L
variable (i : I)
local notation "K" => contentAppendTo D Sc cutoff bound (0 : Multiset I) [i]
  ((0 : Multiset I) + ([i] : Multiset I)) (contentBlockCanonicalSum 0 [i])
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff bound 0 i
local notation "T" => truncatedAppend D Sc cutoff bound [i]

/-- The original empty coefficient chart, with the selected content
module endpoint retained in its type. -/
private def tensorVacuumCoefficientEquiv : AQ ≃ₗ[k] (W₀).obj star :=
  weightedEmptyEquiv D Sc cutoff L

/-- The original full coefficient decoder on the actual tensor value. -/
def tensorVacuumDecodeLinear : (V).obj star →ₗ[k] AQ :=
  (tensorVacuumCoefficientEquiv D Sc cutoff L).symm.toLinearMap ∘ₗ
    SVec.toLinearMap ((e).hom.total star)

/-- Its input is the prescribed tensor with the regular probe scalar
unit, before applying any cap or dot. -/
def tensorVacuumInputLinear : AQ →ₗ[k] (V).obj star where
  toFun a := tensorVacuumCoefficientEquiv D Sc cutoff L a ⊗ₜ[k] probeVacuumScalarEquiv D Sc m 1
  map_add' a b := by simp only [map_add, TensorProduct.add_tmul]
  map_smul' r a := by
    rw [map_smul]
    exact (TensorProduct.smul_tmul' r (tensorVacuumCoefficientEquiv D Sc cutoff L a)
      (probeVacuumScalarEquiv D Sc m 1)).symm

/-- The input chart is the literal given unit tensor under the existing
even tensor-vacuum isomorphism. -/
theorem tensorVacuumInput_chart (a : AQ) :
    (e).hom.total star (tensorVacuumInputLinear D Sc m cutoff L a) =
      tensorVacuumCoefficientEquiv D Sc cutoff L a :=
  VacuumTensor.probeVacuumIso_hom_tmul D Sc m cutoff bound W₀ star _

/-- Every coefficient vector is recovered from this original tensor input. -/
theorem tensorVacuumDecode_input (a : AQ) :
    tensorVacuumDecodeLinear D Sc m cutoff L (tensorVacuumInputLinear D Sc m cutoff L a) = a := by
  change (tensorVacuumCoefficientEquiv D Sc cutoff L).symm
    ((e).hom.total star (tensorVacuumInputLinear D Sc m cutoff L a)) = a
  rw [tensorVacuumInput_chart, LinearEquiv.symm_apply_apply]

/-- Every native tensor vector is the prescribed unit tensor in these
coordinates; the input chart is an actual inverse, not a replacement input. -/
theorem tensorVacuumInput_decode (z : (V).obj star) :
    tensorVacuumInputLinear D Sc m cutoff L (tensorVacuumDecodeLinear D Sc m cutoff L z) = z := by
  apply (moduleIsoLinearEquiv e star).injective
  change (e).hom.total star
    (tensorVacuumInputLinear D Sc m cutoff L (tensorVacuumDecodeLinear D Sc m cutoff L z)) =
      (e).hom.total star z
  rw [tensorVacuumInput_chart]
  exact (tensorVacuumCoefficientEquiv D Sc cutoff L).apply_symm_apply _

/-- Decoding retains the exact existing vacuum and empty charts. -/
theorem tensorVacuumDecodeLinear_apply (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L z =
      (tensorVacuumCoefficientEquiv D Sc cutoff L).symm ((e).hom.total star z) := rfl

/-- Every literal unit/dot/cap closure commutes with the even tensor
chart and the actual supported-content chart, at all powers. -/
theorem tensorPowerVacuumCap_moment_square (hN : 0 < cutoff i) (n : ℕ) :
    unitDotColumn K hDot V n ≫ tensorPowerVacuumCap D Sc m cutoff L i hN ≫ (e).hom =
      (e).hom ≫ (restriction Q₀).map
        (unitDotColumn T (truncatedDot_supernatural D Sc cutoff bound i) WM n) ≫
          weightedCoefficientCap D Sc cutoff i L hN := by
  calc
    _ = (e).hom ≫ unitDotColumn K hDot W₀ n ≫
        contentPowerVacuumCap D Sc cutoff i L hN := by
      have hc := column_input_even K hDot (e).hom
        (VacuumTensor.probeVacuumIso_hom_mem D Sc m cutoff bound W₀) n
      have h := congrArg (fun f => f ≫ contentPowerVacuumCap D Sc cutoff i L hN) hc
      have hcap : tensorPowerVacuumCap D Sc m cutoff L i hN ≫ (e).hom =
          (induction K ⋙ restriction K).map (e).hom ≫ contentPowerVacuumCap D Sc cutoff i L hN := by
        simpa only [tensorVacuumIso, tensorVacuumValue] using
          tensorPowerVacuumCap_compare D Sc m cutoff L i hN
      rw [hcap]
      simpa only [Functor.comp_map, Category.assoc, tensorVacuumValue, tensorVacuumIso] using h
    _ = _ := by
      have h := congrArg (fun f => (e).hom ≫ f ≫ weightedCoefficientCap D Sc cutoff i L hN)
        (contentVacuumTargetIso_unitDotColumn D Sc cutoff bound i WM
          (weightedVacuum_contentSupported D Sc cutoff L) n)
      simpa only [contentPowerVacuumCap, Category.assoc, tensorVacuumIso] using h

private def tensorVacuumCap (hN : 0 < cutoff i) :
    (restriction K).obj ((induction K).obj V) ⟶ V :=
  tensorPowerVacuumCap D Sc m cutoff L i hN

/-- The given unit/dot column closed by the same normalized inverse cap. -/
def tensorUnitCapClosure (hN : 0 < cutoff i) (n : ℕ) : End V :=
  unitDotColumn K hDot V n ≫ tensorVacuumCap D Sc m cutoff L i hN

private def weightedUnitCapClosure (hN : 0 < cutoff i) (n : ℕ) : End W₀ :=
  (restriction Q₀).map (unitDotColumn T (truncatedDot_supernatural D Sc cutoff bound i) WM n) ≫
    weightedCoefficientCap D Sc cutoff i L hN

private theorem weightedUnitCapClosure_value (hN : 0 < cutoff i) (n : ℕ) (a : AQ) :
    (tensorVacuumCoefficientEquiv D Sc cutoff L).symm
      ((weightedUnitCapClosure D Sc cutoff L i hN n).total star
        (tensorVacuumCoefficientEquiv D Sc cutoff L a)) =
      weightedMomentMap D Sc cutoff L i hN n a := by
  have h := (weightedFunctional_coefficientCap D Sc cutoff i L hN
    ((unitDotColumn T (truncatedDot_supernatural D Sc cutoff bound i) WM n).total
      ((oldTruncateFunctor D Sc cutoff bound).obj ⟨[]⟩) (weightedEmptyEquiv D Sc cutoff L a))).symm
  dsimp only [weightedUnitCapClosure, tensorVacuumCoefficientEquiv, weightedMomentMap]
  simp only [Superfunctor.comp_total, SVec.comp_apply, restriction_total,
    LinearMap.comp_apply, LinearEquiv.coe_coe, SVec.toLinearMap,
    contentInclusion, oldTruncateFunctor, vacuumPoint] at h ⊢
  convert! h using 1

/-- Every native tensor vector has the existing full-coefficient moment
of the actual prescribed unit, dot and normalized inverse cap. -/
theorem tensorPowerVacuumCap_moment_weighted (hN : 0 < cutoff i) (n : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
      ((tensorUnitCapClosure D Sc m cutoff L i hN n).total star z) =
      weightedMomentMap D Sc cutoff L i hN n (tensorVacuumDecodeLinear D Sc m cutoff L z) := by
  have hs : tensorUnitCapClosure D Sc m cutoff L i hN n ≫ (e).hom =
      (e).hom ≫ weightedUnitCapClosure D Sc cutoff L i hN n := by
    simpa only [tensorUnitCapClosure, tensorVacuumCap, weightedUnitCapClosure, Category.assoc] using
      tensorPowerVacuumCap_moment_square D Sc m cutoff L i hN n
  have h := transport_end_value V W₀ star e (tensorVacuumCoefficientEquiv D Sc cutoff L)
    (tensorUnitCapClosure D Sc m cutoff L i hN n) (weightedUnitCapClosure D Sc cutoff L i hN n)
    hs (weightedMomentMap D Sc cutoff L i hN n)
    (weightedUnitCapClosure_value D Sc cutoff L i hN n) z
  simpa only [tensorVacuumDecodeLinear_apply] using h

/-- The moment formula keeps every homogeneous and inhomogeneous input,
with the original scalar coefficient on the left. -/
theorem tensorPowerVacuumCap_moment_apply (hN : 0 < cutoff i) (n : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
      ((tensorUnitCapClosure D Sc m cutoff L i hN n).total star z) =
      signedMoment D Sc cutoff L i hN n * tensorVacuumDecodeLinear D Sc m cutoff L z := by
  rw [tensorPowerVacuumCap_moment_weighted, weightedMomentMap_apply]

/-- The even-index odd-colour series is the complete raw reservoir series. -/
theorem tensorPowerVacuumCap_moment_even (hi : D.parity i = 1) (hN : 0 < cutoff i)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
      ((tensorUnitCapClosure D Sc m cutoff L i hN (cutoff i - 1 + 2 * r)).total star z) =
      completeCoefficient D cutoff L i r * tensorVacuumDecodeLinear D Sc m cutoff L z := by
  rw [tensorPowerVacuumCap_moment_weighted, weightedMomentMap_even D Sc cutoff L i hi hN r]
  rfl

/-- The odd series retains the original exterior coefficient and cutoff
normalization sign, before any independent bubble identification. -/
theorem tensorPowerVacuumCap_moment_odd (hi : D.parity i = 1) (hN : 0 < cutoff i)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
      ((tensorUnitCapClosure D Sc m cutoff L i hN (cutoff i - 1 + (2 * r + 1))).total star z) =
      ((-1 : k) ^ (cutoff i + 1) •
        (coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩) *
          completeCoefficient D cutoff L i r)) * tensorVacuumDecodeLinear D Sc m cutoff L z := by
  rw [tensorPowerVacuumCap_moment_weighted, weightedMomentMap_odd D Sc cutoff L i hi hN r]
  rfl

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELV
end

end
