import OddMath.QuiverHecke.HalfTurn.PowerWordLayerClasses
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.PowerWordLayerClasses

namespace TwoOdd
private abbrev D := AsymmetricParameters.datum
private abbrev Sc := AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 20
private abbrev ν : List Bool := [false]
private abbrev η : List Bool := [true]
private abbrev s (i j : Bool) : List Bool := (η.reverse ++ [i,j]) ++ ν.reverse
private abbrev t (i j : Bool) : List Bool := (η.reverse ++ [j,i]) ++ ν.reverse
private abbrev d : List Bool := (η.reverse ++ [true]) ++ ν.reverse
private def identityNF (w : List Bool) : NFIdx w w := by
  have hc : Categorification.TypeA.canWord w.length (1 : Equiv.Perm (Fin w.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([],1), by simp, by simp, ?_⟩
  simp only [List.map_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]
private def oddIndex : SKM.SYM.CoefficientIndex D := (0,{⟨false,rfl⟩,⟨true,rfl⟩})
private def occupied (w : List Bool) : ExtendedAtMost D Sc w w 2 :=
  ⟨extensionBasis D Sc w w (oddIndex,identityNF w),
    Submodule.subset_span ⟨(oddIndex,identityNF w), by
      change SKM.SYM.coefficientWeight D oddIndex + 0 ≤ 2
      decide, rfl⟩⟩
private def v (w : List Bool) := powerWordHalfTurnCoordinate D Sc cutoff L w w (occupied w).val
private theorem powers_high (q : Bool × ℕ) : 16 ≤ L q * SKM.SYM.elementaryWeight D q := by
  have hw : 0 < SKM.SYM.elementaryWeight D q := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  change 16 ≤ 20 * SKM.SYM.elementaryWeight D q
  omega
private theorem v_ne_zero (w : List Bool) (hw : 2 + 2 * w.length.choose 2 < 16) : v w ≠ 0 := by
  intro hz
  have hi := powerWordHalfTurnCoordinate_injective_on_extendedAtMost D Sc cutoff L
    (s := w) (t := w) (d := 2) (N := 16) (fun _ => (by decide : 16 ≤ 20)) powers_high hw
  have he : occupied w = 0 := hi (by
    change powerWordHalfTurnCoordinate D Sc cutoff L w w (occupied w).val =
      powerWordHalfTurnCoordinate D Sc cutoff L w w 0
    exact hz.trans (map_zero _).symm)
  exact (extensionBasis D Sc w w).ne_zero (oddIndex,identityNF w) (congrArg Subtype.val he)
private def physicalDot : (OldCategory.mk d.reverse : OldCategory D (parameterTwist D Sc) cutoff) ⟶
    OldCategory.mk d.reverse :=
  ContextualOldGenerators.transport D (parameterTwist D Sc) cutoff
    (by simp [PowerWordContexts.extendedWord_eq, List.append_assoc])
    (by simp [PowerWordContexts.extendedWord_eq, List.append_assoc])
    (PowerWordContexts.extendedArrow D (parameterTwist D Sc) cutoff (ν ++ [true]) (ν ++ [true]) η
      (CyclotomicCrossingTensor.oldAppendDotComponent D (parameterTwist D Sc) cutoff true (OldCategory.mk ν)))
private def physicalCross (i j : Bool) :
    (OldCategory.mk (t i j).reverse : OldCategory D (parameterTwist D Sc) cutoff) ⟶ OldCategory.mk (s i j).reverse :=
  ContextualOldGenerators.transport D (parameterTwist D Sc) cutoff
    (by simp [PowerWordContexts.extendedWord_eq, List.append_assoc])
    (by simp [PowerWordContexts.extendedWord_eq, List.append_assoc])
    (PowerWordContexts.extendedArrow D (parameterTwist D Sc) cutoff ((ν ++ [j]) ++ [i]) ((ν ++ [i]) ++ [j]) η
      (PowerWordContentCross.normalizedOldCross D (parameterTwist D Sc) cutoff ν i j))
private abbrev originalDot := sourceCoefficientHom D Sc 1
  (ContextualOldGenerators.layerDiagram D Sc η.reverse (.dot true) ν.reverse)
private abbrev originalCross (i j : Bool) := sourceCoefficientHom D Sc 1
  (ContextualOldGenerators.layerDiagram D Sc η.reverse (.cross i j) ν.reverse)
private theorem dot_table : halfTurnOldHom D Sc cutoff d d originalDot = physicalDot :=
  ContextualOldGenerators.dot D Sc cutoff ν η true
private theorem cross_table (i j : Bool) :
    halfTurnOldHom D Sc cutoff (s i j) (t i j) (originalCross i j) = physicalCross i j :=
  ContextualOldGenerators.cross D Sc cutoff ν η i j

/-- Both contexts are nonempty; the input coefficient vectors survive. -/
example : ν ≠ [] ∧ η ≠ [] := by decide
example : v d ≠ 0 := v_ne_zero d (by decide)
example (i j : Bool) : v (s i j) ≠ 0 := v_ne_zero (s i j)
  (by change 2 + 2 * (4 : ℕ).choose 2 < 16; decide)
example := cross_table false false
example := cross_table false true
/-- The original source class of an arbitrary actual physical contextual
crossing is recovered on the supplied nonzero exterior input. -/
example (i j : Bool) : PowerWordQuotientCoordinates.coordinate D Sc cutoff L (s i j) (t i j)
    ((PowerWordMorphisms.fromArrow D (parameterTwist D Sc) cutoff L (s i j).reverse (t i j).reverse
      (physicalCross i j)).total (OldCategory.mk (s i j).reverse) (v (s i j))) =
    (PowerWordQuotientCoordinates.kernel D Sc cutoff L (s i j) (t i j)).mkQ
      ((occupied (s i j)).val ≫ originalCross i j) := by
  rw [← cross_table]
  change PowerWordQuotientCoordinates.coordinate D Sc cutoff L (s i j) (t i j)
    ((PowerWordComposition.sourceMap D Sc cutoff L (s i j) (t i j) (originalCross i j)).total _ (v (s i j))) = _
  exact PowerWordQuotientCoordinates.coordinate_action D Sc cutoff L _ _ _
    (PowerWordQuotientCoordinates.coordinate_mk D Sc cutoff L (s i j) (s i j) (occupied (s i j)).val)
example : PowerWordQuotientCoordinates.coordinate D Sc cutoff L d d
    ((PowerWordMorphisms.fromArrow D (parameterTwist D Sc) cutoff L d.reverse d.reverse physicalDot).total
      (OldCategory.mk d.reverse) (v d)) =
    (PowerWordQuotientCoordinates.kernel D Sc cutoff L d d).mkQ ((occupied d).val ≫ originalDot) := by
  rw [← dot_table]
  change PowerWordQuotientCoordinates.coordinate D Sc cutoff L d d
    ((PowerWordComposition.sourceMap D Sc cutoff L d d originalDot).total _ (v d)) = _
  exact PowerWordQuotientCoordinates.coordinate_action D Sc cutoff L _ _ _
    (PowerWordQuotientCoordinates.coordinate_mk D Sc cutoff L d d (occupied d).val)
/-- The literal table is a whole old-Hom equality, hence holds on every
vector, including vectors not supplied by a homogeneous source arrow. -/
example (i j : Bool) (w : OldCategory D (parameterTwist D Sc) cutoff)
    (z : (powerWordModule D (parameterTwist D Sc) cutoff L (s i j).reverse).obj w) :=
  congrArg (fun a : (OldCategory.mk (t i j).reverse : OldCategory D (parameterTwist D Sc) cutoff) ⟶
      OldCategory.mk (s i j).reverse =>
    (PowerWordMorphisms.fromArrow D (parameterTwist D Sc) cutoff L (s i j).reverse (t i j).reverse a).total w z)
    (cross_table i j)

private def dotLayer : Layer (QuiverHecke.sig D) := QuiverHecke.lay D η.reverse (.dot true) ν.reverse
private def crossLayer (i j : Bool) : Layer (QuiverHecke.sig D) :=
  QuiverHecke.lay D η.reverse (.cross i j) ν.reverse
/-- The square uses the actual presentation diagram of the actual affine
layer, with both nonempty contexts and the supplied nonzero input vector. -/
example := PowerWordLayerClasses.affineLayer_eq D Sc dotLayer (Layer.valid_of_subsingleton dotLayer)
example (i j : Bool) := PowerWordLayerClasses.literalLayerMap_eq D Sc cutoff L (crossLayer i j)
  (Layer.valid_of_subsingleton (crossLayer i j))
example (i j : Bool) := PowerWordLayerClasses.affine_class_square D Sc cutoff L
  (crossLayer i j) (Layer.valid_of_subsingleton (crossLayer i j)) (s i j) (v (s i j)) (occupied (s i j)).val
  (PowerWordQuotientCoordinates.coordinate_mk D Sc cutoff L (s i j) (s i j) (occupied (s i j)).val)
example := PowerWordLayerClasses.affine_class_square D Sc cutoff L
  dotLayer (Layer.valid_of_subsingleton dotLayer) d (v d) (occupied d).val
  (PowerWordQuotientCoordinates.coordinate_mk D Sc cutoff L d d (occupied d).val)
/-- Every observation source word and every actual coefficient vector is
covered; the premise only specifies the input quotient class. -/
example (w : List Bool) (i j : Bool)
    (z : (powerWordModule D (parameterTwist D Sc) cutoff L (crossLayer i j).dom.word.reverse).obj
      (OldCategory.mk w.reverse))
    (y : coefficientObj D Sc w ⟶ coefficientObj D Sc (crossLayer i j).dom.word)
    (hy : PowerWordQuotientCoordinates.coordinate D Sc cutoff L w (crossLayer i j).dom.word z =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L w (crossLayer i j).dom.word).mkQ y) :=
  PowerWordLayerClasses.affine_class_square D Sc cutoff L (crossLayer i j)
    (Layer.valid_of_subsingleton (crossLayer i j)) w z y hy

end TwoOdd

namespace Mixed
private def D : SKM.Datum Bool (Bool → ℤ) :=
  { AsymmetricParameters.datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => AsymmetricParameters.datum.even_of_odd i j rfl }
private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 20
private abbrev ν : List Bool := [false]
private abbrev η : List Bool := [true]
private abbrev s (i j : Bool) : List Bool := (η.reverse ++ [i,j]) ++ ν.reverse
private abbrev t (i j : Bool) : List Bool := (η.reverse ++ [j,i]) ++ ν.reverse
private abbrev d : List Bool := (η.reverse ++ [true]) ++ ν.reverse
private def identityNF (w : List Bool) : NFIdx w w := by
  have hc : Categorification.TypeA.canWord w.length (1 : Equiv.Perm (Fin w.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([],1), by simp, by simp, ?_⟩
  simp only [List.map_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]
private def oddIndex : SKM.SYM.CoefficientIndex D := (0,{⟨true,rfl⟩})
private def occupied (w : List Bool) : ExtendedAtMost D Sc w w 2 :=
  ⟨extensionBasis D Sc w w (oddIndex,identityNF w),
    Submodule.subset_span ⟨(oddIndex,identityNF w), by
      change SKM.SYM.coefficientWeight D oddIndex + 0 ≤ 2
      decide, rfl⟩⟩
private def v (w : List Bool) := powerWordHalfTurnCoordinate D Sc cutoff L w w (occupied w).val
private theorem powers_high (q : Bool × ℕ) : 16 ≤ L q * SKM.SYM.elementaryWeight D q := by
  have hw : 0 < SKM.SYM.elementaryWeight D q := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  change 16 ≤ 20 * SKM.SYM.elementaryWeight D q
  omega
private theorem v_ne_zero (w : List Bool) (hw : 2 + 2 * w.length.choose 2 < 16) : v w ≠ 0 := by
  intro hz
  have hi := powerWordHalfTurnCoordinate_injective_on_extendedAtMost D Sc cutoff L
    (s := w) (t := w) (d := 2) (N := 16) (fun _ => (by decide : 16 ≤ 20)) powers_high hw
  have he : occupied w = 0 := hi (by
    change powerWordHalfTurnCoordinate D Sc cutoff L w w (occupied w).val =
      powerWordHalfTurnCoordinate D Sc cutoff L w w 0
    exact hz.trans (map_zero _).symm)
  exact (extensionBasis D Sc w w).ne_zero (oddIndex,identityNF w) (congrArg Subtype.val he)
private def physicalDot : (OldCategory.mk d.reverse : OldCategory D (parameterTwist D Sc) cutoff) ⟶
    OldCategory.mk d.reverse :=
  ContextualOldGenerators.transport D (parameterTwist D Sc) cutoff
    (by simp [PowerWordContexts.extendedWord_eq, List.append_assoc])
    (by simp [PowerWordContexts.extendedWord_eq, List.append_assoc])
    (PowerWordContexts.extendedArrow D (parameterTwist D Sc) cutoff (ν ++ [true]) (ν ++ [true]) η
      (CyclotomicCrossingTensor.oldAppendDotComponent D (parameterTwist D Sc) cutoff true (OldCategory.mk ν)))
private def physicalCross (i j : Bool) :
    (OldCategory.mk (t i j).reverse : OldCategory D (parameterTwist D Sc) cutoff) ⟶ OldCategory.mk (s i j).reverse :=
  ContextualOldGenerators.transport D (parameterTwist D Sc) cutoff
    (by simp [PowerWordContexts.extendedWord_eq, List.append_assoc])
    (by simp [PowerWordContexts.extendedWord_eq, List.append_assoc])
    (PowerWordContexts.extendedArrow D (parameterTwist D Sc) cutoff ((ν ++ [j]) ++ [i]) ((ν ++ [i]) ++ [j]) η
      (PowerWordContentCross.normalizedOldCross D (parameterTwist D Sc) cutoff ν i j))
private abbrev originalDot := sourceCoefficientHom D Sc 1
  (ContextualOldGenerators.layerDiagram D Sc η.reverse (.dot true) ν.reverse)
private abbrev originalCross (i j : Bool) := sourceCoefficientHom D Sc 1
  (ContextualOldGenerators.layerDiagram D Sc η.reverse (.cross i j) ν.reverse)
private theorem dot_table : halfTurnOldHom D Sc cutoff d d originalDot = physicalDot :=
  ContextualOldGenerators.dot D Sc cutoff ν η true
private theorem cross_table (i j : Bool) :
    halfTurnOldHom D Sc cutoff (s i j) (t i j) (originalCross i j) = physicalCross i j :=
  ContextualOldGenerators.cross D Sc cutoff ν η i j

/-- Both contexts are nonempty; the input coefficient vectors survive. -/
example : ν ≠ [] ∧ η ≠ [] := by decide
example : v d ≠ 0 := v_ne_zero d (by decide)
example (i j : Bool) : v (s i j) ≠ 0 := v_ne_zero (s i j)
  (by change 2 + 2 * (4 : ℕ).choose 2 < 16; decide)
example := cross_table true true
example := cross_table false true
/-- The original source class of an arbitrary actual physical contextual
crossing is recovered on the supplied nonzero exterior input. -/
example (i j : Bool) : PowerWordQuotientCoordinates.coordinate D Sc cutoff L (s i j) (t i j)
    ((PowerWordMorphisms.fromArrow D (parameterTwist D Sc) cutoff L (s i j).reverse (t i j).reverse
      (physicalCross i j)).total (OldCategory.mk (s i j).reverse) (v (s i j))) =
    (PowerWordQuotientCoordinates.kernel D Sc cutoff L (s i j) (t i j)).mkQ
      ((occupied (s i j)).val ≫ originalCross i j) := by
  rw [← cross_table]
  change PowerWordQuotientCoordinates.coordinate D Sc cutoff L (s i j) (t i j)
    ((PowerWordComposition.sourceMap D Sc cutoff L (s i j) (t i j) (originalCross i j)).total _ (v (s i j))) = _
  exact PowerWordQuotientCoordinates.coordinate_action D Sc cutoff L _ _ _
    (PowerWordQuotientCoordinates.coordinate_mk D Sc cutoff L (s i j) (s i j) (occupied (s i j)).val)
example : PowerWordQuotientCoordinates.coordinate D Sc cutoff L d d
    ((PowerWordMorphisms.fromArrow D (parameterTwist D Sc) cutoff L d.reverse d.reverse physicalDot).total
      (OldCategory.mk d.reverse) (v d)) =
    (PowerWordQuotientCoordinates.kernel D Sc cutoff L d d).mkQ ((occupied d).val ≫ originalDot) := by
  rw [← dot_table]
  change PowerWordQuotientCoordinates.coordinate D Sc cutoff L d d
    ((PowerWordComposition.sourceMap D Sc cutoff L d d originalDot).total _ (v d)) = _
  exact PowerWordQuotientCoordinates.coordinate_action D Sc cutoff L _ _ _
    (PowerWordQuotientCoordinates.coordinate_mk D Sc cutoff L d d (occupied d).val)
/-- The literal table is a whole old-Hom equality, hence holds on every
vector, including vectors not supplied by a homogeneous source arrow. -/
example (i j : Bool) (w : OldCategory D (parameterTwist D Sc) cutoff)
    (z : (powerWordModule D (parameterTwist D Sc) cutoff L (s i j).reverse).obj w) :=
  congrArg (fun a : (OldCategory.mk (t i j).reverse : OldCategory D (parameterTwist D Sc) cutoff) ⟶
      OldCategory.mk (s i j).reverse =>
    (PowerWordMorphisms.fromArrow D (parameterTwist D Sc) cutoff L (s i j).reverse (t i j).reverse a).total w z)
    (cross_table i j)

private def dotLayer : Layer (QuiverHecke.sig D) := QuiverHecke.lay D η.reverse (.dot true) ν.reverse
private def crossLayer (i j : Bool) : Layer (QuiverHecke.sig D) :=
  QuiverHecke.lay D η.reverse (.cross i j) ν.reverse
/-- The square uses the actual presentation diagram of the actual affine
layer, with both nonempty contexts and the supplied nonzero input vector. -/
example := PowerWordLayerClasses.affineLayer_eq D Sc dotLayer (Layer.valid_of_subsingleton dotLayer)
example (i j : Bool) := PowerWordLayerClasses.literalLayerMap_eq D Sc cutoff L (crossLayer i j)
  (Layer.valid_of_subsingleton (crossLayer i j))
example (i j : Bool) := PowerWordLayerClasses.affine_class_square D Sc cutoff L
  (crossLayer i j) (Layer.valid_of_subsingleton (crossLayer i j)) (s i j) (v (s i j)) (occupied (s i j)).val
  (PowerWordQuotientCoordinates.coordinate_mk D Sc cutoff L (s i j) (s i j) (occupied (s i j)).val)
example := PowerWordLayerClasses.affine_class_square D Sc cutoff L
  dotLayer (Layer.valid_of_subsingleton dotLayer) d (v d) (occupied d).val
  (PowerWordQuotientCoordinates.coordinate_mk D Sc cutoff L d d (occupied d).val)
/-- Every observation source word and every actual coefficient vector is
covered; the premise only specifies the input quotient class. -/
example (w : List Bool) (i j : Bool)
    (z : (powerWordModule D (parameterTwist D Sc) cutoff L (crossLayer i j).dom.word.reverse).obj
      (OldCategory.mk w.reverse))
    (y : coefficientObj D Sc w ⟶ coefficientObj D Sc (crossLayer i j).dom.word)
    (hy : PowerWordQuotientCoordinates.coordinate D Sc cutoff L w (crossLayer i j).dom.word z =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L w (crossLayer i j).dom.word).mkQ y) :=
  PowerWordLayerClasses.affine_class_square D Sc cutoff L (crossLayer i j)
    (Layer.valid_of_subsingleton (crossLayer i j)) w z y hy

end Mixed

end NonVacuity.PowerWordLayerClasses
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.HalfTurn.PowerWordLayerClasses
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
