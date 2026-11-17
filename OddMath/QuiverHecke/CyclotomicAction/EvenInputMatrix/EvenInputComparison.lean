import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Pi
import OddMath.Algebra.LowPolynomialCoordinates
import OddMath.QuiverHecke.CyclotomicAction.CapInputMatrices.ShiftedMatrixFamilies
import OddMath.QuiverHecke.CyclotomicAction.CapInputMatrices.UnitDotColumns
import OddMath.QuiverHecke.CyclotomicAction.EvenBoundaryRecurrence.EvenCoefficientModule

/-!
# Even input matrix

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Even counit and induction-dot input comparison
The canonical even source and ordinary adjunction counit/dot in
DeformedMatrixComparison §4 agree with the prescribed raw input operators.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The induction dot on the literal even-moving coefficient module. -/
def evenSourceInputDot (i : {i : I // D.parity i = 0}) (v t : List I) :
    Source D Sc cutoff i.1 v t →ₗ[k] Source D Sc cutoff i.1 v t :=
  inductionDot D Sc cutoff i.1 (evenMovingCoefficientModule D Sc cutoff i v)
    (⟨t⟩ : OldCategory D Sc cutoff)

theorem evenSourceInputDot_tensor (i : {i : I // D.parity i = 0})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [i.1]) t)
    (b : Old D Sc cutoff v (s ++ [i.1])) :
    evenSourceInputDot D Sc cutoff i v t (tensor D Sc cutoff i.1 v s t g b) =
      tensor D Sc cutoff i.1 v s t
        (oldAppendDotComponent D Sc cutoff i.1 (⟨s⟩ : OldCategory D Sc cutoff) ≫ g) b := by
  change inductionDot D Sc cutoff i.1 (evenMovingCoefficientModule D Sc cutoff i v) _
    (BalancedInduction.tensor _ _ _ g b) = _
  rw [inductionDot_tensor]
  have hg : twist k (D.parity i.1)
      (X := (append D Sc cutoff i.1).obj (⟨s⟩ : OldCategory D Sc cutoff))
      (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g = g := by
    rw [i.property, twist_zero]
  rw [hg]
  rfl

theorem evenSourceInputContraction_q (i : {i : I // D.parity i = 0}) (v t : List I)
    (z : ShortTarget D Sc cutoff i.1 v t) :
    evenSourceInputContraction D Sc cutoff i v t (q D Sc cutoff i.1 v t z) =
      evenInputContractionAffine D Sc cutoff i.1 v t z := by
  suffices h : (evenSourceInputContraction D Sc cutoff i v t).comp
      (q D Sc cutoff i.1 v t) = evenInputContractionAffine D Sc cutoff i.1 v t from
    LinearMap.congr_fun h z
  apply BalancedInduction.hom_ext
  intro s g b
  change evenSourceInputContraction D Sc cutoff i v t
    (q D Sc cutoff i.1 v t (shortTensor D Sc cutoff i.1 v s.word t g b)) = _
  rw [q_shortTensor, evenSourceInputContraction_tensor]
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i.1])).mkQ_surjective b
  change _ = appendC0InputDefect D Sc cutoff i.1 v t
    (shortCross D Sc cutoff i.1 v t
      (shortTensor D Sc cutoff i.1 v s.word t g ((ideal D Sc cutoff _ _).mkQ r))) 0
  rw [ShortCrossCoordinates.column_mk, appendC0InputDefect_crossing]
  simp only [Finsupp.neg_apply, Finsupp.single_eq_same, i.property, zero_mul,
    SKM.zsign_zero, twist_zero, neg_one_smul]
  rfl

theorem evenSourceInputDot_q (i : {i : I // D.parity i = 0}) (v t : List I)
    (z : ShortTarget D Sc cutoff i.1 v t) :
    evenSourceInputDot D Sc cutoff i v t (q D Sc cutoff i.1 v t z) =
      q D Sc cutoff i.1 v t (evenCrossingInputDotAffine D Sc cutoff i.1 v t z) := by
  suffices h : (evenSourceInputDot D Sc cutoff i v t).comp (q D Sc cutoff i.1 v t) =
      (q D Sc cutoff i.1 v t).comp (evenCrossingInputDotAffine D Sc cutoff i.1 v t) from
    LinearMap.congr_fun h z
  apply BalancedInduction.hom_ext
  intro s g b
  change evenSourceInputDot D Sc cutoff i v t
    (q D Sc cutoff i.1 v t (shortTensor D Sc cutoff i.1 v s.word t g b)) =
    q D Sc cutoff i.1 v t
      (evenCrossingInputDotAffine D Sc cutoff i.1 v t
        (shortTensor D Sc cutoff i.1 v s.word t g b))
  rw [q_shortTensor, evenSourceInputDot_tensor]
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i.1])).mkQ_surjective b
  rw [evenCrossingInputDotAffine_representative D Sc cutoff i.1 i.property,
    q_shortTensor, oldAppendDotComponent_eq]
  rfl

/-- Equality on all balanced classes, not only on chosen representatives. -/
theorem evenSourceInputContraction_eq (i : {i : I // D.parity i = 0}) (v t : List I) :
    evenSourceInputContraction D Sc cutoff i v t =
      evenInputContraction D Sc cutoff i.1 i.property v t := by
  apply LinearMap.ext
  intro z
  obtain ⟨a, rfl⟩ := q_surjective D Sc cutoff i.1 v t z
  rw [evenSourceInputContraction_q, evenInputContraction_q]

/-- The ordinary actual induction dot is the prescribed even input dot. -/
theorem evenSourceInputDot_eq (i : {i : I // D.parity i = 0}) (v t : List I) :
    evenSourceInputDot D Sc cutoff i v t =
      evenCrossingInputDot D Sc cutoff i.1 i.property v t := by
  apply LinearMap.ext
  intro z
  obtain ⟨a, rfl⟩ := q_surjective D Sc cutoff i.1 v t z
  rw [evenSourceInputDot_q, evenCrossingInputDot_q]

/-- The canonical source comparison intertwines the ordinary actual dot.
There is no parity conjugation or higher-row scalar for an even colour. -/
theorem evenSourceInputDot_sourceEquiv (i : {i : I // D.parity i = 0})
    (v t : List I)
    (z : (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff))) :
    evenSourceInputDot D Sc cutoff i v t (evenSourceEquiv D Sc cutoff i v t z) =
      evenSourceEquiv D Sc cutoff i v t
        (inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v)
          (⟨t⟩ : OldCategory D Sc cutoff) z) := by
  suffices h : (evenSourceInputDot D Sc cutoff i v t).comp
      (evenSourceEquiv D Sc cutoff i v t).toLinearMap =
      (evenSourceEquiv D Sc cutoff i v t).toLinearMap.comp
        (inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v)
          (⟨t⟩ : OldCategory D Sc cutoff)) from
    LinearMap.congr_fun h z
  apply BalancedInduction.hom_ext
  intro s g b
  change evenSourceInputDot D Sc cutoff i v t
    (evenSourceEquiv D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i.1)
        (restrictedRepresentable D Sc cutoff i.1 v).toFunctor s g b)) =
    evenSourceEquiv D Sc cutoff i v t
      (inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v) _
        (BalancedInduction.tensor _ _ s g b))
  rw [evenSourceEquiv_tensor, evenSourceInputDot_tensor, inductionDot_tensor]
  have hg : twist k (D.parity i.1)
      (X := (append D Sc cutoff i.1).obj s)
      (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g = g := by
    rw [i.property, twist_zero]
  rw [hg, evenSourceEquiv_tensor]

theorem evenSourceInputDot_iterate_sourceEquiv (i : {i : I // D.parity i = 0})
    (v t : List I) (n : ℕ) (z : (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff))) :
    (evenSourceInputDot D Sc cutoff i v t)^[n] (evenSourceEquiv D Sc cutoff i v t z) =
      evenSourceEquiv D Sc cutoff i v t ((inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v)
          (⟨t⟩ : OldCategory D Sc cutoff))^[n] z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, evenSourceInputDot_sourceEquiv,
      Function.iterate_succ_apply']

/-- Every even cap row has the same constant minus relative to the ordinary
adjunction counit, independently of the row index. -/
theorem evenCapRow_normalization (i : {i : I // D.parity i = 0})
    (v t : List I) (n : ℕ) (z : (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff))) :
    evenSourceInputContraction D Sc cutoff i v t
      ((evenSourceInputDot D Sc cutoff i v t)^[n] (evenSourceEquiv D Sc cutoff i v t z)) =
      -unshiftedCounitComponent D Sc cutoff i.1 v t ((inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v)
          (⟨t⟩ : OldCategory D Sc cutoff))^[n] z) := by
  rw [evenSourceInputDot_iterate_sourceEquiv, evenSourceInputContraction_counit]

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Cap pivots on even boundary lifts

The parity-zero input pivots in DeformedRouquierMatrix, section 4.
Decoded moving dots shift the ordinary long coordinates. The raw cap reads
the constant coefficient of the next boundary row. The actual arbitrary-Hom
leading theorem therefore gives the anti-diagonal unit and below-diagonal
vanishing, with every old coefficient and balance twist retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def evenLiftBoundary (p : ZMod 2) (i : I) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] AppendTarget D Sc cutoff i v (t ++ [i]) :=
  (pMap D Sc cutoff i v (t ++ [i])).comp (offDiagonalLongSection D Sc cutoff p i v t)

theorem evenLiftBoundary_shift (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    evenLiftBoundary D Sc cutoff p i v t (evenLongShift D Sc cutoff v t f) =
      appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1
        (evenLiftBoundary D Sc cutoff p i v t f) := by
  change pMap D Sc cutoff i v (t ++ [i]) (offDiagonalLongSection D Sc cutoff p i v t _) = _
  rw [← evenMoving_offDiagonalLongSection D Sc cutoff p i hi, pMap_movingEvenDot D Sc cutoff i hi]
  rfl

def evenBoundaryCrossCoordinates (p : ZMod 2) (i : I) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] ShortTarget D Sc cutoff i v t :=
  (ShortCrossCoordinates.decode D Sc cutoff i v t).comp (evenLiftBoundary D Sc cutoff p i v t)

theorem evenCrossingInputDotAffine_boundaryCrossCoordinates (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    evenCrossingInputDotAffine D Sc cutoff i v t (evenBoundaryCrossCoordinates D Sc cutoff p i v t f) =
      evenBoundaryCrossCoordinates D Sc cutoff p i v t (evenLongShift D Sc cutoff v t f) := by
  change ShortCrossCoordinates.decode D Sc cutoff i v t
    (appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1
      (shortCross D Sc cutoff i v t
        (ShortCrossCoordinates.decode D Sc cutoff i v t (evenLiftBoundary D Sc cutoff p i v t f)))) = _
  rw [shortCross_decode_residual, map_sub, appendMovingPowerTarget_embedding_one,
    map_sub, ShortCrossCoordinates.decode_embedding, sub_zero, ← evenLiftBoundary_shift D Sc cutoff p i hi]
  rfl

theorem evenInputContractionAffine_boundaryCrossCoordinates (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    evenInputContractionAffine D Sc cutoff i v t (evenBoundaryCrossCoordinates D Sc cutoff p i v t f) =
      offDiagonalPolynomialBoundary D Sc cutoff p i v t (evenLongShift D Sc cutoff v t f) 0 := by
  change appendC0InputDefect D Sc cutoff i v t
    (shortCross D Sc cutoff i v t
      (ShortCrossCoordinates.decode D Sc cutoff i v t (evenLiftBoundary D Sc cutoff p i v t f))) 0 = _
  rw [shortCross_decode_residual, map_sub, appendC0InputDefect_embedding, sub_zero]
  change (appendC0 D Sc cutoff i v t
    (appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1
      (evenLiftBoundary D Sc cutoff p i v t f)) -
    appendInputShift D Sc cutoff i v t
      (appendC0 D Sc cutoff i v t (evenLiftBoundary D Sc cutoff p i v t f))) 0 = _
  rw [Finsupp.sub_apply, appendInputShift_zero, sub_zero, ← evenLiftBoundary_shift D Sc cutoff p i hi]
  rfl

theorem evenCrossingInputDotAffine_iterate_boundaryCrossCoordinates (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (r : ℕ) (f : ℕ →₀ Old D Sc cutoff v t) :
    (evenCrossingInputDotAffine D Sc cutoff i v t)^[r] (evenBoundaryCrossCoordinates D Sc cutoff p i v t f) =
      evenBoundaryCrossCoordinates D Sc cutoff p i v t ((evenLongShift D Sc cutoff v t)^[r] f) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih,
      evenCrossingInputDotAffine_boundaryCrossCoordinates D Sc cutoff p i hi,
      Function.iterate_succ_apply']

/-- The raw cap after r input dots reads row r+d+1 at degree zero. -/
theorem evenInputContractionAffine_iterate_boundaryCrossCoordinates (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (r d : ℕ) (b : Old D Sc cutoff v t) :
    evenInputContractionAffine D Sc cutoff i v t
      ((evenCrossingInputDotAffine D Sc cutoff i v t)^[r]
        (evenBoundaryCrossCoordinates D Sc cutoff p i v t (Finsupp.single d b))) =
      offDiagonalPolynomialBoundary D Sc cutoff p i v t (Finsupp.single (r + d + 1) b) 0 := by
  rw [evenCrossingInputDotAffine_iterate_boundaryCrossCoordinates D Sc cutoff p i hi,
    evenInputContractionAffine_boundaryCrossCoordinates D Sc cutoff p i hi,
    evenLongShift_iterate_single, evenLongShift_single]

theorem evenInputContractionAffine_below (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (r d : ℕ) (b : Old D Sc cutoff v t)
    (h : r + d + 1 + endpointQPDegree D cutoff i v < outputSDegree D i v) :
    evenInputContractionAffine D Sc cutoff i v t
      ((evenCrossingInputDotAffine D Sc cutoff i v t)^[r]
        (evenBoundaryCrossCoordinates D Sc cutoff p i v t (Finsupp.single d b))) = 0 := by
  rw [evenInputContractionAffine_iterate_boundaryCrossCoordinates D Sc cutoff p i hi]
  exact offDiagonalBoundary_even_above D Sc cutoff p i hi v t (r + d + 1) 0 b (by omega)

theorem evenInputContractionAffine_pivot (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (r d : ℕ) (b : Old D Sc cutoff v t)
    (h : outputSDegree D i v = r + d + 1 + endpointQPDegree D cutoff i v) :
    evenInputContractionAffine D Sc cutoff i v t
      ((evenCrossingInputDotAffine D Sc cutoff i v t)^[r]
        (evenBoundaryCrossCoordinates D Sc cutoff p i v t (Finsupp.single d b))) =
      evenOffDiagonalBoundaryLeadingEquiv D Sc cutoff p i v t b := by
  rw [evenInputContractionAffine_iterate_boundaryCrossCoordinates D Sc cutoff p i hi]
  exact offDiagonalBoundary_even_top D Sc cutoff p i hi v t (r + d + 1) 0 b (by omega)

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Ordinary-right covariance of the actual unscaled unit/dot columns

The column is exactly the chosen ordinary unit followed by an actual
induction-dot power, in canonical co-Yoneda coordinates. Its source
coefficient is composed without a parity twist.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem inductionUnitDotColumn_comp (i : I) (v t : List I) (n : ℕ)
    (b : Old D Sc cutoff v t) :
    inductionUnitDotColumn D Sc cutoff i v t n b =
      inductionUnitDotSign (k := k) (D.parity i) n •
        ((append D Sc cutoff i).map (X := (⟨v⟩ : OldCategory D Sc cutoff))
          (Y := (⟨t⟩ : OldCategory D Sc cutoff)) b ≫
        ((ideal D Sc cutoff (t ++ [i]) (t ++ [i])).mkQ
          (appendMovingPower D Sc cutoff i t n) :
            (append D Sc cutoff i).obj (⟨t⟩ : OldCategory D Sc cutoff) ⟶
              (append D Sc cutoff i).obj (⟨t⟩ : OldCategory D Sc cutoff))) := by
  rw [inductionUnitDotColumn_apply]
  congr 1
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  rw [appendOutputEmbedding_single, canonicalAppendTarget_projection]
  rfl

/-- The exact ordinary categorical unit/dot column, with no column rescaling. -/
def unitKernelComponent (i : I) (n : ℕ) (v t : OldCategory D Sc cutoff) :
    (v ⟶ t) →ₗ[k] ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) :=
  inductionUnitDotColumn D Sc cutoff i v.word t.word n

theorem unitKernelComponent_precompose (i : I) (n : ℕ)
    {v w : OldCategory D Sc cutoff} (a : v ⟶ w) (t : OldCategory D Sc cutoff) :
    (unitKernelComponent D Sc cutoff i n v t).comp (Linear.leftComp k t a) =
    (Linear.leftComp k ((append D Sc cutoff i).obj t) ((append D Sc cutoff i).map a)).comp
      (unitKernelComponent D Sc cutoff i n w t) := by
  apply LinearMap.ext
  intro b
  cases v with
  | mk v =>
    cases w with
    | mk w =>
      cases t with
      | mk t =>
        change inductionUnitDotColumn D Sc cutoff i v t n (a ≫ b) =
          (append D Sc cutoff i).map a ≫ inductionUnitDotColumn D Sc cutoff i w t n b
        rw [inductionUnitDotColumn_comp, inductionUnitDotColumn_comp,
          Functor.map_comp, Linear.comp_smul, Category.assoc]

/-- The actual unscaled unit/dot-power column is an ordinary-right kernel map. -/
def unitKernel (i : I) (n : ℕ) (t : OldCategory D Sc cutoff) :
    BalancedKernelTensor.inductionKernel (k := k) (𝟭 (OldCategory D Sc cutoff)) t ⟶
      BalancedKernelTensor.inductionKernel (k := k) (append D Sc cutoff i)
        ((append D Sc cutoff i).obj t) where
  app v := ModuleCat.ofHom (unitKernelComponent D Sc cutoff i n v.unop t)
  naturality _ _ a := by
    apply ModuleCat.hom_ext
    exact unitKernelComponent_precompose D Sc cutoff i n a.unop t

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Actual finite matrix component maps and their parity
Brundan--Ellis (1.13)--(1.14) assemble the prescribed even module
entries on the actual finite parity-shifted superspace families.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.MatrixComponentParity
universe u
variable {k : Type u} [CommRing k]
variable {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

private theorem total_even {F G : Superfunctor k C (SVec k)}
    (f : F ⟶ G) (hf : f ∈ parity (R := k) F G 0) (t : C) :
    f.total t ∈ parity (R := k) (F.obj t) (G.obj t) 0 := by
  have hz := Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) t
  have ht : f.total t = f.app 0 t := by
    rw [SuperNatTrans.total, hz, add_zero]
  rw [ht]
  exact f.app_mem 0 t

private theorem inverse_precompose_total {F G H : Superfunctor k C (SVec k)}
    (e : F ≅ G) (f : F ⟶ H) (t : C) (z : G.obj t) :
    f.total t ((moduleIsoLinearEquiv e t).symm z) = (e.inv ≫ f).total t z := by
  rw [Superfunctor.comp_total]
  rfl

private theorem postcompose_total {F G H : Superfunctor k C (SVec k)}
    (e : G ≅ H) (f : F ⟶ G) (t : C) (z : F.obj t) :
    moduleIsoLinearEquiv e t (f.total t z) = (f ≫ e.hom).total t z := by
  rw [Superfunctor.comp_total]
  rfl

end OddMath.QuiverHecke.ELV.MatrixComponentParity

namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The actual finite source superspace with its pointwise shifted grading. -/
def unitMatrixSourceSpace (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff) : SVec k :=
  OddMath.FiniteSuperspace.product fun a => (unitMatrixFamily D Sc cutoff i M m a).obj t

/-- The actual finite target superspace with its pointwise shifted grading. -/
def capMatrixTargetSpace (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff) : SVec k :=
  OddMath.FiniteSuperspace.product fun a => (capMatrixFamily D Sc cutoff i M m a).obj t

/-- Finite assembly of the actual unit-family entries. -/
def unitMatrixComponent (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff) :
    unitMatrixSourceSpace D Sc cutoff i M m t ⟶
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj M)).obj t :=
  OddMath.FiniteSuperspace.assembleColumns _ _
    fun a => (unitMatrixEntry D Sc cutoff i M m a).total t

/-- Finite assembly of the actual cap-family entries. -/
def capMatrixComponent (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff) :
    ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t ⟶
        capMatrixTargetSpace D Sc cutoff i M m t :=
  OddMath.FiniteSuperspace.assembleRows _ _
    fun a => (capMatrixEntry D Sc cutoff i M m a).total t

/-- The actual finite unit matrix is even, for every old module. -/
theorem unitMatrixComponent_even (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff) :
    unitMatrixComponent D Sc cutoff i M m t ∈ parity (R := k) _ _ 0 := by
  apply OddMath.FiniteSuperspace.assembleColumns_even
  intro a
  exact MatrixComponentParity.total_even _ (unitMatrixEntry_mem D Sc cutoff i M m a) t

local instance finiteMatrixComponentsPi :
    PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) := supermodulePiSupercategory

/-- The canonical first source parity isomorphism with fixed literal module endpoints. -/
def unitMatrixFirstSourceIso (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    unitMatrixFamily D Sc cutoff i M m none ≅
      (BalancedInduction.induction (append D Sc cutoff i)).obj
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) :=
  (SKM.homParityShiftDatum (k := k) (D.parity i)).iso
    ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M))

/-- Removing the canonical first source shift gives the actual mate as a module map. -/
theorem unitMatrixEntry_none_unshifted (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    (unitMatrixFirstSourceIso D Sc cutoff i M m).inv ≫
      unitMatrixEntry D Sc cutoff i M m none = matrixMateComponent D Sc cutoff i M := by
  rw [unitMatrixFirstSourceIso, unitMatrixEntry_none, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The literal first unit entry agrees with the mate after the canonical source coordinate. -/
theorem unitMatrixEntry_none_inverse_apply (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff)
    (z : ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t) :
    (unitMatrixEntry D Sc cutoff i M m none).total t
      ((moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i M m) t).symm z) =
      (matrixMateComponent D Sc cutoff i M).total t z := by
  have h := MatrixComponentParity.inverse_precompose_total
    (unitMatrixFirstSourceIso D Sc cutoff i M m)
    (unitMatrixEntry D Sc cutoff i M m none) t z
  rw [unitMatrixEntry_none_unshifted] at h
  exact h

/-- The first literal unit entry uses the canonical source parity coordinate. -/
theorem unitMatrixEntry_none_apply (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff)
    (b : (unitMatrixFamily D Sc cutoff i M m none).obj t) :
    (unitMatrixEntry D Sc cutoff i M m none).total t b =
      (matrixMateComponent D Sc cutoff i M).total t
        (moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i M m) t b) := by
  have h := unitMatrixEntry_none_inverse_apply D Sc cutoff i M m t
    (moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i M m) t b)
  simpa only [LinearEquiv.symm_apply_apply] using h

/-- The canonical first target parity isomorphism with fixed literal module endpoints. -/
def capMatrixFirstTargetIso (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    capMatrixFamily D Sc cutoff i M m none ≅
      (BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj M) :=
  (SKM.homParityShiftDatum (k := k) (D.parity i)).iso
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj
      ((BalancedInduction.induction (append D Sc cutoff i)).obj M))

/-- The literal first cap entry before evaluating components. -/
theorem capMatrixEntry_none (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    capMatrixEntry D Sc cutoff i M m none =
      matrixMateComponent D Sc cutoff i M ≫ (capMatrixFirstTargetIso D Sc cutoff i M m).inv := rfl

/-- Removing the canonical first target parity gives the actual mate as a module map. -/
theorem capMatrixEntry_none_unshifted (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    capMatrixEntry D Sc cutoff i M m none ≫ (capMatrixFirstTargetIso D Sc cutoff i M m).hom =
      matrixMateComponent D Sc cutoff i M := by
  rw [capMatrixEntry_none, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The literal first cap entry uses the canonical target parity coordinate. -/
theorem capMatrixEntry_none_apply (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff)
    (z : ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t) :
    moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t
      ((capMatrixEntry D Sc cutoff i M m none).total t z) =
      (matrixMateComponent D Sc cutoff i M).total t z := by
  have h := MatrixComponentParity.postcompose_total (capMatrixFirstTargetIso D Sc cutoff i M m)
    (capMatrixEntry D Sc cutoff i M m none) t z
  rw [capMatrixEntry_none_unshifted] at h
  exact h

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end
