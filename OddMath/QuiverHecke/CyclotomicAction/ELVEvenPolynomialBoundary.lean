import OddMath.QuiverHecke.CyclotomicAction.ELVEvenLongCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalBoundary
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputSComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVReverseBoundary

/-! # Independent S in the even polynomial boundary

The parity-zero polynomial projection of DeformedMackeyBoundary (5).
The canonical arbitrary-Hom coordinates agree with the established diagonal
coordinates. This permits the independently defined S to be used in the
actual C0P boundary, whose even iterates have the prescribed ordered reverse
numerator. No boundary division or categorical inverse is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem diagonalCastPair (p : ZMod 2) (i : I) {v w s s' : List I}
    (e : s = v) (e' : s' = v)
    (f : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D w))
    (g : (pres D Sc).obj (ob D (i :: s')) ⟶ (pres D Sc).obj (ob D w))
    (h : HEq f g) :
    Eq.mp (congrArg (fun a => Old D Sc cutoff v a →ₗ[k] Target D Sc cutoff i v w) e)
      (pair D Sc cutoff p i ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f)) =
    Eq.mp (congrArg (fun a => Old D Sc cutoff v a →ₗ[k] Target D Sc cutoff i v w) e')
      (pair D Sc cutoff p i ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] g)) := by
  subst s
  subst s'
  cases h
  rfl

theorem longHomLift_diagonal (p : ZMod 2) (i : I) (v : List I)
    (y : NFIdx v v) (m : ℕ) :
    longHomLift D Sc cutoff p i y m = outputLongLift D Sc cutoff p i v m := by
  have hk : (longHomIndex i y m).tailKey = (longOutputIndex i v m).tailKey :=
    Prod.ext rfl (longHomIndex_shuffle i y m)
  unfold longHomLift outputLongLift
  exact congrArg
    (fun f : Old D Sc cutoff v v →ₗ[k] Target D Sc cutoff i v (v ++ [i]) =>
      (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m • f)
    (diagonalCastPair D Sc cutoff p i
      (longHomIndex_oldTarget i y m) (longOutputIndex_oldTarget i v m) _ _
      (prependTail_heq_of_tailKey_eq D Sc _ _ hk))

/-- Diagonal specialization preserves the prescribed normalized long section. -/
theorem offDiagonalLongSection_diagonal (p : ZMod 2) (i : I) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    offDiagonalLongSection D Sc cutoff p i v v f = outputLongSection D Sc cutoff p i v f := by
  let y : NFIdx v v :=
    Eq.mp (congrArg (fun t => NFIdx v t) (longOutputIndex_oldTarget i v 0))
      (longOutputIndex i v 0).old
  rw [offDiagonalLongSection_eq D Sc cutoff p i y]
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b =>
    simp only [longHomSection, Finsupp.lsum_single, outputLongSection_single,
      longHomLift_diagonal]

/-- The arbitrary-Hom extraction restricts to the established diagonal extraction. -/
theorem offDiagonalLongExtraction_diagonal (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) :
    offDiagonalLongExtraction D Sc cutoff p i v v z = outputLongExtraction D Sc cutoff p i v z := by
  let d := z - outputLongSection D Sc cutoff p i v (outputLongExtraction D Sc cutoff p i v z)
  have hd : d ∈ chronologicalShortSpan D Sc cutoff i v v := by
    rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v,
      LinearMap.mem_ker]
    dsimp only [d]
    rw [map_sub, outputLongExtraction_section, sub_self]
  have he : offDiagonalLongExtraction D Sc cutoff p i v v d = 0 := by
    rw [← LinearMap.mem_ker,
      ker_offDiagonalLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v v]
    exact hd
  dsimp only [d] at he
  rw [map_sub, ← offDiagonalLongSection_diagonal, offDiagonalLongExtraction_section,
    sub_eq_zero] at he
  exact he

/-- Every even iterate extracts to the ordinary finite shift iterate. -/
theorem offDiagonalLongExtraction_evenMoving_iterate (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (d : ℕ)
    (z : Target D Sc cutoff i v (t ++ [i])) :
    offDiagonalLongExtraction D Sc cutoff p i v t
      ((movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi]))^[d] z) =
    (evenLongShift D Sc cutoff v t)^[d] (offDiagonalLongExtraction D Sc cutoff p i v t z) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply',
      offDiagonalLongExtraction_evenMoving D Sc cutoff p i hi, ih,
      Function.iterate_succ_apply']

theorem offDiagonalLongExtraction_move_independentS (p : ZMod 2) (i : I) (v : List I) :
    offDiagonalLongExtraction D Sc cutoff p i v v
      (projection D Sc cutoff i v (v ++ [i]) (move D Sc cutoff i v)) =
      SKM.zsign k (D.parity i) ^ v.count i • independentOutputS D Sc cutoff i v := by
  rw [offDiagonalLongExtraction_diagonal]
  exact outputLongExtraction_move_independentS D Sc cutoff p i v

/-- The even iterated moving intertwiner extracts to the independent S polynomial. -/
theorem offDiagonalLongExtraction_evenMoving_move (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v : List I) (d : ℕ) :
    offDiagonalLongExtraction D Sc cutoff p i v v
      ((movingPowerTarget D Sc cutoff i v (v ++ [i]) 1 (by simp [hi]))^[d]
        (projection D Sc cutoff i v (v ++ [i]) (move D Sc cutoff i v))) =
      (evenLongShift D Sc cutoff v v)^[d] (independentOutputS D Sc cutoff i v) := by
  rw [offDiagonalLongExtraction_evenMoving_iterate D Sc cutoff p i hi,
    offDiagonalLongExtraction_move_independentS]
  simp only [hi, SKM.zsign_zero, one_pow, one_smul]

/-- Independent S compares with the ordered reverse numerator under actual C0P. -/
theorem offDiagonalPolynomialBoundary_even_independentS (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v : List I) (d : ℕ) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v v
      ((evenLongShift D Sc cutoff v v)^[d] (independentOutputS D Sc cutoff i v)) =
    appendC0 D Sc cutoff i v v
      (appendProjection D Sc cutoff i v (v ++ [i])
        (appendMovingPower D Sc cutoff i v d ≫
          affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
          endpointELV D Sc cutoff i v)) := by
  have h := appendC0_pMap_offDiagonal D Sc cutoff p i v v
    ((movingPowerTarget D Sc cutoff i v (v ++ [i]) 1 (by simp [hi]))^[d]
      (projection D Sc cutoff i v (v ++ [i]) (move D Sc cutoff i v)))
  have hp := pMap_evenDot_move_iterate D Sc cutoff i hi v (v ++ [i]) d (𝟙 _)
  simp only [Category.comp_id] at hp
  rw [hp, offDiagonalLongExtraction_evenMoving_move D Sc cutoff p i hi] at h
  exact h.symm

end OddMath.QuiverHecke.ELVOld
