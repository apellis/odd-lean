import OddMath.Frontier.CenterPoly
import OddMath.Frontier.CenterONH
import OddMath.Frontier.NilHeckeCenterControls

/-!
# Controls for the corrected center of EKL arXiv:1111.1320v1, Prop. 2.15, p. 13

Hand-checked small cases on the actual carriers: the joint kernel `OΛ_N` of the odd
divided differences (as a subring of the integer skew polynomial ring `Pol_N`), and the
presented odd nilHecke ring `ONH_N`. These controls use only the two proved halves and
do not import the combined statement.

Hand derivations (relation `x_j x_i = - x_i x_j` for `i ≠ j`):
* Rank two: `(x_0 x_1) x_0 = - x_0 x_0 x_1 = - x_0 (x_0 x_1)`, so the volume `x_0 x_1`
  anticommutes with `x_0`; it lies in `OΛ_2` but is not central there.
* Rank two: `x_0^2 + x_1^2` is the square of the power sum `p_1 = X_0 + X_1`; each
  `x_j^2` commutes with every generator, and `∂_0(x_0^2 + x_1^2) = (x_0 - x_1) +
  (x_1 - x_0) = 0`, so it is central in `OΛ_2` and lies in the squared symmetric ring.
* Rank three: `x_0 (x_0 x_1 x_2) = x_0 x_0 x_1 x_2` and
  `(x_0 x_1 x_2) x_0 = (-1)^2 x_0 x_0 x_1 x_2`; likewise for `x_1`, `x_2`. So the volume
  `V = x_0 x_1 x_2` is central, lies in `OΛ_3`, and has odd exponents, hence is not a
  polynomial in the squares: the printed statement fails in rank three, on both
  `OΛ_3` and (through the dot inclusion) `ONH_3`.
-/

namespace OddMath.Frontier.CenterCorrectedControls
open OddMath.SkewPolynomial (SkewPolynomial generator)
open OddMath.Frontier.AllRankDivided OddMath.Frontier.OddSymmetricKernel
open OddMath.Frontier.NilHeckeAction
noncomputable section

/-- Rank two: `x_0^2 + x_1^2` is the image of the first power sum under `squareHom`. -/
theorem rankTwo_psum_image :
    CenterPoly.squareHom (n := 0) (MvPolynomial.psum (Fin 2) ℤ 1) =
      generator 0 ^ 2 + generator 1 ^ 2 := by
  simp [MvPolynomial.psum_one, Fin.sum_univ_two, CenterPoly.squareHom_X]

/-- Rank two: `x_0^2 + x_1^2` lies in the squared symmetric ring. -/
theorem rankTwo_psum_mem_sq :
    (generator (0 : Fin 2) ^ 2 + generator 1 ^ 2) ∈ CenterPoly.sq 0 :=
  (CenterPoly.mem_sq _).mpr ⟨_, MvPolynomial.psum_isSymmetric (Fin 2) ℤ 1, rankTwo_psum_image⟩

/-- Rank two: `x_0^2 + x_1^2` is in `OΛ_2` and central in `Pol_2`. -/
theorem rankTwo_psum_kernel_center :
    (generator (0 : Fin 2) ^ 2 + generator 1 ^ 2) ∈ kernelSubring 0 ∧
      (generator (0 : Fin 2) ^ 2 + generator 1 ^ 2) ∈ Subring.center (SkewPolynomial 2) :=
  (CenterPoly.kernel_inter_center 0 _).mpr
    ⟨_, rankTwo_psum_mem_sq, 0, zero_mem _, by
      rw [if_neg (by decide), add_zero]⟩

/-- Rank two: `x_0^2 + x_1^2`, as an element of `OΛ_2`, is central in `OΛ_2`. -/
theorem rankTwo_psum_center_kernel :
    (⟨_, rankTwo_psum_kernel_center.1⟩ : kernelSubring 0) ∈ Subring.center (kernelSubring 0) :=
  (CenterONH.center_kernel _).mpr rankTwo_psum_kernel_center.2

/-- Rank two: the volume `x_0 x_1`, as an element of `OΛ_2`, is NOT central in `OΛ_2`. -/
theorem rankTwo_volume_not_center_kernel :
    (⟨_, NilHeckeCenterControls.rankTwo_kernel_not_ordinary_central.1⟩ : kernelSubring 0) ∉
      Subring.center (kernelSubring 0) := fun h =>
  NilHeckeCenterControls.rankTwo_kernel_not_ordinary_central.2
    ((CenterONH.center_kernel _).mp h)

/-- Rank three: the volume `V = x_0 x_1 x_2`, as an element of `OΛ_3`, is central in
`OΛ_3`. -/
theorem rankThree_volume_center_kernel :
    (⟨CenterPoly.V 1, CenterPoly.V_mem_kernel⟩ : kernelSubring 1) ∈
      Subring.center (kernelSubring 1) :=
  (CenterONH.center_kernel _).mpr (CenterPoly.V_mem_center (by decide))

/-- Rank three: `V` is not in the squared symmetric ring. -/
theorem rankThree_volume_not_sq : CenterPoly.V 1 ∉ CenterPoly.sq 1 :=
  (CenterPoly.odd_rank 1 (by decide)).2.2

/-- Rank three: `V` has the corrected form `0 + V * 1`. -/
theorem rankThree_volume_corrected_form :
    ∃ a ∈ CenterPoly.sq 1, ∃ b ∈ CenterPoly.sq 1,
      CenterPoly.V 1 = a + (if Odd (1+2) then CenterPoly.V 1 * b else 0) :=
  ⟨0, zero_mem _, 1, one_mem _, by rw [if_pos (by decide), mul_one, zero_add]⟩

/-- Rank three: the dot image of `V` is central in `ONH_3`. -/
theorem rankThree_dotVolume_center :
    CenterONH.polynomialInclusion 1 (CenterPoly.V 1) ∈ Subring.center (Presented 1) :=
  (CenterONH.center_nilHecke _).mpr
    ⟨CenterPoly.V 1, CenterPoly.V_mem_kernel, CenterPoly.V_mem_center (by decide), rfl⟩

/-- Rank three: the dot image of `V` is not the dot image of any element of the squared
symmetric ring. -/
theorem rankThree_dotVolume_not_printed :
    ¬ ∃ a ∈ CenterPoly.sq 1,
      CenterONH.polynomialInclusion 1 (CenterPoly.V 1) = CenterONH.polynomialInclusion 1 a := by
  rintro ⟨a, ha, h⟩
  exact rankThree_volume_not_sq (CenterONH.polynomialInclusion_injective h ▸ ha)

end
end OddMath.Frontier.CenterCorrectedControls
