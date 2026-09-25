import OddMath.Frontier.AllRankDivided

/-! # Square-zero and kernel-image equality for actual all-rank divided differences
EKL arXiv:1111.1320v1 Proposition 2.1 (2.7); Ellis arXiv:1111.3932v1 §2.1.
-/
namespace OddMath.Frontier.DividedSquareZero
open PbwL2 PbwL3 AllRankDivided
open OddMath.SkewPolynomial (SkewPolynomial generator)
variable {n : ℕ}

/-- The square commutes with left multiplication by every generator,
including arbitrary spectators. This is not a rank-two reduction. -/
theorem divided_sq_generator_mul (i : Fin (n+1)) (j : Fin (n+2))
    (f : SkewPolynomial (n+2)) :
    divided i (divided i (generator j * f)) =
      generator j * divided i (divided i f) := by
  by_cases hl : j = i.castSucc
  · subst j
    rw [divided_left_mul, map_sub, divided_right_mul]
    abel
  · by_cases hr : j = i.succ
    · subst j
      rw [divided_right_mul, map_sub, divided_left_mul]
      abel
    · rw [divided_spectator_mul i j hl hr, neg_mul, map_neg,
        divided_spectator_mul i j hl hr, neg_mul, neg_neg]

/-- Extend the generator identity to all actual polynomials through the
parent's free-algebra evaluation and quotient/PBW surjectivity. -/
theorem divided_sq_mul (i : Fin (n+1)) (a f : SkewPolynomial (n+2)) :
    divided i (divided i (a * f)) = a * divided i (divided i f) := by
  obtain ⟨x, rfl⟩ := PbwRealization.Phi_surjective (n+2) a
  induction x using Quotient.inductionOn' with
  | h w =>
      change divided i (divided i (evalAlg (n+2) w * f)) =
        evalAlg (n+2) w * divided i (divided i f)
      induction w using FreeAlgebra.induction generalizing f with
      | grade0 r =>
          rw [AlgHom.commutes]
          change divided i (divided i ((r • 1) * f)) =
            (r • 1) * divided i (divided i f)
          simp only [smul_mul_assoc, one_mul, map_smul]
      | grade1 j =>
          rw [evalAlg_ι]
          exact divided_sq_generator_mul i j f
      | add a b ha hb =>
          rw [map_add, add_mul, map_add, map_add, ha, hb, add_mul]
      | mul a b ha hb =>
          rw [map_mul (evalAlg (n+2)) a b, mul_assoc, ha, hb, mul_assoc]

/-- The genuine integral odd divided difference is square-zero in every rank. -/
theorem divided_sq_zero (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    divided i (divided i f) = 0 := by
  simpa only [mul_one, divided_one, map_zero, mul_zero] using divided_sq_mul i f 1

/-- Linear-map form of the square-zero relation. -/
theorem divided_comp_self (i : Fin (n+1)) : (divided i).comp (divided i) = 0 := by
  apply LinearMap.ext
  intro f
  exact divided_sq_zero i f

/-- A concrete integral preimage of every kernel element. -/
theorem divided_preimage_of_kernel (i : Fin (n+1)) (f : SkewPolynomial (n+2))
    (h : divided i f = 0) : divided i (generator i.castSucc * f) = f := by
  rw [divided_left_mul, h, mul_zero, sub_zero]

/-- Both directions are proved for the actual operator, not postulated. -/
theorem divided_eq_zero_iff_exists (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    divided i f = 0 ↔ ∃ g, divided i g = f := by
  constructor
  · intro h
    exact ⟨generator i.castSucc * f, divided_preimage_of_kernel i f h⟩
  · rintro ⟨g, rfl⟩
    exact divided_sq_zero i g

/-- Equality as submodules over the integers. -/
theorem ker_eq_range (i : Fin (n+1)) :
    LinearMap.ker (divided i) = LinearMap.range (divided i) := by
  ext f
  exact divided_eq_zero_iff_exists i f

/-- Arbitrary images are kernel elements. -/
theorem divided_image_mem_kernel (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    divided i f ∈ LinearMap.ker (divided i) := divided_sq_zero i f

/-- The explicit preimage also recovers every arbitrary image. -/
theorem divided_preimage_of_image (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    divided i (generator i.castSucc * divided i f) = divided i f :=
  divided_preimage_of_kernel i (divided i f) (divided_sq_zero i f)
end OddMath.Frontier.DividedSquareZero
