import OddMath.Frontier.NilHeckeCenter
import OddMath.Frontier.NilHeckeCenterControls

/-! Hand-checked controls for the corrected center of EKL arXiv:1111.1320v1,
Prop. 2.15, p. 13, on the actual skew polynomial carrier.

Hand derivations (increasing-index normal order, `x_j x_i = - x_i x_j` for `i ≠ j`):
* `x0^2 x1 = x0 (x0 x1) = - x0 x1 x0 = x1 x0 x0`: squares commute with generators.
* `∂0(x0 x0) = ∂0(x0) x0 + s0(x0) ∂0(x0) = x0 - x1`, and `∂0(x1 x1) = x1 - x0`.
* `x0 (x0 - x1) + (x0 - x1) x1 = x0^2 - x1^2 = x0^2 - s0(x0^2)`: the identity used
  for the second claim of the proposition.
* In rank two `x0 x1` is in the kernel but not central (even rank: the volume
  fails); in rank three `x0 x1 x2` is central and fixed by `s0`, `s1`. -/
namespace OddMath.Frontier.CenterPolyControls
open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open OddMath.Frontier.AllRankDivided OddMath.Frontier.NilHeckeCenter
open OddMath.Frontier.OddSymmetricKernel
noncomputable section

theorem square_commutes_rankTwo :
    generator (0 : Fin 2) ^ 2 * generator 1 = generator 1 * generator 0 ^ 2 := by
  have h : generator (0 : Fin 2) * generator 1 = -(generator 1 * generator 0) :=
    OddMath.PbwL1.rel_anticommute (0 : Fin 2) 1 (by decide)
  rw [pow_two, mul_assoc, h, mul_neg, ← mul_assoc, ← mul_assoc, h, neg_mul, neg_neg]

theorem divided_square_rankTwo :
    divided (0 : Fin 1) (generator 0 * generator 0) = generator 0 - generator 1 := by
  rw [divided_mul, divided_generator, s_generator]
  simp [sub_eq_add_neg]

theorem divided_square_other_rankTwo :
    divided (0 : Fin 1) (generator 1 * generator 1) = generator 1 - generator 0 := by
  rw [divided_mul, divided_generator, s_generator]
  simp [sub_eq_add_neg]

theorem twisted_identity_rankTwo :
    generator (0 : Fin 2) * divided (0 : Fin 1) (generator 0 * generator 0) +
      divided (0 : Fin 1) (generator 0 * generator 0) * generator 1 =
    generator 0 * generator 0 - s (0 : Fin 1) (generator 0 * generator 0) := by
  rw [divided_square_rankTwo, map_mul, s_generator]
  have h1 : (Equiv.swap (0 : Fin 1).castSucc (0 : Fin 1).succ) 0 = (1 : Fin 2) := by decide
  rw [h1]
  noncomm_ring

theorem even_rank_volume_not_central :
    generator (0 : Fin 2) * generator 1 ∈ kernelSubring 0 ∧
    generator (0 : Fin 2) * generator 1 ∉ Subring.center (SkewPolynomial 2) :=
  NilHeckeCenterControls.rankTwo_kernel_not_ordinary_central

theorem odd_rank_volume_central_fixed :
    volume ∈ Subring.center (SkewPolynomial 3) ∧ ∀ i : Fin 2, s i volume = volume :=
  ⟨volume_central, volume_signed_fixed⟩

end
end OddMath.Frontier.CenterPolyControls
