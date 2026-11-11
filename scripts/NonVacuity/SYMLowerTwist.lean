import OddMath.SKM.SYMLowerTwist

/-! # Lowering twists of the bubble coefficient algebra

Two even vertices with Cartan entries `-3`, and the twist with `a i s = 1` for `s ≤ 3`
(three lower bubbles added to each elementary generator), as produced by the pure monomials
of `Qᵢⱼ(u, v) = u³ + u² + u + 1 + v³`.
-/

noncomputable section
namespace NonVacuity.SYMLowerTwist
open OddMath OddMath.SKM

/-- Two even vertices with Cartan entries `-3`. -/
def datum : Datum Bool (Bool → ℤ) where
  cd := {
    root := fun j i => if i = j then 2 else -3
    coroot := fun i => LinearMap.proj i
    coroot_root_self := fun i => by simp }
  isGCM := {
    diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
    offDiag_nonpos := by
      intro i j hij
      cases i <;> cases j <;> simp_all [CartanDatum.cartanMatrix_apply]
    zero_comm := by
      intro i j
      cases i <;> cases j <;> norm_num [CartanDatum.cartanMatrix_apply] }
  parity := fun _ => 0
  even_of_odd := by
    intro i j h
    exact absurd h (by decide)

example : Function.Bijective
    (SYM.lowerTwist datum ℚ fun _ s => if s ≤ 3 then (1 : ℚ) else 0) :=
  SYM.lowerTwist_bijective datum ℚ _

end NonVacuity.SYMLowerTwist
