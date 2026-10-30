/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryRho

/-!
# Full-coefficient PBW coordinates of the corrected source iterates

The input-first-dot PBW coordinates of the corrected operator are computed
on every moving tail and arbitrary old quotient coefficient. The parity twist
acts on the entire old coefficient, not just its diagram. This supplies an
explicit two-term formula for every odd iterate, including the delta term.
These are input PBW coordinates; the output-last-dot Mackey extraction still
requires its separate triangular coordinate comparison.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The quotient correction is the old delta action, not a discarded scalar. -/
theorem boundaryRho_eq_moving_add_old (j : {j : I // D.parity j = 1})
    (v w : List I) (z : Target D Sc cutoff j.1 v w) :
    boundaryRho D Sc cutoff j v w z =
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        (signedMovingPowerTarget D Sc cutoff j.1 v w 1 z +
          (2 * (-1 : k) ^ cutoff j.1) •
            oldSourceTarget D Sc cutoff j.1 v w (boundaryDelta D Sc cutoff j v) z) := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff j.1 v w z
  rw [boundaryRho_projection]
  change _ = _ • (projection D Sc cutoff j.1 v w (_ ≫ h) +
    _ • projection D Sc cutoff j.1 v w (_ ≫ h))
  rw [boundaryFirstDot, Preadditive.add_comp, Linear.smul_comp, map_add, map_smul,
    insert_boundaryDelta]

/-- Exact two-term action on an arbitrary input PBW tail with arbitrary full
old coefficient and arbitrary source balance parity. -/
theorem boundaryRho_pair (p : ZMod 2) (j : {j : I // D.parity j = 1})
    {v w : List I} (x : PrependIdx j.1 v w) (b : Old D Sc cutoff v x.oldTarget) :
    boundaryRho D Sc cutoff j v w
      (pair D Sc cutoff p j.1
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x) b) =
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        (pair D Sc cutoff p j.1
          ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
            prependTail D Sc (x.shift 1))
          (oldTwist D Sc cutoff (D.parity j.1) v x.oldTarget b) +
        (2 * (-1 : k) ^ cutoff j.1) •
          pair D Sc cutoff p j.1
            ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x)
            (oldPrecomp D Sc cutoff v x.oldTarget
              (twist k p (boundaryDelta D Sc cutoff j v)) b)) := by
  rw [boundaryRho_eq_moving_add_old, signedMovingPower_pair_shift, oldSourceTarget_pair,
    one_nsmul]

/-- Every even corrected iterate on every PBW tail retains the old coefficient. -/
theorem boundaryRho_iterate_even_pair (p : ZMod 2) (j : {j : I // D.parity j = 1})
    {v w : List I} (x : PrependIdx j.1 v w) (q : ℕ)
    (b : Old D Sc cutoff v x.oldTarget) :
    (boundaryRho D Sc cutoff j v w)^[2 * q]
      (pair D Sc cutoff p j.1
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x) b) =
      pair D Sc cutoff p j.1
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc (x.shift (2 * q))) b := by
  rw [boundaryRho_iterate_even, signedMovingPower_pair_shift]
  have hp : (2 * q) • D.parity j.1 = 0 := by
    rw [mul_nsmul]
    simp only [j.property]
    have ht : (2 : ℕ) • (1 : ZMod 2) = 0 := by decide
    rw [ht, smul_zero]
  rw [hp]
  congr 1
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v x.oldTarget).mkQ_surjective b
  change (ideal D Sc cutoff v x.oldTarget).mkQ (twist k 0 r) = _
  rw [twist_zero]

/-- Every odd corrected iterate has two explicit PBW tails. The unchanged
balance parity acts on delta and total parity acts on the old coefficient. -/
theorem boundaryRho_iterate_odd_pair (p : ZMod 2) (j : {j : I // D.parity j = 1})
    {v w : List I} (x : PrependIdx j.1 v w) (q : ℕ)
    (b : Old D Sc cutoff v x.oldTarget) :
    (boundaryRho D Sc cutoff j v w)^[2 * q + 1]
      (pair D Sc cutoff p j.1
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x) b) =
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        (pair D Sc cutoff p j.1
          ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
            prependTail D Sc ((x.shift (2 * q)).shift 1))
          (oldTwist D Sc cutoff (D.parity j.1) v x.oldTarget b) +
        (2 * (-1 : k) ^ cutoff j.1) •
          pair D Sc cutoff p j.1
            ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
              prependTail D Sc (x.shift (2 * q)))
            (oldPrecomp D Sc cutoff v x.oldTarget
              (twist k p (boundaryDelta D Sc cutoff j v)) b)) := by
  rw [Function.iterate_succ_apply', boundaryRho_iterate_even_pair, boundaryRho_pair]
  rfl

end OddMath.QuiverHecke.ELVOld
