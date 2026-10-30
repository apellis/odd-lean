/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendQPTransport
import OddMath.QuiverHecke.CyclotomicAction.ELVEndpointPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendNormRegularity
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryRho
/-! # Ordered reverse boundary polynomial and corrected iterates

`pMap_move_projection` gives the literal reverse QP polynomial identity on the
old-only append quotient, canceling G on its proved domain.
`pMap_boundaryRho_move_iterate` and `pMap_evenDot_move_iterate` give every
corrected right-dot iterate in both parities. These are the quotient-level
inputs to `DeformedBoundaryDivision.md` §§3–4, not an identification with
longest-output coordinates, and not the full reverse-chain norm.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem affineQP_comp_move (i : I) (v : List I) :
    affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫ move D Sc cutoff i v =
      move D Sc cutoff i v ≫ affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) := by
  change affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫
      affineUnit D Sc cutoff _ _ (moveHom D Sc i [] v) =
    affineUnit D Sc cutoff _ _ (moveHom D Sc i [] v) ≫
      affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v)
  rw [← affineUnit_comp, ← affineUnit_comp]
  exact congrArg (affineUnit D Sc cutoff (i :: v) (v ++ [i]))
    (qpProduct_comp_moveHom D Sc i v)

/-- The reverse boundary polynomial identity in the append-old quotient.
The endpoint polynomial is explicit and ordered, and G is canceled only on
its proved old-only domain. -/
theorem pMap_move_projection (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) :
    pMap D Sc cutoff i v w
      (projection D Sc cutoff i v w (move D Sc cutoff i v ≫ h)) =
    sign k ((cutoff i • D.parity i) * (D.parity i * wordSumParity D v)) •
      appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
          endpointELV D Sc cutoff i v ≫ h) := by
  apply qMap_injective D Sc cutoff i v w
  rw [qMap_pMap_projection, map_smul, qMap_projection]
  rw [Category.assoc, ← Category.assoc (relation D Sc cutoff i v), relation_comp_move,
    Linear.smul_comp, Linear.comp_smul, map_smul]
  congr 1
  rw [← Category.assoc, ← Category.assoc, affineQP_comp_move]
  change projection D Sc cutoff i v w
      (((move D Sc cutoff i v ≫ affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v)) ≫
        endpointELV D Sc cutoff i v) ≫ h) =
    projection D Sc cutoff i v w
      (move D Sc cutoff i v ≫ (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
        (endpointELV D Sc cutoff i v ≫ h)))
  simp only [Category.assoc]

/-- Every corrected odd iterate has the ordered right-dot image.
This is a quotient identity prior to longest-output extraction. -/
theorem pMap_boundaryRho_move_iterate (j : {i : I // D.parity i = 1})
    (v w : List I) (d : ℕ) (h : hom D Sc cutoff (v ++ [j.1]) w) :
    pMap D Sc cutoff j.1 v w
      ((boundaryRho D Sc cutoff j v w)^[d]
        (projection D Sc cutoff j.1 v w (move D Sc cutoff j.1 v ≫ h))) =
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) •
      appendProjection D Sc cutoff j.1 v w
        (appendMovingPower D Sc cutoff j.1 v d ≫
          affineUnit D Sc cutoff _ _ (appendQPProduct D Sc j.1 v) ≫
          endpointELV D Sc cutoff j.1 v ≫ h) := by
  rw [pMap_boundaryRho_iterate, pMap_move_projection, map_smul,
    appendMovingPowerTarget_projection]
private theorem pMap_evenDot_iterate (i : I) (hi : D.parity i = 0)
    (v w : List I) (d : ℕ) (z : Target D Sc cutoff i v w) :
    pMap D Sc cutoff i v w
      ((movingPowerTarget D Sc cutoff i v w 1 (by simp [hi]))^[d] z) =
    appendMovingPowerTarget D Sc cutoff i v w d (pMap D Sc cutoff i v w z) := by
  induction d with
  | zero =>
    obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
    simp only [Function.iterate_zero, id_eq, pMap_projection,
      appendMovingPowerTarget_projection, appendMovingPower, pow_zero,
      End.one_def, affineUnit_id, Category.id_comp]
  | succ d ih =>
    rw [Function.iterate_succ_apply', pMap_movingEvenDot D Sc cutoff i hi, ih,
      appendMovingPowerTarget_add, Nat.add_comm 1 d]

/-- At even colour the same ordered reverse identity needs no correction. -/
theorem pMap_evenDot_move_iterate (i : I) (hi : D.parity i = 0)
    (v w : List I) (d : ℕ) (h : hom D Sc cutoff (v ++ [i]) w) :
    pMap D Sc cutoff i v w
      ((movingPowerTarget D Sc cutoff i v w 1 (by simp [hi]))^[d]
        (projection D Sc cutoff i v w (move D Sc cutoff i v ≫ h))) =
      appendProjection D Sc cutoff i v w
        (appendMovingPower D Sc cutoff i v d ≫
          affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
          endpointELV D Sc cutoff i v ≫ h) := by
  rw [pMap_evenDot_iterate D Sc cutoff i hi, pMap_move_projection]
  simp only [hi, nsmul_zero, zero_mul, sign_zero, one_smul,
    appendMovingPowerTarget_projection]

end OddMath.QuiverHecke.ELVOld
