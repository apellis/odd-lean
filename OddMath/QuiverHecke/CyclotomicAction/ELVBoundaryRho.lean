/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVPCentral
import OddMath.QuiverHecke.CyclotomicAction.ELVSignedMovingPower
import OddMath.QuiverHecke.CyclotomicAction.ELVFirstDotTransport
import OddMath.QuiverHecke.CyclotomicAction.ELVPInjective

/-!
# Corrected odd moving dot on the ELV source

This constructs the first-order source operator in
`docs/Nondegeneracy/DeformedMackeyBoundary.md` §1 on the full coefficient
quotient. In diagrammatic order the normalizer is
`x + 2 (-1)^N delta`; the content sign is applied after this correction.
The downstream use is the first-order Mackey boundary recurrence, not just
central-square linearity. No inverse or boundary compatibility is assumed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The exterior coefficient as an old endomorphism. -/
def boundaryDelta (j : {j : I // D.parity j = 1}) (v : List I) :
    hom D Sc cutoff v v :=
  SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D k j) ⊗ₜ[k] (𝟙 _)

@[simp] theorem insert_boundaryDelta (j : {j : I // D.parity j = 1}) (v : List I) :
    insert D Sc cutoff j.1 v v (boundaryDelta D Sc cutoff j v) =
      boundaryDelta D Sc cutoff j (j.1 :: v) := by
  rw [boundaryDelta, insert_tmul]
  change _ ⊗ₜ[k] ((pres D Sc).obj (ob D [j.1]) ◁ (𝟙 _)) = _
  rw [MonoidalSupercategory.whiskerLeft_id (R := k)]
  rfl

/-- The corrected first dot before the content sign. -/
def boundaryFirstDot (j : {j : I // D.parity j = 1}) (v : List I) :
    hom D Sc cutoff (j.1 :: v) (j.1 :: v) :=
  movingPower D Sc cutoff j.1 v 1 +
    (2 * (-1 : k) ^ cutoff j.1) • boundaryDelta D Sc cutoff j (j.1 :: v)

/-- The corrected first dot preserves every old cyclotomic relation. -/
theorem boundaryFirstDot_relations (j : {j : I // D.parity j = 1}) {v w : List I}
    {h : hom D Sc cutoff (j.1 :: v) w} (hh : h ∈ relations D Sc cutoff j.1 v w) :
    boundaryFirstDot D Sc cutoff j v ≫ h ∈ relations D Sc cutoff j.1 v w := by
  rw [boundaryFirstDot, Preadditive.add_comp, Linear.smul_comp]
  apply Submodule.add_mem
  · exact movingPower_relations_twist D Sc cutoff j.1 1 hh
  · apply Submodule.smul_mem
    rw [← insert_boundaryDelta]
    induction hh using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨t, r, hr, f, rfl⟩ := hh
      rw [← Category.assoc, ← insert_comp]
      exact Submodule.subset_span ⟨t, _, comp_ideal D Sc cutoff _ hr, f, rfl⟩
    | zero => simp only [Limits.comp_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact Submodule.add_mem _ ha hb
    | smul a b _ hb => rw [Linear.comp_smul]; exact Submodule.smul_mem _ a hb

/-- Corrected source operator, with total moving-content sign. -/
def boundaryRho (j : {j : I // D.parity j = 1}) (v w : List I) :
    Target D Sc cutoff j.1 v w →ₗ[k] Target D Sc cutoff j.1 v w :=
  SKM.zsign k (D.parity j.1 * wordSumParity D v) •
    (relations D Sc cutoff j.1 v w).mapQ (relations D Sc cutoff j.1 v w)
      (Linear.leftComp k _ (boundaryFirstDot D Sc cutoff j v))
      (fun _ hh => boundaryFirstDot_relations D Sc cutoff j hh)

@[simp] theorem boundaryRho_projection (j : {j : I // D.parity j = 1}) (v w : List I)
    (h : hom D Sc cutoff (j.1 :: v) w) :
    boundaryRho D Sc cutoff j v w (projection D Sc cutoff j.1 v w h) =
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        projection D Sc cutoff j.1 v w (boundaryFirstDot D Sc cutoff j v ≫ h) := rfl

/-- The decorated relation factors through the corrected first dot, with both
cutoff parities and every exterior coefficient retained. -/
theorem appendDecoratedW_one_boundaryFirstDot (j : {j : I // D.parity j = 1})
    (v : List I) :
    appendDecoratedW D Sc cutoff j.1 v 1 =
      appendW D Sc cutoff j.1 v ≫ boundaryFirstDot D Sc cutoff j v := by
  have ht : movingPower D Sc cutoff j.1 v 1 ≫ relation D Sc cutoff j.1 v =
      relation D Sc cutoff j.1 v ≫ boundaryFirstDot D Sc cutoff j v := by
    simpa only [boundaryFirstDot, movingPower, pow_one, boundaryDelta]
      using firstDot_relation_transport D Sc cutoff j v
  rw [appendDecoratedW, ht, appendW, Category.assoc]

/-- First-order intertwining for the full ELV quotient at every old word.
This is the corrected odd-dot identity, not unchanged odd-dot linearity. -/
theorem pMap_boundaryRho (j : {j : I // D.parity j = 1}) (v w : List I)
    (z : Target D Sc cutoff j.1 v w) :
    pMap D Sc cutoff j.1 v w (boundaryRho D Sc cutoff j v w z) =
      appendMovingPowerTarget D Sc cutoff j.1 v w 1 (pMap D Sc cutoff j.1 v w z) := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff j.1 v w z
  rw [boundaryRho_projection, map_smul]
  have he := lastDot_comp_appendDecoratedW_mem D Sc cutoff j.1 v 0
  rw [appendDecoratedW_zero, zero_add, appendDecoratedW_one_boundaryFirstDot] at he
  have hz := (appendProjection_eq_zero_iff D Sc cutoff j.1 v w _).mpr
    (appendRelations_comp D Sc cutoff j.1 he h)
  rw [Preadditive.sub_comp, Linear.smul_comp, map_sub, map_smul, sub_eq_zero] at hz
  simpa only [pMap_projection, appendMovingPowerTarget_projection,
    appendW, Category.assoc, appendMovingPower, pow_one] using hz.symm

/-- Moving powers compose on the append quotient without a parity restriction. -/
theorem appendMovingPowerTarget_add (i : I) (v w : List I) (d e : ℕ)
    (z : AppendTarget D Sc cutoff i v w) :
    appendMovingPowerTarget D Sc cutoff i v w d
        (appendMovingPowerTarget D Sc cutoff i v w e z) =
      appendMovingPowerTarget D Sc cutoff i v w (d + e) z := by
  obtain ⟨h, rfl⟩ := (appendRelations D Sc cutoff i v w).mkQ_surjective z
  change appendProjection D Sc cutoff i v w (_ ≫ (_ ≫ h)) =
    appendProjection D Sc cutoff i v w (_ ≫ h)
  rw [← Category.assoc]
  apply congrArg (appendProjection D Sc cutoff i v w)
  apply congrArg (fun a => a ≫ h)
  unfold appendMovingPower
  rw [← affineUnit_comp]
  change affineUnit D Sc cutoff _ _
    (dotE D Sc (v ++ [i]) v.length ^ e * dotE D Sc (v ++ [i]) v.length ^ d) = _
  rw [← pow_add, Nat.add_comm e d]

/-- The square of the corrected odd dot is the unchanged moving square.
Cancellation uses the proved full-ELV injectivity of P, not an inverse assumption. -/
theorem boundaryRho_square (j : {j : I // D.parity j = 1}) (v w : List I)
    (z : Target D Sc cutoff j.1 v w) :
    boundaryRho D Sc cutoff j v w (boundaryRho D Sc cutoff j v w z) =
      signedMovingPowerTarget D Sc cutoff j.1 v w 2 z := by
  apply pMap_injective D Sc cutoff j.1 v w
  rw [pMap_boundaryRho, pMap_boundaryRho, appendMovingPowerTarget_add]
  exact (pMap_movingSquare D Sc cutoff j.1 v w z).symm

/-- Every corrected iterate has the prescribed last-dot image under P.
The dot acts on the right in algebra notation; it is not moved through the ELV polynomial. -/
theorem pMap_boundaryRho_iterate (j : {j : I // D.parity j = 1}) (v w : List I)
    (d : ℕ) (z : Target D Sc cutoff j.1 v w) :
    pMap D Sc cutoff j.1 v w ((boundaryRho D Sc cutoff j v w)^[d] z) =
      appendMovingPowerTarget D Sc cutoff j.1 v w d (pMap D Sc cutoff j.1 v w z) := by
  induction d with
  | zero =>
    obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff j.1 v w z
    simp only [Function.iterate_zero, id_eq, pMap_projection,
      appendMovingPowerTarget_projection, appendMovingPower, pow_zero,
      End.one_def, affineUnit_id, Category.id_comp]
  | succ d ih =>
    rw [Function.iterate_succ_apply', pMap_boundaryRho, ih,
      appendMovingPowerTarget_add, Nat.add_comm 1 d]

/-- Unsigned moving powers add on the old quotient. -/
theorem signedMovingPowerTarget_add (i : I) (v w : List I) (d e : ℕ)
    (z : Target D Sc cutoff i v w) :
    signedMovingPowerTarget D Sc cutoff i v w d
        (signedMovingPowerTarget D Sc cutoff i v w e z) =
      signedMovingPowerTarget D Sc cutoff i v w (d + e) z := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  simp only [signedMovingPowerTarget_projection, ← Category.assoc,
    movingPower_comp_movingPower]

/-- All even corrected iterates are the literal moving powers. -/
theorem boundaryRho_iterate_even (j : {j : I // D.parity j = 1}) (v w : List I)
    (q : ℕ) (z : Target D Sc cutoff j.1 v w) :
    (boundaryRho D Sc cutoff j v w)^[2 * q] z =
      signedMovingPowerTarget D Sc cutoff j.1 v w (2 * q) z := by
  induction q with
  | zero =>
    obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff j.1 v w z
    simp only [mul_zero, Function.iterate_zero, id_eq, signedMovingPowerTarget_projection]
    change projection D Sc cutoff j.1 v w h =
      projection D Sc cutoff j.1 v w
        (affineUnit D Sc cutoff _ _ (dotE D Sc (j.1 :: v) 0 ^ 0) ≫ h)
    rw [pow_zero, End.one_def, affineUnit_id, Category.id_comp]
  | succ q ih =>
    rw [show 2 * (q + 1) = 2 + 2 * q by omega, Function.iterate_add_apply,
      Function.iterate_succ_apply', Function.iterate_one, boundaryRho_square,
      ih, signedMovingPowerTarget_add]

/-- All odd corrected iterates have precisely one delta correction. -/
theorem boundaryRho_iterate_odd_projection (j : {j : I // D.parity j = 1})
    (v w : List I) (q : ℕ) (h : hom D Sc cutoff (j.1 :: v) w) :
    (boundaryRho D Sc cutoff j v w)^[2 * q + 1]
        (projection D Sc cutoff j.1 v w h) =
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        projection D Sc cutoff j.1 v w
          (boundaryFirstDot D Sc cutoff j v ≫ movingPower D Sc cutoff j.1 v (2 * q) ≫ h) := by
  rw [Function.iterate_succ_apply', boundaryRho_iterate_even,
    signedMovingPowerTarget_projection, boundaryRho_projection]

end OddMath.QuiverHecke.ELVOld
