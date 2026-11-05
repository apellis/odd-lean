/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightDot
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRouquierFields

/-! # The chosen stored-target OLD probe dot in the module grid

Brundan–Ellis (1.8): the actual chosen probe block dot retains the
literal signed OLD append transformation used by the induction-grid
slide relations. Only full scalar-evaluation certificates are forgotten.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- The physical signed dot of the actual stored-target block append. -/
def probeOldBlockDotArrow (β : WeightBlocks D Λ x)
    (s : OldContentCategory D Sc (probeCutoff D m) β.1.toList) :
    (probeOldBlockAppend D Sc m i Λ h β).obj s ⟶ (probeOldBlockAppend D Sc m i Λ h β).obj s :=
  CyclotomicCrossingTensor.oldAppendDotComponent D Sc (probeCutoff D m) i s.obj

theorem probeOldBlockDotArrow_supernatural (β : WeightBlocks D Λ x) :
    IsSupernatural k (D.parity i) (probeOldBlockDotArrow D Sc m i Λ h β) where
  mem s := (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc (probeCutoff D m) i).mem s.obj
  naturality hf := (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc (probeCutoff D m) i).naturality hf

/-- Every chosen block-dot component is the literal OLD induction-grid dot. -/
theorem probeOldBlockDot_app (β : WeightBlocks D Λ x)
    (p : ZMod 2) (M : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockDot D Sc m i Λ h β).app p M).hom =
      (inductionModuleDot (probeOldBlockAppend D Sc m i Λ h β)
        (probeOldBlockDotArrow_supernatural D Sc m i Λ h β)).app p M.obj := by
  unfold probeOldBlockDot probeAppendToInductionDot inductionModuleDot
  dsimp only [IsSupernatural.toSuperNatTrans]
  split_ifs <;> rfl

/-- Total evaluation also retains the exact signed OLD grid dot. -/
theorem probeOldBlockDot_total (β : WeightBlocks D Λ x)
    (M : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockDot D Sc m i Λ h β).total M).hom =
      (inductionModuleDot (probeOldBlockAppend D Sc m i Λ h β)
        (probeOldBlockDotArrow_supernatural D Sc m i Λ h β)).total M.obj := by
  change ((probeOldBlockDot D Sc m i Λ h β).app 0 M).hom +
    ((probeOldBlockDot D Sc m i Λ h β).app 1 M).hom = _
  rw [probeOldBlockDot_app, probeOldBlockDot_app]
  rfl

end OddMath.QuiverHecke
