/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightDot
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightCrossing

/-! # The chosen OLD probe dots on two-step weight induction

Brundan–Ellis (1.8): identify both independently whiskered global dots
in the same literal stored-target coordinates as the chosen equal crossing.
The identities retain all input modules and every parity component; they
supply the comparison required by the signed two-strand slide equations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u v w t z

private theorem outerDot_conjugate
    {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A : Type t} [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    (G : C ⥤ A) {M₀ M₁ : C} (hM : M₀ = M₁) {V : A}
    (hV : V = G.obj M₀) (hW : V = G.obj M₁) (d : SuperNatTrans k G G) (p : ZMod 2) :
    eqToHom hV ≫ d.app p M₀ ≫ eqToHom hV.symm =
      eqToHom hW ≫ d.app p M₁ ≫ eqToHom hW.symm := by
  cases hM
  cases hV
  cases hW
  rfl

private theorem innerDot_conjugate
    {C : Type v} [Category.{w} C] {A : Type t} [Category.{z} A]
    (G : C ⥤ A) {M₀ M₁ : C} (hM : M₀ = M₁) {V : A}
    (hV : V = G.obj M₀) (hW : V = G.obj M₁) (d : End M₁) :
    eqToHom hV ≫ G.map (eqToHom hM ≫ d ≫ eqToHom hM.symm) ≫ eqToHom hV.symm =
      eqToHom hW ≫ G.map d ≫ eqToHom hW.symm := by
  cases hM
  cases hV
  cases hW
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

/-- The outer independently chosen global dot uses the exact pair coordinate equality. -/
theorem probeOldOuterDot_component (β : WeightBlocks D Λ x₀)
    (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    ((probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).app p M)
        (blockSucc₂ D i i Λ h₁ h₂ β) =
      eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M) ≫
        (probeOldBlockDot D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)).app p
          ((probeOldBlockInd D Sc m i Λ h₁ β).obj (M β)) ≫
        eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M).symm := by
  change probeOldWeightDotComponent D Sc m i Λ h₂ p
    ((probeOldEFunctor D Sc m i Λ h₁).obj M) (blockSucc₂ D i i Λ h₁ h₂ β) = _
  rw [probeOldWeightDotComponent_blockSucc]
  exact outerDot_conjugate
    (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)).toFunctor
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₁ β M) _
    (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M)
    (probeOldBlockDot D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)) p

/-- The inner independently chosen global dot uses the identical pair coordinate equality. -/
theorem probeOldInnerDot_component (β : WeightBlocks D Λ x₀)
    (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    ((probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂).app p M)
        (blockSucc₂ D i i Λ h₁ h₂ β) =
      eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M) ≫
        (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)).map
          ((probeOldBlockDot D Sc m i Λ h₁ β).app p (M β)) ≫
        eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M).symm := by
  change (probeOldInductionComponent D Sc m i Λ h₂ (blockSucc₂ D i i Λ h₁ h₂ β)).map
    ((probeOldActionDot D Sc m i Λ h₁).app p M) = _
  rw [probeOldInductionComponent_map_blockSucc]
  change eqToHom _ ≫ (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)).map
    (probeOldWeightDotComponent D Sc m i Λ h₁ p M (blockSucc D Λ i h₁ β)) ≫ eqToHom _ = _
  rw [probeOldWeightDotComponent_blockSucc]
  exact innerDot_conjugate
    (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)).toFunctor
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₁ β M) _
    (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M) _

end OddMath.QuiverHecke
