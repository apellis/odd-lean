/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentMixedProbe

/-! # Repeated-dot transport in the adjacent mixed braid

The two-crossing map from `Rᵢ Pᵢ Pⱼ` to `Pⱼ Rᵢ Pᵢ` retains the
Q-weighted inverse interchange prescribed by the swapped generators.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hR : StepValid (true, i) false s)
  (hs : nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)) =
    nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s))))

/-- The two unequal crossings, including the target mixed parameter polynomial. -/
def adjacentMixedMove :=
  (P.step (true, i) false s hR).map
    (P.preCrossNe i j (nextSector (true, i) false s) hs Z) ≫
  ((P.mixedJ j i s hR ((P.step (true, i) true _ trivial).obj Z)).inv ≫
    P.mixedQ j i s hR ((P.step (true, i) true _ trivial).obj Z))

/-- Both local and spectator signs occur in transporting the repeated probe dot;
their product is one. -/
theorem adjacentMixedMove_preDot (hij : i ≠ j) :
    P.rpPreDot i s hR ((P.step (true, j) true _ trivial).obj (hs ▸ Z)) ≫
      P.adjacentMixedMove i j s hR hs Z =
    P.adjacentMixedMove i j s hR hs Z ≫
      (P.step (true, j) true s trivial).map
        (P.rpPreDot i (nextSector (true, j) true s) hR Z) := by
  have h₁ := congrArg (P.step (true, i) false s hR).map
    (P.preCrossNe_slideL i j hij (nextSector (true, i) false s) hs Z)
  simp only [Functor.map_comp, Functor.map_smul] at h₁
  have hn := (P.mixedJ_inv_supernatural j i s hR).comp
    (P.mixedQ_supernatural j i s hR)
  have h₂ := hn.naturality (P.T.dot_mem i (P.muP_preE i
    (nextSector (true, j) true (nextSector (true, i) false s))) |> TwoSupercategory.whiskerRight_mem Z)
  simp only [add_zero, mul_assoc, SKM.zmod2_mul_self] at h₂
  dsimp only [Functor.comp_map] at h₂
  have hz (p : ZMod 2) : sign k p = zsign k p := by
    fin_cases p <;> simp [sign, zsign]
  rw [hz] at h₂
  dsimp only [adjacentMixedMove, rpPreDot]
  rw [← Category.assoc, h₁, Linear.smul_comp, Category.assoc]
  erw [h₂]
  rw [Linear.comp_smul, smul_smul]
  rw [mul_comm (D.parity j), zsign_mul_self', one_smul]
  simp only [Category.assoc]
  rfl

/-- The repeated reservoir dot acquires the same sign at each crossing. -/
theorem adjacentMixedMove_postDot :
    P.rpPostDot i s hR ((P.step (true, j) true _ trivial).obj (hs ▸ Z)) ≫
      P.adjacentMixedMove i j s hR hs Z =
    P.adjacentMixedMove i j s hR hs Z ≫
      (P.step (true, j) true s trivial).map
        (P.rpPostDot i (nextSector (true, j) true s) hR Z) := by
  have h₁ := (P.dotDiag_supernatural i false s hR).naturality
    ((P.preCrossNe_supernatural i j (nextSector (true, i) false s) hs).mem Z)
  have hz (p : ZMod 2) : sign k p = zsign k p := by
    fin_cases p <;> simp [sign, zsign]
  simp only [← mul_assoc, SKM.zmod2_mul_self, hz] at h₁
  have h₂ := (P.mixedJinvQ_ne_slides i j s hR
    ((P.step (true, i) true _ trivial).obj Z)).1
  have h₁' := congrArg (fun f => zsign k (D.parity i * D.parity j) • f) h₁
  simp only [smul_smul, zsign_mul_self', one_smul] at h₁'
  dsimp only [adjacentMixedMove, rpPostDot]
  rw [← Category.assoc]
  erw [← h₁']
  rw [Linear.smul_comp, Category.assoc]
  erw [h₂]
  rw [Linear.comp_smul, smul_smul, zsign_mul_self', one_smul]
  simp only [Category.assoc]
  rfl

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
