/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentMixedCoefficient

/-! # Reverse adjacent split coefficient transport

The unweighted two-crossing map from `Pⱼ Rᵢ Pᵢ` to `Rᵢ Pᵢ Pⱼ`
uses the actual mixed comparison and unequal probe crossing. No Q or
crossing is inverted.
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
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

/-- The reverse two-crossing map has no Q factor. -/
def adjacentReverseMove :=
  (P.mixedJ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).hom ≫
    (P.step (true, i) false s hR).map
      (P.preCrossNe j i (nextSector (true, i) false s) hs Z)

/-- The repeated probe dot crosses twice, so its two local signs cancel. -/
theorem adjacentReverseMove_preDot (hij : i ≠ j) :
    (P.step (true, j) true s trivial).map
        (P.rpPreDot i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)) ≫
      P.adjacentReverseMove i j s hR hs Z =
    P.adjacentReverseMove i j s hR hs Z ≫
      P.rpPreDot i s hR ((P.step (true, j) true _ trivial).obj Z) := by
  let Z' : P.H (nextSector (true, i) true
      (nextSector (true, j) true (nextSector (true, i) false s))) := (P.castH hs).obj Z
  have h₁ := (P.mixedJ_supernatural j i s hR).naturality
    (P.T.dot_mem i (P.muP_preE i
      (nextSector (true, j) true (nextSector (true, i) false s))) |>
      TwoSupercategory.whiskerRight_mem Z')
  have h₂ := congrArg (P.step (true, i) false s hR).map
    (P.preCrossNe_slideR j i hij.symm (nextSector (true, i) false s) hs Z)
  simp only [Functor.map_comp, Functor.map_smul] at h₂
  have hz (p : ZMod 2) : sign k p = zsign k p := by
    fin_cases p <;> simp [sign, zsign]
  simp only [mul_assoc, SKM.zmod2_mul_self, hz] at h₁
  dsimp only [Functor.comp_map] at h₁
  have h₁' := congrArg (fun f => f ≫
    (P.step (true, i) false s hR).map
      (P.preCrossNe j i (nextSector (true, i) false s) hs Z)) h₁
  have h₂' := congrArg (fun f =>
    (P.mixedJ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).hom ≫ f) h₂
  simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc] at h₁' h₂'
  have hh := h₁'.trans h₂'.symm
  simpa only [adjacentReverseMove, rpPreDot, rpObj, Z', step, homContentPreE,
    homContentPostE, homPre, homPost, Functor.comp_obj, Functor.comp_map,
    Category.assoc] using hh

/-- The repeated reservoir dot crosses twice, so the two spectator signs cancel. -/
theorem adjacentReverseMove_postDot :
    (P.step (true, j) true s trivial).map
        (P.rpPostDot i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)) ≫
      P.adjacentReverseMove i j s hR hs Z =
    P.adjacentReverseMove i j s hR hs Z ≫
      P.rpPostDot i s hR ((P.step (true, j) true _ trivial).obj Z) := by
  have h₁ := P.prPostDot_comp_mixedJ_ne j i s hR
    ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))
  have h₂ := (P.dotDiag_supernatural i false s hR).naturality
    ((P.preCrossNe_supernatural j i (nextSector (true, i) false s) hs).mem Z)
  have hz (p : ZMod 2) : sign k p = zsign k p := by
    fin_cases p <;> simp [sign, zsign]
  have hp : D.parity i * (D.parity j * D.parity i) = D.parity i * D.parity j := by
    rw [mul_left_comm, SKM.zmod2_mul_self, mul_comm]
  simp only [hp, hz] at h₂
  have h₂' := congrArg (fun f => zsign k (D.parity i * D.parity j) • f) h₂
  simp only [smul_smul, zsign_mul_self', one_smul] at h₂'
  dsimp only [adjacentReverseMove, rpPostDot]
  rw [← Category.assoc]
  erw [h₁]
  rw [Linear.smul_comp, Category.assoc]
  erw [← h₂']
  rw [Linear.comp_smul, smul_smul, mul_comm (D.parity j), zsign_mul_self', one_smul]
  simp only [Category.assoc]
  rfl

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
