/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.LastCrossing
import OddMath.QuiverHecke.CyclotomicAction.InductionComposition

/-!
# The homogeneous crossing between composition corners

Ports the crossing construction of
`Categorification/KLR/CyclotomicAction/Induction.lean`, the intertwiner method of
`Categorification/KLR/CyclotomicAction/Slides.lean` and the corner comparison of
`Categorification/KLR/CyclotomicAction/Comparison.lean`.
The map from `compositionCorner i j` to `compositionCorner j i` is
`x ↦ (-1)^{|i||j||x|} x τᵢⱼ`. Here `τᵢⱼ` is the diagram from the word
ending in `[i,j]` to the word ending in `[j,i]`; right multiplication reverses
this direction on the left ideals. The sign gives signed left linearity and
ordinary right linearity in the superbimodule convention. No inverse is claimed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i j : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "P" => compositionCorner D Sc i j a ha n
local notation "Q" => compositionCorner D Sc j i a ha n
local notation "GC" => cyclotomicParity D Sc a ha (n + 1 + 1)
local notation "GA" => cyclotomicParity D Sc a ha n
local notation "c" => cyclotomicLastCrossing D Sc i j a n
local notation "d" => D.parity i * D.parity j

private theorem crossing_mul_mem (x : CyclotomicAlgebra D Sc a (n + 1 + 1))
    (_hx : x ∈ compositionCornerSubmodule D Sc i j a n) :
    x * c ∈ compositionCornerSubmodule D Sc j i a n := by
  change (x * c) * cyclotomicAppend D Sc j a (n + 1) (cyclotomicAppend D Sc i a n 1) = x * c
  rw [mul_assoc, (cyclotomicLastCrossing_corner D Sc i j a n).2]

/-- Parity sign followed by right multiplication by the concrete crossing. -/
def compositionCrossingLinear : (P).toSVec ⟶ (Q).toSVec :=
  SVec.ofHom ((P).toSVec.sgn d) ≫
    SVec.restrictHom ((SuperBimodule.regular GC).ract c) (crossing_mul_mem D Sc i j a n)

/-- The crossing map has parity `|i||j|`. -/
theorem compositionCrossingLinear_parity :
    compositionCrossingLinear D Sc i j a ha n ∈ SVec.parityHom (P).toSVec (Q).toSVec d := by
  change compositionCrossingLinear D Sc i j a ha n ∈ parity (R := k) (P).toSVec (Q).toSVec d
  unfold compositionCrossingLinear
  have hd := SVec.restrictHom_mem (hU := compositionCorner_odd_mem D Sc i j a ha n)
    (hU' := compositionCorner_odd_mem D Sc j i a ha n)
    ((SuperBimodule.regular GC).ract_mem d c
      (cyclotomicLastCrossing_parity D Sc i j a ha n)) (crossing_mul_mem D Sc i j a n)
  simpa only [compositionCorner, compositionCornerSpace, SuperBimodule.regular, zero_add] using
    Supercategory.comp_mem (SVec.sgn_mem (P).toSVec d) hd

private theorem crossing_sgn_action {p : ZMod 2} {f : (P).toSVec ⟶ (P).toSVec}
    (hf : f ∈ SVec.parityHom (P).toSVec (P).toSVec p) (x : (P).toSVec) :
    (P).toSVec.sgn d (f x) = sign k (p * d) • f ((P).toSVec.sgn d x) :=
  LinearMap.congr_fun (SVec.sgn_comp_of_mem hf d) x

/-- The two action laws follow from the proved signed crossing intertwiner. -/
theorem compositionCrossingLinear_isHom :
    SuperBimodule.IsHom P Q (compositionCrossingLinear D Sc i j a ha n) := by
  apply (SuperBimodule.isHom_iff_of_mem (compositionCrossingLinear_parity D Sc i j a ha n)).2
  constructor
  · intro p b hb
    apply SVec.hom_ext
    intro x
    have h := crossing_sgn_action D Sc i j a ha n ((P).lact_mem p b hb) x
    apply Subtype.ext
    change ((P).toSVec.sgn d ((P).lact b x)).val * c =
      sign k (p * d) • (b * (((P).toSVec.sgn d x).val * c))
    rw [h]
    change (sign k (p * d) • (b * ((P).toSVec.sgn d x).val)) * c = _
    rw [smul_mul_assoc, mul_assoc]
  · intro r
    induction r using SuperBimodule.alg_induction_on GA with
    | zero => simp
    | add r s hr hs => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hr, hs]
    | hom p r hr =>
      apply SVec.hom_ext
      intro x
      have h := crossing_sgn_action D Sc i j a ha n ((P).ract_mem p r hr) x
      apply Subtype.ext
      change ((P).toSVec.sgn d ((P).ract r x)).val * c =
        (((P).toSVec.sgn d x).val * c) *
          cyclotomicAppend D Sc j a (n + 1) (cyclotomicAppend D Sc i a n r)
      rw [h]
      change (sign k (p * d) • (((P).toSVec.sgn d x).val *
        cyclotomicAppend D Sc i a (n + 1) (cyclotomicAppend D Sc j a n r))) * c = _
      rw [smul_mul_assoc, mul_assoc, cyclotomicLastCrossing_intertwines D Sc i j a ha n hr,
        mul_smul_comm, Supercategory.sign_mul, Int.cast_smul_eq_zsmul, koszulSign_smul_smul, mul_assoc]

/-- The homogeneous superbimodule map between the two composition corners. -/
def compositionSuperCrossing : P ⟶ Q :=
  ⟨compositionCrossingLinear D Sc i j a ha n, compositionCrossingLinear_isHom D Sc i j a ha n⟩

theorem compositionSuperCrossing_parity :
    compositionSuperCrossing D Sc i j a ha n ∈ parity (R := k) P Q d :=
  SuperBimodule.mem_parity_iff.2 (compositionCrossingLinear_parity D Sc i j a ha n)

/-- Evaluation on a homogeneous element displays the sign explicitly. -/
theorem compositionSuperCrossing_apply {p : ZMod 2} (x : (P).toSVec)
    (hx : x ∈ (P).toSVec.part p) :
    ((compositionSuperCrossing D Sc i j a ha n).1 x).val =
      koszulSign p d • (x.val * c) := by
  change ((P).toSVec.sgn d x).val * c = _
  rw [SVec.sgn_apply_of_mem d hx]
  change (sign k (p * d) • x.val) * c = _
  rw [smul_mul_assoc, Supercategory.sign_mul, Int.cast_smul_eq_zsmul]

end OddMath.QuiverHecke
