/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVQPRegularity

/-!
# Regularity of the moving-chain norm polynomial at the prepend endpoint

The factors in `DeformedBoundaryDivision.md` §2 are regular on the full-ELV
prepend old-only quotient. Repeated factors retain both the squared difference
and, at odd colour, the sum of squares. This is not the QP polynomial.

`projection_movingNormProduct_regular` uses the existing old-Hom coordinates:
positive moving powers shift their finite support, while old actions do not.
The distinct-colour leading coefficients are the prescribed units `Sc.t`.
Identification with a chain composite and transport to the append-old quotient
are separate obligations; neither is assumed or claimed here.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- One endpoint norm factor, with the moving dot in position zero. -/
def movingNormFactor (i : I) (v : List I) (x : I) (b : ℕ) :
    End ((pres D Sc).obj (ob D (i :: v))) :=
  let t := dotE D Sc (i :: v) 0
  let y := dotE D Sc (i :: v) (b + 1)
  if x = i then
    if D.parity i = 1 then -((y ^ 2 - t ^ 2) ^ 2 * (t ^ 2 + y ^ 2))
    else -((y - t) ^ 2)
  else qPoly D Sc t y i x

/-- The ordered endpoint polynomial, independently of either chain composite. -/
def movingNormProduct (i : I) (v : List I) :
    End ((pres D Sc).obj (ob D (i :: v))) :=
  ((List.range v.length).map fun b => movingNormFactor D Sc i v (v.getD b i) b).prod

namespace ELVOld
variable (cutoff : I → ℕ)

/-- The square difference cancels by its positive moving degree, not by flatness. -/
theorem projection_dotSquareDifference_regular (i : I) (v w : List I) (b : ℕ)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _
        (dotE D Sc (i :: v) (b + 1) ^ 2 - dotE D Sc (i :: v) 0 ^ 2) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  rw [map_sub, Preadditive.sub_comp, map_sub,
    projection_old_dotPower, projection_moving_dotPower] at hh
  apply movingPower_eq_oldSource D Sc cutoff 0 i v w 2
    ((by decide : ∀ p : ZMod 2, (2 : ℕ) • p = 0) (D.parity i)) (by decide)
    (sourceDotPower D Sc cutoff v b 2)
  exact (sub_eq_zero.mp hh).symm

/-- The odd sum-of-squares factor also cancels, over the full coefficient quotient. -/
theorem projection_dotSquareSum_regular (i : I) (v w : List I) (b : ℕ)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _
        (dotE D Sc (i :: v) 0 ^ 2 + dotE D Sc (i :: v) (b + 1) ^ 2) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  rw [map_add, Preadditive.add_comp, map_add,
    projection_moving_dotPower, projection_old_dotPower] at hh
  apply movingPower_eq_oldSource D Sc cutoff 0 i v w 2
    ((by decide : ∀ p : ZMod 2, (2 : ℕ) • p = 0) (D.parity i)) (by decide)
    (-sourceDotPower D Sc cutoff v b 2)
  change signedMovingPowerTarget D Sc cutoff i v w 2
      (projection D Sc cutoff i v w h) =
    projection D Sc cutoff i v w (insert D Sc cutoff i v v
      (-sourceDotPower D Sc cutoff v b 2) ≫ h)
  rw [map_neg, Preadditive.neg_comp, map_neg]
  exact eq_neg_of_add_eq_zero_left hh

/-- Every specified local norm factor detects old-only classes. -/
theorem projection_movingNormFactor_regular (i : I) (v w : List I) (x : I) (b : ℕ)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (movingNormFactor D Sc i v x b) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  unfold movingNormFactor at hh
  split_ifs at hh with hx hp
  · rw [map_neg, Preadditive.neg_comp, map_neg, neg_eq_zero,
      End.mul_def, affineUnit_comp, Category.assoc] at hh
    have hs := projection_dotSquareSum_regular D Sc cutoff i v w b _ hh
    rw [pow_two (dotE D Sc (i :: v) (b + 1) ^ 2 - dotE D Sc (i :: v) 0 ^ 2),
      End.mul_def, affineUnit_comp, Category.assoc] at hs
    exact projection_dotSquareDifference_regular D Sc cutoff i v w b h
      (projection_dotSquareDifference_regular D Sc cutoff i v w b _ hs)
  · rw [map_neg, Preadditive.neg_comp, map_neg, neg_eq_zero,
      pow_two, End.mul_def, affineUnit_comp, Category.assoc] at hh
    exact projection_dotDifference_regular D Sc cutoff i v w b h
      (projection_dotDifference_regular D Sc cutoff i v w b _ hh)
  · exact projection_qPoly_regular D Sc cutoff i x (Ne.symm hx) v w b h hh

/-- Ordered products of the explicit norm factors remain regular. -/
theorem projection_movingNormFactorList_regular (i : I) (v w : List I) (l : List ℕ)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _
        ((l.map fun b => movingNormFactor D Sc i v (v.getD b i) b).prod) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  induction l generalizing h with
  | nil => simpa only [List.map_nil, List.prod_nil, End.one_def, affineUnit_id,
      Category.id_comp] using hh
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons, End.mul_def, affineUnit_comp, Category.assoc] at hh
    exact projection_movingNormFactor_regular D Sc cutoff i v w (v.getD b i) b h (ih _ hh)

/-- The full prescribed norm polynomial is regular on the prepend old-only quotient.
This does not identify it with the reverse-chain composite or assert Q injectivity. -/
theorem projection_movingNormProduct_regular (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (movingNormProduct D Sc i v) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 :=
  projection_movingNormFactorList_regular D Sc cutoff i v w (List.range v.length) h hh

end ELVOld
end OddMath.QuiverHecke
