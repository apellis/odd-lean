/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.MoreGenerators
import OddMath.Diagrams.OddNilHecke.DotTranslation

/-!
# Inverse coordinates and bubble moments under odd dot translation

Supporting the odd-height coefficient-detection route to Brundan–Ellis,
arXiv:1701.04133v2, Section 8. The categorical identities below separate
the coordinate calculation from existence of a translated full action.
-/
noncomputable section
namespace OddMath.SKM.OddDotTranslation
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] {Z X : C}

/-- Odd rows gain the immediately preceding even row times the exterior
coefficient. This is the row operation induced by translating an odd dot. -/
def shiftedCap (v : ℕ → (X ⟶ Z)) (d : Z ⟶ Z) (r : ℕ) : X ⟶ Z :=
  if r % 2 = 1 then v r + v (r - 1) ≫ d else v r

/-- The cap-row operation has the explicit inverse obtained by negating
the coefficient. It does not require division or a domain hypothesis. -/
theorem shiftedCap_inverse (v : ℕ → (X ⟶ Z)) (d : Z ⟶ Z) :
    shiftedCap (shiftedCap v d) (-d) = v := by
  funext r
  by_cases ho : r % 2 = 1
  · have hp : ¬(r - 1) % 2 = 1 := by omega
    simp [shiftedCap, ho, hp, Preadditive.comp_neg]
  · simp [shiftedCap, ho]

/-- The final inverse column keeps all of its coordinates under the
translation row operation, because its predecessor coordinates vanish. -/
theorem last_column_coordinates (v : ℕ → (X ⟶ Z)) (d : Z ⟶ Z)
    (e : Z ⟶ X) (m : ℕ)
    (he : ∀ r ≤ m, e ≫ v r = if r = m then 𝟙 Z else 0) :
    ∀ r ≤ m, e ≫ shiftedCap v d r = if r = m then 𝟙 Z else 0 := by
  intro r hr
  by_cases ho : r % 2 = 1
  · have hp : r - 1 < m := by omega
    simp only [shiftedCap, ite_eq_left ho, Preadditive.comp_add, ← Category.assoc,
      he r hr, he (r - 1) (by omega), ite_eq_right (Nat.ne_of_lt hp), Limits.zero_comp,
      add_zero]
  · simpa only [shiftedCap, ite_eq_right ho] using he r hr

/-- At an odd positive height, the normalized moment gains precisely the
external odd coefficient, provided the last inverse column has been retained
and its even-parity naturality and bottom normalization have been supplied. -/
theorem odd_moment_shift (x dX : End X) (dZ : Z ⟶ Z) (e : Z ⟶ X)
    (v : X ⟶ Z) (m : ℕ)
    (hd : dX * dX = 0) (hx : x * dX + dX * x = 0)
    (hnat : e ≫ dX = dZ ≫ e) (hbottom : e ≫ (x ^ (2 * m)) ≫ v = 𝟙 Z) :
    e ≫ ((x + dX) ^ (2 * m + 1)) ≫ v =
      e ≫ (x ^ (2 * m + 1)) ≫ v + dZ := by
  rw [OddMath.OddNilHecke.DotTranslation.odd_pow x dX hd hx]
  change e ≫ ((show X ⟶ X from x ^ (2 * m + 1)) +
    (dX ≫ (x ^ (2 * m)) : X ⟶ X)) ≫ v = _
  rw [Preadditive.add_comp, Preadditive.comp_add]
  simp only [Category.assoc]
  rw [← Category.assoc e dX, hnat, Category.assoc, hbottom,
    Category.comp_id]

/-- The even moments do not change under the same translation. -/
theorem even_moment_fixed (x dX : End X) (e : Z ⟶ X) (v : X ⟶ Z) (m : ℕ)
    (hd : dX * dX = 0) (hx : x * dX + dX * x = 0) :
    e ≫ ((x + dX) ^ (2 * m)) ≫ v = e ≫ (x ^ (2 * m)) ≫ v := by
  rw [OddMath.OddNilHecke.DotTranslation.even_pow x dX hd hx]

end OddMath.SKM.OddDotTranslation

namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe w
variable {I : Type u} {W : Type v} [AddCommGroup W] {D : Datum I W}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- The actual source's normalized positive-height left cup retains its
last inverse-column coordinates under odd translation of the cap rows. -/
theorem etaP_shifted_cap_coordinates (cs : CScalars Sc) (i : I) (μ : W)
    (m : ℕ) (hh : D.h i μ = (m : ℤ) + 1)
    (d : End ((pres D Sc).obj (ob D μ []))) :
    ∀ r ≤ m,
      ((↑(cs.c μ i)⁻¹ : k) • etaP cs i μ) ≫
        OddDotTranslation.shiftedCap
          (fun s => cl D Sc μ [up i, dn i] [] (epsL i s)) d r =
      if r = m then 𝟙 _ else 0 := by
  apply OddDotTranslation.last_column_coordinates
  intro r hr
  rw [Linear.smul_comp, eq_2_13_c cs i μ r (by omega)]
  by_cases hrm : r = m
  · simp [hh, hrm, smul_smul]
  · have hrm' : (r : ℤ) ≠ D.h i μ - 1 := by omega
    simp [hrm, hrm']

end OddMath.SKM
