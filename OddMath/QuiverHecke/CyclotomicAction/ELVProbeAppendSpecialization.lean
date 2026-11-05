import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOldModule
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ProbeAllUnits

/-! # Actual old append and dot under scalar probe specialization
These formulas compare the existing canonical old append and appended dot
with their literal ordinary probe images. The dot image is a unit in its
actual word corner at every height, including append from the vacuum.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ) (Sc : SKM.Scalars D k) [Fintype I]
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m

omit [Fintype I] in
/-- Unit-coefficient affine arrows specialize to themselves. -/
theorem elvProbeScalarHom_affineUnit {v w : List I}
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    elvProbeScalarHom D m Sc v w (ELVOld.affineUnit D Sc cut v w f) = f := by
  change (elvAffineScalarSpecialization D Sc cut (probeScalarValues D m)
      (probeScalarValues_vanish D m)).map
    (BoxProd.tmulHom (X := ELVOld.obj D Sc cut v) (Y := ELVOld.obj D Sc cut w)
      (SuperalgebraCat.ofElem 1) f) = f
  rw [elvAffineScalarSpecialization_tmul, SuperalgebraCat.toElem_ofElem, map_one, one_smul]

end OddMath.QuiverHecke
