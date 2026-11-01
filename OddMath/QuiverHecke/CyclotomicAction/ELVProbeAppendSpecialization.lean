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

theorem elvProbeHeightWordEntry_affineUnit {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    elvProbeHeightWordEntry D m Sc s t
      ((ELVOld.ideal D Sc cut s.val t.val).mkQ (ELVOld.affineUnit D Sc cut s.val t.val f)) =
      probeHeightMk D m Sc n (FiniteHomMatrix.single t s f) := by
  rw [elvProbeHeightWordEntry_mk, elvProbeScalarHom_affineUnit]

/-- The canonical restricted old append uses the already checked height append map. -/
theorem probeOldWordEntry_append (ν : List I) (i : I)
    {v w : ELVOld.OldContentCategory D Sc cut ν} (f : v ⟶ w) :
    probeOldWordEntry D m Sc (i :: ν) ((ELVOld.oldContentAppend D Sc cut ν i).map f) =
      heightAppend D Sc a i ν.length (probeOldWordEntry D m Sc ν f) := by
  exact (elvProbeHeightWordEntry_append D m Sc i
    (probeContentWord ν (ELVOld.oldContentWord D Sc cut ν v))
    (probeContentWord ν (ELVOld.oldContentWord D Sc cut ν w)) f).symm

/-- The actual old append-dot component specializes to the literal probe last dot. -/
theorem elvProbeOldAppendDot_image {n : ℕ} (s : Word I n) (i : I) :
    elvProbeWordEntry D m Sc (appendWord i s) (appendWord i s)
      (ELVOld.CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut i ⟨s.val⟩) =
      (cyclotomicWordEnd D Sc a (appendWord i s)
        (dotE D Sc (s.val ++ [i]) n)).val := by
  rw [ELVOld.CyclotomicCrossingTensor.oldAppendDotComponent_eq]
  change elvProbeHeightWordEntry D m Sc (appendWord i s) (appendWord i s)
    ((ELVOld.ideal D Sc cut _ _).mkQ
      (ELVOld.affineUnit D Sc cut _ _ (dotE D Sc (s.val ++ [i]) s.val.length ^ 1))) = _
  rw [pow_one, elvProbeHeightWordEntry_affineUnit, s.property]
  rfl

/-- The scalar image of the actual old component, in its actual unital word corner. -/
def elvProbeOldAppendDotCorner {n : ℕ} (s : Word I n) (i : I) :
    CyclotomicWordCorner D Sc a (appendWord i s) :=
  ⟨elvProbeWordEntry D m Sc (appendWord i s) (appendWord i s)
    (ELVOld.CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut i ⟨s.val⟩), by
      rw [elvProbeOldAppendDot_image]
      exact (cyclotomicWordEnd D Sc a (appendWord i s)
        (dotE D Sc (s.val ++ [i]) n)).property⟩

theorem elvProbeOldAppendDotCorner_eq {n : ℕ} (s : Word I n) (i : I) :
    elvProbeOldAppendDotCorner D m Sc s i =
      cyclotomicWordEnd D Sc a (appendWord i s) (dotE D Sc (s.val ++ [i]) n) :=
  Subtype.ext (elvProbeOldAppendDot_image D m Sc s i)

/-- Actual old append-dot images are units; no finite-dimensionality input is needed. -/
theorem elvProbeOldAppendDotCorner_isUnit {n : ℕ} (s : Word I n) (i : I) :
    IsUnit (elvProbeOldAppendDotCorner D m Sc s i) := by
  rw [elvProbeOldAppendDotCorner_eq]
  exact probeWord_dots_isUnit D Sc m n n (Nat.lt_succ_self n) (appendWord i s)

end OddMath.QuiverHecke

