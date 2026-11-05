import OddMath.QuiverHecke.SwappedAssembly.Sigma.FactorWindowInverse
import OddMath.SKM.RouquierHomPrePointwiseSlide
import OddMath.SKM.RouquierHomPreAutWindows

/-! # Probe slide and dotted windows in the literal padded corners

The pure-probe inputs to CentralInverse/ResidualComparison, following
SwappedHomInversion §2 (1) and §3 (6). Both dots come from the actual raw
probe unit. The normalized cap and unit are the given factor maps. The
missing target and the height-zero boundary are retained.
-/
noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM

namespace ProbeWindow
variable {C : Type*} [Category C]

/-- A native automorphism in model-to-native corner coordinates. -/
def cornerAut {X Y : C} (e : X ≅ Y) (a : Aut Y) : Aut X :=
  (Aut.autMulEquivOfIso e).symm a

/-- Every integral power uses the same actual corner chart. -/
theorem cornerAut_zpow_hom {X Y : C} (e : X ≅ Y) (a : Aut Y) (n : ℤ) :
    (cornerAut e a ^ n).hom = e.hom ≫ (a ^ n).hom ≫ e.inv := by
  rw [cornerAut, ← map_zpow]
  rfl

/-- A slide retains its cap and unit under the actual two corner charts. -/
theorem slide_coordinates [Preadditive C] {X Y O X' Y' : C}
    {s : X ⟶ Y} {x : End X} {y : End Y} {v : X ⟶ O} {u : O ⟶ Y} {q : ℤ}
    (H : s ≫ y - q • (x ≫ s) = v ≫ u) (a : X' ≅ X) (b : Y' ≅ Y) :
    (a.hom ≫ s ≫ b.inv) ≫ (b.hom ≫ y ≫ b.inv) -
      q • ((a.hom ≫ x ≫ a.inv) ≫ (a.hom ≫ s ≫ b.inv)) =
      (a.hom ≫ v) ≫ (u ≫ b.inv) := by
  have H' := congrArg (fun f => a.hom ≫ f ≫ b.inv) H
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.comp_sub,
    Preadditive.sub_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp] using H'
end ProbeWindow

namespace ProbeReservoir
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k} (P : ProbeReservoir k B D Sc)

/-- The native probe automorphism uses the specified dot and its actual
inverse, before an output or corner chart is selected. -/
def probeDotAut (i : I)
    (hdot : ∀ {a b : X} (h : a + D.α i = b), IsIso (P.T.dot i h))
    {a b m : X} (h : -b + D.α i = -a) (Z : homWeightSector P.T.obj P.W.obj a m) :
    Aut ((homContentPreE P.T P.W.obj i m h).obj Z) :=
  letI := hdot h
  homPreDotAut P.T P.W i h Z

variable {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]
  (i : I) (t : Sector I) (Z : P.H t) (E : P.H t ⥤ C) [E.Additive]
  (hdot : ∀ {a b : X} (h : a + D.α i = b), IsIso (P.T.dot i h))

/-- The source dot is the actual raw pre dot on the prescribed `E F`
source, evaluated and transported to the literal padded probe corner. -/
def centralPaddedProbeX : Aut (sectorFamilyCorner (fun a => StepValid (up i) a t)
    (fun a => E.obj (P.centralSourceFactor i t Z a)) true) :=
  ProbeWindow.cornerAut (P.centralSourceCornerIso i t Z E ⟨true, by trivial⟩)
    (Functor.mapAut _ E (P.probeDotAut i hdot (P.muP_preE i t)
      ((homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj Z)))

/-- The target dot passes through the actual normalized right adjoint.
At the absent padded target it is the unique zero-object automorphism. -/
def centralPaddedProbeY : Aut (sectorFamilyCorner (fun a => StepValid (dn i) a t)
    (fun a => E.obj (P.centralTargetFactor i t Z a)) true) :=
  if hb : StepValid (dn i) true t then
    ProbeWindow.cornerAut (P.centralTargetCornerIso i t Z E ⟨true, hb⟩)
      (Functor.mapAut _ E (Functor.mapAut _
        (homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preF i hb))
        (P.probeDotAut i hdot (P.muP_preF i hb) Z)))
  else Iso.refl _

omit [Preadditive C] [E.Additive] in
/-- The charted source automorphism retains the actual raw probe dot. -/
theorem centralPaddedProbeX_hom : (P.centralPaddedProbeX i t Z E hdot).hom =
    (P.centralSourceCornerIso i t Z E ⟨true, by trivial⟩).hom ≫
      E.map (homReservoirDot P.T P.W.obj i (P.muM t) (P.muP_preE i t)
        ((homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj Z)) ≫
      (P.centralSourceCornerIso i t Z E ⟨true, by trivial⟩).inv := rfl

omit [Preadditive C] [E.Additive] in
/-- The occupied target automorphism is the normalized right adjoint's
image of the same raw probe dot. -/
theorem centralPaddedProbeY_hom (hb : StepValid (dn i) true t) :
    (P.centralPaddedProbeY i t Z E hdot).hom =
      (P.centralTargetCornerIso i t Z E ⟨true, hb⟩).hom ≫
        E.map ((homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preF i hb)).map
          (homReservoirDot P.T P.W.obj i (P.muM t) (P.muP_preF i hb) Z)) ≫
        (P.centralTargetCornerIso i t Z E ⟨true, hb⟩).inv := by
  simp only [centralPaddedProbeY, dite_eq_left hb]; rfl

omit [E.Additive] in
/-- The actual padded principal has the prescribed native mate coordinate. -/
theorem centralPaddedProbeSigma_eq (c : P.CrossCoeff) (hb : StepValid (dn i) true t) :
    P.centralPaddedSigma c i t Z E true true =
      (P.centralSourceCornerIso i t Z E ⟨true, by trivial⟩).hom ≫
        E.map (homContentPreMate P.T P.W.obj i (P.muM t)
          (P.muP_preE i t) (P.muP_preF i hb) Z) ≫
        (P.centralTargetCornerIso i t Z E ⟨true, hb⟩).inv := by
  simp only [centralPaddedSigma, dite_eq_left (show StepValid (up i) true t from by trivial),
    dite_eq_left hb, centralFactorSigma, homContentPreMate]

omit [E.Additive] in
/-- The zero-exponent padded cap is the actual normalized counit. -/
theorem centralPaddedProbeCap_zero : P.centralPaddedCap i t Z E true 0 =
    (P.centralSourceCornerIso i t Z E ⟨true, by trivial⟩).hom ≫
      E.map ((homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i
        (P.muM t) (P.muP_preE i t)).counit.app Z) := by
  simp only [centralPaddedCap, dite_eq_left (show StepValid (up i) true t from by trivial),
    centralFactorCap, homReservoirCap, pow_zero, End.one_def, Category.id_comp]

omit [E.Additive] in
/-- The occupied zero-exponent padded unit is the actual normalized unit. -/
theorem centralPaddedProbeUnit_zero (hb : StepValid (dn i) true t) :
    P.centralPaddedUnit i t Z E true 0 =
      E.map ((homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i
        (P.muM t) (P.muP_preF i hb)).unit.app Z) ≫
        (P.centralTargetCornerIso i t Z E ⟨true, hb⟩).inv := by
  rw [centralPaddedUnit, dite_eq_left hb, centralFactorUnit, homReservoirCup,
    pow_zero, End.one_def, (homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preF i hb)).map_id]
  congr 2
  exact Category.comp_id _

omit [E.Additive] in
/-- Every actual nonnegative padded cap row is the power of the same
source automorphism used in the separated mixed-bend expansion. -/
theorem centralPaddedProbe_cap_power (n : ℕ) :
    P.centralPaddedCap i t Z E true n =
      (P.centralPaddedProbeX i t Z E hdot ^ (n : ℤ)).hom ≫
        P.centralPaddedCap i t Z E true 0 := by
  let : IsIso (P.T.dot i (P.muP_preE i t)) := hdot (P.muP_preE i t)
  have H := congrArg (fun f =>
    (P.centralSourceCornerIso i t Z E ⟨true, by trivial⟩).hom ≫ E.map f)
    (homReservoirCap_aut P.T P.W i (P.muP_preE i t) n Z)
  simpa only [centralPaddedCap, dite_eq_left (show StepValid (up i) true t from by trivial),
    centralFactorCap, centralPaddedProbeX, ProbeWindow.cornerAut_zpow_hom,
    map_aut_zpow_hom, Functor.map_comp, centralSourceFactor,
    Category.assoc, Iso.inv_hom_id_assoc, probeDotAut] using H

omit [E.Additive] in
/-- Every nonnegative padded unit column uses the same target
automorphism, including the literal zero column at an absent target. -/
theorem centralPaddedProbe_unit_power (n : ℕ) :
    P.centralPaddedUnit i t Z E true n = P.centralPaddedUnit i t Z E true 0 ≫
      (P.centralPaddedProbeY i t Z E hdot ^ (n : ℤ)).hom := by
  by_cases hb : StepValid (dn i) true t
  · let : IsIso (P.T.dot i (P.muP_preF i hb)) := hdot (P.muP_preF i hb)
    have H := congrArg (fun f => E.map f ≫
      (P.centralTargetCornerIso i t Z E ⟨true, hb⟩).inv)
      (homReservoirCup_aut P.T P.W i (P.muP_preF i hb) n Z)
    simpa only [centralPaddedUnit, dite_eq_left hb, centralFactorUnit,
      centralPaddedProbeY, ProbeWindow.cornerAut_zpow_hom, map_aut_zpow_hom,
      Functor.map_comp, centralTargetFactor, Functor.comp_obj,
      Category.assoc, Iso.inv_hom_id_assoc, probeDotAut] using H
  · have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (dn i) a t)
        (fun a => E.obj (P.centralTargetFactor i t Z a)) true) := by
      simpa only [sectorFamilyCorner, dite_eq_right hb] using Limits.isZero_zero C
    exact hz.eq_of_tgt _ _

/-- The literal padded probe principal, its two actual dot units, and
the normalized undotted cap/unit satisfy the residual-comparison slide. -/
theorem centralPaddedProbe_slide (c : P.CrossCoeff) :
    P.centralPaddedSigma c i t Z E true true ≫ (P.centralPaddedProbeY i t Z E hdot).hom -
      koszulSign (D.parity i) (D.parity i) •
        ((P.centralPaddedProbeX i t Z E hdot).hom ≫ P.centralPaddedSigma c i t Z E true true) =
      P.centralPaddedCap i t Z E true 0 ≫ P.centralPaddedUnit i t Z E true 0 := by
  by_cases hb : StepValid (dn i) true t
  · have ha : StepValid (up i) true t := by trivial
    have H := ProbeWindow.slide_coordinates
      (homContentPreMate_slide_map P.T P.W.obj i (P.muM t)
        (P.muP_preE i t) (P.muP_preF i hb) E Z)
      (P.centralSourceCornerIso i t Z E ⟨true, ha⟩)
      (P.centralTargetCornerIso i t Z E ⟨true, hb⟩)
    simp only [P.centralPaddedProbeSigma_eq i t Z E c hb,
      P.centralPaddedProbeX_hom i t Z E hdot, P.centralPaddedProbeY_hom i t Z E hdot hb,
      P.centralPaddedProbeCap_zero i t Z E, P.centralPaddedProbeUnit_zero i t Z E hb]
    exact H
  · have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (dn i) a t)
        (fun a => E.obj (P.centralTargetFactor i t Z a)) true) := by
      simpa only [sectorFamilyCorner, dite_eq_right hb] using Limits.isZero_zero C
    exact hz.eq_of_tgt _ _

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
