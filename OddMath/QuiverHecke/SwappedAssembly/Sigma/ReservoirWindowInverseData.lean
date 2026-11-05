import OddMath.QuiverHecke.SwappedAssembly.Sigma.SupportedFactorWindowInverse

/-! # Chosen reservoir inverse entries in padded factor coordinates

The reservoir elimination in SwappedHomInversion §§4–6 uses the specified
principal inverse and its finite window entries. These records retain
those entries of `W.loc`, through the native Hom and padded corner charts,
so that contracted residual coefficients can be compared to the prescribed
reservoir closures. No inverse is selected from an existential assertion.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct
open scoped Classical
namespace OddMath.QuiverHecke.SwappedAssembly
namespace ProbeWindow
variable {C : Type*} [Category C] [Preadditive C]

/-- A cap inverse retaining its named principal and finite inverse columns. -/
structure CapInverseData {X Y O : C} {n : ℕ} (s : X ⟶ Y) (v : Fin n → (X ⟶ O)) where
  principal : Y ⟶ X
  window : Fin n → (O ⟶ X)
  isInverse : IsCapInverse s v principal window

/-- A unit inverse retaining its named principal and finite inverse rows. -/
structure CupInverseData {X Y O : C} {n : ℕ} (s : X ⟶ Y) (u : Fin n → (O ⟶ Y)) where
  principal : Y ⟶ X
  window : Fin n → (Y ⟶ O)
  isInverse : IsCupInverse s u principal window

/-- Negating the principal entries retains the specified cap columns. -/
def CapInverseData.negPrincipal {X Y O : C} {n : ℕ} {s : X ⟶ Y}
    {v : Fin n → (X ⟶ O)} (J : CapInverseData s v) : CapInverseData (-s) v where
  principal := -J.principal
  window := J.window
  isInverse := J.isInverse.neg_principal

/-- Negating the principal entries retains the specified unit rows. -/
def CupInverseData.negPrincipal {X Y O : C} {n : ℕ} {s : X ⟶ Y}
    {u : Fin n → (O ⟶ Y)} (J : CupInverseData s u) : CupInverseData (-s) u where
  principal := -J.principal
  window := J.window
  isInverse := J.isInverse.neg_principal
end ProbeWindow

namespace ProbeReservoir
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k} (P : ProbeReservoir k B D Sc)
  {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]
  (c : P.CrossCoeff) (i : I) (t : Sector I) (Z : P.H t)
  (E : P.H t ⥤ C) [E.Additive]

/-- Retain the specified principal and finite entries in literal padded coordinates. -/
def centralPaddedReservoir_capInverseData (ha : StepValid (up i) false t)
    (hh : 0 ≤ D.h i (P.muM t)) :
    ProbeWindow.CapInverseData (O := E.obj Z)
      (X := sectorFamilyCorner (fun a => StepValid (up i) a t)
        (fun a => E.obj (P.centralSourceFactor i t Z a)) false)
      (Y := sectorFamilyCorner (fun a => StepValid (dn i) a t)
        (fun a => E.obj (P.centralTargetFactor i t Z a)) false)
      (P.centralPaddedSigma c i t Z E false false)
      (fun a : Fin (D.h i (P.muM t)).toNat => P.centralPaddedCap i t Z E false a) := by
  have hb : StepValid (dn i) false t := by trivial
  let J := homContentPostInvPos P.T.obj P.W i t.1 (P.muP t)
    (P.muM_postE i ha) (P.muM_postF i t) hh Z
  have H := ((FactorWindowInverse.cap J).map E).coordinates
    (P.centralSourceCornerIso i t Z E ⟨false, ha⟩)
    (P.centralTargetCornerIso i t Z E ⟨false, hb⟩)
  have hs : (P.centralSourceCornerIso i t Z E ⟨false, ha⟩).hom ≫ E.map (homContentPostMate P.T.obj P.W i t.1 (P.muP t)
      (P.muM_postE i ha) (P.muM_postF i t) Z) ≫ (P.centralTargetCornerIso i t Z E ⟨false, hb⟩).inv =
      P.centralPaddedSigma c i t Z E false false := by
    simp only [centralPaddedSigma, dite_eq_left ha, dite_eq_left hb,
      centralFactorSigma, homContentPostMate]
  rw [hs] at H
  have hv : (fun r : Fin (D.h i (P.muM t)).toNat => (P.centralSourceCornerIso i t Z E ⟨false, ha⟩).hom ≫
      E.map (homContentPostCap P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i ha) r Z)) =
      (fun r : Fin (D.h i (P.muM t)).toNat => P.centralPaddedCap i t Z E false r) := by
    funext r
    simp only [centralPaddedCap, dite_eq_left ha, centralFactorCap]
  rw [hv] at H
  exact ⟨_, _, H⟩

/-- Retain the specified principal and finite entries in literal padded coordinates. -/
def centralPaddedReservoir_cupInverseData (ha : StepValid (up i) false t)
    (hh : D.h i (P.muM t) ≤ 0) :
    ProbeWindow.CupInverseData (O := E.obj Z)
      (X := sectorFamilyCorner (fun a => StepValid (up i) a t)
        (fun a => E.obj (P.centralSourceFactor i t Z a)) false)
      (Y := sectorFamilyCorner (fun a => StepValid (dn i) a t)
        (fun a => E.obj (P.centralTargetFactor i t Z a)) false)
      (P.centralPaddedSigma c i t Z E false false)
      (fun a : Fin (-D.h i (P.muM t)).toNat => P.centralPaddedUnit i t Z E false a) := by
  have hb : StepValid (dn i) false t := by trivial
  let J := homContentPostInvNeg P.T.obj P.W i t.1 (P.muP t)
    (P.muM_postE i ha) (P.muM_postF i t) hh Z
  have H := ((FactorWindowInverse.cup J).map E).coordinates
    (P.centralSourceCornerIso i t Z E ⟨false, ha⟩)
    (P.centralTargetCornerIso i t Z E ⟨false, hb⟩)
  have hs : (P.centralSourceCornerIso i t Z E ⟨false, ha⟩).hom ≫ E.map (homContentPostMate P.T.obj P.W i t.1 (P.muP t)
      (P.muM_postE i ha) (P.muM_postF i t) Z) ≫ (P.centralTargetCornerIso i t Z E ⟨false, hb⟩).inv =
      P.centralPaddedSigma c i t Z E false false := by
    simp only [centralPaddedSigma, dite_eq_left ha, dite_eq_left hb,
      centralFactorSigma, homContentPostMate]
  rw [hs] at H
  have hu : (fun r : Fin (-D.h i (P.muM t)).toNat =>
      E.map (homContentPostCup P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t) r Z) ≫
        (P.centralTargetCornerIso i t Z E ⟨false, hb⟩).inv) =
      (fun r : Fin (-D.h i (P.muM t)).toNat => P.centralPaddedUnit i t Z E false r) := by
    funext r
    simp only [centralPaddedUnit, dite_eq_left hb, centralFactorUnit]
  rw [hu] at H
  exact ⟨_, _, H⟩

/-- Retain the specified principal and finite entries in literal padded coordinates. -/
def centralPaddedReservoir_capInverseData_of_source_isZero
    (ha : ¬StepValid (up i) false t) {μ : X} (h : μ + D.α i = P.muM t)
    (hzero : Limits.IsZero ((homContentPostE P.T.obj P.W i t.1 (P.muP t) h).obj
      ((homContentPostF P.T.obj P.W i t.1 (P.muP t) h).obj Z)))
    (hh : 0 ≤ D.h i (P.muM t)) :
    ProbeWindow.CapInverseData (O := E.obj Z)
      (X := sectorFamilyCorner (fun a => StepValid (up i) a t)
        (fun a => E.obj (P.centralSourceFactor i t Z a)) false)
      (Y := sectorFamilyCorner (fun a => StepValid (dn i) a t)
        (fun a => E.obj (P.centralTargetFactor i t Z a)) false)
      (P.centralPaddedSigma c i t Z E false false)
      (fun a : Fin (D.h i (P.muM t)).toNat => P.centralPaddedCap i t Z E false a) := by
  have hb : StepValid (dn i) false t := by trivial
  let a := sectorFamilyZeroCornerIso (fun a => StepValid (up i) a t)
    (fun a => E.obj (P.centralSourceFactor i t Z a)) false ha _ (E.map_isZero hzero)
  let b := P.centralTargetCornerIso i t Z E ⟨false, hb⟩
  let J := homContentPostInvPos P.T.obj P.W i t.1 (P.muP t) h (P.muM_postF i t) hh Z
  have H := ((FactorWindowInverse.cap J).map E).coordinates a b
  have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (up i) a t)
      (fun a => E.obj (P.centralSourceFactor i t Z a)) false) := by
    simpa only [sectorFamilyCorner, dite_eq_right ha] using Limits.isZero_zero C
  have hs : a.hom ≫ E.map (homContentPostMate P.T.obj P.W i t.1 (P.muP t)
      h (P.muM_postF i t) Z) ≫ b.inv = P.centralPaddedSigma c i t Z E false false :=
    hz.eq_of_src _ _
  have hv : (fun r : Fin (D.h i (P.muM t)).toNat =>
      a.hom ≫ E.map (homContentPostCap P.T.obj P.W i t.1 (P.muP t) h r Z)) =
      (fun r : Fin (D.h i (P.muM t)).toNat => P.centralPaddedCap i t Z E false r) := by
    funext r
    exact hz.eq_of_src _ _
  rw [hs, hv] at H
  exact ⟨_, _, H⟩

/-- Retain the specified principal and finite entries in literal padded coordinates. -/
def centralPaddedReservoir_cupInverseData_of_source_isZero
    (ha : ¬StepValid (up i) false t) {μ : X} (h : μ + D.α i = P.muM t)
    (hzero : Limits.IsZero ((homContentPostE P.T.obj P.W i t.1 (P.muP t) h).obj
      ((homContentPostF P.T.obj P.W i t.1 (P.muP t) h).obj Z)))
    (hh : D.h i (P.muM t) ≤ 0) :
    ProbeWindow.CupInverseData (O := E.obj Z)
      (X := sectorFamilyCorner (fun a => StepValid (up i) a t)
        (fun a => E.obj (P.centralSourceFactor i t Z a)) false)
      (Y := sectorFamilyCorner (fun a => StepValid (dn i) a t)
        (fun a => E.obj (P.centralTargetFactor i t Z a)) false)
      (P.centralPaddedSigma c i t Z E false false)
      (fun a : Fin (-D.h i (P.muM t)).toNat => P.centralPaddedUnit i t Z E false a) := by
  have hb : StepValid (dn i) false t := by trivial
  let a := sectorFamilyZeroCornerIso (fun a => StepValid (up i) a t)
    (fun a => E.obj (P.centralSourceFactor i t Z a)) false ha _ (E.map_isZero hzero)
  let b := P.centralTargetCornerIso i t Z E ⟨false, hb⟩
  let J := homContentPostInvNeg P.T.obj P.W i t.1 (P.muP t) h (P.muM_postF i t) hh Z
  have H := ((FactorWindowInverse.cup J).map E).coordinates a b
  have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (up i) a t)
      (fun a => E.obj (P.centralSourceFactor i t Z a)) false) := by
    simpa only [sectorFamilyCorner, dite_eq_right ha] using Limits.isZero_zero C
  have hs : a.hom ≫ E.map (homContentPostMate P.T.obj P.W i t.1 (P.muP t)
      h (P.muM_postF i t) Z) ≫ b.inv = P.centralPaddedSigma c i t Z E false false :=
    hz.eq_of_src _ _
  rw [hs] at H
  have hu : (fun r : Fin (-D.h i (P.muM t)).toNat =>
      E.map (homContentPostCup P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t) r Z) ≫ b.inv) =
      (fun r : Fin (-D.h i (P.muM t)).toNat => P.centralPaddedUnit i t Z E false r) := by
    funext r
    simp only [centralPaddedUnit, dite_eq_left hb, centralFactorUnit, b]
  rw [hu] at H
  exact ⟨_, _, H⟩

end ProbeReservoir

namespace SupportedSectors
open CyclotomicAction ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local instance reservoirWindowHomPi (A B : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

variable {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]

/-- The actual prescribed reservoir inverse, with named principal and finite entries. -/
def reservoirCapInverseData
    (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (E : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t ⥤ C) [E.Additive]
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff) (hh : 0 ≤ D.h i ((P).muM t)) :
    ProbeWindow.CapInverseData (O := E.obj Z.obj)
      ((P).centralPaddedSigma c i t Z.obj E false false)
      (fun r : Fin (D.h i ((P).muM t)).toNat => (P).centralPaddedCap i t Z.obj E false r) :=
  if ha : StepValid (up i) false t then
    (P).centralPaddedReservoir_capInverseData c i t Z.obj E ha hh
  else
    let h : (P).muM t - D.α i + D.α i = (P).muM t := sub_add_cancel _ _
    (P).centralPaddedReservoir_capInverseData_of_source_isZero c i t Z.obj E ha h
      (reservoirSource_absent_isZero D Sc m cutoff bound ΛP ΛR hP hR i t Z ha h) hh

/-- At an absent source the chosen principal maps into the literal zero corner. -/
theorem reservoirCapInverseData_principal_of_absent
    (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (E : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t ⥤ C) [E.Additive]
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff) (hh : 0 ≤ D.h i ((P).muM t)) (ha : ¬StepValid (up i) false t) :
    (reservoirCapInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z E c hh).principal = 0 := by
  have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (up i) a t)
      (fun a => E.obj ((P).centralSourceFactor i t Z.obj a)) false) := by
    simpa only [sectorFamilyCorner, dite_eq_right ha] using Limits.isZero_zero C
  exact hz.eq_of_tgt _ _

/-- The actual prescribed reservoir inverse, with named principal and finite entries. -/
def reservoirCupInverseData
    (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (E : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t ⥤ C) [E.Additive]
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff) (hh : D.h i ((P).muM t) ≤ 0) :
    ProbeWindow.CupInverseData (O := E.obj Z.obj)
      ((P).centralPaddedSigma c i t Z.obj E false false)
      (fun r : Fin (-D.h i ((P).muM t)).toNat => (P).centralPaddedUnit i t Z.obj E false r) :=
  if ha : StepValid (up i) false t then
    (P).centralPaddedReservoir_cupInverseData c i t Z.obj E ha hh
  else
    let h : (P).muM t - D.α i + D.α i = (P).muM t := sub_add_cancel _ _
    (P).centralPaddedReservoir_cupInverseData_of_source_isZero c i t Z.obj E ha h
      (reservoirSource_absent_isZero D Sc m cutoff bound ΛP ΛR hP hR i t Z ha h) hh

/-- At an absent source the chosen principal maps into the literal zero corner. -/
theorem reservoirCupInverseData_principal_of_absent
    (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (E : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t ⥤ C) [E.Additive]
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff) (hh : D.h i ((P).muM t) ≤ 0) (ha : ¬StepValid (up i) false t) :
    (reservoirCupInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z E c hh).principal = 0 := by
  have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (up i) a t)
      (fun a => E.obj ((P).centralSourceFactor i t Z.obj a)) false) := by
    simpa only [sectorFamilyCorner, dite_eq_right ha] using Limits.isZero_zero C
  exact hz.eq_of_tgt _ _

/-- An absent cap column lands in the same literal zero corner. -/
theorem reservoirCapInverseData_window_of_absent
    (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (E : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t ⥤ C) [E.Additive]
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff) (hh : 0 ≤ D.h i ((P).muM t))
    (ha : ¬StepValid (up i) false t) (r : Fin (D.h i ((P).muM t)).toNat) :
    (reservoirCapInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z E c hh).window r = 0 := by
  have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (up i) a t)
      (fun a => E.obj ((P).centralSourceFactor i t Z.obj a)) false) := by
    simpa only [sectorFamilyCorner, dite_eq_right ha] using Limits.isZero_zero C
  exact hz.eq_of_tgt _ _

end SupportedSectors
end OddMath.QuiverHecke.SwappedAssembly
