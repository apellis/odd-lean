import OddMath.QuiverHecke.SwappedAssembly.Sigma.AugmentedSectorEntries

/-! # The native two-sector augmented matrix

The evaluated matrices of Brundan–Ellis (1.13)–(1.14) are precisely the
two-sector matrices of the prescribed mates, bends and cap/unit rows.
Absent path corners are padded by zero objects after evaluation.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM Classical
open scoped ZeroObject
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)
variable {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]

/-- A native principal map, padded by zero at either absent pure corner. -/
def centralPaddedSigma (c : P.CrossCoeff) (i : I) (t : Sector I) (Z : P.H t)
    (E : P.H t ⥤ C) (a b : Bool) :
    sectorFamilyCorner (fun a => StepValid (up i) a t)
      (fun a => E.obj (P.centralSourceFactor i t Z a)) a ⟶
    sectorFamilyCorner (fun b => StepValid (dn i) b t)
      (fun b => E.obj (P.centralTargetFactor i t Z b)) b :=
  if ha : StepValid (up i) a t then
    if hb : StepValid (dn i) b t then
      (P.centralSourceCornerIso i t Z E ⟨a, ha⟩).hom ≫
        E.map (P.centralFactorSigma c i t Z ⟨a, ha⟩ ⟨b, hb⟩) ≫
        (P.centralTargetCornerIso i t Z E ⟨b, hb⟩).inv
    else 0
  else 0

/-- The native cap row, padded by zero at an absent reservoir source. -/
def centralPaddedCap (i : I) (t : Sector I) (Z : P.H t) (E : P.H t ⥤ C)
    (a : Bool) (n : ℕ) :
    sectorFamilyCorner (fun a => StepValid (up i) a t)
      (fun a => E.obj (P.centralSourceFactor i t Z a)) a ⟶ E.obj Z :=
  if ha : StepValid (up i) a t then
    (P.centralSourceCornerIso i t Z E ⟨a, ha⟩).hom ≫
      E.map (P.centralFactorCap i t Z n ⟨a, ha⟩)
  else 0

/-- The native unit column, padded by zero at an absent probe target. -/
def centralPaddedUnit (i : I) (t : Sector I) (Z : P.H t) (E : P.H t ⥤ C)
    (b : Bool) (n : ℕ) : E.obj Z ⟶
    sectorFamilyCorner (fun b => StepValid (dn i) b t)
      (fun b => E.obj (P.centralTargetFactor i t Z b)) b :=
  if hb : StepValid (dn i) b t then
    E.map (P.centralFactorUnit i t Z n ⟨b, hb⟩) ≫
      (P.centralTargetCornerIso i t Z E ⟨b, hb⟩).inv
  else 0

/-- The positive model contains the prescribed four principal maps and
every native dotted cap row, with the actual height window. -/
def augPosFactorMatrix (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) :=
  ProbeWindow.posMap (P.centralPaddedSigma c i t Z E false false)
    (P.centralPaddedSigma c i t Z E true true)
    (P.centralPaddedSigma c i t Z E false true)
    (P.centralPaddedSigma c i t Z E true false)
    (P.centralPaddedCap i t Z E false)
    (fun a : Fin (D.h i ν).toNat => P.centralPaddedCap i t Z E true a)

/-- The negative model retains minus of all four prescribed principal
maps, and the native unit columns in the actual height window. -/
def augNegFactorMatrix (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) :=
  ProbeWindow.negMap (-P.centralPaddedSigma c i t Z E false false)
    (-P.centralPaddedSigma c i t Z E true true)
    (-P.centralPaddedSigma c i t Z E false true)
    (-P.centralPaddedSigma c i t Z E true false)
    (P.centralPaddedUnit i t Z E false)
    (fun a : Fin (-D.h i ν).toNat => P.centralPaddedUnit i t Z E true a)

/-- The charted positive augmented matrix equals the prescribed native
two-sector model at every sector, including absent pure corners. -/
theorem augPosSectorMatrix_eq_factorMatrix (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) [Functor.Additive E] :
    P.augPosSectorMatrix c i ν t Z E = P.augPosFactorMatrix c i ν t Z E := by
  apply Mat_.hom_ext
  intro x y
  cases x with
  | none =>
    cases y with
    | none =>
      change (P.augPosSectorMatrix c i ν t Z E) none none = P.centralPaddedSigma c i t Z E false false
      by_cases ha : StepValid (up i) false t
      · by_cases hb : StepValid (dn i) false t
        · simpa only [sectorFamilyIndex, centralPaddedSigma, dite_eq_left ha, dite_eq_left hb,
            centralSourceSlotIso, centralTargetSlotIso] using
            P.augPosSectorMatrix_pure_factor c i ν t Z E ⟨false, ha⟩ ⟨false, hb⟩
        · have hz : Limits.IsZero (sectorFamilyCorner (fun b => StepValid (dn i) b t)
              (fun b => E.obj (P.centralTargetFactor i t Z b)) false) := by
            simpa only [sectorFamilyCorner, dite_eq_right hb] using Limits.isZero_zero C
          exact hz.eq_of_tgt _ _
      · have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (up i) a t)
            (fun a => E.obj (P.centralSourceFactor i t Z a)) false) := by
          simpa only [sectorFamilyCorner, dite_eq_right ha] using Limits.isZero_zero C
        exact hz.eq_of_src _ _
    | some y =>
      cases y with
      | none =>
        change (P.augPosSectorMatrix c i ν t Z E) none (some none) = P.centralPaddedSigma c i t Z E false true
        by_cases ha : StepValid (up i) false t
        · by_cases hb : StepValid (dn i) true t
          · simpa only [sectorFamilyIndex, centralPaddedSigma, dite_eq_left ha, dite_eq_left hb,
              centralSourceSlotIso, centralTargetSlotIso] using
              P.augPosSectorMatrix_pure_factor c i ν t Z E ⟨false, ha⟩ ⟨true, hb⟩
          · have hz : Limits.IsZero (sectorFamilyCorner (fun b => StepValid (dn i) b t)
                (fun b => E.obj (P.centralTargetFactor i t Z b)) true) := by
              simpa only [sectorFamilyCorner, dite_eq_right hb] using Limits.isZero_zero C
            exact hz.eq_of_tgt _ _
        · have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (up i) a t)
              (fun a => E.obj (P.centralSourceFactor i t Z a)) false) := by
            simpa only [sectorFamilyCorner, dite_eq_right ha] using Limits.isZero_zero C
          exact hz.eq_of_src _ _
      | some n =>
        change (P.augPosSectorMatrix c i ν t Z E) none (some (some n)) = P.centralPaddedCap i t Z E false n
        by_cases ha : StepValid (up i) false t
        · simpa only [sectorFamilyIndex, centralPaddedCap, dite_eq_left ha, centralSourceSlotIso] using
            P.augPosSectorMatrix_cap_factor c i ν t Z E ⟨false, ha⟩ n
        · have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (up i) a t)
              (fun a => E.obj (P.centralSourceFactor i t Z a)) false) := by
            simpa only [sectorFamilyCorner, dite_eq_right ha] using Limits.isZero_zero C
          exact hz.eq_of_src _ _
  | some x =>
    cases x with
    | none =>
      cases y with
      | none =>
        change (P.augPosSectorMatrix c i ν t Z E) (some none) none = P.centralPaddedSigma c i t Z E true false
        by_cases ha : StepValid (up i) true t
        · by_cases hb : StepValid (dn i) false t
          · simpa only [sectorFamilyIndex, centralPaddedSigma, dite_eq_left ha, dite_eq_left hb,
              centralSourceSlotIso, centralTargetSlotIso] using
              P.augPosSectorMatrix_pure_factor c i ν t Z E ⟨true, ha⟩ ⟨false, hb⟩
          · have hz : Limits.IsZero (sectorFamilyCorner (fun b => StepValid (dn i) b t)
                (fun b => E.obj (P.centralTargetFactor i t Z b)) false) := by
              simpa only [sectorFamilyCorner, dite_eq_right hb] using Limits.isZero_zero C
            exact hz.eq_of_tgt _ _
        · have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (up i) a t)
              (fun a => E.obj (P.centralSourceFactor i t Z a)) true) := by
            simpa only [sectorFamilyCorner, dite_eq_right ha] using Limits.isZero_zero C
          exact hz.eq_of_src _ _
      | some y =>
        cases y with
        | none =>
          change (P.augPosSectorMatrix c i ν t Z E) (some none) (some none) = P.centralPaddedSigma c i t Z E true true
          by_cases ha : StepValid (up i) true t
          · by_cases hb : StepValid (dn i) true t
            · simpa only [sectorFamilyIndex, centralPaddedSigma, dite_eq_left ha, dite_eq_left hb,
                centralSourceSlotIso, centralTargetSlotIso] using
                P.augPosSectorMatrix_pure_factor c i ν t Z E ⟨true, ha⟩ ⟨true, hb⟩
            · have hz : Limits.IsZero (sectorFamilyCorner (fun b => StepValid (dn i) b t)
                  (fun b => E.obj (P.centralTargetFactor i t Z b)) true) := by
                simpa only [sectorFamilyCorner, dite_eq_right hb] using Limits.isZero_zero C
              exact hz.eq_of_tgt _ _
          · have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (up i) a t)
                (fun a => E.obj (P.centralSourceFactor i t Z a)) true) := by
              simpa only [sectorFamilyCorner, dite_eq_right ha] using Limits.isZero_zero C
            exact hz.eq_of_src _ _
        | some n =>
          change (P.augPosSectorMatrix c i ν t Z E) (some none) (some (some n)) = P.centralPaddedCap i t Z E true n
          by_cases ha : StepValid (up i) true t
          · simpa only [sectorFamilyIndex, centralPaddedCap, dite_eq_left ha, centralSourceSlotIso] using
              P.augPosSectorMatrix_cap_factor c i ν t Z E ⟨true, ha⟩ n
          · have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (up i) a t)
                (fun a => E.obj (P.centralSourceFactor i t Z a)) true) := by
              simpa only [sectorFamilyCorner, dite_eq_right ha] using Limits.isZero_zero C
            exact hz.eq_of_src _ _
    | some x => exact Empty.elim x

/-- The charted negative augmented matrix equals the prescribed native
two-sector model, with all four negative principal signs retained. -/
theorem augNegSectorMatrix_eq_factorMatrix (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) [Functor.Additive E] :
    P.augNegSectorMatrix c i ν t Z E = P.augNegFactorMatrix c i ν t Z E := by
  apply Mat_.hom_ext
  intro x y
  cases y with
  | none =>
    cases x with
    | none =>
      change (P.augNegSectorMatrix c i ν t Z E) none none = -P.centralPaddedSigma c i t Z E false false
      by_cases ha : StepValid (up i) false t
      · by_cases hb : StepValid (dn i) false t
        · simpa only [sectorFamilyIndex, centralPaddedSigma, dite_eq_left ha, dite_eq_left hb,
            centralSourceSlotIso, centralTargetSlotIso] using
            P.augNegSectorMatrix_pure_factor c i ν t Z E ⟨false, ha⟩ ⟨false, hb⟩
        · have hz : Limits.IsZero (sectorFamilyCorner (fun b => StepValid (dn i) b t)
              (fun b => E.obj (P.centralTargetFactor i t Z b)) false) := by
            simpa only [sectorFamilyCorner, dite_eq_right hb] using Limits.isZero_zero C
          exact hz.eq_of_tgt _ _
      · have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (up i) a t)
            (fun a => E.obj (P.centralSourceFactor i t Z a)) false) := by
          simpa only [sectorFamilyCorner, dite_eq_right ha] using Limits.isZero_zero C
        exact hz.eq_of_src _ _
    | some x =>
      cases x with
      | none =>
        change (P.augNegSectorMatrix c i ν t Z E) (some none) none = -P.centralPaddedSigma c i t Z E true false
        by_cases ha : StepValid (up i) true t
        · by_cases hb : StepValid (dn i) false t
          · simpa only [sectorFamilyIndex, centralPaddedSigma, dite_eq_left ha, dite_eq_left hb,
              centralSourceSlotIso, centralTargetSlotIso] using
              P.augNegSectorMatrix_pure_factor c i ν t Z E ⟨true, ha⟩ ⟨false, hb⟩
          · have hz : Limits.IsZero (sectorFamilyCorner (fun b => StepValid (dn i) b t)
                (fun b => E.obj (P.centralTargetFactor i t Z b)) false) := by
              simpa only [sectorFamilyCorner, dite_eq_right hb] using Limits.isZero_zero C
            exact hz.eq_of_tgt _ _
        · have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (up i) a t)
              (fun a => E.obj (P.centralSourceFactor i t Z a)) true) := by
            simpa only [sectorFamilyCorner, dite_eq_right ha] using Limits.isZero_zero C
          exact hz.eq_of_src _ _
      | some n =>
        change (P.augNegSectorMatrix c i ν t Z E) (some (some n)) none = P.centralPaddedUnit i t Z E false n
        by_cases hb : StepValid (dn i) false t
        · simpa only [sectorFamilyIndex, centralPaddedUnit, dite_eq_left hb, centralTargetSlotIso] using
            P.augNegSectorMatrix_unit_factor c i ν t Z E n ⟨false, hb⟩
        · have hz : Limits.IsZero (sectorFamilyCorner (fun b => StepValid (dn i) b t)
              (fun b => E.obj (P.centralTargetFactor i t Z b)) false) := by
            simpa only [sectorFamilyCorner, dite_eq_right hb] using Limits.isZero_zero C
          exact hz.eq_of_tgt _ _
  | some y =>
    cases y with
    | none =>
      cases x with
      | none =>
        change (P.augNegSectorMatrix c i ν t Z E) none (some none) = -P.centralPaddedSigma c i t Z E false true
        by_cases ha : StepValid (up i) false t
        · by_cases hb : StepValid (dn i) true t
          · simpa only [sectorFamilyIndex, centralPaddedSigma, dite_eq_left ha, dite_eq_left hb,
              centralSourceSlotIso, centralTargetSlotIso] using
              P.augNegSectorMatrix_pure_factor c i ν t Z E ⟨false, ha⟩ ⟨true, hb⟩
          · have hz : Limits.IsZero (sectorFamilyCorner (fun b => StepValid (dn i) b t)
                (fun b => E.obj (P.centralTargetFactor i t Z b)) true) := by
              simpa only [sectorFamilyCorner, dite_eq_right hb] using Limits.isZero_zero C
            exact hz.eq_of_tgt _ _
        · have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (up i) a t)
              (fun a => E.obj (P.centralSourceFactor i t Z a)) false) := by
            simpa only [sectorFamilyCorner, dite_eq_right ha] using Limits.isZero_zero C
          exact hz.eq_of_src _ _
      | some x =>
        cases x with
        | none =>
          change (P.augNegSectorMatrix c i ν t Z E) (some none) (some none) = -P.centralPaddedSigma c i t Z E true true
          by_cases ha : StepValid (up i) true t
          · by_cases hb : StepValid (dn i) true t
            · simpa only [sectorFamilyIndex, centralPaddedSigma, dite_eq_left ha, dite_eq_left hb,
                centralSourceSlotIso, centralTargetSlotIso] using
                P.augNegSectorMatrix_pure_factor c i ν t Z E ⟨true, ha⟩ ⟨true, hb⟩
            · have hz : Limits.IsZero (sectorFamilyCorner (fun b => StepValid (dn i) b t)
                  (fun b => E.obj (P.centralTargetFactor i t Z b)) true) := by
                simpa only [sectorFamilyCorner, dite_eq_right hb] using Limits.isZero_zero C
              exact hz.eq_of_tgt _ _
          · have hz : Limits.IsZero (sectorFamilyCorner (fun a => StepValid (up i) a t)
                (fun a => E.obj (P.centralSourceFactor i t Z a)) true) := by
              simpa only [sectorFamilyCorner, dite_eq_right ha] using Limits.isZero_zero C
            exact hz.eq_of_src _ _
        | some n =>
          change (P.augNegSectorMatrix c i ν t Z E) (some (some n)) (some none) = P.centralPaddedUnit i t Z E true n
          by_cases hb : StepValid (dn i) true t
          · simpa only [sectorFamilyIndex, centralPaddedUnit, dite_eq_left hb, centralTargetSlotIso] using
              P.augNegSectorMatrix_unit_factor c i ν t Z E n ⟨true, hb⟩
          · have hz : Limits.IsZero (sectorFamilyCorner (fun b => StepValid (dn i) b t)
                (fun b => E.obj (P.centralTargetFactor i t Z b)) true) := by
              simpa only [sectorFamilyCorner, dite_eq_right hb] using Limits.isZero_zero C
            exact hz.eq_of_tgt _ _
    | some y => exact Empty.elim y

/-- The literal positive augmented matrix square uses the prescribed
native two-sector model, including every absent corner and height zero. -/
theorem augPosFactorMatrix_square (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) [Functor.Additive E] :
    (P.augPosSourceIso i ν t Z E).hom ≫ E.mapMat_.map (P.augPosMat c i ν t t Z) =
      P.augPosFactorMatrix c i ν t Z E ≫ (P.augPosTargetIso i ν t Z E).hom := by
  rw [← augPosSectorMatrix_eq_factorMatrix]
  exact P.augPosSectorMatrix_square c i ν t Z E

/-- The literal negative augmented matrix square uses the prescribed
negative native principal maps and the complete dotted unit window. -/
theorem augNegFactorMatrix_square (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) [Functor.Additive E] :
    (P.augNegSourceIso i ν t Z E).hom ≫ E.mapMat_.map (P.augNegMat c i ν t t Z) =
      P.augNegFactorMatrix c i ν t Z E ≫ (P.augNegTargetIso i ν t Z E).hom := by
  rw [← augNegSectorMatrix_eq_factorMatrix]
  exact P.augNegSectorMatrix_square c i ν t Z E

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
