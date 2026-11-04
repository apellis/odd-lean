import OddMath.QuiverHecke.SwappedAssembly.Sigma.ProbeSlideWindow
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SupportedFactorWindowInverse

/-! # Actual OLD probe slide and windows on supported padded sectors

The probe slide and row/column inputs of CentralInverse/ResidualComparison
are discharged for the prescribed OLD/ELV construction. Invertible dots
come from the actual OLD probe factor, with its normalized precomposition
adjunction. No regular-input replacement or central inverse is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local instance supportedProbeSlideHomPi (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

/-- The whole prescribed OLD probe dot is invertible at every native
edge, before choosing a supported Hom input or an evaluation component. -/
theorem probeWindowDot_isIso [Finite I] (i : I) {a b : X} (h : a + D.α i = b) :
    IsIso ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).T.dot i h) := by
  let := Fintype.ofFinite I
  exact (isUnit_iff_isIso _).mp
    (elvProbeReservoir_dot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i h)

variable {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]

/-- The actual source probe automorphism in the padded source corner. -/
def probeWindowX [Finite I] (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (E : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t ⥤ C) [E.Additive] :=
  (P).centralPaddedProbeX i t Z.obj E
    (fun {_a _b} h => probeWindowDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i h)

/-- The actual target probe automorphism, with its zero-corner boundary. -/
def probeWindowY [Finite I] (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (E : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t ⥤ C) [E.Additive] :=
  (P).centralPaddedProbeY i t Z.obj E
    (fun {_a _b} h => probeWindowDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i h)

/-- At an absent target, exact support compares the literal padded zero
with the actual native normalized precomposition roundtrip. -/
def probeWindowTargetZeroIso (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (E : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t ⥤ C) [E.Additive]
    (hb : ¬StepValid (dn i) true t) {ρ : X} (h : -ρ + D.α i = -(P).muP t) :
    sectorFamilyCorner (fun a => StepValid (dn i) a t)
      (fun a => E.obj ((P).centralTargetFactor i t Z.obj a)) true ≅
      E.obj ((homContentPreF (P).T (P).W.obj i ((P).muM t) h).obj
        ((homContentPreE (P).T (P).W.obj i ((P).muM t) h).obj Z.obj)) :=
  sectorFamilyZeroCornerIso (fun a => StepValid (dn i) a t)
    (fun a => E.obj ((P).centralTargetFactor i t Z.obj a)) true hb _
    (E.map_isZero (probeTarget_absent_isZero D Sc m cutoff bound ΛP ΛR hP hR i t Z hb h))

/-- The absent-target convention is literally the transported actual
probe dot unit. The needed native vanishing is proved from exact support. -/
theorem probeWindowY_of_absent_native [Finite I] (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (E : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t ⥤ C) [E.Additive]
    (hb : ¬StepValid (dn i) true t) {ρ : X} (h : -ρ + D.α i = -(P).muP t) :
    probeWindowY D Sc m cutoff bound ΛP ΛR hP hR i t Z E =
      ProbeWindow.cornerAut (probeWindowTargetZeroIso D Sc m cutoff bound ΛP ΛR hP hR i t Z E hb h)
        (Functor.mapAut _ E (Functor.mapAut _
          (homContentPreF (P).T (P).W.obj i ((P).muM t) h)
          ((P).nativeProbeDotAut i
            (fun {_a _b} h' => probeWindowDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i h') h Z.obj))) :=
  (P).centralPaddedProbeY_of_absent_native i t Z.obj E
    (fun {_a _b} h' => probeWindowDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i h') hb h
    (probeTarget_absent_isZero D Sc m cutoff bound ΛP ΛR hP hR i t Z hb h)

/-- Every literal padded cap row uses the same raw probe automorphism
as the mixed-bend series, at every nonnegative exponent and local height. -/
theorem probe_cap_power [Finite I] (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (E : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t ⥤ C) [E.Additive] (n : ℕ) :
    (P).centralPaddedCap i t Z.obj E true n =
      (probeWindowX D Sc m cutoff bound ΛP ΛR hP hR i t Z E ^ (n : ℤ)).hom ≫
        (P).centralPaddedCap i t Z.obj E true 0 :=
  (P).centralPaddedProbe_cap_power i t Z.obj E
    (fun {_a _b} h => probeWindowDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i h) n

/-- Every literal padded unit column uses the normalized right adjoint
of that raw dot, including all absent-target and height-zero columns. -/
theorem probe_unit_power [Finite I] (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (E : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t ⥤ C) [E.Additive] (n : ℕ) :
    (P).centralPaddedUnit i t Z.obj E true n = (P).centralPaddedUnit i t Z.obj E true 0 ≫
      (probeWindowY D Sc m cutoff bound ΛP ΛR hP hR i t Z E ^ (n : ℤ)).hom :=
  (P).centralPaddedProbe_unit_power i t Z.obj E
    (fun {_a _b} h => probeWindowDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i h) n

/-- The actual padded pure-probe principal satisfies exactly the slide
required by the two-sector residual comparison. -/
theorem probe_slide [Finite I]
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff)
    (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (E : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t ⥤ C) [E.Additive] :
    (P).centralPaddedSigma c i t Z.obj E true true ≫
        (probeWindowY D Sc m cutoff bound ΛP ΛR hP hR i t Z E).hom -
      koszulSign (D.parity i) (D.parity i) •
        ((probeWindowX D Sc m cutoff bound ΛP ΛR hP hR i t Z E).hom ≫
          (P).centralPaddedSigma c i t Z.obj E true true) =
      (P).centralPaddedCap i t Z.obj E true 0 ≫ (P).centralPaddedUnit i t Z.obj E true 0 :=
  (P).centralPaddedProbe_slide i t Z.obj E
    (fun {_a _b} h => probeWindowDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i h) c

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
