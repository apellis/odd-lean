import OddMath.QuiverHecke.SwappedAssembly.Sigma.FactorWindowInverse
import OddMath.QuiverHecke.SwappedAssembly.SupportedPaths
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReservoir

/-! # Prescribed factor inverses on supported OLD/ELV objects

The absent-corner input in CentralMatrixAttachment and
SwappedHomInversion §2 follows from replete exact-content support. The
source and target vanish as whole functors; the local inverse is then
transferred to the literal zero-padded pure factor matrix.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
open scoped Classical
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR

local instance factorHomPi (A B : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

/-- The native reservoir roundtrip at a missing predecessor is zero on
every supported whole Hom object, with the input parity shift retained. -/
theorem reservoirSource_absent_isZero (i : I) (t : Sector I)
    (Z : H D Sc' m cutoff bound ΛP ΛR t)
    (hi : ¬StepValid (up i) false t) {μ : X}
    (h : μ + D.α i = (P).muM t) :
    Limits.IsZero ((homContentPostE (P).T.obj (P).W i t.1 ((P).muP t) h).obj
      ((homContentPostF (P).T.obj (P).W i t.1 ((P).muP t) h).obj Z.obj)) := by
  apply (homContentPostE (P).T.obj (P).W i t.1 ((P).muP t) h).map_isZero
  have hs := ContentHomSupport.shift_supported D Sc' m cutoff bound
    (probeBlock D ΛP t) (reservoirBlock D ΛR t) (homContentShift D i t.1) Z.property
  have ha : i ∉ (reservoirBlock D ΛR t).1 := by
    simpa only [← reservoir_valid_iff] using hi
  exact ContentHomSupport.postF_supported_absent_isZero D Sc' m cutoff bound
    (probeBlock D ΛP t) (reservoirBlock D ΛR t) i h hs ha

/-- The missing probe target vanishes as a whole functor, before
additive evaluation and independently of the central mixed coefficients. -/
theorem probeTarget_absent_isZero (i : I) (t : Sector I)
    (Z : H D Sc' m cutoff bound ΛP ΛR t)
    (hi : ¬StepValid (dn i) true t) {ρ : X}
    (h : -ρ + D.α i = -(P).muP t) :
    Limits.IsZero ((homContentPreF (P).T (P).W.obj i ((P).muM t) h).obj
      ((homContentPreE (P).T (P).W.obj i ((P).muM t) h).obj Z.obj)) := by
  apply (homContentPreF (P).T (P).W.obj i ((P).muM t) h).map_isZero
  have ha : i ∉ (probeBlock D ΛP t).1 := by
    simpa only [← probe_valid_iff] using hi
  exact ContentHomSupport.preE_supported_absent_isZero D Sc' m cutoff bound
    (probeBlock D ΛP t) (reservoirBlock D ΛR t) i h Z.property ha

variable {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]

/-- The normalized probe cap inverse on every supported sector,
including a missing probe target and all inverse cap columns. -/
theorem probe_capInverse
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff)
    (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (E : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t ⥤ C) [E.Additive]
    (hh : D.h i (-(P).muP t) ≤ 0) :
    ∃ j A, ProbeWindow.IsCapInverse ((P).centralPaddedSigma c i t Z.obj E true true)
      (fun a : Fin (-D.h i (-(P).muP t)).toNat => (P).centralPaddedCap i t Z.obj E true a) j A :=
  if hb : StepValid (dn i) true t then
    (P).centralPaddedProbe_capInverse c i t Z.obj E hb hh
  else
    let h : -((P).muP t + D.α i) + D.α i = -(P).muP t :=
      (congrArg (fun z : X => z + D.α i) (neg_add ((P).muP t) (D.α i))).trans
        (neg_add_cancel_right (-(P).muP t) (D.α i))
    (P).centralPaddedProbe_capInverse_of_target_isZero c i t Z.obj E hb h
      (probeTarget_absent_isZero D Sc m cutoff bound ΛP ΛR hP hR i t Z hb h) hh

/-- The normalized probe unit inverse on every supported sector,
including a missing probe target and the whole chosen inverse rows. -/
theorem probe_cupInverse
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff)
    (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (E : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t ⥤ C) [E.Additive]
    (hh : 0 ≤ D.h i (-(P).muP t)) :
    ∃ j B, ProbeWindow.IsCupInverse ((P).centralPaddedSigma c i t Z.obj E true true)
      (fun a : Fin (D.h i (-(P).muP t)).toNat => (P).centralPaddedUnit i t Z.obj E true a) j B :=
  if hb : StepValid (dn i) true t then
    (P).centralPaddedProbe_cupInverse c i t Z.obj E hb hh
  else
    let h : -((P).muP t + D.α i) + D.α i = -(P).muP t :=
      (congrArg (fun z : X => z + D.α i) (neg_add ((P).muP t) (D.α i))).trans
        (neg_add_cancel_right (-(P).muP t) (D.α i))
    (P).centralPaddedProbe_cupInverse_of_target_isZero c i t Z.obj E hb h
      (probeTarget_absent_isZero D Sc m cutoff bound ΛP ΛR hP hR i t Z hb h) hh

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
