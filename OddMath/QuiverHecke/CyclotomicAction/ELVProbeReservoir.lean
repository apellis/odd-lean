import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierMulticolour
import OddMath.QuiverHecke.SwappedAssembly.Sectors
import OddMath.SKM.RouquierFTriangle
import OddMath.QuiverHecke.CyclotomicAction.ParameterTwistPureNilpotent

/-! # The OLD probe and truncated ELV reservoir

SwappedActionAssembly F1–F2 and Brundan–Ellis Definition 1.5: use the
untruncated scalar-evaluated OLD probe with invertible dots and the
specified truncated ELV reservoir. Both retain their original-weight
actions and presentation parameters. The probe's normalized shifted
left adjunctions are constructed from its complete Rouquier family.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction SwappedAssembly
universe u
local instance elvProbeReservoirHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc

/-- The specified asymmetric pair of complete factor families, with their actual highest weights. -/
def elvProbeReservoir : ProbeReservoir k (PiSCat.{u,u,u + 1} k) D Sc where
  T := probeOldRouquierFamily D Sc' m ΛP hP
  W := elvRouquierFamily D Sc' cutoff bound ΛR hR
  leftAdj := (probeOldRouquierFamily D Sc' m ΛP hP).leftAdjoints
  probeRel := probeOldRouquierMulticolour D Sc m ΛP hP
  reservoirRel := elvRouquierMulticolour D Sc cutoff bound ΛR hR
  ΛP := ΛP
  ΛR := ΛR

theorem elvProbeReservoir_W :
    (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).W =
      elvRouquierFamily D Sc' cutoff bound ΛR hR := rfl

/-- The whole chosen probe dot is a unit, as required by the mixed denominators. -/
theorem elvProbeReservoir_dot_isUnit [Fact Sc.PureNilpotent] [Fintype I] (i : I) {x y : X} (h : x + D.α i = y) :
    IsUnit (show End ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).T.E i h) from
      (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).T.dot i h) :=
  probeOldRouquierFamily_dot_isUnit D Sc' m ΛP hP i h

end OddMath.QuiverHecke
