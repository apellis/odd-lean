import OddMath.QuiverHecke.CyclotomicAction.ELVProbeContentBends
import OddMath.QuiverHecke.CyclotomicAction.ELVContentHomZero
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PaddedBendWindowEquations
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SupportedProbeSlideWindow

/-! # Finite mixed bends in the padded output-content corners

`SwappedHomInversion.md` §3 (4)–(6): the chosen ELV coefficient's finite
series retain the entire probe input functor and the literal padded
central entries. The output-content truncation may be increased to the
reservoir window height, including at absent central corners.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction SwappedAssembly
universe u
local instance paddedContentBendHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (m cutoff : I → ℕ) (bound : ℕ) (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local notation "out" "[" t "," δ "]" =>
  elvProbeBendContentEvaluation D Sc m cutoff bound ΛP ΛR hP hR t δ

attribute [local irreducible] elvProbeReservoir elvProbeCrossCoeff

/-- The Dx series can meet any prescribed length without requiring an
occupied reservoir source or probe target. -/
theorem elvProbeDx_content_separated_windows_above [Finite I]
    (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (δ : WeightBlocks D ΛR ((P).muM t))
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (minimum : ℕ) :
    ∃ N, minimum ≤ N ∧
      ELVProbeDxContentSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t Z δ sy hc N := by
  have : Fact Sc.PureNilpotent := ⟨hc.noPure.pureNilpotent⟩
  let := Fintype.ofFinite I
  let : IsIso ((P).T.dot i ((P).muP_preE i t)) :=
    (isUnit_iff_isIso _).mp
      (elvProbeReservoir_dot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i ((P).muP_preE i t))
  obtain ⟨n, hn⟩ := elvProbeDxContentOuterDot_isNilpotent
    D Sc m cutoff bound ΛP ΛR hP hR i t Z δ sy hc
  have hn' := pow_eq_zero_of_le (Nat.le_max_left n minimum) hn
  rcases parity_eq_zero_or_one (D.parity i) with hi | hi
  · refine ⟨max n minimum, Nat.le_max_right _ _, ?_⟩
    exact probeToReservoirBend_even_separated (P) i t Z out[t,δ]
      (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc)
      (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc) hi _ hn'
  · refine ⟨2 * max n minimum, (by omega), ?_⟩
    exact probeToReservoirBend_odd_separated (P) i t Z out[t,δ]
      (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc)
      (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc) hi _ hn'

/-- The chosen Dx equation in the actual padded output-content corners. -/
def ELVProbePaddedDxContentSeparatedAt [Finite I] (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (δ : WeightBlocks D ΛR ((P).muM t))
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ) : Prop :=
  haveI : Fact Sc.PureNilpotent := ⟨hc.noPure.pureNilpotent⟩
  (P).CentralPaddedDxSeparatedAt i t Z out[t,δ]
    (fun {_a _b} h => SupportedSectors.probeWindowDot_isIso
      D Sc m cutoff bound ΛP ΛR hP hR i h)
    (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc) N

/-- The chosen Cx equation retains the padded zero-source and zero-target cases. -/
def ELVProbePaddedCxContentSeparatedAt [Finite I] (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (δ : WeightBlocks D ΛR ((P).muM t))
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ) : Prop :=
  haveI : Fact Sc.PureNilpotent := ⟨hc.noPure.pureNilpotent⟩
  (P).CentralPaddedCxSeparatedAt i t Z out[t,δ]
    (fun {_a _b} h => SupportedSectors.probeWindowDot_isIso
      D Sc m cutoff bound ΛP ΛR hP hR i h)
    (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc) N

/-- One output-content length supplies the two exact padded bend equations
above any minimum, retaining the full probe input functor and every corner. -/
theorem elvProbe_content_padded_central_separated_windows_above [Finite I]
    (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (δ : WeightBlocks D ΛR ((P).muM t))
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (minimum : ℕ) :
    ∃ N, minimum ≤ N ∧
      ELVProbePaddedDxContentSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t Z δ sy hc N ∧
      ELVProbePaddedCxContentSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t Z δ sy hc N := by
  have : Fact Sc.PureNilpotent := ⟨hc.noPure.pureNilpotent⟩
  let hdot := fun {a b : X} (h : a + D.α i = b) =>
    SupportedSectors.probeWindowDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i h
  let c := elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc
  have hDx (N : ℕ)
      (H : ELVProbeDxContentSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t Z δ sy hc N) :
      ELVProbePaddedDxContentSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t Z δ sy hc N :=
    (P).centralPaddedDx_separated i t Z out[t,δ] hdot c N H
  by_cases hb : StepValid (false, i) true t
  · by_cases hv : StepValid (true, i) false t
    · obtain ⟨N, hN, hD, hC⟩ := elvProbe_content_central_separated_windows_above
        D Sc m cutoff bound ΛP ΛR hP hR i t hb hv Z δ sy hc minimum
      exact ⟨N, hN, hDx N hD,
        (P).centralPaddedCx_separated i t Z out[t,δ] hdot c hb hv N hC⟩
    · obtain ⟨N, hN, hD⟩ := elvProbeDx_content_separated_windows_above
        D Sc m cutoff bound ΛP ΛR hP hR i t Z δ sy hc minimum
      exact ⟨N, hN, hDx N hD,
        (P).centralPaddedCx_separated_of_source_absent i t Z out[t,δ] hdot c hv N⟩
  · obtain ⟨N, hN, hD⟩ := elvProbeDx_content_separated_windows_above
      D Sc m cutoff bound ΛP ΛR hP hR i t Z δ sy hc minimum
    exact ⟨N, hN, hDx N hD,
      (P).centralPaddedCx_separated_of_target_absent i t Z out[t,δ] hdot c hb N⟩

end OddMath.QuiverHecke
