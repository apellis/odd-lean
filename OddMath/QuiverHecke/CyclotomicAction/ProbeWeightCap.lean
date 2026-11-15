import OddMath.QuiverHecke.CyclotomicAction.ProbeMixedBraid
import OddMath.QuiverHecke.SwappedAssembly.Sigma.BendWindowEquations
import OddMath.QuiverHecke.CyclotomicAction.ParameterUntwist
import OddMath.QuiverHecke.CyclotomicAction.ContentTriple
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PaddedBendWindowEquations
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SupportedProbeSlideWindow
import OddMath.QuiverHecke.CyclotomicAction.WeightDenominators
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SwappingReservoir
import OddMath.QuiverHecke.SwappedAssembly.Sigma.MixedEntryPureNilpotent
import OddMath.QuiverHecke.SwappedAssembly.Sigma.Permutation
import OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirProbeEntry
import OddMath.QuiverHecke.SwappedAssembly.Sigma.DistinctPureEntries
import OddMath.QuiverHecke.SwappedAssembly.Sigma.DistinctPureReservoirEntry
import OddMath.SKM.RouquierCanonicalDistinctLeftMate
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightQuadratic
import OddMath.SKM.RouquierInverseRelations
import OddMath.SKM.RouquierFTriangle
import OddMath.QuiverHecke.CyclotomicAction.ProbeCap
import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexWeight
import OddMath.QuiverHecke.CyclotomicAction.WeightMixed
import OddMath.SKM.RouquierShiftedAdjunction
import Mathlib.CategoryTheory.Conj
import OddMath.SKM.RouquierHomPreCoordinates
import OddMath.SKM.RouquierNormalizedHomAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightBraid
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts

/-!
# Probe weight cap

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Mixed bends at a whole output-content category

`SwappedHomInversion.md` §3 (4)–(6) and §4 (J): retain every probe input
while projecting to one reservoir output content. A fixed source-content
dot bound gives finite series in the same functor Hom category as the
content coefficient ideal. The exponent may depend on output content.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
set_option quotPrecheck false
open scoped BigOperators
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV CyclotomicAction SwappedAssembly
universe u
local instance contentBendHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (m cutoff : I → ℕ) (bound : ℕ) (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local notation "Sc'" => parameterTwist D Sc

/-- Project the reservoir output, retaining the complete probe-input functor. -/
def elvProbeBendContentEvaluation (t : Sector I)
    (δ : WeightBlocks D ΛR ((P).muM t)) :
    (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t ⥤
      ((P).T.obj (-(P).muP t) ⟶ contentModuleTarget D Sc' cutoff bound δ.1) :=
  RegularReservoir.evalHomFunctor (k := k)
    (fun β : WeightBlocks D ΛR ((P).muM t) => ContentModules D Sc' cutoff bound β.1)
    ((P).T.obj (-(P).muP t)) δ

instance elvProbeBendContentEvaluation_additive (t : Sector I)
    (δ : WeightBlocks D ΛR ((P).muM t)) :
    (elvProbeBendContentEvaluation D Sc m cutoff bound ΛP ΛR hP hR t δ).Additive :=
  inferInstanceAs (RegularReservoir.evalHomFunctor (k := k)
    (fun β : WeightBlocks D ΛR ((P).muM t) => ContentModules D Sc' cutoff bound β.1)
    ((P).T.obj (-(P).muP t)) δ).Additive

/-- One exponent at a fixed mixed output annihilates the chosen postdot
at every probe input module. -/
theorem elvProbeMixedPostDot_pow_zero [Finite I]
    (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H
      (nextSector (true, i) true (nextSector (true, i) false t)))
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound)
    (δ : WeightBlocks D ΛR ((P).muM t)) :
    ∃ n : ℕ, 0 < n ∧ ∀ M : (P).T.obj (-(P).muP t),
      End.of (((P).rpPostDot i t hv Z).total M δ) ^ n = 0 :=
  elvShiftedPostEndEvaluation_dot_pow_zero D Sc' cutoff bound i ΛR
    ((P).muM_postE i hv)
    (elvProbeMixedBase D Sc m cutoff bound ΛP ΛR hP hR i t Z) hdot (SKM.homContentShift D i t.1) δ

private theorem evaluated_conjugation_isNilpotent
    {C E : Type*} [Category C] [Preadditive C] [Category E] [Preadditive E]
    (L : C ⥤ E) [L.Additive] {A B : C} (e : A ≅ B) (f : End A)
    (hf : IsNilpotent ((L.mapEnd A) f)) :
    IsNilpotent ((L.mapEnd B) (bendConjugation e f)) := by
  have h := hf.map (bendConjugation (L.mapIso e))
  change IsNilpotent (End.of (L.map e.inv ≫ L.map f ≫ L.map e.hom)) at h
  change IsNilpotent (End.of (L.map (e.inv ≫ f ≫ e.hom)))
  simpa only [Functor.map_comp] using h

local notation "out" "[" t "," δ "]" =>
  elvProbeBendContentEvaluation D Sc m cutoff bound ΛP ΛR hP hR t δ

private theorem probeToReservoirInnerStepValid (i : I) (t : Sector I) :
    StepValid (true, i) false (nextSector (false, i) false t) := by
  simp [StepValid, nextSector]

section ProbeToReservoir
local notation "FP" "[" i "," t "]" =>
  SKM.homContentPreF (P).T (P).W.obj i ((P).muM t) ((P).muP_preE i t)
local notation "FR" "[" i "," t "]" =>
  SKM.homContentPostF (P).T.obj (P).W i t.1 ((P).muP t) ((P).muM_postF i t)
local notation "s" "[" i "," t "]" => nextSector (false, i) false t
local notation "hv" "[" i "," t "]" => probeToReservoirInnerStepValid i t
local notation "U" "[" i "," t "," Z "]" =>
  ((congrArg (nextSector (true, i) true) (SPath.next_dnUp_false_false (i := i) t)).symm ▸ (FP[i,t]).obj Z)

/-- The Dx coefficient's outer dot is nilpotent before choosing a probe input. -/
theorem elvProbeDxContentOuterDot_isNilpotent [Finite I]
    (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (δ : WeightBlocks D ΛR ((P).muM t))
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) :
    IsNilpotent (probeToReservoirBendCoefficientEvaluation (P) i t Z out[t,δ]
      ((P).rpPostDot i s[i,t] hv[i,t] U[i,t,Z])) := by
  let J := (FR[i,t]) ⋙ out[t,δ]
  let y := (P).rpPostDot i s[i,t] hv[i,t] U[i,t,Z]
  obtain ⟨n, _, hn⟩ := elvProbeMixedPostDot_pow_zero D Sc m cutoff bound ΛP ΛR hP hR
    i s[i,t] hv[i,t] U[i,t,Z] hdot (blockSucc D ΛR i ((P).muM_postF i t) δ)
  have hy : IsNilpotent ((J.mapEnd _) y) := by
    refine ⟨n, ?_⟩
    exact outputEnd_pow_zero D Sc' cutoff bound ΛR ((P).muM t)
      ((P).T.obj (-(P).muP t)) ((FR[i,t]).obj ((P).rpObj i i s[i,t] hv[i,t] U[i,t,Z]))
      ((FR[i,t]).map y) δ n (fun M =>
        shiftedPostRestriction_component_pow_zero D Sc' cutoff bound i ΛR
          ((P).muM_postF i t) ((P).T.obj (-(P).muP t))
          ((P).rpObj i i s[i,t] hv[i,t] U[i,t,Z]) y
          (SKM.homContentShift D i t.1) M δ n (hn M))
  exact evaluated_conjugation_isNilpotent J
    ((P).probeToReservoirCoefficientIso i t ((FP[i,t]).obj Z)) y hy
end ProbeToReservoir

section ReservoirToProbe
local notation "FP" "[" i "," t "," hb "]" =>
  SKM.homContentPreF (P).T (P).W.obj i ((P).muM t) ((P).muP_preF i hb)
local notation "FR" "[" i "," t "," hv "]" =>
  SKM.homContentPostF (P).T.obj (P).W i t.1 ((P).muP t) ((P).muM_postE i hv)
local notation "s" "[" i "," t "]" => nextSector (false, i) true t
local notation "U" "[" i "," t "," hb "," hv "," Z "]" =>
  ((congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)).symm ▸ (FR[i,t,hv]).obj Z)

/-- The Cx coefficient's outer dot is nilpotent on the whole output functor. -/
theorem elvProbeCxContentOuterDot_isNilpotent [Finite I]
    (i : I) (t : Sector I) (hb : StepValid (false, i) true t)
    (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (δ : WeightBlocks D ΛR ((P).muM t))
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) :
    IsNilpotent (reservoirToProbeBendCoefficientEvaluation (P) i t hb hv Z out[t,δ]
      ((P).rpPostDot i s[i,t] hv U[i,t,hb,hv,Z])) := by
  let J := (FP[i,t,hb]) ⋙ out[t,δ]
  let y := (P).rpPostDot i s[i,t] hv U[i,t,hb,hv,Z]
  obtain ⟨n, _, hn⟩ := elvProbeMixedPostDot_pow_zero D Sc m cutoff bound ΛP ΛR hP hR
    i s[i,t] hv U[i,t,hb,hv,Z] hdot δ
  have hy : IsNilpotent ((J.mapEnd _) y) := by
    refine ⟨n, ?_⟩
    exact outputEnd_pow_zero D Sc' cutoff bound ΛR ((P).muM t)
      ((P).T.obj (-(P).muP t)) ((FP[i,t,hb]).obj ((P).rpObj i i s[i,t] hv U[i,t,hb,hv,Z]))
      ((FP[i,t,hb]).map y) δ n (fun M =>
        shiftedPrecomposition_component_pow_zero D Sc' cutoff bound ΛR ((P).muM t)
          ((P).T.obj (-(P).muP s[i,t])) ((P).T.obj (-(P).muP t))
          ((P).T.F i ((P).muP_preF i hb))
          (SKM.leftAdjParity D i (-((P).muP s[i,t])))
          ((P).rpObj i i s[i,t] hv U[i,t,hb,hv,Z]) y M δ n
          (hn (((P).T.F i ((P).muP_preF i hb)).obj M)))
  exact evaluated_conjugation_isNilpotent J
    ((P).reservoirToProbeCoefficientChart i t hb hv ((FR[i,t,hv]).obj Z)) y hy
end ReservoirToProbe

private theorem contentBendFactorDot_isIso [Fact Sc.PureNilpotent] [Finite I] (i : I) {x y : X} (h : x + D.α i = y) :
    IsIso ((P).T.dot i h) := by
  let _ := Fintype.ofFinite I
  exact (isUnit_iff_isIso _).mp
    (elvProbeReservoir_dot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i h)

/-- The whole-output Dx equation has the literal negative probe windows. -/
def ELVProbeDxContentSeparatedAt [Fact Sc.PureNilpotent] [Finite I] (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (δ : WeightBlocks D ΛR ((P).muM t))
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) (N : ℕ) : Prop :=
  let _ := contentBendFactorDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i ((P).muP_preE i t)
  ProbeToReservoirSeparatedAt (P) i t Z out[t,δ]
    (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot) N

/-- The whole-output Cx equation retains the normalized shifted cap. -/
def ELVProbeCxContentSeparatedAt [Fact Sc.PureNilpotent] [Finite I] (i : I) (t : Sector I)
    (hb : StepValid (false, i) true t) (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (δ : WeightBlocks D ΛR ((P).muM t))
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) (N : ℕ) : Prop :=
  let _ := contentBendFactorDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i ((P).muP_preF i hb)
  ReservoirToProbeSeparatedAt (P) i t hb hv Z out[t,δ]
    (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot) N

attribute [local irreducible] elvProbeReservoir elvProbeCrossCoeffOf

/-- A common output-content length above any minimum works on every input. -/
theorem elvProbe_content_central_separated_windows_above [Fact Sc.PureNilpotent] [Finite I]
    (i : I) (t : Sector I) (hb : StepValid (false, i) true t)
    (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (δ : WeightBlocks D ΛR ((P).muM t))
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) (minimum : ℕ) :
    ∃ N, minimum ≤ N ∧ ELVProbeDxContentSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t Z δ hdot N ∧
      ELVProbeCxContentSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t hb hv Z δ hdot N := by
  let _ := contentBendFactorDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i ((P).muP_preE i t)
  let _ := contentBendFactorDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i ((P).muP_preF i hb)
  obtain ⟨nD, hD⟩ := elvProbeDxContentOuterDot_isNilpotent D Sc m cutoff bound ΛP ΛR hP hR i t Z δ hdot
  obtain ⟨nC, hC⟩ := elvProbeCxContentOuterDot_isNilpotent D Sc m cutoff bound ΛP ΛR hP hR i t hb hv Z δ hdot
  let n := max (max nD nC) minimum
  have hDn := pow_eq_zero_of_le
    ((Nat.le_max_left nD nC).trans (Nat.le_max_left (max nD nC) minimum)) hD
  have hCn := pow_eq_zero_of_le
    ((Nat.le_max_right nD nC).trans (Nat.le_max_left (max nD nC) minimum)) hC
  have hminimum : minimum ≤ n := Nat.le_max_right _ _
  rcases parity_eq_zero_or_one (D.parity i) with hi | hi
  · refine ⟨n, hminimum, ?_, ?_⟩
    · exact probeToReservoirBend_even_separated (P) i t Z out[t,δ]
        (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot)
        (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hP hR hdot) hi n hDn
    · exact reservoirToProbeBend_even_separated (P) i t hb hv Z out[t,δ]
        (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot)
        (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hP hR hdot) hi n hCn
  · refine ⟨2*n, (by omega), ?_, ?_⟩
    · exact probeToReservoirBend_odd_separated (P) i t Z out[t,δ]
        (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot)
        (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hP hR hdot) hi n hDn
    · exact reservoirToProbeBend_odd_separated (P) i t hb hv Z out[t,δ]
        (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot)
        (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hP hR hdot) hi n hCn
end OddMath.QuiverHecke
end

end

section

/-! # Finite mixed bends in the padded output-content corners

`SwappedHomInversion.md` §3 (4)–(6): the chosen ELV coefficient's finite
series retain the entire probe input functor and the literal padded
central entries. The output-content truncation may be increased to the
reservoir window height, including at absent central corners.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV CyclotomicAction SwappedAssembly
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

attribute [local irreducible] elvProbeReservoir elvProbeCrossCoeffOf

/-- The Dx series can meet any prescribed length without requiring an
occupied reservoir source or probe target. -/
theorem elvProbeDx_content_separated_windows_above [Fact Sc.PureNilpotent] [Finite I]
    (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (δ : WeightBlocks D ΛR ((P).muM t))
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) (minimum : ℕ) :
    ∃ N, minimum ≤ N ∧
      ELVProbeDxContentSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t Z δ hdot N := by
  let := Fintype.ofFinite I
  let : IsIso ((P).T.dot i ((P).muP_preE i t)) :=
    (isUnit_iff_isIso _).mp
      (elvProbeReservoir_dot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i ((P).muP_preE i t))
  obtain ⟨n, hn⟩ := elvProbeDxContentOuterDot_isNilpotent
    D Sc m cutoff bound ΛP ΛR hP hR i t Z δ hdot
  have hn' := pow_eq_zero_of_le (Nat.le_max_left n minimum) hn
  rcases parity_eq_zero_or_one (D.parity i) with hi | hi
  · refine ⟨max n minimum, Nat.le_max_right _ _, ?_⟩
    exact probeToReservoirBend_even_separated (P) i t Z out[t,δ]
      (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot)
      (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hP hR hdot) hi _ hn'
  · refine ⟨2 * max n minimum, (by omega), ?_⟩
    exact probeToReservoirBend_odd_separated (P) i t Z out[t,δ]
      (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot)
      (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hP hR hdot) hi _ hn'

/-- The chosen Dx equation in the actual padded output-content corners. -/
def ELVProbePaddedDxContentSeparatedAt [Fact Sc.PureNilpotent] [Finite I] (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (δ : WeightBlocks D ΛR ((P).muM t))
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) (N : ℕ) : Prop :=
  (P).CentralPaddedDxSeparatedAt i t Z out[t,δ]
    (fun {_a _b} h => SupportedSectors.probeWindowDot_isIso
      D Sc m cutoff bound ΛP ΛR hP hR i h)
    (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot) N

/-- The chosen Cx equation retains the padded zero-source and zero-target cases. -/
def ELVProbePaddedCxContentSeparatedAt [Fact Sc.PureNilpotent] [Finite I] (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (δ : WeightBlocks D ΛR ((P).muM t))
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) (N : ℕ) : Prop :=
  (P).CentralPaddedCxSeparatedAt i t Z out[t,δ]
    (fun {_a _b} h => SupportedSectors.probeWindowDot_isIso
      D Sc m cutoff bound ΛP ΛR hP hR i h)
    (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot) N

/-- One output-content length supplies the two exact padded bend equations
above any minimum, retaining the full probe input functor and every corner. -/
theorem elvProbe_content_padded_central_separated_windows_above [Fact Sc.PureNilpotent] [Finite I]
    (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (δ : WeightBlocks D ΛR ((P).muM t))
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) (minimum : ℕ) :
    ∃ N, minimum ≤ N ∧
      ELVProbePaddedDxContentSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t Z δ hdot N ∧
      ELVProbePaddedCxContentSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t Z δ hdot N := by
  let hwin := fun {a b : X} (h : a + D.α i = b) =>
    SupportedSectors.probeWindowDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i h
  let c := elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot
  have hDx (N : ℕ)
      (H : ELVProbeDxContentSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t Z δ hdot N) :
      ELVProbePaddedDxContentSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t Z δ hdot N :=
    (P).centralPaddedDx_separated i t Z out[t,δ] hwin c N H
  by_cases hb : StepValid (false, i) true t
  · by_cases hv : StepValid (true, i) false t
    · obtain ⟨N, hN, hD, hC⟩ := elvProbe_content_central_separated_windows_above
        D Sc m cutoff bound ΛP ΛR hP hR i t hb hv Z δ hdot minimum
      exact ⟨N, hN, hDx N hD,
        (P).centralPaddedCx_separated i t Z out[t,δ] hwin c hb hv N hC⟩
    · obtain ⟨N, hN, hD⟩ := elvProbeDx_content_separated_windows_above
        D Sc m cutoff bound ΛP ΛR hP hR i t Z δ hdot minimum
      exact ⟨N, hN, hDx N hD,
        (P).centralPaddedCx_separated_of_source_absent i t Z out[t,δ] hwin c hv N⟩
  · obtain ⟨N, hN, hD⟩ := elvProbeDx_content_separated_windows_above
      D Sc m cutoff bound ΛP ΛR hP hR i t Z δ hdot minimum
    exact ⟨N, hN, hDx N hD,
      (P).centralPaddedCx_separated_of_target_absent i t Z out[t,δ] hwin c hb N⟩

end OddMath.QuiverHecke
end

end

section

/-! # Transposed source norms and swapping for the ELV probe pair

SwappedActionAssembly F2–F3 and SwappedHomInversion §2: package the three
literal source norm units for the prescribed OLD probe and ELV reservoir.
Their inverses were assembled at individual content blocks; no common
nilpotence exponent on a weight fibre is assumed. The existing swapping
mate theorem then applies to the chosen mixed crossing coefficient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV CyclotomicAction SwappedAssembly
universe u
local instance probeTransposeHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR

attribute [local irreducible] SKM.mixedPostSourcePreDot SKM.mixedPostSourcePostDot

/-- All three transposed source norms are units for the specified factor pair. -/
theorem ELVProbeCrossTransposeNormUnits [Fact Sc.PureNilpotent] [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc' cutoff bound) : (P).CrossTransposeNormUnits := by
  let : Fintype I := Fintype.ofFinite I
  constructor
  · intro i hi xP yP xW yW hp hw κ
    have hu := elvProbeReservoir_dot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i hp
    generalize hT : (P).T = T at hu ⊢
    set_option backward.dsimp.instances true in
      dsimp only [elvProbeReservoir, elvRouquierFamily, elvRouquierData]
    intro H
    have hh := elvMixedSource_difference_isUnit (A := T.obj xP) (B := T.obj yP)
      D Sc' cutoff bound i ΛR hw (T.E i hp) κ H
      hdot hi (T.dot i hp)
      (hi ▸ T.dot_mem i hp) hu
    exact hh
  · intro i hi xP yP xW yW hp hw κ
    have hu := elvProbeReservoir_dot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i hp
    generalize hT : (P).T = T at hu ⊢
    set_option backward.dsimp.instances true in
      dsimp only [elvProbeReservoir, elvRouquierFamily, elvRouquierData]
    intro H
    have hh := elvMixedSource_square_difference_isUnit (A := T.obj xP) (B := T.obj yP)
      D Sc' cutoff bound ΛR xW i hw (T.E i hp) κ H
      hdot hi (T.dot i hp)
      (hi ▸ T.dot_mem i hp) hu
    exact hh
  · intro i hi xP yP xW yW hp hw κ
    have hu := elvProbeReservoir_dot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i hp
    generalize hT : (P).T = T at hu ⊢
    set_option backward.dsimp.instances true in
      dsimp only [elvProbeReservoir, elvRouquierFamily, elvRouquierData]
    intro H
    have hh := elvMixedSource_square_sum_isUnit (A := T.obj xP) (B := T.obj yP)
      D Sc' cutoff bound ΛR xW i hw (T.E i hp) κ H
      hdot hi (T.dot i hp)
      (hi ▸ T.dot_mem i hp) hu
    exact hh

/-- Every off-central swapping entry of the chosen mixed coefficient is invertible. -/
theorem elvProbeSwappingInvertible [Fact Sc.PureNilpotent] [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc' cutoff bound) :
    (P).SwappingInvertible (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR
    hdot) :=
  (P).swappingInvertible_of_units
    (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR
    hdot)
    (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hP hR
    hdot)
    (elvProbeCrossDenominatorUnitsOf D Sc m cutoff bound ΛP ΛR hP hR hdot)
    (ELVProbeCrossTransposeNormUnits D Sc m cutoff bound ΛP ΛR hP hR hdot)

end OddMath.QuiverHecke
end

end

section

/-! # Distinct-colour source polynomial units for the ELV probe pair

BE2 (1.11), SwappedDistinctMixedMates (13)–(15): the prescribed probe dot
has an invertible even power, and the prescribed reservoir transpose has
contentwise nilpotent even powers. These construct the source polynomial
units needed by each distinct-colour sideways crossing.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV CyclotomicAction SwappedAssembly OddMath.SKM
universe u
local instance probeSourcePolynomialHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR

attribute [local irreducible] SKM.mixedPostSourcePreDot SKM.mixedPostSourcePostDot

/-- The actual whole-input source criterion for every pair of colours and
original weights; all admissible remainders and all coefficient units are retained. -/
theorem elvProbeMixedPostSourceUnits [Finite I] [Fact Sc.PureNilpotent]
    (hdot : TruncatedAppendDotNilpotent D Sc' cutoff bound) :
    ∀ (i j : I) {a b c d : X} (hT : a + D.α i = b) (hW : c + D.α j = d)
      (κ : ZMod 2) (H : (P).T.obj b ⟶ (P).W.obj d),
    SKM.MixedPostSourceUnits ((P).T.E i hT) ((P).W.adj j hW) κ H
      (SKM.rouquierPower ((P).T.dot i hT) (if D.parity i = 1 then 2 else 1))
      (SKM.rouquierPower ((P).W.dot j hW) (if D.parity j = 1 then 2 else 1)) := by
  let : Fintype I := Fintype.ofFinite I
  intro i j a b c d hT hW κ
  have hu := elvProbeReservoir_dot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i hT
  generalize hTP : (P).T = T at hu ⊢
  set_option backward.dsimp.instances true in
    dsimp only [elvProbeReservoir, elvRouquierFamily, elvRouquierData]
  intro H
  have ha : SKM.rouquierPower (T.dot i hT) (if D.parity i = 1 then 2 else 1) ∈
      parity (R := k) _ _ 0 := by
    have hh := SKM.rouquierPower_mem (T.dot_mem i hT) (if D.parity i = 1 then 2 else 1)
    rwa [ProbeReservoir.mul_parity_pow_eq_zero] at hh
  have hau : IsUnit (show End (T.E i hT) from
      SKM.rouquierPower (T.dot i hT) (if D.parity i = 1 then 2 else 1)) := by
    rw [SKM.rouquierPower_eq_pow]
    exact hu.pow _
  exact elvMixedSource_polynomialUnits D Sc' cutoff bound j ΛR hW hdot (T.E i hT) κ H _ ha hau
    (if D.parity j = 1 then 2 else 1) (by split_ifs <;> decide)
    (ProbeReservoir.mul_parity_pow_eq_zero (D.parity j))

attribute [local irreducible] elvProbeReservoir ProbeReservoir.sigmaEntry

/-- All prescribed distinct-colour sideways entries are invertible from
constructed source units, without a common reservoir nilpotence exponent. -/
theorem elvProbe_distinct_sigmaEntry_isIso [Finite I] [Fact Sc.PureNilpotent]
    (hdot : TruncatedAppendDotNilpotent D Sc' cutoff bound)
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff Sc)
    {i j : I} (hij : i ≠ j) (ν : X) (t : Sector I)
    (q : SPath (wd D ν [dn i, up j]) t
      (nextSector (dn i) false (nextSector (up j) true t)))
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H
      (nextSector (dn i) false (nextSector (up j) true t))) :
    IsIso ((P).sigmaEntry c i j ν
      (SPath.cons _ true t trivial (SPath.cons _ false _ trivial (SPath.nil _))) q Z) :=
  (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).isIso_sigmaEntry_probe_reservoir_sourceUnits
    Fact.out
    (fun i j _ => elvProbeMixedPostSourceUnits D Sc m cutoff bound ΛP ΛR hP hR hdot i j)
    c hij ν t q Z

end OddMath.QuiverHecke
end

end

section

/-! # The distinct-colour permutation for the ELV probe pair

Brundan–Ellis Definition 1.5, (1.11): distinct colours have unique
summand paths at fixed endpoints. The mixed entries are invertible from
the constructed source polynomial units and the inverse interchange mate.
The canonical factor left-mate theorem supplies the pure probe input.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.CyclotomicAction
open ELV SwappedAssembly
universe u
local instance sigmaPermutationHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
variable [Finite I] (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound)
local notation "c" => elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR
    hdot
attribute [local irreducible] elvProbeReservoir ProbeReservoir.sigmaEntry

/-- Intermediate distinct-colour permutation assembly with the two pure
factor-mate inputs explicit. The mixed entries require no extra hypothesis. -/
theorem elvProbeSigmaPermutation_of_pureEntries [Fact Sc.PureNilpotent]
    (hpure : ∀ (i j : I), i ≠ j → ∀ (ν : X) (t s : Sector I)
      (p : SPath (wd D ν [up j, dn i]) t s) (q : SPath (wd D ν [dn i, up j]) t s)
      (side : Bool), p.sides = [side, side] → q.sides = [side, side] →
      ∀ Z : (P).H s, IsIso ((P).sigmaEntry c i j ν p q Z))
    (i j : I) (ν : X) (hij : i ≠ j) : (P).SigmaPermutation c i j ν := by
  apply (P).sigmaPermutation_of_isIso hij ν
  intro t s p q Z
  obtain ⟨a, b, hv₁, hv₂, ep, rfl⟩ := SPath.exists_eq_two p
  obtain ⟨a', b', hw₁, hw₂, eq, rfl⟩ := SPath.exists_eq_two q
  obtain ⟨hk₁, hk₂, he⟩ := SPath.exchange_upDn hij a b hv₁ hv₂
  obtain ⟨ha, hb⟩ := SPath.sides_eq_dnUp hij a' b' b a hw₁ hw₂ hk₁ hk₂
    (eq.trans (ep.symm.trans he.symm))
  subst ha hb
  cases a' <;> cases b'
  · exact hpure i j hij ν t s _ _ false (SPath.sides_two ..) (SPath.sides_two ..) Z
  · subst ep
    exact elvProbe_distinct_sigmaEntry_isIso D Sc m cutoff bound ΛP ΛR hP hR
      hdot c hij ν t _ Z
  · exact (P).isIso_sigmaEntry_reservoir_probe c hij ν _ _
      (SPath.sides_two ..) (SPath.sides_two ..) Z
  · exact hpure i j hij ν t s _ _ true (SPath.sides_two ..) (SPath.sides_two ..) Z

/-- Intermediate factor assembly. The reservoir and both mixed entries are
constructed; only the canonical probe left-mate input remains explicit. -/
theorem elvProbeSigmaPermutation_of_leftMateInvertible [Fact Sc.PureNilpotent]
    (hL : LeftMateInvertible (P).T (P).T.leftAdjoints)
    (i j : I) (ν : X) (hij : i ≠ j) : (P).SigmaPermutation c i j ν := by
  apply elvProbeSigmaPermutation_of_pureEntries D Sc m cutoff bound ΛP ΛR hP hR hdot
    (i := i) (j := j) (ν := ν) (hij := hij)
  intro a b hab μ t s p q side hp hq Z
  cases side with
  | false => exact (P).isIso_sigmaEntry_pure_reservoir c hab μ p q hp hq Z
  | true => exact (P).isIso_sigmaEntry_pure_probe hL c hab μ p q hp hq Z

/-- The prescribed ELV probe and reservoir have invertible distinct-colour
sideways crossings, with every factor input constructed from their relations. -/
theorem elvProbeSigmaPermutation [Fact Sc.PureNilpotent] (i j : I) (ν : X) (hij : i ≠ j) :
    (P).SigmaPermutation c i j ν := by
  refine elvProbeSigmaPermutation_of_leftMateInvertible D Sc m cutoff bound
    ΛP ΛR hP hR hdot ?_ i j ν hij
  with_unfolding_all
    change LeftMateInvertible (probeOldRouquierFamily D (parameterTwist D Sc) m ΛP hP)
      (probeOldRouquierFamily D (parameterTwist D Sc) m ΛP hP).leftAdjoints
  exact RouquierFamily.canonicalLeftMateInvertible _
    (probeOldRouquierMulticolour D Sc m ΛP hP)

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-! # The whole-weight probe left cap at a missing predecessor

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
compare the inverse-defined whole-weight cap with the stored local cap
using their actual unit columns. Inverse uniqueness removes dependence
on the choices used to assemble the whole-weight inverse family.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor CyclotomicAction
universe u v w
private theorem cap_window_total
    {k : Type u} {C : Type v} [CommRing k] [Category.{w} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F : Superfunctor k C C}
    (a : Superfunctor.id k C ⟶ F) (b : F ⟶ Superfunctor.id k C)
    (q : Prop) [Decidable q]
    (h : a ≫ b = if q then 𝟙 (Superfunctor.id k C) else 0) (M : C) :
    a.total M ≫ b.total M = if q then 𝟙 M else 0 := by
  have hh := congrArg (fun η : Superfunctor.id k C ⟶ Superfunctor.id k C => η.total M) h
  rw [Superfunctor.comp_total] at hh
  by_cases hq : q
  · rw [ite_eq_left hq] at hh ⊢
    exact hh.trans (SuperNatTrans.id_total (𝟭 C) M)
  · rw [ite_eq_right hq] at hh ⊢
    simpa only [SuperNatTrans.total, Superfunctor.zero_app, zero_add] using hh

private theorem product_window {ι : Type*} {C : ι → Type*}
    [∀ j, Category (C j)] [∀ j, Preadditive (C j)]
    {A B : ∀ j, C j} (f : A ⟶ B) (g : B ⟶ A) (q : Prop) [Decidable q]
    (h : f ≫ g = if q then 𝟙 A else 0) (j : ι) :
    f j ≫ g j = if q then 𝟙 (A j) else 0 := by
  by_cases hq : q
  · rw [ite_eq_left hq] at h ⊢
    exact congrFun h j
  · rw [ite_eq_right hq] at h ⊢
    exact congrFun h j

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (δ : WeightBlocks D Λ x₁)
local notation "γ" => Multiset.toList (Subtype.val δ)
local notation "perm" => probeOldBlockTarget_perm D i Λ h₂ δ (blockSucc D Λ i h₂ δ) rfl
local notation "L" hc => probeOldWeightLoc D Sc m i Λ h₁ h₂ hc
local notation "U" n => SKM.SuperAdjunction.unit (probeOldActionAdjunction D Sc m i Λ h₂) ≫
  SKM.rouquierPower (probeOldActionDot D Sc m i Λ h₂) n ▷ probeOldF D Sc m i Λ h₂

/-- At a negative-height missing predecessor, the whole-weight raw cap
is exactly the stored missing-colour cap in its prescribed successor
chart. All input modules and all homogeneous components are retained. -/
theorem probeOldWeightLoc_cap_missing
    (hc : (probeCutoff D m i : ℤ) = D.h i Λ)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ)
    (hh : D.h i x₁ < 0) (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    ((L hc).capL).total M δ =
      eqToHom (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M) ≫
        (probeMissingStoredLoc D Sc m γ i perm
          (by simpa only [Multiset.mem_toList] using
            (show i ∉ δ.1 from fun hm => hδ ((exists_blockSucc_iff D Λ i h₁ δ).mpr hm)))).capL.total (M δ) := by
  have hi : i ∉ γ := by
    simpa only [Multiset.mem_toList] using
      (show i ∉ δ.1 from fun hm => hδ ((exists_blockSucc_iff D Λ i h₁ δ).mpr hm))
  let S := probeMissingStoredLoc D Sc m γ i perm hi
  have hHeight : -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) = D.h i x₁ := by
    rw [Multiset.coe_toList, contentCrossingHeight_eq_neg_weight D (probeCutoff D m) i Λ x₁ hc δ, neg_neg]
  have hs : -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) < 0 := by
    simpa only [hHeight] using hh
  let J := Classical.choice (probeOldWeightAbsentUnitInverse_nonempty D Sc m i Λ h₁ h₂ δ hc hδ M)
  apply J.hom_ext
  · exact (probeOldInductionComponent_isZero D Sc m i Λ h₁ δ hδ
      ((probeOldF D Sc m i Λ h₁).obj M)).eq_of_src _ _
  · intro n hn
    have hL := cap_window_total ((L hc).cupD n) (L hc).capL _
      ((L hc).cupD_capL hh hn) M
    have hLc := product_window _ _ _ hL δ
    have hS := cap_window_total (S.cupD n) S.capL _
      (S.cupD_capL hs (by simpa only [hHeight] using hn)) (M δ)
    have hcol := probeOldWeightUnitPower_total_comparison D Sc m i Λ h₂ δ M n
    rw [← probeOldWeightFollowing_eqToHom] at hcol
    change (U n).total M δ ≫ eqToHom (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M) =
      (S.cupD n).total (M δ) at hcol
    change (U n).total M δ ≫ (L hc).capL.total M δ = _
    calc
      _ = if n = (-D.h i x₁ - 1).toNat then 𝟙 (M δ) else 0 := by
        exact hLc
      _ = (S.cupD n).total (M δ) ≫ S.capL.total (M δ) := by
        simpa only [hHeight] using hS.symm
      _ = (U n).total M δ ≫
          (eqToHom (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M) ≫ S.capL.total (M δ)) := by
        rw [← hcol, Category.assoc]

end OddMath.QuiverHecke
end

end

section

/-! # Negative-height normalization of the whole-weight probe counit

SwappedActionAssembly F2: retain the prescribed diagonal Koszul factor
of the whole-weight left adjunction. Multiplying its normalized counit
by that factor recovers the exact raw inverse cap. On missing blocks,
the cap is then the previously identified stored local row.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV CyclotomicAction
universe u
private theorem total_zsmul
    {k C A : Type*} [CommRing k] [Category C] [Category A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : Superfunctor k C A} (η : F ⟶ G) (z : ℤ) (M : C) :
    (z • η).total M = z • η.total M := by
  change z • η.app 0 M + z • η.app 1 M = z • (η.app 0 M + η.app 1 M)
  exact (smul_add _ _ _).symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (Λ : X)
  (hc : ∀ i, (probeCutoff D m i : ℤ) = D.h i Λ)
local notation "T" => probeOldRouquierFamily D Sc m Λ hc

/-- The diagonal parity factor exactly cancels the prescribed
negative-height normalization of the whole-weight left counit. -/
theorem probeOldLeftCounit_negative_sign (i : I) {x y : X}
    (h : x + D.α i = y) (hh : D.h i x < 0) :
    koszulSign (SKM.leftAdjParity D i x) (SKM.leftAdjParity D i x) • ((T).leftAdjoints.adjL i h).counit =
      (probeOldWeightLoc D Sc m i Λ (sub_add_cancel x (D.α i)) h (hc i)).capL := by
  change koszulSign (SKM.leftAdjParity D i x) (SKM.leftAdjParity D i x) • ((T).leftAdjoints.adjL i h).counit = (T).leftCap i h
  rw [SKM.RouquierFamily.leftAdjoints_counit, SKM.RouquierFamily.leftAdjScalar_inv_coe,
    ite_eq_left hh, mul_one, Int.cast_smul_eq_zsmul, smul_smul, koszulSign_mul_self, one_smul]

/-- At every missing output block, the normalized whole-weight counit,
with its prescribed pre-Hom parity factor, is the exact stored raw cap
under the specified successor chart. -/
theorem probeOldLeftCounit_missing (i : I) {x y : X}
    (h : x + D.α i = y) (hh : D.h i x < 0)
    (δ : WeightBlocks D Λ x)
    (hδ : ¬ ∃ β, blockSucc D Λ i (sub_add_cancel x (D.α i)) β = δ)
    (M : ProbeOldWeightProduct D Sc m Λ x) :
    koszulSign (SKM.leftAdjParity D i x) (SKM.leftAdjParity D i x) • (((T).leftAdjoints.adjL i h).counit.total M δ) =
      eqToHom (probeOldWeightFollowing_obj D Sc m i Λ h δ M) ≫
        (probeMissingStoredLoc D Sc m δ.1.toList i
          (probeOldBlockTarget_perm D i Λ h δ (blockSucc D Λ i h δ) rfl)
          (by simpa only [Multiset.mem_toList] using
            (show i ∉ δ.1 from fun hm => hδ
              ((exists_blockSucc_iff D Λ i (sub_add_cancel x (D.α i)) δ).mpr hm)))).capL.total (M δ) := by
  have hf := probeOldLeftCounit_negative_sign D Sc m Λ hc i h hh
  have ht := congrArg (fun f : (T).E i h ≫ (T).F i h ⟶ 𝟙 ((T).obj x) => f.total M δ) hf
  have he : koszulSign (SKM.leftAdjParity D i x) (SKM.leftAdjParity D i x) • (((T).leftAdjoints.adjL i h).counit.total M δ) =
      (probeOldWeightLoc D Sc m i Λ (sub_add_cancel x (D.α i)) h (hc i)).capL.total M δ := by
    have hz := congrFun (total_zsmul ((T).leftAdjoints.adjL i h).counit
      (koszulSign (SKM.leftAdjParity D i x) (SKM.leftAdjParity D i x)) M) δ
    exact hz.symm.trans ht
  exact he.trans (probeOldWeightLoc_cap_missing D Sc m i Λ
    (sub_add_cancel x (D.α i)) h δ (hc i) hδ hh M)

end OddMath.QuiverHecke
end

end

section

/-! # Uniqueness of the prescribed probe cap from its unit window

The local inverse row defining the left cap in `RouquierLeftCupCap`
extracts the right dotted unit columns. At the regular vacuum probe these
columns span, by the given unit matrix inverse. This is the uniqueness
input for comparing that local inverse row with the specified native cap;
it does not assume a left adjunction or a cap-identification premise.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u

private theorem assembled_row_ext {k : Type u} [CommRing k]
    {ι : Type} [Fintype ι] (V : ι → SVec k) (W : SVec k)
    {Z : Type u} [AddCommGroup Z] [Module k Z]
    (col : ∀ a, V a ⟶ W) (e : OddMath.FiniteSuperspace.product V ≅ W)
    (he : e.hom = OddMath.FiniteSuperspace.assembleColumns V W col)
    (f g : W →ₗ[k] Z) (h : ∀ a x, f (col a x) = g (col a x)) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (OddMath.FiniteSuperspace.isoLinearEquiv e).surjective x
  change f (e.hom y) = g (e.hom y)
  rw [he]
  change f (∑ a, col a (y a)) = g (∑ a, col a (y a))
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl (fun a _ => h a (y a))

section Generic
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  (M : Superfunctor k C (SVec k)) (m : ℕ) (w : C)
local instance capUniquenessPi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory

/-- A prescribed finite unit matrix forces uniqueness of every linear row
from its values on the unshifted dotted-unit columns. The matrix premise
is supplied by the existing concrete inverse in applications. -/
theorem unitColumnMatrix_row_ext
    (e : unitColumnSourceSpace p M m w ≅ ((restriction J).obj ((induction J).obj M)).obj w)
    (he : e.hom = unitColumnMatrix J hα M m w)
    {Z : Type u} [AddCommGroup Z] [Module k Z]
    (f g : ((restriction J).obj ((induction J).obj M)).obj w →ₗ[k] Z)
    (h : ∀ a, a < m → f ∘ₗ unitDotLinear J hα M a w =
      g ∘ₗ unitDotLinear J hα M a w) : f = g := by
  apply assembled_row_ext
    (fun r : Fin m => ((SKM.homParityShift (k := k) (r.val • p)).obj M).obj w)
    (((restriction J).obj ((induction J).obj M)).obj w)
    (fun r => (shiftedUnitDotColumn J hα M r.val).total w) e he
  intro r x
  have hr := LinearMap.congr_fun (h r.val r.isLt)
    (((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom.total w x)
  have hc := LinearMap.congr_fun (shiftedUnitDotColumn_total J hα M r.val w) x
  set_option backward.dsimp.instances true in
    dsimp only [shiftedUnitDotLinear, LinearMap.comp_apply, SVec.toLinearMap] at hc
  exact (congrArg f hc).trans (hr.trans (congrArg g hc).symm)
end Generic

private theorem inverse_column
    {k V V' W W' : Type u} [CommRing k]
    [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
    [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']
    (v : V ≃ₗ[k] V') (w : W ≃ₗ[k] W') (a : V →ₗ[k] W) (b : V' →ₗ[k] W')
    (h : w.toLinearMap ∘ₗ a = b ∘ₗ v.toLinearMap) :
    w.symm.toLinearMap ∘ₗ b = a ∘ₗ v.symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  apply w.injective
  have hh := LinearMap.congr_fun h (v.symm x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hh.symm

private theorem pullback_row_ext
    {k V V' W W' Z : Type u} [CommRing k]
    [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
    [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']
    [AddCommGroup Z] [Module k Z]
    (v : V ≃ₗ[k] V') (w : W ≃ₗ[k] W') (a : ℕ → V →ₗ[k] W) (b : ℕ → V' →ₗ[k] W')
    (m : ℕ) (hcol : ∀ n, w.toLinearMap ∘ₗ a n = b n ∘ₗ v.toLinearMap)
    (hspan : ∀ f g : W' →ₗ[k] Z,
      (∀ n, n < m → f ∘ₗ b n = g ∘ₗ b n) → f = g)
    (f g : W →ₗ[k] Z) (h : ∀ n, n < m → f ∘ₗ a n = g ∘ₗ a n) : f = g := by
  have hfg := hspan (f ∘ₗ w.symm.toLinearMap) (g ∘ₗ w.symm.toLinearMap) (fun n hn => by
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, inverse_column v w (a n) (b n) (hcol n)]
    rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, h n hn])
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hfg (w x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hx

private theorem module_column_equality
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (w : C) (a : ℕ)
    (f g : (restriction J).obj ((induction J).obj M) ⟶ M)
    (h : unitDotColumn J hα M a ≫ f = unitDotColumn J hα M a ≫ g) :
    SVec.toLinearMap (f.total w) ∘ₗ unitDotLinear J hα M a w =
      SVec.toLinearMap (g.total w) ∘ₗ unitDotLinear J hα M a w := by
  rw [← unitDotColumn_total]
  rw [← SVec.toLinearMap_comp, ← SVec.toLinearMap_comp,
    ← Superfunctor.comp_total, ← Superfunctor.comp_total, h]

end OddMath.QuiverHecke.ELV.BalancedInduction

namespace OddMath.QuiverHecke.ELV.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
local notation "K" => oldContentAppend D Sc cut []
local notation "T" => probeOrdinaryAppend D Sc m []
local notation "U" => probeOldOrdinaryFunctor D Sc m []
local notation "M" => probeOrdinaryModuleSuperfunctor D Sc m [] N (probeOldModule_evaluatesCoefficients D m Sc [] _)

/-- On the original regular probe, any module row with the prescribed
finite unit/dot window is the given native cap. This intermediate criterion
will be supplied by the actual local augmented inverse's `gg` equations. -/
theorem cap_eq_of_unitDot_window (i : I) (hP : 0 < cut i)
    (f : source D Sc m i ⟶ N)
    (hf : ∀ a, a < cut i →
      unitDotColumn (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N a ≫ f =
        if a + 1 = cut i then 𝟙 N else 0) : f = cap D Sc m i hP := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  suffices he : SVec.toLinearMap (f.total w) = SVec.toLinearMap ((cap D Sc m i hP).total w) by
    exact congrArg SVec.ofHom he
  apply pullback_row_ext
    (probeOutputValueLinearEquiv D Sc m [] N (probeOldModule_evaluatesCoefficients D m Sc [] _) w)
    (probeOutputFELinearEquiv D Sc m [] N (probeOldModule_evaluatesCoefficients D m Sc [] _) i w)
    (fun a => unitDotLinear (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N a w)
    (fun a => unitDotLinear (T i) (probeOrdinaryAppendDot_supernatural D Sc m [] i) M a ((U).obj w))
    (cut i)
  · intro a
    exact probeOutputFELinearEquiv_unitDot D Sc m [] N
      (probeOldModule_evaluatesCoefficients D m Sc [] _) i w a
  · intro g h hgh
    apply unitColumnMatrix_row_ext (T i) (probeOrdinaryAppendDot_supernatural D Sc m [] i) M
      (contentUnitCount D cut i (([] : List I) : Multiset I)) ((U).obj w)
      (probeMissingColourUnitMatrixIso D Sc m [] N
        (probeOldModule_evaluatesCoefficients D m Sc [] _) i (by simp) w)
      (probeMissingColourUnitMatrixIso_hom D Sc m [] N
        (probeOldModule_evaluatesCoefficients D m Sc [] _) i (by simp) w) g h
    intro a ha
    rw [VacuumCoefficient.count] at ha
    exact hgh a ha
  · intro a ha
    exact module_column_equality (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N w a
      f (cap D Sc m i hP) ((hf a ha).trans (unitDotColumn_cap D Sc m i hP a ha).symm)

end OddMath.QuiverHecke.ELV.ProbeVacuumCap
end

end

section

/-! # The stored probe cap in the full OLD coefficient coordinates

SwappedActionAssembly F2: the missing-colour inverse cap is the
prescribed boundary coefficient, transported through the even upper-loop
chart. All module components and full OLD coefficients are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (γ : List I) (i : I) {μ : List I} (h : (i :: γ).Perm μ) (hi : i ∉ γ)
local notation "count" => contentUnitCount D (probeCutoff D m) i (γ : Multiset I)
local notation "L" => probeMissingStoredLoc D Sc m γ i h hi
local notation "V" => probeMissingStoredCoefficients D Sc m γ i h hi

/-- The raw stored local cap is the top boundary coefficient, with no
normalization scalar inserted. -/
theorem probeMissingStoredLoc_cap_eq (hn : 0 < count) : (L).capL = (V).cap := by
  have hcount : (count : ℤ) = contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) :=
    contentUnitCount_cast D (probeCutoff D m) i (γ : Multiset I)
      (contentCrossingHeight_nonneg_of_not_mem D (probeCutoff D m) γ i hi)
  apply (V).hom_ext
  intro n hnc
  have hh : -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) < 0 := by omega
  have hw := (L).cupD_capL hh (n := n) (by omega)
  have he : (- -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) - 1).toNat = count - 1 := by omega
  calc
    _ = if n = count - 1 then 𝟙 _ else 0 := by
      simpa only [he, SKM.SuperRouquierLoc.cupD, SKM.RouquierBoundary.cup] using hw
    _ = _ := ((V).cup_cap hn hnc).symm

/-- The explicit selected upper-loop chart transports the stored cap to
the un-reindexed evaluated OLD boundary cap. -/
theorem probeMissingStoredLoc_cap_chart (hn : 0 < count) :
    (L).capL = (probeAppendUpperLoopSuperIso D Sc m γ i h).inv ≫
      (probeEvaluatedMissingCoefficients D Sc m γ i hi).cap := by
  rw [probeMissingStoredLoc_cap_eq D Sc m γ i h hi hn]
  simp only [SKM.RouquierBoundary.Coefficients.cap, hn, ite_true]
  rfl

/-- On the original regular probe, the full OLD boundary cap is precisely
its prescribed native vacuum cap. The finite moments are proved from the
constructed boundary inverse. -/
theorem probeMissingBoundary_regular_cap [Fintype I]
    (hP : 0 < probeCutoff D m i) :
    (contentMissingBoundaryCoefficients D Sc (probeCutoff D m) [] i (by simp)).cap.total
      (probeOldVacuumRegular D Sc m) = ProbeVacuumCap.cap D Sc m i hP := by
  apply ProbeVacuumCap.cap_eq_of_unitDot_window D Sc m i hP
  intro a ha
  let W := contentMissingBoundaryCoefficients D Sc (probeCutoff D m) [] i (by simp)
  have hp : 0 < contentUnitCount D (probeCutoff D m) i (([] : List I) : Multiset I) := by
    simpa only [VacuumCoefficient.count] using hP
  have hw := W.cup_cap hp (j := a) (by simpa only [VacuumCoefficient.count] using ha)
  have ht := congrArg (fun η => η.total (probeOldVacuumRegular D Sc m)) hw
  rw [Superfunctor.comp_total] at ht
  have hu : (SKM.RouquierBoundary.cup
      (inductionModuleAdjunction (k := k) (oldContentAppend D Sc (probeCutoff D m) [] i))
      (inductionModuleDot (oldContentAppend D Sc (probeCutoff D m) [] i)
        (oldContentAppendDot_supernatural D Sc (probeCutoff D m) [] i)) a).total
          (probeOldVacuumRegular D Sc m) =
      unitDotColumn (oldContentAppend D Sc (probeCutoff D m) [] i)
        (probeOldContentAppendDot_supernatural D Sc m [] i) (probeOldVacuumRegular D Sc m) a := by
    rw [inductionModuleUnitPower_eq, gridUnitColumnTransformation_total]
  rw [hu] at ht
  by_cases he : a + 1 = probeCutoff D m i
  · have he' : a = contentUnitCount D (probeCutoff D m) i (([] : List I) : Multiset I) - 1 := by
      rw [VacuumCoefficient.count]; omega
    rw [ite_eq_left he'] at ht
    exact (ht.trans (SuperNatTrans.id_total
      (𝟭 (Superfunctor k (OldContentCategory D Sc (probeCutoff D m) []) (SVec k)))
      (probeOldVacuumRegular D Sc m))).trans (ite_eq_left he).symm
  · have he' : a ≠ contentUnitCount D (probeCutoff D m) i (([] : List I) : Multiset I) - 1 := by
      rw [VacuumCoefficient.count]; omega
    rw [ite_eq_right he'] at ht
    simpa only [SuperNatTrans.total, Superfunctor.zero_app, zero_add, ite_eq_right he] using ht

end OddMath.QuiverHecke
end

end

section

/-! # Empty-content coordinates of the whole-weight vacuum cap

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
retain the empty-content forgetting map on the upper probe loop and its
full OLD boundary cap. These are the source coordinates required by the
regular-probe evaluation of the chosen central bend.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open CyclotomicAction BalancedInduction CyclotomicCrossingTensor
attribute [local irreducible] probeAppendUpperLoopSuperIso
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)

/-- Empty-content forgetting retains the selected upper loop literally. -/
theorem forgetEmpty_upper_obj (ν : List I) (hν : ν = []) (i : I)
    (N : ProbeEvaluatedModules D Sc m ν) :
    (emptyContentForget D Sc m ν hν).obj
      ((probeEvaluatedRestriction D Sc m ν i).obj ((probeEvaluatedInduction D Sc m ν i).obj N)) =
    (restriction (oldContentAppend D Sc (probeCutoff D m) [] i)).obj
      ((induction (oldContentAppend D Sc (probeCutoff D m) [] i)).obj
        ((emptyContentForget D Sc m ν hν).obj N)) := by
  subst ν
  rfl

/-- The full boundary cap follows the same empty-content source equality. -/
theorem forgetEmpty_boundary_cap (ν : List I) (hν : ν = []) (i : I)
    (N : ProbeEvaluatedModules D Sc m ν) :
    (emptyContentForget D Sc m ν hν).map
      ((probeEvaluatedMissingCoefficients D Sc m ν i (by rw [hν]; simp)).cap.total N) =
    eqToHom (forgetEmpty_upper_obj D Sc m ν hν i N) ≫
      (contentMissingBoundaryCoefficients D Sc (probeCutoff D m) [] i (by simp)).cap.total
        ((emptyContentForget D Sc m ν hν).obj N) := by
  subst ν
  simp only [eqToHom_refl, Category.id_comp]
  change ((probeEvaluatedMissingCoefficients D Sc m [] i (by simp)).cap.total N).hom =
    (contentMissingBoundaryCoefficients D Sc (probeCutoff D m) [] i (by simp)).cap.total N.obj
  exact probeEvaluatedMissingCoefficients_cap_total D Sc m [] i (by simp) N

private def totalEvaluation {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A] (M : C) :
    Superfunctor k C A ⥤ A where
  obj F := F.obj M
  map f := f.total M
  map_id F := SuperNatTrans.id_total F.toFunctor M
  map_comp f g := Superfunctor.comp_total f g M

private theorem family_eqToHom {C : Type*} [Category C] (G : C ⥤ C)
    (a : ∀ M, G.obj M ⟶ M) {M N : C} (h : M = N) :
    a M ≫ eqToHom h = G.map (eqToHom h) ≫ a N := by
  subst N
  simp

private theorem emptyBlock_list (Λ : X) :
    (emptyBlock D Λ).1.toList = [] := Multiset.toList_zero

variable (Λ : X) (i : I) {y : X} (edge : -Λ + D.α i = y)
local notation "δ₀" => emptyBlock D Λ
local notation "N₀" => regularProbe D Sc m Λ
local notation "γ₀" => Multiset.toList (Subtype.val (emptyBlock D Λ))
local notation "perm" => probeOldBlockTarget_perm D i Λ edge δ₀ (blockSucc D Λ i edge δ₀) rfl
local notation "F₀" => emptyContentForget D Sc m γ₀ (emptyBlock_list D Λ)
local notation "K" => oldContentAppend D Sc (probeCutoff D m) [] i

/-- The selected successor, upper-loop, and empty-content charts identify
FE of the regular whole-weight probe with the literal native cap source. -/
def vacuumCapSourceIso [Fintype I] :
    (emptyProbe D Sc m Λ).obj
      (((probeOldE D Sc m i Λ edge) ≫ (probeOldF D Sc m i Λ edge)).obj N₀) ≅
      ProbeVacuumCap.source D Sc m i :=
  (F₀).mapIso (eqToIso (probeOldWeightFollowing_obj D Sc m i Λ edge δ₀ N₀)) ≪≫
    (F₀).mapIso ((totalEvaluation (N₀ δ₀)).mapIso
      (probeAppendUpperLoopSuperIso D Sc m γ₀ i perm).symm) ≪≫
    eqToIso (forgetEmpty_upper_obj D Sc m γ₀ (emptyBlock_list D Λ) i (N₀ δ₀)) ≪≫
    ((induction K) ⋙ (restriction K)).mapIso (eqToIso (emptyProbe_regular D Sc m Λ))

/-- The normalized whole-weight left counit at the regular probe is the
prescribed native vacuum cap under the actual FE source chart. The
nontrivial diagonal parity factor is retained explicitly. -/
theorem vacuumLeftCounit_eq [Fintype I]
    (hc : ∀ j, (probeCutoff D m j : ℤ) = D.h j Λ) (hP : 0 < probeCutoff D m i) :
    koszulSign (SKM.leftAdjParity D i (-Λ)) (SKM.leftAdjParity D i (-Λ)) •
      ((emptyProbe D Sc m Λ).map
        (((probeOldRouquierFamily D Sc m Λ hc).leftAdjoints.adjL i edge).counit.total N₀) ≫
          eqToHom (emptyProbe_regular D Sc m Λ)) =
      (vacuumCapSourceIso D Sc m Λ i edge).hom ≫ ProbeVacuumCap.cap D Sc m i hP := by
  have hneg : D.h i (-Λ) = -D.h i Λ := map_neg (D.cd.coroot i) Λ
  have hh : D.h i (-Λ) < 0 := by rw [hneg, ← hc i]; omega
  have hδ : ¬ ∃ β, blockSucc D Λ i (sub_add_cancel (-Λ) (D.α i)) β = δ₀ := by
    rw [exists_blockSucc_iff]
    change i ∉ (0 : Multiset I)
    simp
  have hi : i ∉ γ₀ := by
    change i ∉ (0 : Multiset I).toList
    rw [Multiset.toList_zero]; simp
  have hn : 0 < contentUnitCount D (probeCutoff D m) i (γ₀ : Multiset I) := by
    change 0 < contentUnitCount D (probeCutoff D m) i ((0 : Multiset I).toList : Multiset I)
    rw [Multiset.toList_zero, VacuumCoefficient.count]
    exact hP
  have hw := probeOldLeftCounit_missing D Sc m Λ hc i edge hh δ₀ hδ N₀
  have he := congrArg (F₀).map hw
  rw [CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_comp] at he
  have hs := probeMissingStoredLoc_cap_chart D Sc m γ₀ i perm hi hn
  have hst := congrArg (fun η => η.total (N₀ δ₀)) hs
  rw [Superfunctor.comp_total] at hst
  rw [hst, CategoryTheory.Functor.map_comp,
    forgetEmpty_boundary_cap D Sc m γ₀ (emptyBlock_list D Λ) i (N₀ δ₀)] at he
  have hout := congrArg (fun f => f ≫ eqToHom (emptyProbe_regular D Sc m Λ)) he
  rw [Preadditive.zsmul_comp] at hout
  refine hout.trans ?_
  rw [Category.assoc, Category.assoc, Category.assoc]
  have hN : (F₀).obj (N₀ δ₀) = probeOldVacuumRegular D Sc m := emptyProbe_regular D Sc m Λ
  rw [family_eqToHom ((induction K) ⋙ (restriction K))
    (fun M => (contentMissingBoundaryCoefficients D Sc (probeCutoff D m) [] i (by simp)).cap.total M)
    hN, probeMissingBoundary_regular_cap D Sc m i hP]
  simp only [vacuumCapSourceIso, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom,
    totalEvaluation, Iso.symm_hom, Category.assoc]

end OddMath.QuiverHecke.ELV.WeightTensorVacuum
end

end

section

/-! # Canonical shifted coordinates for the probe cap

The source comparison in `SwappedActionAssembly.md`, §5 (A14), and
`RouquierHomPreCoordinates` is retained before evaluating the regular
probe. No left unit, triangle identities, or transpose-dot identification
are supplied by these coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u

local instance probeCapPreCoordinatesHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private def evaluation {k : Type u} [CommRing k] {C R : Type*}
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R] (M : C) :
    Superfunctor k C R ⥤ R where
  obj F := F.obj M
  map f := f.total M
  map_id F := SuperNatTrans.id_total F.toFunctor M
  map_comp f g := Superfunctor.comp_total f g M

private theorem total_mem {k : Type u} [CommRing k] {C R : Type*}
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R]
    {F G : Superfunctor k C R} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (M : C) :
    f.total M ∈ parity (R := k) _ _ p := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0), add_zero]
    exact f.app_mem 0 M
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (0 : ZMod 2) ≠ 1), zero_add]
    exact f.app_mem 1 M

private instance evaluationAdditive {k : Type u} [CommRing k] {C R : Type*}
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R] (M : C) :
    (evaluation (k := k) (R := R) M).Additive where
  map_add {F G f g} := by
    change (f.app 0 M + g.app 0 M) + (f.app 1 M + g.app 1 M) =
      (f.app 0 M + f.app 1 M) + (g.app 0 M + g.app 1 M)
    abel

private instance evaluationLinear {k : Type u} [CommRing k] {C R : Type*}
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R] (M : C) :
    (evaluation (k := k) (R := R) M).Linear k where
  map_smul f r := by
    change r • f.app 0 M + r • f.app 1 M = r • (f.app 0 M + f.app 1 M)
    exact (smul_add _ _ _).symm

private instance evaluationSuper {k : Type u} [CommRing k] {C R : Type*}
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R] (M : C) :
    IsSuperfunctor k (evaluation (k := k) (R := R) M) where
  map_mem hf := total_mem hf M

private def sourceCapRow
    {k : Type u} [CommRing k] {A R : PiSCat.{u,u,u+1} k}
    {F : A ⟶ A} {S : A ⟶ R} (H : A ⟶ R) (e : S ≅ F ≫ H)
    (η : F ⟶ 𝟙 A) : S ⟶ H := e.hom ≫ (η ▷ H) ≫ (leftUnitor H).hom

private theorem sourceCapRow_mem
    {k : Type u} [CommRing k] {A R : PiSCat.{u,u,u+1} k}
    {F : A ⟶ A} {S : A ⟶ R} (H : A ⟶ R) (e : S ≅ F ≫ H)
    (η : F ⟶ 𝟙 A) {σ : ZMod 2}
    (he : e.hom ∈ parity (R := k) _ _ σ) (hη : η ∈ parity (R := k) _ _ σ) :
    sourceCapRow H e η ∈ parity (R := k) _ _ 0 := by
  simpa only [sourceCapRow, add_zero, SKM.zmod2_add_self] using
    comp_mem he (comp_mem (TwoSupercategory.whiskerRight_mem H hη)
      (TwoSupercategory.leftUnitor_hom_mem (R := k) H))

private theorem sourceCapRow_total
    {k : Type u} [CommRing k] {A R : PiSCat.{u,u,u+1} k}
    {F : A ⟶ A} {S : A ⟶ R} (H : A ⟶ R) (e : S ≅ F ≫ H)
    (η : F ⟶ 𝟙 A) (M : A) :
    (sourceCapRow H e η).total M =
      ((evaluation M).mapIso e).hom ≫ H.map (η.total M) := by
  rw [sourceCapRow, Superfunctor.comp_total, Superfunctor.comp_total]
  have hη : (η ▷ H).total M = H.map (η.total M) := by
    change H.map (η.app 0 M) + H.map (η.app 1 M) = H.map (η.app 0 M + η.app 1 M)
    exact (Functor.map_add H.toFunctor).symm
  have hid : ((leftUnitor H).hom).total M = 𝟙 (H.obj M) := SuperNatTrans.id_total H.toFunctor M
  rw [hη, hid]
  change e.hom.total M ≫ (H.map (η.total M) ≫ 𝟙 (H.obj M)) =
    e.hom.total M ≫ H.map (η.total M)
  erw [Category.comp_id]

private theorem coordinate_polynomial {C : Type*} [Category C] [Preadditive C]
    {S T : C} (e : T ≅ S) (d : End S) (n : ℕ) (h : (d ^ 2 + 1) ^ n = 0) :
    ((e.symm.conj d) ^ 2 + 1) ^ n = 0 := by
  let c : End S →+* End T := {
    toFun := e.symm.conj
    map_one' := map_one e.symm.conj
    map_mul' := fun a b => map_mul e.symm.conj a b
    map_zero' := by simp [Iso.conj_apply]
    map_add' := fun a b => by
      change e.hom ≫ (a + b) ≫ e.inv = _
      rw [Preadditive.add_comp, Preadditive.comp_add]
      rfl }
  have hc := congrArg c h
  simp only [map_pow, map_add, map_one, map_zero] at hc
  exact hc

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
local notation "K" => oldContentAppend D Sc cut []

/-- The module category after adjoining the moving colour. -/
def raisedModulePiCategory (i : I) : PiSCat.{u,u,u+1} k where
  toSCat := SCat.of k (Superfunctor k (OldContentCategory D Sc cut [i]) (SVec k))
  pi := supermodulePiSupercategory

/-- The same chosen induction functor, between its actual content categories. -/
def inductionCell (i : I) : modulePiCategory D Sc m ⟶ raisedModulePiCategory D Sc m i :=
  show Superfunctor k (Superfunctor k (OldContentCategory D Sc cut []) (SVec k))
    (Superfunctor k (OldContentCategory D Sc cut [i]) (SVec k)) from ⟨induction (K i)⟩

/-- The same chosen restriction functor in the reverse direction. -/
def restrictionCell (i : I) : raisedModulePiCategory D Sc m i ⟶ modulePiCategory D Sc m :=
  show Superfunctor k (Superfunctor k (OldContentCategory D Sc cut [i]) (SVec k))
    (Superfunctor k (OldContentCategory D Sc cut []) (SVec k)) from ⟨restriction (K i)⟩

/-- The canonical source shift removal followed by the existing even
associator, in exactly the order of `homContentPreInverseSource`. -/
def preSource (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) :=
  (SKM.homPre (k := k) (inductionCell D Sc m i)).mapIso
    ((SKM.homParityShiftDatum (k := k) ((cut i - 1) • D.parity i)).iso
      (restrictionCell D Sc m i ≫ H)) ≪≫
    (associator (inductionCell D Sc m i) (restrictionCell D Sc m i) H).symm

omit [Fintype I] in
/-- Source shift removal retains its last-row degree; it is not an even
identification of the two input objects. -/
theorem preSource_mem (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) :
    (preSource D Sc m R i H).hom ∈ parity (R := k) _ _ ((cut i - 1) • D.parity i) := by
  simpa only [preSource, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, add_zero] using
    comp_mem (IsSuperfunctor.map_mem (F := SKM.homPre (k := k) (inductionCell D Sc m i))
      ((SKM.homParityShiftDatum (k := k) ((cut i - 1) • D.parity i)).hom_mem
        (restrictionCell D Sc m i ≫ H)))
      (inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) _ _ _))

/-- The literal parity-shifted precomposition block evaluated at the probe. -/
def shiftedPreSourceObject (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) : R :=
  ((SKM.homPre (k := k) (inductionCell D Sc m i)).obj
    ((SKM.homParityShift (k := k) ((cut i - 1) • D.parity i)).obj
      (restrictionCell D Sc m i ≫ H))).obj N

/-- Evaluate that exact comparison on the original regular probe. -/
def preSourceComponent (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) :
    shiftedPreSourceObject D Sc m R i H ≅ H.obj (source D Sc m i) :=
  (evaluation N).mapIso (preSource D Sc m R i H)

/-- The cap row on the chosen shifted precomposition block. This map uses
the prescribed cap and source comparison, but asserts no left adjunction. -/
def shiftedPreCap (R : PiSCat.{u,u,u+1} k) (i : I) (hP : 0 < cut i)
    (H : modulePiCategory D Sc m ⟶ R) :
    shiftedPreSourceObject D Sc m R i H ⟶ H.obj N :=
  (sourceCapRow H (preSource D Sc m R i H) (capCell D Sc m i hP)).total N

/-- The exact prescribed cap after the canonical input comparison. -/
theorem shiftedPreCap_eq (R : PiSCat.{u,u,u+1} k) (i : I) (hP : 0 < cut i)
    (H : modulePiCategory D Sc m ⟶ R) :
    shiftedPreCap D Sc m R i hP H =
      (preSourceComponent D Sc m R i H).hom ≫ H.map (cap D Sc m i hP) := by
  rw [shiftedPreCap, sourceCapRow_total, capCell_total]
  rfl

/-- Each power of the same precomposition dot in those source coordinates. -/
def coordinatePreDotPower (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) (a : ℕ) : End (shiftedPreSourceObject D Sc m R i H) :=
  (preSourceComponent D Sc m R i H).hom ≫
    (preDotEnd D Sc m R i H ^ a) ≫ (preSourceComponent D Sc m R i H).inv

/-- In the chosen source coordinates the normalized cap is even, because
the source comparison and prescribed cap both have degree `(P-1)p`. -/
theorem shiftedPreCap_mem (R : PiSCat.{u,u,u+1} k) (i : I) (hP : 0 < cut i)
    (H : modulePiCategory D Sc m ⟶ R) :
    shiftedPreCap D Sc m R i hP H ∈ parity (R := k) _ _ 0 := by
  exact total_mem (sourceCapRow_mem H (preSource D Sc m R i H)
    (capCell D Sc m i hP) (preSource_mem D Sc m R i H) (capCell_mem D Sc m i hP)) N

/-- The same signed polynomial survives canonical source parity transport. -/
theorem coordinatePreDot_odd_polynomial (R : PiSCat.{u,u,u+1} k) (i : I) (hi : D.parity i = 1)
    (H : modulePiCategory D Sc m ⟶ R) :
    (coordinatePreDotPower D Sc m R i H 1 ^ 2 + 1) ^ m i = 0 := by
  simpa only [coordinatePreDotPower, pow_one, Iso.conj_apply, Iso.symm_inv, Iso.symm_hom] using
    coordinate_polynomial (preSourceComponent D Sc m R i H) (preDotEnd D Sc m R i H) (m i)
      (preDot_odd_polynomial D Sc m R i hi H)

end OddMath.QuiverHecke.ELV.ProbeVacuumCap
end

end

section

/-! # The normalized whole-weight pre-Hom cap on the regular probe

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
insert the actual normalized probe counit into the prescribed pre-Hom
adjunction. Its regular-probe evaluation is the literal shifted native
cap through the source shift, whole-weight FE, and native source charts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open CyclotomicAction
universe u
local instance preCapHomPi {k : Type u} [CommRing k] (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

private def totalEvaluation_2 {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A] (N : C) :
    Superfunctor k C A ⥤ A where
  obj F := F.obj N
  map f := f.total N
  map_id F := SuperNatTrans.id_total F.toFunctor N
  map_comp f g := Superfunctor.comp_total f g N

private theorem total_zsmul {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : Superfunctor k C A} (f : F ⟶ G) (z : ℤ) (N : C) :
    (z • f).total N = z • f.total N := by
  change z • f.app 0 N + z • f.app 1 N = z • (f.app 0 N + f.app 1 N)
  exact (smul_add _ _ _).symm

private theorem rightWhisker_total {k : Type u} [CommRing k]
    {A B C : PiSCat.{u,u,u+1} k} {F G : A ⟶ B} (f : F ⟶ G) (Z : B ⟶ C) (N : A) :
    (f ▷ Z).total N = Z.map (f.total N) := by
  change Z.map (f.app 0 N) + Z.map (f.app 1 N) = Z.map (f.app 0 N + f.app 1 N)
  exact (Functor.map_add Z.toFunctor).symm

private theorem preCounit_total
    {I X k : Type u} [AddCommGroup X] [CommRing k] {D : SKM.Datum I X}
    (T : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    (W : X → PiSCat.{u,u,u+1} k) (i : I) (muM : X) {muP nuP : X}
    (h : -nuP + D.α i = -muP) (Z : SKM.homWeightSector T.obj W nuP muM)
    (N : T.obj (-nuP)) :
    ((SKM.homContentPreAdjunction T W T.leftAdjoints i muM h).counit.app Z).total N =
      koszulSign (SKM.leftAdjParity D i (-nuP)) (SKM.leftAdjParity D i (-nuP)) •
        ((SKM.homContentPreInverseSource T W i muM h Z).hom.total N ≫
          Z.map ((T.leftAdjoints.adjL i h).counit.total N)) := by
  have hrow : (SKM.homContentPreAdjunction T W T.leftAdjoints i muM h).counit.app Z =
      koszulSign (SKM.leftAdjParity D i (-nuP)) (SKM.leftAdjParity D i (-nuP)) •
        ((SKM.homContentPreInverseSource T W i muM h Z).hom ≫
          (T.leftAdjoints.adjL i h).counit ▷ Z ≫ (leftUnitor Z).hom) := by
    simpa only [SKM.homContentPreInverseSource, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, SKM.homPre, Category.assoc, ← SKM.RouquierFamily.leftAdjoints_counit] using
        SKM.homContentPreAdjunction_leftAdjoints_counit_app T W i muM h Z
  rw [hrow]
  change (koszulSign (SKM.leftAdjParity D i (-nuP)) (SKM.leftAdjParity D i (-nuP)) •
    ((SKM.homContentPreInverseSource T W i muM h Z).hom ≫
      (T.leftAdjoints.adjL i h).counit ▷ Z ≫ (leftUnitor Z).hom)).total N = _
  rw [total_zsmul, Superfunctor.comp_total, Superfunctor.comp_total, rightWhisker_total]
  have hu : (leftUnitor Z).hom.total N = 𝟙 (Z.obj N) := SuperNatTrans.id_total Z.toFunctor N
  rw [hu]
  erw [Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ) (Λ : X)
  (hc : ∀ i, (probeCutoff D m i : ℤ) = D.h i Λ)
  (W : X → PiSCat.{u,u,u+1} k) (muM : X) (i : I) {muP : X}
  (h : -Λ + D.α i = -muP) (H : ProbeVacuumCap.modulePiCategory D Sc m ⟶ W muM)
local notation "T" => probeOldRouquierFamily D Sc m Λ hc
local notation "N₀" => regularProbe D Sc m Λ

/-- The Hom input retains the whole weight product before selecting its
empty probe content and applying the given output functor. -/
def preCapInput : SKM.homWeightSector (T).obj W Λ muM :=
  (emptyProbe D Sc m Λ).comp H
local notation "Z" => preCapInput D Sc m Λ hc W muM H

/-- The actual shifted pre-Hom source is identified with the prescribed
native shifted source through all three selected source comparisons. -/
def vacuumPreSourceIso :
    (((SKM.homContentPreE (T) W i muM h).obj
      ((SKM.homContentPreF (T) W i muM h).obj Z)).obj N₀) ≅
      ProbeVacuumCap.shiftedPreSourceObject D Sc m (W muM) i H :=
  (totalEvaluation_2 N₀).mapIso (SKM.homContentPreInverseSource (T) W i muM h Z) ≪≫
    H.toFunctor.mapIso (vacuumCapSourceIso D Sc m Λ i h) ≪≫
      (ProbeVacuumCap.preSourceComponent D Sc m (W muM) i H).symm

/-- The prescribed whole-weight pre-Hom counit evaluates to the native
shifted cap under the selected source chart. No cap compatibility or
moment premise is supplied. -/
theorem vacuumPreCounit_eq (hP : 0 < probeCutoff D m i) :
    ((SKM.homContentPreAdjunction (T) W (T).leftAdjoints i muM h).counit.app Z).total N₀ ≫
      H.map (eqToHom (emptyProbe_regular D Sc m Λ)) =
    (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom ≫
      ProbeVacuumCap.shiftedPreCap D Sc m (W muM) i hP H := by
  have hw := preCounit_total (T) W i muM h Z N₀
  have hout := congrArg (fun f => f ≫ H.map (eqToHom (emptyProbe_regular D Sc m Λ))) hw
  refine hout.trans ?_
  have hn := congrArg H.toFunctor.map (vacuumLeftCounit_eq D Sc m Λ i h hc hP)
  rw [CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp] at hn
  change (koszulSign (SKM.leftAdjParity D i (-Λ)) (SKM.leftAdjParity D i (-Λ)) •
      ((SKM.homContentPreInverseSource (T) W i muM h Z).hom.total N₀ ≫
        H.map ((emptyProbe D Sc m Λ).map (((T).leftAdjoints.adjL i h).counit.total N₀)))) ≫
        H.map (eqToHom (emptyProbe_regular D Sc m Λ)) = _
  rw [Preadditive.zsmul_comp, Category.assoc, ← Preadditive.comp_zsmul, hn,
    ProbeVacuumCap.shiftedPreCap_eq]
  simp only [vacuumPreSourceIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    totalEvaluation_2, Category.assoc, Iso.inv_hom_id_assoc]

end OddMath.QuiverHecke.ELV.WeightTensorVacuum
end

end

section

/-! # The raw restricted probe dot in the successor source chart

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
the raw probe dot on the upper loop follows the same selected successor
chart as the whole-weight left cap, at every input weight module.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV CyclotomicAction
universe u

private theorem rightWhisker_total
    {k : Type u} [CommRing k] {A B C : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ B} (f : F ⟶ G) (Z : B ⟶ C) (N : A) :
    (f ▷ Z).total N = Z.map (f.total N) := by
  change Z.map (f.app 0 N) + Z.map (f.app 1 N) = Z.map (f.app 0 N + f.app 1 N)
  exact (Functor.map_add Z.toFunctor).symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  (δ : WeightBlocks D Λ x) (M : ProbeOldWeightProduct D Sc m Λ x)
local notation "ε" => blockSucc D Λ i h δ
local notation "perm" => probeOldBlockTarget_perm D i Λ h δ ε rfl
local notation "R" => probeOldBlockRes D Sc m i Λ h δ

/-- The raw upper-loop dot commutes with the selected successor source
chart, without a moment hypothesis or a choice of inverse dot. -/
theorem probeOldWeightFollowing_dot :
    ((probeOldActionDot D Sc m i Λ h ▷ probeOldF D Sc m i Λ h).total M) δ ≫
      eqToHom (probeOldWeightFollowing_obj D Sc m i Λ h δ M) =
    eqToHom (probeOldWeightFollowing_obj D Sc m i Λ h δ M) ≫
      (R).map (probeAppendToDotComponent D Sc m δ.1.toList i ε.1.toList perm (M δ)) := by
  rw [rightWhisker_total, probeOldWeightFollowing_eqToHom]
  change (R).map ((probeOldActionDot D Sc m i Λ h).total M ε) ≫ _ = _
  rw [probeOldActionDot_via_total D Sc m i Λ h δ ε rfl M]
  simp only [Category.assoc, ← Functor.map_comp,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

end OddMath.QuiverHecke
end

end

section

/-! # Restricted probe dots through the upper-loop chart

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
the same OLD append comparison used for the cap source preserves the
raw restricted induction dot at every input module.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor
universe u
attribute [local irreducible] oldAppendReindexIso
private theorem restriction_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (w : C) :
    ((restriction Q).map f).total w = f.total (Q.obj w) := rfl

private theorem transform_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    {J : C ⥤ A} [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ v, J.obj v ⟶ J.obj v} (hα : IsSupernatural k p α)
    (N : Superfunctor k C (SVec k)) (w : A) :
    (transformComponent hα N).total w = transformLinear hα N w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (γ : List I) (i : I) {μ : List I} (h : (i :: γ).Perm μ)
local notation "cut" => probeCutoff D m
local notation "K₀" => oldContentAppendTo D Sc cut γ i (i :: γ) (List.Perm.refl _)
local notation "K" => oldContentAppendTo D Sc cut γ i μ h
local notation "e" => oldAppendReindexIso D Sc cut (List.Perm.refl γ) i
  (List.Perm.refl (i :: γ)) h h

/-- The actual restricted signed dots commute with the selected even
upper-loop comparison before choosing the original regular probe. -/
theorem oldAppendUpperLoop_dot
    (N : Superfunctor k (OldContentCategory D Sc cut γ) (SVec k)) :
    restrictedDotEnd K₀
      (probeAppendToDot_supernatural D Sc m γ i (i :: γ) (List.Perm.refl _)) N ≫
        (restriction K).map ((e).hom.app N) =
      (restriction K).map ((e).hom.app N) ≫
        restrictedDotEnd K (probeAppendToDot_supernatural D Sc m γ i μ h) N := by
  have hd := oldAppendReindexIso_dot D Sc m (List.Perm.refl γ) i
    (List.Perm.refl (i :: γ)) h h N
  have hm := congrArg (restriction K).map hd
  apply HomogeneousSuperfunctorIso.total_ext
  intro w
  have hw := congrArg (fun f => f.total w) hm
  simp only [restrictedDotEnd, Functor.mapEnd_apply, dotEnd, Functor.map_comp,
    Superfunctor.comp_total, restriction_total, transform_total] at hw ⊢
  convert hw using 1 <;> rfl

end OddMath.QuiverHecke
end

end

section

/-! # The whole-weight raw vacuum dot in the cap source chart

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
transport the literal restricted probe dot through precisely the source
isomorphism used for the normalized whole-weight cap.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open CyclotomicAction BalancedInduction CyclotomicCrossingTensor
attribute [local irreducible] probeAppendUpperLoopSuperIso
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)

/-- The dot before selecting any source comparison. -/
def evaluatedLoopDot (ν : List I) (i : I) (N : ProbeEvaluatedModules D Sc m ν) :
    End ((probeEvaluatedRestriction D Sc m ν i).obj
      ((probeEvaluatedInduction D Sc m ν i).obj N)) :=
  (probeEvaluatedRestriction D Sc m ν i).map
    (probeAppendToDotComponent D Sc m ν i (i :: ν) (List.Perm.refl _) N)

/-- The OLD upper-loop comparison preserves the raw dot on every input. -/
theorem upperLoop_dot (ν : List I) (i : I) {μ : List I}
    (perm : (i :: ν).Perm μ) (N : ProbeEvaluatedModules D Sc m ν) :
    evaluatedLoopDot D Sc m ν i N ≫
      (probeAppendUpperLoopSuperIso D Sc m ν i perm).hom.total N =
    (probeAppendUpperLoopSuperIso D Sc m ν i perm).hom.total N ≫
      (probeEvaluatedRestrictTo D Sc m ν i μ perm).map
        (probeAppendToDotComponent D Sc m ν i μ perm N) := by
  apply InducedCategory.hom_ext
  change (evaluatedLoopDot D Sc m ν i N).hom ≫
      ((probeAppendUpperLoopSuperIso D Sc m ν i perm).hom.total N).hom =
    ((probeAppendUpperLoopSuperIso D Sc m ν i perm).hom.total N).hom ≫ _
  rw [probeAppendUpperLoopSuperIso_hom_total]
  exact oldAppendUpperLoop_dot D Sc m ν i perm N.obj

/-- Empty-content forgetting keeps this entire dot map. -/
theorem forgetEmpty_upper_dot (ν : List I) (hν : ν = []) (i : I)
    (N : ProbeEvaluatedModules D Sc m ν) :
    (emptyContentForget D Sc m ν hν).map (evaluatedLoopDot D Sc m ν i N) ≫
      eqToHom (forgetEmpty_upper_obj D Sc m ν hν i N) =
    eqToHom (forgetEmpty_upper_obj D Sc m ν hν i N) ≫
      restrictedDotEnd (oldContentAppend D Sc (probeCutoff D m) [] i)
        (probeOldContentAppendDot_supernatural D Sc m [] i)
        ((emptyContentForget D Sc m ν hν).obj N) := by
  subst ν
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  rfl

private def totalEvaluation_3 {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A] (N : C) :
    Superfunctor k C A ⥤ A where
  obj F := F.obj N
  map f := f.total N
  map_id F := SuperNatTrans.id_total F.toFunctor N
  map_comp f g := Superfunctor.comp_total f g N

private theorem inverse_square {C : Type*} [Category C] {A B : C}
    (e : A ≅ B) (f : End A) (g : End B) (h : f ≫ e.hom = e.hom ≫ g) :
    g ≫ e.inv = e.inv ≫ f := by
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, ← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

private theorem four_squares {C : Type*} [Category C] {A B E F G : C}
    (a : A ≅ B) (b : B ≅ E) (c : E ≅ F) (d : F ≅ G)
    (x : End A) (y : End B) (z : End E) (v : End F) (w : End G)
    (ha : x ≫ a.hom = a.hom ≫ y) (hb : y ≫ b.hom = b.hom ≫ z)
    (hc : z ≫ c.hom = c.hom ≫ v) (hd : v ≫ d.hom = d.hom ≫ w) :
    x ≫ (a ≪≫ b ≪≫ c ≪≫ d).hom = (a ≪≫ b ≪≫ c ≪≫ d).hom ≫ w := by
  simp only [Iso.trans_hom, Category.assoc]
  rw [reassoc_of% ha, reassoc_of% hb, reassoc_of% hc, hd]

private theorem family_eqToHom_2 {C : Type*} [Category C] (F : C ⥤ C)
    (a : ∀ N, End (F.obj N)) {M N : C} (h : M = N) :
    a M ≫ F.map (eqToHom h) = F.map (eqToHom h) ≫ a N := by
  subst N
  simp

private theorem emptyBlock_list_2 (Λ : X) :
    (emptyBlock D Λ).1.toList = [] := Multiset.toList_zero

variable [Fintype I] (Λ : X) (i : I) {y : X} (edge : -Λ + D.α i = y)
local notation "δ₀" => emptyBlock D Λ
local notation "N₀" => regularProbe D Sc m Λ
local notation "γ₀" => Multiset.toList (Subtype.val (emptyBlock D Λ))
local notation "perm" => probeOldBlockTarget_perm D i Λ edge δ₀ (blockSucc D Λ i edge δ₀) rfl
local notation "F₀" => emptyContentForget D Sc m γ₀ (emptyBlock_list_2 D Λ)
local notation "K" => oldContentAppend D Sc (probeCutoff D m) [] i

/-- The literal whole-weight raw upper-loop dot retains its empty block. -/
def vacuumLoopDot :
    End ((emptyProbe D Sc m Λ).obj
      (((probeOldE D Sc m i Λ edge) ≫ (probeOldF D Sc m i Λ edge)).obj N₀)) :=
  (emptyProbe D Sc m Λ).map
    ((probeOldActionDot D Sc m i Λ edge ▷ probeOldF D Sc m i Λ edge).total N₀)

/-- The raw whole-weight dot and the prescribed module dot commute with
exactly the cap's four-factor source chart. -/
theorem vacuumLoopDot_source :
    vacuumLoopDot D Sc m Λ i edge ≫ (vacuumCapSourceIso D Sc m Λ i edge).hom =
      (vacuumCapSourceIso D Sc m Λ i edge).hom ≫ ProbeVacuumCap.moduleDot D Sc m i := by
  let e := (totalEvaluation_3 (N₀ δ₀)).mapIso
    (probeAppendUpperLoopSuperIso D Sc m γ₀ i perm)
  have h₁ := congrArg (F₀).map
    (probeOldWeightFollowing_dot D Sc m i Λ edge δ₀ N₀)
  rw [Functor.map_comp, Functor.map_comp] at h₁
  have hu := upperLoop_dot D Sc m γ₀ i perm (N₀ δ₀)
  have hu' := inverse_square e (evaluatedLoopDot D Sc m γ₀ i (N₀ δ₀))
    ((probeEvaluatedRestrictTo D Sc m γ₀ i _ perm).map
      (probeAppendToDotComponent D Sc m γ₀ i _ perm (N₀ δ₀))) hu
  have h₂ := congrArg (F₀).map hu'
  rw [Functor.map_comp, Functor.map_comp] at h₂
  have h₃ := forgetEmpty_upper_dot D Sc m γ₀ (emptyBlock_list_2 D Λ) i (N₀ δ₀)
  have h₄ := family_eqToHom_2 ((induction K) ⋙ (restriction K))
    (fun N => restrictedDotEnd K (probeOldContentAppendDot_supernatural D Sc m [] i) N)
    (emptyProbe_regular D Sc m Λ)
  let a := (F₀).mapIso (eqToIso (probeOldWeightFollowing_obj D Sc m i Λ edge δ₀ N₀))
  let b := (F₀).mapIso e.symm
  let c := eqToIso (forgetEmpty_upper_obj D Sc m γ₀ (emptyBlock_list_2 D Λ) i (N₀ δ₀))
  let d := ((induction K) ⋙ (restriction K)).mapIso (eqToIso (emptyProbe_regular D Sc m Λ))
  let y := (F₀).map ((probeEvaluatedRestrictTo D Sc m γ₀ i _ perm).map
    (probeAppendToDotComponent D Sc m γ₀ i _ perm (N₀ δ₀)))
  let z := (F₀).map (evaluatedLoopDot D Sc m γ₀ i (N₀ δ₀))
  let v := restrictedDotEnd K (probeOldContentAppendDot_supernatural D Sc m [] i) ((F₀).obj (N₀ δ₀))
  have ha : vacuumLoopDot D Sc m Λ i edge ≫ a.hom = a.hom ≫ y := by
    convert h₁ using 1 <;> rfl
  have hb : y ≫ b.hom = b.hom ≫ z := by
    convert h₂ using 1 <;> rfl
  have hc : z ≫ c.hom = c.hom ≫ v := h₃
  have hd : v ≫ d.hom = d.hom ≫ ProbeVacuumCap.moduleDot D Sc m i := by
    convert h₄ using 1 <;> rfl
  have hf := four_squares a b c d (vacuumLoopDot D Sc m Λ i edge) y z v
    (ProbeVacuumCap.moduleDot D Sc m i) ha hb hc hd
  convert hf using 1 <;> rfl

end OddMath.QuiverHecke.ELV.WeightTensorVacuum
end

end

section

/-! # Koszul signs of the probe dot in shifted precomposition coordinates

The dot in `SwappedActionAssembly.md`, §5 (A14), acts before removal of
the source parity shift. Super-interchange supplies its power signs. The
same probe polynomial survives this signed change of coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u
local instance probeCapPreDotHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private def sourceIso {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    (E : A ⟶ B) (F : B ⟶ A) (H : A ⟶ R) (σ : ZMod 2) :=
  (SKM.homPre (k := k) E).mapIso ((SKM.homParityShiftDatum (k := k) σ).iso (F ≫ H)) ≪≫
    (associator E F H).symm

private theorem source_dot_sign {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    (E : A ⟶ B) (F : B ⟶ A) (H : A ⟶ R) (σ : ZMod 2)
    (x : End E) {p : ZMod 2} (hx : x ∈ parity (R := k) _ _ p) :
    (x ▷ (SKM.homParityShift (k := k) σ).obj (F ≫ H)) ≫ (sourceIso E F H σ).hom =
      koszulSign p σ • ((sourceIso E F H σ).hom ≫ ((x ▷ F) ▷ H)) := by
  simp only [sourceIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    PiSCat.associator_inv]
  erw [Category.comp_id]
  exact TwoSupercategory.super_interchange hx
    ((SKM.homParityShiftDatum (k := k) σ).hom_mem (F ≫ H))

private theorem total_zsmul {k : Type u} [CommRing k] {A R : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ R} (η : F ⟶ G) (z : ℤ) (M : A) :
    (z • η).total M = z • η.total M := by
  change z • η.app 0 M + z • η.app 1 M = z • (η.app 0 M + η.app 1 M)
  exact (smul_add _ _ _).symm

private theorem whisker_total {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ B} (η : F ⟶ G) (H : B ⟶ R) (M : A) :
    (η ▷ H).total M = H.map (η.total M) := by
  change H.map (η.app 0 M) + H.map (η.app 1 M) = H.map (η.app 0 M + η.app 1 M)
  exact (Functor.map_add H.toFunctor).symm

private theorem induction_dot_supernatural
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α) :
    IsSupernatural k p (F := induction J) (G := induction J) (fun M => dotEnd J hα M) :=
  transformComponent_supernatural hα

private theorem family_total {k : Type u} [CommRing k] {C A : Type*}
    [Category C] [Category A] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : C ⥤ A} {p : ZMod 2} {α : ∀ M, F.obj M ⟶ G.obj M}
    (hα : IsSupernatural k p α) (M : C) : hα.toSuperNatTrans.total M = α M := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans]

private theorem restriction_dotEnd
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) :
    (restriction J).map (dotEnd J hα M) = restrictedDotEnd J hα M := rfl

private theorem signed_conjugation {C : Type*} [Category C] [Preadditive C]
    {T S : C} (e : T ≅ S) (a : End T) (b : End S) (z : ℤ)
    (h : a ≫ e.hom = z • (e.hom ≫ b)) : a = z • (e.symm.conj b) := by
  have hh := congrArg (fun f => f ≫ e.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Preadditive.zsmul_comp,
    Iso.conj_apply, Iso.symm_inv, Iso.symm_hom] using hh

private theorem signed_polynomial {A : Type*} [Ring A] (d : A) (p σ : ZMod 2) (n : ℕ)
    (h : (d ^ 2 + 1) ^ n = 0) : ((koszulSign p σ • d) ^ 2 + 1) ^ n = 0 := by
  rw [smul_pow, pow_two (koszulSign p σ), koszulSign_mul_self, one_smul]
  exact h

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
local notation "K" => oldContentAppend D Sc cut []

/-- The original induction dot before any source parity comparison. -/
def inductionDotCell (i : I) : End (inductionCell D Sc m i) :=
  (induction_dot_supernatural (K i) (probeOldContentAppendDot_supernatural D Sc m [] i)).toSuperNatTrans

omit [Fintype I] in
/-- Its homogeneous degree is the moving-colour parity. -/
theorem inductionDotCell_mem (i : I) :
    inductionDotCell D Sc m i ∈ parity (R := k) _ _ (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (induction_dot_supernatural (K i)
      (probeOldContentAppendDot_supernatural D Sc m [] i)).toSuperNatTrans_isHomogeneous

/-- Its probe component is the given signed induction dot. -/
theorem inductionDotCell_total (i : I) :
    (inductionDotCell D Sc m i).total N =
      dotEnd (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N :=
  family_total (induction_dot_supernatural (K i)
    (probeOldContentAppendDot_supernatural D Sc m [] i)) N

/-- The literal raw pre-induction dot on the parity-shifted Hom source. -/
def shiftedPreDot (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) : End (shiftedPreSourceObject D Sc m R i H) :=
  ((inductionDotCell D Sc m i) ▷
    (SKM.homParityShift (k := k) ((cut i - 1) • D.parity i)).obj
      (restrictionCell D Sc m i ≫ H)).total N

/-- Passing the raw induction dot through the canonical source parity
comparison retains precisely its super-interchange sign. -/
theorem shiftedPreDot_coordinates (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) :
    shiftedPreDot D Sc m R i H =
      koszulSign (D.parity i) ((cut i - 1) • D.parity i) •
        coordinatePreDotPower D Sc m R i H 1 := by
  have h := congrArg (fun η => η.total N)
    (source_dot_sign (inductionCell D Sc m i) (restrictionCell D Sc m i) H
      ((cut i - 1) • D.parity i) (inductionDotCell D Sc m i) (inductionDotCell_mem D Sc m i))
  rw [Superfunctor.comp_total, total_zsmul, Superfunctor.comp_total,
    whisker_total, whisker_total, whisker_total, inductionDotCell_total] at h
  have hr := restriction_dotEnd (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N
  change (restrictionCell D Sc m i).map _ = moduleDot D Sc m i at hr
  erw [hr] at h
  have hc := signed_conjugation (preSourceComponent D Sc m R i H)
    (shiftedPreDot D Sc m R i H) (preDotEnd D Sc m R i H)
    (koszulSign (D.parity i) ((cut i - 1) • D.parity i))
  rw [preDotEnd_eq] at hc
  have hraw : shiftedPreDot D Sc m R i H =
      ((SKM.homParityShift (k := k) ((cut i - 1) • D.parity i)).obj
        (restrictionCell D Sc m i ≫ H)).map
          (dotEnd (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N) := by
    rw [shiftedPreDot, whisker_total, inductionDotCell_total]
  have he : (preSourceComponent D Sc m R i H).hom =
      (sourceIso (inductionCell D Sc m i) (restrictionCell D Sc m i) H
        ((cut i - 1) • D.parity i)).hom.total N := rfl
  rw [← hraw, ← he] at h
  simpa only [coordinatePreDotPower, pow_one, preDotEnd_eq, Iso.conj_apply,
    Iso.symm_inv, Iso.symm_hom] using hc h

/-- Squaring removes the comparison sign, so the prescribed signed probe
polynomial holds on the actual shifted pre-induction dot. -/
theorem shiftedPreDot_odd_polynomial (R : PiSCat.{u,u,u+1} k) (i : I) (hi : D.parity i = 1)
    (H : modulePiCategory D Sc m ⟶ R) :
    (shiftedPreDot D Sc m R i H ^ 2 + 1) ^ m i = 0 := by
  rw [shiftedPreDot_coordinates]
  exact signed_polynomial _ _ _ _ (coordinatePreDot_odd_polynomial D Sc m R i hi H)

end OddMath.QuiverHecke.ELV.ProbeVacuumCap
end

end

section

/-! # Raw whole-weight pre-dots on the regular probe

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
retain the raw induction dot through the chosen source parity comparison,
with the same source chart as the normalized pre-Hom counit.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open CyclotomicAction
universe u
local instance preDotHomPi {k : Type u} [CommRing k] (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

private theorem preSource_dot_sign
    {I X k : Type u} [AddCommGroup X] [CommRing k] {D : SKM.Datum I X}
    (T : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    (W : X → PiSCat.{u,u,u+1} k) (i : I) (muM : X) {muP nuP : X}
    (h : -nuP + D.α i = -muP) (Z : SKM.homWeightSector T.obj W nuP muM) :
    SKM.homReservoirDot T W i muM h ((SKM.homContentPreF T W i muM h).obj Z) ≫
      (SKM.homContentPreInverseSource T W i muM h Z).hom =
    koszulSign (D.parity i) (SKM.leftAdjParity D i (-nuP)) •
      ((SKM.homContentPreInverseSource T W i muM h Z).hom ≫ ((T.dot i h ▷ T.F i h) ▷ Z)) := by
  simp only [SKM.homReservoirDot, SKM.homContentPreInverseSource, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, PiSCat.associator_inv, SKM.homPre]
  erw [Category.comp_id]
  exact TwoSupercategory.super_interchange (T.dot_mem i h)
    ((SKM.homParityShiftDatum (k := k) (SKM.leftAdjParity D i (-nuP))).hom_mem (T.F i h ≫ Z))

private theorem total_zsmul_2 {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : Superfunctor k C A} (f : F ⟶ G) (z : ℤ) (N : C) :
    (z • f).total N = z • f.total N := by
  change z • f.app 0 N + z • f.app 1 N = z • (f.app 0 N + f.app 1 N)
  exact (smul_add _ _ _).symm

private theorem rightWhisker_total_2 {k : Type u} [CommRing k]
    {A B C : PiSCat.{u,u,u+1} k} {F G : A ⟶ B} (f : F ⟶ G) (Z : B ⟶ C) (N : A) :
    (f ▷ Z).total N = Z.map (f.total N) := by
  change Z.map (f.app 0 N) + Z.map (f.app 1 N) = Z.map (f.app 0 N + f.app 1 N)
  exact (Functor.map_add Z.toFunctor).symm

private def totalEvaluation_4 {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A] (N : C) :
    Superfunctor k C A ⥤ A where
  obj F := F.obj N
  map f := f.total N
  map_id F := SuperNatTrans.id_total F.toFunctor N
  map_comp f g := Superfunctor.comp_total f g N

private theorem signed_three_squares {C : Type*} [Category C] [Preadditive C]
    {A B E F : C} (a : A ≅ B) (b : B ≅ E) (c : F ≅ E)
    (x : End A) (y : End B) (z : End E) (v : End F) (q : ℤ)
    (ha : x ≫ a.hom = q • (a.hom ≫ y)) (hb : y ≫ b.hom = b.hom ≫ z)
    (hc : c.inv ≫ v = q • (z ≫ c.inv)) :
    x ≫ (a ≪≫ b ≪≫ c.symm).hom = (a ≪≫ b ≪≫ c.symm).hom ≫ v := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% ha]
  simp only [Preadditive.zsmul_comp, Category.assoc]
  rw [reassoc_of% hb, hc, Preadditive.comp_zsmul, Preadditive.comp_zsmul]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ) (Λ : X)
  (hc : ∀ i, (probeCutoff D m i : ℤ) = D.h i Λ)
  (W : X → PiSCat.{u,u,u+1} k) (muM : X) (i : I) {muP : X}
  (h : -Λ + D.α i = -muP) (H : ProbeVacuumCap.modulePiCategory D Sc m ⟶ W muM)
local notation "T" => probeOldRouquierFamily D Sc m Λ hc
local notation "N₀" => regularProbe D Sc m Λ
local notation "Z" => preCapInput D Sc m Λ hc W muM H

include hc in
omit [Fintype I] in
private theorem vacuumAdjParity (hP : 0 < probeCutoff D m i) :
    SKM.leftAdjParity D i (-Λ) = (probeCutoff D m i - 1) • D.parity i := by
  have he : D.h i (-Λ) = - (probeCutoff D m i : ℤ) := by
    rw [show D.h i (-Λ) = -D.h i Λ from map_neg (D.cd.coroot i) Λ, ← hc i]
  rw [SKM.leftAdjParity, he, Int.cast_neg, Int.cast_natCast, nsmul_eq_mul,
    Nat.cast_sub (by omega : 1 ≤ probeCutoff D m i), Nat.cast_one]
  generalize (probeCutoff D m i : ZMod 2) = a
  generalize D.parity i = p
  fin_cases a <;> fin_cases p <;> decide

/-- The raw chosen pre-Hom dot commutes with the same source chart as
the chosen pre-Hom counit. Both source-shift Koszul factors are retained
and matched before the comparison. -/
theorem vacuumPreDot_source (hP : 0 < probeCutoff D m i) :
    (SKM.homReservoirDot T W i muM h ((SKM.homContentPreF T W i muM h).obj Z)).total N₀ ≫
      (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom =
    (vacuumPreSourceIso D Sc m Λ hc W muM i h H).hom ≫
      ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H := by
  have hs := congrArg (fun f => f.total N₀) (preSource_dot_sign T W i muM h Z)
  rw [Superfunctor.comp_total, total_zsmul_2, Superfunctor.comp_total, rightWhisker_total_2] at hs
  have hv := congrArg H.toFunctor.map (vacuumLoopDot_source D Sc m Λ i h)
  rw [Functor.map_comp, Functor.map_comp] at hv
  have hn : (ProbeVacuumCap.preSourceComponent D Sc m (W muM) i H).inv ≫
      ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H =
    koszulSign (D.parity i) (SKM.leftAdjParity D i (-Λ)) •
      (H.map (ProbeVacuumCap.moduleDot D Sc m i) ≫
        (ProbeVacuumCap.preSourceComponent D Sc m (W muM) i H).inv) := by
    rw [ProbeVacuumCap.shiftedPreDot_coordinates, Preadditive.comp_zsmul]
    simp only [ProbeVacuumCap.coordinatePreDotPower, pow_one,
      ProbeVacuumCap.preDotEnd_eq, Iso.inv_hom_id_assoc,
      vacuumAdjParity D m Λ hc i hP]
  let a := (totalEvaluation_4 N₀).mapIso (SKM.homContentPreInverseSource T W i muM h Z)
  let b := H.toFunctor.mapIso (vacuumCapSourceIso D Sc m Λ i h)
  let c := ProbeVacuumCap.preSourceComponent D Sc m (W muM) i H
  let x := (SKM.homReservoirDot T W i muM h ((SKM.homContentPreF T W i muM h).obj Z)).total N₀
  let y := H.map (vacuumLoopDot D Sc m Λ i h)
  let z := H.map (ProbeVacuumCap.moduleDot D Sc m i)
  let v := ProbeVacuumCap.shiftedPreDot D Sc m (W muM) i H
  let q := koszulSign (D.parity i) (SKM.leftAdjParity D i (-Λ))
  have ha : x ≫ a.hom = q • (a.hom ≫ y) := by
    convert hs using 1 <;> rfl
  have hb : y ≫ b.hom = b.hom ≫ z := by
    convert hv using 1 <;> rfl
  have hc : c.inv ≫ v = q • (z ≫ c.inv) := hn
  have hf := signed_three_squares a b c x y z v q ha hb hc
  convert hf using 1 <;> rfl

end OddMath.QuiverHecke.ELV.WeightTensorVacuum
end

end
