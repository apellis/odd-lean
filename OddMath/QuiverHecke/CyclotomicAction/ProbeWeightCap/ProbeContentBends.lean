import Mathlib.CategoryTheory.Conj
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightCap.ProbeCapPreDotSigns
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightCap.ProbeWeightPreCap
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightCap.ProbeWeightVacuumDot
import OddMath.QuiverHecke.SwappedAssembly.Generators.Leftward
import OddMath.QuiverHecke.SwappedAssembly.Inversion
import OddMath.QuiverHecke.SwappedAssembly.Sigma.MixedEntry
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SupportedProbeSlideWindow

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
