import OddMath.QuiverHecke.CyclotomicAction.ELVOutputDotBounds
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeFiniteBends
import OddMath.QuiverHecke.SwappedAssembly.Sigma.BendWindowEquations

/-! # Mixed bends at a whole output-content category

`SwappedHomInversion.md` §3 (4)–(6) and §4 (J): retain every probe input
while projecting to one reservoir output content. A fixed source-content
dot bound gives finite series in the same functor Hom category as the
content coefficient ideal. The exponent may depend on output content.
-/
noncomputable section
set_option quotPrecheck false
open scoped BigOperators
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction SwappedAssembly
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
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (δ : WeightBlocks D ΛR ((P).muM t)) :
    ∃ n : ℕ, 0 < n ∧ ∀ M : (P).T.obj (-(P).muP t),
      End.of (((P).rpPostDot i t hv Z).total M δ) ^ n = 0 :=
  elvShiftedPostEndEvaluation_dot_pow_zero D Sc' cutoff bound i ΛR
    ((P).muM_postE i hv)
    (elvProbeMixedBase D Sc m cutoff bound ΛP ΛR hP hR i t Z) sy
    (parameterTwist_homogeneous D Sc hc) (SKM.homContentShift D i t.1) δ

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
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) :
    IsNilpotent (probeToReservoirBendCoefficientEvaluation (P) i t Z out[t,δ]
      ((P).rpPostDot i s[i,t] hv[i,t] U[i,t,Z])) := by
  let J := (FR[i,t]) ⋙ out[t,δ]
  let y := (P).rpPostDot i s[i,t] hv[i,t] U[i,t,Z]
  obtain ⟨n, _, hn⟩ := elvProbeMixedPostDot_pow_zero D Sc m cutoff bound ΛP ΛR hP hR
    i s[i,t] hv[i,t] U[i,t,Z] sy hc (blockSucc D ΛR i ((P).muM_postF i t) δ)
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
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) :
    IsNilpotent (reservoirToProbeBendCoefficientEvaluation (P) i t hb hv Z out[t,δ]
      ((P).rpPostDot i s[i,t] hv U[i,t,hb,hv,Z])) := by
  let J := (FP[i,t,hb]) ⋙ out[t,δ]
  let y := (P).rpPostDot i s[i,t] hv U[i,t,hb,hv,Z]
  obtain ⟨n, _, hn⟩ := elvProbeMixedPostDot_pow_zero D Sc m cutoff bound ΛP ΛR hP hR
    i s[i,t] hv U[i,t,hb,hv,Z] sy hc δ
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

private theorem contentBendFactorDot_isIso [Finite I] (i : I) {x y : X} (h : x + D.α i = y) :
    IsIso ((P).T.dot i h) := by
  let _ := Fintype.ofFinite I
  exact (isUnit_iff_isIso _).mp
    (elvProbeReservoir_dot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i h)

/-- The whole-output Dx equation has the literal negative probe windows. -/
def ELVProbeDxContentSeparatedAt [Finite I] (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (δ : WeightBlocks D ΛR ((P).muM t))
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ) : Prop :=
  let _ := contentBendFactorDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i ((P).muP_preE i t)
  ProbeToReservoirSeparatedAt (P) i t Z out[t,δ]
    (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc) N

/-- The whole-output Cx equation retains the normalized shifted cap. -/
def ELVProbeCxContentSeparatedAt [Finite I] (i : I) (t : Sector I)
    (hb : StepValid (false, i) true t) (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (δ : WeightBlocks D ΛR ((P).muM t))
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ) : Prop :=
  let _ := contentBendFactorDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i ((P).muP_preF i hb)
  ReservoirToProbeSeparatedAt (P) i t hb hv Z out[t,δ]
    (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc) N

attribute [local irreducible] elvProbeReservoir elvProbeCrossCoeff

/-- A common output-content length above any minimum works on every input. -/
theorem elvProbe_content_central_separated_windows_above [Finite I]
    (i : I) (t : Sector I) (hb : StepValid (false, i) true t)
    (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (δ : WeightBlocks D ΛR ((P).muM t))
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (minimum : ℕ) :
    ∃ N, minimum ≤ N ∧ ELVProbeDxContentSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t Z δ sy hc N ∧
      ELVProbeCxContentSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t hb hv Z δ sy hc N := by
  let _ := contentBendFactorDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i ((P).muP_preE i t)
  let _ := contentBendFactorDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i ((P).muP_preF i hb)
  obtain ⟨nD, hD⟩ := elvProbeDxContentOuterDot_isNilpotent D Sc m cutoff bound ΛP ΛR hP hR i t Z δ sy hc
  obtain ⟨nC, hC⟩ := elvProbeCxContentOuterDot_isNilpotent D Sc m cutoff bound ΛP ΛR hP hR i t hb hv Z δ sy hc
  let n := max (max nD nC) minimum
  have hDn := pow_eq_zero_of_le
    ((Nat.le_max_left nD nC).trans (Nat.le_max_left (max nD nC) minimum)) hD
  have hCn := pow_eq_zero_of_le
    ((Nat.le_max_right nD nC).trans (Nat.le_max_left (max nD nC) minimum)) hC
  have hminimum : minimum ≤ n := Nat.le_max_right _ _
  rcases parity_eq_zero_or_one (D.parity i) with hi | hi
  · refine ⟨n, hminimum, ?_, ?_⟩
    · exact probeToReservoirBend_even_separated (P) i t Z out[t,δ]
        (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc)
        (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc) hi n hDn
    · exact reservoirToProbeBend_even_separated (P) i t hb hv Z out[t,δ]
        (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc)
        (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc) hi n hCn
  · refine ⟨2*n, (by omega), ?_, ?_⟩
    · exact probeToReservoirBend_odd_separated (P) i t Z out[t,δ]
        (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc)
        (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc) hi n hDn
    · exact reservoirToProbeBend_odd_separated (P) i t hb hv Z out[t,δ]
        (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc)
        (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc) hi n hCn
end OddMath.QuiverHecke
