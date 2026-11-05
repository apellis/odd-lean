import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReservoir
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMixedDots
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.CrossCoeff

/-! # Mixed denominator units for the OLD probe and ELV reservoir

SwappedActionAssembly F2–F3 and (A6): identify the actual mixed RP dots
with the prescribed shifted ELV dots, then construct their denominator
units from the whole probe-dot unit and component reservoir bounds.
The constructed coefficient is supernatural by its inverse identities
and these denominator units. No global reservoir nilpotence exponent
is assumed.
-/
noncomputable section
open scoped Classical BigOperators
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction SwappedAssembly
universe u
local instance probeDenominatorHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ) (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR

section Mixed
variable (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
  (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H
    (nextSector (true, i) true (nextSector (true, i) false t)))
local notation "tR" => nextSector (true, i) false t
local notation "h" => ProbeReservoir.muM_postE (P) i hv
local notation "κ" => SKM.homContentShift D i (Prod.fst t)

/-- The literal probe-precomposition Hom object before reservoir induction. -/
abbrev elvProbeMixedBase : (P).T.obj (-(P).muP tR) ⟶
    elvWeightSpace D Sc' cutoff bound ΛR ((P).muM tR) := ((P).step (true, i) true tR (by trivial)).obj Z
local notation "F" => elvProbeMixedBase D Sc m cutoff bound ΛP ΛR hP hR i t Z

/-- The actual chosen probe dot, whiskered by the input Hom object. -/
abbrev elvProbeMixedPreDot : End F := (P).T.dot i ((P).muP_preE i tR) ▷ Z
local notation "α" => elvProbeMixedPreDot D Sc m cutoff bound ΛP ΛR hP hR i t Z

/-- Total evaluation of the literal mixed carrier at one input and reservoir block. -/
def elvProbeMixedEndEvaluation (M : (P).T.obj (-(P).muP t))
    (δ : WeightBlocks D ΛR ((P).muM t)) :
    End ((P).rpObj i i t hv Z) →ₐ[k] End ((((P).rpObj i i t hv Z).obj M) δ) :=
  elvShiftedPostEndEvaluation D Sc' cutoff bound i ΛR h F κ M δ

/-- The selected outer dot has a constructed bound at this component. -/
theorem elvProbeMixedPostDot_isNilpotent [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t)) :
    IsNilpotent (elvProbeMixedEndEvaluation D Sc m cutoff bound ΛP ΛR hP hR i t hv Z M δ
      ((P).rpPostDot i t hv Z)) :=
  elvShiftedPostEndEvaluation_dot_isNilpotent D Sc' cutoff bound i ΛR h F sy
    (parameterTwist_homogeneous D Sc hc) κ M δ

end Mixed

/-- Both mixed denominators are units on the specified complete factor pair. -/
theorem elvProbeCrossDenominatorUnits [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) : (P).CrossDenominatorUnits where
  even i hi t hv Z := by
    change IsUnit (probeELVMixedOuterDot (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound)
      (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := t.1) (h := (P).muM_postE i hv) (Z := Z) (SKM.homContentShift D i t.1) -
      probeELVMixedInnerDot (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound)
      (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := t.1) (h := (P).muM_postE i hv) (Z := Z) (SKM.homContentShift D i t.1))
    exact probeELVMixed_difference_isUnit (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound)
      (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := t.1) (h := (P).muM_postE i hv) (Z := Z) sy hc (SKM.homContentShift D i t.1) hi
  odd i hi t hv Z := by
    change IsUnit (probeELVMixedInnerDot (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound)
      (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := t.1) (h := (P).muM_postE i hv) (Z := Z) (SKM.homContentShift D i t.1) ^ 2 -
      probeELVMixedOuterDot (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound)
      (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := t.1) (h := (P).muM_postE i hv) (Z := Z) (SKM.homContentShift D i t.1) ^ 2)
    exact probeELVMixed_square_difference_isUnit (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound)
      (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := t.1) (h := (P).muM_postE i hv) (Z := Z) sy hc (SKM.homContentShift D i t.1) hi

/-- The actual coefficient chosen from the constructed mixed denominator units. -/
def elvProbeCrossCoeff [Finite I] (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) : (P).CrossCoeff Sc :=
  (P).crossCoeffOfDenominatorUnits (elvProbeCrossDenominatorUnits D Sc m cutoff bound ΛP ΛR hP hR sy hc)

/-- The chosen coefficient has both prescribed even and odd inverse identities. -/
theorem elvProbeCrossCoeff_isInverse [Finite I] (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) :
    (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc).IsInverse :=
  (P).crossCoeffOfDenominatorUnits_isInverse _

/-- The constructed crossing coefficient is supernatural at its prescribed parity. -/
theorem elvProbeCrossCoeff_isSupernatural [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) :
    (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc).IsSupernatural :=
  ProbeReservoir.CrossCoeff.isSupernatural_of_isInverse (P)
    (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc)
    (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc)
    (elvProbeCrossDenominatorUnits D Sc m cutoff bound ΛP ΛR hP hR sy hc)

end OddMath.QuiverHecke
