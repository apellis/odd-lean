import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReservoir
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMixedDots
import OddMath.QuiverHecke.SwappedAssembly.Generators.CrossCoeffExistence

/-! # Mixed denominator units for the OLD probe and ELV reservoir

SwappedActionAssembly F2–F3 and (A6): identify the actual mixed RP dots
with the prescribed shifted ELV dots, then construct their denominator
units from the whole probe-dot unit and component reservoir bounds.
No global reservoir nilpotence exponent is assumed.
-/
noncomputable section
open scoped Classical
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
  (Z : (P).H (nextSector (true, i) true (nextSector (true, i) false t)))
local notation "tR" => nextSector (true, i) false t
local notation "h" => (P).muM_postE i hv
local notation "κ" => SKM.homContentShift D i t.1

/-- The literal probe-precomposition Hom object before reservoir induction. -/
abbrev elvProbeMixedBase := ((P).step (true, i) true tR (by trivial)).obj Z
local notation "F" => elvProbeMixedBase D Sc m cutoff bound ΛP ΛR hP hR i t Z

/-- The actual chosen probe dot, whiskered by the input Hom object. -/
abbrev elvProbeMixedPreDot : End F := (P).T.dot i ((P).muP_preE i tR) ▷ Z
local notation "α" => elvProbeMixedPreDot D Sc m cutoff bound ΛP ΛR hP hR i t Z

/-- The RP carrier is the prescribed shifted native ELV induction. -/
theorem elvProbe_rpObj :
    (P).rpObj i i t hv Z = elvShiftedPostInduction D Sc' cutoff bound i ΛR h F κ := rfl

/-- The inner probe dot uses that same shift, including its action on odd maps. -/
theorem elvProbe_rpPreDot :
    (P).rpPreDot i t hv Z = elvShiftedPostEnd D Sc' cutoff bound i ΛR h F
      (elvPostProbeDot D Sc' cutoff bound i ΛR h F α) κ := rfl

/-- The outer reservoir dot is the literal chosen shifted postdot. -/
theorem elvProbe_rpPostDot :
    (P).rpPostDot i t hv Z = elvShiftedPostDot D Sc' cutoff bound i ΛR h F κ := rfl

/-- The native prewhiskered map has the chosen colour parity. -/
theorem elvProbeMixedPreDot_mem : α ∈ parity (R := k) _ _ (D.parity i) :=
  probeELVMixedPreDot_mem (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound)
    (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := t.1) (Z := Z)

/-- The actual whole probe unit is the generator-level native unit. -/
theorem elvProbeMixedPreDot_isUnit [Finite I] : IsUnit α :=
  probeELVMixedPreDot_isUnit (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound)
    (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := t.1) (Z := Z)

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

/-- The selected inner dot remains a unit at the same component. -/
theorem elvProbeMixedInnerDot_isUnit [Finite I]
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t)) :
    IsUnit (elvProbeMixedEndEvaluation D Sc m cutoff bound ΛP ΛR hP hR i t hv Z M δ
      ((P).rpPreDot i t hv Z)) :=
  elvShiftedPostEndEvaluation_probe_isUnit D Sc' cutoff bound i ΛR h F α
    (elvProbeMixedPreDot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i t Z) κ M δ

/-- The actual mixed coefficient inverse identity determines its even expansion
at the component's constructed reservoir bound. -/
theorem elvProbeMixedCoefficient_even_expansion [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (c : (P).CrossCoeff Sc) (hInv : c.IsInverse) (hi : D.parity i = 0)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t)) :
    let φ := elvProbeMixedEndEvaluation D Sc m cutoff bound ΛP ΛR hP hR i t hv Z M δ
    ∃ n : ℕ, φ ((P).rpPostDot i t hv Z) ^ n = 0 ∧
      φ (c.a i t hv Z) = -∑ r ∈ Finset.range n,
        Ring.inverse (φ ((P).rpPreDot i t hv Z)) ^ (r + 1) * φ ((P).rpPostDot i t hv Z) ^ r := by
  dsimp only
  let φ := elvProbeMixedEndEvaluation D Sc m cutoff bound ΛP ΛR hP hR i t hv Z M δ
  obtain ⟨n, hn⟩ := elvProbeMixedPostDot_isNilpotent D Sc m cutoff bound ΛP ΛR hP hR i t hv Z sy hc M δ
  exact ⟨n, hn, (P).crossCoeff_even_evaluate c i t hv Z φ.toRingHom hInv hi
    (elvProbeMixedInnerDot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i t hv Z M δ) n hn⟩

end Mixed

/-- Both mixed denominators are units on the specified complete factor pair. -/
def elvProbeCrossDenominatorUnits [Finite I]
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

end OddMath.QuiverHecke
