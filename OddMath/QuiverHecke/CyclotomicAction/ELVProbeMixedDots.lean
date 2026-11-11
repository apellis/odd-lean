import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierData
import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedCoefficientEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ParameterTwistPureNilpotent

/-! # The two dots on the OLD-probe and ELV-reservoir Hom summand

SwappedActionAssembly F2–F3: prewhisker the prescribed unit probe dot,
then apply the actual shifted ELV postcomposition. This uses only the
checked generator data, before packaging the full factor pair. Both
mixed denominators are constructed without a whole-weight nilpotence bound.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u
local instance mixedDotsHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private theorem mixedProbeStep {I X : Type u} [AddCommGroup X]
    (D : SKM.Datum I X) (Λ : X) (β : I →₀ ℕ) (i : I) :
    -(Λ - SwappedAssembly.contentWeight D β) + D.α i =
      -(Λ - SwappedAssembly.contentWeight D (β + Finsupp.single i 1)) := by
  rw [SwappedAssembly.contentWeight_add_single]
  abel

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ) (ΛP ΛR : X)
  (i : I) (β : I →₀ ℕ) {x y : X} (h : x + D.α i = y)
variable (Z : probeOldWeightSpace D (parameterTwist D Sc) m ΛP
    (-(ΛP - SwappedAssembly.contentWeight D (β + Finsupp.single i 1))) ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR x)
local notation "Sc'" => parameterTwist D Sc
local notation "w" γ => -(ΛP - SwappedAssembly.contentWeight D γ)

/-- The actual probe raising functor precomposed with the input Hom object. -/
abbrev probeELVMixedBase : probeOldWeightSpace D Sc' m ΛP (w β) ⟶
    elvWeightSpace D Sc' cutoff bound ΛR x := probeOldE D Sc' m i ΛP (mixedProbeStep D ΛP β i) ≫ Z
local notation "F" => probeELVMixedBase (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound) (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := β) (Z := Z)

/-- The original whole probe dot, with its independently chosen input Hom object. -/
abbrev probeELVMixedPreDot : End F :=
  probeOldActionDot D Sc' m i ΛP (mixedProbeStep D ΛP β i) ▷ Z
local notation "α" => probeELVMixedPreDot (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound) (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := β) (Z := Z)

theorem probeELVMixedPreDot_mem : α ∈ parity (R := k) _ _ (D.parity i) :=
  TwoSupercategory.whiskerRight_mem Z (probeOldActionDot_mem D Sc' m i ΛP (mixedProbeStep D ΛP β i))

/-- The known probe dot unit survives arbitrary Hom precomposition. -/
theorem probeELVMixedPreDot_isUnit [Fact Sc.PureNilpotent] [Finite I] : IsUnit α := by
  let _ := Fintype.ofFinite I
  exact (probeOldActionDot_isUnit D Sc' m i ΛP (mixedProbeStep D ΛP β i)).map
    ((SKM.homPost (k := k) Z).mapEnd (probeOldE D Sc' m i ΛP (mixedProbeStep D ΛP β i)))

/-- The postinduced actual probe map with the specified content parity shift. -/
abbrev probeELVMixedInnerDot (κ : ZMod 2) :=
  elvShiftedPostEnd D Sc' cutoff bound i ΛR h F
    (elvPostProbeDot D Sc' cutoff bound i ΛR h F α) κ

/-- The actual full-ELV postdot with precisely the same content shift. -/
abbrev probeELVMixedOuterDot (κ : ZMod 2) :=
  elvShiftedPostDot D Sc' cutoff bound i ΛR h F κ

/-- The even difference denominator on the literal generator Hom object is a unit. -/
theorem probeELVMixed_difference_isUnit [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (κ : ZMod 2) (hi : D.parity i = 0) :
    IsUnit (probeELVMixedOuterDot D Sc m cutoff bound ΛP ΛR i β h Z κ -
      probeELVMixedInnerDot D Sc m cutoff bound ΛP ΛR i β h Z κ) :=
  have : Fact Sc.PureNilpotent := ⟨hc.noPure.pureNilpotent⟩
  elvShiftedPostProbe_difference_isUnit D Sc' cutoff bound i ΛR h F sy
    (parameterTwist_homogeneous D Sc hc) κ hi α
    (hi ▸ probeELVMixedPreDot_mem (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound) (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := β) (Z := Z))
    (probeELVMixedPreDot_isUnit (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound) (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := β) (Z := Z))

/-- The odd square-difference denominator is also constructed on this same Hom object. -/
theorem probeELVMixed_square_difference_isUnit [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (κ : ZMod 2) (hi : D.parity i = 1) :
    IsUnit (probeELVMixedInnerDot D Sc m cutoff bound ΛP ΛR i β h Z κ ^ 2 -
      probeELVMixedOuterDot D Sc m cutoff bound ΛP ΛR i β h Z κ ^ 2) :=
  have : Fact Sc.PureNilpotent := ⟨hc.noPure.pureNilpotent⟩
  elvShiftedPostProbe_square_difference_isUnit D Sc' cutoff bound i ΛR h F sy
    (parameterTwist_homogeneous D Sc hc) κ hi α
    (hi ▸ probeELVMixedPreDot_mem (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound) (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := β) (Z := Z))
    (probeELVMixedPreDot_isUnit (D := D) (Sc := Sc) (m := m) (cutoff := cutoff) (bound := bound) (ΛP := ΛP) (ΛR := ΛR) (i := i) (β := β) (Z := Z))

end OddMath.QuiverHecke
