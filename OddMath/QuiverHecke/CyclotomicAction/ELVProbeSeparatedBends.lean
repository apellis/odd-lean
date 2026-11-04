import OddMath.QuiverHecke.CyclotomicAction.ELVProbeFiniteBends
import OddMath.QuiverHecke.SwappedAssembly.Sigma.BendWindowEquations

/-! # Canonical separated ELV mixed-bend windows

`SwappedHomInversion.md` §3 (4)–(6): the chosen crossing coefficient
has the literal negative probe-automorphism and dotted reservoir
window formulas on arbitrary supported Hom objects. Probe inverses
and finite component bounds are supplied by the ELV construction.
The paired result uses a common output window for both central bends.
-/
noncomputable section
set_option quotPrecheck false
open scoped BigOperators
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction SwappedAssembly
universe u
local instance separatedBendHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (m cutoff : I → ℕ) (bound : ℕ) (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local notation "L" "[" t "," M "," δ "]" =>
  elvProbeBendOutputEvaluation D Sc m cutoff bound ΛP ΛR hP hR t M δ
local notation "dFP" "[" i "," t "]" =>
  SKM.homContentPreF (P).T (P).W.obj i ((P).muM t) ((P).muP_preE i t)
local notation "cFP" "[" i "," t "," hb "]" =>
  SKM.homContentPreF (P).T (P).W.obj i ((P).muM t) ((P).muP_preF i hb)

/-- The whole chosen factor dot is invertible before selecting an input
Hom object or a supported output component. -/
theorem elvProbeFactorDot_isIso [Finite I] (i : I) {x y : X} (h : x + D.α i = y) :
    IsIso ((P).T.dot i h) := by
  let := Fintype.ofFinite I
  exact (isUnit_iff_isIso _).mp
    (elvProbeReservoir_dot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i h)

/-- The evaluated XP-to-YR probe automorphism is the prescribed whole
factor dot with its constructed inverse. -/
def elvProbeDxAut [Finite I] (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t)) :=
  let := elvProbeFactorDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i ((P).muP_preE i t)
  Functor.mapAut _ L[t,M,δ]
    (SKM.homPreDotAut (P).T (P).W i ((P).muP_preE i t) ((dFP[i,t]).obj Z))

/-- The evaluated XR-to-YP probe automorphism uses the specified probe
right adjoint, retaining its normalized parity shift. -/
def elvProbeCxAut [Finite I] (i : I) (t : Sector I) (hb : StepValid (false, i) true t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t)) :=
  let := elvProbeFactorDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i ((P).muP_preF i hb)
  Functor.mapAut _ L[t,M,δ] (Functor.mapAut _ (cFP[i,t,hb])
    (SKM.homPreDotAut (P).T (P).W i ((P).muP_preF i hb) Z))

/-- The literal `hDx` finite-window equation at one evaluated output. -/
def ELVProbeDxSeparatedAt [Finite I] (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t))
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ) : Prop :=
  let _ := elvProbeFactorDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i ((P).muP_preE i t)
  ProbeToReservoirSeparatedAt (P) i t Z L[t,M,δ]
    (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc) N

/-- The literal `hCx` finite-window equation, including its two shifts
in the power of the interchange sign. -/
def ELVProbeCxSeparatedAt [Finite I] (i : I) (t : Sector I)
    (hb : StepValid (false, i) true t) (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t))
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ) : Prop :=
  let _ := elvProbeFactorDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i ((P).muP_preF i hb)
  ReservoirToProbeSeparatedAt (P) i t hb hv Z L[t,M,δ]
    (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc) N

/-- The exact chosen Dx bend has the literal separated window equation,
with no inverse, chart, automorphism or bound premise. -/
theorem elvProbeDx_separated_windows [Finite I]
    (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t))
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) :
    ∃ N, ELVProbeDxSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t Z M δ sy hc N := by
  let := elvProbeFactorDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i ((P).muP_preE i t)
  obtain ⟨n, hn⟩ := elvProbeDxOuterDot_isNilpotent D Sc m cutoff bound ΛP ΛR hP hR i t Z M δ sy hc
  have hi : D.parity i = 0 ∨ D.parity i = 1 := by
    generalize D.parity i = p
    fin_cases p <;> simp
  rcases hi with hi | hi
  · refine ⟨n, ?_⟩
    exact probeToReservoirBend_even_separated (C := ContentModules D (parameterTwist D Sc) cutoff bound δ.1) (P) i t Z L[t,M,δ]
        (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc)
        (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc) hi n hn
  · refine ⟨2*n, ?_⟩
    exact probeToReservoirBend_odd_separated (C := ContentModules D (parameterTwist D Sc) cutoff bound δ.1) (P) i t Z L[t,M,δ]
        (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc)
        (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc) hi n hn

/-- The exact chosen Cx bend has the literal separated window equation,
with no inverse, chart, automorphism or bound premise. -/
theorem elvProbeCx_separated_windows [Finite I]
    (i : I) (t : Sector I) (hb : StepValid (false, i) true t)
    (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t))
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) :
    ∃ N, ELVProbeCxSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t hb hv Z M δ sy hc N := by
  let := elvProbeFactorDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i ((P).muP_preF i hb)
  obtain ⟨n, hn⟩ := elvProbeCxOuterDot_isNilpotent D Sc m cutoff bound ΛP ΛR hP hR i t hb hv Z M δ sy hc
  have hi : D.parity i = 0 ∨ D.parity i = 1 := by
    generalize D.parity i = p
    fin_cases p <;> simp
  rcases hi with hi | hi
  · refine ⟨n, ?_⟩
    exact reservoirToProbeBend_even_separated (C := ContentModules D (parameterTwist D Sc) cutoff bound δ.1) (P) i t hb hv Z L[t,M,δ]
        (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc)
        (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc) hi n hn
  · refine ⟨2*n, ?_⟩
    exact reservoirToProbeBend_odd_separated (C := ContentModules D (parameterTwist D Sc) cutoff bound δ.1) (P) i t hb hv Z L[t,M,δ]
        (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc)
        (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc) hi n hn

/-- A common finite output window supplies both literal central-bend
inputs. The exponent is synchronized at this input and output only. -/
theorem elvProbe_central_separated_windows_above [Finite I]
    (i : I) (t : Sector I) (hb : StepValid (false, i) true t)
    (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t))
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (minimum : ℕ) :
    ∃ N, minimum ≤ N ∧ ELVProbeDxSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t Z M δ sy hc N ∧
      ELVProbeCxSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t hb hv Z M δ sy hc N := by
  let := elvProbeFactorDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i ((P).muP_preE i t)
  let := elvProbeFactorDot_isIso D Sc m cutoff bound ΛP ΛR hP hR i ((P).muP_preF i hb)
  obtain ⟨nD, hD⟩ := elvProbeDxOuterDot_isNilpotent D Sc m cutoff bound ΛP ΛR hP hR i t Z M δ sy hc
  obtain ⟨nC, hC⟩ := elvProbeCxOuterDot_isNilpotent D Sc m cutoff bound ΛP ΛR hP hR i t hb hv Z M δ sy hc
  let n := max (max nD nC) minimum
  have hDn := pow_eq_zero_of_le
    ((Nat.le_max_left nD nC).trans (Nat.le_max_left (max nD nC) minimum)) hD
  have hCn := pow_eq_zero_of_le
    ((Nat.le_max_right nD nC).trans (Nat.le_max_left (max nD nC) minimum)) hC
  have hminimum : minimum ≤ n := Nat.le_max_right _ _
  have hi : D.parity i = 0 ∨ D.parity i = 1 := by
    generalize D.parity i = p
    fin_cases p <;> simp
  rcases hi with hi | hi
  · refine ⟨n, hminimum, ?_, ?_⟩
    · exact probeToReservoirBend_even_separated (C := ContentModules D (parameterTwist D Sc) cutoff bound δ.1) (P) i t Z L[t,M,δ]
          (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc)
          (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc) hi n hDn
    · exact reservoirToProbeBend_even_separated (C := ContentModules D (parameterTwist D Sc) cutoff bound δ.1) (P) i t hb hv Z L[t,M,δ]
          (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc)
          (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc) hi n hCn
  · refine ⟨2*n, (by omega), ?_, ?_⟩
    · exact probeToReservoirBend_odd_separated (C := ContentModules D (parameterTwist D Sc) cutoff bound δ.1) (P) i t Z L[t,M,δ]
          (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc)
          (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc) hi n hDn
    · exact reservoirToProbeBend_odd_separated (C := ContentModules D (parameterTwist D Sc) cutoff bound δ.1) (P) i t hb hv Z L[t,M,δ]
          (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc)
          (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc) hi n hCn

/-- The two prescribed central bends admit a common finite output window. -/
theorem elvProbe_central_separated_windows [Finite I]
    (i : I) (t : Sector I) (hb : StepValid (false, i) true t)
    (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t))
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) :
    ∃ N, ELVProbeDxSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t Z M δ sy hc N ∧
      ELVProbeCxSeparatedAt D Sc m cutoff bound ΛP ΛR hP hR i t hb hv Z M δ sy hc N := by
  obtain ⟨N, _, hD, hC⟩ := elvProbe_central_separated_windows_above
    D Sc m cutoff bound ΛP ΛR hP hR i t hb hv Z M δ sy hc 0
  exact ⟨N, hD, hC⟩

end OddMath.QuiverHecke
