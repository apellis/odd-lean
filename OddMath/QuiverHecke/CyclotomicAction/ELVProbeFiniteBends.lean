import OddMath.QuiverHecke.CyclotomicAction.ELVProbeBendEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeDenominatorUnits
import OddMath.QuiverHecke.SwappedAssembly.Sigma.FiniteBendEvaluation

/-! # Component bounds in the prescribed ELV mixed bends

`SwappedHomInversion.md` §3 (3)–(6): the same selected crossing
coefficient enters both mixed bends. Its output bounds are constructed
at the source content read by the chosen lowering functor. In
particular, restriction uses the successor reservoir block; probe
precomposition uses the transformed probe input. No bound on a whole
weight fibre is required.
-/
noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction SwappedAssembly
universe u
local instance finiteBendHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (m cutoff : I → ℕ) (bound : ℕ) (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local notation "Sc'" => parameterTwist D Sc

/-- The inner RP dot is a unit before any output evaluation. -/
theorem elvProbeRPPreDot_isUnit [Finite I] (i : I) (t : Sector I)
    (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H
      (nextSector (true, i) true (nextSector (true, i) false t))) :
    IsUnit ((P).rpPreDot i t hv Z) := by
  let F := elvProbeMixedBase D Sc m cutoff bound ΛP ΛR hP hR i t Z
  let α := elvProbeMixedPreDot D Sc m cutoff bound ΛP ΛR hP hR i t Z
  have hu := elvPostProbeDot_isUnit D Sc' cutoff bound i ΛR ((P).muM_postE i hv) F α
    (elvProbeMixedPreDot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i t Z)
  exact hu.map ((SKM.homParityShift (k := k)
    (C := (P).T.obj (-(P).muP t) ⟶ elvWeightSpace D Sc' cutoff bound ΛR ((P).muM t))
    (SKM.homContentShift D i t.1)).mapEnd _)

private theorem evaluated_conjugation_isNilpotent
    {C E : Type*} [Category C] [Preadditive C] [Category E] [Preadditive E]
    (L : C ⥤ E) [L.Additive] {A B : C} (e : A ≅ B) (f : End A)
    (hf : IsNilpotent ((L.mapEnd A) f)) :
    IsNilpotent ((L.mapEnd B) (bendConjugation e f)) := by
  have h := hf.map (bendConjugation (L.mapIso e))
  change IsNilpotent (End.of (L.map e.inv ≫ L.map f ≫ L.map e.hom)) at h
  change IsNilpotent (End.of (L.map (e.inv ≫ f ≫ e.hom)))
  simpa only [Functor.map_comp] using h


/-- Literal output evaluation with the complete factor Hom category as
its declared domain, retaining its chosen preadditive structure. -/
def elvProbeBendOutputEvaluation (t : Sector I)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t)) :
    (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t ⥤
      ContentModules D Sc' cutoff bound δ.1 :=
  homContentEvaluation D Sc' cutoff bound ΛR ((P).muM t)
    ((P).T.obj (-(P).muP t)) M δ

instance elvProbeBendOutputEvaluation_additive (t : Sector I)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t)) :
    (elvProbeBendOutputEvaluation D Sc m cutoff bound ΛP ΛR hP hR t M δ).Additive where
  map_add := by
    intro F G f g
    exact congrArg (fun a => a δ) ((supernaturalTotalLinearMap F G M).map_add f g)

local notation "out" "[" t "," M "," δ "]" =>
  elvProbeBendOutputEvaluation D Sc m cutoff bound ΛP ΛR hP hR t M δ

private theorem probeToReservoirInnerStepValid (i : I) (t : Sector I) :
    StepValid (true, i) false (nextSector (false, i) false t) := by
  simp [StepValid, nextSector]

section ProbeToReservoir
local notation "dFP" "[" i "," t "]" =>
  SKM.homContentPreF (P).T (P).W.obj i ((P).muM t) ((P).muP_preE i t)
local notation "dFR" "[" i "," t "]" =>
  SKM.homContentPostF (P).T.obj (P).W i (Prod.fst t) ((P).muP t) ((P).muM_postF i t)
local notation "ds" "[" i "," t "]" => nextSector (false, i) false t
local notation "dh" "[" i "," t "]" =>
  (probeToReservoirInnerStepValid i t)
local notation "dU" "[" i "," t "," Z "]" =>
  ((congrArg (nextSector (true, i) true) (SPath.next_dnUp_false_false (i := i) t)).symm ▸ (dFP[i,t]).obj Z)
local notation "dφ" "[" i "," t "," Z "," M "," δ "]" =>
  probeToReservoirBendCoefficientEvaluation (P) i t Z (out[t,M,δ])

/-- Both coefficient charts and reservoir restriction preserve the whole
probe unit in the actual XP-to-YR bend. -/
theorem elvProbeDxInnerDot_isUnit [Finite I]
    (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t)) :
    IsUnit (dφ[i,t,Z,M,δ] ((P).rpPreDot i ds[i,t] dh[i,t] dU[i,t,Z])) :=
  (elvProbeRPPreDot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i ds[i,t] dh[i,t] dU[i,t,Z]).map dφ[i,t,Z,M,δ]

/-- The XP-to-YR bend reads a constructed bound at the successor of its
literal output block. The probe input and Hom object are arbitrary. -/
theorem elvProbeDxOuterDot_isNilpotent [Finite I]
    (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t))
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) :
    IsNilpotent (dφ[i,t,Z,M,δ] ((P).rpPostDot i ds[i,t] dh[i,t] dU[i,t,Z])) := by
  let J := (dFR[i,t]) ⋙ out[t,M,δ]
  let y := (P).rpPostDot i ds[i,t] dh[i,t] dU[i,t,Z]
  have hy : IsNilpotent ((J.mapEnd _) y) := by
    change IsNilpotent (End.of (((dFR[i,t]).map y).total M δ))
    exact shiftedPostRestriction_component_isNilpotent D Sc' cutoff bound i ΛR
      ((P).muM_postF i t) ((P).T.obj (-(P).muP t)) ((P).rpObj i i ds[i,t] dh[i,t] dU[i,t,Z]) y
      (SKM.homContentShift D i t.1) M δ
      (elvProbeMixedPostDot_isNilpotent D Sc m cutoff bound ΛP ΛR hP hR i ds[i,t] dh[i,t] dU[i,t,Z] hdot M
        (blockSucc D ΛR i ((P).muM_postF i t) δ))
  exact evaluated_conjugation_isNilpotent J
    ((P).probeToReservoirCoefficientIso i t ((dFP[i,t]).obj Z)) y hy

/-- The chosen coefficient in the actual XP-to-YR bend has a finite
even expansion at this output, with all unit and bound inputs supplied. -/
theorem elvProbeDx_even_expansion [Finite I]
    (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t))
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) (_hi : D.parity i = 0) :
    ProbeToReservoirEvenExpansion (P) i t Z out[t,M,δ]
      (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot) := by
  obtain ⟨n, hn⟩ := elvProbeDxOuterDot_isNilpotent D Sc m cutoff bound ΛP ΛR hP hR
    i t Z M δ hdot
  exact ⟨n, hn, probeToReservoirBend_even_expansion (P) i t Z out[t,M,δ] _
    (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hP hR hdot) _hi
    (elvProbeDxInnerDot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i t Z M δ) n hn⟩

/-- The chosen coefficient in the actual XP-to-YR bend has its finite
ordered odd expansion on arbitrary supported Hom objects. -/
theorem elvProbeDx_odd_expansion [Finite I]
    (i : I) (t : Sector I)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t))
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) (_hi : D.parity i = 1) :
    ProbeToReservoirOddExpansion (P) i t Z out[t,M,δ]
      (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot) := by
  obtain ⟨n, hn⟩ := elvProbeDxOuterDot_isNilpotent D Sc m cutoff bound ΛP ΛR hP hR
    i t Z M δ hdot
  exact ⟨n, hn, probeToReservoirBend_odd_expansion (P) i t Z out[t,M,δ] _
    (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hP hR hdot) _hi
    (elvProbeDxInnerDot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i t Z M δ) n hn⟩

end ProbeToReservoir

section ReservoirToProbe
local notation "cFP" "[" i "," t "," hb "]" =>
  SKM.homContentPreF (P).T (P).W.obj i ((P).muM t) ((P).muP_preF i hb)
local notation "cFR" "[" i "," t "," hv "]" =>
  SKM.homContentPostF (P).T.obj (P).W i (Prod.fst t) ((P).muP t) ((P).muM_postE i hv)
local notation "cs" "[" i "," t "]" => nextSector (false, i) true t
local notation "cU" "[" i "," t "," hb "," hv "," Z "]" =>
  ((congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)).symm ▸ (cFR[i,t,hv]).obj Z)
local notation "cφ" "[" i "," t "," hb "," hv "," Z "," M "," δ "]" =>
  reservoirToProbeBendCoefficientEvaluation (P) i t hb hv Z (out[t,M,δ])

/-- The fixed PR minus is outside this ring evaluation; the evaluated
inner dot remains a unit under its full chart and lowering functor. -/
theorem elvProbeCxInnerDot_isUnit [Finite I]
    (i : I) (t : Sector I) (hb : StepValid (false, i) true t)
    (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t)) :
    IsUnit (cφ[i,t,hb,hv,Z,M,δ] ((P).rpPreDot i cs[i,t] hv cU[i,t,hb,hv,Z])) :=
  (elvProbeRPPreDot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i cs[i,t] hv cU[i,t,hb,hv,Z]).map cφ[i,t,hb,hv,Z,M,δ]

/-- The XR-to-YP coefficient has a constructed bound at the transformed
probe input and the same reservoir output block. -/
theorem elvProbeCxOuterDot_isNilpotent [Finite I]
    (i : I) (t : Sector I) (hb : StepValid (false, i) true t)
    (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t))
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) :
    IsNilpotent (cφ[i,t,hb,hv,Z,M,δ] ((P).rpPostDot i cs[i,t] hv cU[i,t,hb,hv,Z])) := by
  let J := (cFP[i,t,hb]) ⋙ out[t,M,δ]
  let y := (P).rpPostDot i cs[i,t] hv cU[i,t,hb,hv,Z]
  have hy : IsNilpotent ((J.mapEnd _) y) := by
    change IsNilpotent (End.of (((cFP[i,t,hb]).map y).total M δ))
    exact shiftedPrecomposition_component_isNilpotent D Sc' cutoff bound ΛR ((P).muM t)
      ((P).T.obj (-(P).muP cs[i,t])) ((P).T.obj (-(P).muP t))
      ((P).T.F i ((P).muP_preF i hb))
      (SKM.leftAdjParity D i (-((P).muP cs[i,t]))) ((P).rpObj i i cs[i,t] hv cU[i,t,hb,hv,Z]) y M δ
      (elvProbeMixedPostDot_isNilpotent D Sc m cutoff bound ΛP ΛR hP hR i cs[i,t] hv cU[i,t,hb,hv,Z] hdot
        (((P).T.F i ((P).muP_preF i hb)).obj M) δ)
  exact evaluated_conjugation_isNilpotent J
    ((P).reservoirToProbeCoefficientChart i t hb hv ((cFR[i,t,hv]).obj Z)) y hy

/-- The chosen coefficient in the actual XR-to-YP bend has a finite
even expansion with its prescribed negative conjugation. -/
theorem elvProbeCx_even_expansion [Finite I]
    (i : I) (t : Sector I) (hb : StepValid (false, i) true t)
    (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t))
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) (_hi : D.parity i = 0) :
    ReservoirToProbeEvenExpansion (P) i t hb hv Z out[t,M,δ]
      (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot) := by
  obtain ⟨n, hn⟩ := elvProbeCxOuterDot_isNilpotent D Sc m cutoff bound ΛP ΛR hP hR
    i t hb hv Z M δ hdot
  exact ⟨n, hn, reservoirToProbeBend_even_expansion (P) i t hb hv Z out[t,M,δ] _
    (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hP hR hdot) _hi
    (elvProbeCxInnerDot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i t hb hv Z M δ) n hn⟩

/-- The actual XR-to-YP bend retains both the ordered odd series and
the outer PR minus, with a componentwise constructed finite bound. -/
theorem elvProbeCx_odd_expansion [Finite I]
    (i : I) (t : Sector I) (hb : StepValid (false, i) true t)
    (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H t)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t))
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) (_hi : D.parity i = 1) :
    ReservoirToProbeOddExpansion (P) i t hb hv Z out[t,M,δ]
      (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot) := by
  obtain ⟨n, hn⟩ := elvProbeCxOuterDot_isNilpotent D Sc m cutoff bound ΛP ΛR hP hR
    i t hb hv Z M δ hdot
  exact ⟨n, hn, reservoirToProbeBend_odd_expansion (P) i t hb hv Z out[t,M,δ] _
    (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hP hR hdot) _hi
    (elvProbeCxInnerDot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i t hb hv Z M δ) n hn⟩

end ReservoirToProbe
end OddMath.QuiverHecke
