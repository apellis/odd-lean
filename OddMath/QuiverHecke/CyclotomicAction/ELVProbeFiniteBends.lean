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

end ReservoirToProbe
end OddMath.QuiverHecke
