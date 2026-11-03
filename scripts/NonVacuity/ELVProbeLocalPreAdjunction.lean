import OddMath.QuiverHecke.CyclotomicAction.ELVProbeLocalPreAdjunction
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.ProbeVacuumCap
namespace NonVacuity.ELVProbeLocalPreAdjunction
private theorem compared_ne_zero {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {S T V : C} (e : T ≅ S) (f : S ⟶ V) (hf : f ≠ 0) : e.hom ≫ f ≠ 0 := by
  intro h
  apply hf
  exact (cancel_epi e.hom).mp (h.trans (Limits.comp_zero).symm)
private theorem pi_map_ne_zero {k C : Type*} [CommRing k] [Category* C]
    [Preadditive C] [Linear k C] [Supercategory k C] [PiSupercategory k C]
    {X Y : C} (f : X ⟶ Y) (hf : f ≠ 0) : (PiSupercategory.pi (R := k)).map f ≠ 0 := by
  intro hz
  have hn := PiSupercategory.ζ_naturality (R := k) f
  rw [hz, Limits.zero_comp] at hn
  have ht : twist k 1 f = 0 :=
    (cancel_epi (PiSupercategory.ζ (R := k) X).hom).mp (hn.symm.trans (Limits.comp_zero).symm)
  have hh := congrArg (twist k 1) ht
  rw [twist_twist, map_zero] at hh
  exact hf hh
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private abbrev R := modulePiCategory D Sc m
private instance probeLocalConsumerPi : PiSupercategory ℚ R := R.pi
private abbrev H : R ⟶ R := PiSCat.piHom R
private abbrev N := probeOldVacuumRegular D Sc m

private theorem cap_map_ne_zero (i : Bool) : H.map (cap D Sc m i (positive i)) ≠ 0 := by
  change (PiSupercategory.pi (R := ℚ) (C := R)).map (cap D Sc m i (positive i)) ≠ 0
  exact pi_map_ne_zero _ (cap_ne_zero D Sc m i (positive i))

/-- Independently of supplied local records, the prescribed component is
nonzero at both occupied asymmetric odd probes. -/
example (i : Bool) : shiftedPreCap D Sc m R i (positive i) H ≠ 0 := by
  rw [shiftedPreCap_eq]
  exact compared_ne_zero _ _ (cap_map_ne_zero i)

section Local
variable (i : Bool)
  {A : PiSCat.{0,0,1} ℚ}
  {E₀ : A ⟶ modulePiCategory D Sc m} {F₀ : modulePiCategory D Sc m ⟶ A}
  (A₀ : SKM.SuperAdjunction (k := ℚ) E₀ F₀) (x₀ : End E₀)
  (t : End (E₀ ≫ inductionCell D Sc m i))
  (L : SKM.SuperRouquierLoc A₀ (appendRightAdjunction D Sc m i)
    x₀ (inductionDotCell D Sc m i) t (D.parity i) (-((probeCutoff D m i : ℕ) : ℤ)))

section Adjacent
variable {Z : PiSCat.{0,0,1} ℚ}
  {E₃ : raisedModulePiCategory D Sc m i ⟶ Z} {F₃ : Z ⟶ raisedModulePiCategory D Sc m i}
  (A₃ : SKM.SuperAdjunction (k := ℚ) E₃ F₃) (x₃ : End E₃)
  (t' : End (inductionCell D Sc m i ≫ E₃))
  (U : SKM.SuperRouquierLoc (appendRightAdjunction D Sc m i) A₃
    (inductionDotCell D Sc m i) x₃ t' (D.parity i) (-((probeCutoff D m i : ℕ) : ℤ) + 2))
  (hsq : t ≫ t = 0) (hsq' : t' ≫ t' = 0)
  (hB : E₀ ◁ t' ≫ ((associator E₀ (inductionCell D Sc m i) E₃).inv ≫ t ▷ E₃ ≫
      (associator E₀ (inductionCell D Sc m i) E₃).hom) ≫ E₀ ◁ t' =
    ((associator E₀ (inductionCell D Sc m i) E₃).inv ≫ t ▷ E₃ ≫
      (associator E₀ (inductionCell D Sc m i) E₃).hom) ≫ E₀ ◁ t' ≫
      ((associator E₀ (inductionCell D Sc m i) E₃).inv ≫ t ▷ E₃ ≫
        (associator E₀ (inductionCell D Sc m i) E₃).hom))



/-- The adjacent local records are supplied input data. Their triangles
are constructed by c21; no additional left-adjunction or cap premise is used. -/
example :
    ((localPreAdjunction D Sc m i A₀ x₀ t L A₃ x₃ t' U (positive i) hsq hsq' hB R).counit.app H).total N =
      shiftedPreCap D Sc m R i (positive i) H :=
  localPreAdjunction_counit_total D Sc m i A₀ x₀ t L A₃ x₃ t' U (positive i) hsq hsq' hB R H

/-- Hence the constructed adjunction's evaluated counit cannot be zero
on this native parity-shift Hom object. -/
example :
    ((localPreAdjunction D Sc m i A₀ x₀ t L A₃ x₃ t' U (positive i) hsq hsq' hB R).counit.app H).total N ≠ 0 := by
  rw [localPreAdjunction_counit_total, shiftedPreCap_eq]
  exact compared_ne_zero _ _ (cap_map_ne_zero i)
end Adjacent
end Local
end NonVacuity.ELVProbeLocalPreAdjunction
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.SKM.RouquierPreAdjunction,
      `OddMath.QuiverHecke.CyclotomicAction.ELVProbeLocalPreAdjunction] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module: {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
