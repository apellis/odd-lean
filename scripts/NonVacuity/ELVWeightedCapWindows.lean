import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedCapWindows
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open BalancedInduction CyclotomicCrossingTensor PowerVacuumCoefficient
namespace NonVacuity.ELVWeightedCapWindows
private theorem occupied_composite
    {k C : Type*} [CommRing k] [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (f : F ⟶ G) (g : G ⟶ F)
    (h : f ≫ g = 𝟙 F) (w : C) (z : F.obj w) (hz : z ≠ 0) :
    g.total w (f.total w z) ≠ 0 := by
  have hc := congrArg (fun a : F ⟶ F => a.total w) h
  rw [Superfunctor.comp_total] at hc
  have hi : (𝟙 F : F ⟶ F).total w = 𝟙 (F.obj w) := by
    simp only [SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one, add_zero]
  rw [hi] at hc
  exact fun he => hz ((congrArg (fun a => a z) hc).symm.trans he)

private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (i : Bool) : ℕ := if i then 6 else 4
private def L (_ : Bool × ℕ) : ℕ := 4
private theorem positive (i : Bool) : 0 < cutoff i := by cases i <;> decide
private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private abbrev WM := weightedVacuum D Sc cutoff L
private abbrev CQ := contentInclusion D Sc cutoff (SKM.SYM.elvPowerWeightBound D cutoff L + 1) (0 : Multiset Bool)
private def deltaClass : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨false, rfl⟩)
private theorem large (i : Bool) : 4 ≤ cutoff i := by cases i <;> decide
private theorem powers_high (a : Bool × ℕ) : 4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega
private theorem delta_ne_zero : deltaClass ≠ 0 := by
  intro hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 1 4 (by decide) large powers_high
  have he := hi (a₁ := ⟨_, SKM.SYM.delta_mem_coefficientAtMost D ℚ ⟨false, rfl⟩⟩) (a₂ := 0)
    (by simpa only [deltaClass, ZeroMemClass.coe_zero, map_zero] using hz)
  have hδ : SKM.SYM.delta D ℚ ⟨false, rfl⟩ ≠ 0 := by
    rw [← SKM.SYM.coefficientBasis_delta]
    exact (SKM.SYM.coefficientBasis D ℚ).ne_zero _
  exact hδ (congrArg Subtype.val he)

/-- The actual finite row extracts the last column and kills the first. -/
example (i : Bool) :
    weightedUnitColumn D Sc cutoff L i (cutoff i - 1) ≫
      weightedCoefficientCap D Sc cutoff i L (positive i) = 𝟙 ((restriction CQ).obj WM) := by
  have h := weightedUnitColumn_cap D Sc cutoff L i (positive i) (cutoff i - 1) (by
    have := positive i; omega)
  rw [ite_eq_left (by have := positive i; omega)] at h
  exact h
example (i : Bool) :
    weightedUnitColumn D Sc cutoff L i 0 ≫
      weightedCoefficientCap D Sc cutoff i L (positive i) = 0 := by
  have h := weightedUnitColumn_cap D Sc cutoff L i (positive i) 0 (positive i)
  rw [ite_eq_right (by have := large i; omega)] at h
  exact h

private theorem top_polynomial :
    weightedUnitColumn D Sc cutoff L true 1 ≫
      weightedPolynomialCap D Sc cutoff L true (positive true) 2 = 𝟙 ((restriction CQ).obj WM) := by
  have h := weightedUnitColumn_polynomialCap D Sc cutoff L true (positive true) 2 1 (by decide)
  rw [ite_eq_left (by decide)] at h
  exact h
example :
    weightedUnitColumn D Sc cutoff L true 0 ≫
      weightedPolynomialCap D Sc cutoff L true (positive true) 2 = 0 := by
  have h := weightedUnitColumn_polynomialCap D Sc cutoff L true (positive true) 2 0 (by decide)
  rw [ite_eq_right (by decide)] at h
  exact h

/-- The entire-module identity is occupied on a surviving odd coefficient;
it is not a zero-module instance of the finite row. -/
example :
    (weightedPolynomialCap D Sc cutoff L true (positive true) 2).total
        (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff (SKM.SYM.elvPowerWeightBound D cutoff L + 1) 0)
      ((weightedUnitColumn D Sc cutoff L true 1).total ⟨⟨[]⟩, rfl⟩
        (weightedEmptyEquiv D Sc cutoff L deltaClass)) ≠ 0 := by
  apply occupied_composite _ _ top_polynomial
  intro hz
  exact delta_ne_zero ((weightedEmptyEquiv D Sc cutoff L).injective (hz.trans (map_zero _).symm))

/-- The same finite window uses the same ordinary unit and endpoint dot. -/
example (i : Bool) (n : ℕ) (hn : n < cutoff i) :
    weightedVacuumUnit D Sc cutoff L i ≫ (weightedVacuumDot D Sc cutoff L i ^ n) ≫
      weightedCoefficientCap D Sc cutoff i L (positive i) =
        if n + 1 = cutoff i then 𝟙 ((restriction CQ).obj WM) else 0 :=
  weightedVacuumUnit_dot_cap_window D Sc cutoff L i (positive i) n hn

/-- The negative-height final low column is identified in the exact dot
powers and ordinary unit needed by the inverse-cap polynomial theorem. -/
example :
    weightedVacuumUnit D Sc cutoff L true ≫ (weightedVacuumDot D Sc cutoff L true ^ 1) ≫
      ((weightedVacuumDot D Sc cutoff L true ^ 2 + 1) ^ 2) ≫
        weightedCoefficientCap D Sc cutoff true L (positive true) = 𝟙 ((restriction CQ).obj WM) := by
  simpa only [weightedUnitColumn_eq_unit_dot, weightedPolynomialCap_eq_dot_cap,
    Category.assoc] using top_polynomial

end NonVacuity.ELVWeightedCapWindows
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedCapWindows
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
