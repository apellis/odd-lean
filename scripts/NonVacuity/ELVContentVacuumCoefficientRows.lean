import OddMath.QuiverHecke.CyclotomicAction.ELVContentVacuumCoefficientRows
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerCoefficients
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.SKM.BubbleSubstitution
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open BalancedInduction CyclotomicCrossingTensor PowerVacuumCoefficient
namespace NonVacuity.ELVContentVacuumCoefficientRows
private theorem module_id_ne_zero
    {C : Type*} [Category* C] [Preadditive C] [Linear ℚ C] [Supercategory ℚ C]
    (M : Superfunctor ℚ C (SVec ℚ)) (w : C) (z : M.obj w) (hz : z ≠ 0) : (𝟙 M : M ⟶ M) ≠ 0 := by
  intro h
  have hh := congrArg (fun f : M ⟶ M => f.total w z) h
  simp only [SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one,
    Superfunctor.zero_app, add_zero] at hh
  change z = 0 at hh
  exact hz hh
private theorem row_ne_zero {C : Type*} [Category* C] [Preadditive C]
    {A B : C} (g : A ⟶ B) (r : B ⟶ A) (hr : g ≫ r = 𝟙 A)
    (hid : (𝟙 A : A ⟶ A) ≠ 0) : r ≠ 0 := by
  intro h
  rw [h, Limits.comp_zero] at hr
  exact hid hr.symm
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (i : Bool) : ℕ := if i then 5 else 4
private def L (_ : Bool × ℕ) : ℕ := 4
private abbrev bound := SKM.SYM.elvPowerWeightBound D cutoff L + 1
private abbrev W : ContentModules D Sc cutoff bound 0 :=
  (restriction (contentInclusion D Sc cutoff bound 0)).obj (weightedVacuum D Sc cutoff L)
private abbrev star : ContentCategory D Sc cutoff bound 0 := ⟨⟨[]⟩, rfl⟩
private theorem large (i : Bool) : 4 ≤ cutoff i := by cases i <;> decide
private theorem powers_high (a : Bool × ℕ) : 4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega
private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private def deltaClass : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨false, rfl⟩)
private theorem delta_ne_zero : deltaClass ≠ 0 := by
  intro hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 1 4 (by decide) large powers_high
  have he := hi (a₁ := ⟨_, SKM.SYM.delta_mem_coefficientAtMost D ℚ ⟨false, rfl⟩⟩) (a₂ := 0)
    (by simpa only [deltaClass, ZeroMemClass.coe_zero, map_zero] using hz)
  have hδ : SKM.SYM.delta D ℚ ⟨false, rfl⟩ ≠ 0 := by
    rw [← SKM.SYM.coefficientBasis_delta]
    exact (SKM.SYM.coefficientBasis D ℚ).ne_zero _
  exact hδ (congrArg Subtype.val he)
private def occupied : W.obj star := weightedEmptyEquiv D Sc cutoff L deltaClass
private theorem occupied_ne_zero : occupied ≠ 0 := by
  intro hz
  exact delta_ne_zero ((weightedEmptyEquiv D Sc cutoff L).injective (hz.trans (map_zero _).symm))
private theorem height (i : Bool) : 0 ≤ contentCrossingHeight D cutoff i (0 : Multiset Bool) := by
  simp only [contentCrossingHeight, Multiset.map_zero, Multiset.sum_zero, sub_zero]
  omega
private def top (i : Bool) : Fin (contentUnitCount D cutoff i (0 : Multiset Bool)) :=
  ⟨cutoff i - 1, by simp only [contentUnitCount, contentCrossingHeight, Multiset.map_zero, Multiset.sum_zero, sub_zero, Int.toNat_natCast]; have := large i; omega⟩
private abbrev K (i : Bool) := contentAppendTo D Sc cutoff bound (0 : Multiset Bool) [i]
  (0 + ([i] : Multiset Bool)) (contentBlockCanonicalSum 0 [i])
private abbrev dot (i : Bool) := contentBlockMatrixDot_supernatural D Sc cutoff bound 0 i
private def inverse (i : Bool) := Classical.choice
  (contentAbsentUnitInverse_nonempty D Sc cutoff bound 0 i (by simp) W)

/-- The two odd colours include even and odd reservoir cutoffs. Both
prescribed native rows are exactly rows of the proved boundary inverse. -/
example (i : Bool) : contentVacuumCoefficientMap D Sc cutoff bound i W (height i) (top i) =
    (inverse i).g' (cutoff i - 1) :=
  contentVacuumCoefficientMap_eq_inverseRow D Sc cutoff bound i W (height i) (top i) (inverse i)

example (i : Bool) : contentVacuumCoefficientMap D Sc cutoff bound i W (height i) (top i) ≠ 0 := by
  apply row_ne_zero (unitDotColumn (K i) (dot i) W (cutoff i - 1))
  · exact (contentVacuumCoefficientMap_unitDotColumn D Sc cutoff bound i W (height i)
      (top i) (cutoff i - 1) (top i).isLt).trans (ite_eq_left rfl)
  · exact module_id_ne_zero W star occupied occupied_ne_zero

/-- Every column, on all coefficient vectors, has the same Kronecker window;
there is no scalar-only or top-degree-only extractor assumption. -/
example (i : Bool) (r : Fin (contentUnitCount D cutoff i (0 : Multiset Bool)))
    (a : ℕ) (ha : a < contentUnitCount D cutoff i (0 : Multiset Bool)) :
    unitDotColumn (K i) (dot i) W a ≫ contentVacuumCoefficientMap D Sc cutoff bound i W (height i) r =
      if a = r.val then 𝟙 W else 0 :=
  contentVacuumCoefficientMap_unitDotColumn D Sc cutoff bound i W (height i) r a ha
end NonVacuity.ELVContentVacuumCoefficientRows
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentVacuumCoefficientRows
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
