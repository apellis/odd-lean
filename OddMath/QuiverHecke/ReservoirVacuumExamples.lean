import OddMath.QuiverHecke.ReservoirVacuumDetection

/-! Concrete connected two-odd tests for the algebraic detection inputs.
These tests do not instantiate an unconstructed fused categorical family. -/
noncomputable section
namespace OddMath.QuiverHecke.ReservoirVacuumExamples
open CategoryTheory StringDiagrams
open scoped Classical

def datum : SKM.Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else -2
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else -2)
    split
    · exact ⟨1, by norm_num⟩
    · exact ⟨-1, by norm_num⟩

def params : SKM.Scalars datum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

def i : {i : Bool // datum.parity i = 1} := ⟨false, rfl⟩
def j : {i : Bool // datum.parity i = 1} := ⟨true, rfl⟩

/-- Recovery works in the common coefficient algebra, retaining both odd
colours and their products, and not in a tensor of independent actions. -/
theorem recover_two_odd_series (n : ℕ) :
    SKM.reservoirDeconvolution
      (SKM.reservoirConvolution
        (fun r => SKM.SYM.e datum ℚ false r + SKM.SYM.delta datum ℚ i * SKM.SYM.delta datum ℚ j)
        (fun r => if r = 0 then 1 else SKM.SYM.e datum ℚ true r))
      (fun r => if r = 0 then 1 else SKM.SYM.e datum ℚ true r) n =
        SKM.SYM.e datum ℚ false n + SKM.SYM.delta datum ℚ i * SKM.SYM.delta datum ℚ j :=
  SKM.reservoirDeconvolution_convolution _ _ (by simp) n

/-- The algebraic detector permits different cutoff parity at adjacent odd
colours. The external-weight realization is a separate action obligation. -/
theorem mixed_parity_detect (t t' : List Bool)
    (f : coefficientObj datum params t ⟶ coefficientObj datum params t')
    (hf : ∀ m, (ELVRelationSpan datum params
      (fun b => 2 * m + if b then 1 else 0) t t').mkQ f = 0) : f = 0 :=
  reservoir_parity_cutoffs_detect datum params (fun b => if b then 1 else 0) t t' f hf

/-- At cutoff five the entire two-strand, degree-two joint span survives,
including crossing vectors carrying the product of the two exterior variables. -/
theorem crossing_window_injective :
    Function.Injective (fun x : ExtendedAtMost datum params [false, true] [true, false] 2 =>
      (ELVRelationSpan datum params (fun _ => 5) [false, true] [true, false]).mkQ
        (x : coefficientObj datum params [false, true] ⟶ coefficientObj datum params [true, false])) :=
  elv_quotient_injective_on_extendedAtMost datum params (N := 5) (fun _ => le_rfl) (by decide)

private def crossingIndex : NFIdx [false, true] [true, false] := by
  let w := Categorification.TypeA.wordProd 2 [0]
  refine ⟨([], w), by simp, by simp, ?_⟩
  change SChain [false, true]
    (pl [false, true] (cw (Categorification.TypeA.canWord 2 w))) [true, false]
  have ht := tgt_cw_eq (Categorification.TypeA.validWord_canWord 2 w)
    (show Categorification.TypeA.ValidWord 2 [0] from by simp [Categorification.TypeA.ValidWord])
    (Categorification.TypeA.wordProd_canWord 2 w) (t := [false, true]) rfl
  have hs := sChain_pl [false, true] (cw (Categorification.TypeA.canWord 2 w))
  rw [ht] at hs
  exact hs

private def crossingExteriorIndex : SKM.SYM.CoefficientIndex datum ×
    NFIdx [false, true] [true, false] := ((0, {i, j}), crossingIndex)

/-- A specific nonzero crossing-times-two-exterior vector survives. In
particular the connected crossing window above is not a zero source module. -/
theorem crossing_two_exterior_ne_zero :
    (ELVRelationSpan datum params (fun _ => 5) [false, true] [true, false]).mkQ
      (extensionBasis datum params [false, true] [true, false] crossingExteriorIndex) ≠ 0 := by
  have hm : extensionBasis datum params [false, true] [true, false] crossingExteriorIndex ∈
      ExtendedAtMost datum params [false, true] [true, false] 2 := by
    apply Submodule.subset_span
    refine ⟨crossingExteriorIndex, ?_, rfl⟩
    have hij : i ≠ j := by decide
    simp [extensionDegree, crossingExteriorIndex, crossingIndex, SKM.SYM.coefficientWeight, hij]
  intro hz
  have he := crossing_window_injective (a₁ := ⟨_, hm⟩) (a₂ := 0) (by simpa using hz)
  exact (extensionBasis datum params [false, true] [true, false]).ne_zero crossingExteriorIndex
    (congrArg Subtype.val he)

#print axioms OddMath.SKM.reservoir_coefficients_recovered
#print axioms OddMath.QuiverHecke.ReservoirVacuumEvaluation.observe_coefficient
#print axioms OddMath.QuiverHecke.upward_independence_of_fused_fixed_weight_families
#print axioms crossing_two_exterior_ne_zero

end OddMath.QuiverHecke.ReservoirVacuumExamples
