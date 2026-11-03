import OddMath.QuiverHecke.CyclotomicAction.ELVSourceQuotientComparison
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSupport
import OddMath.QuiverHecke.CyclotomicAction.ELVOldCategory

/-! The literal coefficient and old first-boundary presentation kernels,
including an occupied odd coefficient killed at cutoff zero.
-/
noncomputable section
namespace NonVacuity.ELVSourceQuotientComparison
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars

example : LinearMap.ker (elvHomQuotient D Sc (fun _ => 4) [false, true] [true, false]) =
    ELVCoefficientRelationSpan D Sc (fun _ => 4) [false, true] [true, false] :=
  elvHomQuotient_ker_eq_coefficientRelationSpan D Sc (fun _ => 4) [false, true] [true, false]

example : (ELVRelationSpan D Sc (fun _ => 4) [false, true] [true, false]).map
    (elvQuotientMap D Sc (fun _ => 4) _ _) =
      ideal D Sc (fun _ => 4) [false, true] [true, false] :=
  map_elvRelationSpan_eq_oldIdeal D Sc (fun _ => 4) [false, true] [true, false]

example : LinearMap.ker (sourceToOldHom D Sc (fun _ => 4) [false, true] [true, false]) =
    ELVRelationSpan D Sc (fun _ => 4) [false, true] [true, false] :=
  sourceToOldHom_ker D Sc (fun _ => 4) [false, true] [true, false]

/-- The target is the actual old category Hom, with its existing quotient. -/
example (x : coefficientObj D Sc [false, true] ⟶ coefficientObj D Sc [true, false]) :
    (⟨[false, true]⟩ : OldCategory D Sc (fun _ => 4)) ⟶ ⟨[true, false]⟩ :=
  sourceToOldHom D Sc (fun _ => 4) [false, true] [true, false] x

private def δ : SKM.SYM D ℚ := SKM.SYM.delta D ℚ ⟨false, rfl⟩
private theorem delta_mem_zeroCutoff : δ ∈ SKM.SYM.elvCoefficientIdeal D ℚ (fun _ => 0) := by
  change δ ∈ TwoSidedIdeal.span {a | SKM.SYM.ELVCoefficientRelation D ℚ (fun _ => 0) a}
  apply TwoSidedIdeal.subset_span
  refine Or.inr ⟨⟨false, rfl⟩, by decide, ?_⟩
  change δ = δ * 1
  rw [mul_one]

private def emptyNF : NFIdx ([] : List Bool) [] := by
  have hc : Categorification.TypeA.canWord 0 (1 : Equiv.Perm (Fin 0)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, List.length_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]

private theorem occupied_odd_source : sourceCoefficientHom D Sc δ (𝟙 ((pres D Sc).obj (ob D []))) ≠ 0 := by
  have h := (extensionBasis D Sc [] []).ne_zero
    ((0, {⟨false, rfl⟩}), emptyNF)
  simpa only [extensionBasis_apply, SKM.SYM.coefficientBasis_delta, vacuum_nf D Sc, δ] using h

/-- The kernel comparison includes the real odd top coefficient relation;
the corresponding source tensor is nonzero before taking the quotient. -/
example : sourceCoefficientHom D Sc δ (𝟙 ((pres D Sc).obj (ob D []))) ≠ 0 ∧
    sourceCoefficientHom D Sc δ (𝟙 ((pres D Sc).obj (ob D []))) ∈
      LinearMap.ker (sourceToOldHom D Sc (fun _ => 0) [] []) := by
  refine ⟨occupied_odd_source, ?_⟩
  rw [sourceToOldHom_ker]
  exact elvCoefficientRelationSpan_le D Sc (fun _ => 0) [] []
    (sourceCoefficientHom_mem_coefficientRelationSpan D Sc (fun _ => 0)
      delta_mem_zeroCutoff (𝟙 _))

end NonVacuity.ELVSourceQuotientComparison

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVSourceQuotientComparison
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
