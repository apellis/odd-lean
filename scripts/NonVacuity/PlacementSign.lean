import OddMath.QuiverHecke.PlacementSign
import OddMath.SKM.MixedCrossingLocalExamples
import Lean.Util.CollectAxioms

noncomputable section
open OddMath.QuiverHecke OddMath.SKM OddMath.SKM.MixedCrossingLocalExamples
open scoped Classical

private def params : Scalars oddDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

private def i : {i : Bool // oddDatum.parity i = 1} := ⟨false, rfl⟩

private theorem canWord_one : Categorification.TypeA.canWord 1 1 = [] := by
  apply List.length_eq_zero_iff.mp
  rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]

/-- One dot on a single odd strand. -/
private def dotIndex : NFIdx [false] [false] :=
  ⟨([0], 1), by simp, by simp, by
    simp only [List.length_singleton, canWord_one, List.reverse_nil, cw, List.map_cons, List.map_nil,
      pl, List.append_nil]
    exact PG.sChain_ld (I := Bool) (PG.dot 0) [false]⟩

private theorem dotIndex_par : dotIndex.par oddDatum = 1 := by
  simp [NFIdx.par, NFIdx.gens, dotIndex, canWord_one, cw, pl, PG.ld,
    OddMath.QuiverHecke.Shape.parity, oddDatum]

/-- An odd coefficient against an odd dot: the placement sign is `-1`. -/
example : placementSign oddDatum params [false] [false]
      (sourceCoefficientHom oddDatum params (SYM.coefficientBasis oddDatum ℚ (0, {i}))
        dotIndex.nf) =
    -sourceCoefficientHom oddDatum params (SYM.coefficientBasis oddDatum ℚ (0, {i}))
        dotIndex.nf := by
  rw [placementSign_sourceCoefficientHom, dotIndex_par]
  simp

/-- The placement sign is a valid placement for a swapped vacuum evaluation. -/
example (d : ℕ) : ∀ x ∈ ExtendedAtMost oddDatum params [false] [false] d,
    placementSign oddDatum params [false] [false] x ∈
      ExtendedAtMost oddDatum params [false] [false] d :=
  fun _ hx => placementSign_mem_extendedAtMost oddDatum params hx

#print axioms placementSign_sourceCoefficientHom
#print axioms placementSign_mem_extendedAtMost

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.PlacementSign then
      for name in env.header.moduleData[i]!.constNames do
        for axiomName in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations found"
  logInfo m!"Audited {count} owned declarations: standard axioms only"
