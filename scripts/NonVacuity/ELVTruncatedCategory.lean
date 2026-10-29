import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedModuleBound
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDetection
import NonVacuity.ELVHomGrading
import Lean.Util.CollectAxioms

noncomputable section
namespace ELVTruncatedCategoryConsumer
open CategoryTheory StringDiagrams BicategoryStruct OddMath OddMath.QuiverHecke
open ELVOld ELVCoefficientCategoryConsumer ELVCoefficientGradingConsumer ELVHomGradingConsumer
open SwappedAssembly.RegularReservoir

/-- The actual one-strand endomorphism algebra over the rational odd datum. -/
def reservoir : GSuperAlg ℚ :=
  truncatedEndGSuperAlg datum scalars (fun _ => 2) 3 sy homogeneous [()]

example : Linear ℚ (TruncatedCategory datum scalars (fun _ => 2) 3) := inferInstance
example : Supercategory ℚ (TruncatedCategory datum scalars (fun _ => 2) 3) := inferInstance
example : GradedSupercategory ℚ (TruncatedCategory datum scalars (fun _ => 2) 3) :=
  truncatedGradedSupercategory datum scalars (fun _ => 2) 3 sy homogeneous

/-- The carrier is literally the established Hom quotient, not a transported algebra. -/
example : reservoir.carrier = TruncatedOld datum scalars (fun _ => 2) 3 [()] [()] := rfl

example (f g : reservoir.carrier) : f * g = truncatedComp datum scalars (fun _ => 2) 3
    [()] [()] [()] g f := rfl

/-- The old nonzero odd witness survives in this endomorphism algebra. -/
def oddWitness : reservoir.carrier :=
  truncatedSingle datum scalars (fun _ => 2) 3 () delta 0

theorem oddWitness_ne_zero : oddWitness ≠ 0 :=
  truncatedSingle_delta_ne_zero datum scalars rfl

theorem oddWitness_parity : oddWitness ∈ reservoir.grading 1 := by
  change (truncatedIdeal datum scalars (fun _ => 2) 3 [()] [()]).mkQ
    (singleTerm datum scalars (fun _ => 2) ()
      (SKM.SYM.elvCoefficientQuotient datum (fun _ => 2) delta) 0) ∈
    truncatedParity datum scalars (fun _ => 2) 3 [()] [()] 1
  apply Submodule.mem_map_of_mem
  simpa [singleTerm, coefficientIdentity, delta, coefficientObj] using
    coefficientIdentity_basis_parity datum scalars (fun _ => 2) [()] (0, {oddColour})

theorem oddWitness_degree : oddWitness ∈ reservoir.degree 2 := by
  simpa [reservoir, truncatedEndGSuperAlg, truncatedEndDegree, oddWitness, delta,
    SKM.SYM.coefficientDegree, sy] using
    truncatedSingle_basis_degree datum scalars (fun _ => 2) sy homogeneous 3 ()
      (0, {oddColour}) 0

/-- Parity is independent of integer degree modulo two. -/
example : (2 : ZMod 2) = 0 := by decide

example : ∃ K : ℕ, ∀ d : ℤ, (K : ℤ) ≤ d → reservoir.degree d = ⊥ :=
  truncatedEndGSuperAlg_single_bounded datum scalars (fun _ => 2) 3 sy homogeneous ()

example : ∃ K : ℕ, ∀ d : ℤ, (K : ℤ) ≤ d →
    ∀ c : 𝟙 reservoir.toSuperAlg ⟶ 𝟙 reservoir.toSuperAlg,
    c ∈ (coeffGrading reservoir).deg d → c = 0 :=
  truncatedSingle_regular_coefficients_bounded datum scalars (fun _ => 2) 3 sy homogeneous ()

example : ∃ K : ℕ, ∀ d : ℤ, (K : ℤ) ≤ d →
    ∀ c : 𝟙 reservoir.toSuperAlg ⟶ 𝟙 reservoir.toSuperAlg,
    c ∈ (coeffGrading reservoir).deg d → realize reservoir c = 0 :=
  truncatedSingle_module_coefficients_bounded datum scalars (fun _ => 2) 3 sy homogeneous ()

/-- The concrete rational reservoir vanishes in every integer degree at least nine. -/
theorem upperSupport (d : ℤ) (hd : (9 : ℕ) ≤ d) : reservoir.degree d = ⊥ := by
  apply truncatedEndGSuperAlg_single_degree_eq_bot datum scalars (fun _ => 2) 3
    sy homogeneous () 2 (by norm_num)
    (SKM.SYM.coefficientDegree_le_weight_mul datum sy 2 (by intro i; norm_num [sy])) d
  have : (8 : ℤ) < d := by omega
  simpa [sy] using this

example (d : ℤ) (hd : (9 : ℕ) ≤ d)
    (c : 𝟙 reservoir.toSuperAlg ⟶ 𝟙 reservoir.toSuperAlg)
    (hc : c ∈ (coeffGrading reservoir).deg d) : c = 0 :=
  coefficient_eq_zero reservoir 9 upperSupport d hd c hc

example (d : ℤ) (hd : (9 : ℕ) ≤ d)
    (c : 𝟙 reservoir.toSuperAlg ⟶ 𝟙 reservoir.toSuperAlg)
    (hc : c ∈ (coeffGrading reservoir).deg d) : realize reservoir c = 0 :=
  realize_eq_zero_of_high_degree reservoir 9 upperSupport c hc hd

example : Function.Injective (realize reservoir) := realize_injective reservoir

end ELVTruncatedCategoryConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedCategory,
    `OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedModuleBound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if owners.contains modules[idx.toNat]! then
        for ax in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Disallowed axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations audited"
  for name in #[`ELVTruncatedCategoryConsumer.oddWitness_ne_zero,
      `ELVTruncatedCategoryConsumer.oddWitness_parity,
      `ELVTruncatedCategoryConsumer.oddWitness_degree] do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {count} declarations in the truncated category and module-bound modules, plus the three odd witness theorems."
