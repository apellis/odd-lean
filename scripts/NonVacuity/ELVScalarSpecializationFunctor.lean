import OddMath.QuiverHecke.CyclotomicAction.ELVScalarSpecializationFunctor
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.SKM.SYM
namespace ELVScalarHomConsumer

private def D : SKM.Datum Unit ℤ where
  cd :=
    { root := fun _ => 2
      coroot := fun _ => LinearMap.id
      coroot_root_self := fun _ => rfl }
  isGCM :=
    { diag := fun _ => rfl
      offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
      zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 1
  even_of_odd := fun _ _ _ => even_two

private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => (by norm_num : (2 : ℚ) ≠ 0).isUnit


private def cutoff : Unit → ℕ := fun _ => 4
private def values : Unit × ℕ → ℚ := fun p => if p.2 = 0 then 3 else 0

private theorem hvalues : ∀ i r, elvElementaryRank D cutoff i ≤ r → values (i,r) = 0 := by
  intro i r hr
  have hr' : 2 ≤ r := by simpa [D, cutoff, elvElementaryRank] using hr
  simp [values, show r ≠ 0 by omega]


example :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (elvQuotientMap D Sc cutoff _ _
        (sourceCoefficientHom D Sc (e D ℚ () 0) (dotE D Sc [()] 0))) =
      (3 : ℚ) • dotE D Sc [()] 0 := by
  rw [elvAffineScalarSpecialization_source, scalarEvaluation_e]
  rfl

example :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (elvQuotientMap D Sc cutoff _ _
        (sourceCoefficientHom D Sc (delta D ℚ ⟨(), rfl⟩) (dotE D Sc [()] 0))) = 0 := by
  rw [elvAffineScalarSpecialization_source, scalarEvaluation_delta, zero_smul]

example : Function.Surjective
    ((elvAffineScalarSpecialization D Sc cutoff values hvalues).map :
      (elvQuotientObj D Sc cutoff (coefficientObj D Sc [()]) ⟶
        elvQuotientObj D Sc cutoff (coefficientObj D Sc [()])) →
      ((pres D Sc).obj (ob D [()]) ⟶ (pres D Sc).obj (ob D [()]))) :=
  elvAffineScalarSpecialization_surjective D Sc cutoff values hvalues [()] [()]

end ELVScalarHomConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVScalarSpecializationFunctor
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
