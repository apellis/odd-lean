import OddMath.QuiverHecke.CyclotomicAction.ELVProbeSpecialization
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke OddMath.SKM.SYM
namespace ELVProbeSpecializationConsumer
private def D : SKM.Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun i j => if i = j then 2 else 0
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by
        simp [CartanDatum.cartanMatrix_apply, Ne.symm h]
      zero_comm := fun i j => by
        by_cases h : i = j
        · subst j
          simp [CartanDatum.cartanMatrix_apply]
        · simp [CartanDatum.cartanMatrix_apply, h, Ne.symm h] }
  parity := fun i => if i then 0 else 1
  even_of_odd := by
    intro i j _
    change Even (if j = i then (2 : ℤ) else 0)
    split_ifs <;> norm_num

private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => (by norm_num : (2 : ℚ) ≠ 0).isUnit


private def m : Bool → ℕ := fun i => if i then 5 else 3
private abbrev cut := probeCutoff D m
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m

example : (elvProbeAffineSpecialization D m Sc).map (ELVOld.relation D Sc cut false [true]) =
    firstDotPoly D Sc a false [true] :=
  elvProbeAffineSpecialization_relation D m Sc false [true]

example : (elvProbeAffineSpecialization D m Sc).map (ELVOld.relation D Sc cut true []) =
    firstDotPoly D Sc a true [] :=
  elvProbeAffineSpecialization_relation D m Sc true []

example : Function.Surjective (elvProbeOldHom D m Sc [false,true] [false,true]) :=
  elvProbeOldHom_surjective D m Sc [false,true] [false,true]

example (f : ELVOld.Old D Sc cut [false] [false]) :
    elvProbeOldHom D m Sc [false,true] [false,true]
        (elvProbeOldRightContext D m Sc [true] [false] [false] f) =
      probeCycHomRightContext D m Sc [true] [false] [false]
        (elvProbeOldHom D m Sc [false] [false] f) :=
  elvProbeOldHom_rightContext D m Sc [true] [false] [false] f

private def s : Word Bool 1 := ⟨[false],rfl⟩

example : elvProbeWordEntry D m Sc s s
    ((ELVOld.ideal D Sc cut s.val s.val).mkQ (𝟙 (ELVOld.obj D Sc cut s.val))) =
      cyclotomicWordIdempotent D Sc a s :=
  elvProbeWordEntry_id D m Sc s

example (f : ELVOld.Old D Sc cut s.val s.val) :
    cyclotomicAppend D Sc true a 0 (elvProbeWordEntry D m Sc s s f) =
      elvProbeWordEntry D m Sc (appendWord true s) (appendWord true s)
        (elvProbeOldRightContext D m Sc [true] s.val s.val f) :=
  elvProbeWordEntry_append D m Sc true s s f

end ELVProbeSpecializationConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeSpecialization
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
