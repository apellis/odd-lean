import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOrdinaryWordCorner
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
open scoped TensorProduct
namespace ELVProbeOrdinaryWordCornerConsumer
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
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private abbrev ν : List Bool := [false,true]
private abbrev s : Word Bool 2 := ⟨ν,rfl⟩
private abbrev hs : s.val.Perm ν := List.Perm.refl _
private abbrev v : OrdinaryContentCategory D Sc a ν := ⟨ν,List.Perm.refl _⟩

example : End v ≃+* CyclotomicWordCorner D Sc a s :=
  ordinaryWordCornerEquiv D Sc a ν s hs

example (f : End (wordObj D Sc s)) :
    ordinaryWordCornerEquiv D Sc a ν s hs
      (End.of ((cycHom D Sc a ν ν).mkQ f)) = cyclotomicWordEnd D Sc a s f :=
  ordinaryWordCornerEquiv_mk D Sc a ν s hs f

/-- The odd dot is a unit in the literal ordinary quotient category. -/
example : IsUnit (End.of ((cycHom D Sc a ν ν).mkQ (dotE D Sc ν 0)) : End v) :=
  probeOrdinaryWordDot_isUnit D Sc ν m s hs 0 (by decide)

/-- The even dot is a unit in the same literal mixed-colour quotient. -/
example : IsUnit (End.of ((cycHom D Sc a ν ν).mkQ (dotE D Sc ν 1)) : End v) :=
  probeOrdinaryWordDot_isUnit D Sc ν m s hs 1 (by decide)

end ELVProbeOrdinaryWordCornerConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeOrdinaryWordCorner
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."