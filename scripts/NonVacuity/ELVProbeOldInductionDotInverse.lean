import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOldInductionDotInverse
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
open scoped TensorProduct
namespace ELVProbeOldInductionDotInverseConsumer
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
private abbrev ν : List Bool := [false,true]
private abbrev M := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 2)
private abbrev N := probeOldModule D m Sc ν M
private abbrev v : ELVOld.OldContentCategory D Sc cut ν :=
  ELVOld.oldContentObject D Sc cut ν ⟨ν,List.Perm.refl ν⟩
private abbrev g : (pres D Sc).obj (ob D ν) ⟶ (pres D Sc).obj (ob D ν) :=
  dotE D Sc ν 0
private abbrev δ := elvCoefficientQuotient D cut (delta D ℚ ⟨false,rfl⟩)
private abbrev χ := elvCoefficientQuotient D cut (e D ℚ false 0)
private abbrev ev := elvScalarEvaluation (k := ℚ) D cut (probeScalarValues D m) (probeScalarValues_vanish D m)


private abbrev hN := probeOldModule_evaluatesCoefficients D m Sc ν M

private abbrev J (i : Bool) := ELVOld.oldContentAppend D Sc cut ν i

example (i : Bool) : IsUnit (End.of
    (probeOldContentInductionDot D Sc m ν i N ((J i).obj v)) :
    End (ELVOld.BalancedInduction.superspace (J i) N.toFunctor ((J i).obj v))) :=
  probeModuleOldInductionDot_isUnit D Sc m ν M i ((J i).obj v)

example : (probeOldContentInductionDotInverse D Sc m ν false N hN
    ((J false).obj v)).comp
    (probeOldContentInductionDot D Sc m ν false N ((J false).obj v)) = LinearMap.id :=
  probeOldContentInductionDotInverse_comp_dot D Sc m ν false N hN ((J false).obj v)

example : (probeOldContentInductionDot D Sc m ν true N ((J true).obj v)).comp
    (probeOldContentInductionDotInverse D Sc m ν true N hN ((J true).obj v)) = LinearMap.id :=
  probeOldContentInductionDot_comp_inverse D Sc m ν true N hN ((J true).obj v)

private abbrev M0 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 0)
private abbrev N0 := probeOldModule D m Sc [] M0
private abbrev v0 : ELVOld.OldContentCategory D Sc cut [] :=
  ELVOld.oldContentObject D Sc cut [] ⟨[],List.Perm.refl []⟩
private abbrev J0 (i : Bool) := ELVOld.oldContentAppend D Sc cut [] i

/-- Vacuum and both moving parities use the same literal old coend construction. -/
example (i : Bool) : IsUnit (End.of
    (probeOldContentInductionDot D Sc m [] i N0 ((J0 i).obj v0)) :
    End (ELVOld.BalancedInduction.superspace (J0 i) N0.toFunctor ((J0 i).obj v0))) :=
  probeModuleOldInductionDot_isUnit D Sc m [] M0 i ((J0 i).obj v0)

end ELVProbeOldInductionDotInverseConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeOldInductionDotInverse
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."