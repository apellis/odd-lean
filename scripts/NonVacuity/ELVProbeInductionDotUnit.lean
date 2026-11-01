import OddMath.QuiverHecke.CyclotomicAction.ELVProbeInductionDotUnit
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
open scoped TensorProduct
namespace ELVProbeInductionDotUnitConsumer
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
private abbrev O := probeOrdinaryModuleSuperfunctor D Sc m ν N hN
private abbrev qv : OrdinaryContentCategory D Sc a ν := ⟨ν,List.Perm.refl _⟩
private abbrev J (i : Bool) := probeOrdinaryAppend D Sc m ν i
private abbrev t (i : Bool) := (J i).obj qv
private abbrev P (i : Bool) := ELVOld.BalancedInduction.superspace (J i) O.toFunctor (t i)

/-- Both parities use the real quotient coend and its prescribed signed dot. -/
example : IsUnit (End.of (ELVOld.BalancedInduction.transformLinear
    (probeOrdinaryAppendDot_supernatural D Sc m ν false) O (t false)) : End (P false)) :=
  probeOrdinaryInductionDot_isUnit D Sc m ν false O (t false)
example : IsUnit (End.of (ELVOld.BalancedInduction.transformLinear
    (probeOrdinaryAppendDot_supernatural D Sc m ν true) O (t true)) : End (P true)) :=
  probeOrdinaryInductionDot_isUnit D Sc m ν true O (t true)

private abbrev M₀ := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 0)
private abbrev N₀ := probeOldModule D m Sc [] M₀
private abbrev O₀ := probeOrdinaryModuleSuperfunctor D Sc m [] N₀
  (probeOldModule_evaluatesCoefficients D m Sc [] M₀)
private abbrev vac : OrdinaryContentCategory D Sc a [] := ⟨[],List.Perm.refl _⟩
private abbrev t₀ (i : Bool) := (probeOrdinaryAppend D Sc m [] i).obj vac
private abbrev P₀ (i : Bool) := ELVOld.BalancedInduction.superspace
  (probeOrdinaryAppend D Sc m [] i) O₀.toFunctor (t₀ i)
example : (End (P₀ false))ˣ := probeOrdinaryInductionDotUnit D Sc m [] false O₀ (t₀ false)
example : (End (P₀ true))ˣ := probeOrdinaryInductionDotUnit D Sc m [] true O₀ (t₀ true)

end ELVProbeInductionDotUnitConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeInductionDotUnit
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."