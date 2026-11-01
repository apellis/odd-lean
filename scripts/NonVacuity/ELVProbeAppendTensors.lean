import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
open scoped TensorProduct
namespace ELVProbeAppendTensorsConsumer
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
private abbrev Q := probeOldOrdinaryFunctor D Sc m ν
private abbrev qv := Q.obj v
private abbrev O := probeOrdinaryModuleSuperfunctor D Sc m ν N hN
private abbrev J (i : Bool) := ELVOld.oldContentAppend D Sc cut ν i
private abbrev T (i : Bool) := probeOrdinaryAppend D Sc m ν i
private abbrev U (i : Bool) := probeOldOrdinaryFunctor D Sc m (i :: ν)
private abbrev w (i : Bool) := (U i).obj ((J i).obj v)

example (b : N.obj v) :
    (probeAppendOrdinaryModuleIso D Sc m ν N hN false).hom.total (w false)
      (ELVOld.BalancedInduction.tensor (J false) N.toFunctor v (𝟙 ((J false).obj v)) b) =
    ELVOld.BalancedInduction.tensor (T false) O.toFunctor qv
      ((U false).map (𝟙 ((J false).obj v))) b :=
  probeAppendOrdinaryModuleIso_hom_tensor D Sc m ν N hN false v ((J false).obj v) (𝟙 ((J false).obj v)) b

example (b : N.obj v) :
    (probeAppendOrdinaryModuleIso D Sc m ν N hN true).hom.total (w true)
      (ELVOld.BalancedInduction.tensor (J true) N.toFunctor v (𝟙 ((J true).obj v)) b) =
    ELVOld.BalancedInduction.tensor (T true) O.toFunctor qv
      ((U true).map (𝟙 ((J true).obj v))) b :=
  probeAppendOrdinaryModuleIso_hom_tensor D Sc m ν N hN true v ((J true).obj v) (𝟙 ((J true).obj v)) b

private abbrev χg := probeOldCoefficient D m Sc (false :: ν) ((J false).obj v) χ
private abbrev δg := probeOldCoefficient D m Sc (true :: ν) ((J true).obj v) δ

/-- Actual nontrivial full-coefficient arrows are specialized, not discarded before induction. -/
example (b : N.obj v) :
    (probeAppendOrdinaryModuleIso D Sc m ν N hN false).hom.total (w false)
      (ELVOld.BalancedInduction.tensor (J false) N.toFunctor v χg b) =
    ELVOld.BalancedInduction.tensor (T false) O.toFunctor qv ((U false).map χg) b :=
  probeAppendOrdinaryModuleIso_hom_tensor D Sc m ν N hN false v ((J false).obj v) χg b
example (b : N.obj v) :
    (probeAppendOrdinaryModuleIso D Sc m ν N hN true).hom.total (w true)
      (ELVOld.BalancedInduction.tensor (J true) N.toFunctor v δg b) =
    ELVOld.BalancedInduction.tensor (T true) O.toFunctor qv ((U true).map δg) b :=
  probeAppendOrdinaryModuleIso_hom_tensor D Sc m ν N hN true v ((J true).obj v) δg b

end ELVProbeAppendTensorsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."