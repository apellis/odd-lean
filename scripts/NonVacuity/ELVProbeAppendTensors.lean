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

example : ev δ = 0 := by
  rw [elvScalarEvaluation_quotient, scalarEvaluation_delta]

example : ev χ = -3 := by
  rw [elvScalarEvaluation_quotient, scalarEvaluation_e]
  norm_num [probeScalarValues, D, m]


private abbrev hN := probeOldModule_evaluatesCoefficients D m Sc ν M
private abbrev Q := probeOldOrdinaryFunctor D Sc m ν
private abbrev qv := Q.obj v
private abbrev O := probeOrdinaryModuleSuperfunctor D Sc m ν N hN
private abbrev J (i : Bool) := ELVOld.oldContentAppend D Sc cut ν i
private abbrev T (i : Bool) := probeOrdinaryAppend D Sc m ν i
private abbrev U (i : Bool) := probeOldOrdinaryFunctor D Sc m (i :: ν)
private abbrev w (i : Bool) := (U i).obj ((J i).obj v)

example (i : Bool) :
    (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom ∈ parity (R := ℚ) _ _ 0 :=
  probeAppendOrdinaryModuleIso_hom_mem D Sc m ν N hN i

example (i : Bool) :
    (probeAppendOrdinaryModuleIso D Sc m ν N hN i).inv ∈ parity (R := ℚ) _ _ 0 :=
  probeAppendOrdinaryModuleIso_inv_mem D Sc m ν N hN i

private abbrev appendDot (i : Bool) : (J i).obj v ⟶ (J i).obj v :=
  (ELVOld.ideal D Sc cut (ν ++ [i]) (ν ++ [i])).mkQ
    (ELVOld.affineUnit D Sc cut (ν ++ [i]) (ν ++ [i]) (dotE D Sc (ν ++ [i]) 0))

/-- The odd moving dot must retain the minus sign on this odd coend arrow. -/
example : twist ℚ 1 (appendDot false) = -appendDot false := by
  have hg : appendDot false ∈ parity (R := ℚ) _ _ 1 :=
    Submodule.mem_map_of_mem
      (ELVOld.affineUnit_mem D Sc cut (firstDot_parity D Sc false [true,false]))
  simpa only [one_mul, sign_one, neg_one_smul] using twist_of_mem 1 hg

example (i : Bool) (b : N.obj v) :
    (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom.total (w i)
      (ELVOld.BalancedInduction.tensor (J i) N.toFunctor v (𝟙 _ + appendDot i) b) =
    ELVOld.BalancedInduction.tensor (T i) O.toFunctor qv ((U i).map (𝟙 _ + appendDot i)) b :=
  probeAppendOrdinaryModuleIso_hom_tensor D Sc m ν N hN i v ((J i).obj v) (𝟙 _ + appendDot i) b

example (i : Bool) :
    (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom.total (w i) ∘ₗ
      probeOldContentInductionDot D Sc m ν i N ((J i).obj v) =
    ELVOld.BalancedInduction.transformLinear
      (probeOrdinaryAppendDot_supernatural D Sc m ν i) O (w i) ∘ₗ
      (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom.total (w i) :=
  probeAppendOrdinaryModuleIso_hom_dot D Sc m ν N hN i ((J i).obj v)

example (i : Bool) (b : N.obj v) :
    (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom.total (w i)
      (ELVOld.BalancedInduction.unit (J i) N.toFunctor v b) =
    ELVOld.BalancedInduction.unit (T i) O.toFunctor qv b :=
  probeAppendOrdinaryModuleIso_hom_unit D Sc m ν N hN i v b

private abbrev M0 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 0)
private abbrev N0 := probeOldModule D m Sc [] M0
private abbrev hN0 := probeOldModule_evaluatesCoefficients D m Sc [] M0
private abbrev O0 := probeOrdinaryModuleSuperfunctor D Sc m [] N0 hN0
private abbrev v0 : ELVOld.OldContentCategory D Sc cut [] :=
  ELVOld.oldContentObject D Sc cut [] ⟨[],List.Perm.refl []⟩
private abbrev J0 (i : Bool) := ELVOld.oldContentAppend D Sc cut [] i
private abbrev T0 (i : Bool) := probeOrdinaryAppend D Sc m [] i
private abbrev Q0 := probeOldOrdinaryFunctor D Sc m []
private abbrev U0 (i : Bool) := probeOldOrdinaryFunctor D Sc m [i]

example (i : Bool) (b : N0.obj v0) :
    (probeAppendOrdinaryModuleIso D Sc m [] N0 hN0 i).hom.total ((U0 i).obj ((J0 i).obj v0))
      (ELVOld.BalancedInduction.unit (J0 i) N0.toFunctor v0 b) =
    ELVOld.BalancedInduction.unit (T0 i) O0.toFunctor (Q0.obj v0) b :=
  probeAppendOrdinaryModuleIso_hom_unit D Sc m [] N0 hN0 i v0 b

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
