import OddMath.QuiverHecke.CyclotomicAction.ELVProbeQuadraticFields
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumVector
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.ELVProbeQuadraticFields
private def D : SKM.Datum Bool (Bool → ℤ) :=
  { AsymmetricParameters.datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => AsymmetricParameters.datum.even_of_odd i j rfl }
private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun i j p q => if (p : ZMod 2) * D.parity i = 0 ∧
    (q : ZMod 2) * D.parity j = 0 then 1 else 0
  s_symm := by intro i j p q; simp only [and_comm]
  s_eq_zero := by intro i j p q h; simp [h]
  two_isUnit := by intro _; norm_num
private def m : Bool → ℕ := fun _ => 4
private abbrev Sc' := parameterTwist D Sc
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc' a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc' m ν :=
  ⟨probeOldModule D m Sc' ν (R ν), probeOldModule_evaluatesCoefficients D m Sc' ν (R ν)⟩
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private def w (v : List Bool) : Bool → ℤ := (v.map D.α).sum - Λ
private def base (v : List Bool) : WeightBlocks D Λ (w v) := ⟨v, rfl⟩
private theorem neq (i : Bool) : i ≠ !i := by cases i <;> decide

-- Connected mixed colours retain a nonzero interior parameter.
example : D.dn false true = 2 ∧ D.dn true false = 4 := by decide
example : Sc.s false true 1 2 ≠ 0 := by norm_num [Sc, D]; decide
example : (N []).obj = probeOldVacuumRegular D Sc' m := rfl
example : probeOldVacuumVector D Sc' m ≠ 0 := probeOldVacuumVector_ne_zero D Sc' m
private def W (x : Bool → ℤ) : ProbeOldWeightProduct D Sc' m Λ x := fun β => N β.1.toList
example : HEq (W (w []) (base [])) (N []) := by
  change HEq (N ((0 : Multiset Bool).toList)) (N [])
  rw [Multiset.toList_zero]
example (i : Bool) := probeOldRouquierData_quadNe D Sc m i (!i) Λ
  (x₀ := w []) rfl rfl rfl (by abel) (neq i) (by cases i <;> decide)
example (i : Bool) := probeOldRouquierData_quadNe D Sc m i (!i) Λ
  (x₀ := w [i,!i]) rfl rfl rfl (by abel) (neq i) (by cases i <;> decide)

-- The all-odd asymmetric pair has a negative crossing-square sign.
private abbrev O := AsymmetricParameters.datum
private abbrev Os := AsymmetricParameters.scalars
private abbrev Ot := parameterTwist O Os
private abbrev ao : Bool → Polynomial ℚ := probePolynomial (probeDotExponent O) m
private def Ro (ν : List Bool) := SuperBimodule.regular
  (heightParity O Ot ao (probePolynomial_parity O m) ν.length)
private def No (ν : List Bool) : ProbeEvaluatedModules O Ot m ν :=
  ⟨probeOldModule O m Ot ν (Ro ν), probeOldModule_evaluatesCoefficients O m Ot ν (Ro ν)⟩
private def wo (v : List Bool) : Bool → ℤ := (v.map O.α).sum - Λ
private def bo (v : List Bool) : WeightBlocks O Λ (wo v) := ⟨v,rfl⟩
example : sign ℚ (O.parity false * O.parity true) = -1 := by decide
example := probeOldRouquierData_quadNe O Os m false true Λ
  (x₀ := wo [false,true]) rfl rfl rfl (by abel) (by decide) (by decide)
example := probeOldRouquierData_quadNe O Os m true false Λ
  (x₀ := wo []) rfl rfl rfl (by abel) (by decide) (by decide)

-- The disconnected branch retains its nontrivial original parameter value 2.
private def disconnected : SKM.Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else 0
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else 0)
    split
    · exact ⟨1, by norm_num⟩
    · exact ⟨0, rfl⟩
private def twoUnit : ℚˣ := Units.mk0 2 (by norm_num)
private def ds : SKM.Scalars disconnected ℚ where
  t := fun i j => if i = j then 1 else twoUnit
  t_self := by intro i; simp
  t_symm_of_d_eq_zero := by intro i j _; simp only [eq_comm]
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num
private def Ld : Bool → ℤ := fun i => probeCutoff disconnected m i
example : disconnected.d false true = 0 := by decide
example : (ds.t false true : ℚ) = 2 := rfl
example : probeOldVacuumVector disconnected (parameterTwist disconnected ds) m ≠ 0 :=
  probeOldVacuumVector_ne_zero disconnected (parameterTwist disconnected ds) m
example := probeOldRouquierData_quadZero disconnected ds m false true Ld
  (x₀ := -Ld) rfl rfl rfl (by abel) (by decide) (by decide)
example := probeOldRouquierData_quadZero disconnected ds m true false Ld
  (x₀ := -Ld) rfl rfl rfl (by abel) (by decide) (by decide)
end NonVacuity.ELVProbeQuadraticFields

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVProbeQuadraticFields] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
