import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightQuadratic
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumVector
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.ELVProbeWeightQuadratic
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
example (i : Bool) := probeOldActionDistinctCross_quadratic D Sc m i (!i) Λ
  (x₀ := w []) rfl rfl rfl (by abel) (neq i)
example (i : Bool) := congrArg (fun f => f.total (W (w [i,!i])))
  (probeOldActionDistinctCross_quadratic D Sc m i (!i) Λ
    (x₀ := w [i,!i]) rfl rfl rfl (by abel) (neq i))
example (i : Bool) := probeOldBlockDistinctCross_quadratic D Sc m i (!i) Λ
  rfl rfl rfl (by abel) (neq i) (base [i,!i]) _ rfl

private def emptyBlock : WeightBlocks D Λ (-Λ) := ⟨0, by simp⟩
private theorem absent (i j : Bool) :
    ¬ ∃ β, blockSucc₂ D i j Λ
      (show (-Λ - D.α i - D.α j) + D.α j = -Λ - D.α i by abel)
      (show (-Λ - D.α i) + D.α i = -Λ by abel) β = emptyBlock := by
  rintro ⟨β, hβ⟩
  have h := congrArg (fun γ => γ.1.card) hβ
  simp only [blockSucc₂, blockSucc_val, Multiset.card_add, Multiset.card_singleton,
    emptyBlock, Multiset.card_zero] at h
  omega
example (i : Bool) := absent i (!i)
example (i : Bool) := probeOldActionDistinctCross_quadratic D Sc m i (!i) Λ
  (x₀ := -Λ - D.α i - D.α (!i)) (xj := -Λ - D.α i)
  (xi := -Λ - D.α (!i)) (xu := -Λ)
  (by abel) (by abel) (by abel) (by abel) (neq i)

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
private def Wo (x : Bool → ℤ) : ProbeOldWeightProduct O Ot m Λ x := fun β => No β.1.toList
private def shifted (x : Bool → ℤ) : ProbeOldWeightProduct O Ot m Λ x := fun β =>
  ⟨supermoduleParityObj (Wo x β).obj,
    probeEvaluatesCoefficients_parity O Ot m β.1.toList (Wo x β).obj (Wo x β).property⟩
private def oddInput (x : Bool → ℤ) : shifted x ⟶ Wo x := fun β =>
  ⟨(supermoduleParityIso (Wo x β).obj).hom⟩
private theorem oddInput_mem (x : Bool → ℤ) : oddInput x ∈ parity (R := ℚ) _ _ 1 :=
  fun β => supermoduleParityIso_hom_mem (Wo x β).obj
example := probeOldActionDistinctCross_quadratic O Os m false true Λ
  (x₀ := wo [false,true]) rfl rfl rfl (by abel) (by decide)
example := probeOldActionDistinctCross_quadratic O Os m true false Λ
  (x₀ := wo []) rfl rfl rfl (by abel) (by decide)
example := (probeOldWeightDistinctCross O Ot m false true Λ (x₀ := -Λ)
  rfl rfl rfl (by abel)).naturality 1 (oddInput (-Λ)) (oddInput_mem (-Λ))
end NonVacuity.ELVProbeWeightQuadratic

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightQuadratic] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
