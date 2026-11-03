import OddMath.QuiverHecke.CyclotomicAction.ELVWeightQuadraticRelation
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.ELVWeightQuadraticRelation
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
private abbrev X := Bool → ℤ
private theorem step (i : Bool) : (0 : X) + D.α i = D.α i := zero_add _
private theorem step₂ (i j : Bool) : D.α j + D.α i = D.α j + D.α i := rfl
private theorem step₄ (i j : Bool) : D.α i + D.α j = D.α j + D.α i := add_comm _ _

-- The connected mixed consumer retains a nonzero interior polynomial term.
example : Sc.s false true 1 2 = 1 := by
  norm_num [Sc, D]; decide
example := elvActionCross_quadratic D Sc (fun _ => 12) 12 true false (0 : X)
  (step false) (step₂ true false) (step true) (step₄ true false) (by decide)
example := elvActionCross_quadNe D Sc (fun _ => 12) 12 true false (0 : X)
  (step false) (step₂ true false) (step true) (step₄ true false) (by decide) (by decide)
example := elvActionCross_quadNe D Sc (fun _ => 12) 12 false true (0 : X)
  (step true) (step₂ false true) (step false) (step₄ false true) (by decide) (by decide)

-- The all-odd asymmetric datum tests both signs of the transported parameters.
example := elvActionCross_quadNe AsymmetricParameters.datum AsymmetricParameters.scalars
  (fun _ => 12) 12 true false (0 : X) (zero_add _) rfl (zero_add _) (add_comm _ _)
  (by decide) (by decide)
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
private def disconnectedScalars : SKM.Scalars disconnected ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num
example := elvActionCross_quadZero disconnected disconnectedScalars (fun _ => 12) 12
  true false (0 : X) (zero_add _) rfl (zero_add _) (add_comm _ _)
  (by decide) (by decide)
end NonVacuity.ELVWeightQuadraticRelation

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVEndEvaluation,
      `OddMath.QuiverHecke.CyclotomicAction.ELVWeightQuadraticRelation] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
