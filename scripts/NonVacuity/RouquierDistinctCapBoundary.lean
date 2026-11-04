import OddMath.SKM.RouquierDistinctCapBoundary
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath OddMath.SKM
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.RouquierDistinctCapBoundary
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

private def m : Bool → ℕ := fun _ => 3
private def Λ : Bool → ℤ := fun i => probeCutoff disconnected m i
private theorem cutoff (i : Bool) : (probeCutoff disconnected m i : ℤ) = disconnected.h i Λ := rfl
private abbrev T := probeOldRouquierFamily disconnected (parameterTwist disconnected ds) m Λ cutoff
private theorem M : RouquierMulticolour T ds := probeOldRouquierMulticolour disconnected ds m Λ cutoff
private def b (i : Bool) : Bool → ℤ := -Λ + 3 • disconnected.α i
private def a (i : Bool) : Bool → ℤ := b i - disconnected.α i
private theorem hab (i : Bool) : a i + disconnected.α i = b i := sub_add_cancel _ _
private theorem hfc (i : Bool) : (a i + disconnected.α (!i)) + disconnected.α i =
    b i + disconnected.α (!i) := by rw [a]; abel
private theorem hed (i : Bool) : (b i + disconnected.α i) + disconnected.α (!i) =
    (b i + disconnected.α (!i)) + disconnected.α i := by abel
private theorem ne (i : Bool) : i ≠ !i := by cases i <;> decide
private theorem zeroHeight (i : Bool) : disconnected.h i (b i) = 0 := by
  cases i <;> norm_num [b, Λ, m, disconnected, Datum.h, Datum.α,
    probeCutoff, probeDotExponent]
private theorem shiftedZeroHeight (i : Bool) :
    disconnected.h i (b i + disconnected.α (!i)) = 0 := by
  cases i <;> norm_num [b, Λ, m, disconnected, Datum.h, Datum.α,
    probeCutoff, probeDotExponent]
private theorem disjoint (i : Bool) : disconnected.d i (!i) = 0 := by cases i <;> decide

example (i : Bool) := T.sig_capL_of_zero (hab i) rfl (zeroHeight i)
example (i : Bool) := T.distinctMixedBraidRight_cap_of_zero_disconnected M (ne i)
  (hab i) rfl rfl (hfc i) rfl (shiftedZeroHeight i) (disjoint i)
example (i : Bool) := T.distinctMixedBraidLeft_cap_of_zero_disconnected M (ne i)
  (hab i) rfl rfl rfl (hfc i) rfl (hed i) (shiftedZeroHeight i) (disjoint i)
example : (ds.t false true : ℚ) = 2 := rfl
example (i : Bool) : probeOldVacuumAppendVector disconnected
    (parameterTwist disconnected ds) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero disconnected (parameterTwist disconnected ds) m i
    (by cases i <;> decide)
end NonVacuity.RouquierDistinctCapBoundary
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierDistinctCapBoundary
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty audit"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
