import OddMath.SKM.RouquierDistinctCapColumns
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath OddMath.SKM
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.RouquierDistinctCapColumns
namespace Connected
private def D : Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else -4
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else -4)
    split
    · exact ⟨1, by norm_num⟩
    · exact ⟨-2, by norm_num⟩
private def twoUnit : ℚˣ := Units.mk0 2 (by norm_num)
private def S : Scalars D ℚ where
  t := fun i j => if i = j then 1 else twoUnit
  t_self := by intro i; simp
  t_symm_of_d_eq_zero := by intro i j _; simp only [eq_comm]
  s := fun i j p q => if i ≠ j ∧ p = 2 ∧ q = 2 then 1 else 0
  s_symm := by
    intro i j p q
    by_cases hij : i = j
    · subst j; simp
    · by_cases hp : p = 2 <;> by_cases hq : q = 2 <;> simp_all [Ne.symm hij]
  s_eq_zero := by
    intro i j p q hp
    have h : p ≠ 2 := by
      intro he
      subst p
      change (2 : ZMod 2) * 1 = 1 at hp
      exact (by decide : ¬ ((2 : ZMod 2) * 1 = 1)) hp
    simp [h]
  two_isUnit := by intro _; norm_num
private def m (_ : Bool) : ℕ := 3
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private theorem cutoff (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := rfl
private abbrev T := probeOldRouquierFamily D (parameterTwist D S) m Λ cutoff
private theorem M : RouquierMulticolour T S := probeOldRouquierMulticolour D S m Λ cutoff
private def a : Bool → ℤ := -Λ
private theorem ne (i : Bool) : i ≠ !i := by cases i <;> decide
private theorem square (i : Bool) : (a + D.α (!i)) + D.α i = (a + D.α i) + D.α (!i) := by abel
private theorem beforeUpper (i : Bool) :
    ((a + D.α (!i)) - D.α i) + D.α i = a + D.α (!i) := sub_add_cancel _ _
private theorem height (i : Bool) : D.h i a = -6 := by
  cases i <;> norm_num [a, Λ, m, D, Datum.h, probeCutoff, probeDotExponent]
private theorem upperHeight (i : Bool) : D.h i (a + D.α (!i)) = -10 := by
  cases i <;> norm_num [a, Λ, m, D, Datum.h, Datum.α, probeCutoff, probeDotExponent]

/-- Both orders of two odd colours, every finite column, and the
nonzero interior parameter are retained in the constructed family. -/
example (i : Bool) (n : Fin 6) := T.distinctCapQuadraticColumn_of_neg M (ne i)
  (show a + D.α i = a + D.α i from rfl) rfl rfl (square i) (beforeUpper i)
  (by rw [height]; decide) n.val (by rw [height]; exact n.isLt)
example (i : Bool) (n : Fin 6) := T.distinctCapColumn_rightDot
  (show a + D.α (!i) = a + D.α (!i) from rfl) (square i) (beforeUpper i)
  (by rw [upperHeight]; decide) n.val 4 (by rw [upperHeight]; have := n.isLt; omega)
example (i : Bool) (n : Fin 6) := T.distinctCapColumn_monomial_zero
  (show a + D.α (!i) = a + D.α (!i) from rfl) (square i) (beforeUpper i)
  (by rw [upperHeight]; decide) n.val 2 2 (by rw [upperHeight]; have := n.isLt; omega)
example (i : Bool) (n : Fin 6) := T.distinctCapColumn_monomial_zero
  (show a + D.α (!i) = a + D.α (!i) from rfl) (square i) (beforeUpper i)
  (by rw [upperHeight]; decide) n.val 0 1 (by rw [upperHeight]; have := n.isLt; omega)
example (i : Bool) : S.s i (!i) 2 2 = 1 := by cases i <;> rfl
example (i : Bool) : (S.t i (!i) : ℚ) = 2 := by cases i <;> rfl
example (i : Bool) : probeOldVacuumAppendVector D (parameterTwist D S) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D (parameterTwist D S) m i (by cases i <;> decide)
end Connected

namespace Disconnected
private def D : Datum Bool (Bool → ℤ) where
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
private def S : Scalars D ℚ where
  t := fun i j => if i = j then 1 else twoUnit
  t_self := by intro i; simp
  t_symm_of_d_eq_zero := by intro i j _; simp only [eq_comm]
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num
private def m (_ : Bool) : ℕ := 3
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private theorem cutoff (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := rfl
private abbrev T := probeOldRouquierFamily D (parameterTwist D S) m Λ cutoff
private theorem M : RouquierMulticolour T S := probeOldRouquierMulticolour D S m Λ cutoff
private def a : Bool → ℤ := -Λ
private theorem ne (i : Bool) : i ≠ !i := by cases i <;> decide
private theorem square (i : Bool) : (a + D.α (!i)) + D.α i = (a + D.α i) + D.α (!i) := by abel
private theorem beforeUpper (i : Bool) :
    ((a + D.α (!i)) - D.α i) + D.α i = a + D.α (!i) := sub_add_cancel _ _
private theorem height (i : Bool) : D.h i a = -6 := by
  cases i <;> norm_num [a, Λ, m, D, Datum.h, probeCutoff, probeDotExponent]
example (i : Bool) (n : Fin 6) := T.distinctCapQuadraticColumn_of_neg M (ne i)
  (show a + D.α i = a + D.α i from rfl) rfl rfl (square i) (beforeUpper i)
  (by rw [height]; decide) n.val (by rw [height]; exact n.isLt)
example (i : Bool) : D.d i (!i) = 0 := by cases i <;> rfl
example (i : Bool) : (S.t i (!i) : ℚ) = 2 := by cases i <;> rfl
example (i : Bool) : probeOldVacuumAppendVector D (parameterTwist D S) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D (parameterTwist D S) m i (by cases i <;> decide)
end Disconnected
end NonVacuity.RouquierDistinctCapColumns
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierDistinctCapColumns
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations: standard axioms only"
