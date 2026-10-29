import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.ReservoirCoefficients
import StringDiagrams.Super.DrinfeldCenterPiCounterexample
import Mathlib.Data.ZMod.Basic
import Lean.Util.CollectAxioms

/-! A nonzero square-zero coefficient ideal over `ZMod 9`, where `2` is invertible.
This checks coefficient transport and ideal multiplication, not existence of a
cyclotomic Rouquier family or odd nondegeneracy. -/

noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open OddMath.QuiverHecke.SwappedAssembly.ProbeWindow

namespace NonVacuity.ReservoirCoefficients

abbrev R := ZMod 9
abbrev B := UnitTwo R
abbrev b : B := .pt
abbrev Z : b ⟶ b := ⟨⟩

def coeffDeg (n : ℤ) : Set R :=
  if n ≤ 0 then Set.univ else if n = 1 then {x | 3 * x = 0} else {0}

theorem coeffDeg_zero (n : ℤ) : (0 : R) ∈ coeffDeg n := by
  simp only [coeffDeg]
  split_ifs <;> simp

theorem coeffDeg_mul {m n : ℤ} {x y : R}
    (hx : x ∈ coeffDeg m) (hy : y ∈ coeffDeg n) : x * y ∈ coeffDeg (m + n) := by
  have hsq : ∀ x y : R, 3 * x = 0 → 3 * y = 0 → x * y = 0 := by decide
  simp only [coeffDeg] at *
  split_ifs at * <;> simp_all [mul_left_comm] <;> try omega
  calc x * (3 * y) = (3 * x) * y := by ring
       _ = 0 := by rw [hx, zero_mul]

/-- A coefficient filtration with a nonzero degree-one ideal and zero degree two. -/
def grading : CoeffGrading R b where
  deg := coeffDeg
  id_mem := by trivial
  comp_mem hx hy := coeffDeg_mul hx hy
  proj_mem := by
    intro m q c hc
    have h0 : c ∈ parity (R := R) (𝟙 b) (𝟙 b) 0 := by
      change c ∈ trivialGrading R 0
      simp
    by_cases hq : q = 0
    · subst q
      simpa only [proj_of_mem h0] using hc
    · rw [proj_of_mem_ne h0 (Ne.symm hq)]
      exact coeffDeg_zero _

theorem grading_bound (m : ℤ) (hm : (2 : ℤ) ≤ m) (c : 𝟙 b ⟶ 𝟙 b)
    (hc : c ∈ grading.deg m) : c = 0 := by
  change c ∈ coeffDeg m at hc
  simpa [coeffDeg, show ¬m ≤ 0 by omega, show m ≠ 1 by omega] using hc

def ideal : CoefficientIdeal (b ⟶ b) := reservoirCoefficientIdeal b grading 2 grading_bound

theorem three_mem : ideal.mem 1 (postCoeff Z (3 : R)) :=
  postCoeff_mem (Gr := grading) (m := 1) (by norm_num) Z (by change 3 * (3 : R) = 0; decide)

example : postCoeff Z (3 : R) ≠ 0 := by
  change (1 : R) * 3 * 1 ≠ 0
  decide

/-- Both factors are nonzero; their composite vanishes by joint ideal nilpotence. -/
example : postCoeff Z (3 : R) ≫ postCoeff Z (3 : R) = 0 := by
  apply ideal.eq_zero
  exact ideal.comp_mem (m := 1) (n := 1) three_mem three_mem

example (f : Z ⟶ Z) : ideal.mem 0 f := mem_coeffIdeal_zero f

example (f g : Z ⟶ Z) : ideal.mem 1 (f ≫ postCoeff Z (3 : R) ≫ g) :=
  comp_postCoeff_comp_mem (Gr := grading) (n := 1) (m := 1) (by norm_num) (by change 3 * (3 : R) = 0; decide) f g

example (f : Z ⟶ Z) (hf : ideal.mem 2 f) : ideal.mem 1 f := ideal.mono hf

example : (2 : R) * 5 = 1 := by decide

#print axioms reservoirCoefficientIdeal
#print axioms coeffIdeal_mono
#print axioms coeffIdeal_comp_mem
#print axioms CoefficientIdeal.isIso_of_sub_mem
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.homCoefficientIdeal

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! ==
        `OddMath.QuiverHecke.SwappedAssembly.CentralInverse.ReservoirCoefficients then
      for name in env.header.moduleData[i]!.constNames do
        for axiomName in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations found"
  logInfo m!"Audited {count} owned declarations: standard axioms only"

end NonVacuity.ReservoirCoefficients