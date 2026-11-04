import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.SeparatedClosures
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

namespace NonVacuity.SeparatedClosures

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

private def a : Aut Z := Iso.refl Z
private def bendD : Z ⟶ Z := -∑ r ∈ Finset.range 3,
  (-1 : ℤ) ^ (r + 1) • ((a ^ (-(r : ℤ) - 1)).hom ≫ 𝟙 Z ≫ 𝟙 Z)
private def bendC : Z ⟶ Z := ∑ s ∈ Finset.range 3,
  (-1 : ℤ) ^ (s + 2) • ((𝟙 Z) ≫ 𝟙 Z ≫ (a ^ (-(s : ℤ) - 1)).hom)

private theorem closure_mem (r s : ℕ) :
    ideal.mem 1 ((fun _ : ℕ => 𝟙 Z) r ≫ postCoeff Z (3 : R) ≫ (fun _ : ℕ => 𝟙 Z) s) := by
  simpa only [Category.id_comp, Category.comp_id] using three_mem

example (s : ℕ) : ideal.mem 1 (bendD ≫ postCoeff Z (3 : R) ≫ (𝟙 Z)) :=
  separated_cap_closure ideal a (𝟙 Z) (-1) (uR := fun _ => 𝟙 Z)
    (vR := fun _ => 𝟙 Z) (N := 3) rfl closure_mem (fun _ _ => mem_coeffIdeal_zero _) s

example (r : ℕ) : ideal.mem 1 ((𝟙 Z) ≫ postCoeff Z (3 : R) ≫ bendC) :=
  separated_unit_closure ideal a (𝟙 Z) (-1) (uR := fun _ => 𝟙 Z)
    (vR := fun _ => 𝟙 Z) (N := 3) rfl closure_mem (fun _ _ => mem_coeffIdeal_zero _) r

example : ideal.mem 1 (bendD ≫ postCoeff Z (3 : R) ≫ bendC) :=
  separated_closed_error ideal a a (𝟙 Z) (𝟙 Z) (-1)
    (uR := fun _ => 𝟙 Z) (vR := fun _ => 𝟙 Z) (ND := 3) (NC := 3)
    rfl rfl closure_mem (fun _ _ => mem_coeffIdeal_zero _) (fun _ _ => mem_coeffIdeal_zero _)

-- Nine summands give a nonzero closed error in the nontrivial square-zero ideal.
example : bendD ≫ postCoeff Z (3 : R) ≫ bendC ≠ 0 := by
  change (-∑ r ∈ Finset.range 3, (-1 : ℤ) ^ (r + 1) • (1 : R)) *
    ((1 : R) * 3 * 1 * (∑ s ∈ Finset.range 3, (-1 : ℤ) ^ (s + 2) • (1 : R))) ≠ 0
  decide

example : pureSourceSign Z Z Z 2 ≫ pureSourceSign Z Z Z 2 = 𝟙 _ :=
  pureSourceSign_involutive Z Z Z 2

example : pureSourceSign Z Z Z 2 ≫
    negMap (𝟙 Z) (𝟙 Z) (3 : R) (6 : R) (fun _ => 𝟙 Z) (fun _ : Fin 2 => 𝟙 Z) =
      negMap (-𝟙 Z) (-𝟙 Z) (-(3 : R)) (-(6 : R)) (fun _ => 𝟙 Z) (fun _ : Fin 2 => 𝟙 Z) :=
  pureSourceSign_comp_negMap _ _ _ _ _ _

end NonVacuity.SeparatedClosures

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.CentralInverse.SeparatedClosures
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
