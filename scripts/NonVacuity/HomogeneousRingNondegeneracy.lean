import OddMath.QuiverHecke.HomogeneousRingNondegeneracy
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

/-!
Non-vacuity of `nondegeneracy_of_homogeneous_commRing`: the Nondegeneracy Conjecture for
homogeneous parameters over commutative rings that are not fields, with every hypothesis proved.
A purely even datum over `ℤ`, where `2` is not a unit, and a mixed even/odd datum over `ℚ[X]`.
-/

noncomputable section
open OddMath OddMath.SKM OddMath.QuiverHecke
namespace HomogeneousRingNondegeneracyConsumer

/-! ### A purely even datum over `ℤ` -/

/-- One even colour of type `A₁`. -/
private def evenDatum : Datum Unit ℤ where
  cd := {
    root := fun _ => 2
    coroot := fun _ => LinearMap.id
    coroot_root_self := fun _ => rfl }
  isGCM := {
    diag := fun _ => rfl
    offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
    zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 0
  even_of_odd := fun _ _ _ => even_two

private def evenScalars : Scalars evenDatum ℤ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by
    rintro ⟨i, hi⟩
    exact (zero_ne_one hi).elim

private theorem evenHomogeneous : evenScalars.Homogeneous :=
  fun _ _ _ _ _ _ _ h => absurd rfl h

private def evenSymmetrizer : Symmetrizer evenDatum where
  d := fun _ => 1
  pos := fun _ => one_pos
  symm := fun _ _ => rfl

private def evenBubbles : CScalars evenScalars where
  c := fun _ _ => 1
  shift := fun _ _ _ => by simp [evenScalars]

/-- `ℤ` is not a field: `2` is not a unit. -/
example : ¬ IsUnit (2 : ℤ) := by decide

/-- The Nondegeneracy Conjecture for a purely even datum over `ℤ`, with every hypothesis
proved. -/
example : NondegeneracyConjecture evenBubbles :=
  nondegeneracy_of_homogeneous_commRing evenSymmetrizer evenHomogeneous evenBubbles

/-! ### A mixed even/odd datum over `ℚ[X]` -/

private abbrev D := ELV.WeightedAppendFixture.datum

private def sy : Symmetrizer D where
  d := fun i => if i then 1 else 2
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl

private theorem two_isUnit_polynomial : IsUnit (2 : Polynomial ℚ) := by
  simpa using (isUnit_of_invertible (2 : ℚ)).map Polynomial.C

/-- Homogeneous parameters over the polynomial ring `ℚ[X]`, which is not a field. -/
private def Sc : Scalars D (Polynomial ℚ) where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => two_isUnit_polynomial

private theorem hc : Sc.Homogeneous := by
  intro _ _ _ _ _ _ _ h
  exact (h rfl).elim

private def bubbles : CScalars Sc where
  c := fun _ _ => 1
  shift := fun _ _ _ => by simp [Sc]

/-- The datum has an odd colour, and `X` is not a unit in `ℚ[X]`. -/
example : (∃ i, D.parity i = 1) ∧ ¬ IsUnit (Polynomial.X : Polynomial ℚ) :=
  ⟨⟨true, rfl⟩, Polynomial.not_isUnit_X⟩

/-- The Nondegeneracy Conjecture for a mixed even/odd datum over `ℚ[X]`, with every hypothesis
proved. -/
example : NondegeneracyConjecture bubbles :=
  nondegeneracy_of_homogeneous_commRing sy hc bubbles

#print axioms nondegeneracy_of_homogeneous_commRing

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.HomogeneousRingNondegeneracy then
      for name in env.header.moduleData[i]!.constNames do
        for axiomName in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations found"
  logInfo m!"Audited {count} owned declarations: standard axioms only"

end HomogeneousRingNondegeneracyConsumer
