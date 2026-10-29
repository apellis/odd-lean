import OddMath.QuiverHecke.SwappedConditionalNondegeneracy
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke OddMath.SKM
open scoped Classical
private def oddDatum : Datum ℕ (ℕ → ℤ) where
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
    split <;> simp

private def params : Scalars oddDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

private def bubbles : CScalars params where
  c := fun _ _ => 1
  shift := fun _ _ _ => by simp [params]

variable (B : Type) [BicategoryStruct.{0, 0} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℚ (a ⟶ b)]
  [∀ a b : B, Supercategory ℚ (a ⟶ b)] [TwoSupercategory ℚ B]
  [∀ a b : B, PiSupercategory ℚ (a ⟶ b)]

/-- Swapped vacuum observations at every upward word pair give the Nondegeneracy Conjecture
for an odd datum; a conditional consumer of the end-to-end reduction. -/
example (h : ∀ (t t' : List ℕ), wt oddDatum 0 (ups t) = wt oddDatum 0 (ups t') →
      ∀ (μ : ℕ → ℤ) (d : ℕ),
        Nonempty (SwappedVacuumObservation B oddDatum params bubbles μ t t' d)) :
    NondegeneracyConjecture bubbles :=
  nondegeneracy_of_swapped_vacuum_observations B oddDatum params bubbles h

/-- The same from observations for the finite restrictions of the infinite colour set. -/
example (h : ∀ (J : Finset ℕ) (tJ t'J : List J),
      wt (oddDatum.restrictColours J) 0 (ups tJ) = wt (oddDatum.restrictColours J) 0 (ups t'J) →
      ∀ (μ : ℕ → ℤ) (d : ℕ), Nonempty (SwappedVacuumObservation B (oddDatum.restrictColours J)
        (params.restrictColours oddDatum J) (bubbles.restrictColours oddDatum J params)
        μ tJ t'J d)) :
    NondegeneracyConjecture bubbles :=
  nondegeneracy_of_restrictColours_swapped_vacuum_observations B oddDatum params bubbles h

#print axioms nondegeneracy_of_swapped_vacuum_observations
#print axioms nondegeneracy_of_restrictColours_swapped_vacuum_observations

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.SwappedConditionalNondegeneracy then
      for name in env.header.moduleData[i]!.constNames do
        for axiomName in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations found"
  logInfo m!"Audited {count} owned declarations: standard axioms only"
