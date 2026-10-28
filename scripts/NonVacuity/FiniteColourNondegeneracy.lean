import OddMath.QuiverHecke.FiniteColourNondegeneracy
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

/-- With infinitely many colours: upward injectivity on every finite restriction gives the
Nondegeneracy Conjecture; a conditional consumer of the reduction. -/
example (h : ∀ (J : Finset ℕ) (tJ t'J : List J),
      wt (oddDatum.restrictColours J) 0 (ups tJ) = wt (oddDatum.restrictColours J) 0 (ups t'J) →
      ∀ μ : ℕ → ℤ, Function.Injective (upwardCoefficientMap (oddDatum.restrictColours J)
        (params.restrictColours oddDatum J) (bubbles.restrictColours oddDatum J params)
        μ tJ t'J)) :
    NondegeneracyConjecture bubbles :=
  nondegeneracy_of_restrictColours_upward oddDatum params bubbles h

/-- The same from vacuum evaluations of every finite restriction. -/
example (h : ∀ (J : Finset ℕ) (tJ t'J : List J),
      wt (oddDatum.restrictColours J) 0 (ups tJ) = wt (oddDatum.restrictColours J) 0 (ups t'J) →
      ∀ (μ : ℕ → ℤ) (d : ℕ), Nonempty (SwappedVacuumEvaluation (oddDatum.restrictColours J)
        (params.restrictColours oddDatum J) (bubbles.restrictColours oddDatum J params)
        μ tJ t'J d)) :
    NondegeneracyConjecture bubbles :=
  nondegeneracy_of_restrictColours_vacuum_evaluations oddDatum params bubbles h

/-- Weights of upward words are unchanged by colour inclusion; no hypothesis. -/
example (μ : ℕ → ℤ) :
    wt (oddDatum.restrictColours {0, 1}) μ (ups [⟨0, by simp⟩, ⟨1, by simp⟩]) =
      wt oddDatum μ (ups [0, 1]) :=
  wt_ups_restrictColours oddDatum {0, 1} μ _

#print axioms nondegeneracy_of_restrictColours_upward
#print axioms nondegeneracy_of_finiteColour_upward
#print axioms nondegeneracy_of_restrictColours_vacuum_evaluations

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.FiniteColourNondegeneracy then
      for name in env.header.moduleData[i]!.constNames do
        for axiomName in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations found"
  logInfo m!"Audited {count} owned declarations: standard axioms only"
