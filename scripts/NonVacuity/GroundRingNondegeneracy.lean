import OddMath

/-! # Ground-ring descent and `K₀ ≅ U̇_ℒ`, on a concrete datum

The two-odd-colour rational datum of `OddMath.SKM.LaurentianK0Examples`, with the scalars of
`OddMath.SKM.DimensionFormulaExamples`. Every hypothesis of
`SKM.nondegeneracyConjecture_of_charZeroField`, `SKM.nondegeneracyConjecture_scalarChange`,
`SKM.homBasisOfCharZeroField` and `QuiverHecke.SerreComplex.gammaInt_bijective_of_charZeroField`
is proved here except the field case of the Nondegeneracy Conjecture, which is the explicit
hypothesis of these results; no instance of the conjecture is asserted.
-/

noncomputable section
namespace NonVacuity.GroundRingNondegeneracy
open CategoryTheory StringDiagrams OddMath OddMath.SKM OddMath.QuiverHecke.SerreComplex
open OddMath.CoveringQuantum.UDot.ContextualExchangeExamples
open OddMath.SKM.LaurentianK0Examples OddMath.SKM.DimensionFormulaExamples

theorem twoOdd_root_independent : LinearIndependent ℤ twoOddDatum.α := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrFun hg i
  cases i <;> simpa [twoOddDatum, OddMath.CoveringQuantum.RootDatum.α] using h

theorem twoOdd_coroot_independent : LinearIndependent ℤ twoOddDatum.cd.coroot := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (fun f : Module.Dual ℤ (Bool → ℤ) ↦ f (Pi.single i 1)) hg
  cases i <;> simpa [twoOddDatum, Pi.single_apply] using h

/-- The descent applies over `ℚ`, where `2` is a unit. -/
example (hK : CharZeroFieldNondegeneracy twoOddDatum.toSKM) :
    NondegeneracyConjecture cScalars :=
  nondegeneracyConjecture_of_charZeroField hK (IsUnit.mk0 _ two_ne_zero) homogeneous cScalars

/-- The conjecture is transported along the ring map `ℚ → ℚ × ℚ`, a ring that is not a
domain. -/
example (hN : NondegeneracyConjecture cScalars) :
    NondegeneracyConjecture (ScalarChange.cScalars twoOddDatum.toSKM
      (RingHom.prod (RingHom.id ℚ) (RingHom.id ℚ)) cScalars) :=
  nondegeneracyConjecture_scalarChange _ hN

/-- The transported scalars stay homogeneous. -/
example : (ScalarChange.scalars twoOddDatum.toSKM
      (RingHom.prod (RingHom.id ℚ) (RingHom.id ℚ)) scalars).Homogeneous :=
  ScalarChange.homogeneous_scalars _ homogeneous

/-- The explicit Hom basis over `ℚ`, given the field case. -/
example (hK : CharZeroFieldNondegeneracy twoOddDatum.toSKM) (ε : Bool) (μ : Bool → ℤ) :
    Module.Basis (Σ _ : (matchingChoice ε).Labels, SYM.CoefficientIndex twoOddDatum.toSKM) ℚ
      ((pres twoOddDatum.toSKM scalars).obj (ob twoOddDatum.toSKM μ (boundary ε)) ⟶
        (pres twoOddDatum.toSKM scalars).obj (ob twoOddDatum.toSKM μ (boundary ε))) :=
  homBasisOfCharZeroField hK (IsUnit.mk0 _ two_ne_zero) homogeneous cScalars rfl μ
    (matchingChoice ε)

/-- `γ` is bijective, given the field case. -/
example (hK : CharZeroFieldNondegeneracy twoOddDatum.toSKM) :
    Function.Bijective (gammaInt twoOddDatum homogeneous cScalars locallyFinite) :=
  gammaInt_bijective_of_charZeroField twoOddDatum homogeneous cScalars locallyFinite hK
    two_ne_zero twoOdd_root_independent twoOdd_coroot_independent

#print axioms OddMath.SKM.nondegeneracyConjecture_of_charZeroField
#print axioms OddMath.QuiverHecke.SerreComplex.gammaInt_bijective_of_charZeroField

end NonVacuity.GroundRingNondegeneracy
