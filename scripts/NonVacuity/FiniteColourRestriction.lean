import OddMath.SKM.FiniteColourRelationsExamples

/-! Finite-subtype restriction for the connected odd/even datum of
Brundan–Ellis Definition 1.5, including the trivial coefficient ring. -/

noncomputable section
namespace OddMath.SKM.FiniteColourRestrictionExamples
open CategoryTheory StringDiagrams
open SerrePolynomialExamples

example : datum.parity false = 1 := rfl

example : diagramColours datum (cupCapDiagram datum false) = {false} :=
  cupCapDiagram_support datum false

example :
    let J := allRelColours datum scalars (.user (cupCapRelation datum false))
    ∃ s : Rel (datum.restrictColours J),
      FiniteColour.relationLabel datum J s = cupCapRelation datum false ∧
      HEq (FiniteColour.linear datum J s.ν s.dom s.cod
        (relation (datum.restrictColours J) (scalars.restrictColours datum J) s))
        (relation datum scalars (cupCapRelation datum false)) :=
  cupCapRelation_restricted datum scalars false

/-- The zero ring still admits the odd datum and its complete syntax. -/
def zeroScalars : Scalars datum (ZMod 1) where
  t _ _ := 1
  t_self _ := rfl
  t_symm_of_d_eq_zero _ _ _ := rfl
  s _ _ _ _ := 0
  s_symm _ _ _ _ := rfl
  s_eq_zero _ _ _ _ _ := rfl
  two_isUnit _ := by
    simpa only [show (2 : ZMod 1) = 1 from Subsingleton.elim _ _] using
      (isUnit_one : IsUnit (1 : ZMod 1))

example : allRelColours datum zeroScalars (.user (cupCapRelation datum false)) = {false} :=
  cupCapRelation_raw_support datum zeroScalars false

/-- Expanded linear support loses the label in the zero ring. -/
example : linearColours datum (relation datum zeroScalars (cupCapRelation datum false)) = ∅ := by
  have hz : relation datum zeroScalars (cupCapRelation datum false) = 0 := by
    apply Finsupp.ext
    intro d
    exact Subsingleton.elim _ _
  rw [hz]
  simp [linearColours, wordColours, cupCapRelation, ob]

example :
    let J := allRelColours datum zeroScalars (.user (cupCapRelation datum false))
    ∃ s : Rel (datum.restrictColours J),
      FiniteColour.relationLabel datum J s = cupCapRelation datum false ∧
      HEq (FiniteColour.linear datum J s.ν s.dom s.cod
        (relation (datum.restrictColours J) (zeroScalars.restrictColours datum J) s))
        (relation datum zeroScalars (cupCapRelation datum false)) :=
  cupCapRelation_restricted datum zeroScalars false

/-- A mixed-colour braid relation with nonzero interior scalar parameters. -/
example :
    let J : Finset Bool := Finset.univ
    let i : J := ⟨false, Finset.mem_univ _⟩
    let j : J := ⟨true, Finset.mem_univ _⟩
    let r : Rel (datum.restrictColours J) := .braidEq i j 0 (by decide)
    HEq (FiniteColour.linear datum J r.ν r.dom r.cod
      (relation (datum.restrictColours J) (scalars.restrictColours datum J) r))
      (relation datum scalars (FiniteColour.relationLabel datum J r)) := by
  exact FiniteColour.linear_relation datum Finset.univ scalars _

end OddMath.SKM.FiniteColourRestrictionExamples
