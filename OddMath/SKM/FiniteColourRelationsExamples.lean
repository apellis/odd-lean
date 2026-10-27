/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.FiniteColourRestriction
import OddMath.SKM.SerrePolynomialExamples

/-!
# A finite witness with an interior cup and cap

Brundan–Ellis, *Super Kac–Moody 2-categories*, Definition 1.5,
inversion relation (2.8): its fifth matrix entry has empty bottom and
top words, yet its defining diagram creates and removes colour `i`.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
variable {k : Type w} [CommRing k] (Sc : Scalars D k)
local instance : DecidableEq I := Classical.decEq I

/-- The zero-index positive inverse relation at the simple-root weight.
Both external words are empty; its nontrivial summand is a decorated cup
followed by a cap of colour `i`. -/
def cupCapRelation (i : I) : Rel D :=
  .invP₅ i (D.α i) 0 0 (by simp [Datum.h, D.cd.coroot_root_self])
    (by simp [Datum.h, D.cd.coroot_root_self])

@[simp] theorem cupCapRelation_dom (i : I) : (cupCapRelation D i).dom = [] := rfl
@[simp] theorem cupCapRelation_cod (i : I) : (cupCapRelation D i).cod = [] := rfl

/-- An actual SKM defining relation whose boundary has no colours still
admits a finite colour witness containing its temporary cup/cap colour. -/
theorem cupCapRelation_finite_witness (i : I) :
    let r := cupCapRelation D i
    let t : (pres D Sc).AllRel := .user r
    let u := ob D (D.α i) []
    let hw : t.dom.WhiskerOK u ([] : List (sig D).Colour) :=
      ⟨by trivial, rfl, by trivial⟩
    ∃ J : Finset I, i ∈ J ∧
      LinDiagram.whisker t.rel u [] hw ∈
        finiteColourIdeal D Sc (t.dom.whisker u []) (t.cod.whisker u []) J := by
  dsimp only
  let r := cupCapRelation D i
  let t : (pres D Sc).AllRel := .user r
  let u := ob D (D.α i) []
  have hw : t.dom.WhiskerOK u ([] : List (sig D).Colour) :=
    ⟨by trivial, rfl, by trivial⟩
  let c : RelationContext D Sc (t.dom.whisker u []) (t.cod.whisker u []) :=
    ⟨t, u, [], hw, 𝟙 _, 𝟙 _⟩
  refine ⟨c.colours, ?_, Submodule.subset_span ⟨c, Finset.Subset.rfl, ?_⟩⟩
  · apply Finset.mem_union_right
    simp [c, t, r, allRelColours, cupCapRelation, Rel.colours]
  · simp only [RelationContext.value, c, Category.comp_id]
    exact Category.id_comp _

/-- The raw support is computed from the relation itself, not added to an
unrelated finite witness. This remains true over the zero ring. -/
@[simp] theorem cupCapRelation_raw_support (i : I) :
    allRelColours D Sc (.user (cupCapRelation D i)) = {i} := by
  simp [allRelColours, cupCapRelation, Rel.colours]

/-- The nonidentity diagram of the zero-index inverse relation. -/
def cupCapDiagram (i : I) : ob D (D.α i) [] ⟶ ob D (D.α i) [] :=
  mkD D (D.α i) (dcupL i 0 ++ epsL i 0)
    ((sChain_dcupL i 0).append (sChain_epsL i 0))

/-- Its empty boundaries do not conceal the internal colour from diagram support. -/
@[simp] theorem cupCapDiagram_support (i : I) :
    diagramColours D (cupCapDiagram D i) = {i} := by
  simp [diagramColours, cupCapDiagram, dcupL, epsL, dotsL, layList,
    layerColours, wordColours, lay, Shape.dom, Shape.colours, wd]

/-- The concrete inverse relation restricts to its computed singleton support;
its full linear expression is recovered by inclusion. No ring nontriviality
hypothesis is needed. -/
theorem cupCapRelation_restricted (i : I) :
    let J : Finset I := allRelColours D Sc (.user (cupCapRelation D i))
    ∃ s : Rel (D.restrictColours J),
      FiniteColour.relationLabel D J s = cupCapRelation D i ∧
      HEq (FiniteColour.linear D J s.ν s.dom s.cod
        (relation (D.restrictColours J) (Sc.restrictColours D J) s))
        (relation D Sc (cupCapRelation D i)) := by
  dsimp only
  let J := allRelColours D Sc (.user (cupCapRelation D i))
  have hr : ∀ j ∈ (cupCapRelation D i).colours, j ∈ J := by
    intro j hj
    simpa [J, cupCapRelation, Rel.colours] using hj
  exact ⟨FiniteColour.restrictLabel D J (cupCapRelation D i) hr,
    FiniteColour.relationLabel_restrictLabel D J (cupCapRelation D i) hr,
    FiniteColour.linear_restrictLabel D J Sc (cupCapRelation D i) hr⟩

/-- Instantiation on a connected odd/even datum over ℚ. -/
example : ∃ J : Finset Bool, false ∈ J := by
  obtain ⟨J, hi, _⟩ := cupCapRelation_finite_witness SerrePolynomialExamples.datum
    SerrePolynomialExamples.scalars (false : Bool)
  exact ⟨J, hi⟩

end OddMath.SKM
