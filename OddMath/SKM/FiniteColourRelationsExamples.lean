/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.FiniteColourRelations
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
  obtain ⟨J, hJ⟩ := mem_finiteColourIdeal D Sc
    ((pres D Sc).whisker_rel_mem_ideal t u [] hw)
  refine ⟨insert i J, Finset.mem_insert_self _ _, ?_⟩
  apply Submodule.span_mono (s := {f | ∃ c : RelationContext D Sc _ _,
    c.colours ⊆ J ∧ c.value = f})
  · rintro f ⟨c, hc, rfl⟩
    exact ⟨c, hc.trans (Finset.subset_insert _ _), rfl⟩
  · exact hJ

/-- Instantiation on a connected odd/even datum over ℚ. -/
example : ∃ J : Finset Bool, false ∈ J := by
  obtain ⟨J, hi, _⟩ := cupCapRelation_finite_witness SerrePolynomialExamples.datum
    SerrePolynomialExamples.scalars (false : Bool)
  exact ⟨J, hi⟩

end OddMath.SKM
