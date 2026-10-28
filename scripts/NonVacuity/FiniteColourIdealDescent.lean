import OddMath.SKM.FiniteColourIdealDescent
import OddMath.SKM.FiniteColourRelationsExamples

/-! Two distinct contextual matrix relations in one finite-span derivation,
with nonempty whiskering and interior cup/cap strands. -/
noncomputable section
namespace OddMath.SKM.FiniteColourIdealDescentExamples
open CategoryTheory StringDiagrams FiniteColour SerrePolynomialExamples
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
variable {k : Type w} [CommRing k] (Sc : Scalars D k) (i : I)
local instance : DecidableEq I := Classical.decEq I

private theorem cupWhiskerOK : (ob D (D.α i) []).WhiskerOK
    (ob D (D.α i) [(true, i)]) (wd D 0 [(true, i)]) := by
  refine ⟨ok_wd D _ _, endR_wd D _ _, ?_⟩
  change (sig D).ok (D.α i) (wd D 0 [(true, i)])
  simpa only [wt_cons, wt_nil, sh, Bool.true_eq, ↓reduceIte, add_zero]
    using ok_wd D 0 [(true, i)]

private def cupContext : RelationContext D Sc
    ((ob D (D.α i) []).whisker (ob D (D.α i) [(true, i)]) (wd D 0 [(true, i)]))
    ((ob D (D.α i) []).whisker (ob D (D.α i) [(true, i)]) (wd D 0 [(true, i)])) where
  rel := .user (cupCapRelation D i)
  left := ob D (D.α i) [(true, i)]
  right := wd D 0 [(true, i)]
  compatible := cupWhiskerOK D i
  pre := LinDiagram.of (Diagram.whisker (cupCapDiagram D i) _ _ (cupWhiskerOK D i))
  post := LinDiagram.of (Diagram.whisker (cupCapDiagram D i) _ _ (cupWhiskerOK D i))

private def zeroScalars : Scalars datum (ZMod 1) where
  t _ _ := 1
  t_self _ := rfl
  t_symm_of_d_eq_zero _ _ _ := rfl
  s _ _ _ _ := 0
  s_symm _ _ _ _ := rfl
  s_eq_zero _ _ _ _ _ := rfl
  two_isUnit _ := by
    simpa only [show (2 : ZMod 1) = 1 from Subsingleton.elim _ _] using
      (isUnit_one : IsUnit (1 : ZMod 1))

/-- The other off-diagonal entry of the positive inverse at the simple root. -/
def nextCupRelation : Rel D :=
  .invP₅ i (D.α i) 1 0 (by simp [Datum.h, D.cd.coroot_root_self])
    (by simp [Datum.h, D.cd.coroot_root_self])

/-- Change the raw relation while keeping the nontrivial whiskering and
closed cup/cap diagrams before and after it. -/
def nextCupContext : RelationContext D Sc
    ((ob D (D.α i) []).whisker (ob D (D.α i) [(true, i)]) (wd D 0 [(true, i)]))
    ((ob D (D.α i) []).whisker (ob D (D.α i) [(true, i)]) (wd D 0 [(true, i)])) where
  rel := .user (nextCupRelation D i)
  left := (cupContext D Sc i).left
  right := (cupContext D Sc i).right
  compatible := cupWhiskerOK D i
  pre := (cupContext D Sc i).pre
  post := (cupContext D Sc i).post

/-- A genuine two-generator sum lies in the finite span and lifts into
an actual restricted presentation ideal at one pair of endpoints. -/
theorem two_context_sum_lift :
    let c := cupContext D Sc i
    let d := nextCupContext D Sc i
    let J := c.colours ∪ d.colours
    c.rel ≠ d.rel ∧
      (c.value + d.value ∈ finiteColourIdeal D Sc _ _ J) ∧
      ∃ a' b' : Obj (sig (D.restrictColours J)),
        ∃ (ha : (inclusion D J).obj a' = _)
          (hb : (inclusion D J).obj b' = _),
          ∃ f' : LinDiagram k a' b',
            f' ∈ (pres (D.restrictColours J) (Sc.restrictColours D J)).ideal a' b' ∧
            LinDiagram.cast ((inclusion D J).toLayerMap.lin f') ha hb = c.value + d.value := by
  classical
  dsimp only
  let c := cupContext D Sc i
  let d := nextCupContext D Sc i
  let J := c.colours ∪ d.colours
  have hc : c.colours ⊆ J := Finset.subset_union_left
  have hd : d.colours ⊆ J := Finset.subset_union_right
  have hsum : c.value + d.value ∈ finiteColourIdeal D Sc _ _ J :=
    Submodule.add_mem _ (Submodule.subset_span ⟨c, hc, rfl⟩)
      (Submodule.subset_span ⟨d, hd, rfl⟩)
  obtain ⟨L⟩ := supported_context_lift D J Sc c hc
  obtain ⟨f', hf', ef'⟩ := supported_ideal_lift_at D J Sc L.source L.target
    L.source_eq L.target_eq hsum
  refine ⟨?_, hsum, L.source, L.target, L.source_eq, L.target_eq, f', hf', ef'⟩
  change (Presentation.AllRel.user (cupCapRelation D i) : (pres D Sc).AllRel) ≠
    .user (nextCupRelation D i)
  intro h
  cases h

example := two_context_sum_lift datum scalars false
example := two_context_sum_lift datum scalars true
example := two_context_sum_lift datum
  (zeroScalars) false

#print axioms supported_ideal_lift_at
#print axioms two_context_sum_lift
end OddMath.SKM.FiniteColourIdealDescentExamples
