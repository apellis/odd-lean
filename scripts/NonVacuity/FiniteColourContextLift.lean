import OddMath.SKM.FiniteColourContextLift
import OddMath.SKM.FiniteColourRelationsExamples

/-! Contextual generators for Brundan–Ellis Definition 1.5: nonidentity
pre/post diagrams, nonempty whiskering, both interchange signs and zero rings. -/

noncomputable section
namespace OddMath.SKM.FiniteColourContextLiftExamples
open CategoryTheory StringDiagrams FiniteColour SerrePolynomialExamples

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
variable {k : Type w} [CommRing k] (Sc : Scalars D k) (i : I)

/-- The cup/cap relation with a strand on either side. -/
theorem cupWhiskerOK : (ob D (D.α i) []).WhiskerOK
    (ob D (D.α i) [(true, i)]) (wd D 0 [(true, i)]) := by
  refine ⟨ok_wd D _ _, endR_wd D _ _, ?_⟩
  change (sig D).ok (D.α i) (wd D 0 [(true, i)])
  simpa only [wt_cons, wt_nil, sh, Bool.true_eq, ↓reduceIte, add_zero]
    using ok_wd D 0 [(true, i)]

/-- Both pre- and post-composition contain an internal closed cup/cap. -/
def cupContext : RelationContext D Sc
    ((ob D (D.α i) []).whisker (ob D (D.α i) [(true, i)]) (wd D 0 [(true, i)]))
    ((ob D (D.α i) []).whisker (ob D (D.α i) [(true, i)]) (wd D 0 [(true, i)])) where
  rel := .user (cupCapRelation D i)
  left := ob D (D.α i) [(true, i)]
  right := wd D 0 [(true, i)]
  compatible := cupWhiskerOK D i
  pre := LinDiagram.of (Diagram.whisker (cupCapDiagram D i) _ _ (cupWhiskerOK D i))
  post := LinDiagram.of (Diagram.whisker (cupCapDiagram D i) _ _ (cupWhiskerOK D i))

theorem cup_context_lift :
    Nonempty (ContextLift D (cupContext D Sc i).colours Sc (cupContext D Sc i)) :=
  supported_context_lift D _ Sc _ Finset.Subset.rfl

/-- Nontrivial diagram syntax is present on both sides of the relation. -/
theorem cup_context_syntax :
    (cupContext D Sc i).left.word.length = 1 ∧ (cupContext D Sc i).right.length = 1 ∧
    (Diagram.layers (Diagram.whisker (cupCapDiagram D i)
      (cupContext D Sc i).left (cupContext D Sc i).right (cupWhiskerOK D i))).length = 2 := by
  simp [cupContext, ob, Diagram.layers_whisker, cupCapDiagram, dcupL, epsL, dotsL, layList]

/-- Raw support survives cancellation of all coefficients. -/
theorem cup_context_raw_support : i ∈ (cupContext D Sc i).colours := by
  classical
  apply Finset.mem_union_right
  simp [cupContext, allRelColours, cupCapRelation, Rel.colours]

/-- Adjacent dots at either parity. -/
def dotSwap : InterchangeData (sig D) :=
  ⟨(wt D (0 : X) [(true, i), (true, i)] : X),
    (.dot i, wt D 0 [(true, i)]), [], (.dot i, 0)⟩

theorem dotSwap_valid : (dotSwap D i).Valid := by
  have h₁ : (dotSwap D i).gh₁ = lay D 0 [] (.dot i) [(true, i)] := rfl
  have h₂ : (dotSwap D i).gh₂ = lay D 0 [(true, i)] (.dot i) [] := rfl
  have h₃ : (dotSwap D i).hg₁ = lay D 0 [(true, i)] (.dot i) [] := rfl
  have h₄ : (dotSwap D i).hg₂ = lay D 0 [] (.dot i) [(true, i)] := rfl
  exact ⟨h₁ ▸ lay_valid D _ _ _ _, h₂ ▸ lay_valid D _ _ _ _,
    h₃ ▸ lay_valid D _ _ _ _, h₄ ▸ lay_valid D _ _ _ _⟩

theorem swapWhiskerOK : (dotSwap D i).dom.WhiskerOK
    (ob D (dotSwap D i).dom.start [(true, i)]) [] :=
  ⟨ok_wd D _ _, endR_wd D _ _, by trivial⟩

/-- A whiskered interchange, with two dot layers before and after it. -/
def swapContext : RelationContext D Sc
    ((dotSwap D i).dom.whisker (ob D (dotSwap D i).dom.start [(true, i)]) [])
    ((dotSwap D i).dom.whisker (ob D (dotSwap D i).dom.start [(true, i)]) []) where
  rel := .interchange (dotSwap D i) (dotSwap_valid D i)
  left := ob D (dotSwap D i).dom.start [(true, i)]
  right := []
  compatible := swapWhiskerOK D i
  pre := LinDiagram.of (Diagram.whisker (InterchangeData.ghDiagram (dotSwap_valid D i))
    _ _ (swapWhiskerOK D i))
  post := LinDiagram.of (Diagram.whisker (InterchangeData.hgDiagram (dotSwap_valid D i))
    _ _ (swapWhiskerOK D i))

theorem swap_context_lift :
    Nonempty (ContextLift D (swapContext D Sc i).colours Sc (swapContext D Sc i)) :=
  supported_context_lift D _ Sc _ Finset.Subset.rfl

/-- This consumer extracts ideal generation and exact recovery, not just existence. -/
theorem swap_generator_recovery :
    ∃ L : ContextLift D (swapContext D Sc i).colours Sc (swapContext D Sc i),
      (pres (D.restrictColours (swapContext D Sc i).colours)
        (Sc.restrictColours D (swapContext D Sc i).colours)).IdealGen L.context.value ∧
      LinDiagram.cast ((inclusion D (swapContext D Sc i).colours).toLayerMap.lin
        L.context.value) L.source_eq L.target_eq = (swapContext D Sc i).value := by
  obtain ⟨L⟩ := swap_context_lift D Sc i
  exact ⟨L, L.idealGen, L.value_eq⟩

example : (dotSwap datum false).sign = -1 := by decide
example : (dotSwap datum true).sign = 1 := by decide
example : Nonempty (ContextLift datum (swapContext datum scalars false).colours scalars
    (swapContext datum scalars false)) := swap_context_lift datum scalars false
example : Nonempty (ContextLift datum (swapContext datum scalars true).colours scalars
    (swapContext datum scalars true)) := swap_context_lift datum scalars true
example : Nonempty (ContextLift datum (cupContext datum scalars false).colours scalars
    (cupContext datum scalars false)) := cup_context_lift datum scalars false

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

example : Nonempty (ContextLift datum (cupContext datum zeroScalars false).colours zeroScalars
    (cupContext datum zeroScalars false)) := cup_context_lift datum zeroScalars false
example : false ∈ (cupContext datum zeroScalars false).colours :=
  cup_context_raw_support datum zeroScalars false
example : Nonempty (ContextLift datum (swapContext datum zeroScalars false).colours zeroScalars
    (swapContext datum zeroScalars false)) := swap_context_lift datum zeroScalars false
example : Nonempty (ContextLift datum (swapContext datum zeroScalars true).colours zeroScalars
    (swapContext datum zeroScalars true)) := swap_context_lift datum zeroScalars true

#print axioms supported_allRel_lift
#print axioms inclusion_whiskerOK_iff
#print axioms supported_linear_lift_at
#print axioms inclusion_whisker_at
#print axioms supported_context_lift
#print axioms ContextLift.idealGen
#print axioms cup_context_lift
#print axioms cup_context_syntax
#print axioms cup_context_raw_support
#print axioms swap_generator_recovery

end OddMath.SKM.FiniteColourContextLiftExamples
