import OddMath.SKM.FiniteColourContextRestriction
import OddMath.SKM.FiniteColourRelationsExamples

/-! Supported free-diagram and signed-interchange restriction for
Brundan–Ellis Definition 1.5, including an internal closed cup/cap and
raw support over the zero coefficient ring. -/

noncomputable section
namespace OddMath.SKM.FiniteColourContextRestrictionExamples
open CategoryTheory StringDiagrams FiniteColour SerrePolynomialExamples

/-- The empty boundary does not remove the internal odd colour. -/
theorem closed_cup_cap_lift :
    ∃ (a b : Obj (sig (datum.restrictColours {false}))) (f : a ⟶ b)
      (ha : (inclusion datum {false}).obj a = ob datum (datum.α false) [])
      (hb : (inclusion datum {false}).obj b = ob datum (datum.α false) []),
      Diagram.cast ((inclusion datum {false}).toLayerMap.map f) ha hb =
        cupCapDiagram datum false :=
  supported_diagram_lift datum {false} (cupCapDiagram datum false)
    (by rw [cupCapDiagram_support])

/-- Two dots on adjacent odd strands, at the original region labels. -/
def oddSwap : InterchangeData (sig datum) :=
  ⟨(wt datum (0 : Bool → ℤ) [(true, false), (true, false)] : Bool → ℤ),
    (.dot false, wt datum 0 [(true, false)]), [], (.dot false, 0)⟩

theorem oddSwap_valid : oddSwap.Valid := by
  have h₁ : oddSwap.gh₁ = lay datum 0 [] (.dot false) [(true, false)] := rfl
  have h₂ : oddSwap.gh₂ = lay datum 0 [(true, false)] (.dot false) [] := rfl
  have h₃ : oddSwap.hg₁ = lay datum 0 [(true, false)] (.dot false) [] := rfl
  have h₄ : oddSwap.hg₂ = lay datum 0 [] (.dot false) [(true, false)] := rfl
  exact ⟨h₁ ▸ lay_valid datum _ _ _ _, h₂ ▸ lay_valid datum _ _ _ _,
    h₃ ▸ lay_valid datum _ _ _ _, h₄ ▸ lay_valid datum _ _ _ _⟩

theorem oddSwap_sign : oddSwap.sign = -1 := by decide

theorem oddSwap_support : interchangeColours datum oddSwap = {false} := by
  simp [interchangeColours, oddSwap, Shape.colours, wordColours]

/-- Both odd vertices, both ordered lists, and the negative interchange sign
survive restriction; the full rational linear expression is recovered. -/
theorem oddSwap_lift :
    ∃ (y : InterchangeData (sig (datum.restrictColours {false}))) (hy : y.Valid)
      (ha : (inclusion datum {false}).obj y.dom = oddSwap.dom)
      (hb : (inclusion datum {false}).obj y.cod = oddSwap.cod),
      includeInterchange datum {false} y = oddSwap ∧ y.sign = oddSwap.sign ∧
      [y.gh₁, y.gh₂].map (inclusion datum {false}).layer = [oddSwap.gh₁, oddSwap.gh₂] ∧
      [y.hg₁, y.hg₂].map (inclusion datum {false}).layer = [oddSwap.hg₁, oddSwap.hg₂] ∧
      LinDiagram.cast ((inclusion datum {false}).toLayerMap.lin (InterchangeData.rel ℚ hy)) ha hb =
        InterchangeData.rel ℚ oddSwap_valid :=
  supported_interchange_lift datum {false} oddSwap (by rw [oddSwap_support]) oddSwap_valid

example :
    let y := restrictInterchange datum {false} oddSwap (by rw [oddSwap_support])
    (sig (datum.restrictColours {false})).odd y.g = true ∧
      (sig (datum.restrictColours {false})).odd y.h = true :=
  restrictInterchange_odd datum {false} oddSwap (by rw [oddSwap_support])

example :
    (restrictInterchange datum {false} oddSwap (by rw [oddSwap_support])).sign = -1 :=
  (restrictInterchange_sign datum {false} oddSwap (by rw [oddSwap_support])).trans oddSwap_sign

/-- A zero coefficient ring does not change the underlying interchange syntax. -/
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

theorem zero_ring_internal_support :
    linearColours datum (relation datum zeroScalars (cupCapRelation datum false)) = ∅ ∧
      diagramColours datum (cupCapDiagram datum false) = {false} ∧
      allRelColours datum zeroScalars (.user (cupCapRelation datum false)) = {false} := by
  refine ⟨?_, cupCapDiagram_support datum false, cupCapRelation_raw_support datum zeroScalars false⟩
  have hz : relation datum zeroScalars (cupCapRelation datum false) = 0 := by
    apply Finsupp.ext
    intro d
    exact Subsingleton.elim _ _
  rw [hz]
  simp [linearColours, wordColours, cupCapRelation, ob]

/-- The interchange lift works even when its linear expression is zero. -/
theorem zero_ring_interchange_lift :
    ∃ (y : InterchangeData (sig (datum.restrictColours {false}))) (hy : y.Valid)
      (ha : (inclusion datum {false}).obj y.dom = oddSwap.dom)
      (hb : (inclusion datum {false}).obj y.cod = oddSwap.cod),
      includeInterchange datum {false} y = oddSwap ∧ y.sign = oddSwap.sign ∧
      [y.gh₁, y.gh₂].map (inclusion datum {false}).layer = [oddSwap.gh₁, oddSwap.gh₂] ∧
      [y.hg₁, y.hg₂].map (inclusion datum {false}).layer = [oddSwap.hg₁, oddSwap.hg₂] ∧
      LinDiagram.cast ((inclusion datum {false}).toLayerMap.lin
        (InterchangeData.rel (ZMod 1) hy)) ha hb = InterchangeData.rel (ZMod 1) oddSwap_valid :=
  supported_interchange_lift datum {false} oddSwap (by rw [oddSwap_support]) oddSwap_valid

example : allRelColours datum zeroScalars (.interchange oddSwap oddSwap_valid) = {false} :=
  oddSwap_support

end OddMath.SKM.FiniteColourContextRestrictionExamples
