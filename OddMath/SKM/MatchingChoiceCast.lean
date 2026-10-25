import OddMath.SKM.MatchingTargetExpansion
import OddMath.SKM.MatchingChoiceTransition

/-! Transport matching choices and their coefficient expansions along boundary equalities. -/
noncomputable section
namespace OddMath.SKM.MatchingBasisChoice
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {a b a' b' : List (Letter I)}

def cast (F : MatchingBasisChoice a b) (ha : a = a') (hb : b = b') :
    MatchingBasisChoice a' b' := ha ▸ hb ▸ F

def castLabelsEquiv (F : MatchingBasisChoice a b) (ha : a = a') (hb : b = b') :
    F.Labels ≃ (F.cast ha hb).Labels := by
  subst a' b'
  exact Equiv.refl _

@[simp] theorem cast_layers (F : MatchingBasisChoice a b) (ha : a = a') (hb : b = b')
    (t : F.Labels) :
    (F.cast ha hb).layers (F.castLabelsEquiv ha hb t) = F.layers t := by
  subst a' b'
  rfl

@[simp] theorem cast_openDots (F : MatchingBasisChoice a b) (ha : a = a') (hb : b = b')
    (t : F.Labels) :
    (F.cast ha hb).openDots (F.castLabelsEquiv ha hb t) = F.openDots t := by
  subst a' b'
  rfl

variable {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} (cs : CScalars Sc) (μ : X)

theorem cast_targetCoefficientMap (F : MatchingBasisChoice a b)
    (ha : a = a') (hb : b = b') (t : F.Labels) (p : SYM D k) :
    (F.cast ha hb).targetCoefficientMap cs μ (F.castLabelsEquiv ha hb t) p =
      wordCast μ ha hb (F.targetCoefficientMap cs μ t p) := by
  subst a' b'
  rfl

theorem cast_expansion (F : MatchingBasisChoice a b)
    (ha : a = a') (hb : b = b') (v : F.Labels →₀ SYM D k) :
    (F.cast ha hb).expansion cs μ (v.mapDomain (F.castLabelsEquiv ha hb)) =
      wordCast μ ha hb (F.expansion cs μ v) := by
  subst a' b'
  simp only [cast, castLabelsEquiv, Equiv.refl_apply]
  rw [show (fun x : F.Labels => x) = id from rfl, Finsupp.mapDomain_id]
  rfl

theorem cast_targetExpansion (F : MatchingBasisChoice a b)
    (ha : a = a') (hb : b = b') (v : F.Labels →₀ SYM D k) :
    (F.cast ha hb).targetExpansion cs μ (v.mapDomain (F.castLabelsEquiv ha hb)) =
      wordCast μ ha hb (F.targetExpansion cs μ v) := by
  subst a' b'
  simp only [cast, castLabelsEquiv, Equiv.refl_apply]
  rw [show (fun x : F.Labels => x) = id from rfl, Finsupp.mapDomain_id]
  rfl

theorem cast_expansion_injective_iff (F : MatchingBasisChoice a b)
    (ha : a = a') (hb : b = b') :
    Function.Injective ((F.cast ha hb).expansion cs μ) ↔ Function.Injective (F.expansion cs μ) := by
  subst a' b'
  rfl

end OddMath.SKM.MatchingBasisChoice
