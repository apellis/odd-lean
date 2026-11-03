import OddMath.QuiverHecke.HalfTurn.CoefficientGenerators
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # The half-turn on the literal boundary quotients

SwappedVacuumCoordinates §§5–6 identifies the transformed last-boundary
ideal with the original first-boundary ideal at `parameterTwist D Sc`,
including any specified homogeneous coefficient generators. The proved
affine half-turn therefore descends to a linear equivalence of the actual
quotient Homs. The forward map is induced by `htCoef`; its inverse is the
already constructed `htCoefInv`, retaining every exterior coefficient.
-/
noncomputable section
open CategoryTheory StringDiagrams
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (cutoff : I → ℕ) (T : Set (SKM.SYM D k))
  (hT : ∀ a ∈ T, ∃ q, CoefParity D q a) (s t : List I)

/-- The signed word reversal on the actual transformed and first-boundary
quotients. No comparison with an identical first-boundary source is made. -/
def halfTurnQuotientEquiv :
    ((coefficientObj D Sc s ⟶ coefficientObj D Sc t) ⧸ TransformedIdeal D Sc cutoff T s t) ≃ₗ[k]
      (coefficientObj D (parameterTwist D Sc) t.reverse ⟶
        coefficientObj D (parameterTwist D Sc) s.reverse) ⧸
        (ELVRelationSpan D (parameterTwist D Sc) cutoff t.reverse s.reverse ⊔
          CoefficientGeneratorSpan D (parameterTwist D Sc) T t.reverse s.reverse) :=
  Submodule.Quotient.equiv _ _ (htCoefEquiv D Sc s t)
    (map_htCoef_transformedIdeal_sup D Sc cutoff T hT s t)

/-- The forward quotient map is the class of the literal full-coefficient half-turn. -/
@[simp] theorem halfTurnQuotientEquiv_mk
    (x : coefficientObj D Sc s ⟶ coefficientObj D Sc t) :
    halfTurnQuotientEquiv D Sc cutoff T hT s t (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (htCoef D Sc s t x) := rfl

/-- The inverse quotient map is the class of the existing involutive inverse. -/
@[simp] theorem halfTurnQuotientEquiv_symm_mk
    (y : coefficientObj D (parameterTwist D Sc) t.reverse ⟶
      coefficientObj D (parameterTwist D Sc) s.reverse) :
    (halfTurnQuotientEquiv D Sc cutoff T hT s t).symm (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (htCoefInv D Sc s t y) := rfl

end OddMath.QuiverHecke
