import OddMath.QuiverHecke.CyclotomicAction.ELVUnitDotColumns
import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedSourceLinearEquiv
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalPositiveCrossing

/-! # Ordinary-source positive unit-column inverse

DeformedMatrixComparison (4) transports the positive inverse of
DeformedRouquierMatrix, section 4, to the ordinary induction-restriction
source and ordinary unit/dot columns. The first entry is explicitly minus
the balanced crossing after the canonical source equivalence; its ordered
mate identification remains separate. No coefficient elimination is repeated.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Positive inverse on the ordinary source, with the prescribed crossing sign. -/
def unitPositiveMatrixEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    ((((BalancedInduction.induction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) × offDiagonalBoundaryRowWindow D Sc cutoff j v t) ≃ₗ[k]
      Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) :=
  (((shiftedSourceCanonicalEquiv D Sc cutoff j v t).trans (LinearEquiv.neg k)).prodCongr
    (LinearEquiv.refl k (offDiagonalBoundaryRowWindow D Sc cutoff j v t))).trans
      (offDiagonalPositiveCrossingEquiv D Sc cutoff p j v t h)

/-- The columns are the normalized ordinary adjunction unit and induction-dot
powers; the first entry is the fixed signed canonical crossing. -/
theorem unitPositiveMatrixEquiv_apply (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v)
    (z : ((BalancedInduction.induction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff))
    (r : offDiagonalBoundaryRowWindow D Sc cutoff j v t) :
    unitPositiveMatrixEquiv D Sc cutoff p j v t h (z, r) =
      -toCyclotomic D Sc cutoff j.1 v t (shiftedSourceCanonicalEquiv D Sc cutoff j v t z) +
        unitDotPolynomialMap D Sc cutoff j.1 v t r.val := by
  change toCyclotomic D Sc cutoff j.1 v t
      (-(shiftedSourceCanonicalEquiv D Sc cutoff j v t z)) +
    canonicalAppendTarget D Sc cutoff j.1 v (t ++ [j.1])
      (appendOutputEmbedding D Sc cutoff j.1 v t r.val) = _
  rw [map_neg, unitDotPolynomialMap_eq]
  rfl

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
