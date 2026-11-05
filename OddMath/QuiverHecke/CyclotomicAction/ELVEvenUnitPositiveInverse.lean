import OddMath.QuiverHecke.CyclotomicAction.ELVEvenCoefficientModule
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenPositiveCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitDotColumns

/-! # Even ordinary-source unit-column inverse
The positive profile of DeformedMatrixComparison §4 uses the canonical
even source, ordinary adjunction unit/dot columns, and signed crossing.
The ordered categorical mate identity remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- For even colours the ordinary columns require no scalar normalization. -/
def evenUnitDotPolynomialMap (i : {i : I // D.parity i = 0}) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] Old D Sc cutoff (v ++ [i.1]) (t ++ [i.1]) :=
  Finsupp.lsum k fun n => inductionUnitDotColumn D Sc cutoff i.1 v t n

@[simp] theorem evenUnitDotPolynomialMap_single (i : {i : I // D.parity i = 0})
    (v t : List I) (n : ℕ) (b : Old D Sc cutoff v t) :
    evenUnitDotPolynomialMap D Sc cutoff i v t (Finsupp.single n b) =
      inductionUnitDotColumn D Sc cutoff i.1 v t n b := by
  rw [evenUnitDotPolynomialMap, Finsupp.lsum_single]

theorem evenUnitDotPolynomialMap_eq (i : {i : I // D.parity i = 0}) (v t : List I) :
    evenUnitDotPolynomialMap D Sc cutoff i v t = unitDotPolynomialMap D Sc cutoff i.1 v t := by
  unfold evenUnitDotPolynomialMap unitDotPolynomialMap
  congr 1
  funext n
  simp only [inductionUnitDotSign, i.property, smul_zero, sign_zero, one_smul]

def evenUnitPositiveMatrixEquiv (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (h : outputSDegree D i.1 v ≤ endpointQPDegree D cutoff i.1 v) :
    ((((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff)) × evenBoundaryRowWindow D Sc cutoff i.1 v t) ≃ₗ[k]
      Old D Sc cutoff (v ++ [i.1]) (t ++ [i.1]) :=
  (((evenSourceEquiv D Sc cutoff i v t).trans (LinearEquiv.neg k)).prodCongr
    (LinearEquiv.refl k (evenBoundaryRowWindow D Sc cutoff i.1 v t))).trans
      (evenPositiveCrossingEquiv D Sc cutoff p i.1 i.property v t h)

/-- The positive columns are the literal ordinary unit/dot columns. -/
theorem evenUnitPositiveMatrixEquiv_apply (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (h : outputSDegree D i.1 v ≤ endpointQPDegree D cutoff i.1 v)
    (z : (((BalancedInduction.restriction (append D Sc cutoff i.1) ⋙
      BalancedInduction.induction (append D Sc cutoff i.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj
        (⟨t⟩ : OldCategory D Sc cutoff)))
    (r : evenBoundaryRowWindow D Sc cutoff i.1 v t) :
    evenUnitPositiveMatrixEquiv D Sc cutoff p i v t h (z, r) =
      -toCyclotomic D Sc cutoff i.1 v t (evenSourceEquiv D Sc cutoff i v t z) +
        evenUnitDotPolynomialMap D Sc cutoff i v t r.val := by
  change toCyclotomic D Sc cutoff i.1 v t (-(evenSourceEquiv D Sc cutoff i v t z)) +
    canonicalAppendTarget D Sc cutoff i.1 v (t ++ [i.1])
      (appendOutputEmbedding D Sc cutoff i.1 v t r.val) = _
  rw [map_neg, evenUnitDotPolynomialMap_eq, unitDotPolynomialMap_eq]
  rfl

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
