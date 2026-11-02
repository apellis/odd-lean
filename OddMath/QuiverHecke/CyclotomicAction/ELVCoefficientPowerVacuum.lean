import OddMath.QuiverHecke.CyclotomicAction.ELVEmptyCoefficientEmbedding
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerGrading
import OddMath.QuiverHecke.CyclotomicAction.ELVFullyFaithfulInduction

/-! # The regular coefficient-power vacuum on the old category

The literal vacuum with coefficient module A/T in
`SwappedNondegeneracy.md`, §2. Balanced induction extends the actual
regular quotient module from the empty coefficient subcategory. The
fully faithful unit compares its empty component with the original A/T.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- The actual old-category extension of the literal regular A/T
coefficient module, using the established balanced induction. -/
def coefficientPowerVacuum : Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  BalancedInduction.induced (emptyCoefficientEmbedding D Sc cutoff)
    (coefficientPowerRegular D cutoff L)

/-- The chosen ordinary induction unit identifies the original regular
coefficient module with the restriction of the old vacuum. -/
def coefficientPowerVacuumUnitIso : coefficientPowerRegular (k := k) D cutoff L ≅
    (BalancedInduction.restriction (emptyCoefficientEmbedding D Sc cutoff)).obj
      (coefficientPowerVacuum D Sc cutoff L) :=
  BalancedInduction.fullyFaithfulUnitIso (emptyCoefficientEmbedding D Sc cutoff)
    (coefficientPowerRegular D cutoff L)

end OddMath.QuiverHecke.ELVOld
