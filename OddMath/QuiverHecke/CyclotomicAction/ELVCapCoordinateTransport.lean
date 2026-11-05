import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryInputDefect
import OddMath.QuiverHecke.CyclotomicAction.ELVSourcePolynomialQuotient
import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicCrossCoordinates

/-! # Parity transport and representative correction for the cap coordinate

The input-oriented contraction in `DeformedMatrixComparison.md` §3 is
transported by total output parity, including exterior coefficients. The
actual defect on the corrected source section is also compared with the
uncorrected rho-compatible section. Corrected-rho preservation proves that
the zeroth contraction kills Pprime and hence descends to the original
cyclotomic source. Identification with the categorical counit and higher
dotted rows remains separate.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

namespace CyclotomicCrossingTensor

end CyclotomicCrossingTensor

end OddMath.QuiverHecke.ELVOld
