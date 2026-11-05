/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendCrossingTriangular
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendDescent

/-!
# Output polynomials and the append crossing dot defect

The output maps in `DeformedMackeyBoundary.md` (4) and the local dot identity
preceding (8), over the full ELV old quotient. These use postcomposition by
the output moving dot, not the input moving-dot operator. The crossing
formula retains total old-Hom parity, including exterior coefficients.
This module does not assert the global corrected polynomial projection.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Output polynomial reconstruction with coefficients in the old quotient. -/
def appendOutputEmbedding (i : I) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] AppendTarget D Sc cutoff i v (t ++ [i]) :=
  Finsupp.lsum k fun m => appendPair D Sc cutoff 0 i
    (appendMovingPower D Sc cutoff i t m)

@[simp] theorem appendOutputEmbedding_single (i : I) (v t : List I)
    (m : ℕ) (g : hom D Sc cutoff v t) :
    appendOutputEmbedding D Sc cutoff i v t
      (Finsupp.single m ((ideal D Sc cutoff v t).mkQ g)) =
    appendProjection D Sc cutoff i v (t ++ [i])
      (rightContext D Sc cutoff [i] v t g ≫ appendMovingPower D Sc cutoff i t m) := by
  simp only [appendOutputEmbedding, Finsupp.lsum_single, appendPair_mk, twist_zero]

/-- The prescribed output polynomial map descends coefficientwise. -/
theorem appendOutputEmbedding_map (i : I) (v t : List I)
    (f : ℕ →₀ hom D Sc cutoff v t) :
    appendOutputEmbedding D Sc cutoff i v t
      (Finsupp.mapRange.linearMap (ideal D Sc cutoff v t).mkQ f) =
    appendProjection D Sc cutoff i v (t ++ [i]) (appendOutputPolynomial D Sc cutoff i v t f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m g =>
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      appendOutputEmbedding_single, appendOutputPolynomial_single]

/-- Exponent translation on output coefficients. -/
def appendOutputShift (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  Finsupp.lsum k fun m => Finsupp.lsingle (m + 1)

/-- The crossing generator with arbitrary old input and output arrows. -/
def appendCrossingClass (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    AppendTarget D Sc cutoff i v (t ++ [i]) :=
  appendProjection D Sc cutoff i v (t ++ [i])
    (rightContext D Sc cutoff [i] _ _ r ≫ affineUnit D Sc cutoff _ _
      (crossLast D Sc s i i) ≫ rightContext D Sc cutoff [i] _ _ g)

end OddMath.QuiverHecke.ELVOld
