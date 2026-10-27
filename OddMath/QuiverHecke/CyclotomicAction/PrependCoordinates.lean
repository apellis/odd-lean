/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.InputParabolic
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerTargetDot
import OddMath.QuiverHecke.ShuffleBasis

/-!
# Prepend PBW expansion in the Hom algebra

The expansion generators for the input-side decomposition used in KKO I,
arXiv:1206.5933v2, Lemma 8.1. `prependPBWTerm_right` checks the right-old-algebra
compatibility on the original affine algebra, and `prependPBWTerm_corner`
checks the original induction corner. Bijectivity is a written argument in
`docs/Nondegeneracy/PrependCoordinates.md`, not a theorem of this module.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification Categorification.TypeA

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The target word after moving the first strand along an inverse shuffle. -/
def prependShuffleTarget (i : I) {n : ℕ} (u : PrependShuffle n) (s : Word I n) :
    Word I (n + 1) :=
  ⟨tgt (i :: s.1) (cw (canWord (n + 1) u.1⁻¹)), by simp [s.2]⟩

/-- The reduced crossing diagram moving the prepended strand. -/
def prependShuffleHom (i : I) {n : ℕ} (u : PrependShuffle n) (s : Word I n) :
    wordObj D Sc (prependWord i s) ⟶ wordObj D Sc (prependShuffleTarget i u s) :=
  cl D Sc (i :: s.1) _ (cw (canWord (n + 1) u.1⁻¹)) (sChain_pl _ _)

/-- Sum over old words, not over colours of a selected matrix entry. -/
def prependShuffleElement (i : I) {n : ℕ} (u : PrependShuffle n) : Hn D Sc (n + 1) :=
  ∑ s : Word I n, FiniteHomMatrix.single (prependShuffleTarget i u s) (prependWord i s)
    (prependShuffleHom D Sc i u s)

/-- A coefficient acts first, followed by new dots and the moving crossings. -/
def prependPBWTerm (i : I) {n : ℕ} (u : PrependShuffle n) (m : ℕ)
    (b : Hn D Sc n) : Hn D Sc (n + 1) :=
  prependShuffleElement D Sc i u * affineFirstDot D Sc i n ^ m * prependAlgebra D Sc i n b

/-- Right coefficients require associativity, not centrality or a parity assumption. -/
theorem prependPBWTerm_right (i : I) {n : ℕ} (u : PrependShuffle n) (m : ℕ)
    (b r : Hn D Sc n) :
    prependPBWTerm D Sc i u m (b * r) =
      prependPBWTerm D Sc i u m b * prependAlgebra D Sc i n r := by
  simp only [prependPBWTerm, map_mul, mul_assoc]

/-- Every expansion term belongs to the original prepend corner. -/
theorem prependPBWTerm_corner (i : I) {n : ℕ} (u : PrependShuffle n) (m : ℕ)
    (b : Hn D Sc n) :
    prependPBWTerm D Sc i u m b * prependAlgebra D Sc i n 1 =
      prependPBWTerm D Sc i u m b := by
  simp only [prependPBWTerm, mul_assoc, ← map_mul, mul_one]

/-- The same term as an element of the induction corner, with no replacement algebra. -/
def prependPBWCorner (i : I) {n : ℕ} (u : PrependShuffle n) (m : ℕ)
    (b : Hn D Sc n) :
    InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)) :=
  ⟨prependPBWTerm D Sc i u m b, prependPBWTerm_corner D Sc i u m b⟩

/-- Compatibility with the corner's existing right action. -/
theorem prependPBWCorner_right (i : I) {n : ℕ} (u : PrependShuffle n) (m : ℕ)
    (b r : Hn D Sc n) :
    prependPBWCorner D Sc i u m (b * r) = MulOpposite.op r • prependPBWCorner D Sc i u m b := by
  apply Subtype.ext
  exact prependPBWTerm_right D Sc i u m b r

end OddMath.QuiverHecke
