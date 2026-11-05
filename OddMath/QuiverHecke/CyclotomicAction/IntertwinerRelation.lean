/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerParity

/-!
# Moving-strand annihilation of old cyclotomic relations

`append_relation_move_tmul_zero` is the relation-killing input to the
repeated-colour QP induction. It allows arbitrary old factors on both
sides of the first-position relation, and arbitrary ambient left factors.
Naturality transports the entire old expression, including its parity
involution, before the old relation is killed in the prescribed balanced
coefficient target. No polynomial is commuted through bare crossings.

The coefficients here are ordinary polynomials over the even ground ring.
This does not assert the coefficient-superalgebra extension or the QP formula.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification MulOpposite MonoidalCategory
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The bare crossing prefix taking the last strand to the first position.
Its execution order is rightmost crossing first, so algebraically it is
`τ₁ ⋯ τₙ` on a word of length `n + 1`. -/
def lastToFirstHom (i : I) : (ν : List I) →
    (pres D Sc).obj (ob D (ν ++ [i])) ⟶ (pres D Sc).obj (ob D (i :: ν))
  | [] => 𝟙 _
  | j :: ν =>
      ((pres D Sc).obj (ob D [j]) ◁ lastToFirstHom i ν) ≫
        cl D Sc (j :: i :: ν) (i :: j :: ν) [.cross 0]
          (by simpa using sChain_crossAt [] ν j i)

end OddMath.QuiverHecke
