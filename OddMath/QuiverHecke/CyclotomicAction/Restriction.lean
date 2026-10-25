/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.Induction
import Categorification.Algebra.InductionAlongRes

/-!
# Underlying cyclotomic induction and restriction

Ports the ungraded functors and the left adjunction from
`Categorification/KLR/CyclotomicAction/Restriction.lean`. They use the actual
cyclotomic quotients of `QuiverHecke.Hn`. This is not the parity-enriched
adjunction or local inversion: odd dots and crossings require homogeneous
transformations, not ordinary module-category natural transformations.
-/

noncomputable section
open CategoryTheory
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Restriction is truncation by the unit image, with the lower algebra action. -/
abbrev cyclotomicRestriction (i : I) (a : I → _root_.Polynomial k) (n : ℕ) :=
  Categorification.InductionAlong.resFunctor
    (cyclotomicAppend D Sc i a n :
      CyclotomicAlgebra D Sc a n →ₙ+* CyclotomicAlgebra D Sc a (n + 1))

/-- The underlying induction–restriction adjunction holds over any coefficient
ring, without a flatness hypothesis. It does not assert the KKO decomposition. -/
def cyclotomicIndResAdjunction (i : I) (a : I → _root_.Polynomial k) (n : ℕ) :
    cyclotomicInduction D Sc i a n ⊣ cyclotomicRestriction D Sc i a n :=
  Categorification.InductionAlong.adjunction
    (cyclotomicAppend D Sc i a n :
      CyclotomicAlgebra D Sc a n →ₙ+* CyclotomicAlgebra D Sc a (n + 1))

end OddMath.QuiverHecke
