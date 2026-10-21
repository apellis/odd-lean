/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.AlgebraMaps
import OddMath.QuiverHecke.AlgebraExamples

/-! Infinite-colour rational consumers of BE2 (11.7)–(11.8). -/
noncomputable section
open CategoryTheory StringDiagrams
namespace OddMath.QuiverHecke.AlgebraMapExamples
open AlgebraExamples

/-- An upward odd dot retains its degree and parity at every external weight. -/
theorem upward_dot_degree (μ : ℕ → ℤ) (i : ℕ) :
    alphaN datum scalars 1 μ (dot i) ∈ upBidegree datum scalars symmetrizer homogeneous 1 μ (2,1) :=
  alphaN_mem_bidegree datum scalars symmetrizer homogeneous μ (dot_bidegree i)

/-- A crossing of two different colours is also checked. -/
theorem upward_cross_degree (μ : ℕ → ℤ) :
    alphaN datum scalars 2 μ (cross 0 1) ∈
      upBidegree datum scalars symmetrizer homogeneous 2 μ (0,1) :=
  alphaN_mem_bidegree datum scalars symmetrizer homogeneous μ cross_bidegree

/-- The same odd dot in the super-opposite source. -/
def sopDot (i : ℕ) : SopAlgebra datum scalars 1 :=
  FiniteHomMatrix.single (oneWord i) (oneWord i) (SOp.sop (dotHom i))

theorem sopDot_degree (i : ℕ) :
    sopDot i ∈ sopBidegree datum scalars symmetrizer homogeneous 1 (2,1) := by
  let := gradedSupercategory datum symmetrizer scalars homogeneous
  apply FiniteHomMatrix.single_mem_component
  change dotHom i ∈ GradedSupercategory.bidegree (R := ℚ)
    (wordObj datum scalars (oneWord i)) (wordObj datum scalars (oneWord i)) (2,1)
  have h := (dot_bidegree i) (oneWord i, oneWord i)
  simpa only [dot, Hn.single, FiniteHomMatrix.single, DFinsupp.single_eq_same] using h

/-- The downward odd dot also retains its degree and parity. -/
theorem downward_dot_degree (μ : ℕ → ℤ) (i : ℕ) :
    alphaPrimeN datum scalars 1 μ (sopDot i) ∈
      downBidegree datum scalars symmetrizer homogeneous 1 μ (2,1) :=
  alphaPrimeN_mem_bidegree datum scalars symmetrizer homogeneous μ (sopDot_degree i)

/-- Multiplication of actual odd entries is respected in the super-opposite source. -/
theorem downward_dot_product (μ : ℕ → ℤ) (i : ℕ) :
    alphaPrimeN datum scalars 1 μ (sopDot i * sopDot i) =
      alphaPrimeN datum scalars 1 μ (sopDot i) * alphaPrimeN datum scalars 1 μ (sopDot i) :=
  (alphaPrimeN datum scalars 1 μ).map_mul _ _

/-- Both fixed-length maps preserve the empty-word idempotent. -/
example (μ : ℕ → ℤ) :
    alphaN datum scalars 0 μ (Hn.wordIdempotent emptyWord) = FiniteHomMatrix.idem emptyWord :=
  alphaN_wordIdempotent datum scalars 0 μ emptyWord

example (μ : ℕ → ℤ) :
    alphaPrimeN datum scalars 0 μ (FiniteHomMatrix.idem emptyWord) = FiniteHomMatrix.idem emptyWord :=
  alphaPrimeN_wordIdempotent datum scalars 0 μ emptyWord

/-- In particular the downward boundary uses `μ`, not `-μ`, in its rightmost region. -/
example (μ : ℕ → ℤ) :
    (alphaPrime datum scalars μ).obj (SOp.mk ((pres datum scalars).obj (ob datum [0,1]))) =
      (SKM.pres datum scalars).obj (SKM.ob datum μ [SKM.dn 0, SKM.dn 1]) :=
  alphaPrime_obj datum scalars μ [0,1]

example (μ : ℕ → ℤ) (r : ℚ) :
    alphaN datum scalars 1 μ (r • dot 0) = r • alphaN datum scalars 1 μ (dot 0) :=
  alphaN_smul datum scalars 1 μ r _

example (μ : ℕ → ℤ) (r : ℚ) :
    alphaPrimeN datum scalars 1 μ (r • sopDot 0) = r • alphaPrimeN datum scalars 1 μ (sopDot 0) :=
  alphaPrimeN_smul datum scalars 1 μ r _

#print axioms alpha
#print axioms alphaPrime
#print axioms alphaN
#print axioms alphaPrimeN
#print axioms alphaN_mem_bidegree
#print axioms alphaPrimeN_mem_bidegree
#print axioms FiniteHomMatrix.unsopLinear_mul

end OddMath.QuiverHecke.AlgebraMapExamples
