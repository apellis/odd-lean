import OddMath

/-! Concrete infinite-colour consumers of the two maps of BE2 §11. -/
noncomputable section
open CategoryTheory StringDiagrams
open OddMath.QuiverHecke OddMath.QuiverHecke.AlgebraExamples
open OddMath.QuiverHecke.AlgebraMapExamples

example (μ : ℕ → ℤ) :
    alphaN datum scalars 2 μ (cross 0 1) ∈
      upBidegree datum scalars symmetrizer homogeneous 2 μ (0,1) :=
  upward_cross_degree μ

example (μ : ℕ → ℤ) :
    alphaPrimeN datum scalars 1 μ (sopDot 0) ∈
      downBidegree datum scalars symmetrizer homogeneous 1 μ (2,1) :=
  downward_dot_degree μ 0

example (μ : ℕ → ℤ) :
    (alphaPrime datum scalars μ).obj (SOp.mk ((pres datum scalars).obj (ob datum [0,1]))) =
      (OddMath.SKM.pres datum scalars).obj
        (OddMath.SKM.ob datum μ [OddMath.SKM.dn 0, OddMath.SKM.dn 1]) :=
  alphaPrime_obj datum scalars μ [0,1]

#print axioms alphaN
#print axioms alphaPrimeN
#print axioms alphaN_mem_bidegree
#print axioms alphaPrimeN_mem_bidegree
#print axioms OddMath.FiniteHomMatrix.unsopLinear_mul
