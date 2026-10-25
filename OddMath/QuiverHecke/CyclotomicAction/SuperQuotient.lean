/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.Parity
import OddMath.QuiverHecke.CyclotomicAction.Induction
import StringDiagrams.Super.BalancedTensor

/-!
# The actual cyclotomic quotient as a superalgebra

Ports the graded-algebra input to
`Categorification/KLR/CyclotomicAction/Induction.lean`. The superspace carrier
is the already constructed cyclotomic quotient, not a new presentation.
-/

noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

private theorem affine_algProj_eq (n : ℕ) (p : ZMod 2) (x : Hn D Sc n) :
    SuperBimodule.algProj (affineParity D Sc n) p x =
      GradedAlgebra.proj (affineParity D Sc n) p x := by
  induction x using DirectSum.Decomposition.inductionOn (affineParity D Sc n) with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | @homogeneous q x =>
    by_cases h : q = p
    · subst q
      rw [SuperBimodule.algProj_of_mem _ x.property]
      simp [GradedAlgebra.proj_apply, DirectSum.decompose_coe]
    · rw [SuperBimodule.algProj_of_mem_ne _ x.property h]
      simp only [GradedAlgebra.proj_apply, DirectSum.decompose_coe,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), ZeroMemClass.coe_zero]

/-- The genuine cyclotomic ideal, stable under parity projection. -/
def cyclotomicGradedSubmodule (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    SVec.GradedSubmodule (SuperBimodule.regularSVec (affineParity D Sc (n + 1))) where
  toSubmodule := (cyclotomicIdeal D Sc a n).restrictScalars k
  odd_mem x hx := by
    change SuperBimodule.algProj (affineParity D Sc (n + 1)) 1 x ∈ _
    rw [affine_algProj_eq]
    exact cyclotomicIdeal_homogeneous_of_polynomials D Sc a ha n 1 hx

/-- Parity on the existing cyclotomic quotient. -/
def cyclotomicSuperspace (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) : SVec k :=
  SVec.quot (SuperBimodule.regularSVec (affineParity D Sc (n + 1)))
    (cyclotomicGradedSubmodule D Sc a ha n)

/-- Homogeneous submodules of the actual quotient algebra. -/
def cyclotomicParity (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (p : ZMod 2) :
    Submodule k (CyclotomicAlgebra D Sc a n) :=
  (cyclotomicSuperspace D Sc a ha n).part p

theorem cyclotomicMk_parity (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) {p : ZMod 2}
    {x : Hn D Sc (n + 1)} (hx : x ∈ affineParity D Sc (n + 1) p) :
    cyclotomicMk D Sc a n x ∈ cyclotomicParity D Sc a ha n p :=
  SVec.quotMkFun_mem_part _ _ ((SuperBimodule.mem_regularSVec_part_iff _).mpr hx)

/-- Every homogeneous quotient vector has a homogeneous affine representative. -/
theorem cyclotomicParity_lift (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) {p : ZMod 2}
    {x : CyclotomicAlgebra D Sc a n} (hx : x ∈ cyclotomicParity D Sc a ha n p) :
    ∃ y ∈ affineParity D Sc (n + 1) p, cyclotomicMk D Sc a n y = x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨SuperBimodule.algProj (affineParity D Sc (n + 1)) p y,
    SuperBimodule.algProj_mem _ _ _, ?_⟩
  change SVec.quotMkFun (SuperBimodule.regularSVec (affineParity D Sc (n + 1)))
    (cyclotomicGradedSubmodule D Sc a ha n) (SuperBimodule.algProj _ p y) =
    SVec.quotMkFun (SuperBimodule.regularSVec (affineParity D Sc (n + 1)))
      (cyclotomicGradedSubmodule D Sc a ha n) y
  rw [← SuperBimodule.regularSVec_proj, ← SVec.quot_proj_mk]
  exact (SVec.mem_part_iff _).mp hx

instance cyclotomicParity_graded (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    GradedAlgebra (cyclotomicParity D Sc a ha n) where
  __ := (SVec.isInternal_part (cyclotomicSuperspace D Sc a ha n)).chooseDecomposition
  one_mem := cyclotomicMk_parity D Sc a ha n (SetLike.one_mem_graded _)
  mul_mem p q := by
    intro x y hx hy
    obtain ⟨x, hx', rfl⟩ := cyclotomicParity_lift D Sc a ha n hx
    obtain ⟨y, hy', rfl⟩ := cyclotomicParity_lift D Sc a ha n hy
    rw [← map_mul]
    exact cyclotomicMk_parity D Sc a ha n (SetLike.GradedMul.mul_mem hx' hy')

omit [Fintype I] in
/-- The affine strand inclusion is parity preserving. -/
theorem appendAlgebra_parity (i : I) (n : ℕ) {p : ZMod 2} {x : Hn D Sc n}
    (hx : x ∈ affineParity D Sc n p) :
    appendAlgebra D Sc i n x ∈ affineParity D Sc (n + 1) p := by
  change appendLinear D Sc i n x ∈ _
  rw [FiniteHomMatrix.eq_sum_single x, map_sum]
  apply Submodule.sum_mem
  intro q _
  rw [appendLinear_single]
  apply FiniteHomMatrix.single_mem_component
  exact MonoidalSupercategory.whiskerRight_mem ((pres D Sc).obj (ob D [i])) (hx q)

/-- The genuine cyclotomic inclusion is an even nonunital algebra map. -/
theorem cyclotomicAppend_parity (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) {p : ZMod 2}
    {x : CyclotomicAlgebra D Sc a n} (hx : x ∈ cyclotomicParity D Sc a ha n p) :
    cyclotomicAppend D Sc i a n x ∈ cyclotomicParity D Sc a ha (n + 1) p := by
  obtain ⟨x, hx', rfl⟩ := cyclotomicParity_lift D Sc a ha n hx
  change cyclotomicAppendLinear D Sc i a n (cyclotomicMk D Sc a n x) ∈ _
  rw [cyclotomicAppendLinear_mk]
  exact cyclotomicMk_parity D Sc a ha (n + 1) (appendAlgebra_parity D Sc i (n + 1) hx')

/-- The supercategory of left supermodules over the actual quotient. -/
abbrev CyclotomicSupermodules (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :=
  SuperBimodule (cyclotomicParity D Sc a ha n) (trivialGrading k)

end OddMath.QuiverHecke
