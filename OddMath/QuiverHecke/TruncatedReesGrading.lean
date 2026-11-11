/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CoefficientGrading
import OddMath.SKM.TruncatedReesParameters
import OddMath.SKM.GradedImage

/-!
# Graded quiver Hecke supercategories over the truncated Rees rings

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5,
the parameters (1.6) and the degree table after (1.31); J. Brundan, W. Wang, B. Webster,
arXiv:2505.22929v2, §2.2.

The truncation `K[h]/(h^N)` of the Rees ring is graded by the images of the homogeneous parts
of `K[h]` (`h` in degree `1`), since the kernel `(h^N)` is homogeneous. The truncated Rees
parameters of a lower-degree parameter system are coefficient-graded homogeneous for this
grading, so the quiver Hecke supercategory over `K[h]/(h^N)`, viewed as `K`-linear, is a graded
supercategory. These are the Artinian graded rings of route step 1 of
`docs/Nondegeneracy/Phase2Plan.md`, with the graded structure of route step 2.

## Main definitions and results

* `QuiverHecke.truncAlg`: the truncation `K[h] → K[h]/(h^N)` as a `K`-algebra map.
* `QuiverHecke.ker_truncAlg`: its kernel is `(h^N)`.
* `QuiverHecke.truncGrading`, `QuiverHecke.truncGradedAlgebra`: the grading of `K[h]/(h^N)`.
* `QuiverHecke.isHomogeneous_truncatedRees`: the quiver Hecke presentation with the truncated
  Rees parameters is coefficient-graded homogeneous.
* `QuiverHecke.truncatedReesGradedSupercategory`: the graded supercategory structure over `K`.
-/

noncomputable section

namespace OddMath.QuiverHecke

open CategoryTheory StringDiagrams OddMath.Diagrams

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
variable (K : Type w) [CommRing K] (sy : SKM.Symmetrizer D)

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The truncation `K[h] → K[h]/(h^N)` as a `K`-algebra map. -/
def truncAlg (N : ℕ) : MvPolynomial Unit K →ₐ[K] SKM.TruncatedRees.TruncRing K N :=
  (Ideal.Quotient.mkₐ K _).comp (MvPolynomial.uniqueAlgEquiv K Unit).toAlgHom

theorem truncAlg_apply (N : ℕ) (x : MvPolynomial Unit K) :
    truncAlg K N x = SKM.TruncatedRees.trunc K N x :=
  rfl

theorem truncAlg_surjective (N : ℕ) : Function.Surjective (truncAlg K N) :=
  (Ideal.Quotient.mkₐ_surjective K _).comp (MvPolynomial.uniqueAlgEquiv K Unit).surjective

/-- The kernel of the truncation is `(h^N)`. -/
theorem ker_truncAlg (N : ℕ) :
    RingHom.ker (truncAlg K N) = Ideal.span {(MvPolynomial.X () : MvPolynomial Unit K) ^ N} := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  change Ideal.Quotient.mk _ (MvPolynomial.uniqueAlgEquiv K Unit x) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    ← map_dvd_iff (MvPolynomial.uniqueAlgEquiv K Unit), map_pow]
  rw [show (MvPolynomial.uniqueAlgEquiv K Unit) (MvPolynomial.X ()) = Polynomial.X from
    MvPolynomial.eval₂_X _ _ _]

theorem isHomogeneous_ker_truncAlg (N : ℕ) :
    (RingHom.ker (truncAlg K N)).IsHomogeneous (reesGrading K) := by
  rw [ker_truncAlg]
  refine Ideal.homogeneous_span _ _ fun x hx => ?_
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨(N : ℤ), (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr
    (by simpa using (MvPolynomial.isWeightedHomogeneous_X K (fun _ : Unit => (1 : ℤ)) ()).pow N)⟩

/-- The grading of `K[h]/(h^N)` with `h` in degree `1`. -/
def truncGrading (N : ℕ) : ℤ → Submodule K (SKM.TruncatedRees.TruncRing K N) :=
  SKM.GradedImage.image (reesGrading K) (truncAlg K N)

/-- `K[h]/(h^N)` is a graded `K`-algebra. -/
@[instance_reducible]
def truncGradedAlgebra (N : ℕ) : GradedAlgebra (truncGrading K N) :=
  SKM.GradedImage.gradedAlgebra _ _ (truncAlg_surjective K N) (isHomogeneous_ker_truncAlg K N)

variable {K}

/-- The truncated Rees parameters. -/
abbrev truncatedReesScalars (Sc : SKM.Scalars D K) (N : ℕ) :
    SKM.Scalars D (SKM.TruncatedRees.TruncRing K N) :=
  (SKM.ScalarChange.scalars D (SKM.TruncatedRees.trunc K N)
    (SKM.ReesParameters.scalars sy Sc)).withProp fun h => by
      simpa [map_ofNat] using
        (Sc.two_isUnit h).map ((SKM.TruncatedRees.trunc K N).comp MvPolynomial.C)

theorem truncatedReesScalars_t (Sc : SKM.Scalars D K) (N : ℕ) (i j : I) :
    (truncatedReesScalars D sy Sc N).t i j =
      Units.map (SKM.TruncatedRees.trunc K N).toMonoidHom
        ((SKM.ReesParameters.scalars sy Sc).t i j) := rfl

theorem truncatedReesScalars_s (Sc : SKM.Scalars D K) (N : ℕ) (i j : I) (p q : ℕ) :
    (truncatedReesScalars D sy Sc N).s i j p q =
      SKM.TruncatedRees.trunc K N ((SKM.ReesParameters.scalars sy Sc).s i j p q) := rfl

theorem truncatedRees_t_mem (Sc : SKM.Scalars D K) (N : ℕ) (i j : I) :
    (((truncatedReesScalars D sy Sc N).t i j : (SKM.TruncatedRees.TruncRing K N)ˣ) :
      SKM.TruncatedRees.TruncRing K N) ∈ truncGrading K N 0 := by
  rw [truncatedReesScalars_t, Units.coe_map]
  exact SKM.GradedImage.map_mem_image (f := truncAlg K N) (rees_t_mem D sy Sc i j)

theorem truncatedRees_s_mem {Sc : SKM.Scalars D K} (hl : Sc.LowerDegree sy) (N : ℕ) (i j : I)
    (p q : ℕ) (hij : i ≠ j) (hp' : (p : ℤ) < D.d i j) (hq' : (q : ℤ) < D.d j i)
    (hs : (truncatedReesScalars D sy Sc N).s i j p q ≠ 0) :
    (truncatedReesScalars D sy Sc N).s i j p q ∈
      truncGrading K N (SKM.coefficientDegree sy i j p q) := by
  rw [truncatedReesScalars_s] at hs ⊢
  have hs' : (SKM.ReesParameters.scalars sy Sc).s i j p q ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hs
    exact hs rfl
  exact SKM.GradedImage.map_mem_image (f := truncAlg K N)
    (rees_s_mem D sy hl i j p q hij hp' hq' hs')

/-- **Truncated Rees parameters.** For lower-degree parameters over `K`, the quiver Hecke
presentation with the Rees parameters truncated to `K[h]/(h^N)` is coefficient-graded
homogeneous for `h` in degree `1`. -/
theorem isHomogeneous_truncatedRees {Sc : SKM.Scalars D K} (hl : Sc.LowerDegree sy) (N : ℕ) :
    CoefficientGrading.IsHomogeneous (truncGrading K N) (gdeg D sy)
      (pres D (truncatedReesScalars D sy Sc N)) :=
  letI := truncGradedAlgebra K N
  isHomogeneous_coefficientGraded D sy (truncGrading K N) _
    (truncatedRees_t_mem D sy Sc N) (truncatedRees_s_mem D sy hl N)

/-- **Graded quiver Hecke supercategory over `K[h]/(h^N)`.** For lower-degree parameters over
`K`, the quiver Hecke supercategory with the truncated Rees parameters, viewed as `K`-linear,
is a graded supercategory with `h` in degree `1`. -/
@[instance_reducible]
def truncatedReesGradedSupercategory {Sc : SKM.Scalars D K} (hl : Sc.LowerDegree sy) (N : ℕ) :
    letI := Diagrams.Linear.restrictScalars K (SKM.TruncatedRees.TruncRing K N)
      (H D (truncatedReesScalars D sy Sc N))
    letI := Diagrams.Supercategory.restrictScalars K (SKM.TruncatedRees.TruncRing K N)
      (H D (truncatedReesScalars D sy Sc N))
    GradedSupercategory K (H D (truncatedReesScalars D sy Sc N)) :=
  letI := truncGradedAlgebra K N
  CoefficientGrading.gradedSupercategory (isParityHomogeneous D _)
    (isHomogeneous_truncatedRees D sy hl N)

end OddMath.QuiverHecke
