/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.LowerDegreeParameters

/-!
# Truncated Rees parameters

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8 (the
Nondegeneracy Conjecture) for the inhomogeneous parameters of (1.6); J. Brundan, W. Wang,
B. Webster, arXiv:2505.22929v2, Theorem 5.6.

Over a field `K`, the Rees parameters `sᵢⱼ^{pq} h^{deg}` of a lower-degree parameter system
live over `K[h]`. Their images in the truncations `K[h]/(h^N)` are parameters over Artinian
rings, finite over `K`, whose positive-degree part is nilpotent. This module reduces the
graded-coefficient statement to these truncations.

## Main results

* `nondegeneracyConjecture_of_separating`: the conjecture over a ring `R` follows from the
  conjecture after base change along a family of ring maps out of `R` that jointly detect
  zero (no flatness or injectivity of any single map).
* `TruncatedRees.trunc_separate`: the truncations `K[h] → K[h]/(h^N)` jointly detect zero.
* `TruncatedRees.charZeroFieldLowerDegree_of_truncated`,
  `gradedCoefficientNondegeneracy_of_truncated`: the conjecture for the truncated Rees
  parameters over characteristic-zero fields implies the lower-degree field case, and with it
  the graded-coefficient statement `GradedCoefficientNondegeneracy D sy`.
-/

noncomputable section

namespace OddMath.SKM

universe u v w w'

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}

/-- **Joint detection.** If ring maps `gⱼ : R → Sⱼ` jointly detect zero and the conjecture
holds after base change along each of them, it holds over `R`. -/
theorem nondegeneracyConjecture_of_separating {R : Type w} [CommRing R] {Ptwo : Prop}
    {Sc : ScalarData D R Ptwo}
    {cs : CScalars Sc} {J : Type*} {S : J → Type w'} [∀ j, CommRing (S j)]
    (g : ∀ j, R →+* S j) [∀ j, ScalarChange.ZTransport (g j) D Sc]
    (hg : ∀ r : R, (∀ j, g j r = 0) → r = 0)
    (h : ∀ j, NondegeneracyConjecture (ScalarChange.cScalars D (g j) cs)) :
    NondegeneracyConjecture cs := by
  rw [nondegeneracyConjecture_iff_injective]
  intro a b hab μ F
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hpt (j : J) :
      Finsupp.mapRange.addMonoidHom (ScalarChange.symMap (D := D) (g j)).toAddMonoidHom
        z = 0 := by
    have hinj := (nondegeneracyConjecture_iff_injective _).1 (h j) a b hab μ F
    apply hinj
    rw [← ScalarChange.homMap_expansion, hz, map_zero, map_zero]
  ext t
  apply ScalarChange.eq_zero_of_symMap_eq_zero g hg (z t)
  intro j
  simpa using congrArg (fun y => y t) (hpt j)

namespace TruncatedRees

open Polynomial

variable (K : Type w) [CommRing K]

/-- The truncation `K[h]/(h^N)`. -/
abbrev TruncRing (N : ℕ) := K[X] ⧸ Ideal.span {(Polynomial.X : K[X]) ^ N}

/-- The truncation map from the Rees ring `K[h] = MvPolynomial Unit K`. -/
def trunc (N : ℕ) : MvPolynomial Unit K →+* TruncRing K N :=
  (Ideal.Quotient.mk _).comp (MvPolynomial.uniqueAlgEquiv K Unit).toRingEquiv.toRingHom

/-- The truncations jointly detect zero. -/
theorem trunc_separate (r : MvPolynomial Unit K) (h : ∀ N, trunc K N r = 0) : r = 0 := by
  apply (MvPolynomial.uniqueAlgEquiv K Unit).injective
  rw [map_zero]
  ext d
  have hd := h (d + 1)
  rw [trunc, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hd
  rw [coeff_zero]
  exact X_pow_dvd_iff.mp hd d (Nat.lt_succ_self d)

variable (D) (sy : Symmetrizer D)

/-- **The truncated case**: over every field `K` of characteristic zero, for every
lower-degree parameter system, every normalization and every `N`, the conjecture for the
Rees parameters truncated to `K[h]/(h^N)`. -/
def TruncatedReesNondegeneracy : Prop :=
  ∀ (K : Type (max u v)) [Field K] [CharZero K] (Sc : Scalars D K), Sc.LowerDegree sy →
    ∀ (cs : CScalars Sc) (N : ℕ),
      NondegeneracyConjecture
        (ScalarChange.cScalars D (trunc K N) (ReesParameters.cScalars sy cs))

/-- The truncated case implies the lower-degree field case. -/
theorem charZeroFieldLowerDegree_of_truncated (h : TruncatedReesNondegeneracy D sy) :
    LowerDegreeParameters.CharZeroFieldLowerDegreeNondegeneracy D sy := by
  intro K _ _ Sc hl cs
  have hR : NondegeneracyConjecture (ReesParameters.cScalars sy cs) :=
    nondegeneracyConjecture_of_separating (fun N => trunc K N) (trunc_separate K)
      (fun N => h K Sc hl cs N)
  have hS := nondegeneracyConjecture_scalarChange ReesParameters.specialize hR
  have h₂ : IsUnit (2 : K) := isUnit_iff_ne_zero.2 two_ne_zero
  refine nondegeneracyConjecture_congr (eq_true h₂).symm
    (ReesParameters.scalarChange_specialize_t sy Sc)
    (ReesParameters.scalarChange_specialize_s sy Sc) _ cs ?_ hS
  intro μ i
  ext
  simp [ScalarChange.cScalars, ReesParameters.cScalars]

end TruncatedRees

/-- **Reduction to truncated Rees parameters.** The truncated case implies the
graded-coefficient statement. -/
theorem gradedCoefficientNondegeneracy_of_truncated {sy : Symmetrizer D}
    (h : TruncatedRees.TruncatedReesNondegeneracy D sy) :
    GradedCoefficientNondegeneracy.{u, v, w} D sy :=
  gradedCoefficientNondegeneracy_of_charZeroField
    (TruncatedRees.charZeroFieldLowerDegree_of_truncated D sy h)

end OddMath.SKM
