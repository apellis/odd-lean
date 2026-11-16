/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.TruncatedReesNondegeneracy
import OddMath.SKM.BWWReesParameters

/-! # The conjecture for Brundan–Wang–Webster parameters

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture, for the parameters of J. Brundan, W. Wang, B. Webster,
arXiv:2505.22929v2, §2.2: the polynomials `Qᵢⱼ(u, v)` with a coefficient `tᵢⱼ;ₚq` for every
`0 ≤ p < dᵢⱼ`, `0 ≤ q < dⱼᵢ` (`SKM.BWWScalars`), the pure coefficients (`p = 0` or `q = 0`)
included. Brundan–Wang–Webster, Theorem 5.6, is the ordinary (even) basis theorem for
symmetrizable data and such parameters over an `ℕ`-graded coefficient ring, homogeneous for
the total grading; this file proves the odd/mixed conjecture for that class of parameters,
for symmetrizable data and coefficient rings with `2` invertible.

The truncated Rees parameters `(BWWReesParameters.scalars sy Sc).map (trunc k N)` of a
lower-degree parameter system over a commutative ring `k` live over `k[h]/(h^N)`, which is
graded in degrees `0, …, N` by `k`-submodules (`truncGrading`). Their units have degree `0`
and every nonzero coefficient below the corners has its coefficient degree
(`bwwTruncatedRees_c_mem`): in the interior by the lower-degree condition, and for `p = 0` or
`q = 0` because that degree is positive (`SKM.coefficientDegree_pos_of_pure`). So
`nondegeneracy_of_graded_base` applies (`bwwTruncatedReesCase`), and the reductions of
`SKM/BWWReesParameters.lean` give the lower-degree and graded cases.

## Main results

* `bwwTruncatedReesCase`: `SKM.BWWParameterProperty.TruncatedReesCase` for the conjecture.
* `bwwLowerDegreeNondegeneracy`: the conjecture for every lower-degree
  Brundan–Wang–Webster parameter system over every commutative ring with `2` invertible.
* `bwwGradedNondegeneracy`: the conjecture for every graded-homogeneous Brundan–Wang–Webster
  parameter system over every `ℕ`-graded commutative ring with `2` invertible (the parameter
  generality of Brundan–Wang–Webster, Theorem 5.6).

These statements carry no hypothesis beyond the symmetrizer and the stated condition on the
parameters. Colours, weights and the coefficient ring are taken in one universe, as for the
swapped route.
-/

-- `letI` keeps the graded-algebra instance available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section

namespace OddMath.QuiverHecke

universe u

variable {I X : Type u} [AddCommGroup X]

open SKM.TruncatedRees (trunc)
open MvPolynomial (C)

/-- The coefficients of the truncated Brundan–Wang–Webster Rees parameters below the corners
lie in their coefficient degree for the grading of `k[h]/(h^N)` with `h` in degree `1`. -/
theorem bwwTruncatedRees_c_mem {D : SKM.Datum I X} (sy : SKM.Symmetrizer D) {k : Type u}
    [CommRing k] {Sc : SKM.BWWScalars D k} (hl : Sc.LowerDegree sy) (N : ℕ) (i j : I)
    (p q : ℕ) (hij : i ≠ j) (hp : (p : ℤ) < D.d i j) (hq : (q : ℤ) < D.d j i)
    (hs : ((SKM.BWWReesParameters.scalars sy Sc).map (trunc k N)).c i j p q ≠ 0) :
    ((SKM.BWWReesParameters.scalars sy Sc).map (trunc k N)).c i j p q ∈
      truncGrading k N (SKM.coefficientDegree sy i j p q) := by
  have hc : Sc.c i j p q ≠ 0 := fun h0 => hs (by
    simp [SKM.BWWScalars.map_c, SKM.BWWReesParameters.scalars, h0])
  have hnn : 0 ≤ SKM.coefficientDegree sy i j p q := by
    by_cases hpq : p = 0 ∨ q = 0
    · exact (SKM.coefficientDegree_pos_of_pure sy hp hq hpq).le
    · exact hl i j p q hij hp hq hc
  have hm : C (Sc.c i j p q) * MvPolynomial.X () ^ SKM.BWWReesParameters.exponent sy i j p q ∈
      reesGrading k (SKM.coefficientDegree sy i j p q) :=
    C_mul_X_pow_mem_reesGrading _ _ (by
      rw [SKM.BWWReesParameters.exponent_of_lt sy hp hq, Int.toNat_of_nonneg hnn])
  exact SKM.GradedImage.map_mem_image (f := truncAlg k N) hm

/-- The units of the truncated Brundan–Wang–Webster Rees parameters have degree `0`. -/
theorem bwwTruncatedRees_t_mem {D : SKM.Datum I X} (sy : SKM.Symmetrizer D) {k : Type u}
    [CommRing k] (Sc : SKM.BWWScalars D k) (N : ℕ) (i j : I) :
    ((((SKM.BWWReesParameters.scalars sy Sc).map (trunc k N)).t i j :
      (SKM.TruncatedRees.TruncRing k N)ˣ) : SKM.TruncatedRees.TruncRing k N) ∈
      truncGrading k N 0 :=
  SKM.GradedImage.map_mem_image (f := truncAlg k N) (C_mem_reesGrading ((Sc.t i j : kˣ) : k))

/-- **The truncated Rees case** for the Brundan–Wang–Webster parameters: over every commutative
ring `k` with `2` invertible, for every lower-degree parameter system, every normalization and
every `N`, the Nondegeneracy Conjecture (Brundan–Ellis, arXiv:1701.04133v2, §8) holds for the
Rees parameters truncated to `k[h]/(h^N)`, pure coefficients included. -/
theorem bwwTruncatedReesCase (D : SKM.Datum I X) (sy : SKM.Symmetrizer D) :
    (SKM.BWWParameterProperty.interiorNondegeneracy.{u, u, u} D).TruncatedReesCase sy := by
  intro k _ _ Sc hl cs N
  letI := truncGradedAlgebra k N
  have h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) N → truncGrading k N m = ⊥ := fun m hm => by
    by_cases h : m < 0
    · exact truncGrading_eq_bot_of_neg k N h
    · exact truncGrading_eq_bot_of_le k N (not_lt.mp fun h' => hm ⟨not_lt.mp h, h'.le⟩)
  exact nondegeneracy_of_graded_base sy (truncGrading k N)
    (Sc := ((SKM.BWWReesParameters.scalars sy Sc).map (trunc k N)).toScalars)
    (bwwTruncatedRees_t_mem sy Sc N) (bwwTruncatedRees_c_mem sy hl N) N h𝒜 _

/-- **The conjecture for lower-degree Brundan–Wang–Webster parameters** (Brundan–Ellis,
arXiv:1701.04133v2, §8, for the parameters of Brundan–Wang–Webster, arXiv:2505.22929v2, §2.2):
for a symmetrizable datum, over every commutative ring `k` with `2` invertible, for every
parameter system whose nonzero interior coefficients have nonnegative coefficient degree and
every normalization, the Nondegeneracy Conjecture holds for `Sc.toScalars`, whose
presentation keeps every coefficient below the corners, the pure ones included. -/
theorem bwwLowerDegreeNondegeneracy (D : SKM.Datum I X) (sy : SKM.Symmetrizer D) (k : Type u)
    [CommRing k] (h₂ : IsUnit (2 : k)) (Sc : SKM.BWWScalars D k) (hl : Sc.LowerDegree sy)
    (cs : SKM.CScalars Sc.toScalars) : SKM.NondegeneracyConjecture cs :=
  SKM.BWWParameterProperty.lowerDegreeCase_of_truncatedReesCase _ sy
    (bwwTruncatedReesCase D sy) k h₂ Sc hl cs

/-- **The conjecture for graded Brundan–Wang–Webster parameters** (Brundan–Ellis,
arXiv:1701.04133v2, §8, in the parameter generality of Brundan–Wang–Webster,
arXiv:2505.22929v2, §2.2 and Theorem 5.6): for a symmetrizable datum, over every `ℕ`-graded
commutative ring `k` with `2` invertible, for every parameter system with the `tᵢⱼ` in degree
`0` and each nonzero coefficient of `u^p v^q` below the corners in its coefficient degree, and
every normalization, the Nondegeneracy Conjecture holds for `Sc.toScalars`. -/
theorem bwwGradedNondegeneracy (D : SKM.Datum I X) (sy : SKM.Symmetrizer D) (k : Type u)
    [CommRing k] {σ : Type u} [SetLike σ k] [AddSubgroupClass σ k] (𝒜 : ℕ → σ)
    [GradedRing 𝒜] (h₂ : IsUnit (2 : k)) (Sc : SKM.BWWScalars D k)
    (hg : Sc.GradedHomogeneous sy 𝒜) (cs : SKM.CScalars Sc.toScalars) :
    SKM.NondegeneracyConjecture cs :=
  bwwLowerDegreeNondegeneracy D sy k h₂ Sc hg.lowerDegree cs

end OddMath.QuiverHecke
