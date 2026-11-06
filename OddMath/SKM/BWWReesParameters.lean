/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BWWGradedParameters
import OddMath.SKM.TruncatedReesParameters

/-!
# Lower-degree Brundan–Wang–Webster parameters and the Rees reduction

J. Brundan, W. Wang, B. Webster, arXiv:2505.22929v2, §2.2 (the parameters `tᵢⱼ;ᵣₛ` for
`0 ≤ r < dᵢⱼ`, `0 ≤ s < dⱼᵢ` over an `ℕ`-graded ring) and Theorem 5.6; J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8 (the Nondegeneracy Conjecture).

This is the Brundan–Wang–Webster version of the reductions of `GradedParameters.lean` and
`TruncatedReesParameters.lean`. Every map below is a ring map; no grading of the presented
category is used.

* `BWWScalars.map`, `BWWScalars.mapCScalars`: base change of parameters and normalizations.
* `BWWScalars.LowerDegree`: every nonzero coefficient of `u^p v^q` below the corners has
  nonnegative coefficient degree. Only the interior monomials are constrained
  (`lowerDegree_iff_interior`): the monomials with `p = 0` or `q = 0`, including the constant
  term, have positive coefficient degree. Graded-homogeneous parameters are lower-degree
  (`GradedHomogeneous.lowerDegree`), and on Brundan–Ellis parameters the condition is
  `ScalarData.LowerDegree` (`ScalarData.toBWW_lowerDegree_iff`).
* `BWWReesParameters.scalars`: over `k[h]`, the coefficient of `u^p v^q` below the corners is
  multiplied by `h` to the power of its coefficient degree. For lower-degree parameters this is
  graded homogeneous (`BWWReesParameters.gradedHomogeneous`); at `h = 1` it returns the given
  parameters (`BWWReesParameters.map_specialize`). In the truncation `k[h]/(h^N)` the pure
  coefficients become nilpotent.
* `BWWParameterProperty`: a property of parameters with normalizations, over rings with `2`
  invertible, that is stable under base change and detected by jointly separating base changes.
  The Nondegeneracy Conjecture has both properties (`nondegeneracyConjecture_scalarChange`,
  `nondegeneracyConjecture_of_separating`); `BWWParameterProperty.interiorNondegeneracy` is the
  Brundan–Ellis conjecture for the interior part `BWWScalars.toScalars`.
* `BWWParameterProperty.lowerDegreeCase_of_truncatedReesCase`: for such a property, the case of
  the truncated Rees parameters over every commutative ring with `2` invertible implies the case
  of every lower-degree parameter system over every such ring, and with it
  (`gradedCase_of_lowerDegreeCase`) the graded case of Brundan–Wang–Webster §2.2.
-/

noncomputable section

namespace OddMath.SKM

universe u v w w'

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}

namespace BWWScalars

section Map

variable {R : Type w} {S : Type w'} [CommRing R] [CommRing S] (f : R →+* S)

/-- Base change of Brundan–Wang–Webster parameters along a ring map. -/
def map (Sc : BWWScalars D R) : BWWScalars D S where
  t i j := Units.map f.toMonoidHom (Sc.t i j)
  t_self i := by rw [Sc.t_self, map_one]
  t_symm_of_d_eq_zero i j h := by rw [Sc.t_symm_of_d_eq_zero i j h]
  c i j p q := f (Sc.c i j p q)
  c_symm i j p q := by rw [Sc.c_symm i j p q]
  c_parity i j p q h := by rw [Sc.c_parity i j p q h, map_zero]
  c_self i p q := by rw [Sc.c_self i p q, map_zero]
  c_corner i j hij := by rw [Sc.c_corner i j hij]; rfl
  c_outside i j p q h := by rw [Sc.c_outside i j p q h, map_zero]
  c_top i j q hq := by rw [Sc.c_top i j q hq, map_zero]
  two_isUnit h := by
    convert (Sc.two_isUnit h).map f using 1
    exact (map_ofNat f 2).symm

@[simp] theorem map_t (Sc : BWWScalars D R) (i j : I) :
    (Sc.map f).t i j = Units.map f.toMonoidHom (Sc.t i j) := rfl

@[simp] theorem map_c (Sc : BWWScalars D R) (i j : I) (p q : ℕ) :
    (Sc.map f).c i j p q = f (Sc.c i j p q) := rfl

/-- The normalization units, transported along a ring map. -/
def mapCScalars {Sc : BWWScalars D R} (cs : CScalars Sc.toScalars) :
    CScalars (Sc.map f).toScalars where
  c μ i := Units.map f.toMonoidHom (cs.c μ i)
  shift μ i j := by
    rw [cs.shift, map_mul]
    rfl

@[simp] theorem mapCScalars_c {Sc : BWWScalars D R} (cs : CScalars Sc.toScalars) (μ : X)
    (i : I) : (mapCScalars f cs).c μ i = Units.map f.toMonoidHom (cs.c μ i) := rfl

end Map

variable {k : Type w} [CommRing k]

/-- Lower-degree parameters: every nonzero coefficient of `u^p v^q` with `p < dᵢⱼ`,
`q < dⱼᵢ` has nonnegative coefficient degree, i.e. `dᵢp + dⱼq ≤ dᵢdᵢⱼ`. No grading of `k` is
involved. -/
def LowerDegree (sy : Symmetrizer D) (Sc : BWWScalars D k) : Prop :=
  ∀ i j (p q : ℕ), i ≠ j → (p : ℤ) < D.d i j → (q : ℤ) < D.d j i → Sc.c i j p q ≠ 0 →
    0 ≤ coefficientDegree sy i j p q

/-- The lower-degree condition only constrains the interior monomials: those with `p = 0` or
`q = 0` below the corners have positive coefficient degree (`coefficientDegree_pos_of_pure`). -/
theorem lowerDegree_iff_interior (sy : Symmetrizer D) (Sc : BWWScalars D k) :
    Sc.LowerDegree sy ↔
      ∀ i j (p q : ℕ), i ≠ j → 0 < p → (p : ℤ) < D.d i j → 0 < q → (q : ℤ) < D.d j i →
        Sc.c i j p q ≠ 0 → 0 ≤ coefficientDegree sy i j p q := by
  refine ⟨fun h i j p q hij _ hp _ hq hs => h i j p q hij hp hq hs,
    fun h i j p q hij hp hq hs => ?_⟩
  by_cases hpq : p = 0 ∨ q = 0
  · exact (coefficientDegree_pos_of_pure sy hp hq hpq).le
  · push Not at hpq
    exact h i j p q hij (Nat.pos_of_ne_zero hpq.1) hp (Nat.pos_of_ne_zero hpq.2) hq hs

/-- Lower-degree parameters stay lower-degree under every ring map. -/
theorem LowerDegree.map {R : Type w} {S : Type w'} [CommRing R] [CommRing S] (f : R →+* S)
    {sy : Symmetrizer D} {Sc : BWWScalars D R} (h : Sc.LowerDegree sy) :
    (Sc.map f).LowerDegree sy := by
  intro i j p q hij hp hq hs
  exact h i j p q hij hp hq fun h0 => hs (by rw [map_c, h0, map_zero])

/-- Graded-homogeneous parameters are lower-degree parameters. -/
theorem GradedHomogeneous.lowerDegree {σ : Type*} [SetLike σ k] {sy : Symmetrizer D}
    {𝒜 : ℕ → σ} {Sc : BWWScalars D k} (h : Sc.GradedHomogeneous sy 𝒜) : Sc.LowerDegree sy := by
  intro i j p q hij hp hq hs
  obtain ⟨n, hn, -⟩ := h.2 i j p q hij hp hq hs
  rw [← hn]
  exact Int.natCast_nonneg n

end BWWScalars

/-- On Brundan–Ellis parameters the lower-degree condition is `ScalarData.LowerDegree`. -/
theorem ScalarData.toBWW_lowerDegree_iff {k : Type w} [CommRing k] (sy : Symmetrizer D)
    (Sc : Scalars D k) : Sc.toBWW.LowerDegree sy ↔ Sc.LowerDegree sy := by
  rw [BWWScalars.lowerDegree_iff_interior]
  constructor
  · intro h i j p q hp hp' hq hq' hs
    have hij : i ≠ j := by
      rintro rfl
      have := D.d_self i
      omega
    have hdn : (D.dn i j : ℤ) = D.d i j := D.dn_cast hij
    have hdn' : (D.dn j i : ℤ) = D.d j i := D.dn_cast (Ne.symm hij)
    have hc := ScalarData.toBWW_c_of_interior Sc hij hp (by omega) hq (by omega)
    rw [← hc] at hs
    exact h i j p q hij hp hp' hq hq' hs
  · intro h i j p q hij hp hp' hq hq' hs
    have hdn : (D.dn i j : ℤ) = D.d i j := D.dn_cast hij
    have hdn' : (D.dn j i : ℤ) = D.d j i := D.dn_cast (Ne.symm hij)
    have hc := ScalarData.toBWW_c_of_interior Sc hij hp (by omega) hq (by omega)
    rw [hc] at hs
    exact h i j p q hp hp' hq hq' hs

namespace BWWReesParameters

open MvPolynomial

variable (sy : Symmetrizer D) {k : Type w} [CommRing k]

/-- The power of `h` attached to the monomial `u^p v^q` of `Qᵢⱼ`: its coefficient degree
(truncated at zero) below the corners, and `0` elsewhere. -/
def exponent (i j : I) (p q : ℕ) : ℕ :=
  if (p : ℤ) < D.d i j ∧ (q : ℤ) < D.d j i then (coefficientDegree sy i j p q).toNat else 0

theorem exponent_symm (i j : I) (p q : ℕ) : exponent sy i j p q = exponent sy j i q p := by
  unfold exponent
  by_cases h : (p : ℤ) < D.d i j ∧ (q : ℤ) < D.d j i
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩, coefficientDegree_symm sy i j p q]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.2, h'.1⟩]

theorem exponent_corner (i j : I) : exponent sy i j (D.dn i j) 0 = 0 := by
  unfold exponent
  rw [if_neg]
  rintro ⟨h, -⟩
  have := Int.self_le_toNat (D.d i j)
  simp only [Datum.dn] at h
  omega

theorem exponent_of_lt {i j : I} {p q : ℕ} (hp : (p : ℤ) < D.d i j) (hq : (q : ℤ) < D.d j i) :
    exponent sy i j p q = (coefficientDegree sy i j p q).toNat := by
  unfold exponent
  rw [if_pos ⟨hp, hq⟩]

/-- The Rees parameters over `k[h] = MvPolynomial Unit k`: the units and the corners are
unchanged, and the coefficient of `u^p v^q` below the corners is multiplied by `h` to the power
of its coefficient degree. -/
def scalars (Sc : BWWScalars D k) : BWWScalars D (MvPolynomial Unit k) where
  t i j := Units.map (C : k →+* MvPolynomial Unit k).toMonoidHom (Sc.t i j)
  t_self i := by rw [Sc.t_self, map_one]
  t_symm_of_d_eq_zero i j h := by rw [Sc.t_symm_of_d_eq_zero i j h]
  c i j p q := C (Sc.c i j p q) * X () ^ exponent sy i j p q
  c_symm i j p q := by rw [Sc.c_symm i j p q, exponent_symm sy i j p q]
  c_parity i j p q h := by rw [Sc.c_parity i j p q h, map_zero, zero_mul]
  c_self i p q := by rw [Sc.c_self i p q, map_zero, zero_mul]
  c_corner i j hij := by rw [Sc.c_corner i j hij, exponent_corner, pow_zero, mul_one]; rfl
  c_outside i j p q h := by rw [Sc.c_outside i j p q h, map_zero, zero_mul]
  c_top i j q hq := by rw [Sc.c_top i j q hq, map_zero, zero_mul]
  two_isUnit h := by
    convert (Sc.two_isUnit h).map (C : k →+* MvPolynomial Unit k) using 1
    exact (map_ofNat _ 2).symm

/-- The normalization units, transported along the constants. -/
def cScalars {Sc : BWWScalars D k} (cs : CScalars Sc.toScalars) :
    CScalars (scalars sy Sc).toScalars where
  c μ i := Units.map (C : k →+* MvPolynomial Unit k).toMonoidHom (cs.c μ i)
  shift μ i j := by
    rw [cs.shift, map_mul]
    rfl

/-- For lower-degree parameters the Rees parameters are graded homogeneous for the grading of
`k[h]` by degree. -/
theorem gradedHomogeneous {Sc : BWWScalars D k} (hl : Sc.LowerDegree sy) :
    (scalars sy Sc).GradedHomogeneous sy (homogeneousSubmodule Unit k) := by
  refine ⟨fun i j => ?_, fun i j p q hij hp hq hs => ?_⟩
  · exact (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ _)
  · have hs' : Sc.c i j p q ≠ 0 := fun h0 => hs (by simp [scalars, h0])
    refine ⟨(coefficientDegree sy i j p q).toNat,
      Int.toNat_of_nonneg (hl i j p q hij hp hq hs'), ?_⟩
    change C (Sc.c i j p q) * X () ^ exponent sy i j p q ∈ _
    rw [exponent_of_lt sy hp hq]
    exact (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C_mul_X_pow (Sc.c i j p q) () _)

/-- Specializing the Rees parameters at `h = 1` recovers the given parameters. -/
theorem map_specialize (Sc : BWWScalars D k) :
    (scalars sy Sc).map ReesParameters.specialize = Sc := by
  refine BWWScalars.ext ?_ ?_
  · funext i j
    ext
    simp [scalars, BWWScalars.map]
  · funext i j p q
    simp [scalars, BWWScalars.map]

end BWWReesParameters

open TruncatedRees (trunc trunc_separate)

variable (D) in
/-- A property of Brundan–Wang–Webster parameters with normalizations, over commutative rings
with `2` invertible, that is stable under base change (`map`) and detected by every family of
base changes that jointly detect zero (`separating`). The Nondegeneracy Conjecture is the
property in view. -/
structure BWWParameterProperty where
  /-- The property. -/
  holds : ∀ {k : Type w} [CommRing k] (Sc : BWWScalars D k), CScalars Sc.toScalars → Prop
  /-- Stability under base change. -/
  map : ∀ {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S), IsUnit (2 : R) →
    ∀ (Sc : BWWScalars D R) (cs : CScalars Sc.toScalars), holds Sc cs →
      holds (Sc.map f) (BWWScalars.mapCScalars f cs)
  /-- Joint detection. -/
  separating : ∀ {R : Type w} [CommRing R], IsUnit (2 : R) →
    ∀ (Sc : BWWScalars D R) (cs : CScalars Sc.toScalars) {J : Type} {S : J → Type w}
      [∀ j, CommRing (S j)] (g : ∀ j, R →+* S j), (∀ r : R, (∀ j, g j r = 0) → r = 0) →
      (∀ j, holds (Sc.map (g j)) (BWWScalars.mapCScalars (g j) cs)) → holds Sc cs

namespace BWWParameterProperty

variable (P : BWWParameterProperty.{u, v, w} D) (sy : Symmetrizer D)

/-- The property depends only on the parameters and the values of the normalization units. -/
theorem holds_congr {k : Type w} [CommRing k] {Sc Sc' : BWWScalars D k} (e : Sc = Sc')
    (cs : CScalars Sc.toScalars) (cs' : CScalars Sc'.toScalars)
    (hc : ∀ μ i, (cs.c μ i : k) = cs'.c μ i) (h : P.holds Sc cs) : P.holds Sc' cs' := by
  subst e
  obtain ⟨c, hcs⟩ := cs
  obtain ⟨c', hcs'⟩ := cs'
  obtain rfl : c = c' := funext fun μ => funext fun i => Units.ext (hc μ i)
  exact h

/-- **The truncated Rees case**: over every commutative ring `k` with `2` invertible, for every
lower-degree parameter system, every normalization and every `N`, the property for the Rees
parameters truncated to `k[h]/(h^N)`. There the coefficients below the corners, in particular
all pure coefficients, are multiples of the nilpotent `h`. -/
def TruncatedReesCase : Prop :=
  ∀ (k : Type w) [CommRing k], IsUnit (2 : k) → ∀ (Sc : BWWScalars D k), Sc.LowerDegree sy →
    ∀ (cs : CScalars Sc.toScalars) (N : ℕ),
      P.holds ((BWWReesParameters.scalars sy Sc).map (trunc k N))
        (BWWScalars.mapCScalars (trunc k N) (BWWReesParameters.cScalars sy cs))

/-- **The lower-degree case**: over every commutative ring with `2` invertible, for every
lower-degree parameter system and every normalization. -/
def LowerDegreeCase : Prop :=
  ∀ (k : Type w) [CommRing k], IsUnit (2 : k) → ∀ (Sc : BWWScalars D k), Sc.LowerDegree sy →
    ∀ cs : CScalars Sc.toScalars, P.holds Sc cs

/-- **The graded case** of Brundan–Wang–Webster §2.2: over every `ℕ`-graded commutative ring
with `2` invertible, for every graded-homogeneous parameter system and every normalization. -/
def GradedCase : Prop :=
  ∀ (k : Type w) [CommRing k] (σ : Type w) [SetLike σ k] [AddSubgroupClass σ k] (𝒜 : ℕ → σ)
    [GradedRing 𝒜], IsUnit (2 : k) → ∀ Sc : BWWScalars D k, Sc.GradedHomogeneous sy 𝒜 →
      ∀ cs : CScalars Sc.toScalars, P.holds Sc cs

/-- **Reduction to truncated Rees parameters.** The truncated Rees case implies the
lower-degree case: the truncations `k[h] → k[h]/(h^N)` jointly detect zero, and the Rees
parameters specialize to the given ones at `h = 1`. -/
theorem lowerDegreeCase_of_truncatedReesCase (h : P.TruncatedReesCase sy) :
    P.LowerDegreeCase sy := by
  intro k _ h₂ Sc hl cs
  have h₂' : IsUnit (2 : MvPolynomial Unit k) := by
    convert h₂.map (MvPolynomial.C : k →+* MvPolynomial Unit k) using 1
    exact (map_ofNat _ 2).symm
  have hR := P.separating h₂' (BWWReesParameters.scalars sy Sc)
    (BWWReesParameters.cScalars sy cs) (fun N => trunc k N) (trunc_separate k)
    (fun N => h k h₂ Sc hl cs N)
  have hS := P.map ReesParameters.specialize h₂' _ _ hR
  exact P.holds_congr (BWWReesParameters.map_specialize sy Sc) _ cs
    (fun μ i => by simp [BWWReesParameters.cScalars]) hS

/-- The lower-degree case implies the graded case. -/
theorem gradedCase_of_lowerDegreeCase (h : P.LowerDegreeCase sy) : P.GradedCase sy := by
  intro k _ σ _ _ 𝒜 _ h₂ Sc hg cs
  exact h k h₂ Sc hg.lowerDegree cs

/-- **Reduction of the graded case.** The truncated Rees case implies the graded case of
Brundan–Wang–Webster §2.2. -/
theorem gradedCase_of_truncatedReesCase (h : P.TruncatedReesCase sy) : P.GradedCase sy :=
  P.gradedCase_of_lowerDegreeCase sy (P.lowerDegreeCase_of_truncatedReesCase sy h)

variable (D) in
/-- The Brundan–Ellis Nondegeneracy Conjecture for the interior part `BWWScalars.toScalars`
of the parameters (the pure coefficients are not seen by the Brundan–Ellis relations). It is a
`BWWParameterProperty` by `nondegeneracyConjecture_scalarChange` and
`nondegeneracyConjecture_of_separating`. -/
def interiorNondegeneracy : BWWParameterProperty.{u, v, w} D where
  holds _ cs := NondegeneracyConjecture cs
  map f h₂ _ _ h :=
    nondegeneracyConjecture_congr (eq_true (ScalarChange.isUnit_two_map f h₂)).symm rfl rfl _ _
      (fun _ _ => rfl) (nondegeneracyConjecture_scalarChange f h)
  separating := by
    intro R _ h₂ Sc cs J S _ g hg h
    exact nondegeneracyConjecture_of_separating g hg fun j =>
      nondegeneracyConjecture_congr (eq_true (ScalarChange.isUnit_two_map (g j) h₂)) rfl rfl _ _
        (fun _ _ => rfl) (h j)

end BWWParameterProperty

end OddMath.SKM
