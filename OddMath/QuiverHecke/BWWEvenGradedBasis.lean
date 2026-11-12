/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.BWWEvenSpecialization
import OddMath.SKM.CoefficientGradedBasis

/-!
# The graded form of the Brundan–Wang–Webster headline at parity zero

J. Brundan, W. Wang, B. Webster, arXiv:2505.22929v2, §2.2 and Theorem 5.6: over an
`ℕ`-graded ring `k`, with parameters homogeneous for the grading of §2.2, the 2-category is
graded by the total degree (diagram degree plus coefficient degree) and its morphism spaces
have a homogeneous basis. This file supplies the graded form of
`QuiverHecke.bwwPolynomials_evenNondegeneracy`.

* `natIntGrading 𝒜`: the `ℤ`-grading of `k` with `𝒜 n` in degree `n ≥ 0` and `0` in negative
  degrees; it is a graded monoid when `𝒜` is.
* `inv_mem_zero_of_mem_zero`: in an `ℕ`-graded ring, the inverse of a unit of degree `0` has
  degree `0`.
* `bwwPolynomials_isHomogeneous`: the defining relations of the presentation with
  Brundan–Wang–Webster parameters are homogeneous for the total degree.
* `bwwPolynomials_evenGradedNondegeneracy`: if moreover the normalization `c_{λ;i}` has degree
  `0`, then for all words `a`, `b` of equal weight, every weight `μ` and every choice `F` of
  decorated reduced matchings, the elements `F_t b_c` (a decorated matching times a monomial in
  the bubbles) form a `k`-basis of the morphism space, and `F_t b_c` lies in total degree
  `deg b_c + deg F_t`.

The degree-`0` condition on the normalization is a hypothesis beyond those of
`QuiverHecke.bwwPolynomials_evenNondegeneracy`; it holds for normalizations taken from the
degree-`0` part of `k`. The direct-sum decomposition of the Hom spaces for `natIntGrading 𝒜` is
not stated here: no `GradedAlgebra` instance is constructed for `natIntGrading 𝒜`.
-/

noncomputable section

namespace OddMath.QuiverHecke

open SKM

universe u

section NatIntGrading

variable {k : Type u} [CommRing k] {σ : Type u} [SetLike σ k] [AddSubgroupClass σ k]
  (𝒜 : ℕ → σ)

/-- The `ℤ`-grading induced by an `ℕ`-grading: `𝒜 n` in degree `n ≥ 0`, zero in negative
degrees. -/
def natIntGrading (n : ℤ) : Submodule ℤ k where
  carrier := {x | (0 ≤ n → x ∈ 𝒜 n.toNat) ∧ (n < 0 → x = 0)}
  add_mem' {x y} hx hy :=
    ⟨fun h => add_mem (hx.1 h) (hy.1 h), fun h => by rw [hx.2 h, hy.2 h, add_zero]⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ => rfl⟩
  smul_mem' c x hx := ⟨fun h => zsmul_mem (hx.1 h) c, fun h => by rw [hx.2 h, smul_zero]⟩

theorem mem_natIntGrading_natCast {n : ℕ} {x : k} : x ∈ natIntGrading 𝒜 n ↔ x ∈ 𝒜 n :=
  ⟨fun h => by simpa using h.1 (Int.natCast_nonneg n),
    fun h => ⟨fun _ => by simpa using h, fun h' => absurd h' (by omega)⟩⟩

instance natIntGrading_gradedMonoid [SetLike.GradedMonoid 𝒜] :
    SetLike.GradedMonoid (natIntGrading 𝒜) where
  one_mem := ⟨fun _ => (SetLike.GradedOne.one_mem : (1 : k) ∈ 𝒜 0), fun h => absurd h (by omega)⟩
  mul_mem i j x y hx hy := by
    by_cases hi : 0 ≤ i
    · by_cases hj : 0 ≤ j
      · refine ⟨fun _ => ?_, fun h => absurd h (by omega)⟩
        rw [Int.toNat_add hi hj]
        exact SetLike.GradedMul.mul_mem (hx.1 hi) (hy.1 hj)
      · rw [hy.2 (by omega), mul_zero]; exact zero_mem _
    · rw [hx.2 (by omega), zero_mul]; exact zero_mem _

/-- In an `ℕ`-graded ring, the inverse of a unit of degree `0` has degree `0`. -/
theorem inv_mem_zero_of_mem_zero [GradedRing 𝒜] (u : kˣ) (hu : (u : k) ∈ 𝒜 0) :
    (↑u⁻¹ : k) ∈ 𝒜 0 := by
  classical
  have hn : ∀ n ≠ 0, (DirectSum.decompose 𝒜 (↑u⁻¹ : k) n : k) = 0 := by
    intro n hn
    have h1 : (DirectSum.decompose 𝒜 ((u : k) * ↑u⁻¹) n : k) = 0 := by
      rw [Units.mul_inv]
      exact DirectSum.decompose_of_mem_ne 𝒜 SetLike.GradedOne.one_mem (Ne.symm hn)
    rw [DirectSum.coe_decompose_mul_of_left_mem_zero 𝒜 hu] at h1
    calc (DirectSum.decompose 𝒜 (↑u⁻¹ : k) n : k)
        = ↑u⁻¹ * ((u : k) * DirectSum.decompose 𝒜 (↑u⁻¹ : k) n) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = 0 := by rw [h1, mul_zero]
  rw [← DirectSum.sum_support_decompose 𝒜 (↑u⁻¹ : k)]
  refine sum_mem fun n _ => ?_
  by_cases h0 : n = 0
  · subst h0; exact SetLike.coe_mem _
  · rw [hn n h0]; exact zero_mem _

end NatIntGrading

variable {I X : Type u} [AddCommGroup X]

/-- **Homogeneous relations.** For Brundan–Wang–Webster polynomials homogeneous for the grading
of §2.2, every defining relation of the presentation lies in one total degree (diagram degree
plus coefficient degree, `CoefficientGrading.IsHomogeneous`). -/
theorem bwwPolynomials_isHomogeneous (D : Datum I X) (sy : Symmetrizer D)
    (hD : EvenBridge.IsEven D) (k : Type u) [CommRing k] {σ : Type u} [SetLike σ k]
    [AddSubgroupClass σ k] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (P : BWWPolynomials D k) (hP : P.GradedHomogeneous sy 𝒜) :
    Diagrams.CoefficientGrading.IsHomogeneous (natIntGrading 𝒜) (SKM.gdeg D sy)
      (SKM.pres D (bwwPolynomialsEquiv hD P).toScalars) := by
  obtain ⟨ht, hc⟩ := (P.gradedHomogeneous_toBWWScalars_iff sy 𝒜 hD).2 hP
  refine SKM.isHomogeneous_coefficientGraded D sy (natIntGrading 𝒜)
    (bwwPolynomialsEquiv hD P).toScalars
    (fun i j => (mem_natIntGrading_natCast 𝒜 (n := 0)).2 (ht i j)) ?_
  intro i j p q hij hp hq h0
  obtain ⟨n, hn, hmem⟩ := hc i j p q hij hp hq h0
  rw [← hn]
  exact (mem_natIntGrading_natCast 𝒜).2 hmem

/-- **The Brundan–Wang–Webster headline at parity zero, graded form** (Brundan–Wang–Webster,
arXiv:2505.22929v2, Theorem 5.6, for the parameters of §2.2): for a purely even datum with a
symmetrizer, over every `ℕ`-graded commutative ring with `2` invertible, for every graded family
of Brundan–Wang–Webster polynomials and every normalization of degree `0`, for all words of equal
weight, every weight `μ` and every choice `F` of decorated reduced matchings, the elements
`F_t b_c` form a `k`-basis of the morphism space and each lies in total degree
`deg b_c + deg F_t`. -/
theorem bwwPolynomials_evenGradedNondegeneracy (D : Datum I X) (sy : Symmetrizer D)
    (hD : EvenBridge.IsEven D) (k : Type u) [CommRing k] {σ : Type u} [SetLike σ k]
    [AddSubgroupClass σ k] (𝒜 : ℕ → σ) [GradedRing 𝒜] (h₂ : IsUnit (2 : k))
    (P : BWWPolynomials D k) (hP : P.GradedHomogeneous sy 𝒜)
    (cs : CScalars (bwwPolynomialsEquiv hD P).toScalars)
    (hc : ∀ μ i, (cs.c μ i : k) ∈ 𝒜 0) :
    ∀ (a b : List (Letter I)), SKM.wt D 0 a = SKM.wt D 0 b →
      ∀ (μ : X) (F : MatchingBasisChoice a b), ∃ hF : F.IsBasis cs μ,
        ∀ x, F.homogeneousBasis cs μ hF x ∈
          Diagrams.CoefficientGrading.presentedPart (natIntGrading 𝒜) (SKM.gdeg D sy)
            (SKM.pres D (bwwPolynomialsEquiv hD P).toScalars) (SKM.ob D μ a) (SKM.ob D μ b)
            (SYM.coefficientDegree D sy x.2 + SKM.tableDegree D sy μ (F.layers x.1)) := by
  have hc' : cs.DegreeZero (natIntGrading 𝒜) := fun μ i =>
    ⟨(mem_natIntGrading_natCast 𝒜 (n := 0)).2 (hc μ i),
      (mem_natIntGrading_natCast 𝒜 (n := 0)).2 (inv_mem_zero_of_mem_zero 𝒜 _ (hc μ i))⟩
  intro a b hab μ F
  have hF := bwwPolynomials_evenNondegeneracy D sy hD k 𝒜 h₂ P hP cs a b hab μ F
  exact ⟨hF, fun x => F.homogeneousBasis_mem sy hc' μ hF x⟩

end OddMath.QuiverHecke
