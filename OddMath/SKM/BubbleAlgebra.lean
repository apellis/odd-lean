/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanBubbles
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot

/-!
# The all-colour algebra of bubble coefficients

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
(1.21)–(1.22).

`SYM D k` is a generators-and-relations presentation of the super tensor product
of one copy of `Sym k` for every even colour and one copy of `SymD k` for every
odd colour. There is an even polynomial generator `e i n` for every colour `i`
and every `n : ℕ` (representing the elementary symmetric function `e_{n+1}`),
and an odd exterior generator `delta i` for every odd colour. The polynomial
generators commute with each other and with the exterior generators; exterior
generators anticommute and have square zero. Thus the presentation is the
polynomial algebra on `I × ℕ` tensored with the exterior algebra on the odd
colours. It imposes no relations coming from a diagram category. In particular,
its definition and its ring and algebra instances do not depend on a weight,
scalar parameters, or a Hom space. The presentation allows arbitrary colour
sets, with each algebra element involving only finitely many generators.

`betaSYM` evaluates these generators at the normalized elementary bubbles and
at the odd bubbles. The polynomial generators are even also for odd colours:
their images then have shifted dot count `2 * (n + 1)`. The cross-colour signs
follow from super interchange. `betaSYM_range` identifies the range with
`bubbleSpan`, using the existing one-colour maps `beta` and `betaD`.

Multiplication in the target endomorphism ring is `f * g = g ≫ f`.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X]

/-- Even elementary generators, together with one odd generator for each odd colour. -/
abbrev SYMGen (D : Datum I X) := (I × ℕ) ⊕ {i : I // D.parity i = 1}

/-- The polynomial and exterior relations defining the all-colour super tensor product.
The square-zero relations are imposed explicitly, including in characteristic two. -/
inductive SYMRel (D : Datum I X) (k : Type w) [CommRing k] :
    FreeAlgebra k (SYMGen D) → FreeAlgebra k (SYMGen D) → Prop
  | polynomial (a b : I × ℕ) :
      SYMRel D k
        (FreeAlgebra.ι k (.inl a) * FreeAlgebra.ι k (.inl b))
        (FreeAlgebra.ι k (.inl b) * FreeAlgebra.ι k (.inl a))
  | mixed (a : I × ℕ) (i : {i : I // D.parity i = 1}) :
      SYMRel D k
        (FreeAlgebra.ι k (.inl a) * FreeAlgebra.ι k (.inr i))
        (FreeAlgebra.ι k (.inr i) * FreeAlgebra.ι k (.inl a))
  | exterior (i j : {i : I // D.parity i = 1}) :
      SYMRel D k
        (FreeAlgebra.ι k (.inr i) * FreeAlgebra.ι k (.inr j))
        (-(FreeAlgebra.ι k (.inr j) * FreeAlgebra.ι k (.inr i)))
  | square (i : {i : I // D.parity i = 1}) :
      SYMRel D k (FreeAlgebra.ι k (.inr i) ^ 2) 0

/-- The all-colour coefficient algebra of Brundan–Ellis (1.21), presented independently
of the diagram category as an even polynomial algebra times an exterior algebra. -/
abbrev SYM (D : Datum I X) (k : Type w) [CommRing k] := RingQuot (SYMRel D k)

namespace SYM

variable (D : Datum I X) (k : Type w) [CommRing k]

/-- The quotient map from the free algebra on the coefficient generators. -/
abbrev mk : FreeAlgebra k (SYMGen D) →ₐ[k] SYM D k := RingQuot.mkAlgHom k (SYMRel D k)

/-- The generating map into the coefficient algebra. -/
def ι (g : SYMGen D) : SYM D k := mk D k (FreeAlgebra.ι k g)

/-- The elementary symmetric generator `e_{n+1}` of colour `i`, always even. -/
def e (i : I) (n : ℕ) : SYM D k := ι D k (.inl (i, n))

/-- The odd square-zero generator belonging to an odd colour. -/
def delta (i : {i : I // D.parity i = 1}) : SYM D k := ι D k (.inr i)

theorem e_commute (i j : I) (m n : ℕ) : Commute (e D k i m) (e D k j n) := by
  show e D k i m * e D k j n = e D k j n * e D k i m
  simpa only [e, ι, map_mul] using
    RingQuot.mkAlgHom_rel k (SYMRel.polynomial (D := D) (k := k) (i, m) (j, n))

theorem e_delta_commute (i : I) (n : ℕ) (j : {j : I // D.parity j = 1}) :
    Commute (e D k i n) (delta D k j) := by
  show e D k i n * delta D k j = delta D k j * e D k i n
  simpa only [e, delta, ι, map_mul] using
    RingQuot.mkAlgHom_rel k (SYMRel.mixed (D := D) (k := k) (i, n) j)

theorem delta_anticommute (i j : {i : I // D.parity i = 1}) :
    delta D k i * delta D k j = -(delta D k j * delta D k i) := by
  simpa only [delta, ι, map_mul, map_neg] using
    RingQuot.mkAlgHom_rel k (SYMRel.exterior (D := D) (k := k) i j)

theorem delta_sq (i : {i : I // D.parity i = 1}) : delta D k i ^ 2 = 0 := by
  simpa only [delta, ι, map_pow, map_zero] using
    RingQuot.mkAlgHom_rel k (SYMRel.square (D := D) (k := k) i)

/-- To bound the range of a homomorphism from `SYM`, it suffices to bound its generators. -/
theorem range_le {A : Type*} [Semiring A] [Algebra k A]
    (f : SYM D k →ₐ[k] A) (S : Subalgebra k A)
    (h : ∀ g, f (ι D k g) ∈ S) : f.range ≤ S := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨p, rfl⟩ := RingQuot.mkAlgHom_surjective k (SYMRel D k) x
  change f (mk D k p) ∈ S
  induction p using FreeAlgebra.induction with
  | grade0 r =>
      simp only [AlgHom.commutes]
      exact S.algebraMap_mem r
  | grade1 g => exact h g
  | mul p q hp hq =>
      rw [map_mul, map_mul]
      exact S.mul_mem hp hq
  | add p q hp hq =>
      rw [map_add, map_add]
      exact S.add_mem hp hq

/-- Homomorphisms out of the coefficient algebra are determined by the generators. -/
@[ext] theorem hom_ext {A : Type*} [Semiring A] [Algebra k A]
    {f g : SYM D k →ₐ[k] A} (h : ∀ a, f (ι D k a) = g (ι D k a)) : f = g := by
  apply RingQuot.ringQuot_ext'
  exact FreeAlgebra.hom_ext (funext h)

end SYM

variable {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- The images of the polynomial and exterior generators of `SYM`. -/
def betaSYMGen (μ : X) : SYMGen D → End ((pres D Sc).obj (ob D μ []))
  | .inl (i, n) => if D.parity i = 0 then betaGen cs i μ n else betaDGen cs i μ (some n)
  | .inr i => oddBubble cs i μ

/-- All the polynomial generators have even images, irrespective of the colour. -/
theorem betaSYMGen_polynomial_mem (μ : X) (a : I × ℕ) :
    betaSYMGen cs μ (.inl a) ∈ closedPar D Sc μ 0 := by
  rcases a with ⟨i, n⟩
  by_cases hi : D.parity i = 0
  · simp only [betaSYMGen, if_pos hi, betaGen]
    exact Submodule.smul_mem _ _ (bubLs_mem_even cs i μ hi _)
  · simp only [betaSYMGen, if_neg hi, betaDGen]
    exact Submodule.smul_mem _ _ (bubLs_two_mul_mem cs i μ _)

/-- Super interchange and the square-zero odd-bubble relation respect the abstract
polynomial/exterior presentation. -/
theorem betaSYM_rel (μ : X) {x y : FreeAlgebra k (SYMGen D)} (h : SYMRel D k x y) :
    FreeAlgebra.lift k (betaSYMGen cs μ) x = FreeAlgebra.lift k (betaSYMGen cs μ) y := by
  cases h with
  | polynomial a b =>
      simp only [map_mul, FreeAlgebra.lift_ι_apply]
      exact (commute_of_mem_zero (betaSYMGen_polynomial_mem cs μ a)
        (betaSYMGen_polynomial_mem cs μ b)).eq
  | mixed a i =>
      simp only [map_mul, FreeAlgebra.lift_ι_apply]
      exact (commute_of_mem_zero (betaSYMGen_polynomial_mem cs μ a)
        (oddBubble_mem cs i μ)).eq
  | exterior i j =>
      simp only [map_mul, map_neg, FreeAlgebra.lift_ι_apply, betaSYMGen, End.mul_def]
      simpa [i.property, j.property, zsign] using
        comm_of_mem (oddBubble_mem cs j μ) (oddBubble_mem cs i μ)
  | square i =>
      simp only [map_pow, map_zero, FreeAlgebra.lift_ι_apply, betaSYMGen, sq, End.mul_def]
      exact oddBubble_sq cs i μ i.property

/-- The all-colour bubble homomorphism of Brundan–Ellis (1.22), with abstract domain (1.21). -/
def betaSYM (μ : X) : SYM D k →ₐ[k] End ((pres D Sc).obj (ob D μ [])) :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k (betaSYMGen cs μ), fun _ _ h => betaSYM_rel cs μ h⟩

@[simp] theorem betaSYM_ι (μ : X) (g : SYMGen D) :
    betaSYM cs μ (SYM.ι D k g) = betaSYMGen cs μ g := by
  simp only [betaSYM, SYM.ι, SYM.mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    FreeAlgebra.lift_ι_apply]

/-- On an even colour, the elementary generator has the image prescribed by `beta`. -/
theorem betaSYM_e_even (μ : X) (i : I) (hi : D.parity i = 0) (n : ℕ) :
    betaSYM cs μ (SYM.e D k i n) = beta cs i μ hi (MvPolynomial.X n) := by
  rw [SYM.e, betaSYM_ι, beta_X]
  simp only [betaSYMGen, if_pos hi]

/-- On an odd colour, the elementary generator has the image prescribed by `betaD`. -/
theorem betaSYM_e_odd (μ : X) (i : I) (hi : D.parity i = 1) (n : ℕ) :
    betaSYM cs μ (SYM.e D k i n) =
      betaD cs i μ hi (SymD.ofSym (MvPolynomial.X n)) := by
  have hne : D.parity i ≠ 0 := by rw [hi]; decide
  rw [SYM.e, betaSYM_ι, SymD.ofSym, AlgHom.comp_apply, MvPolynomial.rename_X,
    betaD_mk, betaDPoly_X]
  simp only [betaSYMGen, if_neg hne]

@[simp] theorem betaSYM_delta (μ : X) (i : {i : I // D.parity i = 1}) :
    betaSYM cs μ (SYM.delta D k i) = oddBubble cs i μ := by
  exact betaSYM_ι cs μ (.inr i)

/-- Each one-colour bubble map factors at the level of ranges through the all-colour map. -/
theorem betaRange_le_betaSYM_range (i : I) (μ : X) :
    betaRange cs i μ ≤ (betaSYM cs μ).range := by
  have hg (g : SYMGen D) : betaSYMGen cs μ g ∈ (betaSYM cs μ).range :=
    ⟨SYM.ι D k g, betaSYM_ι cs μ g⟩
  unfold betaRange
  split_ifs with hi
  · rintro _ ⟨x, rfl⟩
    induction x using MvPolynomial.induction_on with
    | C a =>
        rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
        exact (betaSYM cs μ).range.algebraMap_mem a
    | add p q hp hq =>
        rw [map_add]
        exact (betaSYM cs μ).range.add_mem hp hq
    | mul_X p n hp =>
        rw [map_mul, beta_X]
        exact (betaSYM cs μ).range.mul_mem hp (by
          simpa only [betaSYMGen, if_pos hi] using hg (.inl (i, n)))
  · rintro _ ⟨x, rfl⟩
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective k _ x
    rw [betaD_mk]
    induction p using MvPolynomial.induction_on with
    | C a =>
        rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
        exact (betaSYM cs μ).range.algebraMap_mem a
    | add p q hp hq =>
        rw [map_add]
        exact (betaSYM cs μ).range.add_mem hp hq
    | mul_X p o hp =>
        rw [map_mul, betaDPoly_X]
        refine (betaSYM cs μ).range.mul_mem hp ?_
        cases o with
        | none => exact hg (.inr ⟨i, zmod2_eq_one_of_ne_zero hi⟩)
        | some n =>
            simpa only [betaSYMGen, if_neg hi] using hg (.inl (i, n))

/-- The abstract all-colour bubble homomorphism has exactly the bubble subalgebra as range. -/
theorem betaSYM_range (μ : X) : (betaSYM cs μ).range = bubbleSpan cs μ := by
  apply le_antisymm
  · apply SYM.range_le
    intro g
    rw [betaSYM_ι]
    cases g with
    | inl a =>
        rcases a with ⟨i, n⟩
        by_cases hi : D.parity i = 0
        · simp only [betaSYMGen, if_pos hi, betaGen]
          exact (isBub_bubLs cs i μ _).smul _
        · simp only [betaSYMGen, if_neg hi, betaDGen]
          exact (isBub_bubLs cs i μ _).smul _
    | inr i => exact isBub_oddBubble cs i μ
  · rw [bubbleSpan_eq_iSup]
    exact iSup_le fun i => betaRange_le_betaSYM_range cs i μ

end OddMath.SKM
