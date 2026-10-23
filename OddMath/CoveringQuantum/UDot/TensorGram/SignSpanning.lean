/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TensorGram.RowBasis
import OddMath.CoveringQuantum.Coefficients.HalfSplitting
import OddMath.CoveringQuantum.SuperCount.Count
import OddMath.CoveringQuantum.PreF.BaseChange

/-!
# Spanning words for the negative fiber of the half algebra

Let `S` be a finite set of words closed under rearrangement (words of equal weight). We choose
`W ⊆ S` such that the form on `'f` specialized at `π = -1` has an invertible Gram matrix on `W`,
and such that the negative-fiber component (`Coefficients.negativeIdempotent`) of the image in
the Serre presentation of every word of `S` is a `ℚ(q)`-combination of the words of `W` of the
same weight.

The input is the π = -1 presentation of the half algebra for all super Cartan data with finitely
many simple roots (Brundan–Ellis, arXiv:1701.04133v2, §10;
`SuperCartanDatum.serreIdeal_neg_one_eq_radical_of_transcendental`), and the lifting of
specialized Serre ideal membership by the central idempotent
(`SuperCartanDatum.smul_mem_serreIdeal_of_mapCoeffs`). This is the half-algebra step of the
nondegeneracy of the form on `U̇` at `π = -1` (Brundan–Ellis, Theorem 10.1) without the
bar-consistency hypothesis (10.2). The argument is ours.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.SignSpanning

open Coefficients PreF

variable {I : Type*} [DecidableEq I] (C : SuperCartanDatum I)

/-- The specialization `π ↦ -1` of the generic coefficient ring. -/
abbrev sgn : Coefficients.Ring →ₐ[RatFunc ℚ] RatFunc ℚ := specialize (-1) (by norm_num)

private theorem sgn_q_transcendental :
    Transcendental ℚ ((Units.map (sgn).toMonoidHom q : (RatFunc ℚ)ˣ) : RatFunc ℚ) := by
  change Transcendental ℚ (sgn (q : Coefficients.Ring))
  rw [specialize_q]
  have hi : (RatFunc.instAlgebraOfPolynomial ℚ ℚ : Algebra ℚ (RatFunc ℚ)) =
      (DivisionRing.toRatAlgebra : Algebra ℚ (RatFunc ℚ)) :=
    Subsingleton.elim _ _
  exact (congrArg (fun a : Algebra ℚ (RatFunc ℚ) ↦
    @Transcendental ℚ (RatFunc ℚ) _ _ a RatFunc.X) hi).mp
      (RatFunc.transcendental_X (K := ℚ))

/-- The Gram matrix of the form specialized at `π = -1` on a finite set of words. -/
def signGram (S : Finset (List I)) : Matrix S S (RatFunc ℚ) :=
  Matrix.of fun a b ↦ sgn (C.form q pi (monomial Coefficients.Ring a.1)
    (monomial Coefficients.Ring b.1))

omit [DecidableEq I] in
private theorem mapCoeffs_monomial' {k k' : Type*} [CommRing k] [CommRing k'] (φ : k →+* k')
    (w : List I) : FreeAlgebra.mapCoeffs φ (monomial k w) = monomial k' w := by
  induction w with
  | nil => simp
  | cons i w ih => simp only [monomial_cons, map_mul, θ, FreeAlgebra.mapCoeffs_ι, ih]

/-- Coefficient transport of the form to `π = -1`. -/
theorem form_sgn (x y : PreF Coefficients.Ring I) :
    C.form (Units.map (sgn).toMonoidHom q) (-1) (FreeAlgebra.mapCoeffs (sgn).toRingHom x)
        (FreeAlgebra.mapCoeffs (sgn).toRingHom y) = sgn (C.form q pi x y) := by
  have h := PreF.form_mapCoeffs (sgn).toRingHom (C.chi q pi)
    (C.chi (Units.map (sgn).toMonoidHom q) (-1)) (C.norm q pi)
    (C.norm (Units.map (sgn).toMonoidHom q) (-1))
    (fun i j ↦ by simpa using C.map_chi (sgn).toRingHom q pi i j)
    (fun i ↦ by simpa using C.map_norm (sgn).toRingHom q pi i (denominator_isUnit C i)) x y
  exact h

/-- **Spanning words at `π = -1`.** For a finite set `S` of words closed under passing to words
of the same weight, there is `W ⊆ S` with invertible specialized Gram matrix such that the
negative-fiber image of every word of `S` in the Serre presentation is a `ℚ(q)`-combination of
the images of the words of `W` of the same weight. -/
theorem exists_signSpanning [Finite I] (S : Finset (List I))
    (hS : ∀ a ∈ S, ∀ b, wordWeight b = wordWeight a → b ∈ S) :
    ∃ W : Finset S, ((signGram C S).submatrix ((↑) : W → S) ((↑) : W → S)).det ≠ 0 ∧
      ∀ a : S, ∃ c : S → RatFunc ℚ,
        (∀ w, c w ≠ 0 → w ∈ W ∧ wordWeight w.1 = wordWeight a.1) ∧
        negativeIdempotent • C.toSerreF q pi (monomial Coefficients.Ring a.1) =
          ∑ w ∈ W, algebraMap (RatFunc ℚ) Coefficients.Ring (c w) •
            negativeIdempotent • C.toSerreF q pi (monomial Coefficients.Ring w.1) := by
  classical
  have hform0 : ∀ a b : List I, wordWeight a ≠ wordWeight b →
      C.form q pi (monomial Coefficients.Ring a) (monomial Coefficients.Ring b) = 0 :=
    fun a b h ↦ PreF.form_eq_zero_of_ne _ _ h (monomial_mem_weightSpace a)
      (monomial_mem_weightSpace b)
  obtain ⟨W, hrow, hdet⟩ := RowBasis.exists_rowBasis (signGram C S)
    (fun a b ↦ by simp only [signGram, Matrix.of_apply]; rw [C.form_comm])
    (fun a : S ↦ wordWeight a.1)
    (fun a b h ↦ by simp only [signGram, Matrix.of_apply]; rw [hform0 _ _ h, map_zero])
  refine ⟨W, hdet, fun a ↦ ?_⟩
  obtain ⟨c, hc, hrel⟩ := hrow a
  refine ⟨c, hc, ?_⟩
  set x : PreF Coefficients.Ring I := monomial Coefficients.Ring a.1 -
    ∑ w ∈ W, algebraMap (RatFunc ℚ) Coefficients.Ring (c w) • monomial Coefficients.Ring w.1
    with hx
  -- the specialization of `x` lies in the radical at `π = -1`
  have hrad : FreeAlgebra.mapCoeffs (sgn).toRingHom x ∈
      PreF.radical (C.chi (Units.map (sgn).toMonoidHom q) (-1))
        (C.norm (Units.map (sgn).toMonoidHom q) (-1)) := by
    apply (PreF.mem_radical_iff _ _).mpr
    intro y
    induction y using FreeAlgebra.induction_wordBasis with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz, add_zero]
    | smul c y hy => simp only [map_smul, hy, smul_zero]
    | word b =>
      rw [FreeAlgebra.wordBasis_apply, ← monomial, ← mapCoeffs_monomial' (sgn).toRingHom b]
      change C.form _ _ _ _ = 0
      rw [form_sgn, hx]
      simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply,
        map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, AlgHom.commutes,
        Algebra.algebraMap_self, RingHom.id_apply]
      by_cases hb : b ∈ S
      · have := hrel ⟨b, hb⟩
        simp only [signGram, Matrix.of_apply] at this
        rw [this, sub_self]
      · have hab : wordWeight a.1 ≠ wordWeight b := fun h ↦ hb (hS _ a.2 _ h.symm)
        rw [hform0 _ _ hab, map_zero, zero_sub, neg_eq_zero]
        refine Finset.sum_eq_zero fun w _ ↦ ?_
        by_cases hw : c w = 0
        · rw [hw, zero_mul]
        · rw [hform0 _ _ ((hc w hw).2 ▸ hab), map_zero, mul_zero]
  have hmem : negativeIdempotent • x ∈ C.serreIdeal q pi := by
    apply C.smul_mem_serreIdeal_of_mapCoeffs q pi (sgn).toRingHom
      (algebraMap (RatFunc ℚ) Coefficients.Ring) negativeIdempotent
      negativeIdempotent_mul_self negativeIdempotent_retract
    have h := (C.serreIdeal_neg_one_eq_radical_of_transcendental sgn_q_transcendental).symm ▸ hrad
    simpa using h
  have h0 := (C.mem_serreIdeal q pi _).mp hmem
  rw [hx, smul_sub, map_sub, sub_eq_zero, Finset.smul_sum, map_sum] at h0
  rw [← map_smul, h0]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [smul_comm negativeIdempotent, map_smul, map_smul]

end OddMath.CoveringQuantum.UDot.SignSpanning
