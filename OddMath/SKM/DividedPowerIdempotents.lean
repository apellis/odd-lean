/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.Frontier.OnhReflection
import OddMath.Frontier.OnhStructure
import OddMath.Frontier.SmallRankONH
import OddMath.Frontier.EQOnhDGRing
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Odd divided-power projector conventions

BE2, arXiv:1701.04133v2, §11 immediately before Lemma 11.1, and
Hill–Wang, arXiv:1202.2769v2, (5.20), (5.28).

Rank is `a = n + 2`. Source strand `r = j.val + 1`, counted right-to-left,
corresponds to library dot `j.rev`; source crossing `r = i.val + 1` corresponds
 to `i.rev`. Multiplication acts rightmost first, without an extra super sign.
The odd mixed relations have constant `+1` in both source presentations.

Consequently the literal printed odd element `-T_r X_r` squares to its negative.
The corrected odd generator is `T_r X_r`, whereas the even generator retains
`-T_r X_r`: uniformly the coefficient is `(-1)^(|i|+1)`. This is a sign error
in both cited sources, not a super-opposite or composition convention; see
ERRATA [BE2] 7. In HW the substitution in the calculation after (5.20) omits
this parity dependence. The odd polynomial action in §4.2 already detects it.

The corrected generator is the reflected opposite of EKL's `x_r ∂_r`.
We prove reduced-expression independence, longest-projector idempotence,
degree zero and even parity in the presented ring, with nonvanishing over ℚ.
The printed and corrected longest products generate the same left ideal.
The graded projective decomposition of Lemma 11.1 is a separate result.
-/

namespace OddMath.SKM.DividedPowerIdempotents

open OddMath.Frontier
open NilHeckeAction NilCoxeterWords NilHeckeRightBasis

noncomputable section

/-- BE2 (1.8), even colour: `X_left T - T X_right = 1` and `T² = 0`
make the printed negative element idempotent, in every ambient ring. -/
theorem even_generator_idempotent {A : Type*} [Ring A] (t x y : A)
    (ht : t * t = 0) (hslide : y * t = t * x + 1) : IsIdempotentElem (-(t * x)) := by
  have htx : t * x = y * t - 1 := by rw [hslide]; abel
  have htxt : t * x * t = -t := by
    rw [htx, sub_mul, one_mul, mul_assoc, ht, mul_zero, zero_sub]
  change (-(t * x)) * (-(t * x)) = -(t * x)
  rw [neg_mul_neg, ← mul_assoc, htxt, neg_mul]

/-- BE2 (1.8), odd colour: both mixed constants are positive, so `+T X_right`
is idempotent. No opposite multiplication or crossing rescaling is involved. -/
theorem odd_generator_idempotent {A : Type*} [Ring A] (t x y : A)
    (ht : t * t = 0) (hslide : y * t + t * x = 1) : IsIdempotentElem (t * x) := by
  have htx : t * x = 1 - y * t := by rw [← hslide]; abel
  have htxt : t * x * t = t := by
    rw [htx, sub_mul, one_mul, mul_assoc, ht, mul_zero, sub_zero]
  change (t * x) * (t * x) = t * x
  rw [← mul_assoc, htxt]

variable {n : ℕ}

/-- Right-to-left source strand coordinates, converted to the library coordinates. -/
def sourceDot (n : ℕ) (j : Fin (n + 2)) : Presented n := dot n j.rev

/-- The source crossing, with unchanged sign and reversed spatial index. -/
def sourceCrossing (n : ℕ) (i : Fin (n + 1)) : Presented n := crossing n i.rev

/-- The literal minus sign in BE2 §11 and HW (5.20), in the odd presentation. -/
def printedGenerator (n : ℕ) (i : Fin (n + 1)) : Presented n :=
  -sourceCrossing n i * sourceDot n i.castSucc

/-- The corrected odd generator in the source coordinates. -/
def unsignedGenerator (n : ℕ) (i : Fin (n + 1)) : Presented n :=
  sourceCrossing n i * sourceDot n i.castSucc

/-- Ordinary reversal after spatial reflection; no super-opposite sign is inserted. -/
def reflectedOpposite (n : ℕ) (x : Presented n) : Presented n :=
  reverseLinear n (OnhReflection.sigma n x)

@[simp] theorem reflectedOpposite_mul (x y : Presented n) :
    reflectedOpposite n (x * y) = reflectedOpposite n y * reflectedOpposite n x := by
  simp [reflectedOpposite]

@[simp] theorem reflectedOpposite_one : reflectedOpposite n 1 = 1 := by
  simp [reflectedOpposite]

/-- Exact comparison with the existing EKL generator, including its multiplication order. -/
theorem unsignedGenerator_eq_reflectedOpposite (i : Fin (n + 1)) :
    unsignedGenerator n i = reflectedOpposite n (ZeroHecke.zeroHecke n i) := by
  simp [unsignedGenerator, sourceCrossing, sourceDot, reflectedOpposite, ZeroHecke.zeroHecke]

/-- Spatial reversal interchanges the two positive odd mixed relations, not their signs. -/
theorem source_mixed (i : Fin (n + 1)) :
    sourceCrossing n i * sourceDot n i.castSucc +
        sourceDot n i.succ * sourceCrossing n i = 1 ∧
      sourceCrossing n i * sourceDot n i.succ +
        sourceDot n i.castSucc * sourceCrossing n i = 1 := by
  constructor
  · simp [sourceCrossing, sourceDot, Fin.rev_castSucc, Fin.rev_succ,
      NilHeckeBasis.crossing_dot_right]
  · simp [sourceCrossing, sourceDot, Fin.rev_castSucc, Fin.rev_succ,
      NilHeckeBasis.crossing_dot_left]

/-- The sign-free comparison is an idempotent in the actual quotient ring. -/
theorem unsignedGenerator_sq (i : Fin (n + 1)) :
    unsignedGenerator n i * unsignedGenerator n i = unsignedGenerator n i := by
  rw [unsignedGenerator_eq_reflectedOpposite, ← reflectedOpposite_mul, ZeroHecke.zeroHecke_sq]

/-- This equality retains, rather than repairs, the printed minus sign. -/
theorem printedGenerator_eq_neg (i : Fin (n + 1)) :
    printedGenerator n i = -unsignedGenerator n i := by
  simp [printedGenerator, unsignedGenerator]

/-- Obstruction to the printed odd idempotence claim, valid in every rank at least two. -/
theorem printedGenerator_sq (i : Fin (n + 1)) :
    printedGenerator n i * printedGenerator n i = -printedGenerator n i := by
  rw [printedGenerator_eq_neg, neg_mul_neg, unsignedGenerator_sq, neg_neg]

/-- Concrete polynomial test: the unsigned comparison fixes the constant polynomial. -/
theorem action_unsignedGenerator_one (i : Fin (n + 1)) :
    action n (unsignedGenerator n i) 1 = 1 := by
  rw [unsignedGenerator, action_mul_apply, sourceDot, action_dot_one,
    sourceCrossing, action_crossing_apply, Fin.rev_castSucc]
  simp [AllRankDivided.divided_generator]

/-- The literal printed odd generator sends the constant polynomial to minus one. -/
theorem action_printedGenerator_one (i : Fin (n + 1)) :
    action n (printedGenerator n i) 1 = -1 := by
  rw [printedGenerator_eq_neg, map_neg, LinearMap.neg_apply, action_unsignedGenerator_one]

/-- Nonzero in the actual quotient, not just a formal symbol. -/
theorem printedGenerator_ne_zero (i : Fin (n + 1)) : printedGenerator n i ≠ 0 := by
  intro h
  have he := action_printedGenerator_one i
  rw [h, map_zero, LinearMap.zero_apply] at he
  exact one_ne_zero (neg_eq_zero.mp he.symm)

/-- The printed odd generator is not idempotent over the integral presentation. -/
theorem printedGenerator_not_idempotent (i : Fin (n + 1)) :
    ¬ IsIdempotentElem (printedGenerator n i) := by
  intro h
  have he := congrArg (fun x => action n x 1) h
  rw [printedGenerator_sq, map_neg, LinearMap.neg_apply,
    action_printedGenerator_one, neg_neg] at he
  have hc := congrArg (fun f : OddMath.SkewPolynomial.SkewPolynomial (n + 2) => f 0) he
  have hone : (1 : OddMath.SkewPolynomial.SkewPolynomial (n + 2)) 0 = 1 :=
    Finsupp.single_eq_same
  simp only [Finsupp.neg_apply, hone] at hc
  norm_num at hc

/-- Ordinary braid for the unsigned comparison, transported through the explicit anti-map. -/
theorem unsignedGenerator_braid (i j : Fin (n + 1)) (h : j.val = i.val + 1) :
    unsignedGenerator n i * unsignedGenerator n j * unsignedGenerator n i =
      unsignedGenerator n j * unsignedGenerator n i * unsignedGenerator n j := by
  have he := congrArg (reflectedOpposite n) (ZeroHecke.zeroHecke_braid i j h)
  simpa only [reflectedOpposite_mul, ← unsignedGenerator_eq_reflectedOpposite, mul_assoc] using he

/-- Distant unsigned comparisons commute, with no residual sign. -/
theorem unsignedGenerator_distant (i j : Fin (n + 1))
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    unsignedGenerator n i * unsignedGenerator n j =
      unsignedGenerator n j * unsignedGenerator n i := by
  have he := congrArg (reflectedOpposite n) (ZeroHecke.zeroHecke_distant i j h)
  simpa only [reflectedOpposite_mul, ← unsignedGenerator_eq_reflectedOpposite] using he.symm

/-- Written-order product of the unsigned comparisons, not of the printed generators. -/
def unsignedProduct : Word n → Presented n
  | [] => 1
  | i :: w => unsignedGenerator n i * unsignedProduct w

/-- Reversal of the word is necessary because the comparison is an anti-map. -/
theorem unsignedProduct_eq_reflectedOpposite (w : Word n) :
    unsignedProduct w = reflectedOpposite n (ZeroHecke.zeroHeckeProduct w.reverse) := by
  induction w with
  | nil => simp [unsignedProduct]
  | cons i w ih =>
      simp [unsignedProduct, List.reverse_cons, ih, unsignedGenerator_eq_reflectedOpposite]

/-- Reduced-word independence for the explicit unsigned comparison. -/
theorem unsignedProduct_reduced_eq (w v : Word n) (hw : Reduced w) (hv : Reduced v)
    (hp : permutation w = permutation v) : unsignedProduct w = unsignedProduct v := by
  rw [unsignedProduct_eq_reflectedOpposite, unsignedProduct_eq_reflectedOpposite]
  exact congrArg (reflectedOpposite n) (ZeroHecke.zeroHeckeProduct_reduced_eq _ _
    (reduced_reverse w hw) (reduced_reverse v hv) (by simp [hp]))

/-- The corrected odd longest projector, compared with the existing EKL projector. -/
def oppositeProjector (n : ℕ) : Presented n :=
  reflectedOpposite n (ZeroHecke.projector n)

/-- Longest-word comparison: reversing the fixed longest word is explicit. -/
theorem oppositeProjector_eq_unsignedProduct (n : ℕ) :
    oppositeProjector n =
      unsignedProduct (LongestDivided.wordIn n (n + 2) le_rfl).reverse := by
  rw [unsignedProduct_eq_reflectedOpposite, List.reverse_reverse]
  rfl

/-- Every reduced longest word gives the same unsigned comparison projector. -/
theorem oppositeProjector_eq_of_reduced (w : Word n) (hw : Reduced w)
    (hp : permutation w = LongestElementary.longest (n + 2)) :
    oppositeProjector n = unsignedProduct w := by
  rw [unsignedProduct_eq_reflectedOpposite]
  apply congrArg (reflectedOpposite n)
  apply ZeroHecke.projector_eq_of_length w.reverse (reduced_reverse w hw)
  rw [List.length_reverse, hw, hp, LongestFactor.length_longest]

/-- The comparison projector is idempotent, with no assumed decomposition. -/
theorem oppositeProjector_idempotent (n : ℕ) : IsIdempotentElem (oppositeProjector n) := by
  change reflectedOpposite n (ZeroHecke.projector n) *
    reflectedOpposite n (ZeroHecke.projector n) = reflectedOpposite n (ZeroHecke.projector n)
  rw [← reflectedOpposite_mul, ZeroHecke.projector_mul_projector]

/-- Nonvanishing transfers through the two already constructed injective reflections. -/
theorem oppositeProjector_ne_zero (n : ℕ) : oppositeProjector n ≠ 0 := by
  intro h
  have he : reverseLinear n (OnhReflection.sigma n (ZeroHecke.projector n)) =
      reverseLinear n 0 := by simpa [oppositeProjector, reflectedOpposite] using h
  have hs := (reverseEquiv n).injective he
  have hz : OnhReflection.sigma n (ZeroHecke.projector n) = OnhReflection.sigma n 0 := by
    simpa using hs
  exact OnhStructure.projector_ne_zero n ((OnhReflection.sigma n).injective hz)

/-! ## Homogeneity in the existing integral and parity gradings -/

open EQOnhDG

/-- The corrected generator has degree zero in the existing internal grading
of the presented ring. This grading assigns a dot degree one; zero is
unchanged by the source's rescaling by `2dᵢ`. -/
theorem unsignedGenerator_degree (i : Fin (n + 1)) :
    unsignedGenerator n i ∈ grading n 0 := by
  simpa [unsignedGenerator, sourceDot, sourceCrossing] using
    mul_mem_grading (crossing_mem_grading n i.rev) (dot_mem_grading n i.castSucc.rev)

/-- Every corrected word has degree zero, without a reducedness hypothesis. -/
theorem unsignedProduct_degree (w : Word n) : unsignedProduct w ∈ grading n 0 := by
  induction w with
  | nil => exact one_mem_grading n
  | cons i w ih => simpa [unsignedProduct] using
      mul_mem_grading (unsignedGenerator_degree i) ih

/-- The corrected longest projector has degree zero. -/
theorem oppositeProjector_degree (n : ℕ) : oppositeProjector n ∈ grading n 0 := by
  rw [oppositeProjector_eq_unsignedProduct]
  exact unsignedProduct_degree _

open OddMath.Diagrams.OddNilHecke

/-- Even parity is membership in the existing diagrammatic parity grading. -/
theorem unsignedGenerator_even (i : Fin (n + 1)) :
    unsignedGenerator n i ∈ parity n 0 :=
  grading_le_parity n 0 (unsignedGenerator_degree i)

/-- Every corrected word is even. -/
theorem unsignedProduct_even (w : Word n) : unsignedProduct w ∈ parity n 0 :=
  grading_le_parity n 0 (unsignedProduct_degree w)

/-- The longest projector is even in the presented-ring/diagram comparison. -/
theorem oppositeProjector_even (n : ℕ) : oppositeProjector n ∈ parity n 0 :=
  grading_le_parity n 0 (oppositeProjector_degree n)

/-- The corrected `D_w`, choosing a reduced expression only internally. -/
def demazure (p : Perm n) : Presented n := unsignedProduct (chosenWord p)

/-- The chosen expression does not affect `D_w`. -/
theorem demazure_eq (p : Perm n) (w : Word n) (hw : Reduced w)
    (hp : permutation w = p) : demazure p = unsignedProduct w :=
  unsignedProduct_reduced_eq _ _ (chosenWord_reduced p) hw
    ((chosenWord_permutation p).trans hp.symm)

/-- The permutation-indexed construction recovers the corrected longest projector. -/
theorem demazure_longest (n : ℕ) :
    demazure (n := n) (LongestElementary.longest (n + 2)) = oppositeProjector n :=
  unsignedProduct_longest _ (chosenWord_reduced _) (chosenWord_permutation _)

/-- The corrected odd longest idempotent in every rank, including the empty
products in ranks zero and one. Uses the existing all-rank odd nilHecke ring. -/
def dividedPower : (a : ℕ) → SmallRank.ONH a
  | 0 => 1
  | 1 => 1
  | n + 2 => oppositeProjector n

/-- The corrected odd longest product is idempotent in every rank. -/
theorem dividedPower_idempotent (a : ℕ) : IsIdempotentElem (dividedPower a) := by
  match a with
  | 0 => exact one_mul _
  | 1 => exact one_mul _
  | n + 2 => exact oppositeProjector_idempotent n

end

/-! ## Rational scalar extension

The integral quotient above is a construction tool, not an admissible odd-colour ground ring
for BE2. Extend both its algebra and its polynomial representation to ℚ. The constant-coefficient
functional below proves that the constant polynomial survives this extension.
-/

open scoped TensorProduct
open OddMath.SkewPolynomial (SkewPolynomial)

variable {n : ℕ}

/-- The odd nilHecke algebra obtained by extending the integral presentation to ℚ. -/
abbrev RationalPresented (n : ℕ) := ℚ ⊗[ℤ] Presented n

/-- Rational skew polynomials, obtained from the integral polynomial module by scalar extension. -/
abbrev RationalPolynomial (n : ℕ) := ℚ ⊗[ℤ] SkewPolynomial (n + 2)

/-- Canonical map from the integral presentation, preserving all seven source relation families. -/
noncomputable def rationalInclude (n : ℕ) : Presented n →ₐ[ℤ] RationalPresented n :=
  Algebra.TensorProduct.includeRight

/-- Scalar extension of the constructed polynomial action, not an assumed representation. -/
noncomputable def rationalAction (n : ℕ) :
    RationalPresented n →ₐ[ℚ] Module.End ℚ (RationalPolynomial n) :=
  AlgHom.liftEquiv ℤ ℚ _ _
    ((Module.End.baseChangeHom ℤ ℚ (SkewPolynomial (n + 2))).comp
      (action n).toIntAlgHom)

/-- The constant polynomial after scalar extension. -/
noncomputable def rationalOne (n : ℕ) : RationalPolynomial n := 1 ⊗ₜ[ℤ] (1 : SkewPolynomial (n + 2))

/-- Constant coefficient followed by the actual integer-to-rational coefficient map. -/
noncomputable def rationalConstantCoeff (n : ℕ) : RationalPolynomial n →ₗ[ℚ] ℚ :=
  LinearMap.liftBaseChange ℚ
    ((Int.castAddHom ℚ).toIntLinearMap.comp (Finsupp.lapply (R := ℤ) 0))

/-- The constant polynomial has coefficient one; in particular scalar extension is nonzero here. -/
theorem rationalConstantCoeff_one (n : ℕ) : rationalConstantCoeff n (rationalOne n) = 1 := by
  simp only [rationalConstantCoeff, rationalOne, LinearMap.liftBaseChange_tmul, one_smul]
  change ((1 : SkewPolynomial (n + 2)) 0 : ℚ) = 1
  rw [show (1 : SkewPolynomial (n + 2)) 0 = 1 from Finsupp.single_eq_same]
  rfl

/-- Nonvanishing is certified by the coefficient functional, with no torsion-freeness assumption. -/
theorem rationalOne_ne_zero (n : ℕ) : rationalOne n ≠ 0 := by
  intro h
  have he := rationalConstantCoeff_one n
  rw [h, map_zero] at he
  exact zero_ne_one he

/-- The source ground-ring requirement for odd colours holds over ℚ. -/
theorem rational_two_isUnit : IsUnit (2 : ℚ) := by norm_num

/-- Evaluation of the extended representation on pure tensors. -/
theorem rationalAction_include_tmul (n : ℕ) (a : Presented n) (q : ℚ)
    (p : SkewPolynomial (n + 2)) :
    rationalAction n (rationalInclude n a) (q ⊗ₜ[ℤ] p) =
      q ⊗ₜ[ℤ] (action n a p) := by
  change (1 : ℚ) • ((action n a).baseChange ℚ) (q ⊗ₜ[ℤ] p) = _
  simp

/-- Every defining source relator is zero in the scalar-extended polynomial action. -/
theorem rationalAction_relation (n : ℕ) (w : Free n) (hw : w ∈ relSet n) :
    (freeAction n w).baseChange ℚ = 0 := by
  rw [relation_killed n w hw]
  exact LinearMap.baseChange_zero

/-- The literal printed odd generator after extension to the admissible field ℚ. -/
noncomputable def rationalPrintedGenerator (n : ℕ) (r : Fin (n + 1)) :
    RationalPresented n := rationalInclude n (printedGenerator n r)

/-- The unsigned, corrected odd generator over ℚ. -/
noncomputable def rationalUnsignedGenerator (n : ℕ) (r : Fin (n + 1)) :
    RationalPresented n := rationalInclude n (unsignedGenerator n r)

/-- The printed generator acts by minus one on the nonzero constant polynomial over ℚ. -/
theorem rationalPrintedGenerator_one (r : Fin (n + 1)) :
    rationalAction n (rationalPrintedGenerator n r) (rationalOne n) = -rationalOne n := by
  rw [rationalPrintedGenerator, rationalOne, rationalAction_include_tmul,
    action_printedGenerator_one, TensorProduct.tmul_neg]

/-- The literal printed odd element is nonzero over an admissible characteristic-zero field. -/
theorem rationalPrintedGenerator_ne_zero (r : Fin (n + 1)) :
    rationalPrintedGenerator n r ≠ 0 := by
  intro h
  have he := rationalPrintedGenerator_one r
  rw [h, map_zero, LinearMap.zero_apply] at he
  exact rationalOne_ne_zero n (neg_eq_zero.mp he.symm)

/-- The printed odd generator is not idempotent over ℚ, detected by its constant coefficient. -/
theorem rationalPrintedGenerator_not_idempotent (r : Fin (n + 1)) :
    ¬ IsIdempotentElem (rationalPrintedGenerator n r) := by
  intro h
  have he := congrArg (fun a => rationalConstantCoeff n
    (rationalAction n a (rationalOne n))) h
  simp only [map_mul, Module.End.mul_apply, rationalPrintedGenerator_one, map_neg,
    neg_neg, rationalConstantCoeff_one] at he
  norm_num at he

/-- The corrected element remains idempotent after scalar extension. -/
theorem rationalUnsignedGenerator_idempotent (r : Fin (n + 1)) :
    IsIdempotentElem (rationalUnsignedGenerator n r) := by
  change rationalInclude n (unsignedGenerator n r) * rationalInclude n (unsignedGenerator n r) = _
  rw [← map_mul, unsignedGenerator_sq r]
  rfl

/-! ## Principal left ideals and word signs

Right multiplication has image the principal LEFT ideal. Equality below is equality of actual
left submodules, not merely an abstract isomorphism and not equality of right ideals.
These equalities do not yet supply the graded projective decomposition or its Q/Π normalization.
-/

/-- Negating the generator leaves the actual principal left ideal unchanged. -/
theorem range_mulRight_neg {A : Type*} [Ring A] (a : A) :
    LinearMap.range (LinearMap.mulRight A (-a)) =
      LinearMap.range (LinearMap.mulRight A a) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨-y, by simp⟩
  · rintro ⟨y, rfl⟩
    exact ⟨-y, by simp⟩

/-- The sign correction preserves the principal left ideal in the integral presentation. -/
theorem printedGenerator_leftIdeal (r : Fin (n + 1)) :
    LinearMap.range (LinearMap.mulRight (Presented n) (printedGenerator n r)) =
      LinearMap.range (LinearMap.mulRight (Presented n) (unsignedGenerator n r)) := by
  rw [printedGenerator_eq_neg, range_mulRight_neg]

/-- The same equality of left modules holds over the admissible field ℚ. -/
theorem rationalPrintedGenerator_leftIdeal (r : Fin (n + 1)) :
    LinearMap.range (LinearMap.mulRight (RationalPresented n) (rationalPrintedGenerator n r)) =
      LinearMap.range
        (LinearMap.mulRight (RationalPresented n) (rationalUnsignedGenerator n r)) := by
  unfold rationalPrintedGenerator rationalUnsignedGenerator
  rw [printedGenerator_eq_neg, map_neg, range_mulRight_neg]

/-- A fixed word of printed generators differs from the unsigned word by its length sign. -/
theorem printed_word_sign (w : List (Fin (n + 1))) :
    (w.map (printedGenerator n)).prod =
      (-1 : Presented n) ^ w.length * (w.map (unsignedGenerator n)).prod := by
  induction w with
  | nil => simp
  | cons r w ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, ih, printedGenerator_eq_neg]
    rw [pow_succ']
    simp only [neg_mul, neg_inj, one_mul]
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    exact (Commute.neg_one_left (unsignedGenerator n r)).pow_left w.length |>.eq.symm

/-- The recursive unsigned product agrees with the written-order list product. -/
theorem unsignedProduct_eq_list_prod (w : Word n) :
    unsignedProduct w = (w.map (unsignedGenerator n)).prod := by
  induction w with
  | nil => rfl
  | cons r w ih =>
      simp only [unsignedProduct, List.map_cons, List.prod_cons, ih]

/-- The explicit length sign for any reduced longest word. -/
theorem printed_longest_sign (w : Word n) (hw : Reduced w)
    (hp : permutation w = LongestElementary.longest (n + 2)) :
    (w.map (printedGenerator n)).prod = (-1 : Presented n) ^ w.length * oppositeProjector n := by
  rw [printed_word_sign, oppositeProjector_eq_of_reduced w hw hp, unsignedProduct_eq_list_prod]

/-- A central length sign does not change the actual principal left ideal. -/
theorem range_mulRight_sign {A : Type*} [Ring A] (k : ℕ) (a : A) :
    LinearMap.range (LinearMap.mulRight A ((-1 : A) ^ k * a)) =
      LinearMap.range (LinearMap.mulRight A a) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', neg_one_mul, neg_mul, range_mulRight_neg, ih]

/-- Every fixed printed word generates the same left ideal as its unsigned word. -/
theorem printed_word_leftIdeal (w : Word n) :
    LinearMap.range (LinearMap.mulRight (Presented n) (w.map (printedGenerator n)).prod) =
      LinearMap.range (LinearMap.mulRight (Presented n) (unsignedProduct w)) := by
  rw [printed_word_sign, range_mulRight_sign, unsignedProduct_eq_list_prod]

/-- A reduced longest printed word generates precisely the corrected projector's left module. -/
theorem printed_longest_leftIdeal (w : Word n) (hw : Reduced w)
    (hp : permutation w = LongestElementary.longest (n + 2)) :
    LinearMap.range (LinearMap.mulRight (Presented n) (w.map (printedGenerator n)).prod) =
      LinearMap.range (LinearMap.mulRight (Presented n) (oppositeProjector n)) := by
  rw [printed_word_leftIdeal, oppositeProjector_eq_of_reduced w hw hp]

/-- The reduced-longest left-module equality also holds after extension to ℚ. -/
theorem rationalPrinted_longest_leftIdeal (w : Word n) (hw : Reduced w)
    (hp : permutation w = LongestElementary.longest (n + 2)) :
    LinearMap.range (LinearMap.mulRight (RationalPresented n)
      (rationalInclude n (w.map (printedGenerator n)).prod)) =
      LinearMap.range (LinearMap.mulRight (RationalPresented n)
        (rationalInclude n (oppositeProjector n))) := by
  rw [printed_longest_sign w hw hp, map_mul, map_pow, map_neg, map_one, range_mulRight_sign]

end OddMath.SKM.DividedPowerIdempotents
