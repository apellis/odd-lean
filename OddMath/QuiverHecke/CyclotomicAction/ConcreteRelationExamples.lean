/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.MixedComparison
import OddMath.QuiverHecke.CyclotomicAction.BraidCorrection
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ParameterTransport

/-!
# Concrete asymmetric transported-parameter consumers

Consumers of the super port of
`Categorification/KLR/CyclotomicAction/Square.lean` and
`Categorification/KLR/CyclotomicAction/MixedComparison.lean`.
The all-odd datum with Cartan matrix `[[2,-2],[-4,2]]` uses the transported
quadratic `u²-v⁴`. The equations below hold in the concrete word endomorphism
rings and their actual cyclotomic matrix quotients, not a freely specified
representation. They do not prove nonvanishing or local inversion.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke.CyclotomicAction.ConcreteRelationExamples
open AsymmetricParameters

/-- The involutive general coefficient transport recovers the asymmetric leading units. -/
theorem parameterTwist_asymmetric_t (i j : Bool) :
    (parameterTwist datum scalars).t i j = transportedScalars.t i j := by
  cases i <;> cases j <;>
    norm_num [parameterTwist, parameterSignUnit, parameterSignExponent, scalars,
      transportedScalars, datum, SKM.Datum.dn, SKM.Datum.d, SKM.Datum.h, SKM.Datum.α]
  decide

/-- The zero mixed coefficients remain zero under the same transport. -/
theorem parameterTwist_asymmetric_s (i j : Bool) (p q : ℕ) :
    (parameterTwist datum scalars).s i j p q = transportedScalars.s i j p q := by
  simp [parameterTwist, scalars, transportedScalars]

/-- The transported word polynomial is exactly the quadratic-minus-quartic expression. -/
theorem transported_word_quadratic (t : List Bool) (r : ℕ) :
    wordQuadratic datum transportedScalars false true t r =
      dotE datum transportedScalars t r ^ 2 - dotE datum transportedScalars t (r + 1) ^ 4 := by
  have hd : datum.d false true ≠ 0 := by decide
  have h₂ : datum.dn false true = 2 := rfl
  have h₄ : datum.dn true false = 4 := rfl
  simp [wordQuadratic, hd, h₂, h₄, transportedScalars, sub_eq_add_neg]

/-- Actual affine mixed crossing square for the asymmetric transported parameters. -/
theorem transported_affine_square (n : ℕ) :
    affineLastCrossing datum transportedScalars true false n *
        affineLastCrossing datum transportedScalars false true n =
      ∑ w : Word Bool n, FiniteHomMatrix.single (appendWord true (appendWord false w))
        (appendWord true (appendWord false w))
        (dotE datum transportedScalars (appendWord true (appendWord false w)).1 w.1.length ^ 2 -
          dotE datum transportedScalars (appendWord true (appendWord false w)).1
            (w.1.length + 1) ^ 4) := by
  rw [affineLastCrossing_mixed datum transportedScalars false true (by decide)]
  simp only [affinePairQuadratic, transported_word_quadratic]

/-- The transported quadratic relation holds after every specified cyclotomic quotient. -/
theorem transported_cyclotomic_square (a : Bool → _root_.Polynomial ℚ) (n : ℕ) :
    cyclotomicLastCrossing datum transportedScalars true false a n *
        cyclotomicLastCrossing datum transportedScalars false true a n =
      cyclotomicMk datum transportedScalars a (n + 1 + 1)
        (∑ w : Word Bool (n + 1), FiniteHomMatrix.single (appendWord true (appendWord false w))
          (appendWord true (appendWord false w))
          (dotE datum transportedScalars (appendWord true (appendWord false w)).1 w.1.length ^ 2 -
            dotE datum transportedScalars (appendWord true (appendWord false w)).1
              (w.1.length + 1) ^ 4)) := by
  simp only [cyclotomicLastCrossing, ← map_mul]
  rw [transported_affine_square]

/-- The actual two odd corner maps carry the minus sign, not the unsigned square. -/
theorem transported_signed_square (a : Bool → _root_.Polynomial ℚ)
    (ha : CyclotomicPolynomialParity datum a) (n : ℕ) {p : ZMod 2}
    (x : (compositionCorner datum transportedScalars true false a ha n).toSVec)
    (hx : x ∈ (compositionCorner datum transportedScalars true false a ha n).toSVec.part p) :
    ((compositionSuperCrossing datum transportedScalars false true a ha n).1
      ((compositionSuperCrossing datum transportedScalars true false a ha n).1 x)).val =
      -(x.val * cyclotomicPairQuadratic datum transportedScalars false true a n) := by
  simpa only [show datum.parity true * datum.parity false = 1 from rfl,
    Supercategory.koszulSign_one_one, neg_one_zsmul] using
      compositionSuperCrossing_mixed_apply datum transportedScalars true false (by decide)
        a ha n x hx

/-- The signed odd repeated-colour correction is the last dot minus the first. -/
theorem transported_word_braid_correction {n : ℕ} (w : Word Bool n) :
    tripleBraidCorrection datum transportedScalars false true w =
      dotE datum transportedScalars (tripleWord false true false w).1 (w.1.length + 2) -
        dotE datum transportedScalars (tripleWord false true false w).1 w.1.length := by
  have h₂ : datum.dn false true = 2 := rfl
  have h₄ : datum.dn true false = 4 := rfl
  have hi : datum.parity false = 1 := rfl
  have hj : datum.parity true = 1 := rfl
  simp [tripleBraidCorrection, transportedScalars, h₂, h₄, Finset.sum_range_succ,
    hi, hj, SKM.zsign, sub_eq_add_neg, add_comm]

/-- This is the repeated-colour braid of the actual affine corner matrices. -/
theorem transported_affine_braid_correction (n : ℕ) :
    affineTripleLeft datum transportedScalars true false false n *
        (affineTripleRight datum transportedScalars true false false n *
          affineTripleLeft datum transportedScalars false true false n) -
      affineTripleRight datum transportedScalars false false true n *
        (affineTripleLeft datum transportedScalars false false true n *
          affineTripleRight datum transportedScalars false true false n) =
      tripleMatrix datum transportedScalars false true false false true false
        (fun w : Word Bool n =>
          dotE datum transportedScalars (tripleWord false true false w).1 (w.1.length + 2) -
            dotE datum transportedScalars (tripleWord false true false w).1 w.1.length) := by
  rw [affineTriple_braid_correction datum transportedScalars false true (by decide)]
  unfold affineTripleBraidCorrection
  congr 1
  funext w
  exact transported_word_braid_correction w

end OddMath.QuiverHecke.CyclotomicAction.ConcreteRelationExamples
