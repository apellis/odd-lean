/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TensorGram.FiniteGram
import OddMath.CoveringQuantum.PreF.BaseChange

/-!
# Coefficient-bar identities for root-graded derivatives

Inverse bicharacters exchange left and right derivatives on the free half
algebra. Root multidegrees are retained independently of their weight images.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.BarDerivatives
open PreF Coefficients GenericVerma PolarizationTransport

section General
variable {k I : Type*} [CommRing k] [DecidableEq I]

/-- Inverse bicharacters exchange right and left derivatives, without a basis hypothesis. -/
theorem inverse_rDeriv (χ ψ : Bichar k I) (hinv : ∀ i j, χ i j * ψ i j = 1)
    (i : I) (x : PreF k I) : rDeriv ψ i x = twist ψ i (lDeriv χ i x) := by
  induction x using PreF.induction_left with
  | algebraMap c => simp
  | smul c x hx => simp only [map_smul, hx]
  | add x y hx hy => simp only [map_add, hx, hy]
  | θ_mul j x hx =>
    rw [rDeriv_θ_mul, lDeriv_θ_mul, map_add, map_smul, map_mul, twist_θ, hx,
      smul_mul_assoc, smul_smul, hinv, one_smul]
    split_ifs <;> simp [add_comm]

omit [DecidableEq I] in
/-- Inverse twists cancel on the entire free algebra. -/
theorem inverse_twist (χ ψ : Bichar k I) (hinv : ∀ i j, χ i j * ψ i j = 1)
    (i : I) (x : PreF k I) : twist χ i (twist ψ i x) = x := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 j => simp [θ, twist, smul_smul, mul_comm (ψ i j), hinv]
  | mul x y hx hy => simp only [map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Homogeneity of the original left derivative, deduced from actual right
homogeneity and inverse twists, not an independence assertion. -/
theorem inverse_lDeriv_mem (χ ψ : Bichar k I) (hinv : ∀ i j, χ i j * ψ i j = 1)
    (i : I) {μ : I →₀ ℕ} {x : PreF k I}
    (hx : x ∈ weightSpace k (μ + Finsupp.single i 1)) :
    lDeriv χ i x ∈ weightSpace k μ := by
  have he : lDeriv χ i x = twist χ i (rDeriv ψ i x) := by
    rw [inverse_rDeriv χ ψ hinv, inverse_twist χ ψ hinv]
  rw [he]
  exact twist_mem_weightSpace χ i (rDeriv_mem_weightSpace ψ i hx)

end General

variable {I X : Type*} [AddCommGroup X] [DecidableEq I]
variable (D : RootDatum I X)

/-- The actual coefficient bar bicharacter. -/
def barChi : Bichar Coefficients.Ring I where
  toFun i j := bar (D.chi Coefficients.q pi i j)
  symm i j := congrArg bar ((D.chi Coefficients.q pi).comm i j)

omit [DecidableEq I] in
theorem bar_chi (i j : I) : barChi D i j =
    qp Coefficients.q (D.dot i j) * pi ^ (D.parity i * D.parity j).val := by
  change bar (qp Coefficients.q (-D.dot i j) * _) = _
  simp only [map_mul, map_pow, bar_pi, barData.map_qp, neg_neg]

omit [DecidableEq I] in
theorem chi_barChi (i j : I) : D.chi Coefficients.q pi i j * barChi D i j = 1 := by
  rw [bar_chi]
  change (qp Coefficients.q (-D.dot i j) * _) * _ = _
  have hp : (pi ^ (D.parity i * D.parity j).val) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm _ 2, pow_mul, pi_sq, one_pow]
  calc
    _ = (qp Coefficients.q (-D.dot i j) * qp Coefficients.q (D.dot i j)) *
        (pi ^ (D.parity i * D.parity j).val) ^ 2 := by ring
    _ = 1 := by rw [qp_mul, neg_add_cancel, qp_zero, hp, mul_one]

/-- Coefficient bar, followed by the actual inverse-bicharacter conversion. -/
theorem bar_rDeriv (i : I) (x : PreF Coefficients.Ring I) :
    FreeAlgebra.mapCoeffs bar (rDeriv (D.chi Coefficients.q pi) i x) =
      twist (barChi D) i (lDeriv (D.chi Coefficients.q pi) i
        (FreeAlgebra.mapCoeffs bar x)) := by
  rw [mapCoeffs_rDeriv bar (D.chi Coefficients.q pi) (barChi D) (fun _ _ ↦ rfl),
    inverse_rDeriv _ _ (chi_barChi D)]

omit [DecidableEq I] in
/-- The word-level bar fixes every generator; no reversal of words occurs. -/
theorem bar_monomial (w : List I) :
    FreeAlgebra.mapCoeffs bar (monomial Coefficients.Ring w) = monomial Coefficients.Ring w := by
  induction w with
  | nil => simp
  | cons i w ih => simp only [monomial_cons, map_mul, θ, FreeAlgebra.mapCoeffs_ι, ih]

/-- Right-to-left conversion on every word, with its full degree twist retained. -/
theorem bar_rDeriv_word (i : I) (w : List I) :
    FreeAlgebra.mapCoeffs bar (rDeriv (D.chi Coefficients.q pi) i
      (monomial Coefficients.Ring w)) =
    twist (barChi D) i (lDeriv (D.chi Coefficients.q pi) i
      (monomial Coefficients.Ring w)) := by
  rw [bar_rDeriv, bar_monomial]

omit [DecidableEq I] in
/-- Coefficient bar preserves each free root-lattice homogeneous submodule. -/
theorem bar_mem_weightSpace {ν : I →₀ ℕ} {x : PreF Coefficients.Ring I}
    (hx : x ∈ weightSpace Coefficients.Ring ν) :
    FreeAlgebra.mapCoeffs bar x ∈ weightSpace Coefficients.Ring ν := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [bar_monomial]
    exact hw ▸ monomial_mem_weightSpace w
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [FreeAlgebra.mapCoeffs_smul]; exact Submodule.smul_mem _ _ hx

/-- Explicit total-degree scalar conversion for every homogeneous free element. -/
theorem bar_rDeriv_homogeneous (i : I) {μ : I →₀ ℕ} {x : PreF Coefficients.Ring I}
    (hx : x ∈ weightSpace Coefficients.Ring (μ + Finsupp.single i 1)) :
    FreeAlgebra.mapCoeffs bar (rDeriv (D.chi Coefficients.q pi) i x) =
      (barChi D).wt (Finsupp.single i 1) μ •
        lDeriv (D.chi Coefficients.q pi) i (FreeAlgebra.mapCoeffs bar x) := by
  rw [bar_rDeriv]
  exact twist_of_mem i (inverse_lDeriv_mem _ _ (chi_barChi D) i (bar_mem_weightSpace hx))

/-- The explicit homogeneous-word version, retaining its actual root multidegree. -/
theorem bar_rDeriv_word_degree (i : I) (w : List I) (μ : I →₀ ℕ)
    (hw : wordWeight w = μ + Finsupp.single i 1) :
    FreeAlgebra.mapCoeffs bar (rDeriv (D.chi Coefficients.q pi) i
      (monomial Coefficients.Ring w)) =
      (barChi D).wt (Finsupp.single i 1) μ •
        lDeriv (D.chi Coefficients.q pi) i (monomial Coefficients.Ring w) := by
  rw [bar_rDeriv_homogeneous D i (hw ▸ monomial_mem_weightSpace w), bar_monomial]

/-- Bar of the parity-weighted right derivative is the positive weight twist
of the original left derivative. This holds on the entire free algebra. -/
theorem bar_parity_rDeriv (i : I) (x : PreF Coefficients.Ring I) :
    FreeAlgebra.mapCoeffs bar
      (parityTwist D.toSuperCartanDatum pi i (rDeriv (D.chi Coefficients.q pi) i x)) =
    weightTwist D.toSuperCartanDatum Coefficients.q i
      (lDeriv (D.chi Coefficients.q pi) i (FreeAlgebra.mapCoeffs bar x)) := by
  have hm (y : PreF Coefficients.Ring I) :
      FreeAlgebra.mapCoeffs bar (parityTwist D.toSuperCartanDatum pi i y) =
      parityTwist D.toSuperCartanDatum pi i (FreeAlgebra.mapCoeffs bar y) := by
    induction y using FreeAlgebra.induction with
    | grade0 c => simp
    | grade1 j => simp [parityTwist, FreeAlgebra.mapCoeffs_smul]
    | mul y z hy hz => simp only [map_mul, hy, hz]
    | add y z hy hz => simp only [map_add, hy, hz]
  rw [hm, bar_rDeriv, parityTwist, twist, diagTwist_diagTwist]
  have hc : (fun j ↦ pi ^ (D.parity i * D.parity j).val) * (fun j ↦ barChi D i j) =
      (fun j ↦ ((Coefficients.q ^ D.dot i j : Coefficients.Ringˣ) : Coefficients.Ring)) := by
    funext j
    simp only [Pi.mul_apply, bar_chi]
    have hp : (pi ^ (D.parity i * D.parity j).val) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm _ 2, pow_mul, pi_sq, one_pow]
    change _ = qp Coefficients.q (D.dot i j)
    calc
      _ = qp Coefficients.q (D.dot i j) * (pi ^ (D.parity i * D.parity j).val) ^ 2 := by ring
      _ = _ := by rw [hp, mul_one]
  rw [hc]
  rfl

/-- The exact scalar preceding either branch in the existing word polynomial. -/
def stepScalar (i : I) (w : List I) : Coefficients.Ring :=
  D.norm Coefficients.q pi i *
    ((D.qi Coefficients.q i ^ (-D.h i (halfWeight D true (wordWeight w))) :
      Coefficients.Ringˣ) : Coefficients.Ring)

/-- Select the top branch in the ACTUAL `wordPolynomial` recursion. -/
def topBranch : List I → PreF Coefficients.Ring I →ₗ[Coefficients.Ring] Coefficients.Ring
  | [] => counit.toLinearMap
  | i :: w => (-stepScalar D i w) •
      ((topBranch w).comp ((parityTwist D.toSuperCartanDatum pi i).toLinearMap.comp
        (rDeriv (D.chi Coefficients.q pi) i)))

/-- Explicit highest-coefficient normalization for the first word, independent
of the second test argument and both highest weights. -/
def topScale : List I → Coefficients.Ring
  | [] => 1
  | i :: w => (D.pii pi i * qp Coefficients.q (2 * D.d i) *
      qp Coefficients.q (2 * D.d i * D.h i (halfWeight D true (wordWeight w)))) * topScale w

omit [DecidableEq I] in
private theorem step_bar (i : I) (w : List I) :
    -bar (stepScalar D i w) *
      ((D.qi Coefficients.q i ^ D.h i (halfWeight D true (wordWeight w)) :
        Coefficients.Ringˣ) : Coefficients.Ring) =
    (D.pii pi i * qp Coefficients.q (2 * D.d i) *
      qp Coefficients.q (2 * D.d i * D.h i (halfWeight D true (wordWeight w)))) *
      D.norm Coefficients.q pi i := by
  rw [stepScalar, map_mul, bar_norm, qi_zpow, qi_zpow, barData.map_qp]
  simp only [mul_neg, neg_neg, neg_mul]
  have hq : qp Coefficients.q (D.d i * D.h i (halfWeight D true (wordWeight w))) *
      qp Coefficients.q (D.d i * D.h i (halfWeight D true (wordWeight w))) =
      qp Coefficients.q (2 * D.d i * D.h i (halfWeight D true (wordWeight w))) := by
    rw [qp_mul]
    congr 1
    ring
  calc
    _ = (D.pii pi i * qp Coefficients.q (2 * D.d i)) *
        (qp Coefficients.q (D.d i * D.h i (halfWeight D true (wordWeight w))) *
        qp Coefficients.q (D.d i * D.h i (halfWeight D true (wordWeight w)))) *
        D.norm Coefficients.q pi i := by ring
    _ = _ := by rw [hq]

/-- All-word leading-branch identity with the original free half form.
The second argument is arbitrary, not necessarily homogeneous. -/
theorem bar_topBranch (w : List I) (y : PreF Coefficients.Ring I) :
    bar (topBranch D w y) = topScale D w *
      D.form Coefficients.q pi (monomial Coefficients.Ring w) (FreeAlgebra.mapCoeffs bar y) := by
  induction w generalizing y with
  | nil => simp [topBranch, topScale, SuperCartanDatum.form, counit_mapCoeffs]
  | cons i w ih =>
    simp only [topBranch, LinearMap.smul_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, smul_eq_mul, map_mul, map_neg, ih, bar_parity_rDeriv]
    have ht (z : PreF Coefficients.Ring I) :
        D.form Coefficients.q pi (monomial Coefficients.Ring w)
          (weightTwist D.toSuperCartanDatum Coefficients.q i z) =
        ((D.qi Coefficients.q i ^ D.h i (halfWeight D true (wordWeight w)) :
          Coefficients.Ringˣ) : Coefficients.Ring) *
        D.form Coefficients.q pi (monomial Coefficients.Ring w) z := by
      have he : D.form Coefficients.q pi
          (weightTwist D.toSuperCartanDatum Coefficients.q i (monomial Coefficients.Ring w)) z =
          D.form Coefficients.q pi (monomial Coefficients.Ring w)
            (weightTwist D.toSuperCartanDatum Coefficients.q i z) := form_diagTwist _ _ _ _ _
      rw [← he, weightTwist_monomial, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [ht, monomial_cons, SuperCartanDatum.form, form_θ_mul]
    change _ = topScale D (i :: w) * (_ * _)
    rw [topScale]
    have hs := step_bar D i w
    linear_combination topScale D w *
      D.form Coefficients.q pi (monomial Coefficients.Ring w)
        (lDeriv (D.chi Coefficients.q pi) i (FreeAlgebra.mapCoeffs bar y)) * hs

/-- In particular, on any two words the second argument has no hidden bar. -/
theorem bar_topBranch_words (w v : List I) :
    bar (topBranch D w (monomial Coefficients.Ring v)) = topScale D w *
      D.form Coefficients.q pi (monomial Coefficients.Ring w) (monomial Coefficients.Ring v) := by
  rw [bar_topBranch, bar_monomial]

omit [DecidableEq I] in
/-- Total root degree of a word, independent of its image in the weight group. -/
theorem wordWeight_sum (w : List I) : (wordWeight w).sum (fun _ n ↦ n) = w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [wordWeight_cons, Finsupp.sum_add_index' (by simp) (by intros; rfl)]
    simp only [Finsupp.sum_single_index, ih, List.length_cons]
    omega

/-- The selected branch really is the coefficient of the full word multidegree
in the library's existing comparison polynomial. -/
theorem coeff_wordPolynomial (w : List I) (y : PreF Coefficients.Ring I) :
    (wordPolynomial D w y).coeff (wordWeight w) = topBranch D w y := by
  induction w generalizing y with
  | nil => simp [wordPolynomial, topBranch]
  | cons i w ih =>
    have hz : (wordPolynomial D w
        (weightTwist D.toSuperCartanDatum Coefficients.q i
          (lDeriv (D.chi Coefficients.q pi) i y))).coeff (wordWeight (i :: w)) = 0 := by
      apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
      have hd := wordPolynomial_totalDegree D w
        (weightTwist D.toSuperCartanDatum Coefficients.q i
          (lDeriv (D.chi Coefficients.q pi) i y))
      have hs := wordWeight_sum (i :: w)
      change (wordWeight (i :: w)).sum (fun _ n ↦ n) = (i :: w).length at hs
      change _ < (wordWeight (i :: w)).sum (fun _ n ↦ n)
      rw [hs, List.length_cons]
      omega
    rw [wordPolynomial, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_sub, hz,
      wordWeight_cons, MvPolynomial.coeff_X_mul, ih]
    simp [topBranch, stepScalar, smul_eq_mul]

/-- Exact coefficient-bar identity for every word and every free-half argument.
This is the leading coefficient of the actual existing polynomial, not a newly
assumed comparison form. -/
theorem bar_coeff_wordPolynomial (w : List I) (y : PreF Coefficients.Ring I) :
    bar ((wordPolynomial D w y).coeff (wordWeight w)) = topScale D w *
      D.form Coefficients.q pi (monomial Coefficients.Ring w) (FreeAlgebra.mapCoeffs bar y) := by
  rw [coeff_wordPolynomial, bar_topBranch]

/-- The requested all-word version, over the actual covering coefficient ring. -/
theorem bar_coeff_wordPolynomial_words (w v : List I) :
    bar ((wordPolynomial D w (monomial Coefficients.Ring v)).coeff (wordWeight w)) =
      topScale D w * D.form Coefficients.q pi
        (monomial Coefficients.Ring w) (monomial Coefficients.Ring v) := by
  rw [bar_coeff_wordPolynomial, bar_monomial]

omit [DecidableEq I] in
/-- The leading normalization is a unit in the covering ring, with explicit
inverse its coefficient bar. No field cancellation is used. -/
theorem topScale_bar (w : List I) : topScale D w * bar (topScale D w) = 1 := by
  induction w with
  | nil => simp [topScale]
  | cons i w ih =>
    simp only [topScale, map_mul, barData.map_pii, barData.map_qp]
    have hq (a : ℤ) : qp Coefficients.q a * qp Coefficients.q (-a) = 1 := by
      rw [qp_mul, add_neg_cancel, qp_zero]
    calc
      _ = (D.pii pi i ^ 2) *
          (qp Coefficients.q (2 * D.d i) * qp Coefficients.q (-(2 * D.d i))) *
          (qp Coefficients.q (2 * D.d i * D.h i (halfWeight D true (wordWeight w))) *
            qp Coefficients.q (-(2 * D.d i * D.h i (halfWeight D true (wordWeight w))))) *
          (topScale D w * bar (topScale D w)) := by ring
      _ = 1 := by rw [D.pii_sq pi pi_sq, hq, hq, ih]; simp

/-- Normalized exact all-word leading coefficient, equal to the ORIGINAL form. -/
theorem normalized_bar_coeff_wordPolynomial (w v : List I) :
    bar (topScale D w) *
      bar ((wordPolynomial D w (monomial Coefficients.Ring v)).coeff (wordWeight w)) =
      D.form Coefficients.q pi (monomial Coefficients.Ring w) (monomial Coefficients.Ring v) := by
  rw [bar_coeff_wordPolynomial_words, ← mul_assoc, mul_comm (bar (topScale D w)),
    topScale_bar, one_mul]

end OddMath.CoveringQuantum.UDot.BarDerivatives
