/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.QAdic
import OddMath.CoveringQuantum.UDot.VermaComparison

/-!
# The q-adic limit of the normalized Verma polarization

After each specialization pi = +1 or -1, the actual normalized Verma form
converges to the existing half form. The proof bounds every coefficient in the
finite error support, including coefficients with negative q-order. It applies
to arbitrary finite free inputs, not only homogeneous elements or single words.

The topology is the q-adic topology at q = 0 (source parameter v = q^-1).
The normalization is the explicit wordwise pi-sign required by BE2 rho / Clark
IV tau1-prime, not the untwisted CHWII tau1 polarization. This supplies the
valuation step underlying the comparison in CHWII Proposition 6.10; it is not
integrable-quotient descent or the tensor-module limit of Clark IV Proposition
5.11. Filter nonvacuity is characterized separately and is not asserted for an
arbitrary root datum. No nondegeneracy is inferred from this half comparison.

Unlike the finite, bar-consistent setting of those sources, the algebraic
comparison, finite-support order bounds and conditional convergence here allow
arbitrary colour types without bar-consistency. The positive-weight criterion
for filter nonvacuity still requires finitely many colours.
-/

noncomputable section
open scoped Topology
open Filter
namespace OddMath.CoveringQuantum.UDot.GenericVerma
open PreF Coefficients
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

omit [DecidableEq I] [DecidableEq X] in
private theorem specialize_qi_zpow (ε : RatFunc ℚ) (hε : ε ^ 2 = 1)
    (i : I) (n : ℤ) :
    specialize ε hε ((D.qi Coefficients.q i ^ n : Coefficients.Ringˣ) : Coefficients.Ring) =
      RatFunc.X ^ (D.d i * n) := by
  have hm := map_zpow ((specialize ε hε).toRingHom.toMonoidHom.comp
    (Units.coeHom Coefficients.Ring)) (D.qi Coefficients.q i) n
  change specialize ε hε ((D.qi Coefficients.q i ^ n : Coefficients.Ringˣ) : Coefficients.Ring) =
    (specialize ε hε (D.qi Coefficients.q i : Coefficients.Ring)) ^ n at hm
  rw [hm]
  simp only [SuperCartanDatum.qi, Units.val_pow_eq_pow_val, map_pow, specialize_q]
  rw [← zpow_natCast, ← zpow_mul]

omit [DecidableEq I] [DecidableEq X] in
/-- Each specialization has the same parameter order. The pi factor is an actual
unit of order zero, including at pi = -1. -/
theorem deformationParameter_order (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) (Λ : X) (i : I) :
    QAdic.order (specialize ε hε (deformationParameter D Λ i)) =
      (D.d i * (2 * D.h i Λ) : ℤ) := by
  rw [deformationParameter, map_mul, map_pow, specialize_qi_zpow,
    QAdic.order.map_mul, QAdic.order.map_pow, QAdic.order_X_zpow]
  have hp : QAdic.order (specialize ε hε (D.pii pi i)) = 0 := by
    simp only [SuperCartanDatum.pii, map_pow, specialize_pi, QAdic.order.map_pow]
    rcases sq_eq_one_iff.mp hε with rfl | rfl <;> simp
  simp [hp]

/-- A polynomial error on arbitrary finite free inputs, by actual linear extension
in the first input. It does not postulate a polarization or a norm estimate. -/
def freeComparisonError (y : PreF Coefficients.Ring I) :
    PreF Coefficients.Ring I →ₗ[Coefficients.Ring] MvPolynomial I Coefficients.Ring :=
  (FreeAlgebra.wordBasis Coefficients.Ring I).constr Coefficients.Ring
    (fun w => comparisonError D w y)

omit [DecidableEq X] in
@[simp] theorem freeComparisonError_word (w : List I) (y : PreF Coefficients.Ring I) :
    freeComparisonError D y (monomial Coefficients.Ring w) = comparisonError D w y := by
  simpa only [FreeAlgebra.wordBasis_apply, monomial, freeComparisonError, θ] using
    (Module.Basis.constr_basis (FreeAlgebra.wordBasis Coefficients.Ring I)
      Coefficients.Ring (fun w => comparisonError D w y) w)

omit [DecidableEq X] in
theorem freeComparisonError_constantCoeff (x y : PreF Coefficients.Ring I) :
    MvPolynomial.constantCoeff (freeComparisonError D y x) = 0 := by
  induction x using FreeAlgebra.induction_wordBasis with
  | zero => simp
  | add x z hx hz => simp [hx, hz]
  | smul a x hx => simp [hx]
  | word w =>
    simp only [FreeAlgebra.wordBasis_apply]
    change MvPolynomial.constantCoeff (freeComparisonError D y (monomial Coefficients.Ring w)) = 0
    rw [freeComparisonError_word, comparisonError_constantCoeff]

/-- The rho/tau1-prime normalization is applied wordwise before taking the actual
Verma pairing; it cannot be dropped at pi = -1 or on inhomogeneous inputs. -/
def normalizedPolarization (Λ : X) (x y : PreF Coefficients.Ring I) : Coefficients.Ring :=
  polarization D Λ
    (D.toSerreF Coefficients.q pi (diagTwist (polarizationSign D Λ) x))
    (D.toSerreF Coefficients.q pi y)

/-- Exact finite linear-combination extension of the accepted word comparison. -/
theorem normalizedPolarization_sub_half (Λ : X) (x y : PreF Coefficients.Ring I) :
    normalizedPolarization D Λ x y - D.form Coefficients.q pi x y =
      MvPolynomial.eval (deformationParameter D Λ) (freeComparisonError D y x) := by
  induction x using FreeAlgebra.induction_wordBasis with
  | zero => simp [normalizedPolarization]
  | add x z hx hz =>
    simp only [normalizedPolarization, map_add, LinearMap.add_apply] at hx hz ⊢
    rw [← hx, ← hz]
    ring
  | smul a x hx =>
    simp only [normalizedPolarization, map_smul, LinearMap.smul_apply, smul_eq_mul] at hx ⊢
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
    rw [← hx]
    ring
  | word w =>
    simp only [FreeAlgebra.wordBasis_apply]
    change normalizedPolarization D Λ (monomial Coefficients.Ring w) y -
      D.form Coefficients.q pi (monomial Coefficients.Ring w) y =
      MvPolynomial.eval (deformationParameter D Λ)
        (freeComparisonError D y (monomial Coefficients.Ring w))
    rw [freeComparisonError_word, normalizedPolarization, diagTwist_monomial,
      map_smul, map_smul, LinearMap.smul_apply]
    have h := polarization_sub_half D Λ w y
    simpa only [SuperCartanDatum.serreForm_toSerreF, SuperCartanDatum.form, wordSign,
      smul_eq_mul] using h

/-- Explicit threshold determined by the finite coefficient valuations after a
specified pi specialization, not by polynomial degree. -/
def comparisonThreshold (ε : RatFunc ℚ) (hε : ε ^ 2 = 1)
    (x y : PreF Coefficients.Ring I) (N : ℤ) : ℤ :=
  max 0 (N - QAdic.coefficientFloor (specialize ε hε).toRingHom (freeComparisonError D y x))

/-- Actual q-order of the specialized normalized Verma/half error. Only simple
coroot coordinates present in the finite error support are required to be large. -/
theorem normalizedPolarization_order (ε : RatFunc ℚ) (hε : ε ^ 2 = 1)
    (x y : PreF Coefficients.Ring I) (N : ℤ) (Λ : X)
    (hΛ : ∀ i ∈ (freeComparisonError D y x).vars,
      comparisonThreshold D ε hε x y N ≤ D.h i Λ) :
    (N : WithTop ℤ) ≤ QAdic.order (specialize ε hε
      (normalizedPolarization D Λ x y - D.form Coefficients.q pi x y)) := by
  rw [normalizedPolarization_sub_half]
  change (N : WithTop ℤ) ≤ QAdic.order ((specialize ε hε).toRingHom
    (MvPolynomial.eval (deformationParameter D Λ) (freeComparisonError D y x)))
  rw [MvPolynomial.eval₂_comp]
  apply QAdic.eval_order_lower _ _ (freeComparisonError_constantCoeff D x y)
  intro i hi
  change (comparisonThreshold D ε hε x y N : WithTop ℤ) ≤
    QAdic.order (specialize ε hε (deformationParameter D Λ i))
  rw [deformationParameter_order]
  have hd := D.d_pos i
  have hb : 0 ≤ comparisonThreshold D ε hε x y N := le_max_left _ _
  have hh := hΛ i hi
  change (comparisonThreshold D ε hε x y N : WithTop ℤ) ≤ _
  exact_mod_cast (show comparisonThreshold D ε hε x y N ≤ (D.d i : ℤ) * (2 * D.h i Λ) by
    have hd' : (1 : ℤ) ≤ D.d i := by exact_mod_cast hd
    nlinarith)

/-- A single bound works simultaneously for pi = +1 and pi = -1. -/
theorem normalizedPolarization_order_both (x y : PreF Coefficients.Ring I) (N : ℤ) :
    ∃ B : ℤ, 0 ≤ B ∧ ∀ Λ : X, (∀ i, B ≤ D.h i Λ) →
      (N : WithTop ℤ) ≤ QAdic.order (specialize 1 (one_pow 2)
        (normalizedPolarization D Λ x y - D.form Coefficients.q pi x y)) ∧
      (N : WithTop ℤ) ≤ QAdic.order (specialize (-1) (by norm_num)
        (normalizedPolarization D Λ x y - D.form Coefficients.q pi x y)) := by
  let B := max (comparisonThreshold D 1 (one_pow 2) x y N)
    (comparisonThreshold D (-1) (by norm_num) x y N)
  refine ⟨B, (le_max_left 0 _).trans (le_max_left _ _), ?_⟩
  intro Λ hΛ
  constructor
  · exact normalizedPolarization_order D 1 (one_pow 2) x y N Λ
      (fun i _ => (le_max_left _ _).trans (hΛ i))
  · exact normalizedPolarization_order D (-1) (by norm_num) x y N Λ
      (fun i _ => (le_max_right _ _).trans (hΛ i))

/-- The filter in which every simple-coroot coordinate tends to +infinity.
It may be bottom for a general root datum; nonvacuity is a separate theorem. -/
def coordinateFilter : Filter X :=
  Filter.comap (fun Λ i => D.h i Λ) Filter.atTop

omit [DecidableEq I] [DecidableEq X] in
theorem eventually_coordinate_lower (B : ℤ) :
    ∀ᶠ Λ in coordinateFilter D, ∀ i, B ≤ D.h i Λ := by
  apply Filter.eventually_comap.mpr
  filter_upwards [Filter.eventually_ge_atTop (fun _ : I => B)] with b hb
  intro Λ hΛ i
  rw [congrFun hΛ i]
  exact hb i

/-- Genuine convergence in the X-adic topology of Q(q), for each of the two pi
specializations. This is the normalized actual Verma pairing, not an assumed form.
No existence of large dominant weights is included in this assertion. -/
theorem normalizedPolarization_tendsto (ε : RatFunc ℚ) (hε : ε ^ 2 = 1)
    (x y : PreF Coefficients.Ring I) :
    Tendsto (fun Λ => specialize ε hε (normalizedPolarization D Λ x y))
      (coordinateFilter D) (𝓝 (specialize ε hε (D.form Coefficients.q pi x y))) := by
  have hh : Tendsto (fun Λ => specialize ε hε
      (normalizedPolarization D Λ x y - D.form Coefficients.q pi x y))
      (coordinateFilter D) (𝓝 0) := by
    apply QAdic.tendsto_zero_of_order
    intro N
    filter_upwards [eventually_coordinate_lower D (comparisonThreshold D ε hε x y N)] with Λ hΛ
    exact normalizedPolarization_order D ε hε x y N Λ (fun i _ => hΛ i)
  have hs := hh.add (tendsto_const_nhds (x := specialize ε hε (D.form Coefficients.q pi x y)))
  simpa only [map_sub, sub_add_cancel, zero_add] using hs

omit [DecidableEq I] [DecidableEq X] in
/-- Exact nonvacuity boundary: coordinate convergence is nontrivial precisely when
all coordinate lower bounds can be attained. This is NOT assumed for root data. -/
theorem coordinateFilter_neBot_iff : (coordinateFilter D).NeBot ↔
    ∀ b : I → ℤ, ∃ Λ : X, ∀ i, b i ≤ D.h i Λ := by
  change (Filter.comap (fun Λ i => D.h i Λ) Filter.atTop).NeBot ↔ _
  rw [(Filter.atTop_basis.comap (fun Λ i => D.h i Λ)).neBot_iff]
  constructor
  · intro h b
    exact h trivial
  · intro h b _
    exact h b

omit [DecidableEq I] [DecidableEq X] in
/-- For finite I, a weight with all positive simple-coroot coordinates suffices for
nonvacuity, by its integer multiples. No such weight is silently supplied. -/
theorem coordinateFilter_neBot_of_positive_weight [Finite I] (ξ : X) (hξ : ∀ i, 0 < D.h i ξ) :
    (coordinateFilter D).NeBot := by
  classical
  let _ := Fintype.ofFinite I
  apply (coordinateFilter_neBot_iff D).mpr
  intro b
  let n : ℤ := ∑ i : I, |b i|
  have hn : 0 ≤ n := Finset.sum_nonneg (fun i _ => abs_nonneg (b i))
  refine ⟨n • ξ, fun i => ?_⟩
  have hi : b i ≤ n := (le_abs_self (b i)).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (b j)) (Finset.mem_univ i))
  simp only [map_zsmul, zsmul_eq_mul]
  change b i ≤ n * D.h i ξ
  have hh := hξ i
  nlinarith

omit [DecidableEq I] [DecidableEq X] in
/-- For finite I, an explicit positive weight is exactly the missing nonvacuity
condition. This theorem does not assert that any such weight exists. -/
theorem coordinateFilter_neBot_iff_positive_weight [Finite I] :
    (coordinateFilter D).NeBot ↔ ∃ ξ : X, ∀ i, 0 < D.h i ξ := by
  constructor
  · intro h
    obtain ⟨ξ, hξ⟩ := (coordinateFilter_neBot_iff D).mp h (fun _ => 1)
    exact ⟨ξ, fun i => lt_of_lt_of_le (by decide : (0 : ℤ) < 1) (hξ i)⟩
  · rintro ⟨ξ, hξ⟩
    exact coordinateFilter_neBot_of_positive_weight D ξ hξ

/-- Word-level statement directly on the accepted Verma polarization. -/
theorem polarization_word_order (ε : RatFunc ℚ) (hε : ε ^ 2 = 1)
    (w : List I) (y : PreF Coefficients.Ring I) (N : ℤ) (Λ : X)
    (hΛ : ∀ i ∈ (comparisonError D w y).vars,
      max 0 (N - QAdic.coefficientFloor (specialize ε hε).toRingHom (comparisonError D w y)) ≤
        D.h i Λ) :
    (N : WithTop ℤ) ≤ QAdic.order (specialize ε hε
      (wordSign D Λ w * polarization D Λ
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))
        (D.toSerreF Coefficients.q pi y) -
        D.form Coefficients.q pi (monomial Coefficients.Ring w) y)) := by
  have h := normalizedPolarization_order D ε hε (monomial Coefficients.Ring w) y N Λ
    (by simpa only [comparisonThreshold, freeComparisonError_word] using hΛ)
  simpa only [normalizedPolarization, diagTwist_monomial, map_smul,
    LinearMap.smul_apply, smul_eq_mul, wordSign] using h

/-- The normalized accepted word polarization converges after either pi specialization. -/
theorem polarization_word_tendsto (ε : RatFunc ℚ) (hε : ε ^ 2 = 1)
    (w : List I) (y : PreF Coefficients.Ring I) :
    Tendsto (fun Λ => specialize ε hε (wordSign D Λ w * polarization D Λ
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))
      (D.toSerreF Coefficients.q pi y))) (coordinateFilter D)
      (𝓝 (specialize ε hε (D.form Coefficients.q pi (monomial Coefficients.Ring w) y))) := by
  simpa only [normalizedPolarization, diagTwist_monomial, map_smul,
    LinearMap.smul_apply, smul_eq_mul, wordSign] using
    normalizedPolarization_tendsto D ε hε (monomial Coefficients.Ring w) y

end OddMath.CoveringQuantum.UDot.GenericVerma
