/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.UDot.TensorGram.Words

/-!
# Finite fixed-column reduction of rho-adjoint forms

Finite positive-pair coordinates compare the actual normalized tensor Gram
with the positive modified form. The positive-word polynomial identity is
supplied in the subsequent comparison modules.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.NormalizedMixedComparison
open Coefficients PreF GenericVerma PolarizationTransport
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

abbrev WordPair (I : Type*) := List I × List I

def word (positive : Bool) (w : List I) (μ : X) : modified D Coefficients.q pi :=
  ⟨halfWord D Coefficients.q pi positive w μ,
    block_le_modified D Coefficients.q pi _ _ (halfWord_mem_block D Coefficients.q pi positive w μ)⟩

def weightOne (μ : X) : modified D Coefficients.q pi :=
  ⟨one D Coefficients.q pi μ, one_mem_modified D Coefficients.q pi μ⟩

theorem word_positive (w : List I) (μ : X) :
    word D true w μ = positiveHalf D Coefficients.q pi μ
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) := by
  apply Subtype.ext
  exact (halfMap_monomial D Coefficients.q pi true w μ).symm

theorem word_mul_one (b : Bool) (w : List I) (μ ζ : X) :
    word D b w μ * weightOne D ζ = if μ = ζ then word D b w μ else 0 := by
  apply Subtype.ext
  simpa only [word, weightOne, NonUnitalSubalgebra.coe_mul, Subtype.coe_mk,
    apply_ite, NonUnitalSubalgebra.coe_zero] using
    mul_one_of_mem_block D Coefficients.q pi (halfWord_mem_block D Coefficients.q pi b w μ) ζ

/-- Evaluation of finite positive-pair coordinates in a bilinear form. -/
def evaluate (ζ : X) (c : WordPair I →₀ Coefficients.Ring)
    (B : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi)) :
    Coefficients.Ring :=
  Finsupp.linearCombination Coefficients.Ring
    (fun p : WordPair I ↦ B (word D true p.1 ζ) (word D true p.2 ζ)) c

@[simp] theorem evaluate_zero (ζ : X)
    (B : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi)) :
    evaluate D ζ 0 B = 0 := map_zero _

@[simp] theorem evaluate_add (ζ : X) (c d : WordPair I →₀ Coefficients.Ring)
    (B : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi)) :
    evaluate D ζ (c + d) B = evaluate D ζ c B + evaluate D ζ d B := map_add _ _ _

@[simp] theorem evaluate_smul (ζ : X) (a : Coefficients.Ring)
    (c : WordPair I →₀ Coefficients.Ring)
    (B : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi)) :
    evaluate D ζ (a • c) B = a • evaluate D ζ c B := map_smul _ _ _

@[simp] theorem evaluate_single (ζ : X) (p : WordPair I) (a : Coefficients.Ring)
    (B : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi)) :
    evaluate D ζ (Finsupp.single p a) B =
      a * B (word D true p.1 ζ) (word D true p.2 ζ) := by
  simp [evaluate, Finsupp.linearCombination_single, smul_eq_mul]

/-- Every actual triangular term has universal positive-pair coordinates after
cutting its right column. The coefficients have no highest-weight parameter. -/
theorem triangular_coordinates (ζ : X) (a b : List I) (μ ν : X) :
    ∃ c : WordPair I →₀ Coefficients.Ring,
      ∀ B : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi),
      (∀ u x y, B (u * x) y = B x (rhoModified D Coefficients.q pi pi_sq u * y)) →
      B (weightOne D ζ) ((word D false a μ * word D true b ν) * weightOne D ζ) =
        evaluate D ζ c B := by
  classical
  obtain ⟨r, hr⟩ := rho_halfWord_unit D Coefficients.q pi pi_sq false a μ
  have hh : rhoModified D Coefficients.q pi pi_sq (word D false a μ) =
      (r : Coefficients.Ring) • word D true a.reverse
        (μ + halfWeight D false (wordWeight a)) := Subtype.ext hr
  by_cases hν : ν = ζ
  · subst ν
    by_cases hμ : μ + halfWeight D false (wordWeight a) = ζ
    · refine ⟨Finsupp.single (a.reverse, b) (r : Coefficients.Ring), fun B hB ↦ ?_⟩
      rw [mul_assoc, word_mul_one, ite_eq_left rfl]
      have he := hB (rhoModified D Coefficients.q pi pi_sq (word D false a μ))
        (weightOne D ζ) (word D true b ζ)
      rw [rhoModified_rhoModified, hh, smul_mul_assoc, hμ, word_mul_one, ite_eq_left rfl] at he
      rw [← he, map_smul, LinearMap.smul_apply, evaluate_single, smul_eq_mul]
    · refine ⟨0, fun B hB ↦ ?_⟩
      rw [mul_assoc, word_mul_one, ite_eq_left rfl]
      have he := hB (rhoModified D Coefficients.q pi pi_sq (word D false a μ))
        (weightOne D ζ) (word D true b ζ)
      rw [rhoModified_rhoModified, hh, smul_mul_assoc, word_mul_one, ite_eq_right hμ,
        smul_zero, map_zero, LinearMap.zero_apply] at he
      rw [← he, evaluate_zero]
  · refine ⟨0, fun B _ ↦ ?_⟩
    rw [mul_assoc, word_mul_one, ite_eq_right hν, mul_zero, map_zero, evaluate_zero]

/-- Finite coordinates valid simultaneously for every rho-adjoint bilinear form.
No leading coefficient, limit, basis or nondegeneracy hypothesis is supplied. -/
theorem column_coordinates (ζ : X) (z : modified D Coefficients.q pi) :
    ∃ c : WordPair I →₀ Coefficients.Ring,
      ∀ B : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi),
      (∀ u x y, B (u * x) y = B x (rhoModified D Coefficients.q pi pi_sq u * y)) →
      B (weightOne D ζ) (z * weightOne D ζ) = evaluate D ζ c B := by
  have hz : z.val ∈ triangularSpan D Coefficients.q pi := by
    rw [triangularSpan_eq_modified]
    exact z.property
  have aux : ∀ t ∈ triangularSpan D Coefficients.q pi,
      ∀ ht : t ∈ modified D Coefficients.q pi,
      ∃ c : WordPair I →₀ Coefficients.Ring,
        ∀ B : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi),
        (∀ u x y, B (u * x) y = B x (rhoModified D Coefficients.q pi pi_sq u * y)) →
        B (weightOne D ζ) (⟨t, ht⟩ * weightOne D ζ) = evaluate D ζ c B := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨a, b, μ, ν, rfl⟩ := ht
      intro ht
      exact triangular_coordinates D ζ a b μ ν
    | zero =>
      intro ht
      refine ⟨0, fun B _ ↦ ?_⟩
      change B (weightOne D ζ) (0 * weightOne D ζ) = _
      rw [zero_mul, map_zero, evaluate_zero]
    | add t v ht hv iht ihv =>
      intro htv
      have et : t ∈ modified D Coefficients.q pi := by
        change t ∈ (modified D Coefficients.q pi).toSubmodule
        rw [← triangularSpan_eq_modified]; exact ht
      have ev : v ∈ modified D Coefficients.q pi := by
        change v ∈ (modified D Coefficients.q pi).toSubmodule
        rw [← triangularSpan_eq_modified]; exact hv
      obtain ⟨c, hc⟩ := iht et
      obtain ⟨d, hd⟩ := ihv ev
      refine ⟨c + d, fun B hB ↦ ?_⟩
      change B (weightOne D ζ) ((⟨t, et⟩ + ⟨v, ev⟩) * weightOne D ζ) = _
      rw [add_mul, map_add, hc B hB, hd B hB, evaluate_add]
    | smul a t ht iht =>
      intro hat
      have et : t ∈ modified D Coefficients.q pi := by
        change t ∈ (modified D Coefficients.q pi).toSubmodule
        rw [← triangularSpan_eq_modified]; exact ht
      obtain ⟨c, hc⟩ := iht et
      refine ⟨a • c, fun B hB ↦ ?_⟩
      change B (weightOne D ζ) ((a • (⟨t, et⟩ : modified D Coefficients.q pi)) * weightOne D ζ) = _
      rw [smul_mul_assoc, map_smul, hc B hB, evaluate_smul]
  exact aux z.val hz z.property

/-- The same finite coordinates work for both actual forms, for every growing
weight pair. This is an exact reduction, not a claimed residual-order bound. -/
theorem actual_comparison_reduction [Finite I] (hD : D.toSuperCartanDatum.BarConsistent)
    (ζ : X) (x y : modified D Coefficients.q pi)
    (hx : x * weightOne D ζ = x) (hy : y * weightOne D ζ = y) :
    ∃ c : WordPair I →₀ Coefficients.Ring, ∀ (Λ Μ : X)
      (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ) (s : Bool),
      modifiedGram D hD Λ Μ hΛ hΜ s x y - GenericTensor.positiveModifiedForm D hD x y =
        evaluate D ζ c (modifiedGram D hD Λ Μ hΛ hΜ s) -
          evaluate D ζ c (GenericTensor.positiveModifiedForm D hD) := by
  obtain ⟨c, hc⟩ := column_coordinates D ζ (rhoModified D Coefficients.q pi pi_sq x * y)
  refine ⟨c, fun Λ Μ hΛ hΜ s ↦ ?_⟩
  have he (B : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi))
      (hB : ∀ u v w, B (u * v) w = B v (rhoModified D Coefficients.q pi pi_sq u * w)) :
      B x y = evaluate D ζ c B := by
    rw [← hx, hB]
    simpa only [mul_assoc, hy] using hc B hB
  rw [he _ (fun u v w ↦ gram_adjoint D hD Λ Μ hΛ hΜ s u.val v.val w.val),
    he _ (GenericTensor.positiveModifiedForm_adjoint D hD)]

@[simp] theorem algebraWord_mul_one [Finite I] (ζ : X) (w : List (Bool × I)) :
    MixedGram.algebraWord D ζ w * weightOne D ζ = MixedGram.algebraWord D ζ w := by
  induction w with
  | nil =>
    apply Subtype.ext
    exact one_mul_one_self D Coefficients.q pi ζ
  | cons g w ih =>
    change (_ * MixedGram.algebraWord D ζ w) * weightOne D ζ = _
    rw [mul_assoc, ih]
    rfl

/-- The finite constant is evaluated in the existing positiveModifiedForm,
not in a newly specified form or an assumed leading functional. -/
theorem evaluate_positive [Finite I] (hD : D.toSuperCartanDatum.BarConsistent)
    (ζ : X) (c : WordPair I →₀ Coefficients.Ring) :
    evaluate D ζ c (GenericTensor.positiveModifiedForm D hD) =
      c.sum (fun p a ↦ a * D.form Coefficients.q pi
        (monomial Coefficients.Ring p.1) (monomial Coefficients.Ring p.2)) := by
  simp only [evaluate, word_positive, GenericTensor.positiveModifiedForm_positiveHalf,
    SuperCartanDatum.serreForm_toSerreF, Finsupp.linearCombination_apply, smul_eq_mul]

/-- Exact arbitrary mixed-column residual identity with fixed finite coefficients.
The positive-word residuals on the right are actual values, not hypotheses. -/
theorem actual_residual_sum [Finite I] (hD : D.toSuperCartanDatum.BarConsistent)
    (ζ : X) (x y : modified D Coefficients.q pi)
    (hx : x * weightOne D ζ = x) (hy : y * weightOne D ζ = y) :
    ∃ c : WordPair I →₀ Coefficients.Ring, ∀ (Λ Μ : X)
      (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ) (s : Bool),
      modifiedGram D hD Λ Μ hΛ hΜ s x y - GenericTensor.positiveModifiedForm D hD x y =
        c.sum (fun p a ↦ a * (modifiedGram D hD Λ Μ hΛ hΜ s
          (word D true p.1 ζ) (word D true p.2 ζ) -
            D.form Coefficients.q pi (monomial Coefficients.Ring p.1)
              (monomial Coefficients.Ring p.2))) := by
  obtain ⟨c, hc⟩ := actual_comparison_reduction D hD ζ x y hx hy
  refine ⟨c, fun Λ Μ hΛ hΜ s ↦ ?_⟩
  rw [hc Λ Μ hΛ hΜ s, evaluate_positive]
  simp only [evaluate, Finsupp.linearCombination_apply, smul_eq_mul,
    Finsupp.sum, mul_sub, Finset.sum_sub_distrib]

end OddMath.CoveringQuantum.UDot.NormalizedMixedComparison
