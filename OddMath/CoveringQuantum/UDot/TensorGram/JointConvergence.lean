/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.UDot.TensorGram.JointLimit

/-!
# Fixed-difference joint convergence of normalized tensor Grams

The original weight-pair filter and actual normalized Gram on its eventually
dominant domain give convergence to the positive modified form, even for a
varying native coproduct. A strictly positive coroot weight is used only for
nonvacuity and cofinal sequences, not the algebraic bounds or conditional limit.
No printed Delta3/Delta4 identification, new integrable-quotient descent,
separation, faithfulness or full modified-form nondegeneracy is asserted.
-/

noncomputable section
open scoped Topology
open Filter
namespace OddMath.CoveringQuantum.UDot.NormalizedJointLimit
open Coefficients PreF GenericVerma MixedGram PolarizationTransport NormalizedMixedComparison
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent)

/-- The actual Gram on the eventual dominant domain, extended by zero elsewhere. -/
def gramExtension (ζ : X) (x y : modified D Coefficients.q pi) (s : Bool)
    (p : WeightPair ζ) : Coefficients.Ring := by
  classical
  exact if h : (∀ i, 0 ≤ D.h i p.val.1) ∧ (∀ i, 0 ≤ D.h i p.val.2) then
    modifiedGram D hD p.val.1 p.val.2 h.1 h.2 s x y
  else 0

/-- Agreement is pointwise on all actual dominant pairs, not merely a choice
of a convenient residual-polynomial extension. -/
theorem gramExtension_eq (ζ : X) (x y : modified D Coefficients.q pi) (s : Bool)
    (p : WeightPair ζ) (hΛ : ∀ i, 0 ≤ D.h i p.val.1) (hΜ : ∀ i, 0 ≤ D.h i p.val.2) :
    gramExtension D hD ζ x y s p = modifiedGram D hD p.val.1 p.val.2 hΛ hΜ s x y := by
  simp [gramExtension, hΛ, hΜ]

omit [DecidableEq I] [DecidableEq X] [Finite I] in
/-- Both coordinate families eventually exceed any one finite threshold. -/
theorem jointFilter_eventually_lower (ζ : X) (B : ℤ) :
    ∀ᶠ p in jointFilter D ζ,
      (∀ i, B ≤ D.h i p.val.1) ∧ (∀ i, B ≤ D.h i p.val.2) := by
  apply Filter.eventually_comap.mpr
  filter_upwards [Filter.eventually_ge_atTop (fun _ : Bool × I ↦ B)] with b hb
  intro p hp
  constructor
  · intro i
    have h := hb (true, i)
    simpa only [← congrFun hp (true, i), jointCoordinates, ite_true] using h
  · intro i
    have h := hb (false, i)
    simpa only [← congrFun hp (false, i), jointCoordinates, Bool.false_eq_true, ite_false] using h

/-- Actual eventual identification on the original fixed-difference domain. -/
theorem gramExtension_eventually_actual (ζ : X) (x y : modified D Coefficients.q pi) :
    ∀ᶠ p in jointFilter D ζ,
      ∃ (hΛ : ∀ i, 0 ≤ D.h i p.val.1) (hΜ : ∀ i, 0 ≤ D.h i p.val.2), ∀ s,
        gramExtension D hD ζ x y s p = modifiedGram D hD p.val.1 p.val.2 hΛ hΜ s x y := by
  filter_upwards [jointFilter_eventually_dominant D ζ] with p hp
  exact ⟨hp.1, hp.2, fun s ↦ gramExtension_eq D hD ζ x y s p hp.1 hp.2⟩

/-- A single eventual event controls all four (pi sign, native coproduct) cases. -/
theorem gramExtension_eventually_order_both (ζ : X) (x y : modified D Coefficients.q pi)
    (hx : x * weightOne D ζ = x) (hy : y * weightOne D ζ = y) (N : ℤ) :
    ∀ᶠ p in jointFilter D ζ, ∀ s : Bool,
      (N : WithTop ℤ) ≤ QAdic.order (specialize 1 (one_pow 2)
        (gramExtension D hD ζ x y s p - GenericTensor.positiveModifiedForm D hD x y)) ∧
      (N : WithTop ℤ) ≤ QAdic.order (specialize (-1) (by norm_num)
        (gramExtension D hD ζ x y s p - GenericTensor.positiveModifiedForm D hD x y)) := by
  filter_upwards [jointFilter_eventually_dominant D ζ,
    jointFilter_eventually_lower D ζ (bothThreshold (residualPolynomial D hD ζ x y hx hy) N)]
      with p hp hb
  intro s
  rw [gramExtension_eq D hD ζ x y s p hp.1 hp.2]
  exact (modifiedGram_order_both D hD ζ x y hx hy N).2
    p.val.1 p.val.2 hp.1 hp.2 p.property hb.2 s

/-- Genuine q-adic limit at q = 0 for every pi^2 = 1 specialization.
The coproduct may even vary with the weight pair: the estimate is uniform. -/
theorem gramExtension_tendsto (ζ : X) (x y : modified D Coefficients.q pi)
    (hx : x * weightOne D ζ = x) (hy : y * weightOne D ζ = y)
    (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) (s : WeightPair ζ → Bool) :
    Tendsto (fun p ↦ specialize ε hε (gramExtension D hD ζ x y (s p) p))
      (jointFilter D ζ) (𝓝 (specialize ε hε (GenericTensor.positiveModifiedForm D hD x y))) := by
  have hh : Tendsto (fun p ↦ specialize ε hε
      (gramExtension D hD ζ x y (s p) p - GenericTensor.positiveModifiedForm D hD x y))
      (jointFilter D ζ) (𝓝 0) := by
    apply QAdic.tendsto_zero_of_order
    intro N
    filter_upwards [gramExtension_eventually_order_both D hD ζ x y hx hy N] with p hp
    rcases sq_eq_one_iff.mp hε with rfl | rfl
    · exact (hp (s p)).1
    · exact (hp (s p)).2
  have hs := hh.add (tendsto_const_nhds
    (x := specialize ε hε (GenericTensor.positiveModifiedForm D hD x y)))
  simpa only [map_sub, sub_add_cancel, zero_add] using hs

/-- Nonvacuous joint convergence requires an explicit strictly positive
coroot weight. This assumption is absent from every algebraic estimate. -/
theorem nonvacuous_joint_limit (ζ ξ : X) (hξ : ∀ i, 0 < D.h i ξ)
    (x y : modified D Coefficients.q pi)
    (hx : x * weightOne D ζ = x) (hy : y * weightOne D ζ = y) :
    (jointFilter D ζ).NeBot ∧ ∀ (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) (s : WeightPair ζ → Bool),
      Tendsto (fun p ↦ specialize ε hε (gramExtension D hD ζ x y (s p) p))
        (jointFilter D ζ) (𝓝 (specialize ε hε (GenericTensor.positiveModifiedForm D hD x y))) :=
  ⟨jointFilter_neBot_of_positive D ζ ξ hξ, gramExtension_tendsto D hD ζ x y hx hy⟩

/-- The concrete natural-number fixed-difference sequence (ζ+nξ,nξ). -/
def cofinalPair (ζ ξ : X) (n : ℕ) : WeightPair ζ :=
  ⟨(ζ + n • ξ, n • ξ), by simp⟩

omit [DecidableEq I] [DecidableEq X] in
/-- Cofinality is proved from the positive coordinates, not assumed. -/
theorem cofinalPair_tendsto (ζ ξ : X) (hξ : ∀ i, 0 < D.h i ξ) :
    Tendsto (cofinalPair ζ ξ) atTop (jointFilter D ζ) := by
  classical
  let _ := Fintype.ofFinite I
  apply tendsto_comap_iff.mpr
  apply tendsto_atTop.mpr
  intro b
  let m : ℤ := ∑ i : I, (|b (true, i) - D.h i ζ| + |b (false, i)|)
  filter_upwards [eventually_ge_atTop m.toNat] with n hn
  have hn' : m ≤ (n : ℤ) := by omega
  rintro ⟨s, i⟩
  have hi : |b (true, i) - D.h i ζ| + |b (false, i)| ≤ m :=
    Finset.single_le_sum (f := fun j ↦ |b (true, j) - D.h j ζ| + |b (false, j)|)
      (fun j _ ↦ add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)
  have hdi := hξ i
  have ht := le_abs_self (b (true, i) - D.h i ζ)
  have hf := le_abs_self (b (false, i))
  have ha := abs_nonneg (b (true, i) - D.h i ζ)
  have hb := abs_nonneg (b (false, i))
  have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  cases s
  · change b (false, i) ≤ D.h i (n • ξ)
    have he : D.h i (n • ξ) = n * D.h i ξ := by simp [RootDatum.h]
    rw [he]
    nlinarith
  · change b (true, i) ≤ D.h i (ζ + n • ξ)
    have he : D.h i (ζ + n • ξ) = D.h i ζ + n * D.h i ξ := by simp [RootDatum.h]
    rw [he]
    nlinarith

omit [DecidableEq I] [DecidableEq X] in
/-- The actual sequence enters the domain of the dominant tensor modules. -/
theorem cofinalPair_eventually_dominant (ζ ξ : X) (hξ : ∀ i, 0 < D.h i ξ) :
    ∀ᶠ n : ℕ in atTop, (∀ i, 0 ≤ D.h i (ζ + n • ξ)) ∧ (∀ i, 0 ≤ D.h i (n • ξ)) :=
  (cofinalPair_tendsto D ζ ξ hξ).eventually (jointFilter_eventually_dominant D ζ)

/-- A nonempty sequential consumer for both native coproducts and both signs. -/
theorem cofinalPair_gram_tendsto (ζ ξ : X) (hξ : ∀ i, 0 < D.h i ξ)
    (x y : modified D Coefficients.q pi)
    (hx : x * weightOne D ζ = x) (hy : y * weightOne D ζ = y)
    (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) (s : Bool) :
    Tendsto (fun n : ℕ ↦ specialize ε hε (gramExtension D hD ζ x y s (cofinalPair ζ ξ n)))
      atTop (𝓝 (specialize ε hε (GenericTensor.positiveModifiedForm D hD x y))) :=
  (gramExtension_tendsto D hD ζ x y hx hy ε hε (fun _ ↦ s)).comp
    (cofinalPair_tendsto D ζ ξ hξ)

end OddMath.CoveringQuantum.UDot.NormalizedJointLimit
