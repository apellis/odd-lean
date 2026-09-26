import OddMath.Frontier.EKGeneralQIdeal

/-!
# [EK] §5.2, p. 39: relations propagate to all higher degrees

Source: A. P. Ellis, M. Khovanov, *The Hopf algebra of odd symmetric functions*,
arXiv:1107.5610v2, §5.2, p. 39: "Since a nontrivial relation in degree `k` causes nontrivial
relations in all higher degrees, we only list the new minimal polynomials in each degree."

Here `Λ′ = L k` is the free algebra on `h₁, h₂, …` over an arbitrary commutative ring `k`, with
the form (2.1) at an arbitrary `q : k` and its radical `I` (`EKGeneralQ.radical`), and `I_n`
is the degree-`n` part of `I`. A nontrivial relation in degree `n` is a nonzero element of
`I_n`.

* `radicalDeg_mul_h_one`: if `x ∈ I_n` then `x h₁ ∈ I_{n+1}` and `h₁ x ∈ I_{n+1}`;
* `mul_h_one_ne_zero`, `h_one_mul_ne_zero`: multiplication by `h₁` on either side is injective
  on `Λ′` (for every `k`);
* `ek_p39_relations_propagate`: if `I_n ≠ 0` then `I_m ≠ 0` for every `m ≥ n`.
-/

noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKMore
open EKGeneralQ
open EKFreeCoproduct (W degree degree_mul)

variable {k : Type*} [CommRing k]
attribute [local instance] Classical.propDecidable

/-- `x ∈ I_n`: `x` lies in the radical and is homogeneous of degree `n`. -/
def InRadicalDeg (q : k) (n : ℕ) (x : L k) : Prop :=
  x ∈ radical q ∧ degreeProj k n x = x

theorem degree_of_zero : degree (FreeMonoid.of (0 : ℕ)) = 1 := rfl

theorem degreeProj_mul_h_one (n : ℕ) (x : L k) :
    degreeProj k (n + 1) (x * h k 1) = degreeProj k n x * h k 1 := by
  have e : (degreeProj k (n + 1) ∘ₗ LinearMap.mulRight k (h k 1)) =
      (LinearMap.mulRight k (h k 1) ∘ₗ degreeProj k n) := by
    apply (wordBasis k).ext
    intro w
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, degreeProj_basis]
    rw [show h k 1 = wordBasis k (FreeMonoid.of (0 : ℕ)) from (wordBasis_of k 0).symm,
      ← wordBasis_mul, degreeProj_basis, degree_mul, degree_of_zero]
    by_cases hw : degree w = n
    · simp [hw]
    · simp [hw]
  exact congrArg (fun f : L k →ₗ[k] L k => f x) e

theorem degreeProj_h_one_mul (n : ℕ) (x : L k) :
    degreeProj k (n + 1) (h k 1 * x) = h k 1 * degreeProj k n x := by
  have e : (degreeProj k (n + 1) ∘ₗ LinearMap.mulLeft k (h k 1)) =
      (LinearMap.mulLeft k (h k 1) ∘ₗ degreeProj k n) := by
    apply (wordBasis k).ext
    intro w
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, degreeProj_basis]
    rw [show h k 1 = wordBasis k (FreeMonoid.of (0 : ℕ)) from (wordBasis_of k 0).symm,
      ← wordBasis_mul, degreeProj_basis, degree_mul, degree_of_zero]
    by_cases hw : degree w = n
    · simp [hw, add_comm]
    · have : ¬ 1 + degree w = n + 1 := by omega
      simp [hw, this]
  exact congrArg (fun f : L k →ₗ[k] L k => f x) e

/-- Coordinates of `x h₁`: the coefficient of the word `w·h₁` is the coefficient of `w`. -/
theorem repr_mul_h_one (x : L k) (w : W) :
    (wordBasis k).repr (x * h k 1) (w * FreeMonoid.of (0 : ℕ)) = (wordBasis k).repr x w := by
  have e : (Finsupp.lapply (w * FreeMonoid.of (0 : ℕ)) ∘ₗ (wordBasis k).repr.toLinearMap ∘ₗ
      LinearMap.mulRight k (h k 1)) = (Finsupp.lapply w ∘ₗ (wordBasis k).repr.toLinearMap) := by
    apply (wordBasis k).ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearEquiv.coe_coe,
      Finsupp.lapply_apply]
    rw [show h k 1 = wordBasis k (FreeMonoid.of (0 : ℕ)) from (wordBasis_of k 0).symm,
      ← wordBasis_mul, Basis.repr_self, Basis.repr_self, Finsupp.single_apply,
      Finsupp.single_apply]
    by_cases hv : v = w
    · simp [hv]
    · have : ¬ v * FreeMonoid.of (0 : ℕ) = w * FreeMonoid.of (0 : ℕ) := fun h => hv (mul_right_cancel h)
      simp [hv, this]
  exact congrArg (fun f : L k →ₗ[k] k => f x) e

theorem repr_h_one_mul (x : L k) (w : W) :
    (wordBasis k).repr (h k 1 * x) (FreeMonoid.of (0 : ℕ) * w) = (wordBasis k).repr x w := by
  have e : (Finsupp.lapply (FreeMonoid.of (0 : ℕ) * w) ∘ₗ (wordBasis k).repr.toLinearMap ∘ₗ
      LinearMap.mulLeft k (h k 1)) = (Finsupp.lapply w ∘ₗ (wordBasis k).repr.toLinearMap) := by
    apply (wordBasis k).ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearEquiv.coe_coe,
      Finsupp.lapply_apply]
    rw [show h k 1 = wordBasis k (FreeMonoid.of (0 : ℕ)) from (wordBasis_of k 0).symm,
      ← wordBasis_mul, Basis.repr_self, Basis.repr_self, Finsupp.single_apply,
      Finsupp.single_apply]
    by_cases hv : v = w
    · simp [hv]
    · have : ¬ FreeMonoid.of (0 : ℕ) * v = FreeMonoid.of (0 : ℕ) * w := fun h => hv (mul_left_cancel h)
      simp [hv, this]
  exact congrArg (fun f : L k →ₗ[k] k => f x) e

theorem mul_h_one_ne_zero {x : L k} (hx : x ≠ 0) : x * h k 1 ≠ 0 := by
  intro h0
  apply hx
  apply (wordBasis k).repr.injective
  ext w
  rw [← repr_mul_h_one, h0]
  simp

theorem h_one_mul_ne_zero {x : L k} (hx : x ≠ 0) : h k 1 * x ≠ 0 := by
  intro h0
  apply hx
  apply (wordBasis k).repr.injective
  ext w
  rw [← repr_h_one_mul, h0]
  simp

/-- If `x ∈ I_n` then `x h₁, h₁ x ∈ I_{n+1}`. -/
theorem radicalDeg_mul_h_one (q : k) {n : ℕ} {x : L k} (hx : InRadicalDeg q n x) :
    InRadicalDeg q (n + 1) (x * h k 1) ∧ InRadicalDeg q (n + 1) (h k 1 * x) :=
  ⟨⟨radical_mul_right q hx.1 _, by rw [degreeProj_mul_h_one, hx.2]⟩,
    ⟨radical_mul_left q _ hx.1, by rw [degreeProj_h_one_mul, hx.2]⟩⟩

/-- [EK] p. 39: a nontrivial relation in degree `n` causes nontrivial relations in all higher
degrees (for the form (2.1) at any `q` over any commutative ring). -/
theorem ek_p39_relations_propagate (q : k) {n : ℕ} (hn : ∃ x, x ≠ 0 ∧ InRadicalDeg q n x) :
    ∀ m, n ≤ m → ∃ x, x ≠ 0 ∧ InRadicalDeg q m x := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact hn
  | succ m _ ih =>
    obtain ⟨x, hx0, hx⟩ := ih
    exact ⟨x * h k 1, mul_h_one_ne_zero hx0, (radicalDeg_mul_h_one q hx).1⟩

end OddMath.Frontier.EKMore
