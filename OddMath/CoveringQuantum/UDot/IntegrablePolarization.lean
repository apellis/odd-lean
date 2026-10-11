import OddMath.CoveringQuantum.UDot.VermaComparison
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Descent to the source-generated highest-weight quotient

The integrability vectors are proved singular under the original Verma lowering
operators. Their original-action generated submodule is then proved to lie in both
radicals of the actual polarization. We descend the action and form to that exact
quotient, retain arbitrary-representative computation and E/F adjointness, and
transport the normalized half-form polynomial comparison.

The source quotient is CHWII Remark 2.5; the adjoint convention is Clark IV
Proposition 5.8 / §5.2 (tau1-prime, v = q^-1). Dominance is explicit and local.
This does not prove local nilpotence on all quotient vectors, simplicity,
nondegeneracy, or the tensor J-polarization / mixed modified-form limit.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot
open PreF Coefficients

private theorem lDeriv_θ_pow {k I : Type*} [CommRing k] [DecidableEq I]
    (χ : Bichar k I) (i j : I) (n : ℕ) :
    lDeriv χ j (θ k i ^ n) =
      if j = i then (∑ s ∈ Finset.range n, χ i i ^ s) • θ k i ^ (n - 1) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', lDeriv_mul, ih, lDeriv_θ, twist_θ]
    split_ifs with h
    · subst j
      rw [one_mul, mul_smul_comm, smul_mul_assoc, smul_smul, ← pow_succ']
      cases n with
      | zero => simp
      | succ n =>
        rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
        conv_lhs => arg 1; rw [← one_smul k (θ k i ^ (n + 1))]
        rw [← add_smul, Finset.sum_range_succ' _ (n + 1), Finset.sum_mul, pow_zero,
          add_comm (1 : k)]
        congr 2
        exact Finset.sum_congr rfl fun s _ ↦ (pow_succ _ _).symm
    · simp

/-- The actual integrability generator is singular, before imposing any quotient.
No parity restriction on the nonnegative highest-weight coordinate is needed. -/
theorem lowerFree_integrability {k I : Type*} [CommRing k] [DecidableEq I]
    (C : SuperCartanDatum I) (q : kˣ) (π : k) (i j : I) (n : ℕ) (m : ℤ)
    (hm : j = i → m = n) :
    lowerFree C q π j m (θ k i ^ (n + 1)) = 0 := by
  simp only [lowerFree, lowerNumerator, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, rDeriv_θ_pow, lDeriv_θ_pow]
  by_cases h : j = i
  · subst j
    rw [hm rfl]
    simp only [ite_true, Nat.add_sub_cancel, map_smul, map_pow, parityTwist,
      weightTwist, diagTwist_θ, smul_pow, smul_smul, Int.natAbs_natCast]
    have hp : π ^ (C.parity i * C.parity i).val = C.pii π i := by
      have hh : ∀ p : ZMod 2, p * p = p := by decide
      simp only [hh, SuperCartanDatum.pii]
    have hq : ((q ^ C.dot i i : kˣ) : k) = ((C.qi q i : kˣ) : k) ^ 2 := by
      rw [C.dot_self, mul_comm (2 : ℤ), zpow_mul]
      simp [SuperCartanDatum.qi]
    rw [hp, hq]
    have hs : ((C.qi q i ^ (n : ℤ) : kˣ) : k) =
        ((C.qi q i ^ (-(n : ℤ)) : kˣ) : k) * (((C.qi q i : kˣ) : k) ^ 2) ^ n := by
      rw [← pow_mul, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← Units.val_mul,
        ← zpow_add]
      congr 2
      push_cast
      ring
    rw [hs]
    module
  · simp [h]

namespace GenericVerma
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent) (Λ : X)

/-- The original form is contravariant also for the unital envelope. -/
theorem polarization_representation_adjoint
    (u : CoveringUDot Coefficients.Ring D Coefficients.q pi)
    (x y : D.serreF Coefficients.q pi) :
    polarization D hD Λ (representation D hD Λ u x) y =
      polarization D hD Λ x
        (representation D hD Λ (rho D Coefficients.q pi pi_sq u).unop y) := by
  obtain ⟨u, rfl⟩ := mk_surjective D Coefficients.q pi u
  induction u using FreeAlgebra.induction generalizing x y with
  | grade0 c => simp
  | grade1 g =>
    have hg : mk D Coefficients.q pi (FreeAlgebra.ι Coefficients.Ring g) ∈
        modified D Coefficients.q pi := by
      cases g with
      | one μ => exact one_mem_modified D Coefficients.q pi μ
      | e i μ => exact E_mem_modified D Coefficients.q pi i μ
      | f i μ => exact F_mem_modified D Coefficients.q pi i μ
    exact polarization_adjoint D hD Λ ⟨_, hg⟩ x y
  | add a b ha hb => simp only [map_add, MulOpposite.unop_add, LinearMap.add_apply,
      LinearMap.add_apply, map_add, ha, hb]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_apply, MulOpposite.unop_mul]
    rw [ha, hb]

/-- Source integrability relation `Fᵢ^(⟨i,Λ⟩+1) · 1`, in the actual Serre half. -/
def integrabilityGenerator (i : I) : D.serreF Coefficients.q pi :=
  D.toSerreF Coefficients.q pi (θ Coefficients.Ring i ^ ((D.h i Λ).toNat + 1))

omit [DecidableEq X] in
/-- Local dominance at `i` suffices for this singular-vector calculation. -/
theorem lower_integrabilityGenerator (i j : I) (hi : 0 ≤ D.h i Λ) :
    lower D.toSuperCartanDatum hD j (D.h j Λ) (integrabilityGenerator D Λ i) = 0 := by
  rw [integrabilityGenerator, lower_mk,
    lowerFree_integrability D.toSuperCartanDatum Coefficients.q pi i j
      (D.h i Λ).toNat (D.h j Λ)
      (fun h ↦ h ▸ (Int.toNat_of_nonneg hi).symm), map_zero]

omit [DecidableEq X] [Finite I] in
private theorem constant_integrabilityGenerator (i : I) :
    constant D (integrabilityGenerator D Λ i) = 0 := by
  simp [integrabilityGenerator, pow_succ']

/-- The source relation lies in the right radical, proved from original lowering
operators and the normalized vacuum, not assumed as a quotient hypothesis. -/
theorem polarization_integrabilityGenerator_right (i : I) (hi : 0 ≤ D.h i Λ)
    (x : D.serreF Coefficients.q pi) :
    polarization D hD Λ x (integrabilityGenerator D Λ i) = 0 := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  induction x using induction_monomial with
  | word w =>
    cases w with
    | nil =>
      simpa only [monomial_nil, map_one, polarization_one_left] using
        constant_integrabilityGenerator D Λ i
    | cons j w =>
      rw [polarization_word_cons, lower_integrabilityGenerator D hD Λ i j hi,
        map_zero, smul_zero]
  | zero => simp
  | smul c x hx => simp only [map_smul, LinearMap.smul_apply, hx, smul_zero]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, add_zero]

theorem polarization_integrabilityGenerator_left (i : I) (hi : 0 ≤ D.h i Λ)
    (x : D.serreF Coefficients.q pi) :
    polarization D hD Λ (integrabilityGenerator D Λ i) x = 0 := by
  rw [polarization_comm, polarization_integrabilityGenerator_right D hD Λ i hi]

/-- The submodule generated by the source integrability relations under the
original unital-envelope representation. This definition does not use the form. -/
def integrabilityRelations : Submodule Coefficients.Ring (D.serreF Coefficients.q pi) :=
  Submodule.span Coefficients.Ring {x | ∃ (i : I)
    (u : CoveringUDot Coefficients.Ring D Coefficients.q pi),
    x = representation D hD Λ u (integrabilityGenerator D Λ i)}

theorem integrabilityGenerator_mem (i : I) :
    integrabilityGenerator D Λ i ∈ integrabilityRelations D hD Λ :=
  Submodule.subset_span ⟨i, 1, by simp⟩

/-- Minimality identifies the relations as the actual original-action submodule
generated by the integrability vectors, independently of any bilinear form. -/
theorem integrabilityRelations_le (S : Submodule Coefficients.Ring (D.serreF Coefficients.q pi))
    (hgen : ∀ i, integrabilityGenerator D Λ i ∈ S)
    (hstable : ∀ u, S ≤ S.comap (representation D hD Λ u)) :
    integrabilityRelations D hD Λ ≤ S := by
  rw [integrabilityRelations, Submodule.span_le]
  rintro x ⟨i, u, rfl⟩
  exact hstable u (hgen i)

/-- Stability is proved for the original action, before quotienting. -/
theorem integrabilityRelations_invariant
    (u : CoveringUDot Coefficients.Ring D Coefficients.q pi) :
    integrabilityRelations D hD Λ ≤
      (integrabilityRelations D hD Λ).comap (representation D hD Λ u) := by
  rw [integrabilityRelations, Submodule.span_le]
  rintro x ⟨i, v, rfl⟩
  exact Submodule.subset_span ⟨i, u * v, by simp⟩

/-- Exact dominance is local to the weight. No parity condition, independent-root
assumption, positivity witness or cofinal family is used for descent. -/
theorem integrabilityRelations_le_radical (hΛ : ∀ i, 0 ≤ D.h i Λ) :
    integrabilityRelations D hD Λ ≤ (polarization D hD Λ).ker := by
  rw [integrabilityRelations, Submodule.span_le]
  rintro x ⟨i, u, rfl⟩
  apply LinearMap.ext
  intro y
  exact (polarization_representation_adjoint D hD Λ u _ y).trans
    (polarization_integrabilityGenerator_left D hD Λ i (hΛ i) _)

theorem integrabilityRelations_le_right_radical (hΛ : ∀ i, 0 ≤ D.h i Λ) :
    integrabilityRelations D hD Λ ≤ (polarization D hD Λ).flip.ker := by
  intro x hx
  apply LinearMap.ext
  intro y
  change polarization D hD Λ y x = 0
  rw [polarization_comm]
  exact congrArg (fun f ↦ f y) (integrabilityRelations_le_radical D hD Λ hΛ hx)

/-- The actual highest-weight quotient by the source integrability relations.
Local nilpotence and nondegeneracy are not part of this definition. -/
abbrev IntegrableQuotient :=
  (D.serreF Coefficients.q pi) ⧸ integrabilityRelations D hD Λ

/-- Quotient projection from the original Serre-half Verma module. -/
def toIntegrable : D.serreF Coefficients.q pi →ₗ[Coefficients.Ring]
    IntegrableQuotient D hD Λ := (integrabilityRelations D hD Λ).mkQ

@[simp] theorem toIntegrable_generator (i : I) :
    toIntegrable D hD Λ (integrabilityGenerator D Λ i) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (integrabilityGenerator_mem D hD Λ i)

/-- Original action descended using the proved invariant submodule. -/
def integrableRepresentation :
    CoveringUDot Coefficients.Ring D Coefficients.q pi →ₐ[Coefficients.Ring]
      Module.End Coefficients.Ring (IntegrableQuotient D hD Λ) where
  toFun u := (integrabilityRelations D hD Λ).mapQ _ (representation D hD Λ u)
    (integrabilityRelations_invariant D hD Λ u)
  map_zero' := by ext ⟨x⟩; simp
  map_one' := by ext ⟨x⟩; simp
  map_add' u v := by ext ⟨x⟩; simp
  map_mul' u v := by ext ⟨x⟩; simp
  commutes' c := by ext ⟨x⟩; simp

@[simp] theorem integrableRepresentation_toIntegrable
    (u : CoveringUDot Coefficients.Ring D Coefficients.q pi)
    (x : D.serreF Coefficients.q pi) :
    integrableRepresentation D hD Λ u (toIntegrable D hD Λ x) =
      toIntegrable D hD Λ (representation D hD Λ u x) := rfl

/-- Descent of the actual Verma form, not a radical quotient or a new pairing. -/
def integrablePolarization (hΛ : ∀ i, 0 ≤ D.h i Λ) :
    LinearMap.BilinForm Coefficients.Ring (IntegrableQuotient D hD Λ) :=
  (polarization D hD Λ).liftQ₂ _ _ (integrabilityRelations_le_radical D hD Λ hΛ)
    (integrabilityRelations_le_right_radical D hD Λ hΛ)

@[simp] theorem integrablePolarization_toIntegrable (hΛ : ∀ i, 0 ≤ D.h i Λ)
    (x y : D.serreF Coefficients.q pi) :
    integrablePolarization D hD Λ hΛ (toIntegrable D hD Λ x) (toIntegrable D hD Λ y) =
      polarization D hD Λ x y := rfl

theorem integrablePolarization_symmetric (hΛ : ∀ i, 0 ≤ D.h i Λ)
    (x y : IntegrableQuotient D hD Λ) :
    integrablePolarization D hD Λ hΛ x y = integrablePolarization D hD Λ hΛ y x := by
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  exact polarization_comm D hD Λ x y

theorem integrablePolarization_adjoint (hΛ : ∀ i, 0 ≤ D.h i Λ)
    (u : CoveringUDot Coefficients.Ring D Coefficients.q pi)
    (x y : IntegrableQuotient D hD Λ) :
    integrablePolarization D hD Λ hΛ (integrableRepresentation D hD Λ u x) y =
      integrablePolarization D hD Λ hΛ x
        (integrableRepresentation D hD Λ (rho D Coefficients.q pi pi_sq u).unop y) := by
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  exact polarization_representation_adjoint D hD Λ u x y

@[simp] theorem integrablePolarization_highest (hΛ : ∀ i, 0 ≤ D.h i Λ) :
    integrablePolarization D hD Λ hΛ (toIntegrable D hD Λ 1) (toIntegrable D hD Λ 1) = 1 := by
  simp

/-- Explicit original Chevalley E/F adjointness on arbitrary quotient vectors. -/
theorem integrablePolarization_E (hΛ : ∀ i, 0 ≤ D.h i Λ) (i : I) (μ : X)
    (x y : IntegrableQuotient D hD Λ) :
    integrablePolarization D hD Λ hΛ
        (integrableRepresentation D hD Λ (E D Coefficients.q pi i μ) x) y =
      qp Coefficients.q (-(D.d i * (D.h i μ + 1))) •
        integrablePolarization D hD Λ hΛ x
          (integrableRepresentation D hD Λ (F D Coefficients.q pi i (μ + D.α i)) y) := by
  simpa only [rho_E, map_smul, LinearMap.smul_apply] using
    integrablePolarization_adjoint D hD Λ hΛ (E D Coefficients.q pi i μ) x y

theorem integrablePolarization_F (hΛ : ∀ i, 0 ≤ D.h i Λ) (i : I) (μ : X)
    (x y : IntegrableQuotient D hD Λ) :
    integrablePolarization D hD Λ hΛ
        (integrableRepresentation D hD Λ (F D Coefficients.q pi i μ) x) y =
      qp Coefficients.q (D.d i * (D.h i μ - 1)) •
        integrablePolarization D hD Λ hΛ x
          (integrableRepresentation D hD Λ (E D Coefficients.q pi i (μ - D.α i)) y) := by
  simpa only [rho_F, map_smul, LinearMap.smul_apply] using
    integrablePolarization_adjoint D hD Λ hΛ (F D Coefficients.q pi i μ) x y

/-- The original E action, on arbitrary representatives of the actual quotient. -/
@[simp] theorem integrableRepresentation_E_mk (i : I) (μ : X)
    (x : D.serreF Coefficients.q pi) :
    integrableRepresentation D hD Λ (E D Coefficients.q pi i μ) (toIntegrable D hD Λ x) =
      toIntegrable D hD Λ (lower D.toSuperCartanDatum hD i (D.h i Λ)
        (weightProject D hD Λ μ x)) := by
  rw [integrableRepresentation_toIntegrable, representation_E, Module.End.mul_apply]

/-- The original F action, on arbitrary representatives of the actual quotient. -/
@[simp] theorem integrableRepresentation_F_mk (i : I) (μ : X)
    (x : D.serreF Coefficients.q pi) :
    integrableRepresentation D hD Λ (F D Coefficients.q pi i μ) (toIntegrable D hD Λ x) =
      toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i) *
        weightProject D hD Λ μ x) := by
  rw [integrableRepresentation_toIntegrable, representation_F]

/-- The constructed quotient is nonzero: the highest vector still has norm one. -/
theorem toIntegrable_one_ne_zero (hΛ : ∀ i, 0 ≤ D.h i Λ) :
    toIntegrable D hD Λ 1 ≠ 0 := by
  intro h
  have hn := integrablePolarization_highest D hD Λ hΛ
  rw [h, map_zero] at hn
  exact zero_ne_one hn

/-- The accepted half-form comparison now holds on the actual source-generated
quotient. This remains normalized by the explicit rho/tau1-prime word sign. -/
theorem integrablePolarization_sub_half (hΛ : ∀ i, 0 ≤ D.h i Λ)
    (w : List I) (y : PreF Coefficients.Ring I) :
    wordSign D Λ w * integrablePolarization D hD Λ hΛ
        (toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)))
        (toIntegrable D hD Λ (D.toSerreF Coefficients.q pi y)) -
      D.serreForm Coefficients.q pi pi_sq
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))
        (D.toSerreF Coefficients.q pi y) =
      MvPolynomial.eval (deformationParameter D Λ) (comparisonError D w y) :=
  polarization_sub_half D hD Λ w y

end GenericVerma
end OddMath.CoveringQuantum.UDot
