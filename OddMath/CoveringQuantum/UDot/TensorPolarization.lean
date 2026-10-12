import OddMath.CoveringQuantum.UDot.TensorRepresentation
import OddMath.CoveringQuantum.UDot.LowestPolarization
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Native tensor J-polarization on the original highest/lowest quotients

The product of the accepted highest polarization and the J-repaired lowest
polarization is a well-defined bilinear form on their actual quotient tensor.
For dominant weights it is symmetric, has vacuum norm one, and pairs the
accepted Delta1 action with the accepted Delta2 action through BE2 rho, and
conversely. The proof covers the entire original unital presentation and its
nonunital modified algebra, not just homogeneous vectors or generators.

Here source v=q^-1 and rho is tau1-prime: E is adjoint to v_i K_i F and F to
v_i K_i^-1 E. Delta1/Delta2 are those of Clark, arXiv:1312.4855v2, §2.4;
tau1-prime is from Proposition 5.8. This is not the printed tau1/Delta3/Delta4
pairing of §5.3. Transport to that convention, the mixed Gram limit, separation
and nondegeneracy remain separate. The full adjointness theorem supplies the
native contravariance needed by the mixed Gram-limit route to BE2 Theorem 10.1.

No root independence, finite weight fibers, basis, local nilpotence or form
nondegeneracy is assumed. Word characters descend by the existing quotient
construction; their adjointness is proved without recovering word degree from
its possibly noninjective image in the weight group.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma
open PreF Coefficients TensorProduct
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent) (Λ Μ : X)

/-- Product of the actual highest form and the J-repaired lowest form. -/
def tensorPolarization (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ) :
    LinearMap.BilinForm Coefficients.Ring
      (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  (integrablePolarization D hD Λ hΛ).tmul (lowestPolarization D hD Μ hΜ)

@[simp] theorem tensorPolarization_tmul (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (x x' : IntegrableQuotient D hD Λ) (y y' : IntegrableQuotient D hD Μ) :
    tensorPolarization D hD Λ Μ hΛ hΜ (x ⊗ₜ y) (x' ⊗ₜ y') =
      integrablePolarization D hD Λ hΛ x x' * lowestPolarization D hD Μ hΜ y y' := by
  simp only [tensorPolarization, LinearMap.BilinForm.tmul,
    LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul, mul_comm]

/-- The arbitrary-representative formula uses the original Serre-half form and
its already descended J character; no representatives are selected. -/
theorem tensorPolarization_representatives
    (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (x x' y y' : D.serreF Coefficients.q pi) :
    tensorPolarization D hD Λ Μ hΛ hΜ
      (toIntegrable D hD Λ x ⊗ₜ toIntegrable D hD Μ y)
      (toIntegrable D hD Λ x' ⊗ₜ toIntegrable D hD Μ y') =
      polarization D hD Λ x x' * polarization D hD Μ y
        (GenericTensor.diagonal D.toSuperCartanDatum (polarizationSign D Μ) y') := by
  rw [tensorPolarization_tmul]
  rfl

@[simp] theorem tensorPolarization_vacuum (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ) :
    tensorPolarization D hD Λ Μ hΛ hΜ
      (toIntegrable D hD Λ 1 ⊗ₜ toIntegrable D hD Μ 1)
      (toIntegrable D hD Λ 1 ⊗ₜ toIntegrable D hD Μ 1) = 1 := by simp

omit [DecidableEq X] in
private theorem lower_diagonal_pair (c : I → Coefficients.Ring) (i : I) (n : ℤ)
    (x : D.serreF Coefficients.q pi) :
    lower D.toSuperCartanDatum hD i n (GenericTensor.diagonal D.toSuperCartanDatum c x) =
      c i • GenericTensor.diagonal D.toSuperCartanDatum c (lower D.toSuperCartanDatum hD i n x) := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  simp only [GenericTensor.diagonal_mk, lower_mk, ← map_smul]
  congr 1
  simp only [lowerFree, lowerNumerator, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, rDeriv_diagTwist, lDeriv_diagTwist,
    map_smul, parityTwist, weightTwist, map_sub, diagTwist_diagTwist]
  simp only [mul_comm c, smul_sub, smul_smul]
  simp only [mul_comm, mul_assoc]

private theorem polarization_diagonal (c : I → Coefficients.Ring)
    (x y : D.serreF Coefficients.q pi) :
    polarization D hD Λ (GenericTensor.diagonal D.toSuperCartanDatum c x) y =
      polarization D hD Λ x (GenericTensor.diagonal D.toSuperCartanDatum c y) := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  induction x using induction_monomial generalizing y with
  | zero => simp
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | smul a x hx => simp only [map_smul, LinearMap.smul_apply, hx]
  | word w =>
    induction w generalizing y with
    | nil =>
      simp only [monomial_nil, map_one, polarization_one_left]
      obtain ⟨y, rfl⟩ := D.toSerreF_surjective Coefficients.q pi y
      induction y using induction_monomial with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | smul a b hb => simp only [map_smul, hb]
      | word w => cases w <;> simp [GenericTensor.diagonal_mk, diagTwist_monomial]
    | cons i w ih =>
      simp only [GenericTensor.diagonal_mk, diagTwist_monomial, map_smul,
        LinearMap.smul_apply, List.map_cons, List.prod_cons, polarization_word_cons]
      rw [lower_diagonal_pair, map_smul]
      have hh := ih (lower D.toSuperCartanDatum hD i (D.h i Λ) y)
      simp only [GenericTensor.diagonal_mk, diagTwist_monomial, map_smul,
        LinearMap.smul_apply] at hh
      rw [← hh]
      simp only [smul_eq_mul]
      ring

/-- Every descended square-one word character is self-adjoint; word degree is
not reconstructed from an ambiguous root weight. -/
theorem integrablePolarization_sign (hΛ : ∀ i, 0 ≤ D.h i Λ)
    (c : I → Coefficients.Ring) (hc : ∀ i, c i ^ 2 = 1)
    (x y : IntegrableQuotient D hD Λ) :
    integrablePolarization D hD Λ hΛ (integrableSign D hD Λ c hc x) y =
      integrablePolarization D hD Λ hΛ x (integrableSign D hD Λ c hc y) := by
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  exact polarization_diagonal D hD Λ c x y

/-- Actual represented weight idempotents are self-adjoint. -/
theorem integrablePolarization_project (hΛ : ∀ i, 0 ≤ D.h i Λ) (μ : X)
    (x y : IntegrableQuotient D hD Λ) :
    integrablePolarization D hD Λ hΛ (integrableRepresentation D hD Λ (one D Coefficients.q pi μ) x) y =
      integrablePolarization D hD Λ hΛ x (integrableRepresentation D hD Λ (one D Coefficients.q pi μ) y) := by
  simpa only [rho_one] using integrablePolarization_adjoint D hD Λ hΛ (one D Coefficients.q pi μ) x y

/-- Arbitrary functions of genuine weights are self-adjoint. -/
theorem integrablePolarization_weight (hΛ : ∀ i, 0 ≤ D.h i Λ) (f : X → Coefficients.Ring)
    (x y : IntegrableQuotient D hD Λ) :
    integrablePolarization D hD Λ hΛ (integrableWeight D hD Λ f x) y =
      integrablePolarization D hD Λ hΛ x (integrableWeight D hD Λ f y) := by
  induction x using integrable_weight_induction D hD Λ with
  | zero => simp
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | project μ x =>
    rw [integrableWeight_project, map_smul, LinearMap.smul_apply,
      integrablePolarization_project, integrablePolarization_project]
    induction y using integrable_weight_induction D hD Λ with
    | zero => simp
    | add y z hy hz => simp only [map_add, smul_add, hy, hz]
    | project ν y =>
      rw [integrableWeight_project]
      simp only [map_smul, ← Module.End.mul_apply,
        ← map_mul, one_mul_one]
      split_ifs with h
      · subst ν; rfl
      · simp

theorem lowestPolarization_symmetric (hΛ : ∀ i, 0 ≤ D.h i Λ)
    (x y : IntegrableQuotient D hD Λ) :
    lowestPolarization D hD Λ hΛ x y = lowestPolarization D hD Λ hΛ y x := by
  change integrablePolarization D hD Λ hΛ x (integrableJ D hD Λ y) =
    integrablePolarization D hD Λ hΛ y (integrableJ D hD Λ x)
  unfold integrableJ
  rw [← integrablePolarization_sign, integrablePolarization_symmetric]

theorem lowestPolarization_project (hΛ : ∀ i, 0 ≤ D.h i Λ) (μ : X)
    (x y : IntegrableQuotient D hD Λ) :
    lowestPolarization D hD Λ hΛ (integrableRepresentation D hD Λ (one D Coefficients.q pi μ) x) y =
      lowestPolarization D hD Λ hΛ x (integrableRepresentation D hD Λ (one D Coefficients.q pi μ) y) := by
  simpa only [rho_one, lowestRepresentation_one, neg_neg] using
    lowestPolarization_adjoint D hD Λ hΛ (one D Coefficients.q pi (-μ)) x y

private theorem form_weight_self (B : LinearMap.BilinForm Coefficients.Ring (IntegrableQuotient D hD Λ))
    (hp : ∀ μ x y, B (integrableRepresentation D hD Λ (one D Coefficients.q pi μ) x) y =
      B x (integrableRepresentation D hD Λ (one D Coefficients.q pi μ) y))
    (f : X → Coefficients.Ring) (x y : IntegrableQuotient D hD Λ) :
    B (integrableWeight D hD Λ f x) y = B x (integrableWeight D hD Λ f y) := by
  induction x using integrable_weight_induction D hD Λ with
  | zero => simp
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | project μ x =>
    rw [integrableWeight_project, map_smul, LinearMap.smul_apply, hp, hp]
    induction y using integrable_weight_induction D hD Λ with
    | zero => simp
    | add y z hy hz => simp only [map_add, smul_add, hy, hz]
    | project ν y =>
      rw [integrableWeight_project]
      simp only [map_smul, ← Module.End.mul_apply, ← map_mul, one_mul_one]
      split_ifs with h
      · subst ν; rfl
      · simp

theorem lowestPolarization_weight (hΛ : ∀ i, 0 ≤ D.h i Λ) (f : X → Coefficients.Ring)
    (x y : IntegrableQuotient D hD Λ) :
    lowestPolarization D hD Λ hΛ (integrableWeight D hD Λ f x) y =
      lowestPolarization D hD Λ hΛ x (integrableWeight D hD Λ f y) :=
  form_weight_self D hD Λ _ (lowestPolarization_project D hD Λ hΛ) f x y

/-- Native tau1-prime: E is adjoint to v_i K_i F on the highest factor. -/
theorem integrablePolarization_global_E (hΛ : ∀ i, 0 ≤ D.h i Λ) (i : I)
    (x y : IntegrableQuotient D hD Λ) :
    integrablePolarization D hD Λ hΛ (integrableChevalley D hD Λ true i x) y =
      qp Coefficients.q (-D.d i) • integrablePolarization D hD Λ hΛ x
        (tensorK D hD Λ i (integrableChevalley D hD Λ false i y)) := by
  induction x using integrable_weight_induction D hD Λ with
  | zero => simp
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, smul_add]
  | project μ x =>
    rw [integrableChevalley_project]
    change integrablePolarization D hD Λ hΛ (integrableRepresentation D hD Λ (E D Coefficients.q pi i μ) x) y = _
    rw [integrablePolarization_E, tensorK, ← integrablePolarization_weight,
      integrableWeight_project, map_smul, LinearMap.smul_apply,
      integrablePolarization_project, integrableProject_chevalley,
      integrableChevalley_project]
    simp only [halfRoot, Bool.false_eq_true, ite_false, sub_neg_eq_add, halfGen,
      tensorToralScalar, one_mul, smul_smul, qp_mul]
    congr 2
    ring

/-- On the omega-lowest factor the source K is the inverse of the underlying K. -/
theorem lowestPolarization_global_E (hΜ : ∀ i, 0 ≤ D.h i Μ) (i : I)
    (x y : IntegrableQuotient D hD Μ) :
    lowestPolarization D hD Μ hΜ (integrableChevalley D hD Μ false i x) y =
      qp Coefficients.q (-D.d i) • lowestPolarization D hD Μ hΜ x
        (tensorKInv D hD Μ i (lowestF D hD Μ i y)) := by
  induction x using integrable_weight_induction D hD Μ with
  | zero => simp
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, smul_add]
  | project μ x =>
    have he := lowestPolarization_adjoint D hD Μ hΜ (E D Coefficients.q pi i (-μ)) x y
    simp only [lowestRepresentation_E, neg_neg, rho_E, map_smul, LinearMap.smul_apply] at he
    rw [integrableChevalley_project]
    change lowestPolarization D hD Μ hΜ (integrableRepresentation D hD Μ (F D Coefficients.q pi i μ) x) y = _
    rw [he, tensorKInv, ← lowestPolarization_weight, integrableWeight_project,
      map_smul, LinearMap.smul_apply, lowestPolarization_project]
    have hp : integrableRepresentation D hD Μ (one D Coefficients.q pi μ) (lowestF D hD Μ i y) =
        lowestF D hD Μ i (integrableRepresentation D hD Μ (one D Coefficients.q pi (μ - D.α i)) y) := by
      simp only [lowestF_eq_smul, map_smul, LinearMap.smul_apply,
        integrableProject_chevalley, halfRoot, ite_true]
    rw [hp]
    have hn : μ - D.α i = -(-μ + D.α i) := by abel
    rw [hn, ← lowestRepresentation_one, lowestF_project]
    simp only [RootDatum.h, map_neg, smul_smul, qp_mul]
    congr 2
    ring

theorem tensorPolarization_symmetric (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (x y : IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :
    tensorPolarization D hD Λ Μ hΛ hΜ x y = tensorPolarization D hD Λ Μ hΛ hΜ y x := by
  exact (LinearMap.IsSymm.tmul ⟨integrablePolarization_symmetric D hD Λ hΛ⟩
    ⟨lowestPolarization_symmetric D hD Μ hΜ⟩).eq x y

private theorem polarization_twist (hΛ : ∀ i, 0 ≤ D.h i Λ) (s : Bool) (i : I)
    (x y : IntegrableQuotient D hD Λ) :
    integrablePolarization D hD Λ hΛ (tensorTwist D hD Λ s i x) y =
      integrablePolarization D hD Λ hΛ x
        (tensorK D hD Λ i (tensorFTwist D hD Λ (!s) i y)) := by
  have hp := (integrableWeight_parity D hD Λ (tensorToralScalar D false i) i).eq
  simp only [tensorTwist_eq_smul, tensorFTwist_eq_smul, LinearMap.smul_apply,
    Module.End.mul_apply, map_smul]
  rw [tensorK, integrablePolarization_weight]
  change _ • integrablePolarization D hD Λ hΛ (integrableSign D hD Λ _ _ x) _ = _
  rw [integrablePolarization_sign]
  have hh := congrArg (fun f ↦ f y) hp
  simp only [Module.End.mul_apply] at hh
  change _ = _ • integrablePolarization D hD Λ hΛ x (tensorK D hD Λ i (integrableParity D hD Λ i y))
  change _ • integrablePolarization D hD Λ hΛ x (integrableParity D hD Λ i (integrableWeight D hD Λ (tensorToralScalar D false i) y)) = _
  rw [← hh]
  cases s <;> rfl

/-- Exact native generator adjoint: Delta1(E) pairs with Delta2(v_i K_i F),
and conversely. All toral and Koszul factors are the accepted operators. -/
theorem tensorPolarization_global_E (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (i : I)
    (x y : IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :
    tensorPolarization D hD Λ Μ hΛ hΜ (tensorE D hD Λ Μ s i x) y =
      qp Coefficients.q (-D.d i) • tensorPolarization D hD Λ Μ hΛ hΜ x
        (tensorGroupK D hD Λ Μ i (tensorF D hD Λ Μ (!s) i y)) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, smul_add]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz, smul_add]
    | tmul c d =>
      simp only [tensorE_tmul, tensorF_tmul, map_add, LinearMap.add_apply,
        tensorGroupK_tmul, tensorPolarization_tmul]
      rw [integrablePolarization_global_E, lowestPolarization_global_E, polarization_twist]
      have hk := congrArg (fun f ↦ f d) (tensorK_inv_mul D hD Μ i)
      simp only [Module.End.mul_apply, Module.End.one_apply] at hk
      rw [hk]
      simp only [smul_eq_mul]
      ring

theorem tensorPolarization_groupK (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (i : I) (x y : IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :
    tensorPolarization D hD Λ Μ hΛ hΜ (tensorGroupK D hD Λ Μ i x) y =
      tensorPolarization D hD Λ Μ hΛ hΜ x (tensorGroupK D hD Λ Μ i y) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul c d =>
      simp only [tensorGroupK_tmul, tensorPolarization_tmul, tensorK, tensorKInv,
        integrablePolarization_weight, lowestPolarization_weight]

private theorem lowestPolarization_orthogonal (hΜ : ∀ i, 0 ≤ D.h i Μ) {μ ν : X} (hn : μ ≠ ν)
    (x y : IntegrableQuotient D hD Μ) :
    lowestPolarization D hD Μ hΜ
      (integrableRepresentation D hD Μ (one D Coefficients.q pi μ) x)
      (integrableRepresentation D hD Μ (one D Coefficients.q pi ν) y) = 0 := by
  rw [lowestPolarization_project, ← Module.End.mul_apply, ← map_mul, one_mul_one]
  simp [hn]

theorem tensorPolarization_project (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (η : X) (x y : IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :
    tensorPolarization D hD Λ Μ hΛ hΜ (tensorProject D hD Λ Μ η x) y =
      tensorPolarization D hD Λ Μ hΛ hΜ x (tensorProject D hD Λ Μ η y) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul c d =>
      induction b using integrable_weight_induction D hD Μ with
      | zero => simp
      | add b e hb he => simp only [tmul_add, map_add, LinearMap.add_apply, hb, he]
      | project μ b =>
        induction d using integrable_weight_induction D hD Μ with
        | zero => simp
        | add d e hd he => simp only [tmul_add, map_add, hd, he]
        | project ν d =>
          simp only [tensorProject_tmul_project, tensorPolarization_tmul]
          by_cases hn : μ = ν
          · subst ν; rw [integrablePolarization_project]
          · rw [lowestPolarization_orthogonal D hD Μ hΜ hn, mul_zero, mul_zero]

/-- Group-like K has the actual total-weight eigenvalue on every projector. -/
theorem tensorGroupK_project (i : I) (η : X)
    (x : IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :
    tensorGroupK D hD Λ Μ i (tensorProject D hD Λ Μ η x) =
      qp Coefficients.q (-(D.d i * D.h i η)) • tensorProject D hD Λ Μ η x := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, hx, hz, smul_add]
  | tmul a b =>
    induction b using integrable_weight_induction D hD Μ with
    | zero => simp
    | add b c hb hc => simp only [tmul_add, map_add, hb, hc, smul_add]
    | project ν b =>
      simp only [tensorProject_tmul_project, tensorGroupK_tmul, tensorK, tensorKInv,
        integrableWeight_project, smul_tmul, tmul_smul, smul_smul, tensorToralScalar,
        Bool.false_eq_true, ite_false, one_mul, qp_mul]
      congr 2
      simp only [RootDatum.h, map_add]
      ring

/-- Weight-labelled E adjoint, with the exact original rho coefficient. -/
theorem tensorPolarization_E (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (i : I) (μ : X)
    (x y : IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :
    tensorPolarization D hD Λ Μ hΛ hΜ (tensorRepresentation D hD Λ Μ s (E D Coefficients.q pi i μ) x) y =
      qp Coefficients.q (-(D.d i * (D.h i μ + 1))) • tensorPolarization D hD Λ Μ hΛ hΜ x
        (tensorRepresentation D hD Λ Μ (!s) (F D Coefficients.q pi i (μ + D.α i)) y) := by
  simp only [tensorRepresentation_E, tensorEBlock, Module.End.mul_apply]
  rw [tensorPolarization_global_E, ← tensorPolarization_groupK, tensorGroupK_project,
    map_smul, LinearMap.smul_apply, tensorPolarization_project, smul_smul, qp_mul]
  have hp := congrArg (fun f ↦ f y) (tensorProject_F D hD Λ Μ (!s) i μ)
  simp only [Module.End.mul_apply] at hp
  rw [hp, tensorRepresentation_F, Module.End.mul_apply]
  congr 2
  ring

/-- Weight-labelled F adjoint. Symmetry and the inverse rho coefficients yield
this from E without assuming nondegeneracy of either factor. -/
theorem tensorPolarization_F (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (i : I) (μ : X)
    (x y : IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :
    tensorPolarization D hD Λ Μ hΛ hΜ (tensorRepresentation D hD Λ Μ s (F D Coefficients.q pi i μ) x) y =
      qp Coefficients.q (D.d i * (D.h i μ - 1)) • tensorPolarization D hD Λ Μ hΛ hΜ x
        (tensorRepresentation D hD Λ Μ (!s) (E D Coefficients.q pi i (μ - D.α i)) y) := by
  have h := tensorPolarization_E D hD Λ Μ hΛ hΜ (!s) i (μ - D.α i) y x
  simp only [Bool.not_not, sub_add_cancel] at h
  rw [tensorPolarization_symmetric D hD Λ Μ hΛ hΜ x, h, smul_smul]
  have hc : qp Coefficients.q (D.d i * (D.h i μ - 1)) *
      qp Coefficients.q (-(D.d i * (D.h i (μ - D.α i) + 1))) = 1 := by
    rw [qp_mul]
    apply qp_eq_one
    simp only [RootDatum.h, map_sub, D.coroot_root, D.isGCM.diag]
    ring
  rw [hc, one_smul, tensorPolarization_symmetric]

/-- Full original-envelope adjointness for the genuine Delta1/Delta2 action pair.
The anti-involution is native BE2 rho = tau1-prime at source v=q^-1. -/
theorem tensorPolarization_adjoint (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (u : CoveringUDot Coefficients.Ring D Coefficients.q pi)
    (x y : IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :
    tensorPolarization D hD Λ Μ hΛ hΜ (tensorRepresentation D hD Λ Μ s u x) y =
      tensorPolarization D hD Λ Μ hΛ hΜ x
        (tensorRepresentation D hD Λ Μ (!s) (rho D Coefficients.q pi pi_sq u).unop y) := by
  obtain ⟨u, rfl⟩ := mk_surjective D Coefficients.q pi u
  induction u using FreeAlgebra.induction generalizing x y with
  | grade0 c => simp
  | grade1 g =>
    cases g with
    | one μ =>
      change tensorPolarization D hD Λ Μ hΛ hΜ (tensorRepresentation D hD Λ Μ s (one D Coefficients.q pi μ) x) y = tensorPolarization D hD Λ Μ hΛ hΜ x (tensorRepresentation D hD Λ Μ (!s) (rho D Coefficients.q pi pi_sq (one D Coefficients.q pi μ)).unop y)
      simp only [rho_one, tensorRepresentation_one]
      exact tensorPolarization_project D hD Λ Μ hΛ hΜ μ x y
    | e i μ =>
      change tensorPolarization D hD Λ Μ hΛ hΜ (tensorRepresentation D hD Λ Μ s (E D Coefficients.q pi i μ) x) y = tensorPolarization D hD Λ Μ hΛ hΜ x (tensorRepresentation D hD Λ Μ (!s) (rho D Coefficients.q pi pi_sq (E D Coefficients.q pi i μ)).unop y)
      simpa only [rho_E, map_smul, LinearMap.smul_apply] using tensorPolarization_E D hD Λ Μ hΛ hΜ s i μ x y
    | f i μ =>
      change tensorPolarization D hD Λ Μ hΛ hΜ (tensorRepresentation D hD Λ Μ s (F D Coefficients.q pi i μ) x) y = tensorPolarization D hD Λ Μ hΛ hΜ x (tensorRepresentation D hD Λ Μ (!s) (rho D Coefficients.q pi pi_sq (F D Coefficients.q pi i μ)).unop y)
      simpa only [rho_F, map_smul, LinearMap.smul_apply] using tensorPolarization_F D hD Λ Μ hΛ hΜ s i μ x y
  | add a b ha hb => simp only [map_add, MulOpposite.unop_add, LinearMap.add_apply, map_add, ha, hb]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_apply, MulOpposite.unop_mul]
    rw [ha, hb]

/-- Restriction to the actual original modified algebra, including arbitrary
inhomogeneous elements and tensors. No new compatibility packet is assumed. -/
theorem tensorPolarization_modified_adjoint
    (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (u : modified D Coefficients.q pi)
    (x y : IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :
    tensorPolarization D hD Λ Μ hΛ hΜ (tensorModifiedRepresentation D hD Λ Μ s u x) y =
      tensorPolarization D hD Λ Μ hΛ hΜ x
        (tensorModifiedRepresentation D hD Λ Μ (!s) (rhoModified D Coefficients.q pi pi_sq u) y) :=
  tensorPolarization_adjoint D hD Λ Μ hΛ hΜ s u x y

/-- Source group-like K inverse on the original highest/lowest tensor. -/
def tensorGroupKInv (i : I) : Module.End Coefficients.Ring
    (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  TensorProduct.map (tensorKInv D hD Λ i) (tensorK D hD Μ i)

theorem tensorGroupKInv_project (i : I) (η : X)
    (x : IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :
    tensorGroupKInv D hD Λ Μ i (tensorProject D hD Λ Μ η x) =
      qp Coefficients.q (D.d i * D.h i η) • tensorProject D hD Λ Μ η x := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, hx, hz, smul_add]
  | tmul a b =>
    induction b using integrable_weight_induction D hD Μ with
    | zero => simp
    | add b c hb hc => simp only [tmul_add, map_add, hb, hc, smul_add]
    | project ν b =>
      simp only [tensorProject_tmul_project, tensorGroupKInv, TensorProduct.map_tmul,
        tensorK, tensorKInv, integrableWeight_project, smul_tmul, tmul_smul,
        smul_smul, tensorToralScalar, Bool.false_eq_true, ite_false, one_mul, qp_mul]
      congr 2
      simp only [RootDatum.h, map_add]
      ring

theorem tensorPolarization_groupKInv (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (i : I) (x y : IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :
    tensorPolarization D hD Λ Μ hΛ hΜ (tensorGroupKInv D hD Λ Μ i x) y =
      tensorPolarization D hD Λ Μ hΛ hΜ x (tensorGroupKInv D hD Λ Μ i y) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul c d =>
      simp only [tensorGroupKInv, TensorProduct.map_tmul, tensorPolarization_tmul,
        tensorK, tensorKInv, integrablePolarization_weight, lowestPolarization_weight]

private theorem tensor_weight_induction
    {P : IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ → Prop}
    (project : ∀ μ x, P (tensorProject D hD Λ Μ μ x)) (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y)) (x) : P x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => exact add x y hx hy
  | tmul a b =>
    induction a using integrable_weight_induction D hD Λ with
    | zero => simpa only [zero_tmul] using zero
    | add a c ha hc => simpa only [add_tmul] using add _ _ ha hc
    | project μ a =>
      induction b using integrable_weight_induction D hD Μ with
      | zero => simpa only [tmul_zero] using zero
      | add b c hb hc => simpa only [tmul_add] using add _ _ hb hc
      | project ν b =>
        have hh := project (μ - ν)
          (integrableRepresentation D hD Λ (one D Coefficients.q pi μ) a ⊗ₜ
            integrableRepresentation D hD Μ (one D Coefficients.q pi ν) b)
        simpa only [tensorProject_tmul_project, sub_add_cancel, ← Module.End.mul_apply,
          ← map_mul, one_mul_one_self] using hh

/-- Exact global F adjoint: the other genuine coproduct applied to v_i K_i^-1 E.
This is proved on arbitrary tensors, not just on weight vectors or the vacuum. -/
theorem tensorPolarization_global_F (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (i : I)
    (x y : IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :
    tensorPolarization D hD Λ Μ hΛ hΜ (tensorF D hD Λ Μ s i x) y =
      qp Coefficients.q (-D.d i) • tensorPolarization D hD Λ Μ hΛ hΜ x
        (tensorGroupKInv D hD Λ Μ i (tensorE D hD Λ Μ (!s) i y)) := by
  induction x using tensor_weight_induction D hD Λ Μ with
  | zero => simp
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, smul_add]
  | project μ x =>
    have hf := tensorPolarization_F D hD Λ Μ hΛ hΜ s i μ x y
    simp only [tensorRepresentation_F, tensorRepresentation_E, tensorEBlock,
      Module.End.mul_apply] at hf
    rw [hf, ← tensorPolarization_groupKInv, tensorGroupKInv_project,
      map_smul, LinearMap.smul_apply, tensorPolarization_project, smul_smul, qp_mul]
    have hp := congrArg (fun f ↦ f y) (tensorProject_E D hD Λ Μ (!s) i μ)
    simp only [Module.End.mul_apply] at hp
    rw [hp]
    congr 2
    ring

end OddMath.CoveringQuantum.UDot.GenericVerma
