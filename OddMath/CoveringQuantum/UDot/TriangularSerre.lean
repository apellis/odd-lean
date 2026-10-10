import OddMath.CoveringQuantum.UDot.TriangularOperators

/-!
# Positive Serre relations on the regular triangular tensor module

For the actual generic Serre half `F`, the regular operators of
`TriangularOperators` satisfy the positive Serre relations on all of `F ⊗ F`.
Toral covariance gives a free-word mixed identity involving the skew derivatives
at `q⁻¹` and `q`. Both derivatives kill a Serre element; induction in the first
factor then extends the known vacuum identity to the entire tensor product.

This is a direct regular-module variant of the tensor construction in [CHW1] v2
§2.3, using the corrected [BE2]-convention operators already defined in
`TriangularOperators`. It uses neither toral-character separation nor a field
hypothesis. Finiteness and bar-consistency enter through the existing generic
quotient numerators. `positiveHalfAction` is an actual quotient algebra action;
tensor weight projections, modified-presentation descent, and triangular
injectivity are separate obligations.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open PreF Coefficients TensorProduct
variable {I : Type*} [DecidableEq I] [Finite I]
variable (C : SuperCartanDatum I) (hC : C.BarConsistent)

private theorem numerator_diag (i : I) (a b : Coefficients.Ring)
    (c : I → Coefficients.Ring) (x : C.serreF Coefficients.q pi) :
    numerator C hC i a b (diagonal C c x) =
      c i • diagonal C c (numerator C hC i a b x) := by
  obtain ⟨x, rfl⟩ := C.toSerreF_surjective Coefficients.q pi x
  have h : lowerNumerator C Coefficients.q pi i a b (diagTwist c x) =
      c i • diagTwist c (lowerNumerator C Coefficients.q pi i a b x) := by
    simp only [lowerNumerator, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, AlgHom.toLinearMap_apply, rDeriv_diagTwist, lDeriv_diagTwist,
      map_smul, map_sub, parityTwist, weightTwist, diagTwist_comm c]
    simp only [smul_sub, smul_comm (c i)]
  simpa only [diagonal_mk, numerator_mk, map_smul] using
    congrArg (C.toSerreF Coefficients.q pi) h

private theorem weight_numerator (v : Coefficients.Ringˣ) (i j : I)
    (a b : Coefficients.Ring) (x : C.serreF Coefficients.q pi) :
    weight C v i (numerator C hC j a b x) =
      ((v ^ (-C.dot i j) : Coefficients.Ringˣ) : Coefficients.Ring) •
        numerator C hC j a b (weight C v i x) := by
  rw [weight, numerator_diag, smul_smul]
  simp only [← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
    Units.val_one, one_smul]

omit [DecidableEq I] [Finite I] in
private theorem diagonal_comm (c d : I → Coefficients.Ring)
    (x : C.serreF Coefficients.q pi) :
    diagonal C c (diagonal C d x) = diagonal C d (diagonal C c x) := by
  obtain ⟨x, rfl⟩ := C.toSerreF_surjective Coefficients.q pi x
  simp only [diagonal_mk, diagTwist_comm c d]

/-- Toral covariance of the positive regular operators on the whole tensor. -/
theorem toral_positive (n : I → ℤ) (v : Coefficients.Ringˣ) (i j : I) :
    toral C v i * positive C hC n j =
      ((v ^ C.dot i j : Coefficients.Ringˣ) : Coefficients.Ring) •
        (positive C hC n j * toral C v i) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
    Module.End.mul_apply, positive, toral, LinearMap.add_apply,
    LinearMap.smul_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
    map_add, map_smul, create, Algebra.lsmul_apply]
  simp only [smul_eq_mul, map_mul, weight_numerator, inv_zpow, zpow_neg, inv_inv]
  have hp := diagonal_comm C
    (fun l ↦ ((v⁻¹ ^ C.dot i l : Coefficients.Ringˣ) : Coefficients.Ring))
    (fun l ↦ pi ^ (C.parity j * C.parity l).val) x
  have hw (u : Coefficients.Ringˣ) := diagonal_comm C
    (fun l ↦ ((v ^ C.dot i l : Coefficients.Ringˣ) : Coefficients.Ring))
    (fun l ↦ ((u ^ C.dot j l : Coefficients.Ringˣ) : Coefficients.Ring)) y
  simp only [weight, parity] at hp hw ⊢
  rw [hp, hw Coefficients.q, hw Coefficients.q⁻¹, diagonal_θ]
  simp only [smul_mul_assoc, tmul_smul, smul_tmul, smul_add, smul_smul,
    mul_comm (Ring.inverse (vermaDenominator C Coefficients.q pi j))]

private abbrev coeffA (n : I → ℤ) (i : I) : Coefficients.Ring :=
  Ring.inverse (vermaDenominator C Coefficients.q pi i) *
    (((C.qi Coefficients.q i) ^ n i : Coefficients.Ringˣ) : Coefficients.Ring)

private abbrev coeffB (n : I → ℤ) (i : I) : Coefficients.Ring :=
  Ring.inverse (vermaDenominator C Coefficients.q pi i) *
    (-(C.pii pi i ^ (n i).natAbs *
      (((C.qi Coefficients.q i) ^ (-n i) : Coefficients.Ringˣ) : Coefficients.Ring)))

private theorem mixed_apply (n : I → ℤ) (i l : I)
    (z : C.serreF Coefficients.q pi ⊗[Coefficients.Ring] C.serreF Coefficients.q pi) :
    positive C hC n i (negative C l z) =
      pi ^ (C.parity l * C.parity i).val • negative C l (positive C hC n i z) +
      if i = l then coeffA C n l • toral C Coefficients.q l z +
        coeffB C n l • toral C Coefficients.q⁻¹ l z else 0 := by
  have h := congrArg (fun f ↦ f z) (positive_negative C hC n i l)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at h
  rw [h]
  by_cases hil : i = l
  · subst i
    simp only [ite_true, coeffA, coeffB, LinearMap.smul_apply, LinearMap.add_apply,
      smul_add, smul_smul]
  · simp [hil, mul_comm (C.parity i) (C.parity l)]

private theorem toral_positive_apply (n : I → ℤ) (v : Coefficients.Ringˣ) (l i : I)
    (z : C.serreF Coefficients.q pi ⊗[Coefficients.Ring] C.serreF Coefficients.q pi) :
    toral C v l (positive C hC n i z) =
      ((v ^ C.dot l i : Coefficients.Ringˣ) : Coefficients.Ring) •
        positive C hC n i (toral C v l z) :=
  congrArg (fun f ↦ f z) (toral_positive C hC n v l i)

/-- Commuting an arbitrary free positive element past a negative generator.
The two correction terms use the skew derivatives at opposite parameters. -/
theorem positiveFree_mixed (n : I → ℤ) (x : PreF Coefficients.Ring I) (l : I)
    (z : C.serreF Coefficients.q pi ⊗[Coefficients.Ring] C.serreF Coefficients.q pi) :
    positiveFree C hC n x (negative C l z) =
      negative C l (positiveFree C hC n (parityTwist C pi l x) z) +
      (Ring.inverse (vermaDenominator C Coefficients.q pi l) *
        (((C.qi Coefficients.q l) ^ n l : Coefficients.Ringˣ) : Coefficients.Ring)) •
        positiveFree C hC n (rDeriv (C.chi Coefficients.q⁻¹ pi) l x)
          (toral C Coefficients.q l z) +
      (Ring.inverse (vermaDenominator C Coefficients.q pi l) *
        (-(C.pii pi l ^ (n l).natAbs *
          (((C.qi Coefficients.q l) ^ (-n l) : Coefficients.Ringˣ) : Coefficients.Ring)))) •
        positiveFree C hC n (rDeriv (C.chi Coefficients.q pi) l x)
          (toral C Coefficients.q⁻¹ l z) := by
  change positiveFree C hC n x (negative C l z) =
    negative C l (positiveFree C hC n (parityTwist C pi l x) z) +
    coeffA C n l • positiveFree C hC n (rDeriv (C.chi Coefficients.q⁻¹ pi) l x)
      (toral C Coefficients.q l z) +
    coeffB C n l • positiveFree C hC n (rDeriv (C.chi Coefficients.q pi) l x)
      (toral C Coefficients.q⁻¹ l z)
  induction x using induction_right generalizing z with
  | algebraMap c =>
    simp [Module.algebraMap_end_apply]
  | smul c x hx =>
    simp only [map_smul, LinearMap.smul_apply, hx]
    simp only [smul_add, smul_comm c]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy]
    simp only [smul_add]
    abel
  | mul_θ x i hx =>
    simp only [map_mul, Module.End.mul_apply, positiveFree_θ]
    rw [mixed_apply]
    simp only [map_add, map_smul, hx, rDeriv_mul_θ, map_mul, map_add, map_smul,
      Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      show ∀ j, parityTwist C pi l (θ Coefficients.Ring j) =
        pi ^ (C.parity l * C.parity j).val • θ Coefficients.Ring j from
        fun j ↦ diagTwist_θ _ j, positiveFree_θ]
    rw [toral_positive_apply C hC n Coefficients.q,
      toral_positive_apply C hC n Coefficients.q⁻¹]
    simp only [map_smul, inv_zpow, SuperCartanDatum.chi_apply]
    by_cases hil : i = l
    · subst i
      simp only [ite_true, map_add, map_smul]
      simp only [smul_add, smul_smul, zpow_neg]
      simp only [inv_inv, mul_assoc, mul_left_comm, mul_comm]
      abel
    · simp only [hil, Ne.symm hil, ite_false, map_zero, LinearMap.zero_apply]
      simp only [smul_add, smul_smul, zpow_neg, add_zero]
      simp only [inv_inv, mul_assoc, mul_left_comm, mul_comm, smul_zero, zero_add]

/-- The positive Serre relations hold as endomorphism identities on the entire
actual tensor product, not merely on the first-factor vacuum. -/
theorem positive_serre (n : I → ℤ) (i j : I) (hij : i ≠ j) :
    positiveFree C hC n (C.serreElt Coefficients.q pi i j) = 0 := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, LinearMap.zero_apply]
  obtain ⟨x, rfl⟩ := C.toSerreF_surjective Coefficients.q pi x
  induction x using induction_left with
  | algebraMap c =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one, ← smul_tmul', map_smul,
      positive_serre_vacuum C hC n i j hij, smul_zero]
  | smul c x hx => rw [map_smul, ← smul_tmul', map_smul, hx, smul_zero]
  | add x z hx hz => rw [map_add, add_tmul, map_add, hx, hz, add_zero]
  | θ_mul l x hx =>
    rw [map_mul, ← negative_tmul, positiveFree_mixed,
      C.rDeriv_serreElt Coefficients.q pi pi_sq hij,
      ← serreElt_inv_q C Coefficients.q pi pi_sq hij,
      C.rDeriv_serreElt Coefficients.q⁻¹ pi pi_sq hij,
      serreElt_inv_q C Coefficients.q pi pi_sq hij]
    simp only [parityTwist, C.diagTwist_serreElt, map_smul, LinearMap.smul_apply,
      hx, map_zero, LinearMap.zero_apply, smul_zero, add_zero]

/-- The positive Serre half acts on the actual two-sided regular tensor module. -/
def positiveHalfAction (n : I → ℤ) : C.serreF Coefficients.q pi →ₐ[Coefficients.Ring]
    Module.End Coefficients.Ring
      (C.serreF Coefficients.q pi ⊗[Coefficients.Ring] C.serreF Coefficients.q pi) :=
  RingQuot.liftAlgHom Coefficients.Ring
    ⟨positiveFree C hC n, fun x y h ↦ by
      cases h with
      | serre i j hij => rw [map_zero, positive_serre C hC n i j hij]⟩

/-- The quotient action agrees with the original free regular action. -/
@[simp] theorem positiveHalfAction_mk (n : I → ℤ) (x : PreF Coefficients.Ring I) :
    positiveHalfAction C hC n (C.toSerreF Coefficients.q pi x) =
      positiveFree C hC n x := by
  change RingQuot.liftAlgHom Coefficients.Ring _
    (RingQuot.mkAlgHom Coefficients.Ring _ _) = _
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]

@[simp] theorem positiveHalfAction_θ (n : I → ℤ) (i : I) :
    positiveHalfAction C hC n (C.toSerreF Coefficients.q pi (θ Coefficients.Ring i)) =
      positive C hC n i := by
  rw [positiveHalfAction_mk, positiveFree_θ]

/-- On a first-factor vacuum, arbitrary positive-half elements act by multiplication
in the second factor. Neither argument needs to be homogeneous. -/
theorem positiveHalfAction_vacuum (n : I → ℤ) (x y : C.serreF Coefficients.q pi) :
    positiveHalfAction C hC n x ((1 : C.serreF Coefficients.q pi) ⊗ₜ[Coefficients.Ring] y) =
      (1 : C.serreF Coefficients.q pi) ⊗ₜ[Coefficients.Ring] (x * y) := by
  obtain ⟨x, rfl⟩ := C.toSerreF_surjective Coefficients.q pi x
  rw [positiveHalfAction_mk, positiveFree_vacuum]

/-- Exact vacuum recovery by the two genuine half-algebra actions. This does not
assert descent of the modified presentation or triangular injectivity. -/
theorem halfActions_vacuum (n : I → ℤ) (x y : C.serreF Coefficients.q pi) :
    negativeHalfAction C x
      (positiveHalfAction C hC n y ((1 : C.serreF Coefficients.q pi) ⊗ₜ[Coefficients.Ring] 1)) =
      x ⊗ₜ[Coefficients.Ring] y := by
  rw [positiveHalfAction_vacuum]
  simp [negativeHalfAction]

end OddMath.CoveringQuantum.UDot.GenericTensor
