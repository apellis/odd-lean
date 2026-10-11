import OddMath.CoveringQuantum.UDot.ModifiedForm

/-!
# Uniqueness and symmetry of the actual modified-algebra form

Endpoint orthogonality, left rho-adjointness for all modified elements, and
normalization on all negative-half pairs characterize `modifiedForm` uniquely.
The proof uses finite local units and the positive-negative spanning family
obtained by applying the actual semilinear omega to triangular spanning.
Transposing the form then gives symmetry by uniqueness.

The statements concern arbitrary, possibly nonhomogeneous elements over the
generic covering ring, for finite bar-consistent data. No independence of the
simple roots, nondegeneracy, or full-form hypothesis is used in the construction.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients TensorProduct PreF
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

private def wordModified (positive : Bool) (w : List I) (μ : X) :
    modified D Coefficients.q pi :=
  ⟨halfWord D Coefficients.q pi positive w μ,
    block_le_modified D Coefficients.q pi _ _ (halfWord_mem_block D Coefficients.q pi positive w μ)⟩

private def weightOne (μ : X) : modified D Coefficients.q pi :=
  ⟨one D Coefficients.q pi μ, one_mem_modified D Coefficients.q pi μ⟩

private theorem wordModified_negative (w : List I) (μ : X) :
    wordModified D false w μ = negativeHalf D Coefficients.q pi μ
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) := by
  apply Subtype.ext
  exact (halfMap_monomial D Coefficients.q pi false w μ).symm

private theorem linear_ext_EF
    (f g : modified D Coefficients.q pi →ₗ[Coefficients.Ring] Coefficients.Ring)
    (h : ∀ a b μ ν, f (wordModified D true a μ * wordModified D false b ν) =
      g (wordModified D true a μ * wordModified D false b ν)) : f = g := by
  ext x
  have hx : (omegaModified D x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈
      triangularSpan D Coefficients.q pi := by
    rw [triangularSpan_eq_modified]
    exact (omegaModified D x).property
  have aux : ∀ z ∈ triangularSpan D Coefficients.q pi, ∀ hz : z ∈ modified D Coefficients.q pi,
      f (omegaModified D ⟨z, hz⟩) = g (omegaModified D ⟨z, hz⟩) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, b, μ, ν, rfl⟩ := hz
      intro hz
      have he : omegaModified D ⟨halfWord D Coefficients.q pi false a μ *
          halfWord D Coefficients.q pi true b ν, hz⟩ =
          wordModified D true a (-μ) * wordModified D false b (-ν) := by
        apply Subtype.ext
        exact (map_mul (omega D Coefficients.q pi bar barData) _ _).trans
          (congrArg₂ (· * ·) (omega_negative_halfWord D μ a) (GenericVerma.omega_halfWord D ν b))
      rw [he]
      exact h a b (-μ) (-ν)
    | zero => intro hz; change f (omegaModified D 0) = g (omegaModified D 0); simp
    | add z w hz hw ihz ihw =>
      intro hzw
      have ez : z ∈ modified D Coefficients.q pi := by
        change z ∈ (modified D Coefficients.q pi).toSubmodule
        rw [← triangularSpan_eq_modified]; exact hz
      have ew : w ∈ modified D Coefficients.q pi := by
        change w ∈ (modified D Coefficients.q pi).toSubmodule
        rw [← triangularSpan_eq_modified]; exact hw
      change f (omegaModified D (⟨z, ez⟩ + ⟨w, ew⟩)) = g (omegaModified D (⟨z, ez⟩ + ⟨w, ew⟩))
      simp only [map_add, ihz ez, ihw ew]
    | smul c z hz ih =>
      intro hcz
      have ez : z ∈ modified D Coefficients.q pi := by
        change z ∈ (modified D Coefficients.q pi).toSubmodule
        rw [← triangularSpan_eq_modified]; exact hz
      change f (omegaModified D (c • ⟨z, ez⟩)) = g (omegaModified D (c • ⟨z, ez⟩))
      simp only [map_smulₛₗ, ih ez]
  have he := aux _ hx (omegaModified D x).property
  change f (omegaModified D (omegaModified D x)) = g (omegaModified D (omegaModified D x)) at he
  simpa only [omegaModified_omegaModified] using he

private theorem forms_eq_of_negative_words
    (B C : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi))
    (hB : ∀ u x y, B (u * x) y = B x (rhoModified D Coefficients.q pi pi_sq u * y))
    (hC : ∀ u x y, C (u * x) y = C x (rhoModified D Coefficients.q pi pi_sq u * y))
    (hn : ∀ a b μ ν, B (wordModified D false a μ) (wordModified D false b ν) =
      C (wordModified D false a μ) (wordModified D false b ν)) : B = C := by
  have ho (η : X) : B (weightOne D η) = C (weightOne D η) := by
    apply linear_ext_EF D
    intro a b μ ν
    obtain ⟨c, hc⟩ := rho_halfWord_unit D Coefficients.q pi pi_sq true a μ
    have hr : rhoModified D Coefficients.q pi pi_sq (wordModified D true a μ) =
        (c : Coefficients.Ring) • wordModified D false a.reverse
          (μ + halfWeight D true (wordWeight a)) := Subtype.ext hc
    have he (F : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi))
        (hF : ∀ u x y, F (u * x) y = F x (rhoModified D Coefficients.q pi pi_sq u * y)) :
        F (weightOne D η) (wordModified D true a μ * wordModified D false b ν) =
        F ((rhoModified D Coefficients.q pi pi_sq (wordModified D true a μ)) * weightOne D η)
          (wordModified D false b ν) := by
      rw [hF, rhoModified_rhoModified]
    rw [he B hB, he C hC, hr, smul_mul_assoc]
    have hm : wordModified D false a.reverse (μ + halfWeight D true (wordWeight a)) * weightOne D η =
        if μ + halfWeight D true (wordWeight a) = η then
          wordModified D false a.reverse (μ + halfWeight D true (wordWeight a)) else 0 := by
      apply Subtype.ext
      simpa only [wordModified, weightOne, NonUnitalSubalgebra.coe_mul, Subtype.coe_mk,
        apply_ite, NonUnitalSubalgebra.coe_zero] using
        mul_one_of_mem_block D Coefficients.q pi
          (halfWord_mem_block D Coefficients.q pi false a.reverse
            (μ + halfWeight D true (wordWeight a))) η
    rw [hm]
    split_ifs <;> simp [hn]
  ext x y
  obtain ⟨s, _, hs⟩ := exists_localUnit D Coefficients.q pi x.property
  have hx : x * ∑ η ∈ s, weightOne D η = x := by
    apply Subtype.ext
    change (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) *
      (modified D Coefficients.q pi).toSubmodule.subtype (∑ η ∈ s, weightOne D η) = _
    simpa only [map_sum, Submodule.subtype_apply, weightOne] using hs
  calc
    B x y = B (x * ∑ η ∈ s, weightOne D η) y := by rw [hx]
    _ = B (∑ η ∈ s, weightOne D η) (rhoModified D Coefficients.q pi pi_sq x * y) := hB _ _ _
    _ = C (∑ η ∈ s, weightOne D η) (rhoModified D Coefficients.q pi pi_sq x * y) := by
      simp only [map_sum, LinearMap.sum_apply, ho]
    _ = C (x * ∑ η ∈ s, weightOne D η) y := (hC _ _ _).symm
    _ = C x y := by rw [hx]

variable [Finite I]

/-- Endpoint orthogonality, adjointness for all actual modified elements, and
normalization on all negative-half pairs uniquely determine the constructed form.
No homogeneity or independence of the simple roots is assumed. -/
theorem modifiedForm_unique (hD : D.toSuperCartanDatum.BarConsistent)
    (B : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi))
    (horth : ∀ μ ν μ' ν' (x y : modified D Coefficients.q pi),
      (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ ν →
      (y : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ' ν' →
      μ ≠ μ' ∨ ν ≠ ν' → B x y = 0)
    (hadj : ∀ u x y, B (u * x) y = B x (rhoModified D Coefficients.q pi pi_sq u * y))
    (hnegative : ∀ μ (x y : D.serreF Coefficients.q pi),
      B (negativeHalf D Coefficients.q pi μ x) (negativeHalf D Coefficients.q pi μ y) =
        D.serreForm Coefficients.q pi pi_sq x y) : B = modifiedForm D hD := by
  apply forms_eq_of_negative_words D B (modifiedForm D hD) hadj (modifiedForm_adjoint D hD)
  intro a b μ ν
  by_cases h : μ = ν
  · subst ν
    rw [wordModified_negative, wordModified_negative, hnegative, modifiedForm_negativeHalf]
  · rw [horth _ _ _ _ _ _ (halfWord_mem_block D Coefficients.q pi false a μ)
        (halfWord_mem_block D Coefficients.q pi false b ν) (Or.inr h),
      modifiedForm_orthogonal D hD _ _ _ _ _ _ (halfWord_mem_block D Coefficients.q pi false a μ)
        (halfWord_mem_block D Coefficients.q pi false b ν) (Or.inr h)]

/-- Symmetry follows by applying uniqueness to the transposed form. -/
theorem modifiedForm_comm (hD : D.toSuperCartanDatum.BarConsistent)
    (x y : modified D Coefficients.q pi) : modifiedForm D hD x y = modifiedForm D hD y x := by
  have he : (modifiedForm D hD).flip = modifiedForm D hD := by
    apply modifiedForm_unique D hD
    · intro μ ν μ' ν' a b ha hb hn
      exact modifiedForm_orthogonal D hD μ' ν' μ ν b a hb ha
        (hn.imp Ne.symm Ne.symm)
    · intro u a b
      change modifiedForm D hD b (u * a) =
        modifiedForm D hD (rhoModified D Coefficients.q pi pi_sq u * b) a
      rw [modifiedForm_adjoint, rhoModified_rhoModified]
    · intro μ a b
      change modifiedForm D hD (negativeHalf D Coefficients.q pi μ b)
        (negativeHalf D Coefficients.q pi μ a) = _
      rw [modifiedForm_negativeHalf, SuperCartanDatum.serreForm_comm]
  exact (LinearMap.congr_fun (LinearMap.congr_fun he x) y).symm

end OddMath.CoveringQuantum.UDot.GenericTensor
