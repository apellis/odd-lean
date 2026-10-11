import OddMath.CoveringQuantum.UDot.PositiveFormUniqueness
import OddMath.CoveringQuantum.PreF.Reversal

/-!
# The sesquilinear form on the modified covering algebra

Pulling the positive-normalized bilinear form back by the original `psi` in its
first argument gives the form of Brundan–Ellis, Theorem 10.1, over the generic
covering ring for finite bar-consistent data. The original `star` and `shriek`
are retained. All-half uniqueness and identities (4) and (5) require no root
separation; only the shorter same-length-word characterization assumes the
explicit root-sum length separation hypothesis. Nondegeneracy and existence
without bar consistency are not asserted.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients PreF
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

@[simp] theorem coe_psiModified (x : modified D Coefficients.q pi) :
    (psiModified D x : CoveringUDot Coefficients.Ring D Coefficients.q pi) =
      psi D Coefficients.q pi bar barData x := rfl

@[simp] theorem psiModified_psiModified (x : modified D Coefficients.q pi) :
    psiModified D (psiModified D x) = x :=
  Subtype.ext (psi_psi barData bar_bar x.val)

theorem psiModified_mul (x y : modified D Coefficients.q pi) :
    psiModified D (x * y) = psiModified D x * psiModified D y :=
  Subtype.ext (map_mul (psi D Coefficients.q pi bar barData) x.val y.val)

/-- The restriction of the original shriek, not an adjoint defined from the form. -/
def shriekModified : modified D Coefficients.q pi →ₛₗ[bar] modified D Coefficients.q pi :=
  (psiModified D).comp (rhoModified D Coefficients.q pi pi_sq)

@[simp] theorem coe_shriekModified (x : modified D Coefficients.q pi) :
    (shriekModified D x : CoveringUDot Coefficients.Ring D Coefficients.q pi) =
      (shriek D Coefficients.q pi bar barData x).unop := rfl

@[simp] theorem starModified_shriekModified (x : modified D Coefficients.q pi) :
    starModified D (shriekModified D x) = x := by
  change rhoModified D Coefficients.q pi pi_sq
    (psiModified D (psiModified D (rhoModified D Coefficients.q pi pi_sq x))) = x
  rw [psiModified_psiModified, rhoModified_rhoModified]

@[simp] theorem shriekModified_starModified (x : modified D Coefficients.q pi) :
    shriekModified D (starModified D x) = x := by
  change psiModified D (rhoModified D Coefficients.q pi pi_sq
    (rhoModified D Coefficients.q pi pi_sq (psiModified D x))) = x
  rw [rhoModified_rhoModified, psiModified_psiModified]

private theorem psi_positive_halfWord (a : List I) (μ : X) :
    psi D Coefficients.q pi bar barData (halfWord D Coefficients.q pi true a μ) =
      halfWord D Coefficients.q pi true a μ := by
  induction a with
  | nil => simp [halfWord]
  | cons i a ih => simp [halfWord, halfGen, ih]

@[simp] theorem psiModified_positive_monomial (a : List I) (μ : X) :
    psiModified D (positiveHalf D Coefficients.q pi μ
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a))) =
      positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a)) := by
  apply Subtype.ext
  change psi D Coefficients.q pi bar barData (halfMap D Coefficients.q pi true μ _) = _
  rw [halfMap_monomial, psi_positive_halfWord]
  exact (halfMap_monomial D Coefficients.q pi true a μ).symm

variable [Finite I] (hD : D.toSuperCartanDatum.BarConsistent)

/-- Scalar conjugation on the positive half agrees with the original psi. -/
theorem psiModified_positiveHalf (μ : X) (x : D.serreF Coefficients.q pi) :
    psiModified D (positiveHalf D Coefficients.q pi μ x) =
      positiveHalf D Coefficients.q pi μ (GenericVerma.halfBar D hD x) := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  induction x using induction_monomial with
  | word w => rw [psiModified_positive_monomial, GenericVerma.halfBar_monomial]
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => simp only [map_smul, map_smulₛₗ, hx]

/-- Antilinear in the first argument and linear in the second, over the generic ring. -/
def sesquilinearForm : modified D Coefficients.q pi →ₛₗ[bar]
    (modified D Coefficients.q pi →ₗ[Coefficients.Ring] Coefficients.Ring) :=
  LinearMap.comp (positiveModifiedForm D hD) (psiModified D)

theorem sesquilinearForm_apply (x y : modified D Coefficients.q pi) :
    sesquilinearForm D hD x y = positiveModifiedForm D hD (psiModified D x) y := rfl

/-- The original star is the left adjoint for every modified element. -/
theorem sesquilinearForm_adjoint (u x y : modified D Coefficients.q pi) :
    sesquilinearForm D hD (u * x) y =
      sesquilinearForm D hD x (starModified D u * y) := by
  simp only [sesquilinearForm_apply, psiModified_mul, positiveModifiedForm_adjoint]
  rfl

/-- Both endpoints are orthogonal. -/
theorem sesquilinearForm_orthogonal (μ ν μ' ν' : X) (x y : modified D Coefficients.q pi)
    (hx : (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ ν)
    (hy : (y : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ' ν')
    (hne : μ ≠ μ' ∨ ν ≠ ν') : sesquilinearForm D hD x y = 0 :=
  positiveModifiedForm_orthogonal D hD μ ν μ' ν' (psiModified D x) y
    (psi_mem_block D Coefficients.q pi barData hx) hy hne

/-- Normalization on the entire positive half, including arbitrary coefficients. -/
theorem sesquilinearForm_positiveHalf (μ : X) (x y : D.serreF Coefficients.q pi) :
    sesquilinearForm D hD (positiveHalf D Coefficients.q pi μ x)
      (positiveHalf D Coefficients.q pi μ y) =
        D.serreForm Coefficients.q pi pi_sq (GenericVerma.halfBar D hD x) y := by
  rw [sesquilinearForm_apply, psiModified_positiveHalf D hD, positiveModifiedForm_positiveHalf]

/-- The reversed positive-word normalization in Theorem 10.1(3). -/
theorem sesquilinearForm_reversed_words (μ : X) (a b : List I) :
    sesquilinearForm D hD
      (positiveHalf D Coefficients.q pi μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a.reverse)))
      (positiveHalf D Coefficients.q pi μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b.reverse))) =
        D.serreForm Coefficients.q pi pi_sq
          (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a))
          (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b)) := by
  rw [sesquilinearForm_positiveHalf, GenericVerma.halfBar_monomial,
    SuperCartanDatum.serreForm_monomial_reverse]

/-- The psi-twisted symmetry of Theorem 10.1(4). -/
theorem sesquilinearForm_psi_comm (x y : modified D Coefficients.q pi) :
    sesquilinearForm D hD x y = sesquilinearForm D hD (psiModified D y) (psiModified D x) := by
  rw [sesquilinearForm_apply, sesquilinearForm_apply, psiModified_psiModified,
    positiveModifiedForm_comm]

/-- The original shriek is the right adjoint, as in Theorem 10.1(5). -/
theorem sesquilinearForm_shriek_adjoint (x y z : modified D Coefficients.q pi) :
    sesquilinearForm D hD x (y * z) =
      sesquilinearForm D hD (shriekModified D y * x) z := by
  simp only [sesquilinearForm_apply, psiModified_mul]
  change positiveModifiedForm D hD (psiModified D x) (y * z) =
    positiveModifiedForm D hD (psiModified D (psiModified D (rhoModified D Coefficients.q pi pi_sq y)) * psiModified D x) z
  rw [psiModified_psiModified, positiveModifiedForm_adjoint, rhoModified_rhoModified]

private def bilinearPullback
    (S : modified D Coefficients.q pi →ₛₗ[bar]
      (modified D Coefficients.q pi →ₗ[Coefficients.Ring] Coefficients.Ring)) :
    LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi) where
  toFun x := S (psiModified D x)
  map_add' x y := by simp only [map_add]
  map_smul' c x := by simp only [map_smulₛₗ, bar_bar, RingHom.id_apply]

omit [Finite I] in
private theorem bilinearPullback_orthogonal
    (S : modified D Coefficients.q pi →ₛₗ[bar]
      (modified D Coefficients.q pi →ₗ[Coefficients.Ring] Coefficients.Ring))
    (horth : ∀ μ ν μ' ν' (x y : modified D Coefficients.q pi),
      (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ ν →
      (y : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ' ν' →
      μ ≠ μ' ∨ ν ≠ ν' → S x y = 0)
    (μ ν μ' ν' : X) (x y : modified D Coefficients.q pi)
    (hx : (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ ν)
    (hy : (y : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ' ν')
    (hne : μ ≠ μ' ∨ ν ≠ ν') : bilinearPullback D S x y = 0 :=
  horth μ ν μ' ν' (psiModified D x) y (psi_mem_block D Coefficients.q pi barData hx) hy hne

omit [Finite I] in
private theorem bilinearPullback_adjoint
    (S : modified D Coefficients.q pi →ₛₗ[bar]
      (modified D Coefficients.q pi →ₗ[Coefficients.Ring] Coefficients.Ring))
    (hadj : ∀ u x y, S (u * x) y = S x (starModified D u * y))
    (u x y : modified D Coefficients.q pi) :
    bilinearPullback D S (u * x) y =
      bilinearPullback D S x (rhoModified D Coefficients.q pi pi_sq u * y) := by
  change S (psiModified D (u * x)) y = S (psiModified D x) _
  rw [psiModified_mul, hadj]
  change S (psiModified D x)
    (rhoModified D Coefficients.q pi pi_sq (psiModified D (psiModified D u)) * y) = _
  rw [psiModified_psiModified]

private theorem eq_of_bilinearPullback_eq
    (S : modified D Coefficients.q pi →ₛₗ[bar]
      (modified D Coefficients.q pi →ₗ[Coefficients.Ring] Coefficients.Ring))
    (he : bilinearPullback D S = positiveModifiedForm D hD) :
    S = sesquilinearForm D hD := by
  ext x y
  have h := LinearMap.congr_fun (LinearMap.congr_fun he (psiModified D x)) y
  change S (psiModified D (psiModified D x)) y = positiveModifiedForm D hD (psiModified D x) y at h
  simpa only [psiModified_psiModified, sesquilinearForm_apply] using h

/-- Endpoint orthogonality, original-star adjointness, and all-half normalization
uniquely characterize the form, with no root separation hypothesis. -/
theorem sesquilinearForm_unique
    (S : modified D Coefficients.q pi →ₛₗ[bar]
      (modified D Coefficients.q pi →ₗ[Coefficients.Ring] Coefficients.Ring))
    (horth : ∀ μ ν μ' ν' (x y : modified D Coefficients.q pi),
      (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ ν →
      (y : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ' ν' →
      μ ≠ μ' ∨ ν ≠ ν' → S x y = 0)
    (hadj : ∀ u x y, S (u * x) y = S x (starModified D u * y))
    (hpositive : ∀ μ (x y : D.serreF Coefficients.q pi),
      S (positiveHalf D Coefficients.q pi μ x) (positiveHalf D Coefficients.q pi μ y) =
        D.serreForm Coefficients.q pi pi_sq (GenericVerma.halfBar D hD x) y) :
    S = sesquilinearForm D hD := by
  apply eq_of_bilinearPullback_eq D hD S
  apply positiveModifiedForm_unique D hD (bilinearPullback D S)
    (bilinearPullback_orthogonal D S horth) (bilinearPullback_adjoint D S hadj)
  intro μ x y
  change S (psiModified D (positiveHalf D Coefficients.q pi μ x)) _ = _
  rw [psiModified_positiveHalf D hD, hpositive, GenericVerma.halfBar_halfBar]

/-- The three-axiom characterization using normalization on the entire positive half. -/
theorem sesquilinearForm_eq_iff
    (S : modified D Coefficients.q pi →ₛₗ[bar]
      (modified D Coefficients.q pi →ₗ[Coefficients.Ring] Coefficients.Ring)) :
    S = sesquilinearForm D hD ↔
      (∀ μ ν μ' ν' (x y : modified D Coefficients.q pi),
        (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ ν →
        (y : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ' ν' →
        μ ≠ μ' ∨ ν ≠ ν' → S x y = 0) ∧
      (∀ u x y, S (u * x) y = S x (starModified D u * y)) ∧
      (∀ μ (x y : D.serreF Coefficients.q pi),
        S (positiveHalf D Coefficients.q pi μ x) (positiveHalf D Coefficients.q pi μ y) =
          D.serreForm Coefficients.q pi pi_sq (GenericVerma.halfBar D hD x) y) := by
  constructor
  · rintro rfl
    exact ⟨sesquilinearForm_orthogonal D hD, sesquilinearForm_adjoint D hD,
      sesquilinearForm_positiveHalf D hD⟩
  · rintro ⟨horth, hadj, hpositive⟩
    exact sesquilinearForm_unique D hD S horth hadj hpositive

/-- Same-length reversed positive words suffice under the explicit local
root-sum length separation assumption. This assumption is not needed for the
construction, all-half characterization, or the two adjoint identities. -/
theorem sesquilinearForm_unique_of_same_length
    (hlength : ∀ a b : List I, (a.map D.α).sum = (b.map D.α).sum → a.length = b.length)
    (S : modified D Coefficients.q pi →ₛₗ[bar]
      (modified D Coefficients.q pi →ₗ[Coefficients.Ring] Coefficients.Ring))
    (horth : ∀ μ ν μ' ν' (x y : modified D Coefficients.q pi),
      (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ ν →
      (y : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ' ν' →
      μ ≠ μ' ∨ ν ≠ ν' → S x y = 0)
    (hadj : ∀ u x y, S (u * x) y = S x (starModified D u * y))
    (hwords : ∀ μ (a b : List I), a.length = b.length →
      S (positiveHalf D Coefficients.q pi μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a.reverse)))
        (positiveHalf D Coefficients.q pi μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b.reverse))) =
        D.serreForm Coefficients.q pi pi_sq
          (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a))
          (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b))) :
    S = sesquilinearForm D hD := by
  apply eq_of_bilinearPullback_eq D hD S
  apply positiveModifiedForm_unique_of_same_length D hD hlength (bilinearPullback D S)
    (bilinearPullback_orthogonal D S horth) (bilinearPullback_adjoint D S hadj)
  intro μ a b hab
  change S (psiModified D (positiveHalf D Coefficients.q pi μ _)) _ = _
  rw [psiModified_positive_monomial]
  have h := hwords μ a.reverse b.reverse (by simpa only [List.length_reverse] using hab)
  simpa only [List.reverse_reverse, SuperCartanDatum.serreForm_monomial_reverse] using h

/-- Theorem 10.1's shorter three-axiom characterization, with reversed words
in normalization and a theorem-local length separation hypothesis. -/
theorem sesquilinearForm_eq_iff_of_length_separation
    (hlength : ∀ a b : List I, (a.map D.α).sum = (b.map D.α).sum → a.length = b.length)
    (S : modified D Coefficients.q pi →ₛₗ[bar]
      (modified D Coefficients.q pi →ₗ[Coefficients.Ring] Coefficients.Ring)) :
    S = sesquilinearForm D hD ↔
      (∀ μ ν μ' ν' (x y : modified D Coefficients.q pi),
        (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ ν →
        (y : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ' ν' →
        μ ≠ μ' ∨ ν ≠ ν' → S x y = 0) ∧
      (∀ u x y, S (u * x) y = S x (starModified D u * y)) ∧
      (∀ μ (a b : List I), a.length = b.length →
        S (positiveHalf D Coefficients.q pi μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a.reverse)))
          (positiveHalf D Coefficients.q pi μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b.reverse))) =
          D.serreForm Coefficients.q pi pi_sq
            (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a))
            (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b))) := by
  constructor
  · rintro rfl
    refine ⟨sesquilinearForm_orthogonal D hD, sesquilinearForm_adjoint D hD, ?_⟩
    intro μ a b _
    exact sesquilinearForm_reversed_words D hD μ a b
  · rintro ⟨horth, hadj, hwords⟩
    exact sesquilinearForm_unique_of_same_length D hD hlength S horth hadj hwords

end OddMath.CoveringQuantum.UDot.GenericTensor
