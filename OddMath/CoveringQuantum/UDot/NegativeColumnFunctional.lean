import OddMath.CoveringQuantum.UDot.AdjointColumn

/-!
# The all-negative-half-pairs column functional

The first step of Lusztig, Introduction to Quantum Groups, Theorem 26.1.2,
and Clark, arXiv:1312.4855v2, Theorem 5.2, is a functional normalized on
adjoint-negative products. We construct such a functional on the actual
modified presentation, using the existing triangular coordinates.

Our triangular order is negative-positive. The actual semilinear omega
transports it to the required order. Both the adjoint and the half form are
conjugated before transport, so no identification of q with its inverse is
silently made. The final normalization uses exactly `UDot.rho` and
`SuperCartanDatum.serreForm` from this library.

The generic covering coefficient ring, finiteness and bar consistency are
used; no independence of simple roots is imposed. This is the column
functional, not a nondegeneracy or BE2 sesquilinear-form theorem.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients TensorProduct PreF
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent)

omit [Finite I] in
/-- The actual scalar-bar symmetry on negative half words. -/
theorem omega_negative_halfWord (μ : X) (w : List I) :
    omega D Coefficients.q pi bar barData (halfWord D Coefficients.q pi false w μ) =
      halfWord D Coefficients.q pi true w (-μ) := by
  have h := GenericVerma.omega_halfWord D (-μ) w
  rw [neg_neg] at h
  rw [← h, omega_omega barData bar_bar]

omit [Finite I] in
theorem omega_mem_modified {x : CoveringUDot Coefficients.Ring D Coefficients.q pi}
    (hx : x ∈ modified D Coefficients.q pi) :
    omega D Coefficients.q pi bar barData x ∈ modified D Coefficients.q pi := by
  refine Submodule.iSup_induction (fun b : X × X ↦ block D Coefficients.q pi b.1 b.2)
    (motive := fun x ↦ omega D Coefficients.q pi bar barData x ∈ modified D Coefficients.q pi) hx ?_ ?_ ?_
  · intro b x hx
    apply block_le_modified D Coefficients.q pi (-b.1) (-b.2)
    constructor
    · simpa only [map_mul, omega_one] using congrArg (omega D Coefficients.q pi bar barData) hx.1
    · simpa only [map_mul, omega_one] using congrArg (omega D Coefficients.q pi bar barData) hx.2
  · simp only [map_zero]; exact zero_mem _
  · intro x y hx hy
    simpa only [map_add] using add_mem hx hy

/-- Restriction of omega is genuinely scalar-bar-semilinear. -/
def omegaModified : modified D Coefficients.q pi →ₛₗ[bar] modified D Coefficients.q pi where
  toFun x := ⟨omega D Coefficients.q pi bar barData x, omega_mem_modified D x.property⟩
  map_add' _ _ := Subtype.ext (by simp)
  map_smul' c x := Subtype.ext (by
    simpa only [NonUnitalSubalgebra.coe_smul] using omega_smul (D := D) barData c x.val)

omit [Finite I] in
@[simp] theorem coe_omegaModified (x : modified D Coefficients.q pi) :
    (omegaModified D x : CoveringUDot Coefficients.Ring D Coefficients.q pi) =
      omega D Coefficients.q pi bar barData x := rfl

omit [Finite I] in
@[simp] theorem omegaModified_omegaModified (x : modified D Coefficients.q pi) :
    omegaModified D (omegaModified D x) = x := Subtype.ext (omega_omega barData bar_bar x.val)

/-- Conjugation by two semilinear maps gives a linear adjoint, not rho itself. -/
def conjugateRho : modified D Coefficients.q pi →ₗ[Coefficients.Ring] modified D Coefficients.q pi where
  toFun x := omegaModified D (rhoModified D Coefficients.q pi pi_sq (omegaModified D x))
  map_add' _ _ := by simp
  map_smul' c x := by simp only [map_smul, map_smulₛₗ, bar_bar, RingHom.id_apply]

omit [Finite I] in
@[simp] theorem conjugateRho_conjugateRho (x : modified D Coefficients.q pi) :
    conjugateRho D (conjugateRho D x) = x := by
  simp [conjugateRho]

omit [Finite I] in
theorem omegaModified_positive_monomial (μ : X) (w : List I) :
    omegaModified D (positiveHalf D Coefficients.q pi μ
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) =
    negativeHalf D Coefficients.q pi (-μ)
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) := by
  apply Subtype.ext
  change omega D Coefficients.q pi bar barData (halfMap D Coefficients.q pi true μ _) =
    halfMap D Coefficients.q pi false (-μ) _
  rw [halfMap_monomial, halfMap_monomial, GenericVerma.omega_halfWord]

omit [Finite I] in
/-- The conjugated adjoint has the actual unit word formula needed by the contraction. -/
theorem conjugateRho_word (μ : X) (w : List I) :
    ∃ c : Coefficients.Ringˣ,
      (conjugateRho D (positiveHalf D Coefficients.q pi μ
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) :
        CoveringUDot Coefficients.Ring D Coefficients.q pi) =
      (c : Coefficients.Ring) • halfWord D Coefficients.q pi false w.reverse
        (μ + halfWeight D true (wordWeight w)) := by
  obtain ⟨c, hc⟩ := rho_halfWord_unit D Coefficients.q pi pi_sq false w (-μ)
  refine ⟨Units.map bar.toMonoidHom c, ?_⟩
  change omega D Coefficients.q pi bar barData
    ((rho D Coefficients.q pi pi_sq (omegaModified D (positiveHalf D Coefficients.q pi μ _))).unop) = _
  rw [omegaModified_positive_monomial]
  change omega D Coefficients.q pi bar barData
    ((rho D Coefficients.q pi pi_sq (halfMap D Coefficients.q pi false (-μ) _)).unop) = _
  rw [halfMap_monomial, hc, omega_smul, Bool.not_false, GenericVerma.omega_halfWord]
  have hw : halfWeight D false (wordWeight w) = -halfWeight D true (wordWeight w) := by
    simp [halfWeight, halfRoot, Finsupp.sum, Finset.sum_neg_distrib]
  simp [hw, add_comm]

/-- The half form with both its arguments and its scalar value conjugated.
The double scalar conjugation is essential in transporting normalization. -/
def conjugateHalfForm : LinearMap.BilinForm Coefficients.Ring (D.serreF Coefficients.q pi) where
  toFun x :=
    { toFun := fun y ↦ bar (D.serreForm Coefficients.q pi pi_sq
        (GenericVerma.halfBar D hD x) (GenericVerma.halfBar D hD y))
      map_add' := by intro y z; simp
      map_smul' := by intro c y; simp only [map_smulₛₗ, smul_eq_mul, map_mul, bar_bar, RingHom.id_apply] }
  map_add' := by intro x z; ext y; simp
  map_smul' := by
    intro c x
    ext y
    change bar (D.serreForm Coefficients.q pi pi_sq
      (GenericVerma.halfBar D hD (c • x)) (GenericVerma.halfBar D hD y)) =
      c • bar (D.serreForm Coefficients.q pi pi_sq
        (GenericVerma.halfBar D hD x) (GenericVerma.halfBar D hD y))
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, bar_bar, RingHom.id_apply]

@[simp] theorem conjugateHalfForm_apply (x y : D.serreF Coefficients.q pi) :
    conjugateHalfForm D hD x y = bar (D.serreForm Coefficients.q pi pi_sq
      (GenericVerma.halfBar D hD x) (GenericVerma.halfBar D hD y)) := rfl

theorem conjugateHalfForm_orthogonal (a b : List I)
    (hab : halfWeight D true (wordWeight a) ≠ halfWeight D true (wordWeight b)) :
    conjugateHalfForm D hD (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a))
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b)) = 0 := by
  rw [conjugateHalfForm_apply, GenericVerma.halfBar_monomial, GenericVerma.halfBar_monomial,
    SuperCartanDatum.serreForm_toSerreF]
  have h : D.form Coefficients.q pi (monomial Coefficients.Ring a) (monomial Coefficients.Ring b) = 0 :=
    PreF.form_eq_zero_of_ne _ _ (fun h ↦ hab (congrArg (halfWeight D true) h))
      (monomial_mem_weightSpace a) (monomial_mem_weightSpace b)
  rw [h, map_zero]

/-- Lusztig's column functional in the negative-half convention, obtained by
actual omega transport of the adjoint-corrected triangular contraction. -/
def negativeColumnFunctional (μ : X) :
    CoveringUDot Coefficients.Ring D Coefficients.q pi →ₗ[Coefficients.Ring] Coefficients.Ring where
  toFun x := bar (adjointColumn D hD (conjugateRho D) (conjugateHalfForm D hD) (-μ)
    (omega D Coefficients.q pi bar barData x))
  map_add' _ _ := by simp
  map_smul' c x := by simp only [omega_smul, map_smul, smul_eq_mul, map_mul, bar_bar, RingHom.id_apply]

/-- Every negative word pair, without a length or root-independence restriction. -/
theorem negativeColumnFunctional_rho_halfWord (μ : X) (a b : List I) :
    negativeColumnFunctional D hD μ
      ((rho D Coefficients.q pi pi_sq (halfWord D Coefficients.q pi false a μ)).unop *
        halfWord D Coefficients.q pi false b μ) =
      D.form Coefficients.q pi (monomial Coefficients.Ring a) (monomial Coefficients.Ring b) := by
  have ha : omega D Coefficients.q pi bar barData
      ((rho D Coefficients.q pi pi_sq (halfWord D Coefficients.q pi false a μ)).unop) =
      (conjugateRho D (positiveHalf D Coefficients.q pi (-μ)
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a))) :
          CoveringUDot Coefficients.Ring D Coefficients.q pi) := by
    change _ = omega D Coefficients.q pi bar barData
      ((rho D Coefficients.q pi pi_sq
        (omegaModified D (positiveHalf D Coefficients.q pi (-μ) _))).unop)
    rw [omegaModified_positive_monomial, neg_neg]
    change _ = omega D Coefficients.q pi bar barData
      ((rho D Coefficients.q pi pi_sq (halfMap D Coefficients.q pi false μ _)).unop)
    rw [halfMap_monomial]
  change bar (adjointColumn D hD (conjugateRho D) (conjugateHalfForm D hD) (-μ)
    (omega D Coefficients.q pi bar barData _)) = _
  rw [map_mul, ha, omega_negative_halfWord,
    adjointColumn_halfWord D hD (conjugateRho D) (conjugateHalfForm D hD)
      (conjugateRho_conjugateRho D) (conjugateRho_word D) (conjugateHalfForm_orthogonal D hD),
    conjugateHalfForm_apply, GenericVerma.halfBar_monomial, GenericVerma.halfBar_monomial,
    bar_bar, SuperCartanDatum.serreForm_toSerreF]

/-- The all-half-pairs normalization on the actual quotient, including nonhomogeneous inputs. -/
theorem negativeColumnFunctional_rho_halfMap (μ : X) (x y : D.serreF Coefficients.q pi) :
    negativeColumnFunctional D hD μ
      ((rho D Coefficients.q pi pi_sq (halfMap D Coefficients.q pi false μ x)).unop *
        halfMap D Coefficients.q pi false μ y) = D.serreForm Coefficients.q pi pi_sq x y := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  obtain ⟨y, rfl⟩ := D.toSerreF_surjective Coefficients.q pi y
  induction x using induction_monomial with
  | zero => simp
  | add x z hx hz => simp only [map_add, MulOpposite.unop_add, add_mul, hx, hz, LinearMap.add_apply]
  | smul c x hx => simp only [map_smul, MulOpposite.unop_smul, smul_mul_assoc, hx, LinearMap.smul_apply]
  | word a =>
    induction y using induction_monomial with
    | zero => simp
    | add y z hy hz => simp only [map_add, mul_add, hy, hz]
    | smul c y hy => simp only [map_smul, mul_smul_comm, hy]
    | word b => rw [halfMap_monomial, halfMap_monomial, negativeColumnFunctional_rho_halfWord,
        SuperCartanDatum.serreForm_toSerreF]

end OddMath.CoveringQuantum.UDot.GenericTensor
