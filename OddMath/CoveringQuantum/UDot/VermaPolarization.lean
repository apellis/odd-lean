import OddMath.CoveringQuantum.UDot.GlobalTriangular
import OddMath.CoveringQuantum.UDot.RhoHalfWords

/-!
# The actual generic Verma polarization

Construct the form on the existing Serre-half Verma module by a vacuum matrix
coefficient, and prove symmetry, normalization and full rho-contravariance.
This is the Verma precursor in Clark IV §5.2, Proposition 5.8's tau1-prime convention;
no integrable-quotient descent or nondegeneracy is claimed.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma
open PreF Coefficients
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent) (Λ : X)

/-- The actual constant coefficient on the Serre half. -/
def constant : D.serreF Coefficients.q pi →ₗ[Coefficients.Ring] Coefficients.Ring :=
  D.serreForm Coefficients.q pi pi_sq 1

omit [DecidableEq X] [Finite I] in
@[simp] theorem constant_mk (x : PreF Coefficients.Ring I) :
    constant D (D.toSerreF Coefficients.q pi x) = counit x := by
  change D.serreForm Coefficients.q pi pi_sq 1 _ = _
  rw [← map_one (D.toSerreF Coefficients.q pi), SuperCartanDatum.serreForm_toSerreF]
  exact form_one_left _ _ _

omit [DecidableEq X] [Finite I] in
@[simp] theorem constant_one : constant D 1 = 1 :=
  D.serreForm_one_one Coefficients.q pi pi_sq

omit [DecidableEq X] [Finite I] in
@[simp] theorem constant_create (i : I) (x : D.serreF Coefficients.q pi) :
    constant D (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i) * x) = 0 := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  rw [← map_mul, constant_mk]
  simp

@[simp] theorem weightProject_one (μ : X) :
    weightProject D hD Λ μ 1 = if μ = Λ then 1 else 0 := by
  rw [← map_one (D.toSerreF Coefficients.q pi), weightProject_mk]
  change D.toSerreF Coefficients.q pi
    (weightProjectFree D Λ μ (monomial Coefficients.Ring [])) = _
  simp only [weightProjectFree_monomial, wordWeight_nil, halfWeight_zero]
  by_cases h : μ = Λ
  · subst μ; simp
  · have hn : (0 : X) ≠ Λ - μ := by intro he; exact h (sub_eq_zero.mp he.symm).symm
    simp [h, hn]

/-- The highest-weight matrix coefficient on the actual envelope. -/
def vacuumCoefficient : CoveringUDot Coefficients.Ring D Coefficients.q pi →ₗ[Coefficients.Ring]
    Coefficients.Ring := (constant D).comp (vacuumEval D hD Λ)

@[simp] theorem vacuumCoefficient_one (μ : X) :
    vacuumCoefficient D hD Λ (one D Coefficients.q pi μ) = if μ = Λ then 1 else 0 := by
  change constant D (representation D hD Λ (one D Coefficients.q pi μ) 1) = _
  rw [representation_one, weightProject_one]
  split_ifs <;> simp

private theorem constant_negativeWord (i : I) (w : List I) (μ : X)
    (x : D.serreF Coefficients.q pi) :
    constant D (representation D hD Λ (halfWord D Coefficients.q pi false (i :: w) μ) x) = 0 := by
  simp only [halfWord, halfGen, Bool.false_eq_true, ite_false, map_mul, Module.End.mul_apply,
    representation_F, constant_create]

private theorem positiveWord_vacuum (i : I) (w : List I) (μ : X) :
    representation D hD Λ (halfWord D Coefficients.q pi true (i :: w) μ) 1 = 0 := by
  induction w generalizing i μ with
  | nil =>
    simp only [halfWord, wordWeight_nil, halfWeight_zero, add_zero, halfGen, ite_true,
      map_mul, Module.End.mul_apply, representation_E, representation_one, weightProject_one]
    split_ifs with h <;> simp [h]
  | cons j w ih =>
    rw [halfWord, map_mul, Module.End.mul_apply, ih, map_zero]

private theorem vacuumCoefficient_halfWords_zero (a b : List I) (ν μ : X)
    (h : a ≠ [] ∨ b ≠ []) :
    vacuumCoefficient D hD Λ
      (halfWord D Coefficients.q pi false a ν * halfWord D Coefficients.q pi true b μ) = 0 := by
  change constant D (representation D hD Λ (_ * _) 1) = 0
  rw [map_mul, Module.End.mul_apply]
  cases a with
  | cons i a => exact constant_negativeWord D hD Λ i a ν _
  | nil =>
    cases b with
    | nil => simp at h
    | cons j b => rw [positiveWord_vacuum, map_zero, map_zero]

/-- The vacuum coefficient is invariant under the actual adjoint involution.
The proof uses triangular spanning and the constructed Verma action. -/
theorem vacuumCoefficient_rho (z : modified D Coefficients.q pi) :
    vacuumCoefficient D hD Λ (rhoModified D Coefficients.q pi pi_sq z) =
      vacuumCoefficient D hD Λ z := by
  obtain ⟨z, hm⟩ := z
  have hz : z ∈ triangularSpan D Coefficients.q pi := by
    rw [triangularSpan_eq_modified]; exact hm
  change vacuumCoefficient D hD Λ (rho D Coefficients.q pi pi_sq z).unop =
    vacuumCoefficient D hD Λ z
  clear hm
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, b, ν, μ, rfl⟩ := hz
    by_cases h : a = [] ∧ b = []
    · obtain ⟨rfl, rfl⟩ := h
      simp only [halfWord, one_mul_one]
      split_ifs with h <;> simp_all
    · have hn : a ≠ [] ∨ b ≠ [] := not_and_or.mp h
      rw [vacuumCoefficient_halfWords_zero D hD Λ a b ν μ hn, rho_mul]
      obtain ⟨c, hc⟩ := rho_halfWord_unit D Coefficients.q pi pi_sq true b μ
      obtain ⟨d, hd⟩ := rho_halfWord_unit D Coefficients.q pi pi_sq false a ν
      rw [hc, hd, smul_mul_assoc, mul_smul_comm, map_smul, map_smul]
      simp only [Bool.not_true, Bool.not_false]
      rw [vacuumCoefficient_halfWords_zero D hD Λ b.reverse a.reverse _ _ (by
        simpa using hn.symm), smul_zero, smul_zero]
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, MulOpposite.unop_add, ihx, ihy]
  | smul c x hx ih => simp only [map_smul, MulOpposite.unop_smul, ih]

/-- A bilinear form on the existing Verma module, constructed by normal ordering. -/
def polarization : LinearMap.BilinForm Coefficients.Ring (D.serreF Coefficients.q pi) where
  toFun x := (constant D).comp
    (representation D hD Λ (rho D Coefficients.q pi pi_sq
      (halfMap D Coefficients.q pi false Λ x)).unop)
  map_add' x y := by ext z; simp
  map_smul' c x := by ext z; simp

@[simp] theorem polarization_apply (x y : D.serreF Coefficients.q pi) :
    polarization D hD Λ x y = constant D
      (representation D hD Λ (rho D Coefficients.q pi pi_sq
        (halfMap D Coefficients.q pi false Λ x)).unop y) := rfl

/-- Evaluation identifies the second argument with its actual negative-half lift. -/
theorem polarization_coefficient (x y : D.serreF Coefficients.q pi) :
    polarization D hD Λ x y = vacuumCoefficient D hD Λ
      (rhoModified D Coefficients.q pi pi_sq (negativeHalf D Coefficients.q pi Λ x) *
        negativeHalf D Coefficients.q pi Λ y) := by
  change _ = constant D (representation D hD Λ (_ * _) 1)
  rw [map_mul, Module.End.mul_apply]
  change _ = constant D (representation D hD Λ _ (vacuumEval D hD Λ _))
  change _ = constant D (representation D hD Λ _
    (vacuumEval D hD Λ (halfMap D Coefficients.q pi false Λ y)))
  rw [vacuumEval_halfMap]; rfl

/-- Symmetry follows from the proved vacuum-coefficient invariance. -/
theorem polarization_comm (x y : D.serreF Coefficients.q pi) :
    polarization D hD Λ x y = polarization D hD Λ y x := by
  rw [polarization_coefficient, polarization_coefficient]
  have h := vacuumCoefficient_rho D hD Λ
    (rhoModified D Coefficients.q pi pi_sq (negativeHalf D Coefficients.q pi Λ x) *
      negativeHalf D Coefficients.q pi Λ y)
  rw [rhoModified_mul, rhoModified_rhoModified] at h
  exact h.symm

/-- The constant coefficient is unchanged by projecting onto the highest weight. -/
theorem constant_weightProject (x : D.serreF Coefficients.q pi) :
    constant D (weightProject D hD Λ Λ x) = constant D x := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  rw [weightProject_mk, constant_mk, constant_mk]
  have h := weightProjectFree_form D (D.chi Coefficients.q pi) (D.norm Coefficients.q pi)
    Λ Λ 1 x
  have h1 : weightProjectFree D Λ Λ (1 : PreF Coefficients.Ring I) = 1 := by
    change weightProjectFree D Λ Λ (monomial Coefficients.Ring []) = _
    rw [weightProjectFree_monomial]
    simp
  rw [h1, form_one_left, form_one_left] at h
  exact h.symm

@[simp] theorem polarization_one_left (x : D.serreF Coefficients.q pi) :
    polarization D hD Λ 1 x = constant D x := by
  rw [polarization_apply, halfMap_one, rho_one, representation_one, constant_weightProject]

@[simp] theorem polarization_one_one : polarization D hD Λ 1 1 = 1 := by simp

private theorem polarization_vacuum_right (x : D.serreF Coefficients.q pi)
    (v : modified D Coefficients.q pi) :
    polarization D hD Λ x (vacuumEval D hD Λ v) = vacuumCoefficient D hD Λ
      ((rhoModified D Coefficients.q pi pi_sq (negativeHalf D Coefficients.q pi Λ x) * v :
        modified D Coefficients.q pi)) := by
  change _ = constant D (representation D hD Λ (_ * _) 1)
  rw [map_mul, Module.End.mul_apply]
  rfl

/-- The constructed form descends from the actual matrix coefficient in BOTH arguments.
This proves independence of arbitrary presentation lifts, not merely negative words. -/
theorem polarization_vacuum (v w : modified D Coefficients.q pi) :
    polarization D hD Λ (vacuumEval D hD Λ v) (vacuumEval D hD Λ w) =
      vacuumCoefficient D hD Λ ((rhoModified D Coefficients.q pi pi_sq v * w : modified D Coefficients.q pi)) := by
  rw [polarization_comm, polarization_vacuum_right, ← vacuumCoefficient_rho D hD Λ
    (rhoModified D Coefficients.q pi pi_sq
      (negativeHalf D Coefficients.q pi Λ (vacuumEval D hD Λ w)) * v),
    rhoModified_mul, rhoModified_rhoModified]
  change constant D (representation D hD Λ (_ * _) 1) =
    constant D (representation D hD Λ (_ * _) 1)
  rw [map_mul, Module.End.mul_apply, map_mul, Module.End.mul_apply]
  change constant D (representation D hD Λ _
    (vacuumEval D hD Λ (halfMap D Coefficients.q pi false Λ (vacuumEval D hD Λ w)))) = _
  rw [vacuumEval_halfMap]
  rfl

/-- Full contravariance for the original modified representation and its actual adjoint.
No polarization, Gram matrix, or nondegeneracy is a hypothesis. -/
theorem polarization_adjoint (u : modified D Coefficients.q pi)
    (x y : D.serreF Coefficients.q pi) :
    polarization D hD Λ (modifiedRepresentation D hD Λ u x) y =
      polarization D hD Λ x
        (modifiedRepresentation D hD Λ (rhoModified D Coefficients.q pi pi_sq u) y) := by
  let v := negativeHalf D Coefficients.q pi Λ x
  let w := negativeHalf D Coefficients.q pi Λ y
  have hv : vacuumEval D hD Λ v = x := vacuumEval_halfMap D hD Λ x
  have hw : vacuumEval D hD Λ w = y := vacuumEval_halfMap D hD Λ y
  have hm (a b : modified D Coefficients.q pi) : vacuumEval D hD Λ ((a * b : modified D Coefficients.q pi)) =
      modifiedRepresentation D hD Λ a (vacuumEval D hD Λ b) := by
    change representation D hD Λ (_ * _) 1 = _
    rw [map_mul, Module.End.mul_apply]; rfl
  rw [← hv, ← hw, ← hm, ← hm, polarization_vacuum, polarization_vacuum,
    rhoModified_mul, mul_assoc]

end OddMath.CoveringQuantum.UDot.GenericVerma
