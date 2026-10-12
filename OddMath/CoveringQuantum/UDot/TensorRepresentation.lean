import OddMath.CoveringQuantum.UDot.TensorMixed

/-!
# Complete original covering-quantum-group tensor action

Finite total-weight projectors and both root operators satisfy every relation of
CoveringUDot, including both Serre families and the same/different-colour mixed
relations at every weight. The original RingQuot lift constructs the unital
action and its restriction to the nonunital modified algebra. The negative half
also descends, with the prescribed corners, weight shifts and projected Serre
relations. No dominance, independent-root or finite-Cartan-type assumption is
added. This is not a proof of tensor polarization, local nilpotence or BE2 10.1.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma
open PreF Coefficients TensorProduct
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent) (Λ Μ : X)

local instance : AddCommGroup
    (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  TensorProduct.addCommGroup

theorem tensorProject_tmul_project (η ν : X)
    (x : IntegrableQuotient D hD Λ) (y : IntegrableQuotient D hD Μ) :
    tensorProject D hD Λ Μ η
      (x ⊗ₜ[Coefficients.Ring] integrableRepresentation D hD Μ (one D Coefficients.q pi ν) y) =
      integrableRepresentation D hD Λ (one D Coefficients.q pi (η + ν)) x ⊗ₜ[Coefficients.Ring]
        integrableRepresentation D hD Μ (one D Coefficients.q pi ν) y := by
  induction y using integrable_induction D hD Μ with
  | zero => simp
  | add y z hy hz => simp only [map_add, tmul_add, hy, hz]
  | smul c y hy => simp only [map_smul, tmul_smul, hy]
  | word w =>
    simp only [integrableRepresentation_toIntegrable, representation_one,
      weightProject_mk, weightProjectFree_monomial]
    split_ifs with h
    · have hv : ν = Μ - halfWeight D true (wordWeight w) := by rw [h]; abel
      rw [tensorProject_tmul_word, hv]
      congr 3
      abel
    · simp

theorem tensorProject_tmul_of_project (η ν : X)
    (x : IntegrableQuotient D hD Λ) (y : IntegrableQuotient D hD Μ)
    (hy : integrableRepresentation D hD Μ (one D Coefficients.q pi ν) y = y) :
    tensorProject D hD Λ Μ η (x ⊗ₜ[Coefficients.Ring] y) =
      integrableRepresentation D hD Λ (one D Coefficients.q pi (η + ν)) x ⊗ₜ[Coefficients.Ring] y := by
  simpa only [hy] using tensorProject_tmul_project D hD Λ Μ η ν x y

theorem integrableProject_parity (i : I) (μ : X) (x : IntegrableQuotient D hD Λ) :
    integrableRepresentation D hD Λ (one D Coefficients.q pi μ) (integrableParity D hD Λ i x) =
      integrableParity D hD Λ i (integrableRepresentation D hD Λ (one D Coefficients.q pi μ) x) := by
  induction x using integrable_induction D hD Λ with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => simp only [map_smul, hx]
  | word w =>
    simp only [integrableParity, integrableSign_word, map_smul,
      integrableRepresentation_toIntegrable, representation_one, weightProject_mk,
      weightProjectFree_monomial]
    split_ifs <;> simp only [integrableSign_word, map_zero, smul_zero]

/-- Negative weight covariance on arbitrary tensors of the original quotients. -/
theorem tensorProject_F (withJ : Bool) (i : I) (η : X) :
    tensorProject D hD Λ Μ η * tensorF D hD Λ Μ withJ i =
      tensorF D hD Λ Μ withJ i * tensorProject D hD Λ Μ (η + D.α i) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, Module.End.mul_apply]
  induction y using integrable_weight_induction D hD Μ with
  | zero => simp
  | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
  | project ν y =>
    have hpy : integrableRepresentation D hD Μ (one D Coefficients.q pi ν)
        (integrableRepresentation D hD Μ (one D Coefficients.q pi ν) y) =
        integrableRepresentation D hD Μ (one D Coefficients.q pi ν) y := by
      rw [← Module.End.mul_apply, ← map_mul, one_mul_one_self]
    have hlp : integrableRepresentation D hD Μ (one D Coefficients.q pi (ν + D.α i))
        (lowestF D hD Μ i (integrableRepresentation D hD Μ (one D Coefficients.q pi ν) y)) =
        lowestF D hD Μ i (integrableRepresentation D hD Μ (one D Coefficients.q pi ν) y) := by
      simp only [lowestF_eq_smul, LinearMap.smul_apply, map_smul,
        integrableProject_chevalley, halfRoot, ite_true, add_sub_cancel_right, hpy]
    simp only [tensorF_tmul, map_add, tensorK, integrableWeight_project, tmul_smul,
      map_smul, tensorProject_tmul_project, tensorProject_tmul_of_project D hD Λ Μ η _ _ _ hlp,
      integrableProject_chevalley, halfRoot, Bool.false_eq_true, ite_false, sub_neg_eq_add,
      tensorFTwist_eq_smul, LinearMap.smul_apply, integrableProject_parity]
    have h1 : η + ν + D.α i = η + D.α i + ν := by abel
    have h2 : η + (ν + D.α i) = η + D.α i + ν := by abel
    rw [h1, h2]


/-- The actual two global tensor root operators, with positive part unchanged. -/
def tensorChevalley (withJ positive : Bool) (i : I) : Module.End Coefficients.Ring
    (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  if positive then tensorE D hD Λ Μ withJ i else tensorF D hD Λ Μ withJ i

variable (withJ : Bool)

private theorem tensorProject_chevalley (positive : Bool) (i : I) (μ : X) :
    tensorProject D hD Λ Μ μ * tensorChevalley D hD Λ Μ withJ positive i =
      tensorChevalley D hD Λ Μ withJ positive i *
        tensorProject D hD Λ Μ (μ - halfRoot D positive i) := by
  cases positive
  · simpa only [tensorChevalley, Bool.false_eq_true, ite_false, halfRoot, sub_neg_eq_add]
      using tensorProject_F D hD Λ Μ withJ i μ
  · exact tensorProject_E D hD Λ Μ withJ i μ

private theorem tensorProject_chevalley_pow (positive : Bool) (i : I) (n : ℕ) (μ : X) :
    tensorProject D hD Λ Μ μ * tensorChevalley D hD Λ Μ withJ positive i ^ n =
      tensorChevalley D hD Λ Μ withJ positive i ^ n *
        tensorProject D hD Λ Μ (μ - n • halfRoot D positive i) := by
  induction n generalizing μ with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← mul_assoc, tensorProject_chevalley, mul_assoc, ih, ← mul_assoc, ← pow_succ']
    congr 2
    rw [succ_nsmul]
    abel

private theorem tensorProject_power_absorb (positive : Bool) (i : I) (n : ℕ) (μ : X) :
    tensorProject D hD Λ Μ (μ + n • halfRoot D positive i) *
      tensorChevalley D hD Λ Μ withJ positive i ^ n * tensorProject D hD Λ Μ μ =
        tensorChevalley D hD Λ Μ withJ positive i ^ n * tensorProject D hD Λ Μ μ := by
  rw [tensorProject_chevalley_pow, add_sub_cancel_right, mul_assoc, tensorProject_mul]
  simp

/-- The actual action assigned to each generator of the unital envelope. -/
def tensorGenAction : Gen I X → Module.End Coefficients.Ring (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ)
  | .one μ => tensorProject D hD Λ Μ μ
  | .e i μ => tensorChevalley D hD Λ Μ withJ true i * tensorProject D hD Λ Μ μ
  | .f i μ => tensorChevalley D hD Λ Μ withJ false i * tensorProject D hD Λ Μ μ

/-- Evaluation of the free presentation in concrete endomorphisms. -/
def tensorFreeAction : Free Coefficients.Ring I X →ₐ[Coefficients.Ring]
    Module.End Coefficients.Ring (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  FreeAlgebra.lift Coefficients.Ring (tensorGenAction D hD Λ Μ withJ)

@[simp] theorem tensorFreeAction_one (μ : X) :
    tensorFreeAction D hD Λ Μ withJ (Free.one Coefficients.Ring μ) = tensorProject D hD Λ Μ μ := by
  simp [tensorFreeAction, Free.one, tensorGenAction]

@[simp] theorem tensorFreeAction_E (i : I) (μ : X) :
    tensorFreeAction D hD Λ Μ withJ (Free.E Coefficients.Ring i μ) =
      tensorChevalley D hD Λ Μ withJ true i * tensorProject D hD Λ Μ μ := by
  simp [tensorFreeAction, Free.E, tensorGenAction]

@[simp] theorem tensorFreeAction_F (i : I) (μ : X) :
    tensorFreeAction D hD Λ Μ withJ (Free.F Coefficients.Ring i μ) =
      tensorChevalley D hD Λ Μ withJ false i * tensorProject D hD Λ Μ μ := by
  simp [tensorFreeAction, Free.F, tensorGenAction]

private theorem tensorFreeAction_epow (i : I) (n : ℕ) (μ : X) :
    tensorFreeAction D hD Λ Μ withJ (epow D i n μ) =
      tensorChevalley D hD Λ Μ withJ true i ^ n * tensorProject D hD Λ Μ μ := by
  induction n with
  | zero => simp [epow]
  | succ n ih =>
    have hp := tensorProject_power_absorb D hD Λ Μ withJ true i n μ
    simp only [halfRoot, ite_true] at hp
    rw [epow, map_mul, tensorFreeAction_E, ih, mul_assoc, ← mul_assoc
      (tensorProject D hD Λ Μ _), hp, ← mul_assoc, ← pow_succ']

private theorem tensorFreeAction_fpow (i : I) (n : ℕ) (μ : X) :
    tensorFreeAction D hD Λ Μ withJ (fpow D i n μ) =
      tensorChevalley D hD Λ Μ withJ false i ^ n * tensorProject D hD Λ Μ μ := by
  induction n with
  | zero => simp [fpow]
  | succ n ih =>
    rw [fpow, map_mul, tensorFreeAction_F, ih]
    have he : μ - n • D.α i = μ + n • halfRoot D false i := by simp [halfRoot, sub_eq_add_neg]
    rw [he, mul_assoc, ← mul_assoc (tensorProject D hD Λ Μ _),
      tensorProject_power_absorb, ← mul_assoc, ← pow_succ']

private theorem tensorProjected_serre_term (positive : Bool) (i j : I) (a r : ℕ) (μ : X) :
    (tensorChevalley D hD Λ Μ withJ positive i ^ a *
      tensorProject D hD Λ Μ (μ + r • halfRoot D positive i + halfRoot D positive j)) *
      (tensorChevalley D hD Λ Μ withJ positive j * tensorProject D hD Λ Μ (μ + r • halfRoot D positive i)) *
      (tensorChevalley D hD Λ Μ withJ positive i ^ r * tensorProject D hD Λ Μ μ) =
    (tensorChevalley D hD Λ Μ withJ positive i ^ a * tensorChevalley D hD Λ Μ withJ positive j *
      tensorChevalley D hD Λ Μ withJ positive i ^ r) * tensorProject D hD Λ Μ μ := by
  have h1 : tensorProject D hD Λ Μ (μ + r • halfRoot D positive i + halfRoot D positive j) *
      tensorChevalley D hD Λ Μ withJ positive j * tensorProject D hD Λ Μ (μ + r • halfRoot D positive i) =
      tensorChevalley D hD Λ Μ withJ positive j * tensorProject D hD Λ Μ (μ + r • halfRoot D positive i) := by
    rw [tensorProject_chevalley, add_sub_cancel_right, mul_assoc, tensorProject_mul]
    simp
  calc
    _ = tensorChevalley D hD Λ Μ withJ positive i ^ a *
        (tensorProject D hD Λ Μ (μ + r • halfRoot D positive i + halfRoot D positive j) *
          tensorChevalley D hD Λ Μ withJ positive j * tensorProject D hD Λ Μ (μ + r • halfRoot D positive i)) *
        (tensorChevalley D hD Λ Μ withJ positive i ^ r * tensorProject D hD Λ Μ μ) := by noncomm_ring
    _ = tensorChevalley D hD Λ Μ withJ positive i ^ a * tensorChevalley D hD Λ Μ withJ positive j *
        (tensorProject D hD Λ Μ (μ + r • halfRoot D positive i) *
          tensorChevalley D hD Λ Μ withJ positive i ^ r * tensorProject D hD Λ Μ μ) := by
      rw [h1]; noncomm_ring
    _ = _ := by rw [tensorProject_power_absorb]; noncomm_ring

private theorem tensorChevalley_serre (positive : Bool) {i j : I} (hij : i ≠ j) :
    ∑ r ∈ Finset.range (D.serreDeg i j + 1), D.serreCoeff Coefficients.q pi i j r •
      (tensorChevalley D hD Λ Μ withJ positive i ^ (D.serreDeg i j - r) * tensorChevalley D hD Λ Μ withJ positive j *
        tensorChevalley D hD Λ Μ withJ positive i ^ r) = 0 := by
  cases positive
  · exact tensorF_serre D hD Λ Μ withJ hij
  · exact tensorE_serre D hD Λ Μ withJ hij

private theorem tensorFreeAction_serreE {i j : I} (hij : i ≠ j) (μ : X) :
    tensorFreeAction D hD Λ Μ withJ (serreE D Coefficients.q pi i j μ) = 0 := by
  simp only [serreE, map_sum, map_smul, map_mul, tensorFreeAction_epow, tensorFreeAction_E]
  have ht := tensorProjected_serre_term D hD Λ Μ withJ true i j
  simp only [halfRoot, ite_true] at ht
  simp only [ht, ← smul_mul_assoc, ← Finset.sum_mul]
  simpa only [← smul_mul_assoc, zero_mul] using
    congrArg (· * tensorProject D hD Λ Μ μ) (tensorChevalley_serre D hD Λ Μ withJ true hij)

private theorem tensorFreeAction_serreF {i j : I} (hij : i ≠ j) (μ : X) :
    tensorFreeAction D hD Λ Μ withJ (serreF D Coefficients.q pi i j μ) = 0 := by
  simp only [serreF, map_sum, map_smul, map_mul, tensorFreeAction_fpow, tensorFreeAction_F]
  have ht := tensorProjected_serre_term D hD Λ Μ withJ false i j
  simp only [halfRoot, Bool.false_eq_true, ite_false, smul_neg, ← sub_eq_add_neg] at ht
  simp only [ht, ← smul_mul_assoc, ← Finset.sum_mul]
  simpa only [← smul_mul_assoc, zero_mul] using
    congrArg (· * tensorProject D hD Λ Μ μ) (tensorChevalley_serre D hD Λ Μ withJ false hij)

private theorem tensorProject_step_absorb (positive : Bool) (i : I) (μ : X) :
    tensorProject D hD Λ Μ (μ + halfRoot D positive i) *
      (tensorChevalley D hD Λ Μ withJ positive i * tensorProject D hD Λ Μ μ) =
        tensorChevalley D hD Λ Μ withJ positive i * tensorProject D hD Λ Μ μ := by
  rw [← mul_assoc, tensorProject_chevalley, add_sub_cancel_right, mul_assoc, tensorProject_mul]
  simp

/-- Every relation of the existing modified presentation holds for the concrete operators. -/
theorem tensorFreeAction_rel {x y : Free Coefficients.Ring I X}
    (h : Rel D Coefficients.q pi x y) : tensorFreeAction D hD Λ Μ withJ x = tensorFreeAction D hD Λ Μ withJ y := by
  cases h with
  | one_one μ ν =>
    simp only [map_mul, tensorFreeAction_one, tensorProject_mul]
    split_ifs <;> simp
  | one_E i μ =>
    simpa only [map_mul, tensorFreeAction_one, tensorFreeAction_E, halfRoot, ite_true] using
      tensorProject_step_absorb D hD Λ Μ withJ true i μ
  | one_F i μ =>
    simpa only [map_mul, tensorFreeAction_one, tensorFreeAction_F, halfRoot, Bool.false_eq_true,
      ite_false, sub_eq_add_neg] using tensorProject_step_absorb D hD Λ Μ withJ false i μ
  | E_one i μ => simp only [map_mul, tensorFreeAction_E, tensorFreeAction_one, mul_assoc,
      tensorProject_mul, ite_true]
  | F_one i μ => simp only [map_mul, tensorFreeAction_F, tensorFreeAction_one, mul_assoc,
      tensorProject_mul, ite_true]
  | serreE i j μ hij => rw [tensorFreeAction_serreE D hD Λ Μ withJ hij, map_zero]
  | serreF i j μ hij => rw [tensorFreeAction_serreF D hD Λ Μ withJ hij, map_zero]
  | comm i j μ =>
    have he := tensorProject_step_absorb D hD Λ Μ withJ true i μ
    have hf := tensorProject_step_absorb D hD Λ Μ withJ false j μ
    simp only [halfRoot, ite_true] at he
    simp only [halfRoot, Bool.false_eq_true, ite_false, ← sub_eq_add_neg] at hf
    simp only [map_sub, map_mul, map_smul, tensorFreeAction_E, tensorFreeAction_F, mul_assoc, he, hf]
    have hm := tensor_mixed_project D hD Λ Μ withJ i j μ
    simpa only [tensorChevalley, ite_true, Bool.false_eq_true, ite_false, sub_mul,
      smul_mul_assoc, mul_assoc, apply_ite, map_smul, tensorFreeAction_one, map_zero] using hm

/-- The complete Delta1/Delta2 tensor action of the original unital envelope,
with no dominance assumption. Its construction checks every original relation.
This does not assert integrability, nondegeneracy, or faithfulness. -/
def tensorRepresentation : CoveringUDot Coefficients.Ring D Coefficients.q pi →ₐ[Coefficients.Ring]
    Module.End Coefficients.Ring (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  RingQuot.liftAlgHom Coefficients.Ring ⟨tensorFreeAction D hD Λ Μ withJ, fun _ _ h ↦ tensorFreeAction_rel D hD Λ Μ withJ h⟩

@[simp] theorem tensorRepresentation_mk (x : Free Coefficients.Ring I X) :
    tensorRepresentation D hD Λ Μ withJ (mk D Coefficients.q pi x) = tensorFreeAction D hD Λ Μ withJ x := by
  simp only [tensorRepresentation, mk, RingQuot.liftAlgHom_mkAlgHom_apply]

@[simp] theorem tensorRepresentation_one (μ : X) :
    tensorRepresentation D hD Λ Μ withJ (one D Coefficients.q pi μ) = tensorProject D hD Λ Μ μ := by
  rw [one, tensorRepresentation_mk, tensorFreeAction_one]

@[simp] theorem tensorRepresentation_E (i : I) (μ : X) :
    tensorRepresentation D hD Λ Μ withJ (E D Coefficients.q pi i μ) =
      tensorEBlock D hD Λ Μ withJ i μ := by
  rw [E, tensorRepresentation_mk, tensorFreeAction_E]
  rfl

@[simp] theorem tensorRepresentation_F (i : I) (μ : X) :
    tensorRepresentation D hD Λ Μ withJ (F D Coefficients.q pi i μ) =
      tensorF D hD Λ Μ withJ i * tensorProject D hD Λ Μ μ := by
  rw [F, tensorRepresentation_mk, tensorFreeAction_F]
  rfl

/-- Restriction of the constructed action to the actual nonunital modified algebra. -/
def tensorModifiedRepresentation : modified D Coefficients.q pi →ₙₐ[Coefficients.Ring]
    Module.End Coefficients.Ring (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  (tensorRepresentation D hD Λ Μ withJ).toNonUnitalAlgHom.comp (NonUnitalSubalgebraClass.subtype (modified D Coefficients.q pi))

/-- Evaluation of free negative words in the existing mixed tensor F operators. -/
def tensorNegativeFree (withJ : Bool) : PreF Coefficients.Ring I →ₐ[Coefficients.Ring]
    Module.End Coefficients.Ring
      (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  FreeAlgebra.lift Coefficients.Ring (tensorF D hD Λ Μ withJ)

@[simp] theorem tensorNegativeFree_θ (withJ : Bool) (i : I) :
    tensorNegativeFree D hD Λ Μ withJ (θ Coefficients.Ring i) =
      tensorF D hD Λ Μ withJ i := by simp [tensorNegativeFree, θ]

/-- The actual negative-half action, with Serre proved rather than assumed. -/
def tensorNegativeAction (withJ : Bool) : D.serreF Coefficients.q pi →ₐ[Coefficients.Ring]
    Module.End Coefficients.Ring
      (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  RingQuot.liftAlgHom Coefficients.Ring
    ⟨tensorNegativeFree D hD Λ Μ withJ, fun _ _ h ↦ by
      cases h with
      | serre i j hij =>
        simpa only [SuperCartanDatum.serreElt, map_sum, map_smul, map_mul, map_pow,
          tensorNegativeFree_θ, map_zero] using tensorF_serre D hD Λ Μ withJ hij⟩

@[simp] theorem tensorNegativeAction_mk (withJ : Bool) (x : PreF Coefficients.Ring I) :
    tensorNegativeAction D hD Λ Μ withJ (D.toSerreF Coefficients.q pi x) =
      tensorNegativeFree D hD Λ Μ withJ x :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ x

@[simp] theorem tensorNegativeAction_θ (withJ : Bool) (i : I) :
    tensorNegativeAction D hD Λ Μ withJ (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i)) =
      tensorF D hD Λ Μ withJ i := by simp

/-- The actual negative weight-labelled tensor generator. -/
def tensorFBlock (withJ : Bool) (i : I) (η : X) : Module.End Coefficients.Ring
    (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  tensorF D hD Λ Μ withJ i * tensorProject D hD Λ Μ η

private theorem tensorProject_negativeWord (withJ : Bool) (η : X) (w : List I) :
    tensorProject D hD Λ Μ η * tensorNegativeFree D hD Λ Μ withJ (monomial Coefficients.Ring w) =
      tensorNegativeFree D hD Λ Μ withJ (monomial Coefficients.Ring w) *
        tensorProject D hD Λ Μ (η - halfWeight D false (wordWeight w)) := by
  induction w generalizing η with
  | nil => simp
  | cons i w ih =>
    simp only [monomial_cons, map_mul, tensorNegativeFree_θ, wordWeight_cons, halfWeight_add,
      halfWeight_single, halfRoot, Bool.false_eq_true, ite_false]
    rw [← mul_assoc, tensorProject_F, mul_assoc, ih, ← mul_assoc]
    congr 2
    abel

/-- Weight covariance of the descended half action on any homogeneous half element. -/
theorem tensorProject_negativeAction (withJ : Bool) (η : X) {ν : I →₀ ℕ}
    {x : D.serreF Coefficients.q pi} (hx : x ∈ halfWeightSpace D Coefficients.q pi ν) :
    tensorProject D hD Λ Μ η * tensorNegativeAction D hD Λ Μ withJ x =
      tensorNegativeAction D hD Λ Μ withJ x *
        tensorProject D hD Λ Μ (η - halfWeight D false ν) := by
  obtain ⟨x, hx, rfl⟩ := hx
  simp only [AlgHom.toLinearMap_apply, tensorNegativeAction_mk]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    change wordWeight w = ν at hw
    rw [← hw]
    exact tensorProject_negativeWord D hD Λ Μ withJ η w
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, mul_add, add_mul, ihx, ihy]
  | smul c x hx ih => simp only [map_smul, mul_smul_comm, smul_mul_assoc, ih]

/-- Weight-labelled negative-half map: its unit is the existing finite projector,
not the unit of the endomorphism algebra. -/
def tensorNegativeBlock (withJ : Bool) (η : X) : D.serreF Coefficients.q pi →ₗ[Coefficients.Ring]
    Module.End Coefficients.Ring
      (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) where
  toFun x := tensorNegativeAction D hD Λ Μ withJ x * tensorProject D hD Λ Μ η
  map_add' x y := by rw [map_add, add_mul]
  map_smul' c x := by rw [map_smul, smul_mul_assoc]; rfl

@[simp] theorem tensorNegativeBlock_one (withJ : Bool) (η : X) :
    tensorNegativeBlock D hD Λ Μ withJ η 1 = tensorProject D hD Λ Μ η := by
  change tensorNegativeAction D hD Λ Μ withJ 1 * _ = _
  rw [map_one, one_mul]

@[simp] theorem tensorNegativeBlock_θ (withJ : Bool) (η : X) (i : I) :
    tensorNegativeBlock D hD Λ Μ withJ η
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i)) =
        tensorFBlock D hD Λ Μ withJ i η := by
  change tensorNegativeAction D hD Λ Μ withJ _ * _ = _
  rw [tensorNegativeAction_θ]; rfl

/-- Right corner of every, possibly inhomogeneous, descended half element. -/
theorem tensorNegativeBlock_project (withJ : Bool) (η : X) (x : D.serreF Coefficients.q pi) :
    tensorNegativeBlock D hD Λ Μ withJ η x * tensorProject D hD Λ Μ η =
      tensorNegativeBlock D hD Λ Μ withJ η x := by
  change (tensorNegativeAction D hD Λ Μ withJ x * tensorProject D hD Λ Μ η) *
    tensorProject D hD Λ Μ η = _
  rw [mul_assoc, tensorProject_mul]
  simp only [ite_true]
  rfl

/-- Left corner with the actual weight shift of a homogeneous half element. -/
theorem tensorProject_negativeBlock (withJ : Bool) (η : X) {ν : I →₀ ℕ}
    {x : D.serreF Coefficients.q pi} (hx : x ∈ halfWeightSpace D Coefficients.q pi ν) :
    tensorProject D hD Λ Μ (η + halfWeight D false ν) *
        tensorNegativeBlock D hD Λ Μ withJ η x = tensorNegativeBlock D hD Λ Μ withJ η x := by
  change tensorProject D hD Λ Μ (η + halfWeight D false ν) *
    (tensorNegativeAction D hD Λ Μ withJ x * tensorProject D hD Λ Μ η) = _
  rw [← mul_assoc, tensorProject_negativeAction D hD Λ Μ withJ _ hx,
    add_sub_cancel_right, mul_assoc, tensorProject_mul]
  simp only [ite_true]
  rfl

/-- Shifted multiplication law for the weight-labelled descent. Only the right
factor needs a degree; both operators act on arbitrary original quotient tensors. -/
theorem tensorNegativeBlock_mul (withJ : Bool) (η : X) {ν : I →₀ ℕ}
    (x : D.serreF Coefficients.q pi) {y : D.serreF Coefficients.q pi}
    (hy : y ∈ halfWeightSpace D Coefficients.q pi ν) :
    tensorNegativeBlock D hD Λ Μ withJ η (x * y) =
      tensorNegativeBlock D hD Λ Μ withJ (η + halfWeight D false ν) x *
        tensorNegativeBlock D hD Λ Μ withJ η y := by
  change tensorNegativeAction D hD Λ Μ withJ (x * y) * _ = (_ * _) * (_ * _)
  rw [map_mul]
  simp only [mul_assoc]
  exact congrArg (fun z ↦ tensorNegativeAction D hD Λ Μ withJ x * z)
    (tensorProject_negativeBlock D hD Λ Μ withJ η hy).symm

/-- Negative divided-free power with the actual finite right projector. -/
def tensorFPowBlock (withJ : Bool) (i : I) (n : ℕ) (η : X) : Module.End Coefficients.Ring
    (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  tensorF D hD Λ Μ withJ i ^ n * tensorProject D hD Λ Μ η

private theorem tensorProject_F_pow (withJ : Bool) (i : I) (n : ℕ) (η : X) :
    tensorProject D hD Λ Μ η * tensorF D hD Λ Μ withJ i ^ n =
      tensorF D hD Λ Μ withJ i ^ n * tensorProject D hD Λ Μ (η + n • D.α i) := by
  induction n generalizing η with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← mul_assoc, tensorProject_F, mul_assoc, ih, ← mul_assoc]
    congr 2
    rw [add_nsmul, one_nsmul]
    abel

@[simp] theorem tensorFPowBlock_zero (withJ : Bool) (i : I) (η : X) :
    tensorFPowBlock D hD Λ Μ withJ i 0 η = tensorProject D hD Λ Μ η := by
  simp [tensorFPowBlock]

/-- Recursion in the actual weight-labelled generators, not merely unprojected powers. -/
theorem tensorFPowBlock_succ (withJ : Bool) (i : I) (n : ℕ) (η : X) :
    tensorFPowBlock D hD Λ Μ withJ i (n + 1) η =
      tensorFBlock D hD Λ Μ withJ i (η - n • D.α i) *
        tensorFPowBlock D hD Λ Μ withJ i n η := by
  simp only [tensorFPowBlock, tensorFBlock]
  rw [mul_assoc, ← mul_assoc (tensorProject D hD Λ Μ _), tensorProject_F_pow,
    sub_add_cancel, mul_assoc, tensorProject_mul]
  simp only [ite_true, ← mul_assoc, pow_succ']

private theorem tensorNegativeSerreWord_block (withJ : Bool) (i j : I) (n m : ℕ) (η : X) :
    tensorFPowBlock D hD Λ Μ withJ i n (η - m • D.α i - D.α j) *
        tensorFBlock D hD Λ Μ withJ j (η - m • D.α i) *
        tensorFPowBlock D hD Λ Μ withJ i m η =
      (tensorF D hD Λ Μ withJ i ^ n * tensorF D hD Λ Μ withJ j *
        tensorF D hD Λ Μ withJ i ^ m) * tensorProject D hD Λ Μ η := by
  simp only [tensorFPowBlock, tensorFBlock]
  simp only [mul_assoc]
  rw [← mul_assoc (tensorProject D hD Λ Μ _), tensorProject_F,
    sub_add_cancel, mul_assoc, ← mul_assoc (tensorProject D hD Λ Μ _),
    tensorProject_mul]
  simp only [ite_true]
  rw [← mul_assoc (tensorProject D hD Λ Μ _), tensorProject_F_pow,
    sub_add_cancel, mul_assoc, tensorProject_mul]
  simp only [ite_true]

/-- The full weight-labelled negative Serre relation, with all prescribed intermediate
weights. It holds as an endomorphism of the original mixed tensor, in either convention. -/
theorem tensorFBlock_serre (withJ : Bool) {i j : I} (hij : i ≠ j) (η : X) :
    ∑ r ∈ Finset.range (D.serreDeg i j + 1), D.serreCoeff Coefficients.q pi i j r •
      (tensorFPowBlock D hD Λ Μ withJ i (D.serreDeg i j - r) (η - r • D.α i - D.α j) *
        tensorFBlock D hD Λ Μ withJ j (η - r • D.α i) *
        tensorFPowBlock D hD Λ Μ withJ i r η) = 0 := by
  have hs := congrArg (fun f ↦ f * tensorProject D hD Λ Μ η)
    (tensorF_serre D hD Λ Μ withJ hij)
  simpa only [tensorNegativeSerreWord_block, Finset.sum_mul, smul_mul_assoc, zero_mul] using hs

/-- The mixed relation in the original presentation, with every weight label
and coefficient retained. This is an equality of endomorphisms, not just a
homogeneous-vector computation. -/
theorem tensorBlock_comm (i j : I) (μ : X) :
    tensorEBlock D hD Λ Μ withJ i (μ - D.α j) * tensorFBlock D hD Λ Μ withJ j μ -
      pi ^ (D.parity i * D.parity j).val •
        (tensorFBlock D hD Λ Μ withJ j (μ + D.α i) * tensorEBlock D hD Λ Μ withJ i μ) =
      if i = j then qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i μ) •
        tensorProject D hD Λ Μ μ else 0 := by
  have h := congrArg (tensorRepresentation D hD Λ Μ withJ) (comm_rel D Coefficients.q pi i j μ)
  simpa only [map_sub, map_mul, map_smul, tensorRepresentation_E, tensorRepresentation_F,
    tensorRepresentation_one, tensorFBlock, apply_ite, map_zero] using h

theorem tensorProject_FBlock (i : I) (μ : X) :
    tensorProject D hD Λ Μ (μ - D.α i) * tensorFBlock D hD Λ Μ withJ i μ =
      tensorFBlock D hD Λ Μ withJ i μ := by
  simp only [tensorFBlock, ← mul_assoc, tensorProject_F, sub_add_cancel]
  rw [mul_assoc, tensorProject_mul]
  simp

theorem tensorFBlock_project (i : I) (μ : X) :
    tensorFBlock D hD Λ Μ withJ i μ * tensorProject D hD Λ Μ μ =
      tensorFBlock D hD Λ Μ withJ i μ := by
  simp only [tensorFBlock, mul_assoc, tensorProject_mul, ite_true]

end OddMath.CoveringQuantum.UDot.GenericVerma
