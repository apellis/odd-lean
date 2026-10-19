/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.IntegrableSigns
import OddMath.CoveringQuantum.UDot.LowestQuotient

/-!
# Global operators on the source-generated quotient

Finite weight support comes from the actual free-word grading, with equal root
images grouped in the weight group. Global Chevalley and toral operators descend
through the original action-generated relations, not a radical replacement.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma
open PreF Coefficients
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X) (Λ : X)

omit [DecidableEq I] [DecidableEq X] in
/-- The existing grading coefficient is the corresponding actual weight projector. -/
theorem grading_eq_project (x : D.serreF Coefficients.q pi) (a : X) :
    GenericTensor.grading D x a = weightProject D Λ (Λ - a) x := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  change weightProject D 0 (-a) (D.toSerreF Coefficients.q pi x) = _
  simp only [weightProject_mk, weightProjectFree, zero_sub, neg_neg, sub_sub_cancel]

omit [DecidableEq I] [DecidableEq X] in
/-- Summing the genuine finitely supported grading recovers an arbitrary vector. -/
theorem sum_grading (x : D.serreF Coefficients.q pi) :
    Finsupp.lsum Coefficients.Ring (fun _ : X ↦
      (LinearMap.id : Module.End Coefficients.Ring (D.serreF Coefficients.q pi)))
      (GenericTensor.grading D x) = x := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  induction x using induction_monomial with
  | word w => rw [GenericTensor.grading_monomial, Finsupp.lsum_single]; rfl
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => simp only [map_smul, hx]

/-- Every actual graded coefficient preserves the source relation submodule. -/
theorem grading_mem_integrabilityRelations {x : D.serreF Coefficients.q pi}
    (hx : x ∈ integrabilityRelations D Λ) (a : X) :
    GenericTensor.grading D x a ∈ integrabilityRelations D Λ := by
  rw [grading_eq_project D Λ, ← representation_one]
  exact integrabilityRelations_invariant D Λ _ hx

private def gradingToQuotient : D.serreF Coefficients.q pi →ₗ[Coefficients.Ring]
    (X →₀ IntegrableQuotient D Λ) :=
  (Finsupp.mapRange.linearMap (toIntegrable D Λ)).comp (GenericTensor.grading D)

/-- Finite root-image coordinates on the actual quotient. No independent-root
or finite-fiber hypothesis is used. -/
def integrableGrading : IntegrableQuotient D Λ →ₗ[Coefficients.Ring]
    (X →₀ IntegrableQuotient D Λ) :=
  (integrabilityRelations D Λ).liftQ (gradingToQuotient D Λ) (by
    intro x hx
    ext a
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (grading_mem_integrabilityRelations D Λ hx a))

@[simp] theorem integrableGrading_mk (x : D.serreF Coefficients.q pi) (a : X) :
    integrableGrading D Λ (toIntegrable D Λ x) a =
      toIntegrable D Λ (GenericTensor.grading D x a) := rfl

/-- The coordinates are exactly the original represented weight idempotents. -/
theorem integrableGrading_apply (x : IntegrableQuotient D Λ) (a : X) :
    integrableGrading D Λ x a =
      integrableRepresentation D Λ (one D Coefficients.q pi (Λ - a)) x := by
  obtain ⟨x⟩ := x
  change toIntegrable D Λ (GenericTensor.grading D x a) =
    toIntegrable D Λ (representation D Λ (one D Coefficients.q pi (Λ - a)) x)
  rw [representation_one, grading_eq_project D Λ]

@[simp] theorem integrableGrading_word (w : List I) :
    integrableGrading D Λ
      (toIntegrable D Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) =
      Finsupp.single (halfWeight D true (wordWeight w))
        (toIntegrable D Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) := by
  change Finsupp.mapRange (toIntegrable D Λ) (map_zero _)
    (GenericTensor.grading D (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) = _
  rw [GenericTensor.grading_monomial, Finsupp.mapRange_single]

/-- Quotient vectors are finite sums of their actual weight components. -/
theorem sum_integrableGrading (x : IntegrableQuotient D Λ) :
    Finsupp.lsum Coefficients.Ring (fun _ : X ↦
      (LinearMap.id : Module.End Coefficients.Ring (IntegrableQuotient D Λ)))
      (integrableGrading D Λ x) = x := by
  obtain ⟨x⟩ := x
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  change Finsupp.lsum Coefficients.Ring (fun _ : X ↦
    (LinearMap.id : Module.End Coefficients.Ring (IntegrableQuotient D Λ)))
    (integrableGrading D Λ (toIntegrable D Λ (D.toSerreF Coefficients.q pi x))) =
      toIntegrable D Λ (D.toSerreF Coefficients.q pi x)
  induction x using induction_monomial with
  | word w => rw [integrableGrading_word, Finsupp.lsum_single]; rfl
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => simp only [map_smul, hx]

private theorem chevalley_eq_weight_sum (positive : Bool) (i : I)
    (x : D.serreF Coefficients.q pi) :
    chevalley D Λ positive i x =
      Finsupp.lsum Coefficients.Ring (fun a ↦
        representation D Λ (halfGen D Coefficients.q pi positive i (Λ - a)))
        (GenericTensor.grading D x) := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  induction x using induction_monomial with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => simp only [map_smul, hx]
  | word w =>
    rw [GenericTensor.grading_monomial, Finsupp.lsum_single]
    have hp : weightProject D Λ (Λ - halfWeight D true (wordWeight w))
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) =
        D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w) := by
      rw [weightProject_mk, weightProjectFree_monomial]
      simp
    cases positive
    · simp only [halfGen, Bool.false_eq_true, ite_false, representation_F, hp,
        chevalley_false_apply]
    · simp only [halfGen, ite_true, representation_E, Module.End.mul_apply, hp, chevalley_true]

/-- Global E and F preserve the original relations. The proof uses the finite
weight decomposition, so it applies also to inhomogeneous relation orbits. -/
theorem chevalley_integrabilityRelations (positive : Bool) (i : I) :
    integrabilityRelations D Λ ≤ (integrabilityRelations D Λ).comap
      (chevalley D Λ positive i) := by
  intro x hx
  change chevalley D Λ positive i x ∈ integrabilityRelations D Λ
  rw [chevalley_eq_weight_sum]
  change (GenericTensor.grading D x).sum (fun a y ↦
    representation D Λ (halfGen D Coefficients.q pi positive i (Λ - a)) y) ∈ _
  apply Submodule.sum_mem
  intro a _
  exact integrabilityRelations_invariant D Λ _
    (grading_mem_integrabilityRelations D Λ hx a)

/-- Unprojected Chevalley operator on the original quotient. -/
def integrableChevalley (positive : Bool) (i : I) :
    Module.End Coefficients.Ring (IntegrableQuotient D Λ) :=
  (integrabilityRelations D Λ).mapQ _ (chevalley D Λ positive i)
    (chevalley_integrabilityRelations D Λ positive i)

@[simp] theorem integrableChevalley_mk (positive : Bool) (i : I)
    (x : D.serreF Coefficients.q pi) :
    integrableChevalley D Λ positive i (toIntegrable D Λ x) =
      toIntegrable D Λ (chevalley D Λ positive i x) := rfl

/-- The global operator followed by a weight projection is exactly the accepted
weight-labelled action, not merely an operator with the same vacuum value. -/
theorem integrableChevalley_project (positive : Bool) (i : I) (μ : X)
    (x : IntegrableQuotient D Λ) :
    integrableChevalley D Λ positive i
      (integrableRepresentation D Λ (one D Coefficients.q pi μ) x) =
      integrableRepresentation D Λ (halfGen D Coefficients.q pi positive i μ) x := by
  obtain ⟨x⟩ := x
  change toIntegrable D Λ (chevalley D Λ positive i
    (representation D Λ (one D Coefficients.q pi μ) x)) =
    toIntegrable D Λ (representation D Λ (halfGen D Coefficients.q pi positive i μ) x)
  rw [representation_one]
  cases positive
  · simp only [halfGen, Bool.false_eq_true, ite_false, representation_F, chevalley_false_apply]
  · simp only [halfGen, ite_true, representation_E, Module.End.mul_apply, chevalley_true]

/-- Weight-diagonal operators on the quotient, defined by a genuinely finite sum. -/
def integrableWeight (f : X → Coefficients.Ring) :
    Module.End Coefficients.Ring (IntegrableQuotient D Λ) :=
  (Finsupp.lsum Coefficients.Ring (fun a ↦ f (Λ - a) • LinearMap.id)).comp
    (integrableGrading D Λ)

@[simp] theorem integrableWeight_word (f : X → Coefficients.Ring) (w : List I) :
    integrableWeight D Λ f
      (toIntegrable D Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) =
      f (Λ - halfWeight D true (wordWeight w)) •
        toIntegrable D Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) := by
  simp only [integrableWeight, LinearMap.comp_apply, integrableGrading_word,
    Finsupp.lsum_single, LinearMap.smul_apply, LinearMap.id_apply]

/-- Linear induction over actual quotient words. -/
theorem integrable_induction {P : IntegrableQuotient D Λ → Prop}
    (word : ∀ w, P (toIntegrable D Λ
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))))
    (zero : P 0) (add : ∀ x y, P x → P y → P (x + y))
    (smul : ∀ (c : Coefficients.Ring) x, P x → P (c • x))
    (x : IntegrableQuotient D Λ) : P x := by
  obtain ⟨x⟩ := x
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  change P (toIntegrable D Λ (D.toSerreF Coefficients.q pi x))
  induction x using induction_monomial with
  | word w => exact word w
  | zero => simpa only [map_zero] using zero
  | add x y hx hy => simpa only [map_add] using add _ _ hx hy
  | smul c x hx => simpa only [map_smul] using smul c _ hx

/-- Finite resolution of identity as a spanning principle. -/
theorem integrable_weight_induction {P : IntegrableQuotient D Λ → Prop}
    (project : ∀ μ x, P (integrableRepresentation D Λ (one D Coefficients.q pi μ) x))
    (zero : P 0) (add : ∀ x y, P x → P y → P (x + y))
    (x : IntegrableQuotient D Λ) : P x := by
  rw [← sum_integrableGrading D Λ x]
  change P ((integrableGrading D Λ x).sum (fun _ y ↦ y))
  apply Finset.sum_induction
  · exact add
  · exact zero
  · intro a _
    rw [integrableGrading_apply]
    exact project _ x

/-- Weight multiplication is pointwise on every quotient vector. -/
theorem integrableWeight_mul (f g : X → Coefficients.Ring) :
    integrableWeight D Λ f * integrableWeight D Λ g =
      integrableWeight D Λ (fun μ ↦ f μ * g μ) := by
  apply LinearMap.ext
  intro x
  induction x using integrable_induction D Λ with
  | word w => simp [Module.End.mul_apply, smul_smul, mul_comm]
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul c x hx => simpa only [map_smul] using congrArg (c • ·) hx

/-- Constant-one weight scaling is the identity, including on mixed weights. -/
@[simp] theorem integrableWeight_one : integrableWeight D Λ (fun _ ↦ 1) = 1 := by
  apply LinearMap.ext
  intro x
  simpa only [integrableWeight, one_smul, LinearMap.comp_apply, Module.End.one_apply]
    using sum_integrableGrading D Λ x

/-- Weight scaling agrees with the selected scalar on the actual idempotent image. -/
theorem integrableWeight_project (f : X → Coefficients.Ring) (μ : X)
    (x : IntegrableQuotient D Λ) :
    integrableWeight D Λ f
      (integrableRepresentation D Λ (one D Coefficients.q pi μ) x) =
      f μ • integrableRepresentation D Λ (one D Coefficients.q pi μ) x := by
  induction x using integrable_induction D Λ with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | smul c x hx => simp only [map_smul, hx, smul_comm c]
  | word w =>
    rw [integrableRepresentation_toIntegrable, representation_one,
      weightProject_mk, weightProjectFree_monomial]
    split_ifs with h
    · rw [integrableWeight_word]
      have hw : Λ - halfWeight D true (wordWeight w) = μ := by rw [h]; abel
      rw [hw]
    · simp

/-- The global operators have their actual weight shifts on all quotient vectors. -/
theorem integrableProject_chevalley (positive : Bool) (i : I) (μ : X)
    (x : IntegrableQuotient D Λ) :
    integrableRepresentation D Λ (one D Coefficients.q pi μ)
      (integrableChevalley D Λ positive i x) =
      integrableChevalley D Λ positive i
        (integrableRepresentation D Λ
          (one D Coefficients.q pi (μ - halfRoot D positive i)) x) := by
  obtain ⟨x⟩ := x
  change integrableRepresentation D Λ _
    (integrableChevalley D Λ positive i (toIntegrable D Λ x)) =
    integrableChevalley D Λ positive i
      (integrableRepresentation D Λ _ (toIntegrable D Λ x))
  simp only [integrableChevalley_mk, integrableRepresentation_toIntegrable, representation_one]
  exact congrArg (toIntegrable D Λ)
    (congrArg (fun f ↦ f x) (project_chevalley D Λ positive i μ))

/-- All toral covariance follows from the genuine finite quotient grading. -/
theorem integrableWeight_chevalley (f : X → Coefficients.Ring) (positive : Bool)
    (i : I) (x : IntegrableQuotient D Λ) :
    integrableWeight D Λ f (integrableChevalley D Λ positive i x) =
      integrableChevalley D Λ positive i
        (integrableWeight D Λ (fun μ ↦ f (μ + halfRoot D positive i)) x) := by
  induction x using integrable_weight_induction D Λ with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | project μ x =>
    have hp : integrableRepresentation D Λ
        (one D Coefficients.q pi (μ + halfRoot D positive i))
        (integrableChevalley D Λ positive i
          (integrableRepresentation D Λ (one D Coefficients.q pi μ) x)) =
        integrableChevalley D Λ positive i
          (integrableRepresentation D Λ (one D Coefficients.q pi μ) x) := by
      rw [integrableProject_chevalley, add_sub_cancel_right]
      congr 1
      rw [← Module.End.mul_apply, ← map_mul, one_mul_one_self]
    calc
      _ = integrableWeight D Λ f
          (integrableRepresentation D Λ (one D Coefficients.q pi (μ + halfRoot D positive i))
            (integrableChevalley D Λ positive i
              (integrableRepresentation D Λ (one D Coefficients.q pi μ) x))) :=
        congrArg (integrableWeight D Λ f) hp.symm
      _ = _ := by rw [integrableWeight_project, hp, integrableWeight_project, map_smul]

/-- Koszul covariance for both global Chevalley operators. -/
theorem integrableParity_chevalley (i j : I) (positive : Bool)
    (x : IntegrableQuotient D Λ) :
    integrableParity D Λ i (integrableChevalley D Λ positive j x) =
      pi ^ (D.parity i * D.parity j).val • integrableChevalley D Λ positive j
        (integrableParity D Λ i x) := by
  obtain ⟨x⟩ := x
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  change integrableParity D Λ i (toIntegrable D Λ
      (chevalley D Λ positive j (D.toSerreF Coefficients.q pi x))) =
    pi ^ (D.parity i * D.parity j).val • integrableChevalley D Λ positive j
      (integrableParity D Λ i (toIntegrable D Λ (D.toSerreF Coefficients.q pi x)))
  induction x using induction_monomial with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | smul c x hx => simp only [map_smul, hx, smul_comm c]
  | word w =>
    have hp : integrableRepresentation D Λ
        (one D Coefficients.q pi (Λ - halfWeight D true (wordWeight w)))
        (toIntegrable D Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) =
        toIntegrable D Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) := by
      simp [integrableRepresentation_toIntegrable, representation_one,
        weightProject_mk, weightProjectFree_monomial]
    have hs : integrableRepresentation D Λ
        (one D Coefficients.q pi (Λ - halfWeight D true (wordWeight w)))
        (integrableParity D Λ i
          (toIntegrable D Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)))) =
        integrableParity D Λ i
          (toIntegrable D Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) := by
      change integrableRepresentation D Λ _ (integrableSign D Λ _ _ _) = _
      simp only [integrableParity, integrableSign_word, map_smul, hp]
    rw [← integrableChevalley_mk]
    have he := integrableChevalley_project D Λ positive j
      (Λ - halfWeight D true (wordWeight w))
      (toIntegrable D Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)))
    rw [hp] at he
    rw [he]
    have he' := integrableChevalley_project D Λ positive j
      (Λ - halfWeight D true (wordWeight w))
      (integrableParity D Λ i
        (toIntegrable D Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))))
    rw [hs] at he'
    rw [he']
    cases positive
    · exact integrableParity_F D Λ i j _ _
    · exact integrableParity_E D Λ i j _ _

private theorem halfEnd_integrabilityRelations (positive : Bool)
    (u : D.serreF Coefficients.q pi) :
    integrabilityRelations D Λ ≤ (integrabilityRelations D Λ).comap
      (halfEnd D Λ positive u) := by
  obtain ⟨u, rfl⟩ := D.toSerreF_surjective Coefficients.q pi u
  intro x hx
  change halfEnd D Λ positive (D.toSerreF Coefficients.q pi u) x ∈ integrabilityRelations D Λ
  induction u using FreeAlgebra.induction generalizing x with
  | grade0 c => simpa using Submodule.smul_mem (integrabilityRelations D Λ) c hx
  | grade1 i => exact chevalley_integrabilityRelations D Λ positive i hx
  | add a b ha hb => simp only [map_add, LinearMap.add_apply]; exact add_mem (ha hx) (hb hx)
  | mul a b ha hb => simp only [map_mul, Module.End.mul_apply]; exact ha (hb hx)

/-- Both actual Serre halves act globally on the source-generated quotient. -/
def integrableHalfEnd (positive : Bool) :
    D.serreF Coefficients.q pi →ₐ[Coefficients.Ring]
      Module.End Coefficients.Ring (IntegrableQuotient D Λ) where
  toFun u := (integrabilityRelations D Λ).mapQ _ (halfEnd D Λ positive u)
    (halfEnd_integrabilityRelations D Λ positive u)
  map_zero' := by ext ⟨x⟩; simp
  map_one' := by ext ⟨x⟩; simp
  map_add' u v := by ext ⟨x⟩; simp
  map_mul' u v := by ext ⟨x⟩; simp
  commutes' c := by ext ⟨x⟩; simp

@[simp] theorem integrableHalfEnd_θ (positive : Bool) (i : I) :
    integrableHalfEnd D Λ positive (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i)) =
      integrableChevalley D Λ positive i := rfl

/-- All single-factor global Serre relations hold, before constructing any tensor action. -/
theorem integrableChevalley_serre (positive : Bool) {i j : I} (hij : i ≠ j) :
    ∑ r ∈ Finset.range (D.serreDeg i j + 1),
      D.serreCoeff Coefficients.q pi i j r •
        (integrableChevalley D Λ positive i ^ (D.serreDeg i j - r) *
          integrableChevalley D Λ positive j * integrableChevalley D Λ positive i ^ r) = 0 := by
  have hs := congrArg (integrableHalfEnd D Λ positive)
    (D.toSerreF_serreElt Coefficients.q pi hij)
  simpa only [SuperCartanDatum.serreElt, map_sum, map_smul, map_mul, map_pow,
    integrableHalfEnd_θ, map_zero] using hs

end OddMath.CoveringQuantum.UDot.GenericVerma
