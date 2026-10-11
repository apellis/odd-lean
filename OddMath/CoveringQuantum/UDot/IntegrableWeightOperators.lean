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
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent) (Λ : X)

/-- The existing grading coefficient is the corresponding actual weight projector. -/
theorem grading_eq_project (x : D.serreF Coefficients.q pi) (a : X) :
    GenericTensor.grading D hD x a = weightProject D hD Λ (Λ - a) x := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  change weightProject D hD 0 (-a) (D.toSerreF Coefficients.q pi x) = _
  simp only [weightProject_mk, weightProjectFree, zero_sub, neg_neg, sub_sub_cancel]

/-- Summing the genuine finitely supported grading recovers an arbitrary vector. -/
theorem sum_grading (x : D.serreF Coefficients.q pi) :
    Finsupp.lsum Coefficients.Ring (fun _ : X ↦ (LinearMap.id : Module.End Coefficients.Ring (D.serreF Coefficients.q pi)))
      (GenericTensor.grading D hD x) = x := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  induction x using induction_monomial with
  | word w => rw [GenericTensor.grading_monomial, Finsupp.lsum_single]; rfl
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => simp only [map_smul, hx]

/-- Every actual graded coefficient preserves the source relation submodule. -/
theorem grading_mem_integrabilityRelations {x : D.serreF Coefficients.q pi}
    (hx : x ∈ integrabilityRelations D hD Λ) (a : X) :
    GenericTensor.grading D hD x a ∈ integrabilityRelations D hD Λ := by
  rw [grading_eq_project D hD Λ, ← representation_one]
  exact integrabilityRelations_invariant D hD Λ _ hx

private def gradingToQuotient : D.serreF Coefficients.q pi →ₗ[Coefficients.Ring]
    (X →₀ IntegrableQuotient D hD Λ) :=
  (Finsupp.mapRange.linearMap (toIntegrable D hD Λ)).comp (GenericTensor.grading D hD)

/-- Finite root-image coordinates on the actual quotient. No independent-root
or finite-fiber hypothesis is used. -/
def integrableGrading : IntegrableQuotient D hD Λ →ₗ[Coefficients.Ring]
    (X →₀ IntegrableQuotient D hD Λ) :=
  (integrabilityRelations D hD Λ).liftQ (gradingToQuotient D hD Λ) (by
    intro x hx
    ext a
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (grading_mem_integrabilityRelations D hD Λ hx a))

@[simp] theorem integrableGrading_mk (x : D.serreF Coefficients.q pi) (a : X) :
    integrableGrading D hD Λ (toIntegrable D hD Λ x) a =
      toIntegrable D hD Λ (GenericTensor.grading D hD x a) := rfl

/-- The coordinates are exactly the original represented weight idempotents. -/
theorem integrableGrading_apply (x : IntegrableQuotient D hD Λ) (a : X) :
    integrableGrading D hD Λ x a =
      integrableRepresentation D hD Λ (one D Coefficients.q pi (Λ - a)) x := by
  obtain ⟨x⟩ := x
  change toIntegrable D hD Λ (GenericTensor.grading D hD x a) =
    toIntegrable D hD Λ (representation D hD Λ (one D Coefficients.q pi (Λ - a)) x)
  rw [representation_one, grading_eq_project D hD Λ]

@[simp] theorem integrableGrading_word (w : List I) :
    integrableGrading D hD Λ
      (toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) =
      Finsupp.single (halfWeight D true (wordWeight w))
        (toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) := by
  change Finsupp.mapRange (toIntegrable D hD Λ) (map_zero _)
    (GenericTensor.grading D hD (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) = _
  rw [GenericTensor.grading_monomial, Finsupp.mapRange_single]

/-- Quotient vectors are finite sums of their actual weight components. -/
theorem sum_integrableGrading (x : IntegrableQuotient D hD Λ) :
    Finsupp.lsum Coefficients.Ring (fun _ : X ↦ (LinearMap.id : Module.End Coefficients.Ring (IntegrableQuotient D hD Λ)))
      (integrableGrading D hD Λ x) = x := by
  obtain ⟨x⟩ := x
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  change Finsupp.lsum Coefficients.Ring (fun _ : X ↦ (LinearMap.id : Module.End Coefficients.Ring (IntegrableQuotient D hD Λ)))
    (integrableGrading D hD Λ (toIntegrable D hD Λ (D.toSerreF Coefficients.q pi x))) =
      toIntegrable D hD Λ (D.toSerreF Coefficients.q pi x)
  induction x using induction_monomial with
  | word w => rw [integrableGrading_word, Finsupp.lsum_single]; rfl
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => simp only [map_smul, hx]

private theorem chevalley_eq_weight_sum (positive : Bool) (i : I)
    (x : D.serreF Coefficients.q pi) :
    chevalley D hD Λ positive i x =
      Finsupp.lsum Coefficients.Ring (fun a ↦
        representation D hD Λ (halfGen D Coefficients.q pi positive i (Λ - a)))
        (GenericTensor.grading D hD x) := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  induction x using induction_monomial with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => simp only [map_smul, hx]
  | word w =>
    rw [GenericTensor.grading_monomial, Finsupp.lsum_single]
    have hp : weightProject D hD Λ (Λ - halfWeight D true (wordWeight w))
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) =
        D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w) := by
      rw [weightProject_mk, weightProjectFree_monomial]
      simp
    cases positive
    · simp only [halfGen, Bool.false_eq_true, ite_false, representation_F, hp, chevalley_false_apply]
    · simp only [halfGen, ite_true, representation_E, Module.End.mul_apply, hp, chevalley_true]

/-- Global E and F preserve the original relations. The proof uses the finite
weight decomposition, so it applies also to inhomogeneous relation orbits. -/
theorem chevalley_integrabilityRelations (positive : Bool) (i : I) :
    integrabilityRelations D hD Λ ≤ (integrabilityRelations D hD Λ).comap
      (chevalley D hD Λ positive i) := by
  intro x hx
  change chevalley D hD Λ positive i x ∈ integrabilityRelations D hD Λ
  rw [chevalley_eq_weight_sum]
  change (GenericTensor.grading D hD x).sum (fun a y ↦
    representation D hD Λ (halfGen D Coefficients.q pi positive i (Λ - a)) y) ∈ _
  apply Submodule.sum_mem
  intro a _
  exact integrabilityRelations_invariant D hD Λ _
    (grading_mem_integrabilityRelations D hD Λ hx a)

/-- Unprojected Chevalley operator on the original quotient. -/
def integrableChevalley (positive : Bool) (i : I) :
    Module.End Coefficients.Ring (IntegrableQuotient D hD Λ) :=
  (integrabilityRelations D hD Λ).mapQ _ (chevalley D hD Λ positive i)
    (chevalley_integrabilityRelations D hD Λ positive i)

@[simp] theorem integrableChevalley_mk (positive : Bool) (i : I)
    (x : D.serreF Coefficients.q pi) :
    integrableChevalley D hD Λ positive i (toIntegrable D hD Λ x) =
      toIntegrable D hD Λ (chevalley D hD Λ positive i x) := rfl

/-- The global operator followed by a weight projection is exactly the accepted
weight-labelled action, not merely an operator with the same vacuum value. -/
theorem integrableChevalley_project (positive : Bool) (i : I) (μ : X)
    (x : IntegrableQuotient D hD Λ) :
    integrableChevalley D hD Λ positive i
      (integrableRepresentation D hD Λ (one D Coefficients.q pi μ) x) =
      integrableRepresentation D hD Λ (halfGen D Coefficients.q pi positive i μ) x := by
  obtain ⟨x⟩ := x
  change toIntegrable D hD Λ (chevalley D hD Λ positive i
    (representation D hD Λ (one D Coefficients.q pi μ) x)) =
    toIntegrable D hD Λ (representation D hD Λ (halfGen D Coefficients.q pi positive i μ) x)
  rw [representation_one]
  cases positive
  · simp only [halfGen, Bool.false_eq_true, ite_false, representation_F, chevalley_false_apply]
  · simp only [halfGen, ite_true, representation_E, Module.End.mul_apply, chevalley_true]

/-- Weight-diagonal operators on the quotient, defined by a genuinely finite sum. -/
def integrableWeight (f : X → Coefficients.Ring) :
    Module.End Coefficients.Ring (IntegrableQuotient D hD Λ) :=
  (Finsupp.lsum Coefficients.Ring (fun a ↦ f (Λ - a) • LinearMap.id)).comp
    (integrableGrading D hD Λ)

@[simp] theorem integrableWeight_word (f : X → Coefficients.Ring) (w : List I) :
    integrableWeight D hD Λ f
      (toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) =
      f (Λ - halfWeight D true (wordWeight w)) •
        toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) := by
  simp only [integrableWeight, LinearMap.comp_apply, integrableGrading_word,
    Finsupp.lsum_single, LinearMap.smul_apply, LinearMap.id_apply]

/-- Linear induction over actual quotient words. -/
theorem integrable_induction {P : IntegrableQuotient D hD Λ → Prop}
    (word : ∀ w, P (toIntegrable D hD Λ
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))))
    (zero : P 0) (add : ∀ x y, P x → P y → P (x + y))
    (smul : ∀ (c : Coefficients.Ring) x, P x → P (c • x))
    (x : IntegrableQuotient D hD Λ) : P x := by
  obtain ⟨x⟩ := x
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  change P (toIntegrable D hD Λ (D.toSerreF Coefficients.q pi x))
  induction x using induction_monomial with
  | word w => exact word w
  | zero => simpa only [map_zero] using zero
  | add x y hx hy => simpa only [map_add] using add _ _ hx hy
  | smul c x hx => simpa only [map_smul] using smul c _ hx

/-- Finite resolution of identity as a spanning principle. -/
theorem integrable_weight_induction {P : IntegrableQuotient D hD Λ → Prop}
    (project : ∀ μ x, P (integrableRepresentation D hD Λ (one D Coefficients.q pi μ) x))
    (zero : P 0) (add : ∀ x y, P x → P y → P (x + y))
    (x : IntegrableQuotient D hD Λ) : P x := by
  rw [← sum_integrableGrading D hD Λ x]
  change P ((integrableGrading D hD Λ x).sum (fun _ y ↦ y))
  apply Finset.sum_induction
  · exact add
  · exact zero
  · intro a _
    rw [integrableGrading_apply]
    exact project _ x

/-- Weight multiplication is pointwise on every quotient vector. -/
theorem integrableWeight_mul (f g : X → Coefficients.Ring) :
    integrableWeight D hD Λ f * integrableWeight D hD Λ g =
      integrableWeight D hD Λ (fun μ ↦ f μ * g μ) := by
  apply LinearMap.ext
  intro x
  induction x using integrable_induction D hD Λ with
  | word w => simp [Module.End.mul_apply, smul_smul, mul_comm]
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul c x hx => simpa only [map_smul] using congrArg (c • ·) hx

/-- Constant-one weight scaling is the identity, including on mixed weights. -/
@[simp] theorem integrableWeight_one : integrableWeight D hD Λ (fun _ ↦ 1) = 1 := by
  apply LinearMap.ext
  intro x
  simpa only [integrableWeight, one_smul, LinearMap.comp_apply, Module.End.one_apply]
    using sum_integrableGrading D hD Λ x

/-- Weight scaling agrees with the selected scalar on the actual idempotent image. -/
theorem integrableWeight_project (f : X → Coefficients.Ring) (μ : X)
    (x : IntegrableQuotient D hD Λ) :
    integrableWeight D hD Λ f
      (integrableRepresentation D hD Λ (one D Coefficients.q pi μ) x) =
      f μ • integrableRepresentation D hD Λ (one D Coefficients.q pi μ) x := by
  induction x using integrable_induction D hD Λ with
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
    (x : IntegrableQuotient D hD Λ) :
    integrableRepresentation D hD Λ (one D Coefficients.q pi μ)
      (integrableChevalley D hD Λ positive i x) =
      integrableChevalley D hD Λ positive i
        (integrableRepresentation D hD Λ
          (one D Coefficients.q pi (μ - halfRoot D positive i)) x) := by
  obtain ⟨x⟩ := x
  change integrableRepresentation D hD Λ _
    (integrableChevalley D hD Λ positive i (toIntegrable D hD Λ x)) =
    integrableChevalley D hD Λ positive i
      (integrableRepresentation D hD Λ _ (toIntegrable D hD Λ x))
  simp only [integrableChevalley_mk, integrableRepresentation_toIntegrable, representation_one]
  exact congrArg (toIntegrable D hD Λ)
    (congrArg (fun f ↦ f x) (project_chevalley D hD Λ positive i μ))

/-- All toral covariance follows from the genuine finite quotient grading. -/
theorem integrableWeight_chevalley (f : X → Coefficients.Ring) (positive : Bool)
    (i : I) (x : IntegrableQuotient D hD Λ) :
    integrableWeight D hD Λ f (integrableChevalley D hD Λ positive i x) =
      integrableChevalley D hD Λ positive i
        (integrableWeight D hD Λ (fun μ ↦ f (μ + halfRoot D positive i)) x) := by
  induction x using integrable_weight_induction D hD Λ with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | project μ x =>
    have hp : integrableRepresentation D hD Λ
        (one D Coefficients.q pi (μ + halfRoot D positive i))
        (integrableChevalley D hD Λ positive i
          (integrableRepresentation D hD Λ (one D Coefficients.q pi μ) x)) =
        integrableChevalley D hD Λ positive i
          (integrableRepresentation D hD Λ (one D Coefficients.q pi μ) x) := by
      rw [integrableProject_chevalley, add_sub_cancel_right]
      congr 1
      rw [← Module.End.mul_apply, ← map_mul, one_mul_one_self]
    calc
      _ = integrableWeight D hD Λ f
          (integrableRepresentation D hD Λ (one D Coefficients.q pi (μ + halfRoot D positive i))
            (integrableChevalley D hD Λ positive i
              (integrableRepresentation D hD Λ (one D Coefficients.q pi μ) x))) :=
        congrArg (integrableWeight D hD Λ f) hp.symm
      _ = _ := by rw [integrableWeight_project, hp, integrableWeight_project, map_smul]

/-- Koszul covariance for both global Chevalley operators. -/
theorem integrableParity_chevalley (i j : I) (positive : Bool)
    (x : IntegrableQuotient D hD Λ) :
    integrableParity D hD Λ i (integrableChevalley D hD Λ positive j x) =
      pi ^ (D.parity i * D.parity j).val • integrableChevalley D hD Λ positive j
        (integrableParity D hD Λ i x) := by
  obtain ⟨x⟩ := x
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  change integrableParity D hD Λ i (toIntegrable D hD Λ
      (chevalley D hD Λ positive j (D.toSerreF Coefficients.q pi x))) =
    pi ^ (D.parity i * D.parity j).val • integrableChevalley D hD Λ positive j
      (integrableParity D hD Λ i (toIntegrable D hD Λ (D.toSerreF Coefficients.q pi x)))
  induction x using induction_monomial with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | smul c x hx => simp only [map_smul, hx, smul_comm c]
  | word w =>
    have hp : integrableRepresentation D hD Λ
        (one D Coefficients.q pi (Λ - halfWeight D true (wordWeight w)))
        (toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) =
        toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) := by
      simp [integrableRepresentation_toIntegrable, representation_one,
        weightProject_mk, weightProjectFree_monomial]
    have hs : integrableRepresentation D hD Λ
        (one D Coefficients.q pi (Λ - halfWeight D true (wordWeight w)))
        (integrableParity D hD Λ i
          (toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)))) =
        integrableParity D hD Λ i
          (toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) := by
      change integrableRepresentation D hD Λ _ (integrableSign D hD Λ _ _ _) = _
      simp only [integrableParity, integrableSign_word, map_smul, hp]
    rw [← integrableChevalley_mk]
    have he := integrableChevalley_project D hD Λ positive j
      (Λ - halfWeight D true (wordWeight w))
      (toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)))
    rw [hp] at he
    rw [he]
    have he' := integrableChevalley_project D hD Λ positive j
      (Λ - halfWeight D true (wordWeight w))
      (integrableParity D hD Λ i
        (toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))))
    rw [hs] at he'
    rw [he']
    cases positive
    · exact integrableParity_F D hD Λ i j _ _
    · exact integrableParity_E D hD Λ i j _ _

private theorem halfEnd_integrabilityRelations (positive : Bool)
    (u : D.serreF Coefficients.q pi) :
    integrabilityRelations D hD Λ ≤ (integrabilityRelations D hD Λ).comap
      (halfEnd D hD Λ positive u) := by
  obtain ⟨u, rfl⟩ := D.toSerreF_surjective Coefficients.q pi u
  intro x hx
  change halfEnd D hD Λ positive (D.toSerreF Coefficients.q pi u) x ∈ integrabilityRelations D hD Λ
  induction u using FreeAlgebra.induction generalizing x with
  | grade0 c => simpa using Submodule.smul_mem (integrabilityRelations D hD Λ) c hx
  | grade1 i => exact chevalley_integrabilityRelations D hD Λ positive i hx
  | add a b ha hb => simp only [map_add, LinearMap.add_apply]; exact add_mem (ha hx) (hb hx)
  | mul a b ha hb => simp only [map_mul, Module.End.mul_apply]; exact ha (hb hx)

/-- Both actual Serre halves act globally on the source-generated quotient. -/
def integrableHalfEnd (positive : Bool) :
    D.serreF Coefficients.q pi →ₐ[Coefficients.Ring]
      Module.End Coefficients.Ring (IntegrableQuotient D hD Λ) where
  toFun u := (integrabilityRelations D hD Λ).mapQ _ (halfEnd D hD Λ positive u)
    (halfEnd_integrabilityRelations D hD Λ positive u)
  map_zero' := by ext ⟨x⟩; simp
  map_one' := by ext ⟨x⟩; simp
  map_add' u v := by ext ⟨x⟩; simp
  map_mul' u v := by ext ⟨x⟩; simp
  commutes' c := by ext ⟨x⟩; simp

@[simp] theorem integrableHalfEnd_θ (positive : Bool) (i : I) :
    integrableHalfEnd D hD Λ positive (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i)) =
      integrableChevalley D hD Λ positive i := rfl

/-- All single-factor global Serre relations hold, before constructing any tensor action. -/
theorem integrableChevalley_serre (positive : Bool) {i j : I} (hij : i ≠ j) :
    ∑ r ∈ Finset.range (D.serreDeg i j + 1),
      D.serreCoeff Coefficients.q pi i j r •
        (integrableChevalley D hD Λ positive i ^ (D.serreDeg i j - r) *
          integrableChevalley D hD Λ positive j * integrableChevalley D hD Λ positive i ^ r) = 0 := by
  have hs := congrArg (integrableHalfEnd D hD Λ positive)
    (D.toSerreF_serreElt Coefficients.q pi hij)
  simpa only [SuperCartanDatum.serreElt, map_sum, map_smul, map_mul, map_pow,
    integrableHalfEnd_θ, map_zero] using hs

end OddMath.CoveringQuantum.UDot.GenericVerma
