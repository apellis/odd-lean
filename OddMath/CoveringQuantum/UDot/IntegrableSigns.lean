import OddMath.CoveringQuantum.UDot.IntegrablePolarization

/-!
# Koszul and J-normalization operators on the actual quotient

Every square-one diagonal character of the free generators preserves the
accepted action-generated integrability-relation submodule. The proof checks
weight projections, skew-derivative lowering and creation, then the entire
original representation and the generating powers. Thus the character descends
to an involution on arbitrary, including inhomogeneous, quotient vectors.

`integrableParity` supplies the actual Koszul pi^(p(i)*p(j)) covariance for
both Chevalley generators, including two odd indices. `integrableJ` descends the
already accepted word-sign normalization and fixes the original vacuum. No root
independence, even highest-coordinate restriction or pi specialization is used.

These are the missing quotient operators required to formulate the genuine
mixed tensor action/pairing in Clark, arXiv:1312.4855v2, §5.3 Propositions 5.10–5.11.
They are not an assumed action-compatibility structure, a tensor representation,
a full grading decomposition, or a proof of the mixed Gram limit.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot
open Coefficients PreF
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent) (Λ : X)

namespace GenericVerma

omit [DecidableEq X] in
private theorem lower_diagonal (c : I → Coefficients.Ring) (i : I) (n : ℤ)
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

private theorem diagonal_project (c : I → Coefficients.Ring) (μ : X)
    (x : D.serreF Coefficients.q pi) :
    GenericTensor.diagonal D.toSuperCartanDatum c (weightProject D hD Λ μ x) =
      weightProject D hD Λ μ (GenericTensor.diagonal D.toSuperCartanDatum c x) := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  simp only [GenericTensor.diagonal_mk, weightProject_mk, weightProjectFree_diag]

omit [DecidableEq X] in
private theorem diagonal_lower (c : I → Coefficients.Ring) (hc : ∀ i, c i ^ 2 = 1)
    (i : I) (n : ℤ) (x : D.serreF Coefficients.q pi) :
    GenericTensor.diagonal D.toSuperCartanDatum c (lower D.toSuperCartanDatum hD i n x) =
      c i • lower D.toSuperCartanDatum hD i n (GenericTensor.diagonal D.toSuperCartanDatum c x) := by
  rw [lower_diagonal, smul_smul, ← pow_two, hc, one_smul]

/-- Every involutive diagonal character preserves the actual action-generated relations.
In particular this supplies both the Koszul parity and the lowest J-normalization. -/
theorem diagonal_integrabilityRelations (c : I → Coefficients.Ring) (hc : ∀ i, c i ^ 2 = 1) :
    integrabilityRelations D hD Λ ≤ (integrabilityRelations D hD Λ).comap
      (GenericTensor.diagonal D.toSuperCartanDatum c).toLinearMap := by
  apply integrabilityRelations_le D hD Λ
  · intro i
    change GenericTensor.diagonal D.toSuperCartanDatum c (integrabilityGenerator D Λ i) ∈ integrabilityRelations D hD Λ
    simp only [integrabilityGenerator, GenericTensor.diagonal_mk, map_pow, diagTwist_θ,
      smul_pow, map_smul]
    simpa only [integrabilityGenerator, map_pow] using
      Submodule.smul_mem (integrabilityRelations D hD Λ) (c i ^ ((D.h i Λ).toNat + 1))
        (integrabilityGenerator_mem D hD Λ i)
  · intro u x hx
    change GenericTensor.diagonal D.toSuperCartanDatum c (representation D hD Λ u x) ∈ integrabilityRelations D hD Λ
    change GenericTensor.diagonal D.toSuperCartanDatum c x ∈ integrabilityRelations D hD Λ at hx
    obtain ⟨u, rfl⟩ := mk_surjective D Coefficients.q pi u
    induction u using FreeAlgebra.induction generalizing x with
    | grade0 a =>
      simpa using Submodule.smul_mem (integrabilityRelations D hD Λ) a hx
    | grade1 g =>
      cases g with
      | one μ =>
        change GenericTensor.diagonal D.toSuperCartanDatum c
          (representation D hD Λ (one D Coefficients.q pi μ) x) ∈ integrabilityRelations D hD Λ
        rw [representation_one, diagonal_project, ← representation_one]
        exact integrabilityRelations_invariant D hD Λ _ hx
      | e i μ =>
        change GenericTensor.diagonal D.toSuperCartanDatum c
          (representation D hD Λ (E D Coefficients.q pi i μ) x) ∈ integrabilityRelations D hD Λ
        rw [representation_E, Module.End.mul_apply, diagonal_lower D hD c hc,
          diagonal_project]
        apply Submodule.smul_mem
        simpa only [Submodule.mem_comap, representation_E, Module.End.mul_apply] using
          integrabilityRelations_invariant D hD Λ (E D Coefficients.q pi i μ) hx
      | f i μ =>
        change GenericTensor.diagonal D.toSuperCartanDatum c
          (representation D hD Λ (F D Coefficients.q pi i μ) x) ∈ integrabilityRelations D hD Λ
        rw [representation_F, map_mul, GenericTensor.diagonal_θ, smul_mul_assoc,
          diagonal_project]
        apply Submodule.smul_mem
        simpa only [Submodule.mem_comap, representation_F] using
          integrabilityRelations_invariant D hD Λ (F D Coefficients.q pi i μ) hx
    | add a b ha hb =>
      simp only [map_add, LinearMap.add_apply]
      exact add_mem (ha hx) (hb hx)
    | mul a b ha hb =>
      simp only [map_mul, Module.End.mul_apply]
      exact ha (hb hx)

/-- The diagonal character on the original quotient, with descent proved above. -/
def integrableSign (c : I → Coefficients.Ring) (hc : ∀ i, c i ^ 2 = 1) :
    Module.End Coefficients.Ring (IntegrableQuotient D hD Λ) :=
  (integrabilityRelations D hD Λ).mapQ _
    (GenericTensor.diagonal D.toSuperCartanDatum c).toLinearMap
    (diagonal_integrabilityRelations D hD Λ c hc)

@[simp] theorem integrableSign_mk (c : I → Coefficients.Ring) (hc : ∀ i, c i ^ 2 = 1)
    (x : D.serreF Coefficients.q pi) :
    integrableSign D hD Λ c hc (toIntegrable D hD Λ x) =
      toIntegrable D hD Λ (GenericTensor.diagonal D.toSuperCartanDatum c x) := rfl

/-- The sign map is computed on all free words; no root-independence is needed. -/
theorem integrableSign_word (c : I → Coefficients.Ring) (hc : ∀ i, c i ^ 2 = 1)
    (w : List I) :
    integrableSign D hD Λ c hc
      (toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) =
      (w.map c).prod •
        toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) := by
  simp only [integrableSign_mk, GenericTensor.diagonal_mk, diagTwist_monomial, map_smul]

/-- The quotient character is an involution, also on inhomogeneous quotient vectors. -/
@[simp] theorem integrableSign_involutive (c : I → Coefficients.Ring) (hc : ∀ i, c i ^ 2 = 1)
    (x : IntegrableQuotient D hD Λ) :
    integrableSign D hD Λ c hc (integrableSign D hD Λ c hc x) = x := by
  obtain ⟨x⟩ := x
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  change integrableSign D hD Λ c hc (integrableSign D hD Λ c hc
    (toIntegrable D hD Λ (D.toSerreF Coefficients.q pi x))) = _
  simp only [integrableSign_mk, GenericTensor.diagonal_mk, diagTwist_diagTwist]
  have he : c * c = 1 := by funext i; simpa only [Pi.mul_apply, Pi.one_apply, ← pow_two] using hc i
  rw [he]
  have hi : diagTwist (1 : I → Coefficients.Ring) = AlgHom.id _ _ := by
    ext i
    simp [diagTwist_θ]
  rw [hi]
  rfl

/-- The descended character has the actual E covariance on every quotient vector. -/
theorem integrableSign_E (c : I → Coefficients.Ring) (hc : ∀ i, c i ^ 2 = 1)
    (i : I) (μ : X) (x : IntegrableQuotient D hD Λ) :
    integrableSign D hD Λ c hc (integrableRepresentation D hD Λ (E D Coefficients.q pi i μ) x) =
      c i • integrableRepresentation D hD Λ (E D Coefficients.q pi i μ)
        (integrableSign D hD Λ c hc x) := by
  obtain ⟨x⟩ := x
  change integrableSign D hD Λ c hc
    (integrableRepresentation D hD Λ (E D Coefficients.q pi i μ) (toIntegrable D hD Λ x)) =
      c i • integrableRepresentation D hD Λ (E D Coefficients.q pi i μ)
        (integrableSign D hD Λ c hc (toIntegrable D hD Λ x))
  rw [integrableRepresentation_E_mk, integrableSign_mk, integrableSign_mk,
    integrableRepresentation_E_mk, diagonal_lower D hD c hc, diagonal_project, map_smul]

/-- The descended character has the actual F covariance on every quotient vector. -/
theorem integrableSign_F (c : I → Coefficients.Ring) (hc : ∀ i, c i ^ 2 = 1)
    (i : I) (μ : X) (x : IntegrableQuotient D hD Λ) :
    integrableSign D hD Λ c hc (integrableRepresentation D hD Λ (F D Coefficients.q pi i μ) x) =
      c i • integrableRepresentation D hD Λ (F D Coefficients.q pi i μ)
        (integrableSign D hD Λ c hc x) := by
  obtain ⟨x⟩ := x
  change integrableSign D hD Λ c hc
    (integrableRepresentation D hD Λ (F D Coefficients.q pi i μ) (toIntegrable D hD Λ x)) =
      c i • integrableRepresentation D hD Λ (F D Coefficients.q pi i μ)
        (integrableSign D hD Λ c hc (toIntegrable D hD Λ x))
  rw [integrableRepresentation_F_mk, integrableSign_mk, integrableSign_mk,
    integrableRepresentation_F_mk, map_mul, GenericTensor.diagonal_θ,
    smul_mul_assoc, diagonal_project, map_smul]

omit [DecidableEq I] [DecidableEq X] [Finite I] in
private theorem parityCharacter_sq (i j : I) : (pi ^ (D.parity i * D.parity j).val) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm _ 2, pow_mul, pi_sq, one_pow]

/-- The first-factor Koszul operator required by the covering tensor action. -/
def integrableParity (i : I) : Module.End Coefficients.Ring (IntegrableQuotient D hD Λ) :=
  integrableSign D hD Λ (fun j ↦ pi ^ (D.parity i * D.parity j).val) (parityCharacter_sq D i)

/-- In particular two odd indices produce pi, not an omitted sign. -/
theorem integrableParity_E (i j : I) (μ : X) (x : IntegrableQuotient D hD Λ) :
    integrableParity D hD Λ i (integrableRepresentation D hD Λ (E D Coefficients.q pi j μ) x) =
      pi ^ (D.parity i * D.parity j).val •
        integrableRepresentation D hD Λ (E D Coefficients.q pi j μ) (integrableParity D hD Λ i x) :=
  integrableSign_E D hD Λ _ _ j μ x

theorem integrableParity_F (i j : I) (μ : X) (x : IntegrableQuotient D hD Λ) :
    integrableParity D hD Λ i (integrableRepresentation D hD Λ (F D Coefficients.q pi j μ) x) =
      pi ^ (D.parity i * D.parity j).val •
        integrableRepresentation D hD Λ (F D Coefficients.q pi j μ) (integrableParity D hD Λ i x) :=
  integrableSign_F D hD Λ _ _ j μ x

omit [DecidableEq I] [DecidableEq X] [Finite I] in
private theorem polarizationSign_sq (i : I) : polarizationSign D Λ i ^ 2 = 1 := by
  simpa [wordSign] using wordSign_sq D Λ [i]

/-- The actual J/word normalization descends to the quotient, including pi=-1.
This is an operator, not an assertion of tensor-action compatibility. -/
def integrableJ : Module.End Coefficients.Ring (IntegrableQuotient D hD Λ) :=
  integrableSign D hD Λ (polarizationSign D Λ) (polarizationSign_sq D Λ)

theorem integrableJ_word (w : List I) :
    integrableJ D hD Λ
      (toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) =
      wordSign D Λ w •
        toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) :=
  integrableSign_word D hD Λ _ _ w

/-- The normalization fixes the original vacuum; no ad hoc norm is chosen. -/
@[simp] theorem integrableJ_vacuum :
    integrableJ D hD Λ (toIntegrable D hD Λ 1) = toIntegrable D hD Λ 1 := by
  change integrableSign D hD Λ _ _ _ = _
  rw [integrableSign_mk, map_one]

end GenericVerma
end OddMath.CoveringQuantum.UDot
