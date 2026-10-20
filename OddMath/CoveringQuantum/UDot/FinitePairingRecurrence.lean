/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.SesquilinearForm

/-!
# Finite triangular-coordinate pairing recurrence

The actual left action on finite triangular coordinates is computed columnwise.
Its positive generator is the parity-twisted leading creation plus the two
skew-derivative corrections. The corrections lower negative word degree on the
Serre quotient, and weight projection preserves this filtration without root
independence. Every finite family has a uniform degree bound.

`positiveModifiedForm_F_recurrence` removes one negative generator from the first
argument of the actual bilinear form, keeping the complete positive action in
the second. Together with `coordinateAction_E_leading` this is a degree-controlled
normal-order recurrence, not an identification with a tensor-product Gram form.
The mixed commutator mechanism is that of Clark–Hill–Wang, Quantum supergroups I,
Proposition 2.2.2; the formulas here use the existing inverse-q half-form convention.

This does not prove full-form nondegeneracy: lower word degree is not higher
q-valuation, and this filtration is not orthogonal for the form. The valuation
control supplied by canonical bases and tensor polarizations in Clark, Quantum
supergroups IV, Propositions 5.10–5.11 and Theorem 5.12, is not asserted here.
The form and action are defined for arbitrary colours without bar consistency
over the generic covering ring. No canonical basis, detecting family, or Gram invertibility
is assumed.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients TensorProduct PreF
variable {I : Type*} [DecidableEq I]
variable (C : SuperCartanDatum I)

/-- Word-length filtration of the actual Serre half. -/
def halfWordDegree (n : ℕ) : Submodule Coefficients.Ring (C.serreF Coefficients.q pi) :=
  Submodule.span Coefficients.Ring {x | ∃ w : List I, w.length ≤ n ∧
    x = C.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)}

omit [DecidableEq I] in
private theorem monomial_mem_halfWordDegree (n : ℕ) (w : List I) (hw : w.length ≤ n) :
    C.toSerreF Coefficients.q pi (monomial Coefficients.Ring w) ∈ halfWordDegree C n :=
  Submodule.subset_span ⟨w, hw, rfl⟩

omit [DecidableEq I] in
private theorem diagonal_mem_halfWordDegree (n : ℕ) (c : I → Coefficients.Ring)
    {x : C.serreF Coefficients.q pi} (hx : x ∈ halfWordDegree C n) :
    diagonal C c x ∈ halfWordDegree C n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [diagonal_mk, diagTwist_monomial, map_smul]
    exact Submodule.smul_mem _ _ (monomial_mem_halfWordDegree C n w hw)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

omit [DecidableEq I] in
private theorem create_mem_halfWordDegree (n : ℕ) (i : I)
    {x : C.serreF Coefficients.q pi} (hx : x ∈ halfWordDegree C n) :
    create C i x ∈ halfWordDegree C (n + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    change C.toSerreF Coefficients.q pi (θ Coefficients.Ring i) * _ ∈ _
    rw [← map_mul, ← monomial_cons]
    exact monomial_mem_halfWordDegree C (n + 1) (i :: w) (by simpa using Nat.succ_le_succ hw)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

private theorem numerator_monomial_mem (i : I) (a b : Coefficients.Ring) (n : ℕ)
    (w : List I) (hw : w.length ≤ n + 1) :
    numerator C i a b (C.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) ∈
      halfWordDegree C n := by
  induction n generalizing w with
  | zero =>
    cases w with
    | nil => simp [monomial]
    | cons j w =>
      have hw0 : w = [] := List.length_eq_zero_iff.mp (by simpa using hw)
      subst w
      simp only [monomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      have he := numerator_create C i j a b 1
      simp only [mul_one, numerator_one, mul_zero, smul_zero, zero_add, map_one] at he
      rw [he]
      split_ifs
      · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (by
          simpa [monomial] using monomial_mem_halfWordDegree C 0 [] (by simp)))
          (Submodule.smul_mem _ _ (by
          simpa [monomial] using monomial_mem_halfWordDegree C 0 [] (by simp)))
      · exact Submodule.zero_mem _
  | succ n ih =>
    cases w with
    | nil => simp [monomial]
    | cons j w =>
      have hw' : w.length ≤ n + 1 := by simpa using hw
      rw [monomial_cons, map_mul, numerator_create]
      apply Submodule.add_mem
      · exact Submodule.smul_mem _ _ (create_mem_halfWordDegree C n j (ih w hw'))
      · split_ifs
        · exact Submodule.sub_mem _
            (Submodule.smul_mem _ _ (diagonal_mem_halfWordDegree C (n + 1) _
              (monomial_mem_halfWordDegree C (n + 1) w hw')))
            (Submodule.smul_mem _ _ (diagonal_mem_halfWordDegree C (n + 1) _
              (monomial_mem_halfWordDegree C (n + 1) w hw')))
        · exact Submodule.zero_mem _

/-- The actual descended skew numerator lowers word degree, including cancellation
and arbitrary inhomogeneous linear combinations in the Serre quotient. -/
theorem numerator_mem_halfWordDegree (i : I) (a b : Coefficients.Ring) (n : ℕ)
    {x : C.serreF Coefficients.q pi} (hx : x ∈ halfWordDegree C (n + 1)) :
    numerator C i a b x ∈ halfWordDegree C n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact numerator_monomial_mem C i a b n w hw
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

/-- The first (negative) tensor factor has word degree at most `n`.
The second factor is unrestricted; this is a submodule of the actual tensor quotient. -/
def negativeTensorDegree (n : ℕ) : Submodule Coefficients.Ring
    (C.serreF Coefficients.q pi ⊗[Coefficients.Ring] C.serreF Coefficients.q pi) :=
  Submodule.span Coefficients.Ring {z | ∃ (w : List I) (y : C.serreF Coefficients.q pi),
    w.length ≤ n ∧
      z = C.toSerreF Coefficients.q pi (monomial Coefficients.Ring w) ⊗ₜ[Coefficients.Ring] y}

omit [DecidableEq I] in
private theorem tmul_mem_negativeTensorDegree (n : ℕ) {x : C.serreF Coefficients.q pi}
    (hx : x ∈ halfWordDegree C n) (y : C.serreF Coefficients.q pi) :
    x ⊗ₜ[Coefficients.Ring] y ∈ negativeTensorDegree C n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact Submodule.subset_span ⟨w, y, hw, rfl⟩
  | zero => simp
  | add x z hx hz ihx ihz => simpa only [add_tmul] using Submodule.add_mem _ ihx ihz
  | smul c x hx ih => simpa only [smul_tmul'] using Submodule.smul_mem _ c ih

/-- Every skew correction lowers the negative tensor degree, for arbitrary
finite sums of tensors, not merely a pure tensor or a rank-one family. -/
theorem numerator_map_mem_negativeTensorDegree (n : ℕ) (i : I) (a b : Coefficients.Ring)
    (g : Module.End Coefficients.Ring (C.serreF Coefficients.q pi))
    {z : C.serreF Coefficients.q pi ⊗[Coefficients.Ring] C.serreF Coefficients.q pi}
    (hz : z ∈ negativeTensorDegree C (n + 1)) :
    TensorProduct.map (numerator C i a b) g z ∈ negativeTensorDegree C n := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, y, hw, rfl⟩ := hz
    rw [TensorProduct.map_tmul]
    exact tmul_mem_negativeTensorDegree C n (numerator_monomial_mem C i a b n w hw) _
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

omit [DecidableEq I] in
/-- The negative-degree submodules form an increasing filtration. -/
theorem negativeTensorDegree_mono {m n : ℕ} (hmn : m ≤ n) :
    negativeTensorDegree C m ≤ negativeTensorDegree C n := by
  apply Submodule.span_le.mpr
  rintro z ⟨w, y, hw, rfl⟩
  exact Submodule.subset_span ⟨w, y, hw.trans hmn, rfl⟩

omit [DecidableEq I] in
/-- Every actual tensor, including an inhomogeneous sum, has finite negative degree. -/
theorem exists_negativeTensorDegree
    (z : C.serreF Coefficients.q pi ⊗[Coefficients.Ring] C.serreF Coefficients.q pi) :
    ∃ n, z ∈ negativeTensorDegree C n := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw =>
    obtain ⟨m, hm⟩ := hz
    obtain ⟨n, hn⟩ := hw
    exact ⟨max m n, Submodule.add_mem _
      (negativeTensorDegree_mono C (le_max_left m n) hm)
      (negativeTensorDegree_mono C (le_max_right m n) hn)⟩
  | tmul x y =>
    obtain ⟨x, rfl⟩ := C.toSerreF_surjective Coefficients.q pi x
    induction x using induction_monomial with
    | zero => exact ⟨0, by simp⟩
    | word w => exact ⟨w.length, Submodule.subset_span ⟨w, y, le_rfl, rfl⟩⟩
    | add x z hx hz =>
      obtain ⟨m, hm⟩ := hx
      obtain ⟨n, hn⟩ := hz
      refine ⟨max m n, ?_⟩
      simpa only [map_add, add_tmul] using Submodule.add_mem _
        (negativeTensorDegree_mono C (le_max_left m n) hm)
        (negativeTensorDegree_mono C (le_max_right m n) hn)
    | smul c x hx =>
      obtain ⟨n, hn⟩ := hx
      exact ⟨n, by simpa only [map_smul, smul_tmul'] using Submodule.smul_mem _ c hn⟩

end OddMath.CoveringQuantum.UDot.GenericTensor

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients TensorProduct PreF
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

/-- Left multiplication is the actual regular action on every finite coordinate. -/
theorem triangularCoordinates_mul (u x : modified D Coefficients.q pi) (μ : X) :
    triangularCoordinates D (u * x) μ =
      modifiedRepresentation D μ u (triangularCoordinates D x μ) := by
  simp only [triangularCoordinates_eq_vacuum, map_mul, Module.End.mul_apply]

/-- The concrete coordinate action, retaining finite support. -/
def coordinateAction (u : modified D Coefficients.q pi) :
    (X →₀ D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) →ₗ[
      Coefficients.Ring]
      (X →₀ D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :=
  Finsupp.lsum Coefficients.Ring fun μ ↦
    (Finsupp.lsingle μ).comp (modifiedRepresentation D μ u)

@[simp] theorem coordinateAction_apply (u : modified D Coefficients.q pi)
    (f : X →₀ D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) (μ : X) :
    coordinateAction D u f μ = modifiedRepresentation D μ u (f μ) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg]
  | single η z =>
    simp only [coordinateAction, Finsupp.lsum_single, LinearMap.comp_apply,
      Finsupp.lsingle_apply]
    by_cases h : η = μ
    · subst η; simp
    · simp [Ne.symm h]

/-- Left multiplication on every finite coordinate family is this concrete action. -/
theorem mul_globalTriangular
    (u : modified D Coefficients.q pi)
    (f : X →₀ D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :
    u * globalTriangular D f = globalTriangular D (coordinateAction D u f) := by
  apply (globalTriangularEquiv D).symm.injective
  change triangularCoordinates D _ = triangularCoordinates D _
  rw [triangularCoordinates_globalTriangular]
  ext μ
  rw [triangularCoordinates_mul, triangularCoordinates_globalTriangular, coordinateAction_apply]

/-- The exact raising part in normal order. -/
def positiveLeading (i : I) : Module.End Coefficients.Ring
    (D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :=
  TensorProduct.map (parity D.toSuperCartanDatum i).toLinearMap (create D.toSuperCartanDatum i)

/-- The two skew-derivative terms, with their right-weight parameters. -/
def positiveCorrection (μ : X) (i : I) : Module.End Coefficients.Ring
    (D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :=
  Ring.inverse (vermaDenominator D.toSuperCartanDatum Coefficients.q pi i) •
    (TensorProduct.map (numerator D.toSuperCartanDatum i
      (((D.qi Coefficients.q i) ^ D.h i μ : Coefficients.Ringˣ) : Coefficients.Ring) 0)
      (weight D.toSuperCartanDatum Coefficients.q i).toLinearMap +
    TensorProduct.map (numerator D.toSuperCartanDatum i 0
      (D.pii pi i ^ (D.h i μ).natAbs *
        (((D.qi Coefficients.q i) ^ (-D.h i μ) : Coefficients.Ringˣ) : Coefficients.Ring)))
      (weight D.toSuperCartanDatum Coefficients.q⁻¹ i).toLinearMap)

omit [DecidableEq X] in
theorem positive_eq_leading_add_correction (μ : X) (i : I) :
    positive D.toSuperCartanDatum (fun j ↦ D.h j μ) i =
      positiveLeading D i + positiveCorrection D μ i := rfl

/-- A negative generator in the first argument is removed using the exact
positive normal-order operator on arbitrary finite triangular input. -/
theorem positiveModifiedForm_F_recurrence (i : I) (ν : X)
    (x : modified D Coefficients.q pi)
    (f : X →₀ D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :
    positiveModifiedForm D
      (⟨F D Coefficients.q pi i ν, F_mem_modified D Coefficients.q pi i ν⟩ * x)
      (globalTriangular D f) =
    qp Coefficients.q (D.d i * (D.h i ν - 1)) *
      positiveModifiedForm D x (globalTriangular D (coordinateAction D
        ⟨E D Coefficients.q pi i (ν - D.α i),
          E_mem_modified D Coefficients.q pi i (ν - D.α i)⟩ f)) := by
  rw [positiveModifiedForm_adjoint]
  have hr : rhoModified D Coefficients.q pi pi_sq
      ⟨F D Coefficients.q pi i ν, F_mem_modified D Coefficients.q pi i ν⟩ =
      qp Coefficients.q (D.d i * (D.h i ν - 1)) •
        (⟨E D Coefficients.q pi i (ν - D.α i), E_mem_modified D Coefficients.q pi i (ν - D.α i)⟩ :
          modified D Coefficients.q pi) := Subtype.ext (rho_F pi_sq i ν)
  rw [hr, smul_mul_assoc, map_smul, smul_eq_mul, mul_globalTriangular]

/-- The recurrence is reversible for zero testing over the covering ring:
its prefactor is a unit, so no cancellation by a mere nonzero scalar is used.
This reduces a specified pairing, not the radical of the full form. -/
theorem positiveModifiedForm_F_eq_zero_iff (i : I) (ν : X)
    (x : modified D Coefficients.q pi)
    (f : X →₀ D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :
    positiveModifiedForm D
      (⟨F D Coefficients.q pi i ν, F_mem_modified D Coefficients.q pi i ν⟩ * x)
      (globalTriangular D f) = 0 ↔
    positiveModifiedForm D x (globalTriangular D (coordinateAction D
      ⟨E D Coefficients.q pi i (ν - D.α i),
          E_mem_modified D Coefficients.q pi i (ν - D.α i)⟩ f)) = 0 := by
  rw [positiveModifiedForm_F_recurrence]
  exact (Units.isUnit (Coefficients.q ^ (D.d i * (D.h i ν - 1)))).mul_right_eq_zero

/-- Both the leading term and the lower correction occur at each actual column. -/
theorem coordinateAction_E_apply (i : I) (ν μ : X)
    (f : X →₀ D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :
    coordinateAction D
      ⟨E D Coefficients.q pi i ν, E_mem_modified D Coefficients.q pi i ν⟩ f μ =
      positiveLeading D i (weightProject D μ ν (f μ)) +
        positiveCorrection D μ i (weightProject D μ ν (f μ)) := by
  rw [coordinateAction_apply]
  change representation D μ (E D Coefficients.q pi i ν) (f μ) = _
  rw [representation_E, Module.End.mul_apply, positive_eq_leading_add_correction,
    LinearMap.add_apply]

omit [DecidableEq I] [DecidableEq X] in
/-- Weight projection preserves the negative word filtration even when distinct
root degrees have the same weight in `X`. -/
theorem weightProject_mem_negativeTensorDegree (n : ℕ) (μ ν : X)
    {z : D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi}
    (hz : z ∈ negativeTensorDegree D.toSuperCartanDatum n) :
    weightProject D μ ν z ∈ negativeTensorDegree D.toSuperCartanDatum n := by
  classical
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, y, ha, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := D.toSerreF_surjective Coefficients.q pi y
    induction y using induction_monomial with
    | zero => simp
    | add y z hy hz => simpa only [map_add, tmul_add] using Submodule.add_mem _ hy hz
    | smul c y hy => simpa only [map_smul, tmul_smul] using Submodule.smul_mem _ c hy
    | word b =>
      rw [weightProject_monomial]
      split_ifs
      · exact Submodule.subset_span ⟨a, _, ha, rfl⟩
      · exact Submodule.zero_mem _
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

omit [DecidableEq X] in
/-- The full normal-order correction strictly lowers negative word degree. -/
theorem positiveCorrection_mem_negativeTensorDegree (n : ℕ) (μ : X) (i : I)
    {z : D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi}
    (hz : z ∈ negativeTensorDegree D.toSuperCartanDatum (n + 1)) :
    positiveCorrection D μ i z ∈ negativeTensorDegree D.toSuperCartanDatum n := by
  apply Submodule.smul_mem
  apply Submodule.add_mem
  · exact numerator_map_mem_negativeTensorDegree D.toSuperCartanDatum n i _ _ _ hz
  · exact numerator_map_mem_negativeTensorDegree D.toSuperCartanDatum n i _ _ _ hz

/-- The exact action on every column of an arbitrary finite family is its
leading term plus an element of strictly smaller negative degree. -/
theorem coordinateAction_E_leading (n : ℕ) (i : I) (ν μ : X)
    (f : X →₀ D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi)
    (hf : f μ ∈ negativeTensorDegree D.toSuperCartanDatum (n + 1)) :
    ∃ r ∈ negativeTensorDegree D.toSuperCartanDatum n,
      coordinateAction D
        ⟨E D Coefficients.q pi i ν, E_mem_modified D Coefficients.q pi i ν⟩ f μ =
      positiveLeading D i (weightProject D μ ν (f μ)) + r := by
  exact ⟨_, positiveCorrection_mem_negativeTensorDegree D n μ i
    (weightProject_mem_negativeTensorDegree D (n + 1) μ ν hf),
    coordinateAction_E_apply D i ν μ f⟩

omit [DecidableEq I] [DecidableEq X] in
/-- A single bound works for every column in an arbitrary finite coordinate family. -/
theorem finiteFamily_degree_bound
    (f : X →₀ D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :
    ∃ n, ∀ μ, f μ ∈ negativeTensorDegree D.toSuperCartanDatum n := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => exact ⟨0, fun μ ↦ by simp⟩
  | add f g hf hg =>
    obtain ⟨m, hm⟩ := hf
    obtain ⟨n, hn⟩ := hg
    exact ⟨max m n, fun μ ↦ Submodule.add_mem _
      (negativeTensorDegree_mono _ (le_max_left m n) (hm μ))
      (negativeTensorDegree_mono _ (le_max_right m n) (hn μ))⟩
  | single μ z =>
    obtain ⟨n, hn⟩ := exists_negativeTensorDegree D.toSuperCartanDatum z
    refine ⟨n, fun ν ↦ ?_⟩
    by_cases h : μ = ν
    · subst ν; simpa using hn
    · simp [Ne.symm h]

/-- Uniform leading/correction control on every actual finite family. No basis,
detecting family, or bound is supplied as an additional hypothesis. This is an
action recurrence, not nondegeneracy of the bilinear form. -/
theorem finiteFamily_E_leading
    (f : X →₀ D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :
    ∃ n, ∀ (i : I) (ν μ : X),
      ∃ r ∈ negativeTensorDegree D.toSuperCartanDatum n,
        coordinateAction D
          ⟨E D Coefficients.q pi i ν, E_mem_modified D Coefficients.q pi i ν⟩ f μ =
        positiveLeading D i (weightProject D μ ν (f μ)) + r := by
  obtain ⟨n, hn⟩ := finiteFamily_degree_bound D f
  exact ⟨n, fun i ν μ ↦ coordinateAction_E_leading D n i ν μ f
    (negativeTensorDegree_mono _ (Nat.le_succ n) (hn μ))⟩

end OddMath.CoveringQuantum.UDot.GenericTensor
