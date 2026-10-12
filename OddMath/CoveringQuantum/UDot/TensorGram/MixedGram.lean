/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.UDot.TensorPolarization
import OddMath.CoveringQuantum.UDot.VermaLimit
import OddMath.CoveringQuantum.UDot.PositiveForm

/-!
# Finite mixed tensor actions and Gram polynomials

The actual highest/lowest quotient tensor carries the native Delta1/Delta2
actions. Finite word expansions retain both toral factors and the independent
root multidegrees; no injectivity of the root map is required. The fixed-difference
filter is non-bottom precisely when a strictly positive coroot weight exists.
These finite polynomials alone do not give a uniform mixed limit.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma.MixedGram
open PreF Coefficients TensorProduct
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent) (Λ Μ : X)

abbrev RawPair (I : Type*) := PreF Coefficients.Ring I × PreF Coefficients.Ring I

def project (x : PreF Coefficients.Ring I) : IntegrableQuotient D hD Λ :=
  toIntegrable D hD Λ (D.toSerreF Coefficients.q pi x)

def freeWeight (f : X → Coefficients.Ring) :
    Module.End Coefficients.Ring (PreF Coefficients.Ring I) :=
  (FreeAlgebra.wordBasis Coefficients.Ring I).constr Coefficients.Ring
    (fun w ↦ f (Λ - halfWeight D true (wordWeight w)) • monomial Coefficients.Ring w)

omit [DecidableEq I] [DecidableEq X] [Finite I] in
@[simp] theorem freeWeight_word (f : X → Coefficients.Ring) (w : List I) :
    freeWeight D Λ f (monomial Coefficients.Ring w) =
      f (Λ - halfWeight D true (wordWeight w)) • monomial Coefficients.Ring w := by
  simpa only [FreeAlgebra.wordBasis_apply, monomial, freeWeight, θ] using
    (Module.Basis.constr_basis (FreeAlgebra.wordBasis Coefficients.Ring I)
      Coefficients.Ring (fun w ↦ f (Λ - halfWeight D true (wordWeight w)) •
        monomial Coefficients.Ring w) w)

theorem project_weight (f : X → Coefficients.Ring) (x : PreF Coefficients.Ring I) :
    project D hD Λ (freeWeight D Λ f x) = integrableWeight D hD Λ f (project D hD Λ x) := by
  induction x using induction_monomial with
  | zero => simp [project]
  | add x y hx hy => simpa only [map_add, project] using congrArg₂ (· + ·) hx hy
  | smul c x hx => simpa only [map_smul, project] using congrArg (c • ·) hx
  | word w => simp [project, integrableWeight_word]

theorem project_lower (i : I) (x : PreF Coefficients.Ring I) :
    project D hD Λ (lowerFree D.toSuperCartanDatum Coefficients.q pi i (D.h i Λ) x) =
      integrableChevalley D hD Λ true i (project D hD Λ x) := by
  simp only [project, integrableChevalley_mk, chevalley_true, lower_mk]

theorem project_create (i : I) (x : PreF Coefficients.Ring I) :
    project D hD Λ (θ Coefficients.Ring i * x) =
      integrableChevalley D hD Λ false i (project D hD Λ x) := by
  simp only [project, integrableChevalley_mk, chevalley_false_apply, map_mul]

theorem project_parity (i : I) (x : PreF Coefficients.Ring I) :
    project D hD Λ (parityTwist D.toSuperCartanDatum pi i x) =
      integrableParity D hD Λ i (project D hD Λ x) := by
  simp only [project, integrableParity, integrableSign_mk,
    GenericTensor.diagonal_mk, parityTwist]

def freeTwist (s : Bool) (i : I) :
    Module.End Coefficients.Ring (PreF Coefficients.Ring I) :=
  (freeWeight D Λ (tensorToralScalar D s i)).comp
    (parityTwist D.toSuperCartanDatum pi i).toLinearMap

def freeFTwist (s : Bool) (i : I) : Module.End Coefficients.Ring (PreF Coefficients.Ring I) :=
  (if s then 1 else D.pii pi i ^ (D.h i Λ).natAbs) •
    (parityTwist D.toSuperCartanDatum pi i).toLinearMap

def freeLowestF (i : I) : Module.End Coefficients.Ring (PreF Coefficients.Ring I) :=
  polarizationSign D (-Μ) i • lowerFree D.toSuperCartanDatum Coefficients.q pi i (D.h i Μ)

theorem project_twist (s : Bool) (i : I) (x : PreF Coefficients.Ring I) :
    project D hD Λ (freeTwist D Λ s i x) = tensorTwist D hD Λ s i (project D hD Λ x) := by
  simp only [freeTwist, LinearMap.comp_apply, project_weight, AlgHom.toLinearMap_apply,
    project_parity, tensorTwist, Module.End.mul_apply]

theorem project_ftwist (s : Bool) (i : I) (x : PreF Coefficients.Ring I) :
    project D hD Λ (freeFTwist D Λ s i x) = tensorFTwist D hD Λ s i (project D hD Λ x) := by
  simp only [freeFTwist, LinearMap.smul_apply, AlgHom.toLinearMap_apply, tensorFTwist_eq_smul]
  change toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (_ • _)) = _
  rw [map_smul, map_smul]
  exact congrArg (_ • ·) (project_parity D hD Λ i x)

theorem project_lowestF (i : I) (x : PreF Coefficients.Ring I) :
    project D hD Μ (freeLowestF D Μ i x) = lowestF D hD Μ i (project D hD Μ x) := by
  simp only [freeLowestF, LinearMap.smul_apply, lowestF_eq_smul, ← polarizationSign_eq_parl]
  change toIntegrable D hD Μ (D.toSerreF Coefficients.q pi (_ • _)) = _
  rw [map_smul, map_smul]
  exact congrArg (_ • ·) (project_lower D hD Μ i x)

/-- Two actual coproduct branches; lowerFree retains both toral terms and its denominator. -/
def step (s positive : Bool) (i : I) (z : RawPair I) : List (RawPair I) :=
  if positive then
    [(lowerFree D.toSuperCartanDatum Coefficients.q pi i (D.h i Λ) z.1, z.2),
     (freeTwist D Λ s i z.1, θ Coefficients.Ring i * z.2)]
  else
    [(θ Coefficients.Ring i * z.1, freeWeight D Μ (tensorToralScalar D false i) z.2),
     (freeFTwist D Λ s i z.1, freeLowestF D Μ i z.2)]

def pairValue (z : RawPair I) := project D hD Λ z.1 ⊗ₜ[Coefficients.Ring] project D hD Μ z.2

def listValue (zs : List (RawPair I)) := (zs.map (pairValue D hD Λ Μ)).sum

theorem step_value (s positive : Bool) (i : I) (z : RawPair I) :
    listValue D hD Λ Μ (step D Λ Μ s positive i z) =
      tensorChevalley D hD Λ Μ s positive i (pairValue D hD Λ Μ z) := by
  cases positive
  · simp only [step, Bool.false_eq_true, ite_false, listValue, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, pairValue, project_create, project_weight,
      project_ftwist, project_lowestF, tensorChevalley, tensorF_tmul, tensorK]
  · simp only [step, ite_true, listValue, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, pairValue, project_lower, project_twist, project_create,
      tensorChevalley, tensorE_tmul]

/-- Explicit finite expansion for an arbitrary mixed word, outer letter acting last. -/
def expansion (s : Bool) : List (Bool × I) → List (RawPair I)
  | [] => [(1, 1)]
  | g :: w => (expansion s w).flatMap (step D Λ Μ s g.1 g.2)

/-- The original global mixed action, not a replacement action. -/
def wordAction (s : Bool) (w : List (Bool × I)) :=
  (w.map (fun g ↦ tensorChevalley D hD Λ Μ s g.1 g.2)).prod

theorem listValue_step (s positive : Bool) (i : I) (zs : List (RawPair I)) :
    listValue D hD Λ Μ (zs.flatMap (step D Λ Μ s positive i)) =
      tensorChevalley D hD Λ Μ s positive i (listValue D hD Λ Μ zs) := by
  induction zs with
  | nil => simp [listValue]
  | cons z zs ih =>
    simp only [List.flatMap_cons, listValue, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, map_add] at ih ⊢
    rw [← listValue, step_value, ih]

theorem expansion_action (s : Bool) (w : List (Bool × I)) :
    listValue D hD Λ Μ (expansion D Λ Μ s w) =
      wordAction D hD Λ Μ s w
        (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1) := by
  induction w with
  | nil => simp [expansion, listValue, pairValue, project, wordAction]
  | cons g w ih =>
    rw [expansion, listValue_step, ih]
    simp only [wordAction, List.map_cons, List.prod_cons, Module.End.mul_apply]

/-- The accepted half comparison, with its actual finite error, in polynomial form. -/
def halfPolynomial (x y : PreF Coefficients.Ring I) : MvPolynomial I Coefficients.Ring :=
  MvPolynomial.C (D.form Coefficients.q pi x y) + freeComparisonError D y x

omit [DecidableEq X] [Finite I] in
theorem halfPolynomial_constant (x y : PreF Coefficients.Ring I) :
    MvPolynomial.constantCoeff (halfPolynomial D x y) = D.form Coefficients.q pi x y := by
  simp [halfPolynomial, freeComparisonError_constantCoeff]

theorem halfPolynomial_eval (x y : PreF Coefficients.Ring I) :
    MvPolynomial.eval (deformationParameter D Λ) (halfPolynomial D x y) =
      normalizedPolarization D hD Λ x y := by
  have h := normalizedPolarization_sub_half D hD Λ x y
  simp only [halfPolynomial, map_add, MvPolynomial.eval_C]
  rw [← h]
  ring

omit [DecidableEq I] [DecidableEq X] [Finite I] in
theorem sign_involution (x : PreF Coefficients.Ring I) :
    diagTwist (polarizationSign D Λ) (diagTwist (polarizationSign D Λ) x) = x := by
  rw [diagTwist_diagTwist]
  have hh : polarizationSign D Λ * polarizationSign D Λ = fun _ ↦ 1 := by
    funext i
    simpa only [Pi.mul_apply, wordSign, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, pow_two] using wordSign_sq D Λ [i]
  rw [hh]
  have hi : diagTwist (fun _ : I ↦ (1 : Coefficients.Ring)) = AlgHom.id _ _ := by
    ext i
    simp [diagTwist_θ]
  rw [hi]
  rfl

theorem highest_polynomial (hΛ : ∀ i, 0 ≤ D.h i Λ)
    (x y : PreF Coefficients.Ring I) :
    integrablePolarization D hD Λ hΛ (project D hD Λ x) (project D hD Λ y) =
      MvPolynomial.eval (deformationParameter D Λ)
        (halfPolynomial D (diagTwist (polarizationSign D Λ) x) y) := by
  rw [halfPolynomial_eval, normalizedPolarization, sign_involution]
  rfl

theorem lowest_polynomial (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (x y : PreF Coefficients.Ring I) :
    lowestPolarization D hD Μ hΜ (project D hD Μ x) (project D hD Μ y) =
      MvPolynomial.eval (deformationParameter D Μ) (halfPolynomial D x y) := by
  rw [halfPolynomial_eval D hD Μ]
  change integrablePolarization D hD Μ hΜ (project D hD Μ x)
    (integrableJ D hD Μ (project D hD Μ y)) = _
  rw [integrableJ, ← integrablePolarization_sign D hD Μ hΜ]
  simp only [project, integrableSign_mk, GenericTensor.diagonal_mk]
  rfl

/-- The two sets of half parameters remain independent in this finite polynomial. -/
def jointParameter (g : Bool × I) : Coefficients.Ring :=
  if g.1 then deformationParameter D Λ g.2 else deformationParameter D Μ g.2

/-- Exact elementary Gram polynomial. Its inputs may depend on both weights. -/
def pairPolynomial (z z' : RawPair I) : MvPolynomial (Bool × I) Coefficients.Ring :=
  MvPolynomial.rename (fun i ↦ (true, i))
      (halfPolynomial D (diagTwist (polarizationSign D Λ) z.1) z'.1) *
    MvPolynomial.rename (fun i ↦ (false, i)) (halfPolynomial D z.2 z'.2)

theorem pairPolynomial_eval (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (z z' : RawPair I) :
    MvPolynomial.eval (jointParameter D Λ Μ) (pairPolynomial D Λ z z') =
      tensorPolarization D hD Λ Μ hΛ hΜ
        (pairValue D hD Λ Μ z) (pairValue D hD Λ Μ z') := by
  simp only [pairPolynomial, map_mul, MvPolynomial.eval_rename, Function.comp_def,
    jointParameter, ite_true, Bool.false_eq_true, ite_false, pairValue,
    tensorPolarization_tmul, highest_polynomial, lowest_polynomial]

/-- A finite mixed Gram formula, including every coproduct branch.
The action amplitudes in the coefficients depend on both weights; this is NOT
an asymptotic polynomial with uniformly bounded coefficient valuations. -/
def gramPolynomial (s t : Bool) (u v : List (Bool × I)) :
    MvPolynomial (Bool × I) Coefficients.Ring :=
  ((expansion D Λ Μ s u).map (fun z ↦
    ((expansion D Λ Μ t v).map (pairPolynomial D Λ z)).sum)).sum

theorem list_gram (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (zs ws : List (RawPair I)) :
    MvPolynomial.eval (jointParameter D Λ Μ)
      ((zs.map (fun z ↦ (ws.map (pairPolynomial D Λ z)).sum)).sum) =
      tensorPolarization D hD Λ Μ hΛ hΜ
        (listValue D hD Λ Μ zs) (listValue D hD Λ Μ ws) := by
  induction zs with
  | nil => simp [listValue]
  | cons z zs ih =>
    simp only [List.map_cons, List.sum_cons, map_add, ih, listValue,
      LinearMap.add_apply]
    congr 1
    clear ih
    induction ws with
    | nil => simp
    | cons w ws ihw =>
      simp only [List.map_cons, List.sum_cons, map_add,
        pairPolynomial_eval D hD Λ Μ hΛ hΜ] at ihw ⊢
      rw [ihw]

/-- Arbitrary finite mixed words, either original coproduct in either slot.
In particular t=!s is the native cross-Delta Gram matrix. -/
theorem mixed_gram_formula (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s t : Bool) (u v : List (Bool × I)) :
    tensorPolarization D hD Λ Μ hΛ hΜ
      (wordAction D hD Λ Μ s u
        (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1))
      (wordAction D hD Λ Μ t v
        (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1)) =
      MvPolynomial.eval (jointParameter D Λ Μ) (gramPolynomial D Λ Μ s t u v) := by
  rw [← expansion_action, ← expansion_action]
  exact (list_gram D hD Λ Μ hΛ hΜ _ _).symm

omit [DecidableEq I] [DecidableEq X] [Finite I] in
def shift : List (Bool × I) → X
  | [] => 0
  | g :: w => halfRoot D g.1 g.2 + shift w

/-- The genuine composable mixed word in the original modified algebra. -/
def algebraWord (ζ : X) : List (Bool × I) → modified D Coefficients.q pi
  | [] => ⟨one D Coefficients.q pi ζ, one_mem_modified D Coefficients.q pi ζ⟩
  | g :: w =>
    ⟨halfGen D Coefficients.q pi g.1 g.2 (ζ + shift D w),
      block_le_modified D Coefficients.q pi _ _
        (halfGen_mem_block D Coefficients.q pi g.1 g.2 _)⟩ * algebraWord ζ w

theorem project_vacuum :
    tensorProject D hD Λ Μ (Λ - Μ)
      (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1) =
        toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1 := by
  have h := tensorProject_tmul_word D hD Λ Μ (Λ - Μ) (toIntegrable D hD Λ 1) []
  simpa [monomial, wordWeight_nil, integrableRepresentation_toIntegrable,
    representation_one, weightProject_one] using h

theorem project_chevalley (s positive : Bool) (i : I) (μ : X) :
    tensorProject D hD Λ Μ μ * tensorChevalley D hD Λ Μ s positive i =
      tensorChevalley D hD Λ Μ s positive i *
        tensorProject D hD Λ Μ (μ - halfRoot D positive i) := by
  cases positive
  · simpa only [tensorChevalley, Bool.false_eq_true, ite_false,
      halfRoot, sub_neg_eq_add] using tensorProject_F D hD Λ Μ s i μ
  · exact tensorProject_E D hD Λ Μ s i μ

theorem wordAction_weight (s : Bool) (w : List (Bool × I)) :
    tensorProject D hD Λ Μ (Λ - Μ + shift D w)
      (wordAction D hD Λ Μ s w
        (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1)) =
      wordAction D hD Λ Μ s w
        (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1) := by
  induction w with
  | nil => simpa [shift, wordAction] using project_vacuum D hD Λ Μ
  | cons g w ih =>
    simp only [shift, wordAction, List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [← Module.End.mul_apply, project_chevalley, Module.End.mul_apply]
    have he : Λ - Μ + (halfRoot D g.1 g.2 + shift D w) - halfRoot D g.1 g.2 =
        Λ - Μ + shift D w := by abel
    rw [he]
    exact congrArg (tensorChevalley D hD Λ Μ s g.1 g.2) ih

/-- The recursive expansion computes the original quotient action, at the
compatible weight difference, not merely a free Chevalley action. -/
theorem algebraWord_action (s : Bool) (w : List (Bool × I)) :
    tensorRepresentation D hD Λ Μ s (algebraWord D (Λ - Μ) w).val
      (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1) =
      wordAction D hD Λ Μ s w
        (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1) := by
  induction w with
  | nil => simpa [algebraWord, wordAction] using project_vacuum D hD Λ Μ
  | cons g w ih =>
    change tensorRepresentation D hD Λ Μ s
      (halfGen D Coefficients.q pi g.1 g.2 (Λ - Μ + shift D w) *
        (algebraWord D (Λ - Μ) w).val) _ = _
    rw [map_mul, Module.End.mul_apply, ih]
    have hg (b : Bool) (i : I) (μ : X) :
        tensorRepresentation D hD Λ Μ s (halfGen D Coefficients.q pi b i μ) =
          tensorChevalley D hD Λ Μ s b i * tensorProject D hD Λ Μ μ := by
      cases b <;> simp [halfGen, tensorChevalley, tensorEBlock]
    rw [hg, Module.End.mul_apply, wordAction_weight]
    simp only [wordAction, List.map_cons, List.prod_cons, Module.End.mul_apply]

include hD in
/-- Equality of actual modified elements implies equality of the evaluated
finite formula, without any faithfulness or representative hypothesis. -/
theorem gram_representative_invariant
    (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s t : Bool) (u u' v v' : List (Bool × I))
    (hu : algebraWord D (Λ - Μ) u = algebraWord D (Λ - Μ) u')
    (hv : algebraWord D (Λ - Μ) v = algebraWord D (Λ - Μ) v') :
    MvPolynomial.eval (jointParameter D Λ Μ) (gramPolynomial D Λ Μ s t u v) =
      MvPolynomial.eval (jointParameter D Λ Μ) (gramPolynomial D Λ Μ s t u' v') := by
  rw [← mixed_gram_formula D hD Λ Μ hΛ hΜ, ← mixed_gram_formula D hD Λ Μ hΛ hΜ]
  simp only [← algebraWord_action, hu, hv]

/-- The coefficientwise constant of the finite expression. Not asserted to be
weight-independent, a limit, or the positive modified form. -/
def finiteCenter (s t : Bool) (u v : List (Bool × I)) : Coefficients.Ring :=
  ((expansion D Λ Μ s u).map (fun z ↦ ((expansion D Λ Μ t v).map
    (fun z' ↦ D.form Coefficients.q pi (diagTwist (polarizationSign D Λ) z.1) z'.1 *
      D.form Coefficients.q pi z.2 z'.2)).sum)).sum

omit [DecidableEq X] [Finite I] in
theorem gramPolynomial_constant (s t : Bool) (u v : List (Bool × I)) :
    MvPolynomial.constantCoeff (gramPolynomial D Λ Μ s t u v) =
      finiteCenter D Λ Μ s t u v := by
  simp only [gramPolynomial, finiteCenter, map_list_sum, List.map_map,
    Function.comp_def, pairPolynomial, map_mul, MvPolynomial.constantCoeff_rename,
    halfPolynomial_constant]

/-- Only this residual has zero constant. Its coefficients still depend on Λ,Μ. -/
def residualPolynomial (s t : Bool) (u v : List (Bool × I)) :
    MvPolynomial (Bool × I) Coefficients.Ring :=
  gramPolynomial D Λ Μ s t u v - MvPolynomial.C (finiteCenter D Λ Μ s t u v)

omit [DecidableEq X] [Finite I] in
theorem residualPolynomial_constant (s t : Bool) (u v : List (Bool × I)) :
    MvPolynomial.constantCoeff (residualPolynomial D Λ Μ s t u v) = 0 := by
  simp [residualPolynomial, gramPolynomial_constant]

/-- Exact error relative to the EXISTING positive modified form: a nonzero
constant mismatch plus a zero-constant residual. Neither term is discarded. -/
theorem mixed_comparison_identity
    (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (u v : List (Bool × I)) :
    tensorPolarization D hD Λ Μ hΛ hΜ
      (tensorRepresentation D hD Λ Μ s (algebraWord D (Λ - Μ) u).val
        (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1))
      (tensorRepresentation D hD Λ Μ (!s) (algebraWord D (Λ - Μ) v).val
        (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1)) -
      GenericTensor.positiveModifiedForm D hD
        (algebraWord D (Λ - Μ) u) (algebraWord D (Λ - Μ) v) =
      (finiteCenter D Λ Μ s (!s) u v - GenericTensor.positiveModifiedForm D hD
        (algebraWord D (Λ - Μ) u) (algebraWord D (Λ - Μ) v)) +
      MvPolynomial.eval (jointParameter D Λ Μ) (residualPolynomial D Λ Μ s (!s) u v) := by
  rw [algebraWord_action, algebraWord_action, mixed_gram_formula]
  simp only [residualPolynomial, map_sub, MvPolynomial.eval_C]
  ring

omit [DecidableEq X] [Finite I] in
/-- Correct q-adic bound, including weight-dependent negative coefficient orders.
Dominance alone does not imply the displayed threshold hypothesis. -/
theorem residual_order (ε : RatFunc ℚ) (hε : ε ^ 2 = 1)
    (s t : Bool) (u v : List (Bool × I)) (N : ℤ)
    (hbound : ∀ g ∈ (residualPolynomial D Λ Μ s t u v).vars,
      max 0 (N - QAdic.coefficientFloor (specialize ε hε).toRingHom
        (residualPolynomial D Λ Μ s t u v)) ≤ D.h g.2 (if g.1 then Λ else Μ)) :
    (N : WithTop ℤ) ≤ QAdic.order (specialize ε hε
      (MvPolynomial.eval (jointParameter D Λ Μ) (residualPolynomial D Λ Μ s t u v))) := by
  change (N : WithTop ℤ) ≤ QAdic.order ((specialize ε hε).toRingHom
    (MvPolynomial.eval (jointParameter D Λ Μ) (residualPolynomial D Λ Μ s t u v)))
  rw [MvPolynomial.eval₂_comp]
  apply QAdic.eval_order_lower _ _ (residualPolynomial_constant D Λ Μ s t u v)
  intro g hg
  change (max 0 (N - QAdic.coefficientFloor (specialize ε hε).toRingHom
    (residualPolynomial D Λ Μ s t u v)) : WithTop ℤ) ≤
      QAdic.order (specialize ε hε (jointParameter D Λ Μ g))
  have hd : (1 : ℤ) ≤ D.d g.2 := by exact_mod_cast D.d_pos g.2
  have hb := hbound g hg
  have hn : 0 ≤ max 0 (N - QAdic.coefficientFloor (specialize ε hε).toRingHom
    (residualPolynomial D Λ Μ s t u v)) := le_max_left _ _
  let B := max 0 (N - QAdic.coefficientFloor (specialize ε hε).toRingHom
    (residualPolynomial D Λ Μ s t u v))
  change B ≤ D.h g.2 (if g.1 then Λ else Μ) at hb
  change 0 ≤ B at hn
  change (B : WithTop ℤ) ≤ QAdic.order (specialize ε hε (jointParameter D Λ Μ g))
  rcases g with ⟨b, i⟩
  cases b <;> simp only [jointParameter, ite_true, Bool.false_eq_true, ite_false,
    deformationParameter_order] <;>
    exact_mod_cast (by
      simp only [Bool.false_eq_true, ite_false, ite_true] at hb
      dsimp only at hd
      nlinarith : B ≤ _)

omit [DecidableEq X] [Finite I] in
theorem halfPolynomial_word (w : List I) (y : PreF Coefficients.Ring I) :
    halfPolynomial D (monomial Coefficients.Ring w) y = wordPolynomial D w y := by
  simp only [halfPolynomial, freeComparisonError_word, comparisonError]
  ring

omit [DecidableEq X] [Finite I] in
theorem halfPolynomial_theta (i : I) :
    halfPolynomial D (θ Coefficients.Ring i) (θ Coefficients.Ring i) =
      MvPolynomial.C (D.norm Coefficients.q pi i) * (1 - MvPolynomial.X i) := by
  have hw : θ Coefficients.Ring i = monomial Coefficients.Ring [i] := by simp
  rw [hw, halfPolynomial_word, ← hw]
  simp [wordPolynomial]

omit [DecidableEq I] [DecidableEq X] [Finite I] in
@[simp] theorem freeWeight_one (f : X → Coefficients.Ring) :
    freeWeight D Λ f 1 = f Λ • (1 : PreF Coefficients.Ring I) := by
  simpa using freeWeight_word D Λ f []

theorem E_vacuum (s : Bool) (i : I) :
    tensorE D hD Λ Μ s i
      (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1) =
      tensorToralScalar D s i Λ •
        (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring]
          project D hD Μ (θ Coefficients.Ring i)) := by
  have h := step_value D hD Λ Μ s true i (1, 1)
  simpa [step, listValue, pairValue, project, freeTwist, lowerFree,
    freeWeight_one, tensorChevalley, smul_tmul] using h.symm

theorem lowest_theta_norm (hΜ : ∀ i, 0 ≤ D.h i Μ) (i : I) :
    lowestPolarization D hD Μ hΜ
      (project D hD Μ (θ Coefficients.Ring i)) (project D hD Μ (θ Coefficients.Ring i)) =
      D.norm Coefficients.q pi i * (1 - deformationParameter D Μ i) := by
  rw [lowest_polynomial, halfPolynomial_theta]
  simp

/-- The exact rank-one obstruction already present inside every datum.
The prefactor contains q_i^(-2 h_i Λ); no growing-weight normalization is hidden. -/
theorem E_cross_gram (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (i : I) :
    tensorPolarization D hD Λ Μ hΛ hΜ
      (tensorE D hD Λ Μ s i
        (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1))
      (tensorE D hD Λ Μ (!s) i
        (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1)) =
      (D.pii pi i ^ (D.h i Λ).natAbs *
        qp Coefficients.q (-(D.d i * D.h i Λ)) ^ 2) *
      (D.norm Coefficients.q pi i * (1 - deformationParameter D Μ i)) := by
  rw [E_vacuum, E_vacuum, LinearMap.map_smul₂, LinearMap.map_smul,
    tensorPolarization_tmul]
  simp only [integrablePolarization_highest, one_mul,
    lowest_theta_norm, smul_eq_mul]
  cases s <;> simp only [tensorToralScalar, Bool.not_true, Bool.not_false,
    ite_true, Bool.false_eq_true, ite_false, one_mul] <;> ring

/-- Fixed weight-difference pairs, without any existence assertion. -/
abbrev WeightPair (ζ : X) := {p : X × X // p.1 - p.2 = ζ}

omit [DecidableEq I] [DecidableEq X] [Finite I] in
def jointCoordinates (ζ : X) (p : WeightPair ζ) (g : Bool × I) : ℤ :=
  D.h g.2 (if g.1 then p.val.1 else p.val.2)

omit [DecidableEq I] [DecidableEq X] [Finite I] in
def jointFilter (ζ : X) : Filter (WeightPair ζ) :=
  Filter.comap (jointCoordinates D ζ) Filter.atTop

omit [DecidableEq I] [DecidableEq X] [Finite I] in
theorem jointFilter_neBot_iff (ζ : X) : (jointFilter D ζ).NeBot ↔
    ∀ b : Bool × I → ℤ, ∃ p : WeightPair ζ, ∀ g, b g ≤ jointCoordinates D ζ p g := by
  change (Filter.comap (jointCoordinates D ζ) Filter.atTop).NeBot ↔ _
  rw [(Filter.atTop_basis.comap (jointCoordinates D ζ)).neBot_iff]
  constructor
  · intro h b
    exact @h b trivial
  · rintro h b _
    exact h b

omit [DecidableEq I] [DecidableEq X] in
/-- An explicit positive weight produces the genuine fixed-difference family
(ζ+nξ,nξ). The statement does not supply such a ξ for arbitrary root data. -/
theorem jointFilter_neBot_of_positive (ζ ξ : X) (hξ : ∀ i, 0 < D.h i ξ) :
    (jointFilter D ζ).NeBot := by
  classical
  let _ := Fintype.ofFinite I
  apply (jointFilter_neBot_iff D ζ).mpr
  intro b
  let n : ℤ := ∑ i : I, (|b (true, i) - D.h i ζ| + |b (false, i)|)
  have hn : 0 ≤ n := Finset.sum_nonneg (fun i _ ↦ add_nonneg (abs_nonneg _) (abs_nonneg _))
  refine ⟨⟨(ζ + n • ξ, n • ξ), by simp⟩, ?_⟩
  rintro ⟨s, i⟩
  have hi : |b (true, i) - D.h i ζ| + |b (false, i)| ≤ n :=
    Finset.single_le_sum (f := fun j ↦ |b (true, j) - D.h j ζ| + |b (false, j)|)
      (fun j _ ↦ add_nonneg (abs_nonneg _) (abs_nonneg _))
      (Finset.mem_univ i)
  have hdi := hξ i
  have ht := le_abs_self (b (true, i) - D.h i ζ)
  have hf := le_abs_self (b (false, i))
  have ha := abs_nonneg (b (true, i) - D.h i ζ)
  have hb := abs_nonneg (b (false, i))
  cases s
  · change b (false, i) ≤ D.h i (n • ξ)
    have he : D.h i (n • ξ) = n * D.h i ξ := by simp [RootDatum.h]
    rw [he]
    nlinarith
  · change b (true, i) ≤ D.h i (ζ + n • ξ)
    have he : D.h i (ζ + n • ξ) = D.h i ζ + n * D.h i ξ := by simp [RootDatum.h]
    rw [he]
    nlinarith

omit [DecidableEq I] [DecidableEq X] in
/-- Exact nonvacuity criterion for the joint filter at every fixed difference. -/
theorem jointFilter_neBot_iff_positive (ζ : X) :
    (jointFilter D ζ).NeBot ↔ ∃ ξ : X, ∀ i, 0 < D.h i ξ := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := (jointFilter_neBot_iff D ζ).mp h (fun _ ↦ 1)
    refine ⟨p.val.2, fun i ↦ ?_⟩
    have hi := hp (false, i)
    simpa only [jointCoordinates, Bool.false_eq_true, ite_false, Int.lt_iff_add_one_le,
      zero_add] using hi
  · rintro ⟨ξ, hξ⟩
    exact jointFilter_neBot_of_positive D ζ ξ hξ

omit [DecidableEq I] [DecidableEq X] [Finite I] in
/-- Both weights are eventually dominant in the joint filter, even though
nonvacuity and the stronger residual coefficient threshold remain separate. -/
theorem jointFilter_eventually_dominant (ζ : X) :
    ∀ᶠ p in jointFilter D ζ, (∀ i, 0 ≤ D.h i p.val.1) ∧ (∀ i, 0 ≤ D.h i p.val.2) := by
  apply Filter.eventually_comap.mpr
  filter_upwards [Filter.eventually_ge_atTop (fun _ : Bool × I ↦ (0 : ℤ))] with b hb
  intro p hp
  constructor
  · intro i
    have h := hb (true, i)
    simpa only [← congrFun hp (true, i), jointCoordinates, ite_true] using h
  · intro i
    have h := hb (false, i)
    simpa only [← congrFun hp (false, i), jointCoordinates,
      Bool.false_eq_true, ite_false] using h

omit [DecidableEq I] [DecidableEq X] [Finite I] in
/-- Connected off-diagonal entries and the odd×odd Koszul coefficient both
occur in the actual free transition; neither is replaced by a root sign. -/
theorem freeTwist_theta (s : Bool) (i j : I) :
    freeTwist D Λ s i (θ Coefficients.Ring j) =
      (((if s then D.pii pi i ^ (D.h i Λ - D.a i j).natAbs else 1) *
        qp Coefficients.q (-(D.d i * (D.h i Λ - D.a i j)))) *
        pi ^ (D.parity i * D.parity j).val) • θ Coefficients.Ring j := by
  have hw : θ Coefficients.Ring j = monomial Coefficients.Ring [j] := by simp
  simp only [freeTwist, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    parityTwist, diagTwist_θ, map_smul]
  rw [hw, freeWeight_word]
  simp only [wordWeight_cons, wordWeight_nil, add_zero, halfWeight_single,
    halfRoot, ite_true, tensorToralScalar, RootDatum.h, map_sub, D.coroot_root,
    smul_smul]
  rw [mul_comm]

end OddMath.CoveringQuantum.UDot.GenericVerma.MixedGram
