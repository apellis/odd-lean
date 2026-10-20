/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.VermaSerre
import OddMath.CoveringQuantum.UDot.HalfWeights

/-!
# Weight projections on the generic highest-weight module

The grading is constructed on the free half and descends through the actual
Serre ideal by direct homogeneity of its generators. This argument works over
any commutative coefficient ring, with arbitrary colours and weight group;
it needs neither bar consistency nor independence of roots or toral characters.
-/
noncomputable section
namespace OddMath.CoveringQuantum.UDot
open PreF
variable {k I X : Type*} [CommRing k] [AddCommGroup X]
variable [DecidableEq I] [DecidableEq X] (D : RootDatum I X)

/-- The root-lattice grading, pushed forward to the given weight group. -/
def rootGrading : PreF k I →ₐ[k] AddMonoidAlgebra (PreF k I) X :=
  FreeAlgebra.lift k fun i ↦ AddMonoidAlgebra.single (D.α i) (θ k i)

omit [DecidableEq I] [DecidableEq X] in
theorem rootGrading_monomial (w : List I) :
    rootGrading D (monomial k w) =
      AddMonoidAlgebra.single (halfWeight D true (wordWeight w)) (monomial k w) := by
  induction w with
  | nil => simp [rootGrading, AddMonoidAlgebra.one_def]
  | cons i w ih =>
    rw [monomial_cons, map_mul, ih]
    simp [rootGrading, halfWeight_add, halfRoot, AddMonoidAlgebra.single_mul_single]

/-- Projection onto module weight `μ` for highest weight `Λ`, on the free half. -/
def weightProjectFree (Λ μ : X) : Module.End k (PreF k I) where
  toFun x := (rootGrading D x).coeff (Λ - μ)
  map_add' x y := by simp
  map_smul' c x := by simp

omit [DecidableEq I] in
@[simp] theorem weightProjectFree_monomial (Λ μ : X) (w : List I) :
    weightProjectFree D Λ μ (monomial k w) =
      if halfWeight D true (wordWeight w) = Λ - μ then monomial k w else 0 := by
  simp [weightProjectFree, rootGrading_monomial, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]

omit [DecidableEq I] in
/-- Linear induction over the existing free-word spanning family. -/
theorem induction_monomial {P : PreF k I → Prop}
    (word : ∀ w, P (monomial k w)) (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y))
    (smul : ∀ (c : k) x, P x → P (c • x)) (x : PreF k I) : P x := by
  have hx : x ∈ Submodule.span k (Set.range (monomial k (I := I))) := by
    rw [span_monomial]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨w, rfl⟩ := hx; exact word w
  | zero => exact zero
  | add x y _ _ hx hy => exact add x y hx hy
  | smul c x _ hx => exact smul c x hx

omit [DecidableEq X] in
/-- Weight projection is self-adjoint for the free-half form. -/
theorem weightProjectFree_form (χ : Bichar k I) (nm : I → k) (Λ μ : X)
    (x y : PreF k I) :
    form χ nm (weightProjectFree D Λ μ x) y =
      form χ nm x (weightProjectFree D Λ μ y) := by
  classical
  induction x using induction_monomial with
  | zero => simp
  | add x z hx hz => simp [hx, hz]
  | smul c x hx => simp [hx]
  | word w =>
    induction y using induction_monomial with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz]
    | smul c y hy => simp only [map_smul, hy]
    | word v =>
      by_cases h : wordWeight w = wordWeight v
      · simp only [weightProjectFree_monomial, h]
        split_ifs <;> simp
      · have hz := form_eq_zero_of_ne χ nm h
          (monomial_mem_weightSpace (k := k) w) (monomial_mem_weightSpace (k := k) v)
        simp only [weightProjectFree_monomial]
        split_ifs <;> simp [hz]

omit [DecidableEq I] [DecidableEq X] in
theorem weightProjectFree_θ_mul (Λ μ : X) (j : I) (x : PreF k I) :
    weightProjectFree D Λ μ (θ k j * x) =
      θ k j * weightProjectFree D Λ (μ + D.α j) x := by
  classical
  induction x using induction_monomial with
  | zero => simp
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  | smul c x hx => simp only [mul_smul_comm, map_smul, hx]
  | word w =>
    rw [← monomial_cons, weightProjectFree_monomial, weightProjectFree_monomial]
    have he : D.α j + halfWeight D true (wordWeight w) = Λ - μ ↔
        halfWeight D true (wordWeight w) = Λ - (μ + D.α j) := by
      simp only [eq_sub_iff_add_eq, add_comm, add_left_comm]
    simp only [wordWeight_cons, halfWeight_add, halfWeight_single,
      show halfRoot D true j = D.α j from rfl, he]
    split_ifs <;> simp

omit [DecidableEq I] [DecidableEq X] in
theorem weightProjectFree_diag (Λ μ : X) (c : I → k) (x : PreF k I) :
    weightProjectFree D Λ μ (diagTwist c x) =
      diagTwist c (weightProjectFree D Λ μ x) := by
  classical
  induction x using induction_monomial with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul a x hx => simp only [map_smul, hx]
  | word w =>
    rw [diagTwist_monomial, map_smul, weightProjectFree_monomial]
    split_ifs <;> simp [diagTwist_monomial]

omit [DecidableEq X] in
/-- Homogeneity of the actual free lowering numerator, with its correct weight shift. -/
theorem weightProjectFree_numerator (q : kˣ) (π : k) (Λ μ : X) (i : I)
    (a b : k) (x : PreF k I) :
    weightProjectFree D Λ μ (lowerNumerator D.toSuperCartanDatum q π i a b x) =
      lowerNumerator D.toSuperCartanDatum q π i a b
        (weightProjectFree D Λ (μ - D.α i) x) := by
  classical
  induction x using induction_left generalizing μ with
  | algebraMap c =>
    rw [Algebra.algebraMap_eq_smul_one]
    simp only [map_smul]
    rw [show (1 : PreF k I) = monomial k [] from rfl, weightProjectFree_monomial]
    split_ifs <;> simp
  | smul c x hx => simp only [map_smul, hx]
  | add x y hx hy => simp only [map_add, hx, hy]
  | θ_mul j x hx =>
    rw [lowerNumerator_θ_mul, weightProjectFree_θ_mul, lowerNumerator_θ_mul]
    simp only [map_add, map_smul, weightProjectFree_θ_mul, hx]
    have he : μ + D.α j - D.α i = μ - D.α i + D.α j := by abel
    rw [he]
    congr 1
    by_cases h : i = j
    · subst j
      simp only [ite_true, sub_add_cancel, parityTwist, weightTwist, twist,
        map_sub, map_smul, weightProjectFree_diag]
    · simp [h]

omit [DecidableEq X] in
/-- The normalized free lowering operator has the same homogeneous shift. -/
theorem weightProjectFree_lower (q : kˣ) (π : k) (Λ μ : X) (i : I)
    (n : ℤ) (x : PreF k I) :
    weightProjectFree D Λ μ (lowerFree D.toSuperCartanDatum q π i n x) =
      lowerFree D.toSuperCartanDatum q π i n
        (weightProjectFree D Λ (μ - D.α i) x) := by
  simp only [lowerFree, LinearMap.smul_apply, map_smul, weightProjectFree_numerator]

omit [DecidableEq I] [DecidableEq X] in
/-- Each Serre relation is homogeneous in the actual weight group, even when
several root degrees have the same weight. -/
theorem rootGrading_serreElt (q : kˣ) (π : k) (i j : I) :
    rootGrading D (D.serreElt q π i j) =
      AddMonoidAlgebra.single (D.serreDeg i j • D.α i + D.α j)
        (D.serreElt q π i j) := by
  classical
  unfold SuperCartanDatum.serreElt
  rw [map_sum]
  simp only [map_smul, map_mul, map_pow, rootGrading, FreeAlgebra.lift_ι_apply,
    AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single]
  change _ = (AddMonoidAlgebra.singleAddHom (D.serreDeg i j • D.α i + D.α j)) _
  rw [map_sum]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  have hrN : r ≤ D.serreDeg i j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have hw : (D.serreDeg i j - r) • D.α i + D.α j + r • D.α i =
      D.serreDeg i j • D.α i + D.α j := by
    rw [add_right_comm, ← add_nsmul, Nat.sub_add_cancel hrN]
  rw [hw]
  simp

omit [DecidableEq I] [DecidableEq X] in
/-- Projection to any actual weight preserves the Serre ideal directly by
homogeneity, with no finiteness, bar-consistency or condition on `π`. -/
theorem weightProjectFree_mem_serreIdeal (q : kˣ) (π : k) (Λ μ : X)
    {x : PreF k I} (hx : x ∈ D.serreIdeal q π) :
    weightProjectFree D Λ μ x ∈ D.serreIdeal q π := by
  let g := (AddMonoidAlgebra.mapAlgHom X (D.toSerreF q π)).comp (rootGrading D)
  have hle : D.serreIdeal q π ≤ TwoSidedIdeal.ker g := by
    apply D.serreIdeal_le q π
    intro i j hij
    rw [TwoSidedIdeal.mem_ker]
    change AddMonoidAlgebra.mapAlgHom X (D.toSerreF q π)
      (rootGrading D (D.serreElt q π i j)) = 0
    rw [rootGrading_serreElt, AddMonoidAlgebra.mapAlgHom_single,
      D.toSerreF_serreElt q π hij, AddMonoidAlgebra.single_zero]
  have hz := congrArg (fun z : AddMonoidAlgebra (D.serreF q π) X ↦ z.coeff (Λ - μ))
    ((TwoSidedIdeal.mem_ker g).mp (hle hx))
  apply (D.mem_serreIdeal q π _).mpr
  simpa only [g, AlgHom.comp_apply, AddMonoidAlgebra.coeff_mapAlgHom,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, weightProjectFree,
    LinearMap.coe_mk, AddHom.coe_mk] using hz

namespace GenericVerma
open Coefficients

omit [DecidableEq I] [DecidableEq X] in
/-- The genuine weight projections preserve the complete Serre ideal. -/
theorem weightProjectFree_mem_serreIdeal (Λ μ : X) {x : PreF Coefficients.Ring I}
    (hx : x ∈ D.serreIdeal Coefficients.q pi) :
    weightProjectFree D Λ μ x ∈ D.serreIdeal Coefficients.q pi := by
  exact UDot.weightProjectFree_mem_serreIdeal D Coefficients.q pi Λ μ hx

/-- The actual weight idempotent on the negative Serre quotient. -/
def weightProject (Λ μ : X) : Module.End Coefficients.Ring (D.serreF Coefficients.q pi) :=
  let p := (D.toSerreF Coefficients.q pi).toLinearMap
  let f := p.comp (weightProjectFree D Λ μ)
  ((LinearMap.ker p).liftQ f (by
    intro x hx
    change D.toSerreF Coefficients.q pi (weightProjectFree D Λ μ x) = 0
    apply (D.mem_serreIdeal Coefficients.q pi _).mp
    apply weightProjectFree_mem_serreIdeal D Λ μ
    exact (D.mem_serreIdeal Coefficients.q pi x).mpr hx)).comp
    (p.quotKerEquivOfSurjective (D.toSerreF_surjective Coefficients.q pi)).symm.toLinearMap

omit [DecidableEq I] [DecidableEq X] in
@[simp] theorem weightProject_mk (Λ μ : X) (x : PreF Coefficients.Ring I) :
    weightProject D Λ μ (D.toSerreF Coefficients.q pi x) =
      D.toSerreF Coefficients.q pi (weightProjectFree D Λ μ x) := by
  let p := (D.toSerreF Coefficients.q pi).toLinearMap
  simp only [weightProject, LinearMap.comp_apply, LinearEquiv.coe_coe]
  change (LinearMap.ker p).liftQ _ _ ((p.quotKerEquivOfSurjective _).symm (p x)) = _
  exact congrArg ((LinearMap.ker p).liftQ _ _)
    (p.quotKerEquivOfSurjective_symm_apply (D.toSerreF_surjective Coefficients.q pi) x)

omit [DecidableEq I] in
/-- The descended projections are mutually orthogonal idempotents. -/
theorem weightProject_mul (Λ μ ν : X) :
    weightProject D Λ μ * weightProject D Λ ν =
      if μ = ν then weightProject D Λ μ else 0 := by
  ext z
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective Coefficients.q pi z
  simp only [Module.End.mul_apply, weightProject_mk]
  classical
  induction x using induction_monomial with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add] at *
    split_ifs at * <;> simp_all
  | smul c x hx =>
    simp only [map_smul] at *
    split_ifs at * <;> simp_all
  | word w =>
    simp only [weightProjectFree_monomial]
    by_cases h : μ = ν
    · subst ν
      simp only [ite_true]
      split_ifs <;> simp_all
    · have hn : Λ - μ ≠ Λ - ν := by simpa using h
      have h' : ν ≠ μ := Ne.symm h
      split_ifs <;> simp_all

omit [DecidableEq X] in
/-- Weight covariance for the already constructed quotient lowering operators. -/
theorem weightProject_lower (Λ μ : X) (i : I) (n : ℤ)
    (x : D.serreF Coefficients.q pi) :
    weightProject D Λ μ (lower D.toSuperCartanDatum i n x) =
      lower D.toSuperCartanDatum i n (weightProject D Λ (μ - D.α i) x) := by
  obtain ⟨y, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  simp only [lower_mk, weightProject_mk, weightProjectFree_lower]

omit [DecidableEq I] [DecidableEq X] in
/-- Weight covariance for multiplication by the actual negative generator. -/
theorem weightProject_θ_mul (Λ μ : X) (i : I) (x : D.serreF Coefficients.q pi) :
    weightProject D Λ μ (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i) * x) =
      D.toSerreF Coefficients.q pi (θ Coefficients.Ring i) *
        weightProject D Λ (μ + D.α i) x := by
  obtain ⟨y, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  rw [← map_mul, weightProject_mk, weightProjectFree_θ_mul, map_mul, weightProject_mk]

end GenericVerma
end OddMath.CoveringQuantum.UDot
