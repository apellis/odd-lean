import OddMath.CoveringQuantum.UDot.HalfMaps

/-!
# Weight blocks and multiplication of the half maps

The maps constructed from [BE2] (9.3)–(9.4) and (10.1) send a homogeneous
half-algebra element of degree `ν` to its prescribed weight block. Multiplication
uses the shifted right weight, rather than the scalar unit of the envelope.
-/

noncomputable section

namespace OddMath.CoveringQuantum.UDot

open Finset MulOpposite

variable {k I X : Type*} [CommRing k] [AddCommGroup X]
variable (D : RootDatum I X) (q : kˣ) (π : k)

/-- The signed weight in the root lattice of a half-algebra degree. -/
def halfWeight (positive : Bool) (ν : I →₀ ℕ) : X :=
  ν.sum fun i n ↦ n • halfRoot D positive i

@[simp] theorem halfWeight_zero (positive : Bool) : halfWeight D positive 0 = 0 := by
  simp [halfWeight]

theorem halfWeight_add (positive : Bool) (ν η : I →₀ ℕ) :
    halfWeight D positive (ν + η) = halfWeight D positive ν + halfWeight D positive η := by
  exact Finsupp.sum_add_index' (by simp) (by intro i m n; exact add_nsmul _ _ _)

@[simp] theorem halfWeight_single (positive : Bool) (i : I) :
    halfWeight D positive (Finsupp.single i 1) = halfRoot D positive i := by
  simp [halfWeight, Finsupp.sum_single_index]

variable [DecidableEq I] [DecidableEq X]

/-- The degree submodule of the Serre quotient, as the image of the free degree submodule. -/
def halfWeightSpace (ν : I →₀ ℕ) : Submodule k (D.serreF q π) :=
  (PreF.weightSpace k ν).map (D.toSerreF q π).toLinearMap

/-- A signed word with its right weight idempotent. -/
def halfWord (positive : Bool) : List I → X → CoveringUDot k D q π
  | [], μ => one D q π μ
  | i :: w, μ => halfGen D q π positive i (μ + halfWeight D positive (PreF.wordWeight w)) *
      halfWord positive w μ

theorem halfWord_mem_block (positive : Bool) (w : List I) (μ : X) :
    halfWord D q π positive w μ ∈
      block D q π (μ + halfWeight D positive (PreF.wordWeight w)) μ := by
  induction w with
  | nil =>
    simpa only [halfWord, PreF.wordWeight_nil, halfWeight_zero, add_zero] using
      (show one D q π μ ∈ block D q π μ μ from
        ⟨one_mul_one_self D q π μ, one_mul_one_self D q π μ⟩)
  | cons i w ih =>
    have h := mul_mem_block D q π
      (halfGen_mem_block D q π positive i (μ + halfWeight D positive (PreF.wordWeight w))) ih
    simpa only [halfWord, PreF.wordWeight_cons, halfWeight_add, halfWeight_single,
      add_left_comm, add_comm, add_assoc] using h

theorem halfActionFree_monomial (positive : Bool) (w : List I)
    (f : ∀ μ, column D q π μ) (μ : X) :
    sectionEval D q π f μ (halfActionFree D q π positive (PreF.monomial k w)) =
      sectionValue D q π f (μ + halfWeight D positive (PreF.wordWeight w)) *
        halfWord D q π positive w μ := by
  induction w generalizing f μ with
  | nil =>
    simp only [PreF.monomial_nil, map_one, PreF.wordWeight_nil, halfWeight_zero, add_zero,
      halfWord]
    exact (f μ).property.symm
  | cons i w ih =>
    rw [PreF.monomial_cons, map_mul, halfActionFree_θ]
    change sectionEval D q π (halfStep D q π positive i f) μ
      (halfActionFree D q π positive (PreF.monomial k w)) = _
    rw [ih]
    change sectionValue D q π f
      (μ + halfWeight D positive (PreF.wordWeight w) + halfRoot D positive i) *
      halfGen D q π positive i (μ + halfWeight D positive (PreF.wordWeight w)) * _ = _
    simp only [halfWord, PreF.wordWeight_cons, halfWeight_add, halfWeight_single, mul_assoc]
    congr 2
    abel

@[simp] theorem halfMap_monomial (positive : Bool) (w : List I) (μ : X) :
    halfMap D q π positive μ (D.toSerreF q π (PreF.monomial k w)) =
      halfWord D q π positive w μ := by
  change sectionEval D q π (weightUnits D q π) μ
    (halfAction D q π positive (D.toSerreF q π (PreF.monomial k w))) = _
  rw [halfAction_toSerreF, halfActionFree_monomial]
  exact (halfWord_mem_block D q π positive w μ).1

/-- A homogeneous half-algebra element maps to the prescribed weight block. -/
theorem halfMap_mem_block (positive : Bool) (μ : X) {ν : I →₀ ℕ} {x : D.serreF q π}
    (hx : x ∈ halfWeightSpace D q π ν) :
    halfMap D q π positive μ x ∈ block D q π (μ + halfWeight D positive ν) μ := by
  obtain ⟨x, hx, rfl⟩ := hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    change PreF.wordWeight w = ν at hw
    rw [AlgHom.toLinearMap_apply, halfMap_monomial, ← hw]
    exact halfWord_mem_block D q π positive w μ
  | zero => simp
  | add x y hx hy ihx ihy =>
    simp only [map_add, AlgHom.toLinearMap_apply]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    simp only [map_smul, AlgHom.toLinearMap_apply]
    exact Submodule.smul_mem _ c ih

/-- On a homogeneous input, the right action factors through the corresponding half map. -/
theorem halfAction_homogeneous (positive : Bool) {ν : I →₀ ℕ} {x : D.serreF q π}
    (hx : x ∈ halfWeightSpace D q π ν) (f : ∀ μ, column D q π μ) (μ : X) :
    sectionEval D q π f μ (halfAction D q π positive x) =
      sectionValue D q π f (μ + halfWeight D positive ν) * halfMap D q π positive μ x := by
  obtain ⟨x, hx, rfl⟩ := hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    change PreF.wordWeight w = ν at hw
    simp only [AlgHom.toLinearMap_apply, halfAction_toSerreF, halfActionFree_monomial,
      halfMap_monomial, hw]
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, mul_add, ihx, ihy]
  | smul c x hx ih => simp only [map_smul, mul_smul_comm, ih]

/-- Multiplication of half maps shifts the right weight of the left factor. -/
theorem halfMap_mul (positive : Bool) (μ : X) (x : D.serreF q π)
    {ν : I →₀ ℕ} {y : D.serreF q π} (hy : y ∈ halfWeightSpace D q π ν) :
    halfMap D q π positive μ (x * y) =
      halfMap D q π positive (μ + halfWeight D positive ν) x * halfMap D q π positive μ y := by
  change sectionEval D q π (weightUnits D q π) μ (halfAction D q π positive (x * y)) = _
  rw [map_mul]
  exact halfAction_homogeneous D q π positive hy
    (unop (halfAction D q π positive x) (weightUnits D q π)) μ

/-- The half map restricted to one homogeneous degree, with its actual block codomain. -/
def halfBlock (positive : Bool) (μ : X) (ν : I →₀ ℕ) :
    halfWeightSpace D q π ν →ₗ[k] block D q π (μ + halfWeight D positive ν) μ :=
  ((halfMap D q π positive μ).comp (halfWeightSpace D q π ν).subtype).codRestrict _
    (fun x ↦ halfMap_mem_block D q π positive μ x.property)

/-- Positive homogeneous elements lie in the corresponding positive weight block. -/
theorem positiveHalf_mem_block (μ : X) {ν : I →₀ ℕ} {x : D.serreF q π}
    (hx : x ∈ halfWeightSpace D q π ν) :
    (positiveHalf D q π μ x : CoveringUDot k D q π) ∈
      block D q π (μ + halfWeight D true ν) μ := halfMap_mem_block D q π true μ hx

/-- Negative homogeneous elements lie in the corresponding negative weight block. -/
theorem negativeHalf_mem_block (μ : X) {ν : I →₀ ℕ} {x : D.serreF q π}
    (hx : x ∈ halfWeightSpace D q π ν) :
    (negativeHalf D q π μ x : CoveringUDot k D q π) ∈
      block D q π (μ + halfWeight D false ν) μ := halfMap_mem_block D q π false μ hx

/-- Positive half multiplication, with the weight shift of the right factor. -/
theorem positiveHalf_mul (μ : X) (x : D.serreF q π) {ν : I →₀ ℕ} {y : D.serreF q π}
    (hy : y ∈ halfWeightSpace D q π ν) :
    positiveHalf D q π μ (x * y) =
      positiveHalf D q π (μ + halfWeight D true ν) x * positiveHalf D q π μ y := by
  apply Subtype.ext
  exact halfMap_mul D q π true μ x hy

/-- Negative half multiplication, with the weight shift of the right factor. -/
theorem negativeHalf_mul (μ : X) (x : D.serreF q π) {ν : I →₀ ℕ} {y : D.serreF q π}
    (hy : y ∈ halfWeightSpace D q π ν) :
    negativeHalf D q π μ (x * y) =
      negativeHalf D q π (μ + halfWeight D false ν) x * negativeHalf D q π μ y := by
  apply Subtype.ext
  exact halfMap_mul D q π false μ x hy

end OddMath.CoveringQuantum.UDot
