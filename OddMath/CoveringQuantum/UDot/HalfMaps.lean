import OddMath.CoveringQuantum.UDot.Blocks

/-!
# Half-algebra maps to the modified covering quantum group

For the presentation in [BE2] §§9–10, the positive and negative half maps are
weight-dependent linear maps, not unital algebra maps into the modified algebra.
The half-algebra identity maps to `1_λ`. We construct the maps directly from the
Serre relations; no triangular decomposition or nondegeneracy is assumed.
-/

noncomputable section

namespace OddMath.CoveringQuantum.UDot

open Finset MulOpposite

variable {k I X : Type*} [CommRing k] [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X) (q : kˣ) (π : k)

/-- The right weight column in the unital envelope. -/
def column (μ : X) : Submodule k (CoveringUDot k D q π) where
  carrier := {x | x * one D q π μ = x}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; exact (add_mul x y _).trans (congrArg₂ (· + ·) hx hy)
  smul_mem' := by intro c x hx; exact (smul_mul_assoc c x _).trans (congrArg (c • ·) hx)

/-- The signed simple-root shift: `true` is positive, `false` negative. -/
def halfRoot (positive : Bool) (i : I) : X := if positive then D.α i else -D.α i

/-- The signed Chevalley generator with right weight `μ`. -/
def halfGen (positive : Bool) (i : I) (μ : X) : CoveringUDot k D q π :=
  if positive then E D q π i μ else F D q π i μ

/-- The corresponding non-divided power with its right idempotent. -/
def halfPow (positive : Bool) (i : I) (n : ℕ) (μ : X) : CoveringUDot k D q π :=
  if positive then mk D q π (epow D i n μ) else mk D q π (fpow D i n μ)

@[simp] theorem halfPow_zero (positive : Bool) (i : I) (μ : X) :
    halfPow D q π positive i 0 μ = one D q π μ := by
  cases positive <;> rfl

theorem halfPow_succ (positive : Bool) (i : I) (n : ℕ) (μ : X) :
    halfPow D q π positive i (n + 1) μ =
      halfGen D q π positive i (μ + n • halfRoot D positive i) *
        halfPow D q π positive i n μ := by
  cases positive <;> simp [halfPow, halfGen, halfRoot, epow, fpow, sub_eq_add_neg, E, F]

theorem halfGen_mem_block (positive : Bool) (i : I) (μ : X) :
    halfGen D q π positive i μ ∈ block D q π (μ + halfRoot D positive i) μ := by
  cases positive
  · simpa [halfGen, halfRoot, sub_eq_add_neg] using
      (show F D q π i μ ∈ block D q π (μ - D.α i) μ from
        ⟨one_mul_F_self D q π i μ, F_mul_one_self D q π i μ⟩)
  · exact ⟨one_mul_E_self D q π i μ, E_mul_one_self D q π i μ⟩

/-- Right multiplication, shifting the input column along a simple root. -/
def halfStep (positive : Bool) (i : I) :
    Module.End k (∀ μ, column D q π μ) where
  toFun f μ := ⟨(f (μ + halfRoot D positive i) : CoveringUDot k D q π) *
      halfGen D q π positive i μ, by
    change (_ * _) * one D q π μ = _
    rw [mul_assoc, (halfGen_mem_block D q π positive i μ).2]⟩
  map_add' f g := by ext μ; exact add_mul _ _ _
  map_smul' c f := by ext μ; exact smul_mul_assoc c _ _

/-- The free half algebra acts on column sections from the right. -/
def halfActionFree (positive : Bool) : PreF k I →ₐ[k]
    (Module.End k (∀ μ, column D q π μ))ᵐᵒᵖ :=
  FreeAlgebra.lift k fun i ↦ op (halfStep D q π positive i)

@[simp] theorem halfActionFree_θ (positive : Bool) (i : I) :
    halfActionFree D q π positive (PreF.θ k i) = op (halfStep D q π positive i) := by
  simp [halfActionFree]

/-- Forget the column condition of a section. -/
def sectionValue (f : ∀ μ, column D q π μ) (μ : X) : CoveringUDot k D q π := f μ

theorem halfActionFree_pow (positive : Bool) (i : I) (n : ℕ)
    (f : ∀ μ, column D q π μ) (μ : X) :
    ((unop (halfActionFree D q π positive (PreF.θ k i ^ n)) f μ) :
        CoveringUDot k D q π) =
      sectionValue D q π f (μ + n • halfRoot D positive i) *
        halfPow D q π positive i n μ := by
  induction n generalizing f μ with
  | zero =>
    simp only [pow_zero, map_one, unop_one, Module.End.one_apply, zero_nsmul, add_zero,
      halfPow_zero]
    exact (f μ).property.symm
  | succ n ih =>
    rw [pow_succ', map_mul, unop_mul, halfActionFree_θ]
    change ((unop (halfActionFree D q π positive (PreF.θ k i ^ n))
      (halfStep D q π positive i f) μ) : CoveringUDot k D q π) = _
    rw [ih, halfPow_succ]
    change sectionValue D q π f ((μ + n • halfRoot D positive i) + halfRoot D positive i) * _ * _ = _
    simp only [add_nsmul, one_nsmul, ← add_assoc, mul_assoc]

/-- Evaluation of a right action at a column section and a weight. -/
def sectionEval (f : ∀ μ, column D q π μ) (μ : X) :
    (Module.End k (∀ μ, column D q π μ))ᵐᵒᵖ →ₗ[k] CoveringUDot k D q π where
  toFun a := sectionValue D q π (unop a f) μ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem halfActionFree_serreWord (positive : Bool) (i j : I) (n m : ℕ)
    (f : ∀ μ, column D q π μ) (μ : X) :
    sectionEval D q π f μ (halfActionFree D q π positive
      (PreF.θ k i ^ n * PreF.θ k j * PreF.θ k i ^ m)) =
      sectionValue D q π f (μ + m • halfRoot D positive i + halfRoot D positive j +
        n • halfRoot D positive i) *
      (halfPow D q π positive i n (μ + m • halfRoot D positive i + halfRoot D positive j) *
        halfGen D q π positive j (μ + m • halfRoot D positive i) *
        halfPow D q π positive i m μ) := by
  simp only [sectionEval, map_mul]
  change ((unop (halfActionFree D q π positive (PreF.θ k i ^ m))
    (unop (halfActionFree D q π positive (PreF.θ k j))
      (unop (halfActionFree D q π positive (PreF.θ k i ^ n)) f)) μ) :
        CoveringUDot k D q π) = _
  rw [halfActionFree_pow, halfActionFree_θ]
  change (((unop (halfActionFree D q π positive (PreF.θ k i ^ n)) f
    (μ + m • halfRoot D positive i + halfRoot D positive j)) : CoveringUDot k D q π) *
      halfGen D q π positive j (μ + m • halfRoot D positive i)) * _ = _
  rw [halfActionFree_pow]
  simp only [mul_assoc]

theorem halfActionFree_serreElt (positive : Bool) {i j : I} (h : i ≠ j) :
    halfActionFree D q π positive (D.serreElt q π i j) = 0 := by
  apply unop_injective
  ext f μ
  change sectionEval D q π f μ (halfActionFree D q π positive (D.serreElt q π i j)) = 0
  simp only [SuperCartanDatum.serreElt, map_sum, map_smul, halfActionFree_serreWord]
  have shift (r : ℕ) (hr : r ∈ range (D.serreDeg i j + 1)) :
      μ + r • halfRoot D positive i + halfRoot D positive j +
        (D.serreDeg i j - r) • halfRoot D positive i =
      μ + D.serreDeg i j • halfRoot D positive i + halfRoot D positive j := by
    have hr' : r ≤ D.serreDeg i j := by simpa only [mem_range, Nat.lt_succ_iff] using hr
    calc
      _ = μ + (r + (D.serreDeg i j - r)) • halfRoot D positive i +
          halfRoot D positive j := by rw [add_nsmul]; abel
      _ = _ := by rw [Nat.add_sub_of_le hr']
  trans ∑ r ∈ range (D.serreDeg i j + 1), D.serreCoeff q π i j r •
    (sectionValue D q π f (μ + D.serreDeg i j • halfRoot D positive i +
      halfRoot D positive j) *
      (halfPow D q π positive i (D.serreDeg i j - r)
          (μ + r • halfRoot D positive i + halfRoot D positive j) *
        halfGen D q π positive j (μ + r • halfRoot D positive i) *
        halfPow D q π positive i r μ))
  · exact Finset.sum_congr rfl fun r hr ↦ by rw [shift r hr]
  simp_rw [← mul_smul_comm]
  rw [← Finset.mul_sum]
  have hz : (∑ r ∈ range (D.serreDeg i j + 1), D.serreCoeff q π i j r •
      (halfPow D q π positive i (D.serreDeg i j - r)
          (μ + r • halfRoot D positive i + halfRoot D positive j) *
        halfGen D q π positive j (μ + r • halfRoot D positive i) *
        halfPow D q π positive i r μ)) = 0 := by
    cases positive
    · simpa only [serreF, map_sum, map_smul, map_mul, halfPow, halfGen, halfRoot,
        Bool.false_eq_true, ↓reduceIte, smul_neg, sub_eq_add_neg, F] using serreF_rel D q π h μ
    · simpa only [serreE, map_sum, map_smul, map_mul, halfPow, halfGen, halfRoot,
        ↓reduceIte, E] using serreE_rel D q π h μ
  simp only [← mul_smul_comm] at hz
  rw [hz, mul_zero]

/-- The Serre half algebra acts on column sections, with multiplication reversed. -/
def halfAction (positive : Bool) : D.serreF q π →ₐ[k]
    (Module.End k (∀ μ, column D q π μ))ᵐᵒᵖ :=
  RingQuot.liftAlgHom k ⟨halfActionFree D q π positive, by
    intro x y h
    cases h with
    | serre i j h => rw [halfActionFree_serreElt D q π positive h, map_zero]⟩

@[simp] theorem halfAction_toSerreF (positive : Bool) (x : PreF k I) :
    halfAction D q π positive (D.toSerreF q π x) = halfActionFree D q π positive x := by
  simp only [halfAction, SuperCartanDatum.toSerreF, RingQuot.liftAlgHom_mkAlgHom_apply]

/-- The section of weight idempotents, not the scalar identity of the envelope. -/
def weightUnits (μ : X) : column D q π μ :=
  ⟨one D q π μ, one_mul_one_self D q π μ⟩

/-- The signed half map `x ↦ x⁺1_μ` or `x ↦ x⁻1_μ`, with values in the envelope.
Its image in the modified algebra is proved below. -/
def halfMap (positive : Bool) (μ : X) : D.serreF q π →ₗ[k] CoveringUDot k D q π :=
  (sectionEval D q π (weightUnits D q π) μ).comp (halfAction D q π positive).toLinearMap

@[simp] theorem halfMap_one (positive : Bool) (μ : X) :
    halfMap D q π positive μ 1 = one D q π μ := by
  simp [halfMap, sectionEval, sectionValue, weightUnits]

@[simp] theorem halfMap_θ (positive : Bool) (μ : X) (i : I) :
    halfMap D q π positive μ (D.toSerreF q π (PreF.θ k i)) =
      halfGen D q π positive i μ := by
  change sectionEval D q π (weightUnits D q π) μ
    (halfAction D q π positive (D.toSerreF q π (PreF.θ k i))) = _
  rw [halfAction_toSerreF, halfActionFree_θ]
  exact (halfGen_mem_block D q π positive i μ).1

private theorem action_mem_modified (positive : Bool) (x : PreF k I)
    (f : ∀ μ, column D q π μ) (hf : ∀ μ, sectionValue D q π f μ ∈ modified D q π) (μ : X) :
    sectionEval D q π f μ (halfActionFree D q π positive x) ∈ modified D q π := by
  induction x using FreeAlgebra.induction generalizing f μ with
  | grade0 c =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, map_smul]
    exact (modified D q π).smul_mem c (hf μ)
  | grade1 i =>
    rw [halfActionFree_θ]
    exact (modified D q π).mul_mem (hf _) (block_le_modified D q π _ _
      (halfGen_mem_block D q π positive i μ))
  | add x y hx hy =>
    simp only [map_add]
    exact (modified D q π).add_mem (hx f hf μ) (hy f hf μ)
  | mul x y hx hy =>
    rw [map_mul]
    exact hy (unop (halfActionFree D q π positive x) f) (fun μ ↦ hx f hf μ) μ

theorem halfMap_mem_modified (positive : Bool) (μ : X) (x : D.serreF q π) :
    halfMap D q π positive μ x ∈ modified D q π := by
  obtain ⟨x, rfl⟩ := D.toSerreF_surjective q π x
  change sectionEval D q π (weightUnits D q π) μ
    (halfAction D q π positive (D.toSerreF q π x)) ∈ _
  rw [halfAction_toSerreF]
  exact action_mem_modified D q π positive x (weightUnits D q π)
    (one_mem_modified D q π) μ

/-- The actual positive half map to the nonunital modified algebra. -/
def positiveHalf (μ : X) : D.serreF q π →ₗ[k] modified D q π :=
  (halfMap D q π true μ).codRestrict _ (halfMap_mem_modified D q π true μ)

/-- The actual negative half map to the nonunital modified algebra. -/
def negativeHalf (μ : X) : D.serreF q π →ₗ[k] modified D q π :=
  (halfMap D q π false μ).codRestrict _ (halfMap_mem_modified D q π false μ)

@[simp] theorem positiveHalf_one (μ : X) :
    (positiveHalf D q π μ 1 : CoveringUDot k D q π) = one D q π μ :=
  halfMap_one D q π true μ

@[simp] theorem negativeHalf_one (μ : X) :
    (negativeHalf D q π μ 1 : CoveringUDot k D q π) = one D q π μ :=
  halfMap_one D q π false μ

@[simp] theorem positiveHalf_θ (μ : X) (i : I) :
    (positiveHalf D q π μ (D.toSerreF q π (PreF.θ k i)) : CoveringUDot k D q π) =
      E D q π i μ := halfMap_θ D q π true μ i

@[simp] theorem negativeHalf_θ (μ : X) (i : I) :
    (negativeHalf D q π μ (D.toSerreF q π (PreF.θ k i)) : CoveringUDot k D q π) =
      F D q π i μ := halfMap_θ D q π false μ i

end OddMath.CoveringQuantum.UDot
