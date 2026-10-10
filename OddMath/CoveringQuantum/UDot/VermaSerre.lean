import OddMath.CoveringQuantum.UDot.VermaOperators

/-!
# Positive Serre relations for the concrete lowering operators

The corrected lowering operators from [CHW1] Proposition 2.2.2(b), in the
[BE2] parameter convention, satisfy the positive Serre relations. The proof
works first on the free negative half: commuting an evaluated word past a
negative generator produces the two skew derivatives, at `q` and `q⁻¹`.
Both annihilate a Serre element. Its evaluation kills the vacuum, hence every
negative word. This argument uses neither toral-character separation nor a
field structure on the covering coefficient ring.

`lowerFree_serre` holds over a commutative ring with `q` a unit and `π² = 1`.
`GenericVerma.lower_serre` transfers it to the existing quotient operators,
whose construction assumes finite, bar-consistent data over the actual generic
covering ring. `GenericVerma.positiveAction` is an action of the positive half,
not a modified weight-block representation or a triangular injectivity theorem.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot
open PreF
variable {k I : Type*} [CommRing k] [DecidableEq I]
variable (C : SuperCartanDatum I) (q : kˣ) (π : k)

private theorem numerator_diag (i : I) (a b : k) (c : I → k) (x : PreF k I) :
    lowerNumerator C q π i a b (diagTwist c x) =
      c i • diagTwist c (lowerNumerator C q π i a b x) := by
  simp only [lowerNumerator, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, rDeriv_diagTwist, lDeriv_diagTwist,
    map_smul, map_sub, parityTwist, weightTwist, diagTwist_comm c]
  module

omit [DecidableEq I] in
private theorem parity_twist_twist (hπ : π ^ 2 = 1) (i : I) (x : PreF k I) :
    parityTwist C π i (twist (C.chi q π) i x) = weightTwist C q⁻¹ i x := by
  rw [parityTwist, twist, diagTwist_diagTwist]
  have hc : (fun j ↦ π ^ (C.parity i * C.parity j).val) * (fun j ↦ C.chi q π i j) =
      (fun j ↦ ((q⁻¹ ^ C.dot i j : kˣ) : k)) := by
    funext j
    simp only [Pi.mul_apply, SuperCartanDatum.chi_apply, inv_zpow, ← zpow_neg]
    have hp : π ^ (C.parity i * C.parity j).val * π ^ (C.parity i * C.parity j).val = 1 := by
      rw [← pow_two, ← pow_mul, mul_comm _ 2, pow_mul, hπ, one_pow]
    rw [mul_left_comm, hp, mul_one]
  rw [hc]
  rfl

omit [DecidableEq I] in
/-- Inverting the parameter preserves each covering Serre element. -/
theorem serreElt_inv_q (hπ : π ^ 2 = 1) {i j : I} (hij : i ≠ j) :
    C.serreElt q⁻¹ π i j = C.serreElt q π i j := by
  unfold SuperCartanDatum.serreElt
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  simp only [SuperCartanDatum.serreCoeff, SuperCartanDatum.qi, inv_pow,
    qpBinom_inv (C.pii_sq π hπ i)]
  have hp : C.pii π i ^ (r * (C.serreDeg i j - r)) = 1 := by
    rcases C.odd_serreDeg_or π hij with ho | he
    · have hev : Even (r * (C.serreDeg i j - r)) := by
        rcases Nat.even_or_odd r with hr | hr
        · exact hr.mul_right _
        · exact (Nat.Odd.sub_odd ho hr).mul_left _
      obtain ⟨s, hs⟩ := hev
      rw [hs, ← two_mul, pow_mul, C.pii_sq π hπ i, one_pow]
    · rw [he, one_pow]
  rw [hp, one_mul]

/-- Evaluation of free words in the concrete lowering numerators. -/
def numeratorEval (a b : I → k) : PreF k I →ₐ[k] Module.End k (PreF k I) :=
  FreeAlgebra.lift k fun i ↦ lowerNumerator C q π i (a i) (b i)

@[simp] theorem numeratorEval_θ (a b : I → k) (i : I) :
    numeratorEval C q π a b (θ k i) = lowerNumerator C q π i (a i) (b i) := by
  simp [numeratorEval, θ]

private theorem weight_numerator (v : kˣ) (i j : I) (a b : k) (x : PreF k I) :
    weightTwist C v i (lowerNumerator C q π j a b x) =
      ((v ^ (-C.dot i j) : kˣ) : k) •
        lowerNumerator C q π j a b (weightTwist C v i x) := by
  rw [weightTwist, numerator_diag, smul_smul]
  simp only [← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
    Units.val_one, one_smul]

private theorem numeratorEval_mixed (hπ : π ^ 2 = 1) (a b : I → k)
    (x : PreF k I) (l : I) (y : PreF k I) :
    numeratorEval C q π a b x (θ k l * y) =
      θ k l * numeratorEval C q π a b (parityTwist C π l x) y +
      a l • numeratorEval C q π a b (rDeriv (C.chi q⁻¹ π) l x) (weightTwist C q⁻¹ l y) -
      b l • numeratorEval C q π a b (rDeriv (C.chi q π) l x) (weightTwist C q l y) := by
  induction x using induction_right generalizing y with
  | algebraMap c => simp [Module.algebraMap_end_apply]
  | smul c x hx =>
    simp only [map_smul, LinearMap.smul_apply, hx, mul_smul_comm]
    module
  | add x z hx hz =>
    simp only [map_add, LinearMap.add_apply, hx, hz, mul_add]
    module
  | mul_θ x i hx =>
    simp only [map_mul, Module.End.mul_apply, numeratorEval_θ]
    rw [lowerNumerator_θ_mul]
    simp only [map_add, map_smul, hx, rDeriv_mul_θ, map_mul, map_add, map_smul,
      Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      show ∀ j, parityTwist C π l (θ k j) = π ^ (C.parity l * C.parity j).val • θ k j from
        fun j ↦ diagTwist_θ _ j, numeratorEval_θ]
    rw [weight_numerator C q π q⁻¹, weight_numerator C q π q]
    simp only [map_smul, inv_zpow, SuperCartanDatum.chi_apply,
      mul_comm (C.parity i) (C.parity l)]
    by_cases h : i = l
    · subst i
      simp only [ite_true, parity_twist_twist C q π hπ, map_sub, map_smul, mul_smul_comm]
      module
    · simp only [h, Ne.symm h, ite_false, map_zero, LinearMap.zero_apply, mul_smul_comm]
      module

private theorem numeratorEval_one (a b : I → k) (x : PreF k I) :
    numeratorEval C q π a b x 1 = counit x • (1 : PreF k I) := by
  induction x using induction_right with
  | algebraMap c => simp [Module.algebraMap_end_apply]
  | smul c x hx => simp [hx, smul_smul]
  | add x z hx hz => simp [hx, hz, add_smul]
  | mul_θ x i _ => simp [Module.End.mul_apply]

/-- The concrete numerators satisfy the positive Serre relations already on
    the free negative half, for arbitrary highest-weight scalars. -/
theorem numeratorEval_serre (hπ : π ^ 2 = 1) (a b : I → k)
    {i j : I} (hij : i ≠ j) :
    numeratorEval C q π a b (C.serreElt q π i j) = 0 := by
  ext y
  change numeratorEval C q π a b (C.serreElt q π i j) y = 0
  induction y using induction_left with
  | algebraMap c =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, numeratorEval_one,
      C.counit_serreElt, zero_smul, smul_zero]
  | smul c y hy => rw [map_smul, hy, smul_zero]
  | add y z hy hz => rw [map_add, hy, hz, add_zero]
  | θ_mul l y hy =>
    rw [numeratorEval_mixed C q π hπ,
      C.rDeriv_serreElt q π hπ hij,
      ← serreElt_inv_q C q π hπ hij, C.rDeriv_serreElt q⁻¹ π hπ hij,
      serreElt_inv_q C q π hπ hij]
    simp only [parityTwist, C.diagTwist_serreElt, map_smul,
      LinearMap.smul_apply, hy, map_zero, LinearMap.zero_apply, smul_zero,
      mul_zero, add_zero, sub_zero]

/-- The normalized lowering operators satisfy the positive Serre relations
    on the free half algebra; no denominator invertibility is needed for this identity. -/
theorem lowerFree_serre (hπ : π ^ 2 = 1) (n : I → ℤ)
    {i j : I} (hij : i ≠ j) :
    (FreeAlgebra.lift k fun i ↦ lowerFree C q π i (n i)) (C.serreElt q π i j) = 0 := by
  let a : I → k := fun i ↦ Ring.inverse (vermaDenominator C q π i) * ((C.qi q i ^ n i : kˣ) : k)
  let b : I → k := fun i ↦ Ring.inverse (vermaDenominator C q π i) *
    (C.pii π i ^ (n i).natAbs * ((C.qi q i ^ (-n i) : kˣ) : k))
  have he : (FreeAlgebra.lift k fun i ↦ lowerFree C q π i (n i)) = numeratorEval C q π a b := by
    ext i x
    simp only [Function.comp_apply, numeratorEval, FreeAlgebra.lift_ι_apply]
    simp only [lowerFree, lowerNumerator,
      LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    dsimp [a, b]
    module
  rw [he]
  exact numeratorEval_serre C q π hπ a b hij

namespace GenericVerma
open Coefficients
variable {I : Type*} [DecidableEq I] [Finite I] (C : SuperCartanDatum I) (hC : C.BarConsistent)

private theorem lower_lift_mk (n : I → ℤ) (x y : PreF Coefficients.Ring I) :
    (FreeAlgebra.lift Coefficients.Ring fun i ↦ lower C hC i (n i)) x
      (C.toSerreF Coefficients.q pi y) =
    C.toSerreF Coefficients.q pi
      ((FreeAlgebra.lift Coefficients.Ring fun i ↦ lowerFree C Coefficients.q pi i (n i)) x y) := by
  induction x using FreeAlgebra.induction generalizing y with
  | grade0 c => simp [Module.algebraMap_end_apply]
  | grade1 i => simp [lower_mk]
  | add x z hx hz => simp [hx, hz]
  | mul x z hx hz => simp [Module.End.mul_apply, hx, hz]

/-- Positive Serre relations among the actual descended lowering endomorphisms.
    Finiteness and bar-consistency enter only through their existing quotient descent. -/
theorem lower_serre (n : I → ℤ) {i j : I} (hij : i ≠ j) :
    (FreeAlgebra.lift Coefficients.Ring fun i ↦ lower C hC i (n i))
      (C.serreElt Coefficients.q pi i j) = 0 := by
  ext z
  obtain ⟨y, rfl⟩ := C.toSerreF_surjective Coefficients.q pi z
  rw [lower_lift_mk, lowerFree_serre C Coefficients.q pi pi_sq n hij,
    LinearMap.zero_apply, map_zero]
  rfl

/-- The positive Serre relation as an explicit finite sum of compositions of
    the descended endomorphisms, with the existing Serre coefficients. -/
theorem lower_serre_sum (n : I → ℤ) {i j : I} (hij : i ≠ j) :
    ∑ r ∈ Finset.range (C.serreDeg i j + 1),
      C.serreCoeff Coefficients.q pi i j r •
        (lower C hC i (n i) ^ (C.serreDeg i j - r) *
          lower C hC j (n j) * lower C hC i (n i) ^ r) = 0 := by
  simpa only [SuperCartanDatum.serreElt, map_sum, map_smul, map_mul, map_pow,
    θ, FreeAlgebra.lift_ι_apply] using lower_serre C hC n hij

/-- The positive Serre half acts on the actual negative Serre half by the
    constructed highest-weight lowering operators. No faithfulness is claimed. -/
def positiveAction (n : I → ℤ) : C.serreF Coefficients.q pi →ₐ[Coefficients.Ring]
    Module.End Coefficients.Ring (C.serreF Coefficients.q pi) :=
  RingQuot.liftAlgHom Coefficients.Ring
    ⟨FreeAlgebra.lift Coefficients.Ring (fun i ↦ lower C hC i (n i)), fun x y h ↦ by
      cases h with
      | serre i j hij => rw [map_zero, lower_serre C hC n hij]⟩

@[simp] theorem positiveAction_θ (n : I → ℤ) (i : I) :
    positiveAction C hC n (C.toSerreF Coefficients.q pi (θ Coefficients.Ring i)) =
      lower C hC i (n i) := by
  change RingQuot.liftAlgHom Coefficients.Ring _
    (RingQuot.mkAlgHom Coefficients.Ring _ _) = _
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  simp [θ]

end GenericVerma
end OddMath.CoveringQuantum.UDot
