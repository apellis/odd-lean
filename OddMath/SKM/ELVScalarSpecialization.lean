import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientTransport

/-! # Scalar specialization of full ELV coefficients

The ordinary probe specialization of `InvertibleDotProbe.md` §1 kills the
exterior generators and assigns ordinary scalar values to the finitely many
surviving elementary generators. This descends through the exact ELV ideal,
including the even-cutoff delta-times-top relation. It does not descend
through positive-weight coefficient truncations or preserve integer grading.
-/
noncomputable section
open scoped Classical
namespace OddMath.SKM.SYM
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] (D : Datum I X)

private def scalarGen (values : I × ℕ → k) : SYMGen D → k
  | .inl p => values p
  | .inr _ => 0

private theorem scalarGen_rel (values : I × ℕ → k)
    {x y : FreeAlgebra k (SYMGen D)} (h : SYMRel D k x y) :
    FreeAlgebra.lift k (scalarGen D values) x =
      FreeAlgebra.lift k (scalarGen D values) y := by
  cases h with
  | polynomial p q => simp [scalarGen, mul_comm]
  | mixed p i => simp [scalarGen]
  | exterior i j => simp [scalarGen]
  | square i => simp [scalarGen]

def scalarEvaluation (values : I × ℕ → k) : SYM D k →ₐ[k] k :=
  RingQuot.liftAlgHom k
    ⟨FreeAlgebra.lift k (scalarGen D values), fun _ _ h => scalarGen_rel D values h⟩

@[simp] theorem scalarEvaluation_e (values : I × ℕ → k) (i : I) (r : ℕ) :
    scalarEvaluation D values (e D k i r) = values (i,r) := by
  simp only [scalarEvaluation, e, ι, mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    FreeAlgebra.lift_ι_apply, scalarGen]

@[simp] theorem scalarEvaluation_delta (values : I × ℕ → k)
    (i : {i : I // D.parity i = 1}) :
    scalarEvaluation D values (delta D k i) = 0 := by
  simp only [scalarEvaluation, delta, ι, mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    FreeAlgebra.lift_ι_apply, scalarGen]

/-- The coefficient ideal vanishes under scalar specialization when the
elementary values above the precise colour rank vanish. -/
theorem scalarEvaluation_ideal (cutoff : I → ℕ) (values : I × ℕ → k)
    (hvalues : ∀ i r, elvElementaryRank D cutoff i ≤ r → values (i,r) = 0)
    {x : SYM D k} (hx : x ∈ elvCoefficientIdeal D k cutoff) :
    scalarEvaluation D values x = 0 := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    rcases hx with ⟨i, r, hr, rfl⟩ | ⟨i, _, rfl⟩
    · rw [scalarEvaluation_e, hvalues i r hr]
    · rw [map_mul, scalarEvaluation_delta, zero_mul]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | neg x _ hx => rw [map_neg, hx, neg_zero]
  | left_absorb a x _ hx => rw [map_mul, hx, mul_zero]
  | right_absorb a x _ hx => rw [map_mul, hx, zero_mul]

/-- The scalar specialization of the full, untruncated ELV coefficient
algebra. No vanishing of positive-degree scalar values is required. -/
def elvScalarEvaluation (cutoff : I → ℕ) (values : I × ℕ → k)
    (hvalues : ∀ i r, elvElementaryRank D cutoff i ≤ r → values (i,r) = 0) :
    ELVCoefficientAlgebra (k := k) D cutoff →ₐ[k] k :=
  (elvCoefficientIdeal D k cutoff).ringCon.liftₐ (scalarEvaluation D values) (by
    intro x y hxy
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact scalarEvaluation_ideal D cutoff values hvalues
      ((TwoSidedIdeal.rel_iff _ _ _).mp hxy))

@[simp] theorem elvScalarEvaluation_quotient (cutoff : I → ℕ)
    (values : I × ℕ → k)
    (hvalues : ∀ i r, elvElementaryRank D cutoff i ≤ r → values (i,r) = 0)
    (x : SYM D k) :
    elvScalarEvaluation D cutoff values hvalues (elvCoefficientQuotient D cutoff x) =
      scalarEvaluation D values x := rfl

end OddMath.SKM.SYM
