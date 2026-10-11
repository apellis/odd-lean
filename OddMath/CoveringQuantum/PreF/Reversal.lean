import OddMath.CoveringQuantum.SerreForm

/-!
# Word reversal and the covering half form

Scalar-linear reversal exchanges the two skew derivatives. Hence simultaneous
reversal preserves the actual free form and its descended Serre half form. This
supplies the positive/reversed-half convention in Brundan–Ellis Theorem 10.1(3).
-/

noncomputable section
namespace OddMath.CoveringQuantum.PreF
variable {k I : Type*} [CommRing k]

/-- Scalar-linear reversal of words in the actual free algebra. -/
def wordReverse : PreF k I →ₗ[k] PreF k I :=
  (MulOpposite.opLinearEquiv k).symm.toLinearMap.comp
    (FreeAlgebra.lift k fun i : I ↦ MulOpposite.op (θ k i)).toLinearMap

@[simp] theorem wordReverse_algebraMap (c : k) :
    wordReverse (algebraMap k (PreF k I) c) = algebraMap k _ c := by
  simp [wordReverse]

@[simp] theorem wordReverse_one : wordReverse (1 : PreF k I) = 1 := by
  simp [wordReverse]

@[simp] theorem wordReverse_θ (i : I) : wordReverse (θ k i) = θ k i := by
  simp [wordReverse]

theorem wordReverse_mul (x y : PreF k I) :
    wordReverse (x * y) = wordReverse y * wordReverse x := by
  simp [wordReverse]

@[simp] theorem counit_wordReverse (x : PreF k I) : counit (wordReverse x) = counit x := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 i => simp
  | mul x y hx hy => simp [wordReverse_mul, hx, hy, mul_comm]
  | add x y hx hy => simp [hx, hy]

@[simp] theorem wordReverse_monomial (a : List I) :
    wordReverse (monomial k a) = monomial k a.reverse := by
  induction a with
  | nil => simp
  | cons i a ih => simp [wordReverse_mul, ih, List.reverse_cons, monomial_append]

variable [DecidableEq I] (χ : Bichar k I) (nm : I → k)

theorem rDeriv_wordReverse (i : I) (x : PreF k I) :
    rDeriv χ i (wordReverse x) = wordReverse (lDeriv χ i x) := by
  induction x using induction_left with
  | algebraMap c => simp
  | smul c x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]
  | θ_mul j x hx =>
    rw [wordReverse_mul, wordReverse_θ, rDeriv_mul_θ, lDeriv_θ_mul]
    split_ifs <;> simp [wordReverse_mul, hx]

/-- Reversal preserves the actual form, with no invertibility requirement on its normalization. -/
theorem form_wordReverse (x y : PreF k I) :
    form χ nm (wordReverse x) (wordReverse y) = form χ nm x y := by
  induction x using induction_left generalizing y with
  | algebraMap c => simp
  | smul c x hx => simp [hx]
  | add x z hx hz => simp [hx, hz]
  | θ_mul i x hx =>
    rw [wordReverse_mul, wordReverse_θ, form_mul_θ, rDeriv_wordReverse,
      hx, form_θ_mul]

/-- Simultaneous word reversal leaves the free form unchanged. -/
theorem form_monomial_reverse (a b : List I) :
    form χ nm (monomial k a.reverse) (monomial k b.reverse) =
      form χ nm (monomial k a) (monomial k b) := by
  simpa only [wordReverse_monomial] using form_wordReverse χ nm (monomial k a) (monomial k b)
end OddMath.CoveringQuantum.PreF

namespace OddMath.CoveringQuantum.SuperCartanDatum
variable {k I : Type*} [CommRing k] [DecidableEq I]
  (C : SuperCartanDatum I) (q : kˣ) (π : k) (hπ : π ^ 2 = 1)

/-- Simultaneous reversal invariance for the actual Serre half-form. -/
theorem serreForm_monomial_reverse (a b : List I) :
    C.serreForm q π hπ (C.toSerreF q π (PreF.monomial k a.reverse))
      (C.toSerreF q π (PreF.monomial k b.reverse)) =
    C.serreForm q π hπ (C.toSerreF q π (PreF.monomial k a))
      (C.toSerreF q π (PreF.monomial k b)) := by
  simp only [serreForm_toSerreF]
  exact PreF.form_monomial_reverse (C.chi q π) (C.norm q π) a b
end OddMath.CoveringQuantum.SuperCartanDatum
