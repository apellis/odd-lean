import OddMath.SKM.ScalarChange
import OddMath.SKM.MixedCrossingLocalExamples

/-! Brundan–Ellis (1.5), (1.6), (1.17): odd parameters under a
noninjective coefficient specialization. This tests parameter transport,
not yet the presented Hom base-change map. -/

namespace OddMath.SKM.ScalarChangeExamples

open MixedCrossingLocalExamples ScalarChange

private def source : Scalars oddDatum (ZMod 9) where
  t _ _ := 1
  t_self _ := rfl
  t_symm_of_d_eq_zero _ _ _ := rfl
  s _ _ _ _ := 0
  s_symm _ _ _ _ := rfl
  s_eq_zero _ _ _ _ _ := rfl
  two_isUnit _ := (ZMod.isUnit_iff_coprime 2 9).2 (by decide)

private def bubble : CScalars source where
  c _ _ := 1
  shift _ _ _ := rfl

private def specialize : ZMod 9 →+* ZMod 3 := ZMod.castHom (by decide : 3 ∣ 9) _

/-- Both odd colours retain their required invertible `2` after reduction. -/
theorem target_two_isUnit : IsUnit (2 : ZMod 3) :=
  (scalars oddDatum specialize source).two_isUnit ⟨false, rfl⟩

/-- The transported bubble units satisfy the weight-shift law. -/
theorem target_bubble_shift (μ : Bool → ℤ) (i j : Bool) :
    (cScalars oddDatum specialize bubble).c (μ + oddDatum.α j) i =
      (scalars oddDatum specialize source).t i j *
        (cScalars oddDatum specialize bubble).c μ i :=
  (cScalars oddDatum specialize bubble).shift μ i j

/-- This specialization kills a nonzero coefficient and is not a field-valued
embedding; consequently a proof via preserving independence cannot be used. -/
theorem specialization_kills_nonzero :
    (3 : ZMod 9) ≠ 0 ∧ specialize (3 : ZMod 9) = 0 := by
  constructor <;> decide

end OddMath.SKM.ScalarChangeExamples
