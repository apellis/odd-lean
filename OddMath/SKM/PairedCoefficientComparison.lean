import OddMath.SKM.OrientedReduction
import OddMath.SKM.MatchingCoefficientPlacement

/-! Finite paired-sector comparison with principal and shortened-boundary
output labels. Different components may twist the full SYM coefficient
differently; only the selected unit pivot is used for detection. -/
noncomputable section
namespace OddMath.SKM
open scoped BigOperators
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k]

def pairedCoefficientComparison {A B : Type*}
    (column : (A × ℕ) → SYM D k →ₗ[k] (B →₀ SYM D k)) :
    ((A × ℕ) →₀ SYM D k) →ₗ[k] (B →₀ SYM D k) :=
  Finsupp.lsum k column

@[simp] theorem pairedCoefficientComparison_single {A B : Type*}
    (column : (A × ℕ) → SYM D k →ₗ[k] (B →₀ SYM D k))
    (i : A × ℕ) (p : SYM D k) :
    pairedCoefficientComparison column (Finsupp.single i p) = column i p :=
  Finsupp.lsum_single k column i p

/-- The output label set may be a disjoint union of the swapped-boundary
principal family and the shortened-boundary identity families. A unit
diagonal followed by any full-SYM parity involution detects all inputs. -/
theorem pairedCoefficientComparison_injective {A B : Type*}
    (column : (A × ℕ) → SYM D k →ₗ[k] (B →₀ SYM D k))
    (pivot : (A × ℕ) → B) (u : (A × ℕ) → SYM D k)
    (hu : ∀ i, IsUnit (u i)) (q : (A × ℕ) → ZMod 2)
    (hbelow : ∀ i j p, j.2 < i.2 → column j p (pivot i) = 0)
    (hsame : ∀ i j p, j.2 = i.2 → j.1 ≠ i.1 → column j p (pivot i) = 0)
    (hdiag : ∀ i p, column i p (pivot i) = u i * SYM.parityTwist D k (q i) p) :
    Function.Injective (pairedCoefficientComparison column) := by
  have hz (f : (A × ℕ) →₀ SYM D k)
      (hf : pairedCoefficientComparison column f = 0) : f = 0 := by
    apply OrientedReduction.eq_zero_of_crossing_dot_coefficients
      Prod.snd (fun _ => 0) (fun i j p => column j p (pivot i))
    · exact hbelow
    · intro i j p _ h
      omega
    · intro i j p he _ hne
      apply hsame i j p he
      intro hfirst
      exact hne (Prod.ext hfirst he)
    · intro i p hp
      rw [hdiag] at hp
      have ht : SYM.parityTwist D k (q i) p = 0 :=
        (hu i).mul_left_cancel (by simpa only [mul_zero] using hp)
      have H := congrArg (SYM.parityTwist D k (q i)) ht
      simpa only [SYM.parityTwist_involutive, map_zero] using H
    · intro i
      have H := congrArg (fun v : B →₀ SYM D k => v (pivot i)) hf
      simpa [pairedCoefficientComparison, Finsupp.lsum_apply,
        Finsupp.sum, Finsupp.finsetSum_apply] using H
  intro f g hfg
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, hfg, sub_self]
end OddMath.SKM
