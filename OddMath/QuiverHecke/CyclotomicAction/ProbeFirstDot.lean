import OddMath.QuiverHecke.CyclotomicAction.ProbeWordCorner
import Mathlib.RingTheory.Nilpotent.Basic

/-! # First-dot units for cofinal cyclotomic probes

The specializations `(u²-1)^m` at odd colours and `(u-1)^m` at even
colours in `InvertibleDotProbe.md` §3 give literal units in the actual
cyclotomic word corner. Exponents and powers may vary with colour.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  [Fintype I]

def probePolynomial (e m : I → ℕ) (i : I) : Polynomial k :=
  (Polynomial.X ^ e i - 1) ^ m i

/-- The first-position relation itself supplies a unit; its proof does not
require finite dimensionality, a nonzero word, or a flat specialization. -/
theorem probePolynomial_firstDot_isUnit (e m : I → ℕ) {n : ℕ}
    (s : Word I (n + 1))
    (he : e (s.val.get ⟨0, by rw [s.property]; omega⟩) ≠ 0) :
    IsUnit (cyclotomicWordEnd D Sc (probePolynomial e m) s (dotE D Sc s.val 0)) := by
  let i := s.val.get ⟨0, by rw [s.property]; omega⟩
  let x := cyclotomicWordEnd D Sc (probePolynomial e m) s (dotE D Sc s.val 0)
  have hx : IsNilpotent (x ^ e i - 1) := by
    refine ⟨m i, ?_⟩
    have h := cyclotomicWordEnd_generator D Sc (probePolynomial e m) s
    simpa only [probePolynomial, map_pow, map_sub, Polynomial.aeval_X, map_one, map_zero,
      i, x] using h
  have hunit : IsUnit (x ^ e i) := by
    simpa only [add_sub_cancel] using hx.isUnit_one_add
  exact (isUnit_pow_iff he).mp hunit

/-- The exponent dictated by the parity of the simple root. -/
def probeDotExponent (i : I) : ℕ := if D.parity i = 1 then 2 else 1

theorem probe_firstDot_isUnit (m : I → ℕ) {n : ℕ} (s : Word I (n + 1)) :
    IsUnit (cyclotomicWordEnd D Sc (probePolynomial (probeDotExponent D) m) s
      (dotE D Sc s.val 0)) := by
  apply probePolynomial_firstDot_isUnit
  simp only [probeDotExponent]
  split_ifs <;> decide

end OddMath.QuiverHecke
