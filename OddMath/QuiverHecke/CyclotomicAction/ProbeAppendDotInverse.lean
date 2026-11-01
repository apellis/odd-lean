import OddMath.QuiverHecke.CyclotomicAction.ProbeAllUnits
import OddMath.QuiverHecke.CyclotomicAction.LastDot
import OddMath.QuiverHecke.CyclotomicAction.PrefixQPDistinct

/-! # The actual append-corner inverse of the probe last dot

The existing probe algebra assumes a finite colour type. Accordingly the
inverse below sums over the finite type Word I (n+1). It makes no assertion
that words are finite in number over arbitrary colours. The resulting element
is an inverse in the literal append-idempotent corner.
-/
noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]

omit [Fintype I] in
theorem inductionLastDot_eq_position (i : I) {n : ℕ} (w : Word I n) :
    inductionLastDot D Sc i w = dotE D Sc (appendWord i w).val n := by
  have hs : inductionStrandDot D Sc i = dotE D Sc [i] 0 := by
    rw [dotE_eq]
    rfl
  rw [inductionLastDot, hs]
  change (pres D Sc).obj (ob D w.val) ◁ dotE D Sc [i] 0 =
    dotE D Sc (w.val ++ [i]) n
  simpa only [w.property] using whiskerLeft_dotE D Sc w.val i rfl

theorem probeInductionLastDot_isUnit (i : I) (m : I → ℕ) {n : ℕ} (w : Word I n) :
    IsUnit (cyclotomicWordEnd D Sc (probePolynomial (probeDotExponent D) m)
      (appendWord i w) (inductionLastDot D Sc i w)) := by
  rw [inductionLastDot_eq_position]
  exact probeWord_dots_isUnit D Sc m n n (by omega) (appendWord i w)

def probeLastDotWordUnit (i : I) (m : I → ℕ) {n : ℕ} (w : Word I n) :
    (CyclotomicWordCorner D Sc (probePolynomial (probeDotExponent D) m) (appendWord i w))ˣ :=
  Classical.choose (probeInductionLastDot_isUnit D Sc i m w)

theorem probeLastDotWordUnit_val (i : I) (m : I → ℕ) {n : ℕ} (w : Word I n) :
    (probeLastDotWordUnit D Sc i m w).val =
      cyclotomicWordEnd D Sc (probePolynomial (probeDotExponent D) m)
        (appendWord i w) (inductionLastDot D Sc i w) :=
  Classical.choose_spec (probeInductionLastDot_isUnit D Sc i m w)

theorem cyclotomicWordCorner_mul_of_ne (a : I → Polynomial k) {n : ℕ}
    (s t : Word I (n+1)) (hst : s ≠ t)
    (x : CyclotomicWordCorner D Sc a s) (y : CyclotomicWordCorner D Sc a t) :
    x.val * y.val = 0 := by
  have hx := ((Subsemigroup.mem_corner_iff
    (cyclotomicWordIdempotent_idem D Sc a s)).mp x.property).2
  have hy := ((Subsemigroup.mem_corner_iff
    (cyclotomicWordIdempotent_idem D Sc a t)).mp y.property).1
  have he : cyclotomicWordIdempotent D Sc a s *
      cyclotomicWordIdempotent D Sc a t = 0 := by
    change cyclotomicMk D Sc a n _ * cyclotomicMk D Sc a n _ = 0
    rw [← map_mul, Hn.wordIdempotent_orthogonal s t hst, map_zero]
  calc
    x.val * y.val =
        (x.val * cyclotomicWordIdempotent D Sc a s) *
          (cyclotomicWordIdempotent D Sc a t * y.val) := by rw [hx, hy]
    _ = x.val * (cyclotomicWordIdempotent D Sc a s *
          cyclotomicWordIdempotent D Sc a t) * y.val := by noncomm_ring
    _ = 0 := by rw [he, mul_zero, zero_mul]

theorem cyclotomicAppend_one_eq_sum (i : I) (a : I → Polynomial k) (n : ℕ) :
    cyclotomicAppend D Sc i a n 1 =
      ∑ w : Word I (n+1), cyclotomicWordIdempotent D Sc a (appendWord i w) := by
  have h1 : cyclotomicAppend D Sc i a n 1 =
      cyclotomicMk D Sc a (n+1) (appendAlgebra D Sc i (n+1) 1) := by
    change cyclotomicAppendLinear D Sc i a n 1 = _
    rw [← map_one (cyclotomicMk D Sc a n), cyclotomicAppendLinear_mk]
  rw [h1]
  change cyclotomicMk D Sc a (n+1)
    (appendLinear D Sc i (n+1) (FiniteHomMatrix.localUnit Finset.univ)) = _
  rw [FiniteHomMatrix.localUnit, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro w _
  change cyclotomicMk D Sc a (n+1)
    (appendLinear D Sc i (n+1) (FiniteHomMatrix.single w w (𝟙 _))) = _
  rw [appendLinear_single]
  change cyclotomicMk D Sc a (n+1)
    (FiniteHomMatrix.single _ _ (appendEnd D Sc i w 1)) = _
  rw [map_one]
  rfl

def probeLastDotInverseSum (i : I) (m : I → ℕ) (n : ℕ) :
    CyclotomicAlgebra D Sc (probePolynomial (probeDotExponent D) m) (n+1) :=
  ∑ w : Word I (n+1), (probeLastDotWordUnit D Sc i m w).inv.val

theorem probeLastDot_mul_inverseSum (i : I) (m : I → ℕ) (n : ℕ) :
    cyclotomicLastDot D Sc i (probePolynomial (probeDotExponent D) m) n *
      probeLastDotInverseSum D Sc i m n =
      cyclotomicAppend D Sc i (probePolynomial (probeDotExponent D) m) n 1 := by
  rw [cyclotomicLastDot, affineLastDot, map_sum,
    probeLastDotInverseSum, Finset.sum_mul, cyclotomicAppend_one_eq_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.mul_sum, Finset.sum_eq_single w]
  · have h := congrArg (fun x : CyclotomicWordCorner D Sc
        (probePolynomial (probeDotExponent D) m) (appendWord i w) => x.val)
      (probeLastDotWordUnit D Sc i m w).val_inv
    rw [probeLastDotWordUnit_val] at h
    exact h
  · intro z _ hzw
    apply cyclotomicWordCorner_mul_of_ne D Sc
      (probePolynomial (probeDotExponent D) m) (appendWord i w) (appendWord i z)
      (fun h => hzw (appendWord_injective i (n+1) h.symm))
      (cyclotomicWordEnd D Sc (probePolynomial (probeDotExponent D) m)
        (appendWord i w) (inductionLastDot D Sc i w))
      ((probeLastDotWordUnit D Sc i m z).inv)
  · simp

theorem probeLastDot_inverseSum_mul (i : I) (m : I → ℕ) (n : ℕ) :
    probeLastDotInverseSum D Sc i m n *
      cyclotomicLastDot D Sc i (probePolynomial (probeDotExponent D) m) n =
      cyclotomicAppend D Sc i (probePolynomial (probeDotExponent D) m) n 1 := by
  rw [cyclotomicLastDot, affineLastDot, map_sum,
    probeLastDotInverseSum, Finset.sum_mul, cyclotomicAppend_one_eq_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.mul_sum, Finset.sum_eq_single w]
  · have h := congrArg (fun x : CyclotomicWordCorner D Sc
        (probePolynomial (probeDotExponent D) m) (appendWord i w) => x.val)
      (probeLastDotWordUnit D Sc i m w).inv_val
    rw [probeLastDotWordUnit_val] at h
    exact h
  · intro z _ hzw
    apply cyclotomicWordCorner_mul_of_ne D Sc
      (probePolynomial (probeDotExponent D) m) (appendWord i w) (appendWord i z)
      (fun h => hzw (appendWord_injective i (n+1) h.symm))
      ((probeLastDotWordUnit D Sc i m w).inv)
      (cyclotomicWordEnd D Sc (probePolynomial (probeDotExponent D) m)
        (appendWord i z) (inductionLastDot D Sc i z))
  · simp


theorem probeAppendIdempotent (i : I) (a : I → Polynomial k) (n : ℕ) :
    IsIdempotentElem (cyclotomicAppend D Sc i a n 1) := by
  change cyclotomicAppend D Sc i a n 1 * cyclotomicAppend D Sc i a n 1 =
    cyclotomicAppend D Sc i a n 1
  rw [← map_mul, one_mul]

abbrev ProbeAppendCorner (i : I) (a : I → Polynomial k) (n : ℕ) :=
  (probeAppendIdempotent D Sc i a n).Corner

def probeAppendLastDot (i : I) (m : I → ℕ) (n : ℕ) :
    ProbeAppendCorner D Sc i (probePolynomial (probeDotExponent D) m) n :=
  ⟨cyclotomicLastDot D Sc i (probePolynomial (probeDotExponent D) m) n,
    (Subsemigroup.mem_corner_iff (probeAppendIdempotent D Sc i _ n)).mpr
      (cyclotomicLastDot_corner D Sc i _ n)⟩

/-- Project the finite sum of word inverses into the literal append corner. -/
def probeAppendDotInverse (i : I) (m : I → ℕ) (n : ℕ) :
    ProbeAppendCorner D Sc i (probePolynomial (probeDotExponent D) m) n :=
  let e := cyclotomicAppend D Sc i (probePolynomial (probeDotExponent D) m) n 1
  let x := probeLastDotInverseSum D Sc i m n
  ⟨e * x * e, by
    have he : e*e=e := probeAppendIdempotent D Sc i _ n
    apply (Subsemigroup.mem_corner_iff (probeAppendIdempotent D Sc i _ n)).mpr
    constructor
    · calc
        e * (e*x*e) = (e*e)*x*e := by noncomm_ring
        _ = e*x*e := by rw [he]
    · calc
        (e*x*e)*e = e*x*(e*e) := by noncomm_ring
        _ = e*x*e := by rw [he]⟩

theorem probeAppendLastDot_mul_inverse (i : I) (m : I → ℕ) (n : ℕ) :
    probeAppendLastDot D Sc i m n * probeAppendDotInverse D Sc i m n = 1 := by
  apply Subtype.ext
  let e := cyclotomicAppend D Sc i (probePolynomial (probeDotExponent D) m) n 1
  let c := cyclotomicLastDot D Sc i (probePolynomial (probeDotExponent D) m) n
  let x := probeLastDotInverseSum D Sc i m n
  have hce : c*e=c := (cyclotomicLastDot_corner D Sc i _ n).2
  have hcx : c*x=e := probeLastDot_mul_inverseSum D Sc i m n
  have he : e*e=e := probeAppendIdempotent D Sc i _ n
  change c * (e*x*e) = e
  calc
    c * (e*x*e) = ((c*e)*x)*e := by noncomm_ring
    _ = (c*x)*e := by rw [hce]
    _ = e*e := by rw [hcx]
    _ = e := he

theorem probeAppendLastDot_inverse_mul (i : I) (m : I → ℕ) (n : ℕ) :
    probeAppendDotInverse D Sc i m n * probeAppendLastDot D Sc i m n = 1 := by
  apply Subtype.ext
  let e := cyclotomicAppend D Sc i (probePolynomial (probeDotExponent D) m) n 1
  let c := cyclotomicLastDot D Sc i (probePolynomial (probeDotExponent D) m) n
  let x := probeLastDotInverseSum D Sc i m n
  have hec : e*c=c := (cyclotomicLastDot_corner D Sc i _ n).1
  have hxc : x*c=e := probeLastDot_inverseSum_mul D Sc i m n
  have he : e*e=e := probeAppendIdempotent D Sc i _ n
  change (e*x*e) * c = e
  calc
    (e*x*e)*c = e*(x*(e*c)) := by noncomm_ring
    _ = e*(x*c) := by rw [hec]
    _ = e*e := by rw [hxc]
    _ = e := he

/-- The existing append-idempotent last dot is a unit in its actual corner. -/
theorem probeAppendLastDot_isUnit (i : I) (m : I → ℕ) (n : ℕ) :
    IsUnit (probeAppendLastDot D Sc i m n) :=
  ⟨⟨_, probeAppendDotInverse D Sc i m n,
    probeAppendLastDot_mul_inverse D Sc i m n,
    probeAppendLastDot_inverse_mul D Sc i m n⟩, rfl⟩


end OddMath.QuiverHecke
