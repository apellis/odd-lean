import OddMath.QuiverHecke.CyclotomicAction.ProbeAppendDotInverse
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightDot

/-! # Probe dot inverses including the vacuum height
This supplies the all-height algebra input to the dot inversion of
`docs/Nondegeneracy/InvertibleDotProbe.md`, Section 5, equation (6).
The finite sum of literal word-corner inverses is taken over Word I n.
At n = 0 this is the unique empty word and uses the existing first-dot unit.
-/
noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
open scoped Classical
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]

theorem heightLastDot_eq_affine (i : I) (a : I → Polynomial k) (n : ℕ) :
    heightLastDot D Sc a i n =
      cyclotomicMk D Sc a n (affineLastDot D Sc i n) := by
  cases n <;> rfl

theorem heightAppend_one_eq_sum (i : I) (a : I → Polynomial k) (n : ℕ) :
    heightAppend D Sc a i n 1 =
      ∑ w : Word I n, cyclotomicWordIdempotent D Sc a (appendWord i w) := by
  have h1 : heightAppend D Sc a i n 1 =
      cyclotomicMk D Sc a n (appendAlgebra D Sc i n 1) := by
    cases n with
    | zero => rfl
    | succ n =>
      change cyclotomicAppendLinear D Sc i a n 1 = _
      rw [← map_one (cyclotomicMk D Sc a n), cyclotomicAppendLinear_mk]
  rw [h1]
  change cyclotomicMk D Sc a n
    (appendLinear D Sc i n (FiniteHomMatrix.localUnit Finset.univ)) = _
  rw [FiniteHomMatrix.localUnit, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro w _
  change cyclotomicMk D Sc a n
    (appendLinear D Sc i n (FiniteHomMatrix.single w w (𝟙 _))) = _
  rw [appendLinear_single]
  change cyclotomicMk D Sc a n
    (FiniteHomMatrix.single _ _ (appendEnd D Sc i w 1)) = _
  rw [map_one]
  rfl

def probeHeightLastDotInverseSum (i : I) (m : I → ℕ) (n : ℕ) :
    heightAlgebra D Sc (probePolynomial (probeDotExponent D) m) (n+1) :=
  ∑ w : Word I n, (probeLastDotWordUnit D Sc i m w).inv.val

theorem probeHeightLastDot_mul_inverseSum (i : I) (m : I → ℕ) (n : ℕ) :
    heightLastDot D Sc (probePolynomial (probeDotExponent D) m) i n *
      probeHeightLastDotInverseSum D Sc i m n =
      heightAppend D Sc (probePolynomial (probeDotExponent D) m) i n 1 := by
  rw [heightLastDot_eq_affine, affineLastDot, map_sum,
    probeHeightLastDotInverseSum, Finset.sum_mul, heightAppend_one_eq_sum]
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
      (fun h => hzw (appendWord_injective i n h.symm))
      (cyclotomicWordEnd D Sc (probePolynomial (probeDotExponent D) m)
        (appendWord i w) (inductionLastDot D Sc i w))
      ((probeLastDotWordUnit D Sc i m z).inv)
  · simp

theorem probeHeightLastDot_inverseSum_mul (i : I) (m : I → ℕ) (n : ℕ) :
    probeHeightLastDotInverseSum D Sc i m n *
      heightLastDot D Sc (probePolynomial (probeDotExponent D) m) i n =
      heightAppend D Sc (probePolynomial (probeDotExponent D) m) i n 1 := by
  rw [heightLastDot_eq_affine, affineLastDot, map_sum,
    probeHeightLastDotInverseSum, Finset.sum_mul, heightAppend_one_eq_sum]
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
      (fun h => hzw (appendWord_injective i n h.symm))
      ((probeLastDotWordUnit D Sc i m w).inv)
      (cyclotomicWordEnd D Sc (probePolynomial (probeDotExponent D) m)
        (appendWord i z) (inductionLastDot D Sc i z))
  · simp


theorem probeHeightAppendIdempotent (i : I) (a : I → Polynomial k) (n : ℕ) :
    IsIdempotentElem (heightAppend D Sc a i n 1) := by
  change heightAppend D Sc a i n 1 * heightAppend D Sc a i n 1 =
    heightAppend D Sc a i n 1
  rw [← map_mul, one_mul]

abbrev ProbeHeightAppendCorner (i : I) (a : I → Polynomial k) (n : ℕ) :=
  (probeHeightAppendIdempotent D Sc i a n).Corner

def probeHeightAppendLastDot (i : I) (m : I → ℕ) (n : ℕ) :
    ProbeHeightAppendCorner D Sc i (probePolynomial (probeDotExponent D) m) n :=
  ⟨heightLastDot D Sc (probePolynomial (probeDotExponent D) m) i n,
    (Subsemigroup.mem_corner_iff (probeHeightAppendIdempotent D Sc i _ n)).mpr
      (heightLastDot_corner D Sc _ i n)⟩

/-- Project the finite sum of word inverses into the literal append corner. -/
def probeHeightAppendDotInverse (i : I) (m : I → ℕ) (n : ℕ) :
    ProbeHeightAppendCorner D Sc i (probePolynomial (probeDotExponent D) m) n :=
  let e := heightAppend D Sc (probePolynomial (probeDotExponent D) m) i n 1
  let x := probeHeightLastDotInverseSum D Sc i m n
  ⟨e * x * e, by
    have he : e*e=e := probeHeightAppendIdempotent D Sc i _ n
    apply (Subsemigroup.mem_corner_iff (probeHeightAppendIdempotent D Sc i _ n)).mpr
    constructor
    · calc
        e * (e*x*e) = (e*e)*x*e := by noncomm_ring
        _ = e*x*e := by rw [he]
    · calc
        (e*x*e)*e = e*x*(e*e) := by noncomm_ring
        _ = e*x*e := by rw [he]⟩

theorem probeHeightAppendLastDot_mul_inverse (i : I) (m : I → ℕ) (n : ℕ) :
    probeHeightAppendLastDot D Sc i m n * probeHeightAppendDotInverse D Sc i m n = 1 := by
  apply Subtype.ext
  let e := heightAppend D Sc (probePolynomial (probeDotExponent D) m) i n 1
  let c := heightLastDot D Sc (probePolynomial (probeDotExponent D) m) i n
  let x := probeHeightLastDotInverseSum D Sc i m n
  have hce : c*e=c := (heightLastDot_corner D Sc _ i n).2
  have hcx : c*x=e := probeHeightLastDot_mul_inverseSum D Sc i m n
  have he : e*e=e := probeHeightAppendIdempotent D Sc i _ n
  change c * (e*x*e) = e
  calc
    c * (e*x*e) = ((c*e)*x)*e := by noncomm_ring
    _ = (c*x)*e := by rw [hce]
    _ = e*e := by rw [hcx]
    _ = e := he

theorem probeHeightAppendLastDot_inverse_mul (i : I) (m : I → ℕ) (n : ℕ) :
    probeHeightAppendDotInverse D Sc i m n * probeHeightAppendLastDot D Sc i m n = 1 := by
  apply Subtype.ext
  let e := heightAppend D Sc (probePolynomial (probeDotExponent D) m) i n 1
  let c := heightLastDot D Sc (probePolynomial (probeDotExponent D) m) i n
  let x := probeHeightLastDotInverseSum D Sc i m n
  have hec : e*c=c := (heightLastDot_corner D Sc _ i n).1
  have hxc : x*c=e := probeHeightLastDot_inverseSum_mul D Sc i m n
  have he : e*e=e := probeHeightAppendIdempotent D Sc i _ n
  change (e*x*e) * c = e
  calc
    (e*x*e)*c = e*(x*(e*c)) := by noncomm_ring
    _ = e*(x*c) := by rw [hec]
    _ = e*e := by rw [hxc]
    _ = e := he

/-- The existing append-idempotent last dot is a unit in its actual corner. -/
theorem probeHeightAppendLastDot_isUnit (i : I) (m : I → ℕ) (n : ℕ) :
    IsUnit (probeHeightAppendLastDot D Sc i m n) :=
  ⟨⟨_, probeHeightAppendDotInverse D Sc i m n,
    probeHeightAppendLastDot_mul_inverse D Sc i m n,
    probeHeightAppendLastDot_inverse_mul D Sc i m n⟩, rfl⟩


end OddMath.QuiverHecke.CyclotomicAction
