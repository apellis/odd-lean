/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.Slides
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient

/-!
# The global last dot in the cyclotomic algebra

Ports the dot-intertwiner input of
`Categorification/KLR/CyclotomicAction/Slides.lean` to the positive-height
cyclotomic superalgebra. The element is the sum of the last-dot entries on
words ending in the induction colour. Rows are targets, columns are sources,
and matrix multiplication reverses diagram composition. Thus reversing the
local dot-slide equation uses the square-one Koszul sign, not unsigned
commutation. The result supplies an element in the colour-cut corner; dot
transformations on induction supermodules are a separate construction.
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The finite diagonal sum of rightmost dots at height `n+1`. -/
def affineLastDot (i : I) (n : ℕ) : Hn D Sc (n + 1) :=
  ∑ w : Word I n, FiniteHomMatrix.single (appendWord i w) (appendWord i w)
    (inductionLastDot D Sc i w)

/-- Every summand has the parity of the appended colour. -/
theorem affineLastDot_parity (i : I) (n : ℕ) :
    affineLastDot D Sc i n ∈ affineParity D Sc (n + 1) (D.parity i) := by
  apply Submodule.sum_mem
  intro w _
  apply FiniteHomMatrix.single_mem_component
  exact MonoidalSupercategory.whiskerLeft_mem (wordObj D Sc w)
    (inductionStrandDot_parity D Sc i)

private theorem lastDot_mul_entry (i : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (appendWord i t)) :
    affineLastDot D Sc i n * FiniteHomMatrix.single (appendWord i t) (appendWord i s) f =
      FiniteHomMatrix.single (appendWord i t) (appendWord i s)
        (f ≫ inductionLastDot D Sc i t) := by
  rw [affineLastDot, Finset.sum_mul, Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective i n h)) _ _
  · simp

private theorem entry_mul_lastDot (i : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (appendWord i t)) :
    FiniteHomMatrix.single (appendWord i t) (appendWord i s) f * affineLastDot D Sc i n =
      FiniteHomMatrix.single (appendWord i t) (appendWord i s)
        (inductionLastDot D Sc i s ≫ f) := by
  rw [affineLastDot, Finset.mul_sum, Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective i n h.symm)) _ _
  · simp

/-- Signed commutation with every homogeneous affine element. -/
theorem affineLastDot_comm (i : I) (n : ℕ) {p : ZMod 2} {r : Hn D Sc n}
    (hr : r ∈ affineParity D Sc n p) :
    appendAlgebra D Sc i n r * affineLastDot D Sc i n =
      Supercategory.koszulSign p (D.parity i) •
        (affineLastDot D Sc i n * appendAlgebra D Sc i n r) := by
  change appendLinear D Sc i n r * _ = _ • (_ * appendLinear D Sc i n r)
  conv_lhs => rw [FiniteHomMatrix.eq_sum_single r, map_sum, Finset.sum_mul]
  conv_rhs => rw [FiniteHomMatrix.eq_sum_single r, map_sum, Finset.mul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [appendLinear_single, entry_mul_lastDot, lastDot_mul_entry]
  rw [induction_dot_slide D Sc i q.2 q.1 (r q) (hr q)]
  simp only [FiniteHomMatrix.single, DFinsupp.single_smul,
    Supercategory.koszulSign_smul_smul]

/-- The image of one acts as the identity on the global last dot. -/
theorem append_one_mul_affineLastDot (i : I) (n : ℕ) :
    appendAlgebra D Sc i n 1 * affineLastDot D Sc i n = affineLastDot D Sc i n := by
  change appendLinear D Sc i n (FiniteHomMatrix.localUnit Finset.univ) * _ = _
  rw [FiniteHomMatrix.localUnit, map_sum, Finset.sum_mul]
  conv_rhs => unfold affineLastDot
  apply Finset.sum_congr rfl
  intro w _
  change appendLinear D Sc i n (FiniteHomMatrix.single w w (𝟙 _)) * _ = _
  rw [appendLinear_single, entry_mul_lastDot]
  change FiniteHomMatrix.single _ _ (inductionLastDot D Sc i w ≫
    appendEnd D Sc i w 1) = _
  rw [map_one]
  exact congrArg (FiniteHomMatrix.single _ _) (Category.comp_id _)

/-- The other colour-cut identity follows from even commutation. -/
theorem affineLastDot_mul_append_one (i : I) (n : ℕ) :
    affineLastDot D Sc i n * appendAlgebra D Sc i n 1 = affineLastDot D Sc i n := by
  have h := affineLastDot_comm D Sc i n (SetLike.one_mem_graded (affineParity D Sc n))
  simpa only [Supercategory.koszulSign_zero_left, one_smul,
    append_one_mul_affineLastDot] using h.symm

/-- The last dot in the existing quotient at height `n+2`. -/
def cyclotomicLastDot (i : I) (a : I → _root_.Polynomial k) (n : ℕ) :
    CyclotomicAlgebra D Sc a (n + 1) :=
  cyclotomicMk D Sc a (n + 1) (affineLastDot D Sc i (n + 1))

theorem cyclotomicLastDot_parity (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    cyclotomicLastDot D Sc i a n ∈ cyclotomicParity D Sc a ha (n + 1) (D.parity i) :=
  cyclotomicMk_parity D Sc a ha (n + 1) (affineLastDot_parity D Sc i (n + 1))

/-- The global dot supercommutes with the genuine cyclotomic inclusion. -/
theorem cyclotomicLastDot_comm (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) {p : ZMod 2}
    {r : CyclotomicAlgebra D Sc a n} (hr : r ∈ cyclotomicParity D Sc a ha n p) :
    cyclotomicAppend D Sc i a n r * cyclotomicLastDot D Sc i a n =
      Supercategory.koszulSign p (D.parity i) •
        (cyclotomicLastDot D Sc i a n * cyclotomicAppend D Sc i a n r) := by
  obtain ⟨r, hr', rfl⟩ := cyclotomicParity_lift D Sc a ha n hr
  change cyclotomicMk D Sc a (n + 1) (appendAlgebra D Sc i (n + 1) r) *
    cyclotomicMk D Sc a (n + 1) (affineLastDot D Sc i (n + 1)) =
    Supercategory.koszulSign p (D.parity i) •
      (cyclotomicMk D Sc a (n + 1) (affineLastDot D Sc i (n + 1)) *
        cyclotomicMk D Sc a (n + 1) (appendAlgebra D Sc i (n + 1) r))
  rw [← map_mul, ← map_mul, ← map_zsmul]
  exact congrArg (cyclotomicMk D Sc a (n + 1)) (affineLastDot_comm D Sc i (n + 1) hr')

/-- Both corner identities hold without a polynomial-parity hypothesis. -/
theorem cyclotomicLastDot_corner (i : I) (a : I → _root_.Polynomial k) (n : ℕ) :
    cyclotomicAppend D Sc i a n 1 * cyclotomicLastDot D Sc i a n =
      cyclotomicLastDot D Sc i a n ∧
    cyclotomicLastDot D Sc i a n * cyclotomicAppend D Sc i a n 1 =
      cyclotomicLastDot D Sc i a n := by
  have h1 : cyclotomicAppend D Sc i a n 1 =
      cyclotomicMk D Sc a (n + 1) (appendAlgebra D Sc i (n + 1) 1) := by
    change cyclotomicAppendLinear D Sc i a n 1 = _
    rw [← map_one (cyclotomicMk D Sc a n), cyclotomicAppendLinear_mk]
  rw [h1, cyclotomicLastDot, ← map_mul, ← map_mul,
    append_one_mul_affineLastDot, affineLastDot_mul_append_one]
  exact ⟨rfl, rfl⟩

end OddMath.QuiverHecke
