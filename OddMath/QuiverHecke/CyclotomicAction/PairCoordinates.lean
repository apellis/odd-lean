/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.Square

/-!
# Polynomial coordinates on the two-strand induction corner

Ports the endomorphism-polynomial input of
`Categorification/KLR/CyclotomicAction/Square.lean`. A family of word
endomorphisms embeds as a nonunital algebra in the finite matrix algebra;
its unit is precisely the composite colour cut, not the ambient unit.
This distinction is required when evaluating constant polynomial terms.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Diagonal insertion of endomorphisms on each last-pair word. -/
def pairEndMap (i j : I) (n : ℕ) :
    (∀ w : Word I n, End (wordObj D Sc (appendWord j (appendWord i w)))) →ₙₐ[k]
      Hn D Sc (n + 1 + 1) where
  toFun f := ∑ w, FiniteHomMatrix.single (appendWord j (appendWord i w))
    (appendWord j (appendWord i w)) (f w)
  map_zero' := by simp
  map_add' f g := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    exact FiniteHomMatrix.single_add _ _ _ _
  map_smul' c f := by
    change (∑ w, FiniteHomMatrix.single (appendWord j (appendWord i w))
      (appendWord j (appendWord i w)) (c • f w)) =
        c • ∑ w, FiniteHomMatrix.single (appendWord j (appendWord i w))
          (appendWord j (appendWord i w)) (f w)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro w _
    exact FiniteHomMatrix.single_smul _ _ _ _
  map_mul' f g := by
    symm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_mul, Finset.sum_eq_single w]
    · exact FiniteHomMatrix.single_mul_single _ _ _ _ _
    · intro b _ hb
      apply FiniteHomMatrix.single_mul_single_of_ne
      intro h
      exact hb (appendWord_injective i n (appendWord_injective j (n + 1) h))
    · simp

/-- The polynomial unit is the composite colour cut. -/
theorem pairEndMap_one (i j : I) (n : ℕ) :
    pairEndMap D Sc i j n 1 =
      appendAlgebra D Sc j (n + 1) (appendAlgebra D Sc i n 1) := by
  change (∑ w : Word I n, FiniteHomMatrix.single _ _ (𝟙 _)) =
    appendLinear D Sc j (n + 1)
      (appendLinear D Sc i n (FiniteHomMatrix.localUnit Finset.univ))
  rw [FiniteHomMatrix.localUnit, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro w _
  change FiniteHomMatrix.single _ _ (𝟙 _) =
    appendLinear D Sc j (n + 1) (appendLinear D Sc i n (FiniteHomMatrix.single w w (𝟙 _)))
  rw [appendLinear_single, appendLinear_single]
  change FiniteHomMatrix.single (appendWord j (appendWord i w)) (appendWord j (appendWord i w))
    (1 : End (wordObj D Sc (appendWord j (appendWord i w)))) =
    FiniteHomMatrix.single _ _ (appendEnd D Sc j _ (appendEnd D Sc i w 1))
  rw [map_one, map_one]

/-- Dot on the first added strand, supported on its two-colour cut. -/
def affinePairDotLeft (i j : I) (n : ℕ) : Hn D Sc (n + 1 + 1) :=
  pairEndMap D Sc i j n (fun w => dotE D Sc (appendWord j (appendWord i w)).1 w.1.length)

/-- Dot on the last added strand, supported on its two-colour cut. -/
def affinePairDotRight (i j : I) (n : ℕ) : Hn D Sc (n + 1 + 1) :=
  pairEndMap D Sc i j n (fun w => dotE D Sc (appendWord j (appendWord i w)).1 (w.1.length + 1))

/-- The equal-colour crossing is the corresponding endomorphism family. -/
theorem pairEndMap_cross (i : I) (n : ℕ) :
    pairEndMap D Sc i i n (inductionLastCrossing D Sc i i) = affineLastCrossing D Sc i i n := rfl

omit [Fintype I] in
/-- Positioned endomorphism coordinates for the equal-colour crossing. -/
theorem inductionLastCrossing_eq_crossE (i : I) {n : ℕ} (w : Word I n) :
    inductionLastCrossing D Sc i i w =
      crossE D Sc (appendWord i (appendWord i w)).1 w.1.length := by
  rw [inductionLastCrossing_eq_cl]
  exact (genE_eq D Sc (by
    simp [appendWord, pl, PG.ld, Shape.dom, Shape.cod, List.append_assoc])).symm

/-- The first signed nilHecke slide in the actual affine pair corner. -/
theorem affinePair_slide_left (i : I) (n : ℕ) :
    affineLastCrossing D Sc i i n * affinePairDotLeft D Sc i i n -
      SKM.zsign k (D.parity i * D.parity i) •
        (affinePairDotRight D Sc i i n * affineLastCrossing D Sc i i n) =
      appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n 1) := by
  let T : ∀ w : Word I n, End (wordObj D Sc (appendWord i (appendWord i w))) :=
    inductionLastCrossing D Sc i i
  let L : ∀ w : Word I n, End (wordObj D Sc (appendWord i (appendWord i w))) :=
    fun w => dotE D Sc (appendWord i (appendWord i w)).1 w.1.length
  let R : ∀ w : Word I n, End (wordObj D Sc (appendWord i (appendWord i w))) :=
    fun w => dotE D Sc (appendWord i (appendWord i w)).1 (w.1.length + 1)
  have h : T * L - SKM.zsign k (D.parity i * D.parity i) • (R * T) = 1 := by
    funext w
    dsimp only [T, L, R, Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply]
    erw [inductionLastCrossing_eq_crossE]
    exact crossE_dotE D Sc w.1 [] i rfl (by simp [appendWord, List.append_assoc])
  have hh := congrArg (pairEndMap D Sc i i n) h
  simpa only [map_sub, map_mul, map_smul, pairEndMap_cross, pairEndMap_one,
    affinePairDotLeft, affinePairDotRight, T, L, R] using hh

/-- The second signed nilHecke slide in the actual affine pair corner. -/
theorem affinePair_slide_right (i : I) (n : ℕ) :
    affinePairDotLeft D Sc i i n * affineLastCrossing D Sc i i n -
      SKM.zsign k (D.parity i * D.parity i) •
        (affineLastCrossing D Sc i i n * affinePairDotRight D Sc i i n) =
      appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n 1) := by
  let T : ∀ w : Word I n, End (wordObj D Sc (appendWord i (appendWord i w))) :=
    inductionLastCrossing D Sc i i
  let L : ∀ w : Word I n, End (wordObj D Sc (appendWord i (appendWord i w))) :=
    fun w => dotE D Sc (appendWord i (appendWord i w)).1 w.1.length
  let R : ∀ w : Word I n, End (wordObj D Sc (appendWord i (appendWord i w))) :=
    fun w => dotE D Sc (appendWord i (appendWord i w)).1 (w.1.length + 1)
  have h : L * T - SKM.zsign k (D.parity i * D.parity i) • (T * R) = 1 := by
    funext w
    dsimp only [T, L, R, Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply]
    erw [inductionLastCrossing_eq_crossE]
    exact dotE_crossE D Sc w.1 [] i rfl (by simp [appendWord, List.append_assoc])
  have hh := congrArg (pairEndMap D Sc i i n) h
  simpa only [map_sub, map_mul, map_smul, pairEndMap_cross, pairEndMap_one,
    affinePairDotLeft, affinePairDotRight, T, L, R] using hh

/-- The first pair dot in the actual positive-height cyclotomic quotient. -/
def cyclotomicPairDotLeft (i j : I) (a : I → _root_.Polynomial k) (n : ℕ) :
    CyclotomicAlgebra D Sc a (n + 1 + 1) :=
  cyclotomicMk D Sc a (n + 1 + 1) (affinePairDotLeft D Sc i j (n + 1))

/-- The last pair dot in the actual positive-height cyclotomic quotient. -/
def cyclotomicPairDotRight (i j : I) (a : I → _root_.Polynomial k) (n : ℕ) :
    CyclotomicAlgebra D Sc a (n + 1 + 1) :=
  cyclotomicMk D Sc a (n + 1 + 1) (affinePairDotRight D Sc i j (n + 1))

/-- The polynomial constant descends to the composite cyclotomic colour cut. -/
theorem cyclotomicPairCut_mk (i j : I) (a : I → _root_.Polynomial k) (n : ℕ) :
    cyclotomicMk D Sc a (n + 1 + 1)
      (appendAlgebra D Sc j (n + 1 + 1) (appendAlgebra D Sc i (n + 1) 1)) =
        cyclotomicAppend D Sc j a (n + 1) (cyclotomicAppend D Sc i a n 1) := by
  change _ = cyclotomicAppendLinear D Sc j a (n + 1) (cyclotomicAppendLinear D Sc i a n 1)
  rw [← (cyclotomicMk D Sc a n).map_one, cyclotomicAppendLinear_mk, cyclotomicAppendLinear_mk]

/-- The first signed nilHecke slide in the concrete cyclotomic pair corner. -/
theorem cyclotomicPair_slide_left (i : I) (a : I → _root_.Polynomial k) (n : ℕ) :
    cyclotomicLastCrossing D Sc i i a n * cyclotomicPairDotLeft D Sc i i a n -
      SKM.zsign k (D.parity i * D.parity i) •
        (cyclotomicPairDotRight D Sc i i a n * cyclotomicLastCrossing D Sc i i a n) =
      cyclotomicAppend D Sc i a (n + 1) (cyclotomicAppend D Sc i a n 1) := by
  rw [← cyclotomicPairCut_mk]
  simp only [cyclotomicLastCrossing, cyclotomicPairDotLeft, cyclotomicPairDotRight,
    ← map_mul, ← map_smul, ← map_sub]
  exact congrArg (cyclotomicMk D Sc a (n + 1 + 1)) (affinePair_slide_left D Sc i (n + 1))

/-- The second signed nilHecke slide in the concrete cyclotomic pair corner. -/
theorem cyclotomicPair_slide_right (i : I) (a : I → _root_.Polynomial k) (n : ℕ) :
    cyclotomicPairDotLeft D Sc i i a n * cyclotomicLastCrossing D Sc i i a n -
      SKM.zsign k (D.parity i * D.parity i) •
        (cyclotomicLastCrossing D Sc i i a n * cyclotomicPairDotRight D Sc i i a n) =
      cyclotomicAppend D Sc i a (n + 1) (cyclotomicAppend D Sc i a n 1) := by
  rw [← cyclotomicPairCut_mk]
  simp only [cyclotomicLastCrossing, cyclotomicPairDotLeft, cyclotomicPairDotRight,
    ← map_mul, ← map_smul, ← map_sub]
  exact congrArg (cyclotomicMk D Sc a (n + 1 + 1)) (affinePair_slide_right D Sc i (n + 1))

omit [Fintype I] in
/-- Parity of a positioned dot at a specified colour. -/
theorem positionedDot_parity {t : List I} {r : ℕ} {i : I} (hi : t[r]? = some i) :
    dotE D Sc t r ∈ Supercategory.parity (R := k) _ _ (D.parity i) := by
  rw [dotE_eq]
  unfold cl
  apply Presentation.diag_mem_homDeg'
  simp [degree_parity_mkD, pl_dot_of hi, Shape.parity]

/-- Parity of the first dot family, with no restriction on either colour. -/
theorem affinePairDotLeft_parity (i j : I) (n : ℕ) :
    affinePairDotLeft D Sc i j n ∈ affineParity D Sc (n + 1 + 1) (D.parity i) := by
  apply Submodule.sum_mem
  intro w _
  exact FiniteHomMatrix.single_mem_component _ _ (positionedDot_parity D Sc (by
    simp [appendWord, List.getElem?_append]))

/-- Parity of the second dot family, with no restriction on either colour. -/
theorem affinePairDotRight_parity (i j : I) (n : ℕ) :
    affinePairDotRight D Sc i j n ∈ affineParity D Sc (n + 1 + 1) (D.parity j) := by
  apply Submodule.sum_mem
  intro w _
  exact FiniteHomMatrix.single_mem_component _ _ (positionedDot_parity D Sc (by
    simp [appendWord, List.getElem?_append]))

/-- Homogeneity of the first cyclotomic pair dot. -/
theorem cyclotomicPairDotLeft_parity (i j : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    cyclotomicPairDotLeft D Sc i j a n ∈ cyclotomicParity D Sc a ha (n + 1 + 1) (D.parity i) :=
  cyclotomicMk_parity D Sc a ha (n + 1 + 1) (affinePairDotLeft_parity D Sc i j (n + 1))

/-- Homogeneity of the second cyclotomic pair dot. -/
theorem cyclotomicPairDotRight_parity (i j : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    cyclotomicPairDotRight D Sc i j a n ∈ cyclotomicParity D Sc a ha (n + 1 + 1) (D.parity j) :=
  cyclotomicMk_parity D Sc a ha (n + 1 + 1) (affinePairDotRight_parity D Sc i j (n + 1))

end OddMath.QuiverHecke
