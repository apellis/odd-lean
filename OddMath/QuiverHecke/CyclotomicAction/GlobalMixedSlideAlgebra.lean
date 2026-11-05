/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalSlideAlgebra

/-!
# The distinct-colour dot–crossing relations of the last pair of strands

The algebra half of the distinct-colour slides (1.8) of Brundan–Ellis, arXiv:1701.04133v2,
Definition 1.5. For distinct colours `i ≠ j` the quiver Hecke supercategory has, with
`ε = (-1)^{|i||j|}` and diagrams read bottom to top,

  `x_i τ = ε τ x_i`,  `τ x_j = ε x_j τ`,

the dot staying on the strand of its colour (`slide_left_ne`, `slide_right_ne`). Whiskering by
an old word gives the corresponding identities between the last-pair crossing, the appended
dot and the new last dot (`induction_slide_left_ne`, `induction_slide_right_ne`). Since matrix
multiplication reverses diagram composition, in the affine algebra and at every height of the
extended tower they read

  `c φⱼ(y_i) = ε y_i c`,  `φᵢ(y_j) c = ε c y_j`

with `c` the last-pair crossing of `heightLastCrossing D Sc a i j n`, `y` the new last dot and
`φ` the append map (`heightLastCrossing_slide_left_ne`, `heightLastCrossing_slide_right_ne`).
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
namespace OddMath.QuiverHecke
open SKM (zsign)
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

section Local
variable (i j : I)

theorem inductionStrandDot_whiskerRight_comp_crossing_ne :
    inductionStrandDot D Sc i ▷ (pres D Sc).obj (ob D [j]) ≫ inductionStrandCrossing D Sc i j =
      cl D Sc [i, j] [j, i] [.dot 0, .cross 0]
        (by simp [pl, PG.ld, PG.act, Shape.dom, Shape.cod]) := by
  rw [inductionStrandDot, inductionStrandCrossing, Presentation.diag_whiskerRight, cl]
  exact (Presentation.diag_comp _ _ _).symm.trans (Presentation.diag_eq_of_layers_eq _ rfl)

theorem inductionStrandCrossing_comp_whiskerLeft_dot_ne :
    inductionStrandCrossing D Sc i j ≫ (pres D Sc).obj (ob D [j]) ◁ inductionStrandDot D Sc i =
      cl D Sc [i, j] [j, i] [.cross 0, .dot 1]
        (by simp [pl, PG.ld, PG.act, Shape.dom, Shape.cod]) := by
  rw [inductionStrandDot, inductionStrandCrossing, Presentation.diag_whiskerLeft, cl]
  exact (Presentation.diag_comp _ _ _).symm.trans (Presentation.diag_eq_of_layers_eq _ rfl)

theorem inductionStrandCrossing_comp_dot_whiskerRight_ne :
    inductionStrandCrossing D Sc i j ≫ inductionStrandDot D Sc j ▷ (pres D Sc).obj (ob D [i]) =
      cl D Sc [i, j] [j, i] [.cross 0, .dot 0]
        (by simp [pl, PG.ld, PG.act, Shape.dom, Shape.cod]) := by
  rw [inductionStrandDot, inductionStrandCrossing, Presentation.diag_whiskerRight, cl]
  exact (Presentation.diag_comp _ _ _).symm.trans (Presentation.diag_eq_of_layers_eq _ rfl)

theorem whiskerLeft_dot_comp_inductionStrandCrossing_ne :
    (pres D Sc).obj (ob D [i]) ◁ inductionStrandDot D Sc j ≫ inductionStrandCrossing D Sc i j =
      cl D Sc [i, j] [j, i] [.dot 1, .cross 0]
        (by simp [pl, PG.ld, PG.act, Shape.dom, Shape.cod]) := by
  rw [inductionStrandDot, inductionStrandCrossing, Presentation.diag_whiskerLeft, cl]
  exact (Presentation.diag_comp _ _ _).symm.trans (Presentation.diag_eq_of_layers_eq _ rfl)

variable {i j}

/-- **The left dot slide on two strands of distinct colours**, `x_i τ = ε τ x_i`. -/
theorem inductionStrand_slide_left_ne (hij : i ≠ j) :
    (inductionStrandDot D Sc i ▷ (pres D Sc).obj (ob D [j]) ≫ inductionStrandCrossing D Sc i j :
        (pres D Sc).obj (ob D [i, j]) ⟶ (pres D Sc).obj (ob D [j, i])) =
      zsign k (D.parity i * D.parity j) •
        (inductionStrandCrossing D Sc i j ≫
          (pres D Sc).obj (ob D [j]) ◁ inductionStrandDot D Sc i :
          (pres D Sc).obj (ob D [i, j]) ⟶ (pres D Sc).obj (ob D [j, i])) := by
  erw [inductionStrandDot_whiskerRight_comp_crossing_ne,
    inductionStrandCrossing_comp_whiskerLeft_dot_ne]
  exact slide_left_ne D Sc [] [] i j hij _ _

/-- **The right dot slide on two strands of distinct colours**, `τ x_j = ε x_j τ`. -/
theorem inductionStrand_slide_right_ne (hij : i ≠ j) :
    (inductionStrandCrossing D Sc i j ≫ inductionStrandDot D Sc j ▷ (pres D Sc).obj (ob D [i]) :
        (pres D Sc).obj (ob D [i, j]) ⟶ (pres D Sc).obj (ob D [j, i])) =
      zsign k (D.parity i * D.parity j) •
        ((pres D Sc).obj (ob D [i]) ◁ inductionStrandDot D Sc j ≫
          inductionStrandCrossing D Sc i j :
          (pres D Sc).obj (ob D [i, j]) ⟶ (pres D Sc).obj (ob D [j, i])) := by
  erw [inductionStrandCrossing_comp_dot_whiskerRight_ne,
    whiskerLeft_dot_comp_inductionStrandCrossing_ne]
  exact slide_right_ne D Sc [] [] i j hij _ _

end Local

section Word
variable {i j : I}

/-- Conjugating a scalar two-strand identity by the associators. -/
theorem associator_conj_smul {W Y₁ Y₂ Z₁ Z₂ : H D Sc} (f g : Y₁ ⊗ Y₂ ⟶ Z₁ ⊗ Z₂)
    (c : k) (h : f = c • g) :
    (α_ W Y₁ Y₂).hom ≫ W ◁ f ≫ (α_ W Z₁ Z₂).inv =
      c • ((α_ W Y₁ Y₂).hom ≫ W ◁ g ≫ (α_ W Z₁ Z₂).inv) := by
  rw [h, MonoidalSupercategory.whiskerLeft_smul (R := k), Linear.smul_comp,
    Linear.comp_smul]

/-- **The left dot slide on the last pair of an appended word, distinct colours.** -/
theorem induction_slide_left_ne (hij : i ≠ j) {n : ℕ} (w : Word I n) :
    appendHom D Sc j _ _ (inductionLastDot D Sc i w) ≫ inductionLastCrossing D Sc i j w =
      zsign k (D.parity i * D.parity j) •
        (inductionLastCrossing D Sc i j w ≫ inductionLastDot D Sc i (appendWord j w)) := by
  change (wordObj D Sc w ◁ inductionStrandDot D Sc i) ▷ (pres D Sc).obj (ob D [j]) ≫
      (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D [j]))).hom ≫
      wordObj D Sc w ◁ strandCrossingTensor D Sc i j ≫
      (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [j])) ((pres D Sc).obj (ob D [i]))).inv =
    zsign k (D.parity i * D.parity j) •
      (((α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D [j]))).hom ≫
        wordObj D Sc w ◁ strandCrossingTensor D Sc i j ≫
        (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [j])) ((pres D Sc).obj (ob D [i]))).inv) ≫
        (wordObj D Sc w ⊗ (pres D Sc).obj (ob D [j])) ◁ inductionStrandDot D Sc i)
  simp only [Category.assoc]
  rw [← Category.assoc ((wordObj D Sc w ◁ inductionStrandDot D Sc i) ▷ _),
    MonoidalSupercategory.associator_naturality_middle k, associator_inv_whiskerLeft_tensor,
    Category.assoc]
  simp only [whiskerLeft_comp_comp]
  exact associator_conj_smul D Sc _ _ _ (inductionStrand_slide_left_ne D Sc hij)

/-- **The right dot slide on the last pair of an appended word, distinct colours.** -/
theorem induction_slide_right_ne (hij : i ≠ j) {n : ℕ} (w : Word I n) :
    inductionLastCrossing D Sc i j w ≫ appendHom D Sc i _ _ (inductionLastDot D Sc j w) =
      zsign k (D.parity i * D.parity j) •
        (inductionLastDot D Sc j (appendWord i w) ≫ inductionLastCrossing D Sc i j w) := by
  change ((α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D [j]))).hom ≫
      wordObj D Sc w ◁ strandCrossingTensor D Sc i j ≫
      (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [j])) ((pres D Sc).obj (ob D [i]))).inv) ≫
      (wordObj D Sc w ◁ inductionStrandDot D Sc j) ▷ (pres D Sc).obj (ob D [i]) =
    zsign k (D.parity i * D.parity j) •
      ((wordObj D Sc w ⊗ (pres D Sc).obj (ob D [i])) ◁ inductionStrandDot D Sc j ≫
        (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D [j]))).hom ≫
        wordObj D Sc w ◁ strandCrossingTensor D Sc i j ≫
        (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [j])) ((pres D Sc).obj (ob D [i]))).inv)
  simp only [Category.assoc]
  rw [associator_inv_whiskerRight_tensor, ← Category.assoc ((wordObj D Sc w ⊗ _) ◁ _),
    MonoidalSupercategory.associator_naturality_right k, Category.assoc]
  simp only [whiskerLeft_comp_comp]
  exact associator_conj_smul D Sc _ _ _ (inductionStrand_slide_right_ne D Sc hij)

end Word

section Affine
variable [Fintype I] {i j : I}

private theorem affineLastDot_mul_single (c : I) {m : ℕ} (t : Word I m)
    (s : Word I (m + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc (appendWord c t)) :
    affineLastDot D Sc c m * FiniteHomMatrix.single (appendWord c t) s f =
      FiniteHomMatrix.single (appendWord c t) s (f ≫ inductionLastDot D Sc c t) := by
  rw [affineLastDot, Finset.sum_mul, Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective c m h)) _ _
  · simp

private theorem single_mul_affineLastDot (c : I) {m : ℕ} (s : Word I m)
    (r : Word I (m + 1))
    (f : wordObj D Sc (appendWord c s) ⟶ wordObj D Sc r) :
    FiniteHomMatrix.single r (appendWord c s) f * affineLastDot D Sc c m =
      FiniteHomMatrix.single r (appendWord c s) (inductionLastDot D Sc c s ≫ f) := by
  rw [affineLastDot, Finset.mul_sum, Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective c m h.symm)) _ _
  · simp

private theorem affineLastCrossing_mul_single {n : ℕ} (t : Word I n)
    (s : Word I (n + 1 + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc (appendWord j (appendWord i t))) :
    affineLastCrossing D Sc i j n *
      FiniteHomMatrix.single (appendWord j (appendWord i t)) s f =
    FiniteHomMatrix.single (appendWord i (appendWord j t)) s
      (f ≫ inductionLastCrossing D Sc i j t) := by
  rw [affineLastCrossing, Finset.sum_mul, Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective i n (appendWord_injective j (n + 1) h))) _ _
  · simp

private theorem single_mul_affineLastCrossing {n : ℕ} (s : Word I n)
    (r : Word I (n + 1 + 1))
    (f : wordObj D Sc (appendWord i (appendWord j s)) ⟶ wordObj D Sc r) :
    FiniteHomMatrix.single r (appendWord i (appendWord j s)) f * affineLastCrossing D Sc i j n =
    FiniteHomMatrix.single r (appendWord j (appendWord i s))
      (inductionLastCrossing D Sc i j s ≫ f) := by
  rw [affineLastCrossing, Finset.mul_sum, Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective j n (appendWord_injective i (n + 1) h.symm))) _ _
  · simp

private theorem append_affineLastDot_eq_sum' (c d : I) (n : ℕ) :
    appendAlgebra D Sc d (n + 1) (affineLastDot D Sc c n) =
      ∑ w : Word I n, FiniteHomMatrix.single (appendWord d (appendWord c w))
        (appendWord d (appendWord c w)) (appendHom D Sc d _ _ (inductionLastDot D Sc c w)) := by
  change appendLinear D Sc d (n + 1) (affineLastDot D Sc c n) = _
  rw [affineLastDot, map_sum]
  exact Finset.sum_congr rfl fun w _ => appendLinear_single D Sc d _ _ _

/-- **The left slide in the affine algebra, distinct colours**: `c φⱼ(y_i) = ε y_i c`. -/
theorem affineLastCrossing_slide_left_ne (hij : i ≠ j) (n : ℕ) :
    affineLastCrossing D Sc i j n * appendAlgebra D Sc j (n + 1) (affineLastDot D Sc i n) =
      zsign k (D.parity i * D.parity j) •
        (affineLastDot D Sc i (n + 1) * affineLastCrossing D Sc i j n) := by
  rw [append_affineLastDot_eq_sum', Finset.mul_sum]
  simp only [affineLastCrossing_mul_single]
  conv_rhs => rw [affineLastCrossing, Finset.mul_sum]
  simp only [affineLastDot_mul_single, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [induction_slide_left_ne D Sc hij]
  simp only [FiniteHomMatrix.single, DFinsupp.single_smul]

/-- **The right slide in the affine algebra, distinct colours**: `φᵢ(y_j) c = ε c y_j`. -/
theorem affineLastCrossing_slide_right_ne (hij : i ≠ j) (n : ℕ) :
    appendAlgebra D Sc i (n + 1) (affineLastDot D Sc j n) * affineLastCrossing D Sc i j n =
      zsign k (D.parity i * D.parity j) •
        (affineLastCrossing D Sc i j n * affineLastDot D Sc j (n + 1)) := by
  rw [append_affineLastDot_eq_sum', Finset.sum_mul]
  simp only [single_mul_affineLastCrossing]
  conv_rhs => rw [affineLastCrossing, Finset.sum_mul]
  simp only [single_mul_affineLastDot, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [induction_slide_right_ne D Sc hij]
  simp only [FiniteHomMatrix.single, DFinsupp.single_smul]

end Affine

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke.CyclotomicAction
open SKM (zsign)
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I] (a : I → _root_.Polynomial k) {i j : I}

/-- **The left dot slide at every height, distinct colours**: `c φⱼ(y_i) = ε y_i c` in
`heightAlgebra (n+2)`, with `c` the last-pair crossing. -/
theorem heightLastCrossing_slide_left_ne (hij : i ≠ j) (n : ℕ) :
    heightLastCrossing D Sc a i j n * heightAppend D Sc a j (n + 1) (heightLastDot D Sc a i n) =
      zsign k (D.parity i * D.parity j) •
        (heightLastDot D Sc a i (n + 1) * heightLastCrossing D Sc a i j n) := by
  cases n with
  | zero =>
    change cyclotomicMk D Sc a 1 (affineLastCrossing D Sc i j 0) *
        cyclotomicMk D Sc a 1 (appendAlgebra D Sc j 1 (affineLastDot D Sc i 0)) =
      zsign k (D.parity i * D.parity j) •
        (cyclotomicMk D Sc a 1 (affineLastDot D Sc i 1) *
          cyclotomicMk D Sc a 1 (affineLastCrossing D Sc i j 0))
    rw [← map_mul, ← map_mul, ← map_smul, affineLastCrossing_slide_left_ne D Sc hij]
  | succ n =>
    change cyclotomicMk D Sc a (n + 1 + 1) (affineLastCrossing D Sc i j (n + 1)) *
        cyclotomicMk D Sc a (n + 1 + 1)
          (appendAlgebra D Sc j (n + 1 + 1) (affineLastDot D Sc i (n + 1))) =
      zsign k (D.parity i * D.parity j) •
        (cyclotomicMk D Sc a (n + 1 + 1) (affineLastDot D Sc i (n + 1 + 1)) *
          cyclotomicMk D Sc a (n + 1 + 1) (affineLastCrossing D Sc i j (n + 1)))
    rw [← map_mul, ← map_mul, ← map_smul, affineLastCrossing_slide_left_ne D Sc hij]

/-- **The right dot slide at every height, distinct colours**: `φᵢ(y_j) c = ε c y_j`. -/
theorem heightLastCrossing_slide_right_ne (hij : i ≠ j) (n : ℕ) :
    heightAppend D Sc a i (n + 1) (heightLastDot D Sc a j n) * heightLastCrossing D Sc a i j n =
      zsign k (D.parity i * D.parity j) •
        (heightLastCrossing D Sc a i j n * heightLastDot D Sc a j (n + 1)) := by
  cases n with
  | zero =>
    change cyclotomicMk D Sc a 1 (appendAlgebra D Sc i 1 (affineLastDot D Sc j 0)) *
        cyclotomicMk D Sc a 1 (affineLastCrossing D Sc i j 0) =
      zsign k (D.parity i * D.parity j) •
        (cyclotomicMk D Sc a 1 (affineLastCrossing D Sc i j 0) *
          cyclotomicMk D Sc a 1 (affineLastDot D Sc j 1))
    rw [← map_mul, ← map_mul, ← map_smul, affineLastCrossing_slide_right_ne D Sc hij]
  | succ n =>
    change cyclotomicMk D Sc a (n + 1 + 1)
          (appendAlgebra D Sc i (n + 1 + 1) (affineLastDot D Sc j (n + 1))) *
        cyclotomicMk D Sc a (n + 1 + 1) (affineLastCrossing D Sc i j (n + 1)) =
      zsign k (D.parity i * D.parity j) •
        (cyclotomicMk D Sc a (n + 1 + 1) (affineLastCrossing D Sc i j (n + 1)) *
          cyclotomicMk D Sc a (n + 1 + 1) (affineLastDot D Sc j (n + 1 + 1)))
    rw [← map_mul, ← map_mul, ← map_smul, affineLastCrossing_slide_right_ne D Sc hij]

end OddMath.QuiverHecke.CyclotomicAction
