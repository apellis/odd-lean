/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightCrossing
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightDot
import OddMath.QuiverHecke.Centre

/-!
# The dot–crossing relations of the last pair of strands

The algebra half of the slide relations of `Categorification/KLR/CyclotomicAction/GlobalSlides.lean`.
For equal colours the defining relations (1.8) of the quiver Hecke supercategory
(Brundan–Ellis, arXiv:1701.04133v2) read, with `s = (-1)^{|i|}`,

  `x₁ τ - s τ x₂ = 1`,  `τ x₁ - s x₂ τ = 1`

(diagrams read bottom to top, `x₁` the dot on the left strand). Whiskering by an old word
(`induction_slide_left`, `induction_slide_right`) and summing over words gives the
corresponding identities between `affineLastCrossing`, the appended last dot and the new last
dot, with the image of one on the right (`affineLastCrossing_slide_left`,
`affineLastCrossing_slide_right`). Since matrix multiplication reverses diagram composition,
in the algebra the relations read `c y₁ - s y₂ c = θ(1)` and `y₁ c - s c y₂ = θ(1)`. They
descend to every height of the extended tower (`heightLastCrossing_slide_left`,
`heightLastCrossing_slide_right`).
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
namespace OddMath.QuiverHecke
open SKM (zsign)
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

section Local

theorem zsmul_koszulSign_eq_zsign_smul {A : Type*} [AddCommGroup A] [Module k A] (p q : ZMod 2)
    (f : A) : Supercategory.koszulSign p q • f = zsign k (p * q) • f := by
  rcases Supercategory.parity_eq_zero_or_one p with rfl | rfl <;>
    rcases Supercategory.parity_eq_zero_or_one q with rfl | rfl <;>
    simp [Supercategory.koszulSign, zsign]

theorem inductionStrandDot_whiskerRight_comp_crossing (i : I) :
    inductionStrandDot D Sc i ▷ (pres D Sc).obj (ob D [i]) ≫ inductionStrandCrossing D Sc i i =
      cl D Sc [i, i] [i, i] [.dot 0, .cross 0] (by simp [pl, PG.ld, PG.act, Shape.dom, Shape.cod]) := by
  rw [inductionStrandDot, inductionStrandCrossing, Presentation.diag_whiskerRight, cl]
  exact (Presentation.diag_comp _ _ _).symm.trans (Presentation.diag_eq_of_layers_eq _ rfl)

theorem inductionStrandCrossing_comp_whiskerLeft_dot (i : I) :
    inductionStrandCrossing D Sc i i ≫ (pres D Sc).obj (ob D [i]) ◁ inductionStrandDot D Sc i =
      cl D Sc [i, i] [i, i] [.cross 0, .dot 1] (by simp [pl, PG.ld, PG.act, Shape.dom, Shape.cod]) := by
  rw [inductionStrandDot, inductionStrandCrossing, Presentation.diag_whiskerLeft, cl]
  exact (Presentation.diag_comp _ _ _).symm.trans (Presentation.diag_eq_of_layers_eq _ rfl)

theorem inductionStrandCrossing_comp_dot_whiskerRight (i : I) :
    inductionStrandCrossing D Sc i i ≫ inductionStrandDot D Sc i ▷ (pres D Sc).obj (ob D [i]) =
      cl D Sc [i, i] [i, i] [.cross 0, .dot 0] (by simp [pl, PG.ld, PG.act, Shape.dom, Shape.cod]) := by
  rw [inductionStrandDot, inductionStrandCrossing, Presentation.diag_whiskerRight, cl]
  exact (Presentation.diag_comp _ _ _).symm.trans (Presentation.diag_eq_of_layers_eq _ rfl)

theorem whiskerLeft_dot_comp_inductionStrandCrossing (i : I) :
    (pres D Sc).obj (ob D [i]) ◁ inductionStrandDot D Sc i ≫ inductionStrandCrossing D Sc i i =
      cl D Sc [i, i] [i, i] [.dot 1, .cross 0] (by simp [pl, PG.ld, PG.act, Shape.dom, Shape.cod]) := by
  rw [inductionStrandDot, inductionStrandCrossing, Presentation.diag_whiskerLeft, cl]
  exact (Presentation.diag_comp _ _ _).symm.trans (Presentation.diag_eq_of_layers_eq _ rfl)

/-- **The left dot slide on two strands of equal colour**, `x₁ τ - s τ x₂ = 1`. -/
theorem inductionStrand_slide_left (i : I) :
    (inductionStrandDot D Sc i ▷ (pres D Sc).obj (ob D [i]) ≫ inductionStrandCrossing D Sc i i :
        (pres D Sc).obj (ob D [i, i]) ⟶ (pres D Sc).obj (ob D [i, i])) -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        (inductionStrandCrossing D Sc i i ≫
          (pres D Sc).obj (ob D [i]) ◁ inductionStrandDot D Sc i :
          (pres D Sc).obj (ob D [i, i]) ⟶ (pres D Sc).obj (ob D [i, i])) = 𝟙 _ := by
  erw [inductionStrandDot_whiskerRight_comp_crossing, inductionStrandCrossing_comp_whiskerLeft_dot]
  rw [zsmul_koszulSign_eq_zsign_smul (k := k), ]
  refine sub_eq_of_eq_add' ?_
  have hs := slide_left_eq D Sc [] [] i (by simp [pl, PG.ld, PG.act, Shape.dom, Shape.cod])
    (by simp [pl, PG.ld, PG.act, Shape.dom, Shape.cod])
  exact hs.trans (congrArg (_ + ·) (cl_nil D Sc _ _))

/-- **The right dot slide on two strands of equal colour**, `τ x₁ - s x₂ τ = 1`. -/
theorem inductionStrand_slide_right (i : I) :
    (inductionStrandCrossing D Sc i i ≫ inductionStrandDot D Sc i ▷ (pres D Sc).obj (ob D [i]) :
        (pres D Sc).obj (ob D [i, i]) ⟶ (pres D Sc).obj (ob D [i, i])) -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        ((pres D Sc).obj (ob D [i]) ◁ inductionStrandDot D Sc i ≫
          inductionStrandCrossing D Sc i i :
          (pres D Sc).obj (ob D [i, i]) ⟶ (pres D Sc).obj (ob D [i, i])) = 𝟙 _ := by
  erw [inductionStrandCrossing_comp_dot_whiskerRight, whiskerLeft_dot_comp_inductionStrandCrossing]
  rw [zsmul_koszulSign_eq_zsign_smul (k := k), ]
  refine sub_eq_of_eq_add' ?_
  have hs := slide_right_eq D Sc [] [] i (by simp [pl, PG.ld, PG.act, Shape.dom, Shape.cod])
    (by simp [pl, PG.ld, PG.act, Shape.dom, Shape.cod])
  exact hs.trans (congrArg (_ + ·) (cl_nil D Sc _ _))

end Local

section Word

/-- The two-strand crossing with its source and target written as tensor products. -/
def strandCrossingTensor (i j : I) :
    (pres D Sc).obj (ob D [i]) ⊗ (pres D Sc).obj (ob D [j]) ⟶
      (pres D Sc).obj (ob D [j]) ⊗ (pres D Sc).obj (ob D [i]) :=
  inductionStrandCrossing D Sc i j

theorem strandCrossingTensor_slide_left (i : I) :
    inductionStrandDot D Sc i ▷ (pres D Sc).obj (ob D [i]) ≫ strandCrossingTensor D Sc i i -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        (strandCrossingTensor D Sc i i ≫ (pres D Sc).obj (ob D [i]) ◁ inductionStrandDot D Sc i) =
      𝟙 _ :=
  inductionStrand_slide_left D Sc i

theorem strandCrossingTensor_slide_right (i : I) :
    strandCrossingTensor D Sc i i ≫ inductionStrandDot D Sc i ▷ (pres D Sc).obj (ob D [i]) -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        ((pres D Sc).obj (ob D [i]) ◁ inductionStrandDot D Sc i ≫ strandCrossingTensor D Sc i i) =
      𝟙 _ :=
  inductionStrand_slide_right D Sc i

theorem whiskerLeft_sub_zsmul {Y Z : H D Sc} (W : H D Sc) (f g : Y ⟶ Z) (c : ℤ) :
    W ◁ (f - c • g) = W ◁ f - c • (W ◁ g) := by
  rw [sub_eq_add_neg, MonoidalSupercategory.whiskerLeft_add (R := k),
    MonoidalSupercategory.whiskerLeft_neg (R := k), MonoidalSupercategory.whiskerLeft_zsmul (R := k),
    ← sub_eq_add_neg]

theorem whiskerLeft_comp_comp (W : H D Sc) {Y₁ Y₂ Y₃ Z : H D Sc} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃)
    (h : W ⊗ Y₃ ⟶ Z) : W ◁ f ≫ W ◁ g ≫ h = W ◁ (f ≫ g) ≫ h := by
  rw [← Category.assoc, ← MonoidalSupercategory.whiskerLeft_comp (R := k)]

/-- Conjugating a two-strand identity by the associators. -/
theorem associator_conj_sub {W : H D Sc} {Y₁ Y₂ : H D Sc} (f g : Y₁ ⊗ Y₂ ⟶ Y₁ ⊗ Y₂) (c : ℤ)
    (h : f - c • g = 𝟙 _) :
    (α_ W Y₁ Y₂).hom ≫ W ◁ f ≫ (α_ W Y₁ Y₂).inv -
      c • ((α_ W Y₁ Y₂).hom ≫ W ◁ g ≫ (α_ W Y₁ Y₂).inv) = 𝟙 _ := by
  rw [← Preadditive.comp_zsmul, ← Preadditive.zsmul_comp, ← Preadditive.comp_sub,
    ← Preadditive.sub_comp, ← whiskerLeft_sub_zsmul, h,
    MonoidalSupercategory.whiskerLeft_id (R := k), Category.id_comp, Iso.hom_inv_id]

theorem associator_inv_whiskerLeft_tensor (W Y : H D Sc) {Z Z' : H D Sc} (f : Z ⟶ Z') :
    (α_ W Y Z).inv ≫ (W ⊗ Y) ◁ f = W ◁ (Y ◁ f) ≫ (α_ W Y Z').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← MonoidalSupercategory.associator_naturality_right k,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem associator_inv_whiskerRight_tensor (W Y : H D Sc) {Z Z' : H D Sc} (f : Z ⟶ Z') :
    (α_ W Z Y).inv ≫ (W ◁ f) ▷ Y = W ◁ (f ▷ Y) ≫ (α_ W Z' Y).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← MonoidalSupercategory.associator_naturality_middle k,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The left dot slide on the last pair of an appended word.** -/
theorem induction_slide_left (i : I) {n : ℕ} (w : Word I n) :
    appendHom D Sc i _ _ (inductionLastDot D Sc i w) ≫ inductionLastCrossing D Sc i i w -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        (inductionLastCrossing D Sc i i w ≫ inductionLastDot D Sc i (appendWord i w)) = 𝟙 _ := by
  change (wordObj D Sc w ◁ inductionStrandDot D Sc i) ▷ (pres D Sc).obj (ob D [i]) ≫
      (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D [i]))).hom ≫
      wordObj D Sc w ◁ strandCrossingTensor D Sc i i ≫
      (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D [i]))).inv -
    Supercategory.koszulSign (D.parity i) (D.parity i) •
      (((α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D [i]))).hom ≫
        wordObj D Sc w ◁ strandCrossingTensor D Sc i i ≫
        (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D [i]))).inv) ≫
        (wordObj D Sc w ⊗ (pres D Sc).obj (ob D [i])) ◁ inductionStrandDot D Sc i) = 𝟙 _
  simp only [Category.assoc]
  rw [← Category.assoc ((wordObj D Sc w ◁ inductionStrandDot D Sc i) ▷ _),
    MonoidalSupercategory.associator_naturality_middle k, associator_inv_whiskerLeft_tensor,
    Category.assoc]
  simp only [whiskerLeft_comp_comp]
  exact associator_conj_sub D Sc _ _ _ (strandCrossingTensor_slide_left D Sc i)

/-- **The right dot slide on the last pair of an appended word.** -/
theorem induction_slide_right (i : I) {n : ℕ} (w : Word I n) :
    inductionLastCrossing D Sc i i w ≫ appendHom D Sc i _ _ (inductionLastDot D Sc i w) -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        (inductionLastDot D Sc i (appendWord i w) ≫ inductionLastCrossing D Sc i i w) = 𝟙 _ := by
  change ((α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D [i]))).hom ≫
      wordObj D Sc w ◁ strandCrossingTensor D Sc i i ≫
      (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D [i]))).inv) ≫
      (wordObj D Sc w ◁ inductionStrandDot D Sc i) ▷ (pres D Sc).obj (ob D [i]) -
    Supercategory.koszulSign (D.parity i) (D.parity i) •
      ((wordObj D Sc w ⊗ (pres D Sc).obj (ob D [i])) ◁ inductionStrandDot D Sc i ≫
        (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D [i]))).hom ≫
        wordObj D Sc w ◁ strandCrossingTensor D Sc i i ≫
        (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D [i]))).inv) = 𝟙 _
  simp only [Category.assoc]
  rw [associator_inv_whiskerRight_tensor, ← Category.assoc ((wordObj D Sc w ⊗ _) ◁ _),
    MonoidalSupercategory.associator_naturality_right k, Category.assoc]
  simp only [whiskerLeft_comp_comp]
  exact associator_conj_sub D Sc _ _ _ (strandCrossingTensor_slide_right D Sc i)

end Word

section Affine
variable [Fintype I]

omit [Fintype I] in
private theorem single_sub_zsmul {n : ℕ} (s t : Word I n) (f g : wordObj D Sc s ⟶ wordObj D Sc t)
    (c : ℤ) :
    (FiniteHomMatrix.single t s f : Hn D Sc n) - c • FiniteHomMatrix.single t s g =
      FiniteHomMatrix.single t s (f - c • g) := by
  simp only [FiniteHomMatrix.single, DFinsupp.single_sub, DFinsupp.single_smul]

private theorem lastDot_mul_entry' (i : I) {n : ℕ} (s t : Word I n)
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

private theorem entry_mul_lastDot' (i : I) {n : ℕ} (s t : Word I n)
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

private theorem crossing_mul_entry' (i : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc (appendWord i (appendWord i s)) ⟶
      wordObj D Sc (appendWord i (appendWord i t))) :
    affineLastCrossing D Sc i i n *
      FiniteHomMatrix.single (appendWord i (appendWord i t)) (appendWord i (appendWord i s)) f =
    FiniteHomMatrix.single (appendWord i (appendWord i t)) (appendWord i (appendWord i s))
      (f ≫ inductionLastCrossing D Sc i i t) := by
  rw [affineLastCrossing, Finset.sum_mul, Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective i n (appendWord_injective i (n + 1) h))) _ _
  · simp

private theorem entry_mul_crossing' (i : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc (appendWord i (appendWord i s)) ⟶
      wordObj D Sc (appendWord i (appendWord i t))) :
    FiniteHomMatrix.single (appendWord i (appendWord i t)) (appendWord i (appendWord i s)) f *
      affineLastCrossing D Sc i i n =
    FiniteHomMatrix.single (appendWord i (appendWord i t)) (appendWord i (appendWord i s))
      (inductionLastCrossing D Sc i i s ≫ f) := by
  rw [affineLastCrossing, Finset.mul_sum, Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective i n (appendWord_injective i (n + 1) h.symm))) _ _
  · simp

private theorem append_affineLastDot_eq_sum (i : I) (n : ℕ) :
    appendAlgebra D Sc i (n + 1) (affineLastDot D Sc i n) =
      ∑ w : Word I n, FiniteHomMatrix.single (appendWord i (appendWord i w))
        (appendWord i (appendWord i w)) (appendHom D Sc i _ _ (inductionLastDot D Sc i w)) := by
  change appendLinear D Sc i (n + 1) (affineLastDot D Sc i n) = _
  rw [affineLastDot, map_sum]
  exact Finset.sum_congr rfl fun w _ => appendLinear_single D Sc i _ _ _

private theorem append_append_one_eq_sum (i : I) (n : ℕ) :
    appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n 1) =
      ∑ w : Word I n, FiniteHomMatrix.single (appendWord i (appendWord i w))
        (appendWord i (appendWord i w)) (𝟙 _) := by
  change appendLinear D Sc i (n + 1)
    (appendLinear D Sc i n (FiniteHomMatrix.localUnit Finset.univ)) = _
  rw [FiniteHomMatrix.localUnit, map_sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  change appendLinear D Sc i (n + 1)
    (appendLinear D Sc i n (FiniteHomMatrix.single w w (𝟙 _))) = _
  rw [appendLinear_single, appendLinear_single]
  change FiniteHomMatrix.single _ _ (appendEnd D Sc i _ (appendEnd D Sc i w 1)) = _
  rw [map_one, map_one]
  rfl

private theorem affineLastCrossing_eq_sum (i : I) (n : ℕ) :
    affineLastCrossing D Sc i i n =
      ∑ w : Word I n, FiniteHomMatrix.single (appendWord i (appendWord i w))
        (appendWord i (appendWord i w)) (inductionLastCrossing D Sc i i w) := rfl

/-- **The left slide in the affine algebra**: `c y₁ - s y₂ c = θ(1)`. -/
theorem affineLastCrossing_slide_left (i : I) (n : ℕ) :
    affineLastCrossing D Sc i i n * appendAlgebra D Sc i (n + 1) (affineLastDot D Sc i n) -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        (affineLastDot D Sc i (n + 1) * affineLastCrossing D Sc i i n) =
      appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n 1) := by
  rw [append_affineLastDot_eq_sum, append_append_one_eq_sum, Finset.mul_sum]
  simp only [crossing_mul_entry']
  rw [affineLastCrossing_eq_sum, Finset.mul_sum]
  simp only [lastDot_mul_entry']
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [single_sub_zsmul, induction_slide_left]

/-- **The right slide in the affine algebra**: `y₁ c - s c y₂ = θ(1)`. -/
theorem affineLastCrossing_slide_right (i : I) (n : ℕ) :
    appendAlgebra D Sc i (n + 1) (affineLastDot D Sc i n) * affineLastCrossing D Sc i i n -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        (affineLastCrossing D Sc i i n * affineLastDot D Sc i (n + 1)) =
      appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n 1) := by
  rw [append_affineLastDot_eq_sum, append_append_one_eq_sum, Finset.sum_mul]
  simp only [entry_mul_crossing']
  rw [affineLastCrossing_eq_sum, Finset.sum_mul]
  simp only [entry_mul_lastDot']
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [single_sub_zsmul, induction_slide_right]

end Affine

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke.CyclotomicAction
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I] (a : I → _root_.Polynomial k) (i : I)

/-- **The left dot slide at every height**: `c y₁ - s y₂ c = θ(1)` in `heightAlgebra (n+2)`,
where `y₁` is the appended last dot and `y₂` the new last dot. -/
theorem heightLastCrossing_slide_left (n : ℕ) :
    heightLastCrossing D Sc a i i n * heightAppend D Sc a i (n + 1) (heightLastDot D Sc a i n) -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        (heightLastDot D Sc a i (n + 1) * heightLastCrossing D Sc a i i n) =
      heightAppend D Sc a i (n + 1) (heightAppend D Sc a i n 1) := by
  cases n with
  | zero =>
    change cyclotomicMk D Sc a 1 (affineLastCrossing D Sc i i 0) *
        cyclotomicMk D Sc a 1 (appendAlgebra D Sc i 1 (affineLastDot D Sc i 0)) -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        (cyclotomicMk D Sc a 1 (affineLastDot D Sc i 1) *
          cyclotomicMk D Sc a 1 (affineLastCrossing D Sc i i 0)) =
      cyclotomicMk D Sc a 1 (appendAlgebra D Sc i 1 (appendAlgebra D Sc i 0 1))
    rw [← map_mul, ← map_mul, ← map_zsmul, ← map_sub, affineLastCrossing_slide_left]
  | succ n =>
    have h1 : heightAppend D Sc a i (n + 1 + 1) (heightAppend D Sc a i (n + 1) 1) =
        cyclotomicMk D Sc a (n + 1 + 1)
          (appendAlgebra D Sc i (n + 1 + 1) (appendAlgebra D Sc i (n + 1) 1)) := by
      change cyclotomicAppend D Sc i a (n + 1) (cyclotomicAppend D Sc i a n 1) = _
      rw [← map_one (cyclotomicMk D Sc a n)]
      rfl
    rw [h1]
    change cyclotomicMk D Sc a (n + 1 + 1) (affineLastCrossing D Sc i i (n + 1)) *
        cyclotomicMk D Sc a (n + 1 + 1)
          (appendAlgebra D Sc i (n + 1 + 1) (affineLastDot D Sc i (n + 1))) -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        (cyclotomicMk D Sc a (n + 1 + 1) (affineLastDot D Sc i (n + 1 + 1)) *
          cyclotomicMk D Sc a (n + 1 + 1) (affineLastCrossing D Sc i i (n + 1))) = _
    rw [← map_mul, ← map_mul, ← map_zsmul, ← map_sub, affineLastCrossing_slide_left]

/-- **The right dot slide at every height**: `y₁ c - s c y₂ = θ(1)`. -/
theorem heightLastCrossing_slide_right (n : ℕ) :
    heightAppend D Sc a i (n + 1) (heightLastDot D Sc a i n) * heightLastCrossing D Sc a i i n -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        (heightLastCrossing D Sc a i i n * heightLastDot D Sc a i (n + 1)) =
      heightAppend D Sc a i (n + 1) (heightAppend D Sc a i n 1) := by
  cases n with
  | zero =>
    change cyclotomicMk D Sc a 1 (appendAlgebra D Sc i 1 (affineLastDot D Sc i 0)) *
        cyclotomicMk D Sc a 1 (affineLastCrossing D Sc i i 0) -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        (cyclotomicMk D Sc a 1 (affineLastCrossing D Sc i i 0) *
          cyclotomicMk D Sc a 1 (affineLastDot D Sc i 1)) =
      cyclotomicMk D Sc a 1 (appendAlgebra D Sc i 1 (appendAlgebra D Sc i 0 1))
    rw [← map_mul, ← map_mul, ← map_zsmul, ← map_sub, affineLastCrossing_slide_right]
  | succ n =>
    have h1 : heightAppend D Sc a i (n + 1 + 1) (heightAppend D Sc a i (n + 1) 1) =
        cyclotomicMk D Sc a (n + 1 + 1)
          (appendAlgebra D Sc i (n + 1 + 1) (appendAlgebra D Sc i (n + 1) 1)) := by
      change cyclotomicAppend D Sc i a (n + 1) (cyclotomicAppend D Sc i a n 1) = _
      rw [← map_one (cyclotomicMk D Sc a n)]
      rfl
    rw [h1]
    change cyclotomicMk D Sc a (n + 1 + 1)
          (appendAlgebra D Sc i (n + 1 + 1) (affineLastDot D Sc i (n + 1))) *
        cyclotomicMk D Sc a (n + 1 + 1) (affineLastCrossing D Sc i i (n + 1)) -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        (cyclotomicMk D Sc a (n + 1 + 1) (affineLastCrossing D Sc i i (n + 1)) *
          cyclotomicMk D Sc a (n + 1 + 1) (affineLastDot D Sc i (n + 1 + 1))) = _
    rw [← map_mul, ← map_mul, ← map_zsmul, ← map_sub, affineLastCrossing_slide_right]

end OddMath.QuiverHecke.CyclotomicAction
