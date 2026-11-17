import OddMath.QuiverHecke.CyclotomicAction.LastStrand
import OddMath.SKM.Calculus
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient

/-!
# Global height

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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

theorem associator_inv_whiskerRight_tensor (W Y : H D Sc) {Z Z' : H D Sc} (f : Z ⟶ Z') :
    (α_ W Z Y).inv ≫ (W ◁ f) ▷ Y = W ◁ (f ▷ Y) ≫ (α_ W Z' Y).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← MonoidalSupercategory.associator_naturality_middle k,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

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

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

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

variable {i j}

end Local

section Word
variable {i j : I}

end Word

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke.CyclotomicAction
open SKM (zsign)
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I] (a : I → _root_.Polynomial k) {i j : I}

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# The distinct-colour quadratic relation on two inductions from every height

The algebra half of the quadratic relations (1.7) of Brundan–Ellis, arXiv:1701.04133v2,
Definition 1.5, for distinct colours, at every height of the extended tower. On the words
`w j i`, the square of the last-pair crossing is the explicit two-colour polynomial
`Q_{ji}` (`affineLastCrossing_mixed`). Writing `A = φᵢ(y_j)` for the appended dot,
`B = y_i` for the new last dot and `e = φᵢφⱼ(1)` for the two-colour idempotent,

  `c_{ij} c_{ji} = e · Q_{ji}(A, B)`

in the affine algebra (`affineLastCrossing_mul_mixed`) and at every height
(`heightLastCrossing_mul_mixed`), where `Q_{ji}(A, B) = t_{ji} 1` if `d_{ji} = 0` and otherwise

  `Q_{ji}(A, B) = ∑_{0<p<d_{ji}, 0<q<d_{ij}} s_{ji}^{pq} A^p B^q + t_{ji} A^{d_{ji}} + t_{ij} B^{d_{ij}}`.

This is an identity of algebra elements; no parameter change is made here.
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- The explicit two-colour quadratic polynomial in two elements of a `k`-algebra. -/
def pairQuadPoly {R : Type*} [Ring R] [Algebra k R] (i j : I) (A B : R) : R :=
  if D.d i j = 0 then (Sc.t i j : k) • 1 else
    ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
      Sc.s i j p q • (A ^ p * B ^ q) +
      ((Sc.t i j : k) • A ^ D.dn i j + (Sc.t j i : k) • B ^ D.dn j i)

variable [Fintype I]

section PairDiag
variable (i j : I) (n : ℕ)

variable {i j n}

variable (i j n)

private abbrev pairB (w : Word I n) : End (wordObj D Sc (appendWord i (appendWord j w))) :=
  dotE D Sc (appendWord i (appendWord j w)).1 (w.1.length + 1)

variable {i j}

end PairDiag

section Height
open CyclotomicAction
variable (a : I → _root_.Polynomial k) {i j : I}

end Height

end OddMath.QuiverHecke
end

end

section

/-!
# The equal-colour braid on three inductions at every height

The module half of the same-colour braid relation of
`Categorification/KLR/CyclotomicAction/GlobalBraid.lean` (`globalCross_sameBraid`), at a fixed
height of the extended tower. With `t₁` the crossing of the two inner inductions under the
outer induction and `t₂` the crossing of the two outer inductions,

  `t₂ ≫ t₁ ≫ t₂ = t₁ ≫ t₂ ≫ t₁`

on every module (`heightSuperInduction_braid_same`).

Every element of a balanced tensor `P ⊗ N` with `P` an induction corner is the action of
an algebra element on `e ⊗ N`, with `e` the colour-cut idempotent
(`heightInductionCorner_btmul_eq_lact`), and the idempotent can be moved past the action
of the lower algebra (`heightInductionCorner_btmul_lact`). On `e ⊗ e ⊗ N` the crossing acts
by left multiplication by the last-pair crossing (`heightSuperInductionCrossing_idempotent`);
the braid then follows from `heightLastCrossing_braid_same`, the signs on the two sides
agreeing term by term.
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

section Corner
variable (n : ℕ)


end Corner

section Crossing
variable (n : ℕ)


end Crossing

section Braid
variable (n : ℕ)


end Braid

end OddMath.QuiverHecke.CyclotomicAction
end

end
