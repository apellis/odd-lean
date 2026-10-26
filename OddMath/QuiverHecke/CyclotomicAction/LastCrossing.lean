/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.LastDot
import StringDiagrams.Super.MonoidalEnvelope

/-!
# The global crossing of the last two strands

Ports the crossing-intertwiner input of
`Categorification/KLR/CyclotomicAction/Induction.lean`,
`Categorification/KLR/CyclotomicAction/Slides.lean` and
`Categorification/KLR/CyclotomicAction/Comparison.lean`.
The generator `.cross i j` has source `[i,j]` and target `[j,i]`.
Thus `lastCrossing i j` has source `old ++ [i] ++ [j]` and target
`old ++ [j] ++ [i]`. Matrix rows are targets and columns are sources;
multiplication reverses diagram composition. Writing `θᵢⱼ = φᵢ ∘ φⱼ`,
the global element lies in `θᵢⱼ(1) C θⱼᵢ(1)` and satisfies
`θᵢⱼ(r) τ = (-1)^{|r||i||j|} τ θⱼᵢ(r)`.
Right multiplication therefore goes from `C θᵢⱼ(1)` to `C θⱼᵢ(1)`.
No invertibility, quadratic or braid relation is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- The literal two-strand crossing, from `[i,j]` to `[j,i]`. -/
def inductionStrandCrossing (i j : I) :
    (pres D Sc).obj (ob D [i,j]) ⟶ (pres D Sc).obj (ob D [j,i]) :=
  (pres D Sc).diag (mkD D [([], .cross i j, [])] ⟨rfl, rfl⟩)

theorem inductionStrandCrossing_parity (i j : I) :
    inductionStrandCrossing D Sc i j ∈ Supercategory.parity (R := k) _ _
      (D.parity i * D.parity j) := by
  apply Presentation.diag_mem_homDeg'
  simp [degree_parity_mkD, Shape.parity]

/-- Whisker the crossing by the old word; associators expose the last pair. -/
def inductionLastCrossing (i j : I) {n : ℕ} (w : Word I n) :
    wordObj D Sc (appendWord j (appendWord i w)) ⟶
      wordObj D Sc (appendWord i (appendWord j w)) :=
  (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [i]))
    ((pres D Sc).obj (ob D [j]))).hom ≫
  (wordObj D Sc w ◁ inductionStrandCrossing D Sc i j) ≫
  (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [j]))
    ((pres D Sc).obj (ob D [i]))).inv

theorem inductionLastCrossing_parity (i j : I) {n : ℕ} (w : Word I n) :
    inductionLastCrossing D Sc i j w ∈ Supercategory.parity (R := k) _ _
      (D.parity i * D.parity j) := by
  change (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [i]))
      ((pres D Sc).obj (ob D [j]))).hom ≫
    (wordObj D Sc w ◁ inductionStrandCrossing D Sc i j) ≫
    (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [j]))
      ((pres D Sc).obj (ob D [i]))).inv ∈ Supercategory.parity (R := k)
      (((wordObj D Sc w) ⊗ ((pres D Sc).obj (ob D [i]))) ⊗ ((pres D Sc).obj (ob D [j])))
      (((wordObj D Sc w) ⊗ ((pres D Sc).obj (ob D [j]))) ⊗ ((pres D Sc).obj (ob D [i]))) _
  simpa only [zero_add, add_zero] using Supercategory.comp_mem
    (MonoidalSupercategory.associator_hom_mem (R := k) (wordObj D Sc w)
      ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D [j])))
    (Supercategory.comp_mem
      (MonoidalSupercategory.whiskerLeft_mem (wordObj D Sc w)
        (inductionStrandCrossing_parity D Sc i j))
      (Supercategory.inv_mem _ (MonoidalSupercategory.associator_hom_mem (R := k)
        (wordObj D Sc w) ((pres D Sc).obj (ob D [j])) ((pres D Sc).obj (ob D [i])))))

/-- The old homogeneous morphism passes the last pair with the Koszul sign. -/
theorem induction_crossing_slide (i j : I) {n : ℕ} (s t : Word I n) {p : ZMod 2}
    (f : wordObj D Sc s ⟶ wordObj D Sc t)
    (hf : f ∈ Supercategory.parity (R := k) _ _ p) :
    appendHom D Sc j _ _ (appendHom D Sc i s t f) ≫ inductionLastCrossing D Sc i j t =
      Supercategory.koszulSign p (D.parity i * D.parity j) •
        (inductionLastCrossing D Sc i j s ≫
          appendHom D Sc i _ _ (appendHom D Sc j s t f)) := by
  have hinv : f ▷ (((pres D Sc).obj (ob D [j])) ⊗ ((pres D Sc).obj (ob D [i]))) ≫
      (α_ (wordObj D Sc t) ((pres D Sc).obj (ob D [j])) ((pres D Sc).obj (ob D [i]))).inv =
      (α_ (wordObj D Sc s) ((pres D Sc).obj (ob D [j])) ((pres D Sc).obj (ob D [i]))).inv ≫
        (f ▷ ((pres D Sc).obj (ob D [j]))) ▷ ((pres D Sc).obj (ob D [i])) := by
    rw [Iso.comp_inv_eq, Category.assoc,
      MonoidalSupercategory.associator_naturality_left k, Iso.inv_hom_id_assoc]
  dsimp only [inductionLastCrossing, appendHom, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← Category.assoc, MonoidalSupercategory.associator_naturality_left k,
    Category.assoc, ← Category.assoc (f ▷ _)]
  erw [MonoidalSupercategory.super_interchange hf (inductionStrandCrossing_parity D Sc i j)]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
  erw [hinv]

variable [Fintype I]

/-- The finite off-diagonal sum of crossings of the last pair. -/
def affineLastCrossing (i j : I) (n : ℕ) : Hn D Sc (n + 1 + 1) :=
  ∑ w : Word I n, FiniteHomMatrix.single (appendWord i (appendWord j w))
    (appendWord j (appendWord i w)) (inductionLastCrossing D Sc i j w)

theorem affineLastCrossing_parity (i j : I) (n : ℕ) :
    affineLastCrossing D Sc i j n ∈ affineParity D Sc (n + 1 + 1)
      (D.parity i * D.parity j) := by
  apply Submodule.sum_mem
  intro w _
  exact FiniteHomMatrix.single_mem_component _ _ (inductionLastCrossing_parity D Sc i j w)

private theorem crossing_mul_entry (i j : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc (appendWord j (appendWord i s)) ⟶
      wordObj D Sc (appendWord j (appendWord i t))) :
    affineLastCrossing D Sc i j n *
      FiniteHomMatrix.single (appendWord j (appendWord i t)) (appendWord j (appendWord i s)) f =
    FiniteHomMatrix.single (appendWord i (appendWord j t)) (appendWord j (appendWord i s))
      (f ≫ inductionLastCrossing D Sc i j t) := by
  rw [affineLastCrossing, Finset.sum_mul, Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective i n (appendWord_injective j (n + 1) h))) _ _
  · simp

private theorem entry_mul_crossing (i j : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc (appendWord i (appendWord j s)) ⟶
      wordObj D Sc (appendWord i (appendWord j t))) :
    FiniteHomMatrix.single (appendWord i (appendWord j t)) (appendWord i (appendWord j s)) f *
      affineLastCrossing D Sc i j n =
    FiniteHomMatrix.single (appendWord i (appendWord j t)) (appendWord j (appendWord i s))
      (inductionLastCrossing D Sc i j s ≫ f) := by
  rw [affineLastCrossing, Finset.mul_sum, Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective j n (appendWord_injective i (n + 1) h.symm))) _ _
  · simp

/-- Signed intertwining of the two composite affine inclusions. -/
theorem affineLastCrossing_intertwines (i j : I) (n : ℕ) {p : ZMod 2} {r : Hn D Sc n}
    (hr : r ∈ affineParity D Sc n p) :
    appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc j n r) * affineLastCrossing D Sc i j n =
      Supercategory.koszulSign p (D.parity i * D.parity j) •
        (affineLastCrossing D Sc i j n *
          appendAlgebra D Sc j (n + 1) (appendAlgebra D Sc i n r)) := by
  change appendLinear D Sc i (n + 1) (appendLinear D Sc j n r) * _ =
    _ • (_ * appendLinear D Sc j (n + 1) (appendLinear D Sc i n r))
  conv_lhs => rw [FiniteHomMatrix.eq_sum_single r, map_sum, map_sum, Finset.sum_mul]
  conv_rhs => rw [FiniteHomMatrix.eq_sum_single r, map_sum, map_sum, Finset.mul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [appendLinear_single, appendLinear_single, appendLinear_single, appendLinear_single,
    entry_mul_crossing, crossing_mul_entry, induction_crossing_slide D Sc i j q.2 q.1 (r q) (hr q)]
  simp only [FiniteHomMatrix.single, DFinsupp.single_smul, Supercategory.koszulSign_smul_smul]

/-- The two different colour cuts act on their corresponding side. -/
theorem affineLastCrossing_corner (i j : I) (n : ℕ) :
    appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc j n 1) * affineLastCrossing D Sc i j n =
      affineLastCrossing D Sc i j n ∧
    affineLastCrossing D Sc i j n * appendAlgebra D Sc j (n + 1) (appendAlgebra D Sc i n 1) =
      affineLastCrossing D Sc i j n := by
  have hleft : appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc j n 1) *
      affineLastCrossing D Sc i j n = affineLastCrossing D Sc i j n := by
    change appendLinear D Sc i (n + 1)
      (appendLinear D Sc j n (FiniteHomMatrix.localUnit Finset.univ)) * _ = _
    rw [FiniteHomMatrix.localUnit, map_sum, map_sum, Finset.sum_mul]
    conv_rhs => unfold affineLastCrossing
    apply Finset.sum_congr rfl
    intro w _
    change appendLinear D Sc i (n + 1)
      (appendLinear D Sc j n (FiniteHomMatrix.single w w (𝟙 _))) * _ = _
    rw [appendLinear_single, appendLinear_single, entry_mul_crossing]
    change FiniteHomMatrix.single _ _ (inductionLastCrossing D Sc i j w ≫
      appendEnd D Sc i _ (appendEnd D Sc j w 1)) = _
    rw [map_one, map_one]
    exact congrArg (FiniteHomMatrix.single _ _) (Category.comp_id _)
  refine ⟨hleft, ?_⟩
  have h := affineLastCrossing_intertwines D Sc i j n (SetLike.one_mem_graded (affineParity D Sc n))
  simpa only [Supercategory.koszulSign_zero_left, one_smul, hleft] using h.symm

/-- The last-pair crossing in the cyclotomic quotient, at height `n+3`. -/
def cyclotomicLastCrossing (i j : I) (a : I → _root_.Polynomial k) (n : ℕ) :
    CyclotomicAlgebra D Sc a (n + 1 + 1) :=
  cyclotomicMk D Sc a (n + 1 + 1) (affineLastCrossing D Sc i j (n + 1))

theorem cyclotomicLastCrossing_parity (i j : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    cyclotomicLastCrossing D Sc i j a n ∈ cyclotomicParity D Sc a ha (n + 1 + 1)
      (D.parity i * D.parity j) :=
  cyclotomicMk_parity D Sc a ha (n + 1 + 1) (affineLastCrossing_parity D Sc i j (n + 1))

/-- Signed intertwining descends along the genuine cyclotomic quotient. -/
theorem cyclotomicLastCrossing_intertwines (i j : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) {p : ZMod 2}
    {r : CyclotomicAlgebra D Sc a n} (hr : r ∈ cyclotomicParity D Sc a ha n p) :
    cyclotomicAppend D Sc i a (n + 1) (cyclotomicAppend D Sc j a n r) *
        cyclotomicLastCrossing D Sc i j a n =
      Supercategory.koszulSign p (D.parity i * D.parity j) •
        (cyclotomicLastCrossing D Sc i j a n *
          cyclotomicAppend D Sc j a (n + 1) (cyclotomicAppend D Sc i a n r)) := by
  obtain ⟨r, hr', rfl⟩ := cyclotomicParity_lift D Sc a ha n hr
  change cyclotomicMk D Sc a (n + 1 + 1)
      (appendAlgebra D Sc i (n + 1 + 1) (appendAlgebra D Sc j (n + 1) r)) *
    cyclotomicMk D Sc a (n + 1 + 1) (affineLastCrossing D Sc i j (n + 1)) =
    Supercategory.koszulSign p (D.parity i * D.parity j) •
      (cyclotomicMk D Sc a (n + 1 + 1) (affineLastCrossing D Sc i j (n + 1)) *
        cyclotomicMk D Sc a (n + 1 + 1)
          (appendAlgebra D Sc j (n + 1 + 1) (appendAlgebra D Sc i (n + 1) r)))
  rw [← map_mul, ← map_mul, ← map_zsmul]
  exact congrArg (cyclotomicMk D Sc a (n + 1 + 1))
    (affineLastCrossing_intertwines D Sc i j (n + 1) hr')

/-- Both cut identities hold without a polynomial-parity assumption. -/
theorem cyclotomicLastCrossing_corner (i j : I) (a : I → _root_.Polynomial k) (n : ℕ) :
    cyclotomicAppend D Sc i a (n + 1) (cyclotomicAppend D Sc j a n 1) *
        cyclotomicLastCrossing D Sc i j a n = cyclotomicLastCrossing D Sc i j a n ∧
    cyclotomicLastCrossing D Sc i j a n *
        cyclotomicAppend D Sc j a (n + 1) (cyclotomicAppend D Sc i a n 1) =
      cyclotomicLastCrossing D Sc i j a n := by
  have h (i j : I) : cyclotomicAppend D Sc i a (n + 1) (cyclotomicAppend D Sc j a n 1) =
      cyclotomicMk D Sc a (n + 1 + 1)
        (appendAlgebra D Sc i (n + 1 + 1) (appendAlgebra D Sc j (n + 1) 1)) := by
    rw [← map_one (cyclotomicMk D Sc a n)]
    rfl
  rw [h i j, h j i, cyclotomicLastCrossing, ← map_mul, ← map_mul,
    (affineLastCrossing_corner D Sc i j (n + 1)).1,
    (affineLastCrossing_corner D Sc i j (n + 1)).2]
  exact ⟨rfl, rfl⟩

end OddMath.QuiverHecke
