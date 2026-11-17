import StringDiagrams.Super.MonoidalEnvelope
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerChains.IntertwinerMeet
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient

/-!
# Last strand

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
end

end

section

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
end

end

section

/-!
# Peeling the last letter off the moving-strand map

The QP induction of `docs/Nondegeneracy/DeformedGlobalQP.md`, §3 (the deformed form of
Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of Theorem 8.5) removes the last spectator
letter: `V_n = g_n (V_(n-1) ⊗ 1)`. The map `moveHom` is defined by peeling the first
letter, so this file proves the other recursion.

* `whiskerWordRingHom`: right whiskering by a word as a ring homomorphism of
  endomorphism rings;
* `genE_whiskerRight`, `sameIntertwiner_whiskerRight`, `intertwinerHom_whiskerRight`:
  a positioned generator or intertwiner on a word, whiskered on the right by a word,
  is the same generator on the concatenated word;
* `moveHom_append_singleton`: `moveHom i l (ν ++ [x])` is `moveHom i l ν ⊗ 1_x`
  followed by the intertwiner `g` at the last two positions.

Every statement holds for arbitrary colours, parities and words, including empty ones.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory SignedNilHecke

variable {I X : Type*} [AddCommGroup X] (D : SKM.Datum I X) {k : Type*} [CommRing k]
  (Sc : SKM.Scalars D k)

/-- Right whiskering by the word `s`, as a ring homomorphism of endomorphism rings. -/
def whiskerWordRingHom (w s : List I) :
    End ((pres D Sc).obj (ob D w)) →+* End ((pres D Sc).obj (ob D (w ++ s))) where
  toFun f := f ▷ (pres D Sc).obj (ob D s)
  map_one' := MonoidalSupercategory.id_whiskerRight (R := k) _ _
  map_mul' f g := MonoidalSupercategory.comp_whiskerRight (R := k) g f _
  map_zero' := MonoidalSupercategory.zero_whiskerRight k _
  map_add' f g := MonoidalSupercategory.add_whiskerRight (R := k) f g _

@[simp] theorem whiskerWordRingHom_apply (w s : List I) (f : End ((pres D Sc).obj (ob D w))) :
    whiskerWordRingHom D Sc w s f = f ▷ (pres D Sc).obj (ob D s) := rfl

/-- A positioned generator fixing the word `w` keeps its meaning after right whiskering. -/
theorem genE_whiskerRight (w s : List I) (g : PG) (h : SChain w (pl w [g]) w)
    (hg : g.pos + g.width ≤ w.length) :
    genE D Sc w g ▷ (pres D Sc).obj (ob D s) = genE D Sc (w ++ s) g := by
  have hf : Fits w.length [g] := by
    intro g' hg'
    simp only [List.mem_singleton] at hg'
    subst hg'
    exact hg
  rw [genE_eq D Sc h, cl_whiskerRight D Sc [g] h s hf]
  exact (genE_eq D Sc _).symm

theorem dotE_whiskerRight (w s : List I) (a : ℕ) (ha : a < w.length) :
    dotE D Sc w a ▷ (pres D Sc).obj (ob D s) = dotE D Sc (w ++ s) a :=
  genE_whiskerRight D Sc w s (.dot a) (sChain_dotAny w a) (by simpa [PG.pos, PG.width] using ha)

/-- The same-colour intertwiner keeps its meaning after right whiskering. -/
theorem sameIntertwiner_whiskerRight (l r s : List I) (i : I) :
    sameIntertwiner D Sc (l ++ [i, i] ++ r) l.length i ▷ (pres D Sc).obj (ob D s) =
      sameIntertwiner D Sc (l ++ [i, i] ++ r ++ s) l.length i := by
  have hx : whiskerWordRingHom D Sc (l ++ [i, i] ++ r) s (dotE D Sc (l ++ [i, i] ++ r) l.length) =
      dotE D Sc (l ++ [i, i] ++ r ++ s) l.length :=
    dotE_whiskerRight D Sc (l ++ [i, i] ++ r) s l.length (by simp)
  have hy : whiskerWordRingHom D Sc (l ++ [i, i] ++ r) s
      (dotE D Sc (l ++ [i, i] ++ r) (l.length + 1)) =
      dotE D Sc (l ++ [i, i] ++ r ++ s) (l.length + 1) :=
    dotE_whiskerRight D Sc (l ++ [i, i] ++ r) s (l.length + 1) (by simp)
  have hc : whiskerWordRingHom D Sc (l ++ [i, i] ++ r) s (crossE D Sc (l ++ [i, i] ++ r) l.length) =
      crossE D Sc (l ++ [i, i] ++ r ++ s) l.length :=
    genE_whiskerRight D Sc _ s (.cross l.length) (sChain_cross l r i rfl rfl)
      (by simp [PG.pos, PG.width])
  change whiskerWordRingHom D Sc (l ++ [i, i] ++ r) s
      (sameIntertwiner D Sc (l ++ [i, i] ++ r) l.length i) = _
  unfold sameIntertwiner
  split_ifs
  · simp only [OddNilHecke.Intertwiner.element, OddNilHecke.Intertwiner.squareDiff, map_sub,
      map_mul, map_pow, hx, hy, hc]
  · simp only [gEven, phiEven, map_sub, map_mul, map_add, map_one, hx, hy, hc]

/-- Transport of a same-colour intertwiner along an equality of words. -/
theorem sameIntertwiner_eq_transport {w w' : List I} (h : w = w') (a : ℕ) (i : I) :
    sameIntertwiner D Sc w a i =
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h) ≫
        sameIntertwiner D Sc w' a i ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h.symm) := by
  subst h
  simp

/-- Transport of an intertwiner along equalities of its left and right contexts. -/
theorem intertwinerHom_congr {l l' r r' : List I} (hl : l = l') (hr : r = r') (i j : I) :
    intertwinerHom D Sc l r i j =
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (by rw [hl, hr])) ≫
        intertwinerHom D Sc l' r' i j ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (by rw [hl, hr])) := by
  subst hl hr
  simp

/-- Transporting a class along equalities of its source and target words. -/
theorem cl_eq_transport {t t' u u' : List I} {gs : List PG} (e : t = u) (e' : t' = u')
    (h : SChain t (pl t gs) t') (h' : SChain u (pl u gs) u') :
    cl D Sc t t' gs h =
      eqToHom (congrArg (fun w => (pres D Sc).obj (ob D w)) e) ≫ cl D Sc u u' gs h' ≫
        eqToHom (congrArg (fun w => (pres D Sc).obj (ob D w)) e'.symm) := by
  subst e e'
  simp

/-- Right whiskering of an intertwiner by a word is the intertwiner with the longer
right context. -/
theorem intertwinerHom_whiskerRight (l r s : List I) (i j : I) :
    intertwinerHom D Sc l r i j ▷ (pres D Sc).obj (ob D s) =
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
          (show l ++ [i, j] ++ r ++ s = l ++ [i, j] ++ (r ++ s) by simp)) ≫
        intertwinerHom D Sc l (r ++ s) i j ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
            (show l ++ [j, i] ++ (r ++ s) = l ++ [j, i] ++ r ++ s by simp)) := by
  by_cases h : i = j
  · subst h
    rw [intertwinerHom_self, intertwinerHom_self, sameIntertwiner_whiskerRight,
      sameIntertwiner_eq_transport D Sc (show l ++ [i, i] ++ r ++ s = l ++ [i, i] ++ (r ++ s) by simp)]
  · have hf : Fits (l ++ [i, j] ++ r).length [.cross l.length] := by
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      simp [PG.pos, PG.width]
    rw [intertwinerHom_of_ne D Sc _ _ h, intertwinerHom_of_ne D Sc _ _ h,
      cl_whiskerRight D Sc [.cross l.length] _ s hf]
    rw [cl_eq_transport D Sc (show l ++ [i, j] ++ r ++ s = l ++ [i, j] ++ (r ++ s) by simp)
      (show l ++ [j, i] ++ r ++ s = l ++ [j, i] ++ (r ++ s) by simp) _
      (sChain_crossAt l (r ++ s) i j)]

/-- Right whiskering of an identification of words. -/
theorem eqToHom_whiskerRight_word {w w' : List I} (h : w = w') (s : List I) :
    eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h) ▷ (pres D Sc).obj (ob D s) =
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (congrArg (· ++ s) h)) := by
  subst h
  exact MonoidalSupercategory.id_whiskerRight (R := k) _ _

/-- Right whiskering of an arbitrary identification of objects. -/
theorem eqToHom_whiskerRight_obj {Y Y' : (pres D Sc).Presented} (h : Y = Y')
    (Z : (pres D Sc).Presented) :
    eqToHom h ▷ Z = eqToHom (congrArg (· ⊗ Z) h) := by
  subst h
  exact MonoidalSupercategory.id_whiskerRight (R := k) _ _

/-- KKO's `V_(n+1) = g_(n+1) (V_n ⊗ 1)`: the moving strand first crosses `ν`, then the
final letter `x`. The left context `l` is arbitrary. -/
theorem moveHom_append_singleton (i x : I) : ∀ (ν l : List I),
    moveHom D Sc i l (ν ++ [x]) =
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
          (show l ++ i :: (ν ++ [x]) = l ++ i :: ν ++ [x] by simp)) ≫
        (moveHom D Sc i l ν ▷ (pres D Sc).obj (ob D [x])) ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
            (show l ++ ν ++ [i] ++ [x] = l ++ ν ++ [i, x] ++ [] by simp)) ≫
            intertwinerHom D Sc (l ++ ν) [] i x ≫
              eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
                (show l ++ ν ++ [x, i] ++ [] = l ++ (ν ++ [x]) ++ [i] by simp))
  | [], l => by
    simp only [List.nil_append, moveHom]
    rw [eqToHom_whiskerRight_word D Sc (show l ++ [i] = l ++ [] ++ [i] by simp)]
    rw [intertwinerHom_congr D Sc (show l ++ [] = l by simp) rfl i x]
    simp
  | j :: ν, l => by
    have ih := moveHom_append_singleton i x ν (l ++ [j])
    simp only [List.cons_append, moveHom]
    rw [ih]
    simp only [MonoidalSupercategory.comp_whiskerRight (R := k), Category.assoc,
      eqToHom_whiskerRight_obj, intertwinerHom_whiskerRight]
    rw [intertwinerHom_congr D Sc (show l ++ [j] ++ ν = l ++ j :: ν by simp) rfl i x]
    simp

end OddMath.QuiverHecke
end

end

section

/-!
# The last-to-first crossing map as a positioned word

The map `lastToFirstHom i ν : ν ++ [i] → i :: ν` of the all-prefix identity (K) is the
crossing `Tₙ` of the global QP induction in `docs/Nondegeneracy/DeformedGlobalQP.md`, §3
(the deformed form of Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of Theorem 8.5). It is
defined by peeling the first letter of `ν`. This file writes it as the positioned word
`crossingDescent ν.length = [cross (n-1), …, cross 0]` and derives the recursion that peels
the last letter: `T_(n+1) = τ_n (T_n ⊗ 1)`.

* `lastToFirstHom_eq_cl`: `lastToFirstHom i ν` is the class of `crossingDescent ν.length`;
* `lastToFirstHom_append_singleton`: `lastToFirstHom i (ν ++ [x])` is the crossing at
  position `|ν|` followed by `lastToFirstHom i ν ⊗ 1_x`.

Arbitrary colours, parities and words.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) [CommRing k]
  (Sc : SKM.Scalars D k)

/-- The crossings `cross (n-1), …, cross 0`, in this order. -/
def crossingDescent : ℕ → List PG
  | 0 => []
  | n + 1 => .cross n :: crossingDescent n

theorem crossingDescent_succ_shift : ∀ n : ℕ,
    crossingDescent (n + 1) = (crossingDescent n).map (PG.shift 1) ++ [.cross 0]
  | 0 => rfl
  | n + 1 => by
    show PG.cross (n + 1) :: crossingDescent (n + 1) =
      (PG.cross n :: crossingDescent n).map (PG.shift 1) ++ [.cross 0]
    rw [crossingDescent_succ_shift n, List.map_cons, PG.shift_cross, Nat.add_comm 1 n,
      List.cons_append]

theorem fits_crossingDescent (n : ℕ) : Fits (n + 1) (crossingDescent n) := by
  induction n with
  | zero => intro g hg; simp [crossingDescent] at hg
  | succ n ih =>
    intro g hg
    rw [crossingDescent, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp [PG.pos, PG.width]
    · have := ih g hg
      omega

/-- `lastToFirstHom i ν` is the class of the positioned word `crossingDescent |ν|`. -/
theorem lastToFirstHom_eq_cl (i : I) : ∀ ν : List I,
    ∃ h : SChain (ν ++ [i]) (pl (ν ++ [i]) (crossingDescent ν.length)) (i :: ν),
      lastToFirstHom D Sc i ν = cl D Sc _ _ (crossingDescent ν.length) h
  | [] => ⟨sChain_pl [i] [], by simp [lastToFirstHom, crossingDescent, cl_nil]⟩
  | j :: ν => by
    obtain ⟨h, hν⟩ := lastToFirstHom_eq_cl i ν
    have h₂ : SChain (j :: i :: ν) (pl (j :: i :: ν) [.cross 0]) (i :: j :: ν) := by
      simpa using sChain_crossAt [] ν j i
    have h₁ := (by rw [pl_shift]; simpa using sChain_wh h [j] [] :
      SChain ([j] ++ (ν ++ [i])) (pl ([j] ++ (ν ++ [i]))
        ((crossingDescent ν.length).map (PG.shift [j].length))) ([j] ++ (i :: ν)))
    refine ⟨?_, ?_⟩
    · rw [List.length_cons, crossingDescent_succ_shift]
      exact sChain_append_of h₁ h₂
    · rw [lastToFirstHom, hν, cl_whiskerLeft]
      refine (cl_comp D Sc (t := j :: (ν ++ [i])) (t₁ := j :: i :: ν) (t' := i :: j :: ν)
        _ _ h₁ h₂).trans ?_
      exact cl_congr_gs D Sc
        (by rw [show (j :: ν).length = ν.length + 1 from rfl, crossingDescent_succ_shift]; rfl) _ _

/-- KKO's `T_(n+1) = τ_n (T_n ⊗ 1)`: moving the last strand to the front first crosses it
past `x`, then past `ν`. -/
theorem lastToFirstHom_append_singleton (i x : I) (ν : List I) :
    lastToFirstHom D Sc i (ν ++ [x]) =
      cl D Sc (ν ++ [x] ++ [i]) (ν ++ [i] ++ [x]) [.cross ν.length]
          (by simpa using sChain_crossAt ν [] x i) ≫
        (lastToFirstHom D Sc i ν ▷ (pres D Sc).obj (ob D [x])) := by
  obtain ⟨h, hν⟩ := lastToFirstHom_eq_cl D Sc i ν
  obtain ⟨h', hν'⟩ := lastToFirstHom_eq_cl D Sc i (ν ++ [x])
  have hf : Fits (ν ++ [i]).length (crossingDescent ν.length) := by
    simpa using fits_crossingDescent ν.length
  rw [hν', hν, cl_whiskerRight D Sc _ h [x] hf, cl_comp]
  exact cl_congr_gs D Sc (by simp [crossingDescent]) _ _

end OddMath.QuiverHecke
end

end
