import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTripleDotComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVTripleDotAffineContexts

/-! # The three prescribed weight dots in indexed polynomial coordinates

Brundan--Ellis (1.9), the repeated-outer correction. Evaluate the same
selected triple chart on each literal native dot and retain exactly the
indexed affine generators used by the ordered polynomial.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem normalized_module_square
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A B : Superfunctor k C (SVec k)} (e : A ≅ B) (x : End A) (z z' : End B)
    (h : x ≫ e.hom = e.hom ≫ z) (hz : z = z') (w : C) :
    ModuleCoordinateSquare e x w (z'.total w) := by
  have hs := h.trans (congrArg (fun q => e.hom ≫ q) hz)
  have ht := congrArg (fun q => q.total w) hs
  rw [Superfunctor.comp_total, Superfunctor.comp_total] at ht
  exact ht

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

private theorem indexed_dot_transform_eq {β γ : Multiset I} {σ : List I}
    (h : β + (σ : Multiset I) = γ) {p : ZMod 2}
    {a b : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ p)
    (hab : a = b) (M : ContentModules D Sc cutoff bound β) :
    (contentInductionTransform D Sc cutoff bound h h ha).app p M =
      (contentInductionTransform D Sc cutoff bound h h hb).app p M := by
  cases hab
  rfl

private theorem middleIndex_mem (l j i : I) :
    dotE D Sc [l,j,i] 1 ∈ parity (R := k) _ _ (D.parity j) := by
  simpa using positionedDot_parity D Sc [l] [i] j
private theorem lastIndex_mem (l j i : I) :
    dotE D Sc [l,j,i] 2 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa using positionedDot_parity D Sc [l,j] [] i

variable (i j l : I) (Λ : X) {a b c d : X}
  (hal : a + D.α l = b) (hbj : b + D.α j = c) (hci : c + D.α i = d)
  (β : WeightBlocks D Λ a)
local notation "β₃" => elvBlockSucc₃ D i j l Λ hal hbj hci β
local notation "hT" => elvBlockTriple_content_eq D i j l Λ hal hbj hci β
local notation "C₃" => elvWeightTripleComparison D Sc cutoff bound i j l Λ hal hbj hci β β₃ rfl
local notation "hpFirst" => MonoidalSupercategory.whiskerRight_mem (R := k)
  (Presentation.obj (pres D Sc) (ob D [j])) (firstDot_parity D Sc l [])
local notation "hpMiddle" => MonoidalSupercategory.whiskerLeft_mem (R := k)
  (Presentation.obj (pres D Sc) (ob D [l])) (firstDot_parity D Sc j [])
local notation "htFirst" => MonoidalSupercategory.whiskerRight_mem (R := k)
  (Presentation.obj (pres D Sc) (ob D [i])) hpFirst
local notation "htMiddle" => MonoidalSupercategory.whiskerRight_mem (R := k)
  (Presentation.obj (pres D Sc) (ob D [i])) hpMiddle
local notation "htLast" => MonoidalSupercategory.whiskerLeft_mem (R := k)
  (Presentation.obj (pres D Sc) (ob D [l,j])) (firstDot_parity D Sc i [])

/-- The literal first weight dot is the indexed affine generator zero
under the selected triple chart, with full coefficient parity. -/
theorem elvWeightTripleDot_first_coordinate
    (M : ELVWeightProduct D Sc cutoff bound Λ a)
    (w : ContentCategory D Sc cutoff bound β₃.1) :
    ModuleCoordinateSquare ((C₃).app M)
      ((elvWeightTripleFirstDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃) w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff bound hT hT (firstDot_parity D Sc l [j,i])) (M β) w) := by
  have hz := indexed_dot_transform_eq D Sc cutoff bound (σ := [l,j,i]) hT
    htFirst (firstDot_parity D Sc l [j,i]) (tripleFirstDot_affineContexts D Sc l j i) (M β)
  have h := normalized_module_square ((C₃).app M)
    ((elvWeightTripleFirstDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃) _ _
    (by simpa only [Iso.app_hom] using
      elvWeightTripleFirstDot_comparison D Sc cutoff bound i j l Λ hal hbj hci β M) hz w
  simpa only [contentInductionTransform_total] using h

/-- The literal middle weight dot is the indexed affine generator one,
using the identical selected triple chart. -/
theorem elvWeightTripleDot_middle_coordinate
    (M : ELVWeightProduct D Sc cutoff bound Λ a)
    (w : ContentCategory D Sc cutoff bound β₃.1) :
    ModuleCoordinateSquare ((C₃).app M)
      ((elvWeightTripleMiddleDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃) w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff bound hT hT (middleIndex_mem D Sc l j i)) (M β) w) := by
  have hz := indexed_dot_transform_eq D Sc cutoff bound (σ := [l,j,i]) hT
    htMiddle (middleIndex_mem D Sc l j i) (tripleMiddleDot_affineIndex D Sc l j i) (M β)
  have h := normalized_module_square ((C₃).app M)
    ((elvWeightTripleMiddleDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃) _ _
    (by simpa only [Iso.app_hom] using
      elvWeightTripleMiddleDot_comparison D Sc cutoff bound i j l Λ hal hbj hci β M) hz w
  simpa only [contentInductionTransform_total] using h

/-- The literal last weight dot is the indexed affine generator two,
with the true native pair value and selected triple chart retained. -/
theorem elvWeightTripleDot_last_coordinate
    (M : ELVWeightProduct D Sc cutoff bound Λ a)
    (w : ContentCategory D Sc cutoff bound β₃.1) :
    ModuleCoordinateSquare ((C₃).app M)
      ((elvWeightTripleLastDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃) w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff bound hT hT (lastIndex_mem D Sc l j i)) (M β) w) := by
  have hz := indexed_dot_transform_eq D Sc cutoff bound (σ := [l,j,i]) hT
    htLast (lastIndex_mem D Sc l j i) (tripleLastDot_affineIndex D Sc l j i) (M β)
  have h := normalized_module_square ((C₃).app M)
    ((elvWeightTripleLastDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃) _ _
    (by simpa only [Iso.app_hom] using
      elvWeightTripleLastDot_comparison D Sc cutoff bound i j l Λ hal hbj hci β M) hz w
  simpa only [contentInductionTransform_total] using h

end OddMath.QuiverHecke.ELVOld
