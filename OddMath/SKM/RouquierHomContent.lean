import OddMath.SKM.RouquierHomAdjunction
import StringDiagrams.Super.Pi
import Mathlib.Data.Finsupp.Weight

/-!
# Content parity and shifted Hom-sector adjunctions

This ports the weight-indexed Hom functors of
`Categorification/TwoRep/RouqProduct.lean` and the parity bookkeeping needed
by `RouqProductKLR.lean` and `RouqProductLeft.lean`. Its downstream consumer
is the sector comparison in `SuperRouquierLoc.MateProjectionFormula`.

A finite colour content is retained separately from its image in the weight
lattice: parity need not descend along a noninjective root map. Postcomposition
by colour `i` is shifted by `p(i) P(betaP)`. The change of that shift upon adding
colour `j` is exactly `p(i)p(j)`. The Π-action on morphisms is the given
superfunctor, not an unsigned identification of shifted objects.

The right adjoint of this shifted postcomposition functor is constructed,
with Π on the input side. This module does not supply the reverse, shifted
factor adjunction needed for the raising precomposition summand, nor the
original-datum rational crossings and multicolour coherence.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

section Content
variable {I X : Type*} [AddCommGroup X] (D : Datum I X)

/-- Total parity of a finite colour content, before passage to the weight lattice. -/
def contentParity : (I →₀ ℕ) →+ ZMod 2 := Finsupp.weight D.parity

/-- The shift on the postcomposition summand in the asymmetric Hom convention. -/
def homContentShift (i : I) (β : I →₀ ℕ) : ZMod 2 := D.parity i * contentParity D β

@[simp] theorem contentParity_single (i : I) (n : ℕ) :
    contentParity D (Finsupp.single i n) = n • D.parity i :=
  Finsupp.weight_single _ _ _

/-- Adding an opposite-sector label changes the shift by its crossing parity. -/
theorem homContentShift_add_single (i j : I) (β : I →₀ ℕ) :
    homContentShift D i (β + Finsupp.single j 1) =
      homContentShift D i β + D.parity i * D.parity j := by
  simp [homContentShift, map_add, mul_add]

/-- Word concatenation gives the same shift as successive postcomposition steps. -/
theorem homContentShift_add (i : I) (β γ : I →₀ ℕ) :
    homContentShift D i (β + γ) = homContentShift D i β + homContentShift D i γ := by
  simp [homContentShift, map_add, mul_add]
end Content

section Shift
variable {k : Type r} [CommRing k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] [Supercategory k C] [PiSupercategory k C]

/-- Π is self-adjoint; the even comparison Π² ≅ Id supplies both triangles. -/
def homPiAdjunction : PiSupercategory.pi (R := k) (C := C) ⊣
    PiSupercategory.pi (R := k) (C := C) where
  unit := (PiSupercategory.ξIso (R := k)).inv
  counit := (PiSupercategory.ξIso (R := k)).hom
  left_triangle_components f := by
    change (PiSupercategory.pi (R := k)).map (PiSupercategory.ξ (R := k) f).inv ≫
      (PiSupercategory.ξ (R := k) ((PiSupercategory.pi (R := k)).obj f)).hom = _
    rw [PiSupercategory.ξ_pi, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  right_triangle_components f := by
    change (PiSupercategory.ξ (R := k) ((PiSupercategory.pi (R := k)).obj f)).inv ≫
      (PiSupercategory.pi (R := k)).map (PiSupercategory.ξ (R := k) f).hom = _
    rw [← PiSupercategory.ξ_pi, Iso.inv_hom_id]

/-- Parity-indexed shift on the full Hom category, retaining its action on odd maps. -/
def homParityShift (p : ZMod 2) : C ⥤ C :=
  if p = 0 then 𝟭 C else PiSupercategory.pi (R := k)

instance (p : ZMod 2) : (homParityShift (k := k) (C := C) p).Additive := by
  unfold homParityShift
  split_ifs <;> infer_instance

instance (p : ZMod 2) : (homParityShift (k := k) (C := C) p).Linear k := by
  unfold homParityShift
  split_ifs <;> infer_instance

instance (p : ZMod 2) : IsSuperfunctor k (homParityShift (k := k) (C := C) p) := by
  unfold homParityShift
  split_ifs <;> infer_instance

/-- Every parity shift is its own right adjoint. -/
def homParityShiftAdjunction (p : ZMod 2) :
    homParityShift (k := k) (C := C) p ⊣ homParityShift (k := k) (C := C) p := by
  unfold homParityShift
  split_ifs
  · exact Adjunction.id
  · exact homPiAdjunction
end Shift

section Sectors
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}

/-- The original-weight Hom category, with the contravariant factor negated. -/
abbrev homWeightSector (T W : X → B) (muP muM : X) := T (-muP) ⟶ W muM

/-- Content-shifted raising postcomposition at the original datum's weights. -/
def homContentPostE (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM) :
    homWeightSector T W.obj muP muM ⥤ homWeightSector T W.obj muP nuM :=
  homPost (k := k) (W.E i h) ⋙ homParityShift (k := k) (homContentShift D i betaP)

/-- The right adjoint with the parity shift on its input side. -/
def homContentPostF (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM) :
    homWeightSector T W.obj muP nuM ⥤ homWeightSector T W.obj muP muM :=
  homParityShift (k := k) (homContentShift D i betaP) ⋙ homPost (k := k) (W.F i h)

instance (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM) :
    (homContentPostE T W i betaP muP h).Additive := by
  unfold homContentPostE
  infer_instance

instance (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM) :
    (homContentPostF T W i betaP muP h).Additive := by
  unfold homContentPostF
  infer_instance

instance (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM) :
    (homContentPostE T W i betaP muP h).Linear k := by
  unfold homContentPostE
  infer_instance

instance (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM) :
    (homContentPostF T W i betaP muP h).Linear k := by
  unfold homContentPostF
  infer_instance

/-- The shifted postcomposition still preserves the parity of every homogeneous map. -/
instance (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM) :
    IsSuperfunctor k (homContentPostE T W i betaP muP h) := by
  unfold homContentPostE
  infer_instance

instance (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM) :
    IsSuperfunctor k (homContentPostF T W i betaP muP h) := by
  unfold homContentPostF
  infer_instance

/-- The shifted postcomposition adjunction uses the same reservoir content on
both ends, since this edge changes only the probe content. -/
def homContentPostAdjunction (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM) :
    homContentPostE T W i betaP muP h ⊣ homContentPostF T W i betaP muP h :=
  (homPostAdjunction (a := T (-muP)) (W.adj i h)).comp
    (homParityShiftAdjunction (homContentShift D i betaP))

/-- Raising precomposition uses the factor E edge in reverse weight direction.
Its right adjoint requires the factor's shifted left adjunction; the given
right adjunction alone instead makes this functor a right adjoint. -/
def homContentPreE (T : RouquierFamily (k := k) (B := B) D) (W : X → B)
    (i : I) (muM : X) {muP nuP : X} (h : -nuP + D.α i = -muP) :
    homWeightSector T.obj W muP muM ⥤ homWeightSector T.obj W nuP muM :=
  homPre (k := k) (T.E i h)

end Sectors
end OddMath.SKM
