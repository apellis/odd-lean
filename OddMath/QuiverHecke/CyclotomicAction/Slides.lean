/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.Induction

/-!
# The signed dot slide for strand induction

Ports the dot-intertwining step of
`Categorification/KLR/CyclotomicAction/Slides.lean` and
`Categorification/KLR/CyclotomicAction/Induction.lean`. The ordinary intertwiner
condition is replaced by the homogeneous super-intertwiner condition. These
are actual affine Hom morphisms; descent of their parity to the cyclotomic
supercategory is a separate obligation.
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- The one-strand dot, with its literal generator diagram. -/
def inductionStrandDot (i : I) :
    End ((pres D Sc).obj (ob D [i])) :=
  (pres D Sc).diag (mkD D [([], .dot i, [])] ⟨rfl, rfl⟩)

theorem inductionStrandDot_parity (i : I) :
    inductionStrandDot D Sc i ∈ Supercategory.parity (R := k)
      ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D [i])) (D.parity i) := by
  apply Presentation.diag_mem_homDeg'
  simp [degree_parity_mkD, Shape.parity]

/-- The new dot on a word is the rightmost whiskered generator. -/
def inductionLastDot (i : I) {n : ℕ} (w : Word I n) :
    End (wordObj D Sc (appendWord i w)) :=
  wordObj D Sc w ◁ inductionStrandDot D Sc i

/-- Moving the new dot past a homogeneous old morphism has its Koszul sign. -/
theorem induction_dot_slide (i : I) {n : ℕ} (s t : Word I n) {p : ZMod 2}
    (f : wordObj D Sc s ⟶ wordObj D Sc t)
    (hf : f ∈ Supercategory.parity (R := k) (wordObj D Sc s) (wordObj D Sc t) p) :
    appendHom D Sc i s t f ≫ inductionLastDot D Sc i t =
      Supercategory.koszulSign p (D.parity i) •
        (inductionLastDot D Sc i s ≫ appendHom D Sc i s t f) :=
  MonoidalSupercategory.super_interchange hf (inductionStrandDot_parity D Sc i)

/-- An odd dot slides with a minus sign past an odd old morphism. -/
theorem induction_dot_slide_odd (i : I) (hi : D.parity i = 1)
    {n : ℕ} (s t : Word I n) (f : wordObj D Sc s ⟶ wordObj D Sc t)
    (hf : f ∈ Supercategory.parity (R := k) (wordObj D Sc s) (wordObj D Sc t) 1) :
    appendHom D Sc i s t f ≫ inductionLastDot D Sc i t =
      -(inductionLastDot D Sc i s ≫ appendHom D Sc i s t f) := by
  simpa [hi] using induction_dot_slide D Sc i s t f hf

end OddMath.QuiverHecke
