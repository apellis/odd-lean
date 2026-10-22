/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.CategoryTheory.Idempotents.FunctorExtension
import OddMath.QuiverHecke.RowFunctor

/-!
# The graded Karoubi envelope as a category of graded right supermodules

Brundan–Ellis, arXiv:1701.04133v2, §11, (11.2): the graded super Karoubi envelope
`GSKar(C) = Kar(C̲_{q,π})` of a graded supercategory `C` (BE2 Definition 6.10) maps fully
faithfully to graded right supermodules over the Hom-matrix algebra `Mat` of all objects of `C`
(`gsKarFunctor`, `gsKarFunctorFullyFaithful`). It extends the row-module functor
`Q^m Π^a λ ↦ Q^m Π^a (1_λ · Mat)` of `OddMath.QuiverHecke.RowFunctor` first to matrices and then
to the Karoubi envelope, using that graded right supermodules form an additive, idempotent
complete category.

The two extension steps are generic:

* `matLift F : Mat_ C ⥤ D` extends an additive functor `F : C ⥤ D` to a category with finite
  biproducts, and is fully faithful when `F` is (`matLiftFullyFaithful`);
* `karoubiLift G : Karoubi A ⥤ D` extends a functor `G : A ⥤ D` to an idempotent complete
  category, and is fully faithful when `G` is (`karoubiLiftFullyFaithful`).

`matLift` is `Mat_.lift` without the restriction that `C` and `D` live in the same universes.
-/

@[expose] public noncomputable section

namespace OddMath

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

universe v₁ v₂ u₁ u₂

section MatLift

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasFiniteBiproducts D]

attribute [local simp] biproduct.lift_desc

/-- The extension of an additive functor `F : C ⥤ D` to matrices: a matrix object goes to the
biproduct of the images of its entries, a matrix of morphisms to the matrix of their images. -/
@[simps]
def matLift (F : C ⥤ D) [F.Additive] : Mat_ C ⥤ D where
  obj X := ⨁ fun i => F.obj (X.X i)
  map f := biproduct.matrix fun i j => F.map (f i j)
  map_id X := by
    ext i j
    by_cases h : j = i
    · subst h; simp
    · simp [h]

/-- The extension of a fully faithful additive functor to matrices is fully faithful. -/
def matLiftFullyFaithful (F : C ⥤ D) [F.Additive] (hF : F.FullyFaithful) :
    (matLift F).FullyFaithful where
  preimage {X Y} φ := fun i j =>
    hF.preimage (biproduct.ι (fun i => F.obj (X.X i)) i ≫ φ ≫
      biproduct.π (fun j => F.obj (Y.X j)) j)
  map_preimage {X Y} φ := by
    refine biproduct.hom_ext' _ _ fun i => biproduct.hom_ext _ _ fun j => ?_
    simp
  preimage_map {X Y} f := by
    ext i j
    simp

end MatLift

section KaroubiLift

variable {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D] [IsIdempotentComplete D]

/-- The extension of a functor `G : A ⥤ D` to the Karoubi envelope of `A`, for `D` idempotent
complete: an idempotent `p` on `X` goes to a chosen image of `G.map p`. -/
def karoubiLift (G : A ⥤ D) : Karoubi A ⥤ D :=
  (functorExtension A D).obj G

/-- The extension of a fully faithful functor to the Karoubi envelopes is fully faithful. -/
def karoubiMapFullyFaithful (G : A ⥤ D) (hG : G.FullyFaithful) :
    ((functorExtension₂ A D).obj G).FullyFaithful where
  preimage {P Q} φ := ⟨hG.preimage φ.f, hG.map_injective (by
    simpa using φ.comm)⟩
  map_preimage {P Q} φ := by
    ext
    change G.map (hG.preimage φ.f) = φ.f
    simp
  preimage_map {P Q} f := by
    ext
    change hG.preimage (G.map f.f) = f.f
    simp

/-- The extension of a fully faithful functor to the Karoubi envelope of its source is fully
faithful. -/
def karoubiLiftFullyFaithful (G : A ⥤ D) (hG : G.FullyFaithful) :
    (karoubiLift G).FullyFaithful :=
  (karoubiMapFullyFaithful G hG).comp (toKaroubiEquivalence D).fullyFaithfulInverse

/-- The inclusion of `(karoubiLift G).obj P` as a summand of `G.obj P.X`. -/
def karoubiLiftι (G : A ⥤ D) (P : Karoubi A) : (karoubiLift G).obj P ⟶ G.obj P.X :=
  (toKaroubiEquivalence D).inverse.map (Karoubi.decompId_i (((functorExtension₂ A D).obj G).obj P)) ≫
    (toKaroubiEquivalence D).unitIso.inv.app (G.obj P.X)

/-- The projection of `G.obj P.X` onto its summand `(karoubiLift G).obj P`. -/
def karoubiLiftπ (G : A ⥤ D) (P : Karoubi A) : G.obj P.X ⟶ (karoubiLift G).obj P :=
  (toKaroubiEquivalence D).unitIso.hom.app (G.obj P.X) ≫
    (toKaroubiEquivalence D).inverse.map (Karoubi.decompId_p (((functorExtension₂ A D).obj G).obj P))

/-- `(karoubiLift G).obj P` is a retract of `G.obj P.X`. -/
@[reassoc (attr := simp)]
theorem karoubiLiftι_π (G : A ⥤ D) (P : Karoubi A) :
    karoubiLiftι G P ≫ karoubiLiftπ G P = 𝟙 _ := by
  rw [karoubiLiftι, karoubiLiftπ, Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    ← Karoubi.decompId]
  exact (toKaroubiEquivalence D).inverse.map_id _

/-- An isomorphism of the formal image of `G.map P.p` with an object `M` of `D` gives an
isomorphism `(karoubiLift G).obj P ≅ M`. -/
def karoubiLiftObjIso (G : A ⥤ D) (P : Karoubi A) (M : D)
    (e : ((functorExtension₂ A D).obj G).obj P ≅ (toKaroubi D).obj M) :
    (karoubiLift G).obj P ≅ M :=
  (toKaroubiEquivalence D).inverse.mapIso e ≪≫ (toKaroubiEquivalence D).unitIso.symm.app M

end KaroubiLift

namespace FiniteHomMatrix

universe u v w

open StringDiagrams GradedSupercategory

variable {k : Type u} [CommRing k] {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
  [Supercategory k C] [GradedSupercategory k C]

variable (k C) in
/-- **BE2 §11, (11.2).** The functor from the graded super Karoubi envelope `GSKar(C)` to graded
right supermodules over the Hom-matrix algebra of all objects of `C`, extending
`Q^m Π^a λ ↦ Q^m Π^a (1_λ · Mat)`. -/
def gsKarFunctor : GSKar k C ⥤ GSMod.{u, v, w, v, max v w} k (fun X : C => X) :=
  karoubiLift (matLift (rowFunctor k C))

/-- **BE2 §11, (11.2).** The functor from the graded super Karoubi envelope to graded right
supermodules is fully faithful. -/
def gsKarFunctorFullyFaithful : (gsKarFunctor k C).FullyFaithful :=
  karoubiLiftFullyFaithful _ (matLiftFullyFaithful _ rowFunctorFullyFaithful)

instance : (gsKarFunctor k C).Full := gsKarFunctorFullyFaithful.full

instance : (gsKarFunctor k C).Faithful := gsKarFunctorFullyFaithful.faithful

end FiniteHomMatrix

end OddMath
