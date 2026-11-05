import OddMath.Algebra.FiniteSupermoduleFunctor

/-! # Coordinatewise families of supermodule isomorphisms

The finite shifted summands in Brundan--Ellis (1.13)--(1.14) are transported
by their individual chosen comparisons. This constructs their product
comparison as a natural isomorphism on all input-module maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.FiniteSupermodule
universe u v w
variable {k : Type u} [CommRing k]
  {C : Type v} [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
  {ι : Type} {V W : ι → Superfunctor k C (SVec k)}

/-- The coordinatewise isomorphism retaining each specified comparison. -/
def productIso (e : ∀ a, V a ≅ W a) : product V ≅ product W where
  hom := productMap fun a => (e a).hom
  inv := productMap fun a => (e a).inv
  hom_inv_id := by
    rw [← productMap_comp]
    simp only [Iso.hom_inv_id, productMap_id]
  inv_hom_id := by
    rw [← productMap_comp]
    simp only [Iso.inv_hom_id, productMap_id]

variable {A : Type w} [Category A]

/-- Pointwise products of module-valued functors, acting on both map parities. -/
def familyFunctor (F : ι → A ⥤ Superfunctor k C (SVec k)) :
    A ⥤ Superfunctor k C (SVec k) where
  obj x := product fun a => (F a).obj x
  map f := productMap fun a => (F a).map f
  map_id x := by simp only [CategoryTheory.Functor.map_id, productMap_id]
  map_comp f g := by simp only [CategoryTheory.Functor.map_comp, productMap_comp]

end OddMath.FiniteSupermodule
