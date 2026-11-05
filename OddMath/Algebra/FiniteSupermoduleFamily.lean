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

/-- Coordinatewise natural comparisons retain the prescribed product maps. -/
def familyNatIso {F G : ι → A ⥤ Superfunctor k C (SVec k)}
    (e : ∀ a, F a ≅ G a) : familyFunctor F ≅ familyFunctor G :=
  NatIso.ofComponents (fun x => productIso fun a => (e a).app x) (by
    intro x y f
    change productMap _ ≫ productMap _ = productMap _ ≫ productMap _
    rw [← productMap_comp, ← productMap_comp]
    congr 1
    funext a
    exact (e a).hom.naturality f)

@[simp] theorem familyNatIso_hom_total_apply
    {F G : ι → A ⥤ Superfunctor k C (SVec k)}
    (e : ∀ a, F a ≅ G a) (x : A) (t : C)
    (z : ((familyFunctor F).obj x).obj t) (a : ι) :
    ((familyNatIso e).hom.app x).total t z a =
      ((e a).hom.app x).total t (z a) := rfl

end OddMath.FiniteSupermodule
