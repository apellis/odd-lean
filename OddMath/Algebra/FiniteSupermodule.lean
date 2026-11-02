import OddMath.Algebra.FiniteSuperspace
import StringDiagrams.Super.FunctorCategory

/-! # Finite coordinate families of supermodules

Pointwise finite families used in the prescribed matrices of
Brundan--Ellis (1.13)--(1.14). Even module rows and columns assemble into
ordinary natural transformations without restrictions on the parity of
the category arrows.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.FiniteSupermodule
universe u v
variable {k : Type u} [CommRing k]
  {C : Type v} [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
  {ι : Type} (V : ι → Superfunctor k C (SVec k))

/-- Pointwise coordinate action of a family of supermodules. -/
def productFunctor : C ⥤ SVec k where
  obj t := FiniteSuperspace.product fun a => (V a).obj t
  map f := LinearMap.pi fun a => ((V a).map f).comp (LinearMap.proj a)
  map_id t := by
    apply LinearMap.ext
    intro x
    funext a
    exact LinearMap.congr_fun ((V a).toFunctor.map_id t) (x a)
  map_comp f g := by
    apply LinearMap.ext
    intro x
    funext a
    exact LinearMap.congr_fun ((V a).toFunctor.map_comp f g) (x a)

instance : (productFunctor V).Additive where
  map_add {X Y f g} := by
    apply LinearMap.ext
    intro x
    funext a
    have h : (V a).map (f + g) = (V a).map f + (V a).map g := Functor.map_add _
    exact LinearMap.congr_fun h (x a)

instance : (productFunctor V).Linear k where
  map_smul f r := by
    apply LinearMap.ext
    intro x
    funext a
    exact LinearMap.congr_fun ((V a).toFunctor.map_smul r f) (x a)

instance : IsSuperfunctor k (productFunctor V) where
  map_mem {X Y p f} hf := by
    apply SVec.mem_parityHom_of_apply_mem
    intro q x hx
    change x ∈ (FiniteSuperspace.product fun a => (V a).obj X).part q at hx
    change (fun a => (V a).map f (x a)) ∈
      (FiniteSuperspace.product fun a => (V a).obj Y).part (q + p)
    rw [FiniteSuperspace.mem_product_part] at hx ⊢
    intro a
    exact SVec.apply_mem_part ((V a).map_mem hf) (hx a)

/-- Pointwise product with its pointwise superspace grading. -/
def product : Superfunctor k C (SVec k) := ⟨productFunctor V⟩

variable {V} {W : Superfunctor k C (SVec k)}

/-- The total component of an even module map equals its ordinary natural component. -/
theorem total_eq_zeroComponent {F G : Superfunctor k C (SVec k)}
    (f : F ⟶ G) (hf : f ∈ parity (R := k) F G 0) (t : C) :
    f.total t = f.toNatTrans.app t := by
  have hz := Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) t
  change f.app 0 t + f.app 1 t = f.app 0 t
  rw [hz, add_zero]

/-- Even columns assemble naturally, also along inhomogeneous arrows. -/
def columns [Fintype ι] (f : ∀ a, V a ⟶ W)
    (hf : ∀ a, f a ∈ parity (R := k) (V a) W 0) :
    (product V).toFunctor ⟶ W.toFunctor where
  app t := FiniteSuperspace.assembleColumns _ _ fun a => (f a).total t
  naturality X Y g := by
    ext x
    change (∑ a, (f a).total Y ((V a).map g (x a))) =
      W.map g (∑ a, (f a).total X (x a))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [total_eq_zeroComponent (f a) (hf a) Y,
      total_eq_zeroComponent (f a) (hf a) X]
    exact LinearMap.congr_fun ((f a).toNatTrans.naturality g) (x a)

/-- Even rows assemble naturally into the pointwise family. -/
def rows (f : ∀ a, W ⟶ V a)
    (hf : ∀ a, f a ∈ parity (R := k) W (V a) 0) :
    W.toFunctor ⟶ (product V).toFunctor where
  app t := FiniteSuperspace.assembleRows _ _ fun a => (f a).total t
  naturality X Y g := by
    apply LinearMap.ext
    intro x
    funext a
    change (f a).total Y (W.map g x) = (V a).map g ((f a).total X x)
    rw [total_eq_zeroComponent (f a) (hf a) Y,
      total_eq_zeroComponent (f a) (hf a) X]
    exact LinearMap.congr_fun ((f a).toNatTrans.naturality g) x

end OddMath.FiniteSupermodule
