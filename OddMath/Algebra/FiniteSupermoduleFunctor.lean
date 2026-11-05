import OddMath.Algebra.FiniteSupermodule

/-! # Functorial finite families of supermodules

Finite coordinate maps and their even row/column assemblies, needed for
input-module naturality of Brundan--Ellis (1.13)--(1.14).
The maps act on both homogeneous components; input maps need not be even.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.FiniteSupermodule
universe u v
variable {k : Type u} [CommRing k]
  {C : Type v} [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
  {ι : Type} {V W Z : ι → Superfunctor k C (SVec k)}

/-- Coordinatewise maps, retaining both components of each supernatural map. -/
def productMap (f : ∀ a, V a ⟶ W a) : product V ⟶ product W where
  app p t := LinearMap.pi fun a => ((f a).app p t).comp (LinearMap.proj a)
  app_mem p t := by
    apply SVec.mem_parityHom_of_apply_mem
    intro q x hx
    change x ∈ (FiniteSuperspace.product fun a => (V a).obj t).part q at hx
    change (fun a => (f a).app p t (x a)) ∈
      (FiniteSuperspace.product fun a => (W a).obj t).part (q + p)
    rw [FiniteSuperspace.mem_product_part] at hx ⊢
    intro a
    exact SVec.apply_mem_part ((f a).app_mem p t) (hx a)
  naturality p t t' q g hg := by
    apply LinearMap.ext
    intro x
    funext a
    exact LinearMap.congr_fun ((f a).naturality p g hg) (x a)

@[simp] theorem productMap_total_apply (f : ∀ a, V a ⟶ W a)
    (t : C) (x : (product V).obj t) (a : ι) :
    (productMap f).total t x a = (f a).total t (x a) := rfl

@[simp] theorem productMap_id (V : ι → Superfunctor k C (SVec k)) :
    productMap (fun a => 𝟙 (V a)) = 𝟙 (product V) := by
  apply Superfunctor.hom_ext_parity <;> intro t <;> apply LinearMap.ext <;>
    intro x <;> funext a <;> rfl

@[simp] theorem productMap_comp (f : ∀ a, V a ⟶ W a) (g : ∀ a, W a ⟶ Z a) :
    productMap (fun a => f a ≫ g a) = productMap f ≫ productMap g := by
  apply Superfunctor.hom_ext
  intro p t
  apply LinearMap.ext
  intro x
  funext a
  rfl

@[simp] theorem productMap_add (f g : ∀ a, V a ⟶ W a) :
    productMap (fun a => f a + g a) = productMap f + productMap g := by
  apply Superfunctor.hom_ext
  intro p t
  apply LinearMap.ext
  intro x
  funext a
  rfl

@[simp] theorem productMap_smul (r : k) (f : ∀ a, V a ⟶ W a) :
    productMap (fun a => r • f a) = r • productMap f := by
  apply Superfunctor.hom_ext
  intro p t
  apply LinearMap.ext
  intro x
  funext a
  rfl

/-- Coordinatewise assembly preserves a specified map parity. -/
theorem productMap_mem {p : ZMod 2} (f : ∀ a, V a ⟶ W a)
    (hf : ∀ a, f a ∈ parity (R := k) _ _ p) :
    productMap f ∈ parity (R := k) _ _ p := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  funext t
  apply LinearMap.ext
  intro x
  funext a
  exact LinearMap.congr_fun (Superfunctor.app_eq_zero_of_mem (hf a) hq t) (x a)

/-- Total components detect an arbitrary supernatural map. -/
theorem hom_ext_total {F G : Superfunctor k C (SVec k)} {f g : F ⟶ G}
    (h : ∀ t, f.total t = g.total t) : f = g := by
  apply Superfunctor.hom_ext
  intro p t
  have hp (s : F ⟶ G) : proj k p (s.total t) = s.app p t := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · exact proj_eq_of_add rfl (s.app_mem 0 t) (s.app_mem 1 t)
    · exact proj_eq_of_add (add_comm _ _) (s.app_mem 1 t)
        (by simpa using s.app_mem 0 t)
  rw [← hp f, ← hp g, h t]

variable {T : Superfunctor k C (SVec k)}

/-- The even module morphism determined by a finite family of columns. -/
def columnsHom [Fintype ι] (f : ∀ a, V a ⟶ T)
    (hf : ∀ a, f a ∈ parity (R := k) _ _ 0) : product V ⟶ T :=
  SuperNatTrans.ofNatTrans (columns f hf) (fun t =>
    FiniteSuperspace.assembleColumns_even _ _ _ fun a => by
      rw [total_eq_zeroComponent (f a) (hf a) t]
      exact (f a).app_mem 0 t)

/-- The even module morphism determined by a family of rows. -/
def rowsHom (f : ∀ a, T ⟶ V a)
    (hf : ∀ a, f a ∈ parity (R := k) _ _ 0) : T ⟶ product V :=
  SuperNatTrans.ofNatTrans (rows f hf) (fun t =>
    FiniteSuperspace.assembleRows_even _ _ _ fun a => by
      rw [total_eq_zeroComponent (f a) (hf a) t]
      exact (f a).app_mem 0 t)

@[simp] theorem columnsHom_total_apply [Fintype ι] (f : ∀ a, V a ⟶ T)
    (hf : ∀ a, f a ∈ parity (R := k) _ _ 0)
    (t : C) (x : (product V).obj t) :
    (columnsHom f hf).total t x = ∑ a, (f a).total t (x a) := by
  change (∑ a, (f a).total t (x a)) + 0 = _
  exact add_zero _

@[simp] theorem rowsHom_total_apply (f : ∀ a, T ⟶ V a)
    (hf : ∀ a, f a ∈ parity (R := k) _ _ 0)
    (t : C) (x : T.obj t) (a : ι) :
    (rowsHom f hf).total t x a = (f a).total t x := by
  change (f a).total t x + 0 = _
  exact add_zero _

/-- Finite columns commute with a coordinate map whenever every column does. -/
theorem productMap_columnsHom [Fintype ι] {U : Superfunctor k C (SVec k)}
    (f : ∀ a, V a ⟶ W a) (g : ∀ a, W a ⟶ T) (h : ∀ a, V a ⟶ U) (j : U ⟶ T)
    (hg : ∀ a, g a ∈ parity (R := k) _ _ 0)
    (hh : ∀ a, h a ∈ parity (R := k) _ _ 0)
    (hc : ∀ a, f a ≫ g a = h a ≫ j) :
    productMap f ≫ columnsHom g hg = columnsHom h hh ≫ j := by
  apply hom_ext_total
  intro t
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  ext x
  change (columnsHom g hg).total t ((productMap f).total t x) =
    j.total t ((columnsHom h hh).total t x)
  simp only [columnsHom_total_apply, productMap_total_apply, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact LinearMap.congr_fun (by
    simpa only [Superfunctor.comp_total] using congrArg (fun f => f.total t) (hc a)) (x a)

end OddMath.FiniteSupermodule
