import OddMath.QuiverHecke.CyclotomicAction.ELVWeightInverseProducts

/-! # Augmented inverse maps on whole product endofunctors

Brundan–Ellis (1.13)–(1.14): coordinatewise natural augmented inverses
at a common finite window assemble on the entire product category.
Every parity component and every inverse entry, including entries beyond
the window, is retained. No finiteness of the set of blocks is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.SKM
open OddMath.QuiverHecke.CyclotomicAction
universe u v r t
variable {k : Type r} [CommRing k] {ι : Type t} {C : ι → Type u}
  [∀ a, Category.{v} (C a)] [∀ a, Preadditive (C a)]
  [∀ a, Linear k (C a)] [∀ a, Supercategory k (C a)]

/-- Independent endofunctors act on their own input block. -/
def superfunctorProduct (F : ∀ a, Superfunctor k (C a) (C a)) :
    Superfunctor k (∀ a, C a) (∀ a, C a) :=
  ⟨productFunctor C id C (fun a => (F a).toFunctor)⟩

/-- Whole natural maps act coordinatewise in both parity components. -/
def superNatTransProduct {F G : ∀ a, Superfunctor k (C a) (C a)}
    (f : ∀ a, F a ⟶ G a) : superfunctorProduct F ⟶ superfunctorProduct G where
  app p M a := (f a).app p (M a)
  app_mem p M a := (f a).app_mem p (M a)
  naturality p _M _N _q h hh := funext fun a => (f a).naturality p (h a) (hh a)

@[simp] theorem superNatTransProduct_app {F G : ∀ a, Superfunctor k (C a) (C a)}
    (f : ∀ a, F a ⟶ G a) (p : ZMod 2) (M : ∀ a, C a) (a : ι) :
    (superNatTransProduct f).app p M a = (f a).app p (M a) := rfl

@[simp] theorem superNatTransProduct_total {F G : ∀ a, Superfunctor k (C a) (C a)}
    (f : ∀ a, F a ⟶ G a) (M : ∀ a, C a) (a : ι) :
    (superNatTransProduct f).total M a = (f a).total (M a) := rfl

/-- Product endofunctors and their whole natural maps form a functor. -/
def superfunctorProductMap : (∀ a, Superfunctor k (C a) (C a)) ⥤
    Superfunctor k (∀ a, C a) (∀ a, C a) where
  obj := superfunctorProduct
  map := superNatTransProduct
  map_id F := by
    apply Superfunctor.hom_ext
    intro p M
    funext a
    rcases parity_eq_zero_or_one p with rfl | rfl <;> rfl
  map_comp f g := by
    apply Superfunctor.hom_ext
    intro p M
    funext a
    rfl

instance superfunctorProductMap_additive : (superfunctorProductMap (k := k) (C := C)).Additive where
  map_add := by
    intros
    apply Superfunctor.hom_ext
    intro p M
    funext a
    rfl

instance superfunctorProductMap_linear : (superfunctorProductMap (k := k) (C := C)).Linear k where
  map_smul f c := by
    apply Superfunctor.hom_ext
    intro p M
    funext a
    rfl

/-- A common parity on the coordinate maps is the parity of the whole product map. -/
theorem superNatTransProduct_mem {F G : ∀ a, Superfunctor k (C a) (C a)}
    {p : ZMod 2} (f : ∀ a, F a ⟶ G a)
    (hf : ∀ a, f a ∈ parity (R := k) _ _ p) :
    superNatTransProduct f ∈ parity (R := k) _ _ p := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  funext M a
  exact Superfunctor.app_eq_zero_of_mem (hf a) hq (M a)

instance superfunctorProductMap_super : IsSuperfunctor k (superfunctorProductMap (k := k) (C := C)) where
  map_mem hf := superNatTransProduct_mem _ hf

private def mapInvTo {L V : Type*} [Category L] [Preadditive L] [Linear k L] [Supercategory k L]
    [Category V] [Preadditive V] [Linear k V] [Supercategory k V]
    (F : L ⥤ V) [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    {A B Z : L} {f : A ⟶ B} {g : ℕ → (A ⟶ Z)} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
    (J : SuperSumInvTo (k := k) f g p q n) :
    SuperSumInvTo (k := k) (F.map f) (fun m => F.map (g m)) p q n where
  f' := F.map J.f'
  g' m := F.map (J.g' m)
  f_mem := map_mem F J.f_mem
  g_mem m := map_mem F (J.g_mem m)
  f'_mem := map_mem F J.f'_mem
  g'_mem m := map_mem F (J.g'_mem m)
  total := by
    have h := congrArg F.map J.total
    simpa only [Functor.map_add, Functor.map_sum, Functor.map_comp, F.map_id] using h
  ff := by rw [← F.map_comp, J.ff, F.map_id]
  fg m hm := by rw [← F.map_comp, J.fg m hm, F.map_zero]
  gf m hm := by rw [← F.map_comp, J.gf m hm, F.map_zero]
  gg m l hm hl := by
    rw [← F.map_comp, J.gg m l hm hl]
    split_ifs <;> simp only [F.map_id, F.map_zero]

private def mapInvFrom {L V : Type*} [Category L] [Preadditive L] [Linear k L] [Supercategory k L]
    [Category V] [Preadditive V] [Linear k V] [Supercategory k V]
    (F : L ⥤ V) [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    {A B Z : L} {f : B ⟶ A} {g : ℕ → (Z ⟶ A)} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
    (J : SuperSumInvFrom (k := k) f g p q n) :
    SuperSumInvFrom (k := k) (F.map f) (fun m => F.map (g m)) p q n where
  f' := F.map J.f'
  g' m := F.map (J.g' m)
  f_mem := map_mem F J.f_mem
  g_mem m := map_mem F (J.g_mem m)
  f'_mem := map_mem F J.f'_mem
  g'_mem m := map_mem F (J.g'_mem m)
  total := by
    have h := congrArg F.map J.total
    simpa only [Functor.map_add, Functor.map_sum, Functor.map_comp, F.map_id] using h
  ff := by rw [← F.map_comp, J.ff, F.map_id]
  fg m hm := by rw [← F.map_comp, J.fg m hm, F.map_zero]
  gf m hm := by rw [← F.map_comp, J.gf m hm, F.map_zero]
  gg m l hm hl := by
    rw [← F.map_comp, J.gg m l hm hl]
    split_ifs <;> simp only [F.map_id, F.map_zero]

section Inverses
variable {A B Z : ∀ a, Superfunctor k (C a) (C a)}
  {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}

/-- Coordinate row inverses glue to whole product endofunctors, with literal product entries. -/
def superSumInvToProduct {f : ∀ a, A a ⟶ B a} {g : ℕ → ∀ a, A a ⟶ Z a}
    (J : ∀ a, SuperSumInvTo (k := k) (f a) (fun m => g m a) p q n) :
    SuperSumInvTo (k := k) (superNatTransProduct f) (fun m => superNatTransProduct (g m)) p q n :=
  mapInvTo (superfunctorProductMap (k := k) (C := C)) (SuperSumInvTo.pi J)

/-- Coordinate column inverses glue to whole product endofunctors, retaining all inverse rows. -/
def superSumInvFromProduct {f : ∀ a, B a ⟶ A a} {g : ℕ → ∀ a, Z a ⟶ A a}
    (J : ∀ a, SuperSumInvFrom (k := k) (f a) (fun m => g m a) p q n) :
    SuperSumInvFrom (k := k) (superNatTransProduct f) (fun m => superNatTransProduct (g m)) p q n :=
  mapInvFrom (superfunctorProductMap (k := k) (C := C)) (SuperSumInvFrom.pi J)

@[simp] theorem superSumInvToProduct_f' {f : ∀ a, A a ⟶ B a} {g : ℕ → ∀ a, A a ⟶ Z a}
    (J : ∀ a, SuperSumInvTo (k := k) (f a) (fun m => g m a) p q n) :
    (superSumInvToProduct J).f' = superNatTransProduct (fun a => (J a).f') := rfl

@[simp] theorem superSumInvToProduct_g' {f : ∀ a, A a ⟶ B a} {g : ℕ → ∀ a, A a ⟶ Z a}
    (J : ∀ a, SuperSumInvTo (k := k) (f a) (fun m => g m a) p q n) (m : ℕ) :
    (superSumInvToProduct J).g' m = superNatTransProduct (fun a => (J a).g' m) := rfl

@[simp] theorem superSumInvFromProduct_f' {f : ∀ a, B a ⟶ A a} {g : ℕ → ∀ a, Z a ⟶ A a}
    (J : ∀ a, SuperSumInvFrom (k := k) (f a) (fun m => g m a) p q n) :
    (superSumInvFromProduct J).f' = superNatTransProduct (fun a => (J a).f') := rfl

@[simp] theorem superSumInvFromProduct_g' {f : ∀ a, B a ⟶ A a} {g : ℕ → ∀ a, Z a ⟶ A a}
    (J : ∀ a, SuperSumInvFrom (k := k) (f a) (fun m => g m a) p q n) (m : ℕ) :
    (superSumInvFromProduct J).g' m = superNatTransProduct (fun a => (J a).g' m) := rfl
end Inverses
end OddMath.SKM
