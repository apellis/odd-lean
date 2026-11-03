import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMatrixNaturality
import OddMath.Algebra.FiniteSupermoduleFamily

/-! # Input-module functors of the prescribed finite grid matrices

DeformedMatrixComparison (4), (5). The given even entries assemble as
natural transformations on all input-module maps, including odd and
inhomogeneous maps. Explicit endpoint comparisons retain the literal
finite module matrices when their component inverses are attached.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u v
section FamilyAssembly
variable {k A : Type u} {X : Type v} [CommRing k] [Category.{u} X]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  {ι : Type} [Fintype ι]
private def familyColumns (F : ι → X ⥤ Superfunctor k A (SVec k))
    (G : X ⥤ Superfunctor k A (SVec k)) (η : ∀ a, F a ⟶ G)
    (hη : ∀ a x, (η a).app x ∈ parity (R := k) _ _ 0) :
    OddMath.FiniteSupermodule.familyFunctor F ⟶ G where
  app x := OddMath.FiniteSupermodule.columnsHom (fun a => (η a).app x) (fun a => hη a x)
  naturality {x y} f := OddMath.FiniteSupermodule.productMap_columnsHom
    (fun a => (F a).map f) (fun a => (η a).app y) (fun a => (η a).app x) (G.map f)
    (fun a => hη a y) (fun a => hη a x) (fun a => (η a).naturality f)
private def familyRows (F : ι → X ⥤ Superfunctor k A (SVec k))
    (G : X ⥤ Superfunctor k A (SVec k)) (η : ∀ a, G ⟶ F a)
    (hη : ∀ a x, (η a).app x ∈ parity (R := k) _ _ 0) :
    G ⟶ OddMath.FiniteSupermodule.familyFunctor F where
  app x := OddMath.FiniteSupermodule.rowsHom (fun a => (η a).app x) (fun a => hη a x)
  naturality {x y} f := (OddMath.FiniteSupermodule.rowsHom_productMap
    (fun a => (F a).map f) (fun a => (η a).app x) (fun a => (η a).app y) (G.map f)
    (fun a => hη a x) (fun a => hη a y) (fun a => ((η a).naturality f).symm)).symm

private theorem columns_endpoint
    (V W : ι → Superfunctor k A (SVec k)) (T : Superfunctor k A (SVec k))
    (h : ∀ a, V a = W a) (e : OddMath.FiniteSupermodule.product V = OddMath.FiniteSupermodule.product W)
    (f : ∀ a, W a ⟶ T) (hf : ∀ a, f a ∈ parity (R := k) _ _ 0)
    (hg : ∀ a, eqToHom (h a) ≫ f a ∈ parity (R := k) _ _ 0) :
    OddMath.FiniteSupermodule.columnsHom (fun a => eqToHom (h a) ≫ f a) hg =
      eqToHom e ≫ OddMath.FiniteSupermodule.columnsHom f hf := by
  have hh : V = W := funext h
  subst W
  simp only [eqToHom_refl, Category.id_comp]
omit [Fintype ι] in
private theorem rows_endpoint
    (V W : ι → Superfunctor k A (SVec k)) (T : Superfunctor k A (SVec k))
    (h : ∀ a, V a = W a) (e : OddMath.FiniteSupermodule.product V = OddMath.FiniteSupermodule.product W)
    (f : ∀ a, T ⟶ W a) (hf : ∀ a, f a ∈ parity (R := k) _ _ 0)
    (hg : ∀ a, f a ≫ eqToHom (h a).symm ∈ parity (R := k) _ _ 0) :
    OddMath.FiniteSupermodule.rowsHom (fun a => f a ≫ eqToHom (h a).symm) hg =
      OddMath.FiniteSupermodule.rowsHom f hf ≫ eqToHom e.symm := by
  have hh : V = W := funext h
  subst W
  simp only [eqToHom_refl, Category.comp_id]
end FamilyAssembly

private theorem endpoint_even {k : Type u} {C : Type v} [CommRing k] [Category.{u} C] [Preadditive C]
    [Linear k C] [Supercategory k C] {V W : C} (e : V = W) :
    eqToHom e ∈ parity (R := k) _ _ 0 := by
  cases e
  exact id_mem (R := k) V

variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

local instance gridMatrixFunctorPi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory

/-- The entire canonical unit source family as an input-module functor. -/
def gridUnitMatrixSourceFunctor (p : ZMod 2) (m : ℕ) :=
  OddMath.FiniteSupermodule.familyFunctor (gridUnitMatrixSummandFunctor (k := k) J p m)
/-- The entire canonical cap target family as an input-module functor. -/
def gridCapMatrixTargetFunctor (p : ZMod 2) (m : ℕ) :=
  OddMath.FiniteSupermodule.familyFunctor (gridCapMatrixSummandFunctor (k := k) K p m)

instance gridUnitMatrixSourceFunctor_additive (p : ZMod 2) (m : ℕ) :
    (gridUnitMatrixSourceFunctor (k := k) J p m).Additive where
  map_add {M N f g} := by
    change OddMath.FiniteSupermodule.productMap (fun a => (gridUnitMatrixSummandFunctor (k := k) J p m a).map (f + g)) =
      OddMath.FiniteSupermodule.productMap (fun a => (gridUnitMatrixSummandFunctor (k := k) J p m a).map f) +
        OddMath.FiniteSupermodule.productMap (fun a => (gridUnitMatrixSummandFunctor (k := k) J p m a).map g)
    simp only [Functor.map_add, OddMath.FiniteSupermodule.productMap_add]
instance gridUnitMatrixSourceFunctor_linear (p : ZMod 2) (m : ℕ) :
    (gridUnitMatrixSourceFunctor (k := k) J p m).Linear k where
  map_smul f r := by
    change OddMath.FiniteSupermodule.productMap (fun a => (gridUnitMatrixSummandFunctor (k := k) J p m a).map (r • f)) =
      r • OddMath.FiniteSupermodule.productMap (fun a => (gridUnitMatrixSummandFunctor (k := k) J p m a).map f)
    simp only [Functor.map_smul, OddMath.FiniteSupermodule.productMap_smul]
instance gridUnitMatrixSourceFunctor_super (p : ZMod 2) (m : ℕ) :
    IsSuperfunctor k (gridUnitMatrixSourceFunctor (k := k) J p m) where
  map_mem {M N q f} hf := by
    apply OddMath.FiniteSupermodule.productMap_mem
    intro a
    exact IsSuperfunctor.map_mem (F := gridUnitMatrixSummandFunctor (k := k) J p m a) hf

instance gridCapMatrixTargetFunctor_additive (p : ZMod 2) (m : ℕ) :
    (gridCapMatrixTargetFunctor (k := k) K p m).Additive where
  map_add {M N f g} := by
    change OddMath.FiniteSupermodule.productMap (fun a => (gridCapMatrixSummandFunctor (k := k) K p m a).map (f + g)) =
      OddMath.FiniteSupermodule.productMap (fun a => (gridCapMatrixSummandFunctor (k := k) K p m a).map f) +
        OddMath.FiniteSupermodule.productMap (fun a => (gridCapMatrixSummandFunctor (k := k) K p m a).map g)
    simp only [Functor.map_add, OddMath.FiniteSupermodule.productMap_add]
instance gridCapMatrixTargetFunctor_linear (p : ZMod 2) (m : ℕ) :
    (gridCapMatrixTargetFunctor (k := k) K p m).Linear k where
  map_smul f r := by
    change OddMath.FiniteSupermodule.productMap (fun a => (gridCapMatrixSummandFunctor (k := k) K p m a).map (r • f)) =
      r • OddMath.FiniteSupermodule.productMap (fun a => (gridCapMatrixSummandFunctor (k := k) K p m a).map f)
    simp only [Functor.map_smul, OddMath.FiniteSupermodule.productMap_smul]
instance gridCapMatrixTargetFunctor_super (p : ZMod 2) (m : ℕ) :
    IsSuperfunctor k (gridCapMatrixTargetFunctor (k := k) K p m) where
  map_mem {M N q f} hf := by
    apply OddMath.FiniteSupermodule.productMap_mem
    intro a
    exact IsSuperfunctor.map_mem (F := gridCapMatrixSummandFunctor (k := k) K p m a) hf

theorem gridUnitMatrixSourceFunctor_obj (p : ZMod 2) (m : ℕ)
    (N : Superfunctor k A (SVec k)) :
    (gridUnitMatrixSourceFunctor J p m).obj N =
      OddMath.FiniteSupermodule.product (gridUnitMatrixFamily J p N m) := by
  change OddMath.FiniteSupermodule.product _ = _
  congr 1
  funext a
  exact gridUnitMatrixSummandFunctor_obj J p m a N
theorem gridCapMatrixTargetFunctor_obj (p : ZMod 2) (m : ℕ)
    (N : Superfunctor k A (SVec k)) :
    (gridCapMatrixTargetFunctor K p m).obj N =
      OddMath.FiniteSupermodule.product (gridCapMatrixFamily K p N m) := by
  change OddMath.FiniteSupermodule.product _ = _
  congr 1
  funext a
  exact gridCapMatrixSummandFunctor_obj K p m a N

variable {p : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hγ : IsSupernatural k p γ)
  {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
private theorem unitInputEntry_mem (m : ℕ) (a : Option (Fin m))
    (N : Superfunctor k A (SVec k)) :
    (gridUnitMatrixEntryNatTrans J K hγ hβ m a).app N ∈ parity (R := k) _ _ 0 := by
  rw [gridUnitMatrixEntryNatTrans_app]
  have h := comp_mem (endpoint_even (gridUnitMatrixSummandFunctor_obj J p m a N))
    (gridUnitMatrixEntry_mem J K hγ hβ N m a)
  set_option backward.dsimp.instances true in
    dsimp only [induction, Functor.comp_obj] at h ⊢
  simpa only [zero_add] using h
private theorem capInputEntry_mem (m : ℕ) (a : Option (Fin m))
    (N : Superfunctor k A (SVec k)) :
    (gridCapMatrixEntryNatTrans J K hγ hα m a).app N ∈ parity (R := k) _ _ 0 := by
  rw [gridCapMatrixEntryNatTrans_app]
  have h := comp_mem (gridCapMatrixEntry_mem J K hγ hα N m a)
    (endpoint_even (gridCapMatrixSummandFunctor_obj K p m a N).symm)
  set_option backward.dsimp.instances true in
    dsimp only [induction, Functor.comp_obj] at h ⊢
  simpa only [zero_add] using h

/-- The given full unit matrix is natural in every input-module map. -/
def gridUnitMatrixInputNatTrans (m : ℕ) :
    gridUnitMatrixSourceFunctor J p m ⟶ induction (k := k) K ⋙ restriction (k := k) K :=
  familyColumns _ _ (gridUnitMatrixEntryNatTrans J K hγ hβ m) (unitInputEntry_mem J K hγ hβ m)
/-- The given full cap matrix is natural in every input-module map. -/
def gridCapMatrixInputNatTrans (m : ℕ) :
    restriction (k := k) J ⋙ induction (k := k) J ⟶ gridCapMatrixTargetFunctor K p m :=
  familyRows _ _ (gridCapMatrixEntryNatTrans J K hγ hα m) (capInputEntry_mem J K hγ hα m)

/-- The natural unit component is the given module matrix with its explicit endpoint. -/
theorem gridUnitMatrixInputNatTrans_app (m : ℕ) (N : Superfunctor k A (SVec k)) :
    (gridUnitMatrixInputNatTrans J K hγ hβ m).app N =
      eqToHom (gridUnitMatrixSourceFunctor_obj J p m N) ≫ gridUnitMatrixModuleMap J K hγ hβ N m := by
  dsimp only [gridUnitMatrixInputNatTrans, familyColumns]
  simp only [gridUnitMatrixEntryNatTrans_app]
  exact columns_endpoint _ _ _ (fun a => gridUnitMatrixSummandFunctor_obj J p m a N)
    (gridUnitMatrixSourceFunctor_obj J p m N) _ _ _
/-- The natural cap component is the given module matrix with its explicit endpoint. -/
theorem gridCapMatrixInputNatTrans_app (m : ℕ) (N : Superfunctor k A (SVec k)) :
    (gridCapMatrixInputNatTrans J K hγ hα m).app N =
      gridCapMatrixModuleMap J K hγ hα N m ≫ eqToHom (gridCapMatrixTargetFunctor_obj K p m N).symm := by
  dsimp only [gridCapMatrixInputNatTrans, familyRows]
  simp only [gridCapMatrixEntryNatTrans_app]
  exact rows_endpoint _ _ _ (fun a => gridCapMatrixSummandFunctor_obj K p m a N)
    (gridCapMatrixTargetFunctor_obj K p m N) _ _ _

/-- Every given input-natural unit component is even. -/
theorem gridUnitMatrixInputNatTrans_app_mem (m : ℕ) (N : Superfunctor k A (SVec k)) :
    (gridUnitMatrixInputNatTrans J K hγ hβ m).app N ∈ parity (R := k) _ _ 0 := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  funext t
  change (if q = 0 then _ else 0) = 0
  split_ifs with h
  · exact (hq h).elim
  · rfl
/-- Every given input-natural cap component is even. -/
theorem gridCapMatrixInputNatTrans_app_mem (m : ℕ) (N : Superfunctor k A (SVec k)) :
    (gridCapMatrixInputNatTrans J K hγ hα m).app N ∈ parity (R := k) _ _ 0 := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  funext t
  change (if q = 0 then _ else 0) = 0
  split_ifs with h
  · exact (hq h).elim
  · rfl

/-- Reindex a given unit-module inverse at the literal input-functor endpoint. -/
def gridUnitMatrixInputComponentIso (m : ℕ) (N : Superfunctor k A (SVec k))
    (e : OddMath.FiniteSupermodule.product (gridUnitMatrixFamily J p N m) ≅
      (restriction K).obj (induced K N)) :
    (gridUnitMatrixSourceFunctor J p m).obj N ≅ (induction K ⋙ restriction K).obj N :=
  eqToIso (gridUnitMatrixSourceFunctor_obj J p m N) ≪≫ e
/-- Reindex a given cap-module inverse at the literal input-functor endpoint. -/
def gridCapMatrixInputComponentIso (m : ℕ) (N : Superfunctor k A (SVec k))
    (e : induced J ((restriction J).obj N) ≅
      OddMath.FiniteSupermodule.product (gridCapMatrixFamily K p N m)) :
    (restriction J ⋙ induction J).obj N ≅ (gridCapMatrixTargetFunctor K p m).obj N :=
  e ≪≫ eqToIso (gridCapMatrixTargetFunctor_obj K p m N).symm

theorem gridUnitMatrixInputComponentIso_hom (m : ℕ) (N : Superfunctor k A (SVec k))
    (e : OddMath.FiniteSupermodule.product (gridUnitMatrixFamily J p N m) ≅
      (restriction K).obj (induced K N)) (he : e.hom = gridUnitMatrixModuleMap J K hγ hβ N m) :
    (gridUnitMatrixInputComponentIso J K m N e).hom = (gridUnitMatrixInputNatTrans J K hγ hβ m).app N := by
  change eqToHom (gridUnitMatrixSourceFunctor_obj J p m N) ≫ e.hom = _
  rw [he]
  exact (gridUnitMatrixInputNatTrans_app J K hγ hβ m N).symm

theorem gridCapMatrixInputComponentIso_hom (m : ℕ) (N : Superfunctor k A (SVec k))
    (e : induced J ((restriction J).obj N) ≅
      OddMath.FiniteSupermodule.product (gridCapMatrixFamily K p N m))
    (he : e.hom = gridCapMatrixModuleMap J K hγ hα N m) :
    (gridCapMatrixInputComponentIso J K m N e).hom = (gridCapMatrixInputNatTrans J K hγ hα m).app N := by
  change e.hom ≫ eqToHom (gridCapMatrixTargetFunctor_obj K p m N).symm = _
  rw [he]
  exact (gridCapMatrixInputNatTrans_app J K hγ hα m N).symm

end OddMath.QuiverHecke.ELVOld.BalancedInduction
