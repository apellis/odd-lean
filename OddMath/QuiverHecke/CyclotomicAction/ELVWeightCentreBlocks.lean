import OddMath.QuiverHecke.CyclotomicAction.ELVWeightModules
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleCentre

/-! # Exact-content components of a whole-weight supercentral map

Zero extension and naturality show that an identity transformation on the
weight product depends at each output content only on that input component.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke.ELVOld.WeightCentreBlocks
open CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) {x : X} (β : WeightBlocks D Λ x)

private def extensionComponent (δ : WeightBlocks D Λ x) :
    Superfunctor k (ContentModules D Sc cutoff N β.1) (ContentModules D Sc cutoff N δ.1) :=
  if h : δ = β then by subst δ; exact Superfunctor.id k _
  else ⟨elvZeroFunctor D Sc cutoff N δ.1⟩
private def extensionFunctor :
    ContentModules D Sc cutoff N β.1 ⥤ ELVWeightProduct D Sc cutoff N Λ x :=
  Functor.pi' fun δ => (extensionComponent D Sc cutoff N Λ β δ).toFunctor
private instance : (extensionFunctor D Sc cutoff N Λ β).Additive where
  map_add := funext fun δ => (extensionComponent D Sc cutoff N Λ β δ).toFunctor.map_add
private instance : (extensionFunctor D Sc cutoff N Λ β).Linear k where
  map_smul f r := funext fun δ => (extensionComponent D Sc cutoff N Λ β δ).toFunctor.map_smul r f
private instance : IsSuperfunctor k (extensionFunctor D Sc cutoff N Λ β) where
  map_mem hf δ := IsSuperfunctor.map_mem
    (F := (extensionComponent D Sc cutoff N Λ β δ).toFunctor) hf

/-- Place one exact-content module in its original-weight block and zero
modules in every other block, including root collisions. -/
def extension : Superfunctor k (ContentModules D Sc cutoff N β.1)
    (ELVWeightProduct D Sc cutoff N Λ x) := ⟨extensionFunctor D Sc cutoff N Λ β⟩

private theorem component_selected : extensionComponent D Sc cutoff N Λ β β = Superfunctor.id k _ := by
  simp [extensionComponent]

theorem extension_eval : (extension D Sc cutoff N Λ β).comp (elvBlockEval D Sc cutoff N Λ β) =
    Superfunctor.id k (ContentModules D Sc cutoff N β.1) := by
  change extensionComponent D Sc cutoff N Λ β β = _
  exact component_selected D Sc cutoff N Λ β

/-- Restrict a literal whole-weight identity transformation by zero extension
and exact output projection. -/
def restrict (η : Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x) ⟶
    Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x)) :
    ModuleCentre.Centre D Sc cutoff N β.1 :=
  eqToHom (extension_eval D Sc cutoff N Λ β).symm ≫
    Superfunctor.whiskerRight (Superfunctor.whiskerLeft (extension D Sc cutoff N Λ β) η)
      (elvBlockEval D Sc cutoff N Λ β) ≫
        eqToHom (extension_eval D Sc cutoff N Λ β)

/-- The selected component of zero extension is canonically the original module. -/
theorem extension_obj (M : ContentModules D Sc cutoff N β.1) :
    ((extension D Sc cutoff N Λ β).obj M) β = M :=
  congrArg (fun F => F.obj M) (extension_eval D Sc cutoff N Λ β)

private def inclusion (M : ELVWeightProduct D Sc cutoff N Λ x) :
    (extension D Sc cutoff N Λ β).obj (M β) ⟶ M := fun δ =>
  if h : δ = β then by
    subst δ
    exact eqToHom (extension_obj D Sc cutoff N Λ β (M β))
  else 0

private theorem inclusion_mem (M : ELVWeightProduct D Sc cutoff N Λ x) :
    inclusion D Sc cutoff N Λ β M ∈ parity (R := k) _ _ 0 := by
  intro δ
  by_cases h : δ = β
  · subst δ
    simp only [inclusion, ↓reduceDIte]
    exact eqToHom_mem_parity_zero (extension_obj D Sc cutoff N Λ β (M β))
  · simp only [inclusion, dite_eq_right h]
    exact Submodule.zero_mem _

private theorem transport_app {A B : Type*} [Category A] [Preadditive A] [Linear k A]
    [Supercategory k A] [Category B] [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k A B} (h : F = G) (t : End F) (p : ZMod 2) (M : A) :
    (eqToHom h.symm ≫ t ≫ eqToHom h).app p M =
      eqToHom (congrArg (fun K => K.obj M) h.symm) ≫ t.app p M ≫
        eqToHom (congrArg (fun K => K.obj M) h) := by
  subst G
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem conjugate_of_square {C : Type*} [Category C] {A B : C}
    (e : A ≅ B) (f : End A) (g : End B) (h : e.hom ≫ g = f ≫ e.hom) :
    e.inv ≫ f ≫ e.hom = g := by
  rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- The exact-content centre agrees with the original whole-weight map on
its selected component for every input family, independently of other blocks. -/
theorem restrict_app (η : Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x) ⟶
    Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x))
    (p : ZMod 2) (M : ELVWeightProduct D Sc cutoff N Λ x) :
    (restrict D Sc cutoff N Λ β η).app p (M β) = η.app p M β := by
  have hn := congrArg (fun f => f β)
    (η.naturality p (inclusion D Sc cutoff N Λ β M) (inclusion_mem D Sc cutoff N Λ β M))
  change inclusion D Sc cutoff N Λ β M β ≫ η.app p M β =
    koszulSign p 0 • (η.app p ((extension D Sc cutoff N Λ β).obj (M β)) β ≫
      inclusion D Sc cutoff N Λ β M β) at hn
  simp only [inclusion, ↓reduceDIte, Supercategory.koszulSign_zero_right, one_smul] at hn
  unfold restrict
  rw [transport_app]
  change eqToHom (extension_obj D Sc cutoff N Λ β (M β)).symm ≫
    η.app p ((extension D Sc cutoff N Λ β).obj (M β)) β ≫
      eqToHom (extension_obj D Sc cutoff N Λ β (M β)) = _
  exact conjugate_of_square (eqToIso (extension_obj D Sc cutoff N Λ β (M β)))
    (η.app p ((extension D Sc cutoff N Λ β).obj (M β)) β) (η.app p M β) hn

/-- Both parity pieces agree, hence so does the full underlying module map. -/
theorem restrict_total (η : Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x) ⟶
    Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x))
    (M : ELVWeightProduct D Sc cutoff N Λ x) :
    (restrict D Sc cutoff N Λ β η).total (M β) = η.total M β := by
  change (restrict D Sc cutoff N Λ β η).app 0 (M β) +
    (restrict D Sc cutoff N Λ β η).app 1 (M β) = _
  rw [restrict_app, restrict_app]
  rfl

end OddMath.QuiverHecke.ELVOld.WeightCentreBlocks
