import OddMath.QuiverHecke.SwappedAssembly.SupportedSectors

/-! # Restriction of native superfunctors and generator transformations

The supported-action attachment of F4/(A1) in `SwappedActionAssembly.md`.
Full subcategory restriction keeps the literal included components of every
native supernatural transformation and preserves the operations in the
presentation. The canonical target inclusion, rather than a supplied
faithfulness premise, reflects equations between restricted arrows.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedRestriction
universe r u₁ v₁ u₂ v₂ u₃ v₃
variable {k : Type r} [CommRing k]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C] [Supercategory k C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear k D] [Supercategory k D]
  (P : ObjectProperty C) (Q : ObjectProperty D)

private def underlying (F : Superfunctor k C D) (hF : ∀ X, P X → Q (F.obj X)) :
    P.FullSubcategory ⥤ Q.FullSubcategory :=
  Q.lift (P.ι ⋙ F.toFunctor) (fun X => hF X.obj X.property)
private instance (F : Superfunctor k C D) (hF : ∀ X, P X → Q (F.obj X)) :
    (underlying P Q F hF).Additive where
  map_add := by intros; apply InducedCategory.hom_ext; exact F.toFunctor.map_add
private instance (F : Superfunctor k C D) (hF : ∀ X, P X → Q (F.obj X)) :
    (underlying P Q F hF).Linear k where
  map_smul := by intros; apply InducedCategory.hom_ext; exact F.toFunctor.map_smul _ _
private instance (F : Superfunctor k C D) (hF : ∀ X, P X → Q (F.obj X)) :
    IsSuperfunctor k (underlying P Q F hF) where
  map_mem hf := F.map_mem hf

/-- Restrict a native superfunctor whose object operation preserves the chosen subcategories. -/
def functor (F : Superfunctor k C D) (hF : ∀ X, P X → Q (F.obj X)) :
    Superfunctor k P.FullSubcategory Q.FullSubcategory := ⟨underlying P Q F hF⟩

/-- Inclusion of the restriction recovers the native functor on every supported object and map. -/
theorem functor_inclusion (F : Superfunctor k C D) (hF : ∀ X, P X → Q (F.obj X)) :
    (functor P Q F hF).toFunctor ⋙ Q.ι = P.ι ⋙ F.toFunctor := rfl

/-- Every native generator arrow restricts between its supported endpoints. -/
def transformation {F G : Superfunctor k C D}
    (hF : ∀ X, P X → Q (F.obj X)) (hG : ∀ X, P X → Q (G.obj X))
    (η : F ⟶ G) : functor P Q F hF ⟶ functor P Q G hG where
  app p X := ⟨η.app p X.obj⟩
  app_mem p X := η.app_mem p X.obj
  naturality := by
    intro p X Y q f hf
    exact InducedCategory.hom_ext (η.naturality p f.hom hf)

/-- Included components are literally the prescribed native generator components. -/
theorem transformation_app {F G : Superfunctor k C D}
    (hF : ∀ X, P X → Q (F.obj X)) (hG : ∀ X, P X → Q (G.obj X))
    (η : F ⟶ G) (p : ZMod 2) (X : P.FullSubcategory) :
    ((transformation P Q hF hG η).app p X).hom = η.app p X.obj := rfl

theorem transformation_mem {F G : Superfunctor k C D}
    (hF : ∀ X, P X → Q (F.obj X)) (hG : ∀ X, P X → Q (G.obj X))
    {η : F ⟶ G} {p : ZMod 2} (hη : η ∈ parity (R := k) _ _ p) :
    transformation P Q hF hG η ∈ parity (R := k) _ _ p := by
  rw [Superfunctor.mem_parity_iff] at hη ⊢
  funext X
  apply InducedCategory.hom_ext
  exact congrFun hη X.obj

/-- Restriction is linear on all native arrows, including odd ones. -/
def homLinear {F G : Superfunctor k C D}
    (hF : ∀ X, P X → Q (F.obj X)) (hG : ∀ X, P X → Q (G.obj X)) :
    (F ⟶ G) →ₗ[k] (functor P Q F hF ⟶ functor P Q G hG) where
  toFun := transformation P Q hF hG
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The native identity restricts to the identity. -/
theorem transformation_id (F : Superfunctor k C D) (hF : ∀ X, P X → Q (F.obj X)) :
    transformation P Q hF hF (𝟙 F) = 𝟙 (functor P Q F hF) := by
  apply Superfunctor.hom_ext_parity <;> intro X <;> apply InducedCategory.hom_ext <;> rfl

/-- Native vertical composition restricts to vertical composition. -/
theorem transformation_comp {F G H : Superfunctor k C D}
    (hF : ∀ X, P X → Q (F.obj X)) (hG : ∀ X, P X → Q (G.obj X))
    (hH : ∀ X, P X → Q (H.obj X)) (η : F ⟶ G) (θ : G ⟶ H) :
    transformation P Q hF hH (η ≫ θ) =
      transformation P Q hF hG η ≫ transformation P Q hG hH θ := by
  apply Superfunctor.hom_ext_parity <;> intro X <;> apply InducedCategory.hom_ext <;> rfl

/-- Equations of restricted arrows can be checked after the canonical full inclusion. -/
theorem hom_ext {F G : Superfunctor k P.FullSubcategory Q.FullSubcategory}
    {η θ : F ⟶ G} (h : ∀ p X, (η.app p X).hom = (θ.app p X).hom) : η = θ := by
  apply Superfunctor.hom_ext
  intro p X
  exact InducedCategory.hom_ext (h p X)

section Composition
variable {E : Type u₃} [Category.{v₃} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (R : ObjectProperty E)

theorem functor_comp (F : Superfunctor k C D) (G : Superfunctor k D E)
    (hF : ∀ X, P X → Q (F.obj X)) (hG : ∀ X, Q X → R (G.obj X)) :
    functor P R (F.comp G) (fun X hX => hG _ (hF X hX)) =
      (functor P Q F hF).comp (functor Q R G hG) := rfl

/-- Restriction commutes with a native left context. -/
theorem transformation_whiskerLeft (F : Superfunctor k C D) {G H : Superfunctor k D E}
    (hF : ∀ X, P X → Q (F.obj X)) (hG : ∀ X, Q X → R (G.obj X))
    (hH : ∀ X, Q X → R (H.obj X)) (η : G ⟶ H) :
    transformation P R (fun X hX => hG _ (hF X hX)) (fun X hX => hH _ (hF X hX))
      (Superfunctor.whiskerLeft F η) =
    Superfunctor.whiskerLeft (functor P Q F hF) (transformation Q R hG hH η) := by
  apply Superfunctor.hom_ext_parity <;> intro X <;> apply InducedCategory.hom_ext <;> rfl

/-- Restriction commutes with a native right context. -/
theorem transformation_whiskerRight {F G : Superfunctor k C D} (H : Superfunctor k D E)
    (hF : ∀ X, P X → Q (F.obj X)) (hG : ∀ X, P X → Q (G.obj X))
    (hH : ∀ X, Q X → R (H.obj X)) (η : F ⟶ G) :
    transformation P R (fun X hX => hH _ (hF X hX)) (fun X hX => hH _ (hG X hX))
      (Superfunctor.whiskerRight η H) =
    Superfunctor.whiskerRight (transformation P Q hF hG η) (functor Q R H hH) := by
  apply Superfunctor.hom_ext_parity <;> intro X <;> apply InducedCategory.hom_ext <;> rfl

end Composition
end OddMath.QuiverHecke.SwappedAssembly.SupportedRestriction
