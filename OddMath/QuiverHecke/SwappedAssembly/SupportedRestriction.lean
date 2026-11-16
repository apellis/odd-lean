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

/-- Every native generator arrow restricts between its supported endpoints. -/
def transformation {F G : Superfunctor k C D}
    (hF : ∀ X, P X → Q (F.obj X)) (hG : ∀ X, P X → Q (G.obj X))
    (η : F ⟶ G) : functor P Q F hF ⟶ functor P Q G hG where
  app p X := ⟨η.app p X.obj⟩
  app_mem p X := η.app_mem p X.obj
  naturality := by
    intro p X Y q f hf
    exact InducedCategory.hom_ext (η.naturality p f.hom hf)

/-- Equations of restricted arrows can be checked after the canonical full inclusion. -/
theorem hom_ext {F G : Superfunctor k P.FullSubcategory Q.FullSubcategory}
    {η θ : F ⟶ G} (h : ∀ p X, (η.app p X).hom = (θ.app p X).hom) : η = θ := by
  apply Superfunctor.hom_ext
  intro p X
  exact InducedCategory.hom_ext (h p X)

section Composition
variable {E : Type u₃} [Category.{v₃} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (R : ObjectProperty E)

end Composition
end OddMath.QuiverHecke.SwappedAssembly.SupportedRestriction
