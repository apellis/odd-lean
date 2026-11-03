import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTriplePairComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleWhiskering

/-! # Comparison of the prescribed weight braid crossings

Brundan--Ellis (1.9), DeformedActionAssembly §6. Compare the given
whiskered weight crossings through the same selected triple-induction
chart, retaining the normalized equal-colour affine crossing.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem braid_prefix_comparison
    {C B : Type*} [Category* C] [Category* B]
    (F : B ⥤ C) {A P : B} {X W : C}
    (d : X ≅ F.obj A) (e : A ≅ P) (w : F.obj P ≅ W)
    (t : X ≅ W) (x : A ⟶ A) (y : X ⟶ X) (c : P ⟶ P) (z : W ⟶ W)
    (hx : x = e.hom ≫ c ≫ e.inv)
    (hy : y = d.hom ≫ F.map x ≫ d.inv)
    (ht : t.hom = d.hom ≫ F.map e.hom ≫ w.hom)
    (hc : F.map c ≫ w.hom = w.hom ≫ z) :
    y ≫ t.hom = t.hom ≫ z := by
  have he : F.map e.inv ≫ F.map e.hom = 𝟙 _ := by
    rw [← F.map_comp, e.inv_hom_id, F.map_id]
  calc
    y ≫ t.hom = d.hom ≫ F.map e.hom ≫ F.map c ≫ w.hom := by
      simp only [hy, ht, hx, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc (F.map e.inv), he, Category.id_comp]
    _ = t.hom ≫ z := by rw [hc, ht]; simp only [Category.assoc]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂) (h₃ : x₂ + D.α i = x₃)
  (β : WeightBlocks D Λ x₀)
local notation "β₁" => blockSucc D Λ i h₁ β
local notation "β₂" => blockSucc₂ D i i Λ h₁ h₂ β
local notation "β₃" => elvBlockSucc₃ D i i i Λ h₁ h₂ h₃ β
local notation "p" => D.parity i * D.parity i
local notation "hT" => elvBlockTriple_content_eq D i i i Λ h₁ h₂ h₃ β
local notation "hP" => elvBlockPair_content_eq D i i Λ h₁ h₂ β
local notation "h₃c" => elvBlockSucc_content_eq D i Λ h₃ β₂
local notation "C₃" => elvWeightTripleComparison D Sc cutoff bound i i i Λ h₁ h₂ h₃ β β₃ rfl
local notation "C₂" => elvWeightPairComparison D Sc cutoff bound i i Λ h₁ h₂ β β₂ rfl
local notation "L" => contentInductionCompTo D Sc cutoff bound (Subtype.val β) [i,i] (Subtype.val β₂)
  hP [i] (Subtype.val β₃) h₃c hT

/-- The literal prefix crossing intertwines with the normalized affine
prefix through the selected triple chart. -/
theorem elvWeightBraidPrefix_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvWeightBraidPrefix D Sc cutoff bound i Λ h₁ h₂ h₃).total M β₃ ≫ (C₃).hom.app M =
      (C₃).hom.app M ≫
        (contentInductionTransform D Sc cutoff bound hT hT
          (contentTriplePrefixAffine_mem D Sc i i i)).app p (M β) := by
  apply braid_prefix_comparison
    (elvBlockInd D Sc cutoff bound i Λ h₃ β₂).toFunctor
    ((eqToIso (elvEFunctor_comp₃_pairFirst D Sc cutoff bound i i i Λ h₁ h₂ h₃ β)).app M)
    ((C₂).app M) ((L).app (M β)) ((C₃).app M)
    ((elvWeightCrossVia D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ β β₂ rfl).app p M)
    _ ((contentInductionTransform D Sc cutoff bound hP hP (contentCrossAffine_mem D Sc i i)).app p (M β)) _
  · simpa only [Iso.app_hom, Iso.app_inv, Category.assoc] using
      elvWeightCrossVia_component D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ β β₂ rfl M
  · simp only [Iso.app_hom, Iso.app_inv, eqToIso.hom, eqToIso.inv, eqToHom_app]
    exact elvWeightBraidPrefix_blockSucc D Sc cutoff bound i Λ h₁ h₂ h₃ β M
  · exact elvWeightTripleComparison_pairFirst_hom D Sc cutoff bound i i i Λ h₁ h₂ h₃ β M
  · exact contentInductionCompTo_inner_map_of_eq D Sc cutoff bound β.1 [i,i] [i,i] β₂.1
      hP hP [i] β₃.1 h₃c hT hT (contentCrossAffine_mem D Sc i i)
      (contentTriplePrefixAffine_mem D Sc i i i) (contentTriplePrefixAffine_eq_whisker D Sc i i i) (M β)

end OddMath.QuiverHecke.ELVOld
