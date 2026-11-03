import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTripleComparisonCoherence
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierData

/-! # Components of the prescribed original-weight braid crossings

Brundan--Ellis (1.9), DeformedActionAssembly §6. Evaluate the two literal
crossing whiskerings on the actual three weight inductions, retaining the
associator and the selected predecessor-coordinate maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
universe u
section Total
variable {k : Type u} [CommRing k]
private theorem braid_total_whiskerRight
    {A B C : PiSCat.{u, u, u + 1} k} {F G : A ⟶ B}
    (f : F ⟶ G) (H : B ⟶ C) (M : A) :
    (f ▷ H).total M = H.map (f.total M) := by
  change H.map (f.app 0 M) + H.map (f.app 1 M) = H.map (f.app 0 M + f.app 1 M)
  exact H.toFunctor.map_add.symm
private theorem reassociated_prefix_total
    {A B C E : PiSCat.{u, u, u + 1} k}
    (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ E) (x : F ≫ G ⟶ F ≫ G) (M : A) :
    ((associator F G H).inv ≫ x ▷ H ≫ (associator F G H).hom).total M = H.map (x.total M) := by
  erw [PiSCat.associator_inv, PiSCat.associator_hom, Category.id_comp, Category.comp_id]
  exact braid_total_whiskerRight x H M
end Total

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂) (h₃ : x₂ + D.α i = x₃)
local notation "E₁" => elvE D Sc cutoff bound i Λ h₁
local notation "E₂" => elvE D Sc cutoff bound i Λ h₂
local notation "E₃" => elvE D Sc cutoff bound i Λ h₃

/-- The first given pair crossing, in the right-associated triple source. -/
abbrev elvWeightBraidPrefix : E₁ ≫ E₂ ≫ E₃ ⟶ E₁ ≫ E₂ ≫ E₃ :=
  (associator E₁ E₂ E₃).inv ≫
    elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom
/-- The second given pair crossing, after the first weight induction. -/
abbrev elvWeightBraidSuffix : E₁ ≫ E₂ ≫ E₃ ⟶ E₁ ≫ E₂ ≫ E₃ :=
  E₁ ◁ elvActionCross D Sc cutoff bound i i Λ h₂ h₃ h₂ h₃

/-- The actual prefix whiskering is the selected outer induction map. -/
theorem elvWeightBraidPrefix_total
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) (ε : WeightBlocks D Λ x₃) :
    (elvWeightBraidPrefix D Sc cutoff bound i Λ h₁ h₂ h₃).total M ε =
      (elvInductionComponent D Sc cutoff bound i Λ h₃ ε).map
        ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).total M) :=
  congrFun (reassociated_prefix_total E₁ E₂ E₃
    (elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂) M) ε

/-- The actual suffix whiskering uses the prescribed crossing component
on the actual first weight-induced product, including absent sectors. -/
theorem elvWeightBraidSuffix_total
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) (ε : WeightBlocks D Λ x₃) :
    (elvWeightBraidSuffix D Sc cutoff bound i Λ h₁ h₂ h₃).total M ε =
      elvWeightCrossComponent D Sc cutoff bound i i Λ h₂ h₃ h₂ h₃
        (D.parity i * D.parity i) ((elvEFunctor D Sc cutoff bound i Λ h₁).obj M) ε :=
  congrFun (supernatural_total_of_mem
    (elvActionCross_mem D Sc cutoff bound i i Λ h₂ h₃ h₂ h₃) ((E₁).obj M)) ε

end OddMath.QuiverHecke.ELVOld
