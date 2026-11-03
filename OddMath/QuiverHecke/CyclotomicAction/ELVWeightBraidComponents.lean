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

section Supported
variable (β : WeightBlocks D Λ x₀)
local notation "β₁" => blockSucc D Λ i h₁ β
local notation "β₂" => blockSucc₂ D i i Λ h₁ h₂ β
local notation "β₃" => elvBlockSucc₃ D i i i Λ h₁ h₂ h₃ β

/-- On a true triple successor, the first given crossing is induced from
its selected pair component, with the literal outer-coordinate casts. -/
theorem elvWeightBraidPrefix_blockSucc
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvWeightBraidPrefix D Sc cutoff bound i Λ h₁ h₂ h₃).total M β₃ =
      eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h₃ β₂ ((E₁ ≫ E₂).obj M)) ≫
        (elvBlockInd D Sc cutoff bound i Λ h₃ β₂).map
          ((elvWeightCrossVia D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ β β₂ rfl).app
            (D.parity i * D.parity i) M) ≫
          eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h₃ β₂ ((E₁ ≫ E₂).obj M)).symm := by
  have h₀ := elvWeightBraidPrefix_total D Sc cutoff bound i Λ h₁ h₂ h₃ M β₃
  have hm := elvInductionComponent_map_blockSucc D Sc cutoff bound i Λ h₃ β₂
    ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).total M)
  have hc := congrFun (supernatural_total_of_mem
    (elvActionCross_mem D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂) M) β₂
  have ha : (elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).app
      (D.parity i * D.parity i) M β₂ =
    elvWeightCrossComponent D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂
      (D.parity i * D.parity i) M β₂ := rfl
  have hv := elvWeightCrossComponent_of D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂
    (D.parity i * D.parity i) M β β₂ rfl
  have hx := hc.trans (ha.trans hv)
  have hr := congrArg
    (fun (f : (E₁ ≫ E₂).obj M β₂ ⟶ (E₁ ≫ E₂).obj M β₂) =>
      eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h₃ β₂ ((E₁ ≫ E₂).obj M)) ≫
        (elvBlockInd D Sc cutoff bound i Λ h₃ β₂).map f ≫
          eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h₃ β₂ ((E₁ ≫ E₂).obj M)).symm) hx
  have hfinal := h₀.trans (hm.trans hr)
  exact hfinal

/-- The last given crossing uses its true first-successor predecessor. -/
theorem elvWeightBraidSuffix_blockSucc
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvWeightBraidSuffix D Sc cutoff bound i Λ h₁ h₂ h₃).total M β₃ =
      (elvWeightCrossVia D Sc cutoff bound i i Λ h₂ h₃ h₂ h₃ β₁ β₃ rfl).app
        (D.parity i * D.parity i) ((elvEFunctor D Sc cutoff bound i Λ h₁).obj M) := by
  rw [elvWeightBraidSuffix_total]
  exact elvWeightCrossComponent_of D Sc cutoff bound i i Λ h₂ h₃ h₂ h₃
    (D.parity i * D.parity i) _ β₁ β₃ rfl
end Supported

end OddMath.QuiverHecke.ELVOld
