import OddMath.QuiverHecke.CyclotomicAction.ELVPostCoefficientEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedDenominatorUnits

/-! # Output bounds in the prescribed shifted ELV summand

`SwappedHomInversion.md` §3 (2)–(3): evaluate the actual content-shifted
postdot at an input and reservoir block. The nilpotence exponent belongs
to that component, without a common bound on the whole weight fibre.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicAction
universe u

private def productPiEndComponent {k J : Type u} [CommRing k]
    (C : J → Type (u + 1)) [∀ j, Category.{u} (C j)] [∀ j, Preadditive (C j)]
    [∀ j, Linear k (C j)] [∀ j, Supercategory k (C j)] [∀ j, PiSupercategory k (C j)]
    (M : ∀ j, C j) (j : J) :
    letI := productPiSupercategory (k := k) C
    End (M j) →+* End ((PiSupercategory.pi (R := k) (C := ∀ j, C j)).obj M j) := by
  letI := productPiSupercategory (k := k) C
  let e : ((PiSupercategory.pi (R := k) (C := ∀ j, C j)).obj M j) ≅ M j :=
    { hom := (PiSupercategory.ζ (R := k) M).hom j
      inv := (PiSupercategory.ζ (R := k) M).inv j
      hom_inv_id := congrArg (fun f => f j) (PiSupercategory.ζ (R := k) M).hom_inv_id
      inv_hom_id := congrArg (fun f => f j) (PiSupercategory.ζ (R := k) M).inv_hom_id }
  exact
    { toFun := fun f => e.hom ≫ twist k 1 f ≫ e.inv
      map_zero' := by
        change e.hom ≫ twist k 1 (0 : End (M j)) ≫ e.inv = 0
        rw [map_zero, Limits.zero_comp, Limits.comp_zero]
      map_one' := by
        change e.hom ≫ twist k 1 (𝟙 (M j)) ≫ e.inv = 𝟙 _
        rw [twist_id, Category.id_comp, Iso.hom_inv_id]
      map_add' := by
        intro f g
        change e.hom ≫ twist k 1 (f + g) ≫ e.inv =
          (e.hom ≫ twist k 1 f ≫ e.inv) + (e.hom ≫ twist k 1 g ≫ e.inv)
        rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
      map_mul' := by
        intro f g
        change e.hom ≫ twist k 1 (g ≫ f) ≫ e.inv =
          (e.hom ≫ twist k 1 g ≫ e.inv) ≫ (e.hom ≫ twist k 1 f ≫ e.inv)
        simp only [twist_comp, Category.assoc, Iso.inv_hom_id_assoc] }

private theorem productPi_map_component {k J : Type u} [CommRing k]
    (C : J → Type (u + 1)) [∀ j, Category.{u} (C j)] [∀ j, Preadditive (C j)]
    [∀ j, Linear k (C j)] [∀ j, Supercategory k (C j)] [∀ j, PiSupercategory k (C j)]
    (M : ∀ j, C j) (f : End M) (j : J) :
    letI := productPiSupercategory (k := k) C
    ((PiSupercategory.pi (R := k) (C := ∀ j, C j)).map f) j =
      productPiEndComponent (k := k) C M j (f j) := by
  let _ := productPiSupercategory (k := k) C
  rw [PiSupercategory.pi_map_eq]
  change (PiSupercategory.ζ (R := k) M).hom j ≫ (twist k 1 f) j ≫
      (PiSupercategory.ζ (R := k) M).inv j =
    (PiSupercategory.ζ (R := k) M).hom j ≫ twist k 1 (f j) ≫
      (PiSupercategory.ζ (R := k) M).inv j
  have ht : (twist k 1 f) j = twist k 1 (f j) :=
    map_twist (R := k) (Pi.eval C j) 1 f
  rw [ht]

local instance shiftedCoefficientHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u, u, u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  {A : PiSCat.{u,u,u + 1} k} (F : A ⟶ elvWeightSpace D Sc cutoff bound Λ x)
local notation "G" => elvPostInduction D Sc cutoff bound i Λ h F
local notation "Gs" κ => elvShiftedPostInduction D Sc cutoff bound i Λ h F κ
local notation "Ys" κ => elvShiftedPostDot D Sc cutoff bound i Λ h F κ

/-- Total evaluation on the shifted functor followed by the actual reservoir block. -/
def elvShiftedPostEndEvaluation (κ : ZMod 2) (M : A) (δ : WeightBlocks D Λ y) :
    End (Gs κ) →ₐ[k] End (((Gs κ).obj M) δ) :=
  (piEndEvaluation ((Gs κ).obj M) δ).comp (supernaturalEndEvaluation (Gs κ) M)

/-- With no shift the evaluation is the original literal component projection. -/
theorem elvShiftedPostEndEvaluation_zero (M : A) (δ : WeightBlocks D Λ y) (f : End G) :
    elvShiftedPostEndEvaluation D Sc cutoff bound i Λ h F 0 M δ
      (elvShiftedPostEnd D Sc cutoff bound i Λ h F f 0) =
    elvPostEndEvaluation D Sc cutoff bound i Λ h F M δ f := by
  rfl

/-- The odd shift acts by the actual product parity chart at this output block. -/
theorem elvShiftedPostEndEvaluation_one (M : A) (δ : WeightBlocks D Λ y) (f : End G) :
    elvShiftedPostEndEvaluation D Sc cutoff bound i Λ h F 1 M δ
      (elvShiftedPostEnd D Sc cutoff bound i Λ h F f 1) =
    productPiEndComponent (k := k) (fun β : WeightBlocks D Λ y => ContentModules D Sc cutoff bound β.1)
      ((G).obj M) δ (elvPostEndEvaluation D Sc cutoff bound i Λ h F M δ f) := by
  let _ := elvWeightPi D Sc cutoff bound Λ y
  change (((PiSupercategory.pi (R := k) (C := ELVWeightProduct D Sc cutoff bound Λ y)).map
    (f.app 0 M)) δ +
    ((PiSupercategory.pi (R := k) (C := ELVWeightProduct D Sc cutoff bound Λ y)).map
      (f.app 1 M)) δ) = _
  rw [productPi_map_component, productPi_map_component]
  exact (map_add (productPiEndComponent (k := k)
    (fun β : WeightBlocks D Λ y => ContentModules D Sc cutoff bound β.1) ((G).obj M) δ)
    (f.app 0 M δ) (f.app 1 M δ)).symm

/-- The chosen content shift preserves the already proved local reservoir-dot bound. -/
theorem elvShiftedPostEndEvaluation_dot_isNilpotent [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound)
    (κ : ZMod 2) (M : A) (δ : WeightBlocks D Λ y) :
    IsNilpotent (elvShiftedPostEndEvaluation D Sc cutoff bound i Λ h F κ M δ (Ys κ)) := by
  rcases parity_eq_zero_or_one κ with rfl | rfl
  · rw [elvShiftedPostDot, elvShiftedPostEndEvaluation_zero]
    exact elvPostEndEvaluation_dot_isNilpotent D Sc cutoff bound i Λ h F hdot M δ
  · rw [elvShiftedPostDot, elvShiftedPostEndEvaluation_one]
    exact (elvPostEndEvaluation_dot_isNilpotent D Sc cutoff bound i Λ h F hdot M δ).map
      (productPiEndComponent (k := k) (fun β : WeightBlocks D Λ y => ContentModules D Sc cutoff bound β.1)
        ((G).obj M) δ)

end OddMath.QuiverHecke.ELVOld
