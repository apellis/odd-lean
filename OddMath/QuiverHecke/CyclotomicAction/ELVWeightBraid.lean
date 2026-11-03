import OddMath.QuiverHecke.CyclotomicAction.ELVWeightBraidSuffixComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentInductionBraid

/-! # The prescribed same-colour braid on the weight action

Brundan--Ellis (1.9), the same-colour braid field of `SKM.RouquierFamily`.
Both given crossing whiskerings intertwine through the same selected
triple chart; the direct normalized content braid therefore transports.
Absent predecessor sectors are handled by the actual zero-module support
statement. No crossing-compatibility or invertibility premise is added.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem intertwine_product
    {C : Type*} [Category* C] {X Y : C} (e : X ⟶ Y)
    (l r : End X) (a b : End Y)
    (hl : l ≫ e = e ≫ a) (hr : r ≫ e = e ≫ b) :
    (l ≫ r) ≫ e = e ≫ (a ≫ b) := by
  rw [Category.assoc, hr, ← Category.assoc, hl, Category.assoc]
private theorem braid_of_comparison
    {C : Type*} [Category* C] {X Y : C} (e : X ≅ Y)
    (l r : End X) (a b : End Y)
    (hl : l ≫ e.hom = e.hom ≫ a) (hr : r ≫ e.hom = e.hom ≫ b)
    (hb : b ≫ a ≫ b = a ≫ b ≫ a) :
    r ≫ l ≫ r = l ≫ r ≫ l := by
  have hleft := intertwine_product e.hom r (l ≫ r) b (a ≫ b) hr
    (intertwine_product e.hom l r a b hl hr)
  have hright := intertwine_product e.hom l (r ≫ l) a (b ≫ a) hl
    (intertwine_product e.hom r l b a hr hl)
  exact (cancel_mono e.hom).1
    (hleft.trans ((congrArg (fun z => e.hom ≫ z) hb).trans hright.symm))
private theorem braid_total_three
    {k : Type u} [CommRing k] {A B : PiSCat.{u, u, u + 1} k}
    (F : A ⟶ B) (f g h : End F) (M : A) :
    (f ≫ g ≫ h).total M = f.total M ≫ g.total M ≫ h.total M := by
  rw [Superfunctor.comp_total, Superfunctor.comp_total]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂) (h₃ : x₂ + D.α i = x₃)
local notation "E₁" => elvE D Sc cutoff bound i Λ h₁
local notation "E₂" => elvE D Sc cutoff bound i Λ h₂
local notation "E₃" => elvE D Sc cutoff bound i Λ h₃
local notation "t₁" => elvWeightBraidPrefix D Sc cutoff bound i Λ h₁ h₂ h₃
local notation "t₂" => elvWeightBraidSuffix D Sc cutoff bound i Λ h₁ h₂ h₃

/-- The literal given same-colour weight crossings satisfy the braid,
on all product modules and all output blocks, including absent sectors. -/
theorem elvActionCross_braid : t₂ ≫ t₁ ≫ t₂ = t₁ ≫ t₂ ≫ t₁ := by
  apply supernatural_hom_ext_total
  intro M
  funext ε
  have hL := congrFun (braid_total_three (E₁ ≫ E₂ ≫ E₃) t₂ t₁ t₂ M) ε
  have hR := congrFun (braid_total_three (E₁ ≫ E₂ ≫ E₃) t₁ t₂ t₁ M) ε
  by_cases hs : ∃ β, elvBlockSucc₃ D i i i Λ h₁ h₂ h₃ β = ε
  · obtain ⟨β, rfl⟩ := hs
    have hb := contentInduction_sameColour_braid D Sc cutoff bound β.1 i _
      (elvBlockTriple_content_eq D i i i Λ h₁ h₂ h₃ β) (M β)
    have hm := braid_of_comparison
      ((elvWeightTripleComparison D Sc cutoff bound i i i Λ h₁ h₂ h₃ β _ rfl).app M)
      ((t₁).total M (elvBlockSucc₃ D i i i Λ h₁ h₂ h₃ β))
      ((t₂).total M (elvBlockSucc₃ D i i i Λ h₁ h₂ h₃ β))
      ((contentInductionTransform D Sc cutoff bound
        (elvBlockTriple_content_eq D i i i Λ h₁ h₂ h₃ β)
        (elvBlockTriple_content_eq D i i i Λ h₁ h₂ h₃ β)
        (contentNormalizedLeft_mem D Sc i i i)).app (D.parity i * D.parity i) (M β))
      ((contentInductionTransform D Sc cutoff bound
        (elvBlockTriple_content_eq D i i i Λ h₁ h₂ h₃ β)
        (elvBlockTriple_content_eq D i i i Λ h₁ h₂ h₃ β)
        (contentNormalizedRight_mem D Sc i i i)).app (D.parity i * D.parity i) (M β))
      (elvWeightBraidPrefix_comparison D Sc cutoff bound i Λ h₁ h₂ h₃ β M)
      (elvWeightBraidSuffix_comparison D Sc cutoff bound i Λ h₁ h₂ h₃ β M) hb
    exact hL.trans (hm.trans hR.symm)
  · have hz := elvEFunctor_comp₃_isZero D Sc cutoff bound i i i Λ h₁ h₂ h₃ ε hs M
    exact hL.trans ((hz.eq_of_src _ _).trans hR.symm)

/-- This is exactly the same-colour braid field for the independently
chosen `elvRouquierData`, with its prescribed associators and crossings. -/
theorem elvRouquierData_braid :
    let R := elvRouquierData D Sc cutoff bound Λ
    let a := (associator (R.E i h₁) (R.E i h₂) (R.E i h₃)).inv ≫
      R.cross i i h₁ h₂ h₁ h₂ ▷ R.E i h₃ ≫
      (associator (R.E i h₁) (R.E i h₂) (R.E i h₃)).hom
    let b := R.E i h₁ ◁ R.cross i i h₂ h₃ h₂ h₃
    b ≫ a ≫ b = a ≫ b ≫ a :=
  elvActionCross_braid D Sc cutoff bound i Λ h₁ h₂ h₃

end OddMath.QuiverHecke.ELVOld
