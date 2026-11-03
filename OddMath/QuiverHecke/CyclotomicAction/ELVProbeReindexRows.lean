import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexDot
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixRows

/-! # The chosen dotted unit and counit rows under probe reindexing

Brundan–Ellis (1.13)–(1.14): retain the actual adjunction rows through
the canonical append comparisons, at every dot exponent including zero.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u
attribute [local irreducible] oldAppendReindexIso oldAppendReindexLinear
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "cut" => probeCutoff D m
local notation "J₀" => oldContentAppendTo D Sc cut ν i (i :: ν) (List.Perm.refl _)
local notation "K₀" => oldContentAppendTo D Sc cut (i :: ν) i (i :: i :: ν) (List.Perm.refl _)
local notation "J" => oldContentAppendTo D Sc cut ν i ν₁ h₁
local notation "K" => oldContentAppendTo D Sc cut ν₁ i ν₂ h₂
local notation "R₁" => oldModuleReindex D Sc cut h₁
local notation "e₀" => oldAppendReindexIso D Sc cut (List.Perm.refl ν) i
  (List.Perm.refl (i :: ν)) h₁ h₁
local notation "e₁" => oldAppendReindexIso D Sc cut h₁ i
  (List.Perm.refl (i :: i :: ν)) h₂ (List.Perm.trans (List.Perm.cons i h₁) h₂)

/-- The selected lower comparison retains the literal counit. -/
theorem oldAppendReindexIso_cap
    (N : Superfunctor k (OldContentCategory D Sc cut (i :: ν)) (SVec k)) :
    (R₁).map ((adjunction J₀).counit.app N) =
      (e₀).hom.app ((restriction J₀).obj N) ≫
        (adjunction J).counit.app ((R₁).obj N) := by
  have h := oldAppendReindexIso_counit D Sc cut (List.Perm.refl ν) i
    (List.Perm.refl (i :: ν)) h₁ h₁ ((R₁).obj N)
  change (e₀).hom.app ((restriction J₀).obj N) ≫
      ((oldAppendReindexRightAdjunction D Sc cut (List.Perm.refl ν) i
        (List.Perm.refl (i :: ν)) h₁ h₁).counit.app ((R₁).obj N)) = _ at h
  simpa only [oldAppendReindexLeftAdjunction, oldAppendReindexRightAdjunction,
    Adjunction.comp_counit_app, oldModuleReindexAdjunction, oldModuleReindexEquivalence,
    Equivalence.toAdjunction_counit, Equivalence.counit, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Functor.map_id, Category.comp_id, Category.id_comp] using h.symm

/-- The selected upper comparison retains the literal unit. -/
theorem oldAppendReindexIso_unit_row
    (N : Superfunctor k (OldContentCategory D Sc cut (i :: ν)) (SVec k)) :
    (R₁).map ((adjunction K₀).unit.app N) ≫
      (restriction K).map ((e₁).hom.app N) =
        (adjunction K).unit.app ((R₁).obj N) := by
  have h := oldAppendReindexIso_unit D Sc cut h₁ i
    (List.Perm.refl (i :: i :: ν)) h₂ (List.Perm.trans (List.Perm.cons i h₁) h₂) N
  have hh := congrArg (R₁).map h
  simpa only [oldAppendReindexLeftAdjunction, oldAppendReindexRightAdjunction,
    Adjunction.comp_unit_app, oldModuleReindexAdjunction, oldModuleReindexEquivalence,
    Equivalence.toAdjunction_unit, Equivalence.unit, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Functor.map_id, Category.comp_id, Category.id_comp, Functor.map_comp] using hh
end OddMath.QuiverHecke
