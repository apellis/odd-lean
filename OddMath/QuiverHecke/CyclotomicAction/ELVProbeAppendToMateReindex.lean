import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToLocalFields
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexLocal
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexMateNatural

/-! # Reindexing the selected evaluated mate

Brundan–Ellis (1.13)–(1.14): the even loop comparisons retain the chosen
negative mate on evaluated modules. Component calculations keep the
selected ordinary adjunctions and all super parities.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
attribute [local irreducible] oldAppendReindexIso orderedGridMateComponent
section EvenComposition
variable {k C A : Type*} [CommRing k]
  [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category* A] [Preadditive A] [Linear k A] [Supercategory k A]
  {F G H : Superfunctor k C A}
private theorem comp_even_app (x : F ⟶ G) (η : G ⟶ H)
    (hη : η ∈ parity (R := k) _ _ 0) (q : ZMod 2) (N : C) :
    (x ≫ η).app q N = x.app q N ≫ η.total N := by
  rw [HomogeneousSuperfunctorIso.total_eq_app η hη N]
  have hz := Superfunctor.app_eq_zero_of_mem hη (q := 1) (by decide) N
  rcases parity_eq_zero_or_one q with rfl | rfl
  · change x.app 0 N ≫ η.app 0 N + x.app 1 N ≫ η.app 1 N = _
    rw [hz, Limits.comp_zero, add_zero]
  · change x.app 0 N ≫ η.app 1 N + x.app 1 N ≫ η.app 0 N = _
    rw [hz, Limits.comp_zero, zero_add]
private theorem even_comp_app (η : F ⟶ G) (hη : η ∈ parity (R := k) _ _ 0)
    (x : G ⟶ H) (q : ZMod 2) (N : C) :
    (η ≫ x).app q N = η.total N ≫ x.app q N := by
  rw [HomogeneousSuperfunctorIso.total_eq_app η hη N]
  have hz := Superfunctor.app_eq_zero_of_mem hη (q := 1) (by decide) N
  change η.app 0 N ≫ x.app q N + η.app 1 N ≫ x.app (q + 1) N = _
  rw [hz, Limits.zero_comp, add_zero]
private theorem full_square_of_even_components
    (P : ObjectProperty A) {F₀ F₁ F₂ F₃ : Superfunctor k C P.FullSubcategory}
    (f : F₀ ⟶ F₁) (u : F₁ ⟶ F₃) (l : F₀ ⟶ F₂) (g : F₂ ⟶ F₃)
    (hu : u ∈ parity (R := k) _ _ 0) (hl : l ∈ parity (R := k) _ _ 0)
    (h : ∀ q N, (f.app q N).hom ≫ (u.total N).hom =
      (l.total N).hom ≫ (g.app q N).hom) : f ≫ u = l ≫ g := by
  apply Superfunctor.hom_ext
  intro q N
  rw [comp_even_app f u hu, even_comp_app l hl g]
  apply InducedCategory.hom_ext
  exact h q N
end EvenComposition

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "cut" => probeCutoff D m
local notation "reindexInv" => probeEvaluatedReindex D Sc m h₁.symm
local notation "lowerIso" => probeReindexLowerLoopSuperIso D Sc m ν i h₁
local notation "upperIso" => probeReindexUpperLoopSuperIso D Sc m ν i h₁ h₂
local notation "J₀" => oldContentAppendTo D Sc cut ν i (i :: ν) (List.Perm.refl _)
local notation "K₀" => oldContentAppendTo D Sc cut (i :: ν) i (i :: i :: ν) (List.Perm.refl _)
local notation "hγ₀" => oldAppendToEqualCross_supernatural D Sc cut ν i
  (List.Perm.refl (i :: ν)) (List.Perm.refl (i :: i :: ν))

/-- Forgetting the evaluated lower comparison retains the selected OLD map. -/
theorem probeReindexLowerLoopSuperIso_hom_total_native
    (N : ProbeEvaluatedModules D Sc m ν₁) :
    ((lowerIso).hom.total N).hom = oldReindexLowerLoopModuleHom D Sc cut ν i h₁
      ((reindexInv).obj N).obj := by
  rw [probeReindexLowerLoopSuperIso_hom_total]
  unfold probeReindexLowerLoopIso oldReindexLowerLoopModuleHom
  rfl

/-- Forgetting the evaluated upper comparison retains the selected OLD map. -/
theorem probeReindexUpperLoopSuperIso_hom_total_native
    (N : ProbeEvaluatedModules D Sc m ν₁) :
    ((upperIso).hom.total N).hom = oldReindexUpperLoopModuleHom D Sc cut ν i h₁ h₂
      ((reindexInv).obj N).obj := by
  rw [probeReindexUpperLoopSuperIso_hom_total]
  unfold probeReindexUpperLoopIso oldReindexUpperLoopModuleHom
  rfl

def probeEvaluatedLocalMate :
    (⟨probeEvaluatedRestriction D Sc m ν i ⋙ probeEvaluatedInduction D Sc m ν i⟩ :
      Superfunctor k (ProbeEvaluatedModules D Sc m (i :: ν)) (ProbeEvaluatedModules D Sc m (i :: ν))) ⟶
    ⟨probeEvaluatedInduction D Sc m (i :: ν) i ⋙ probeEvaluatedRestriction D Sc m (i :: ν) i⟩ :=
  SKM.rouquierMate
    (probeEvaluatedRightAdjunction D Sc m ν i)
    (probeEvaluatedRightAdjunction D Sc m (i :: ν) i)
    (probeEvaluatedEqualCross D Sc m ν i)

theorem probeEvaluatedLocalMate_app (q : ZMod 2) (N : ProbeEvaluatedModules D Sc m (i :: ν)) :
    ((probeEvaluatedLocalMate D Sc m ν i).app q N).hom =
      (SKM.rouquierMate (inductionModuleAdjunction (k := k) J₀)
        (inductionModuleAdjunction (k := k) K₀) (inductionModuleCross J₀ K₀ hγ₀)).app q N.obj := by
  unfold probeEvaluatedLocalMate
  erw [SKM.rouquierMate_piscat_app, SKM.rouquierMate_piscat_app]
  rfl

attribute [local irreducible] probeEvaluatedLocalMate

private theorem mate_component_square (q : ZMod 2)
    (N : ProbeEvaluatedModules D Sc m ν₁) :
    (((probeReindexLoopFunctor D Sc m ν i h₁).map (probeEvaluatedLocalMate D Sc m ν i)).app q N).hom ≫
        (((upperIso).hom.total N).hom) =
      (((lowerIso).hom.total N).hom) ≫ ((probeAppendToMate D Sc m ν i h₁ h₂).app q N).hom := by
  change (oldModuleReindex D Sc cut h₁).map
      (((probeEvaluatedLocalMate D Sc m ν i).app q ((reindexInv).obj N)).hom) ≫
        (((upperIso).hom.total N).hom) =
    (((lowerIso).hom.total N).hom) ≫ ((probeAppendToMate D Sc m ν i h₁ h₂).app q N).hom
  rw [probeEvaluatedLocalMate_app, probeAppendToMate_app,
    probeReindexUpperLoopSuperIso_hom_total_native, probeReindexLowerLoopSuperIso_hom_total_native,
    inductionModuleMate_eq_grid, inductionModuleMate_eq_grid]
  change (oldModuleReindex D Sc cut h₁).map
      (if q = D.parity i then orderedGridMateComponent J₀ K₀ hγ₀ ((reindexInv).obj N).obj else 0) ≫
        oldReindexUpperLoopModuleHom D Sc cut ν i h₁ h₂ ((reindexInv).obj N).obj =
    oldReindexLowerLoopModuleHom D Sc cut ν i h₁ ((reindexInv).obj N).obj ≫
      (if q = D.parity i then
        orderedGridMateComponent (oldContentAppendTo D Sc cut ν i ν₁ h₁)
          (oldContentAppendTo D Sc cut ν₁ i ν₂ h₂)
          (oldAppendToEqualCross_supernatural D Sc cut ν i h₁ h₂) N.obj else 0)
  by_cases hq : q = D.parity i
  · rw [ite_eq_left hq, ite_eq_left hq]
    exact oldReindexLoopModuleHom_mate D Sc cut ν i h₁ h₂ ((reindexInv).obj N).obj
  · rw [ite_eq_right hq, ite_eq_right hq, Functor.map_zero, Limits.zero_comp, Limits.comp_zero]

/-- The selected evaluated mate follows the prescribed even loop comparisons. -/
theorem probeAppendToMate_reindex :
    (probeReindexLoopFunctor D Sc m ν i h₁).map (probeEvaluatedLocalMate D Sc m ν i) ≫ (upperIso).hom =
      (lowerIso).hom ≫ probeAppendToMate D Sc m ν i h₁ h₂ := by
  exact full_square_of_even_components (ProbeEvaluatesCoefficients D m Sc ν₁)
    ((probeReindexLoopFunctor D Sc m ν i h₁).map (probeEvaluatedLocalMate D Sc m ν i))
    (upperIso).hom (lowerIso).hom (probeAppendToMate D Sc m ν i h₁ h₂)
    (probeReindexUpperLoopSuperIso_hom_mem D Sc m ν i h₁ h₂)
    (probeReindexLowerLoopSuperIso_hom_mem D Sc m ν i h₁)
    (mate_component_square D Sc m ν i h₁ h₂)
end OddMath.QuiverHecke
