import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToLocalFields
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexLoopAction
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexLocal
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexLoopComponents
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

section NativeComponents
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hγ : IsSupernatural k p γ)
private theorem nativeMate_app (q : ZMod 2) (N : Superfunctor k A (SVec k)) :
    (SKM.rouquierMate (inductionModuleAdjunction (k := k) J)
      (inductionModuleAdjunction (k := k) K) (inductionModuleCross J K hγ)).app q N =
      if q = p then orderedGridMateComponent J K hγ N else 0 := by
  rw [inductionModuleMate_eq_grid]
  rfl
end NativeComponents

private theorem map_ite_square
    {C A : Type*} [Category* C] [Preadditive C] [Category* A] [Preadditive A]
    (R : C ⥤ A) [R.Additive] {X Y : C} {X' Y' : A}
    (f : X ⟶ Y) (g : X' ⟶ Y') (l : R.obj X ⟶ X') (u : R.obj Y ⟶ Y')
    (h : R.map f ≫ u = l ≫ g) (p q : ZMod 2) :
    R.map (if q = p then f else 0) ≫ u = l ≫ (if q = p then g else 0) := by
  split_ifs
  · exact h
  · rw [Functor.map_zero, Limits.zero_comp, Limits.comp_zero]

private theorem square_of_four_eq
    {C : Type*} [Category* C] {A B D E : C}
    {f f' : A ⟶ B} {u u' : B ⟶ E} {l l' : A ⟶ D} {g g' : D ⟶ E}
    (hf : f = f') (hu : u = u') (hl : l = l') (hg : g = g')
    (h : f' ≫ u' = l' ≫ g') : f ≫ u = l ≫ g := by
  rw [hf, hu, hl, hg]
  exact h

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

attribute [local irreducible] probeEvaluatedLocalMate

private theorem transportedMate_app (q : ZMod 2)
    (N : ProbeEvaluatedModules D Sc m ν₁) :
    (((probeReindexLoopFunctor D Sc m ν i h₁).map (probeEvaluatedLocalMate D Sc m ν i)).app q N).hom =
      (oldModuleReindex D Sc cut h₁).map
        ((SKM.rouquierMate (inductionModuleAdjunction (k := k) J₀)
          (inductionModuleAdjunction (k := k) K₀) (inductionModuleCross J₀ K₀ hγ₀)).app q
            ((reindexInv).obj N).obj) := by
  rw [probeReindexLoopFunctor_app_hom]
  exact mapped_probeEvaluatedLocalMate_app D Sc m ν i h₁ q
    ((probeEvaluatedReindex D Sc m h₁.symm).obj N)

private theorem native_mate_square (q : ZMod 2)
    (N : ProbeEvaluatedModules D Sc m ν₁) :
    (oldModuleReindex D Sc cut h₁).map
      ((SKM.rouquierMate (inductionModuleAdjunction (k := k) J₀)
        (inductionModuleAdjunction (k := k) K₀) (inductionModuleCross J₀ K₀ hγ₀)).app q
          ((reindexInv).obj N).obj) ≫
        oldReindexUpperLoopModuleHom D Sc cut ν i h₁ h₂ ((reindexInv).obj N).obj =
      oldReindexLowerLoopModuleHom D Sc cut ν i h₁ ((reindexInv).obj N).obj ≫
        (SKM.rouquierMate
          (inductionModuleAdjunction (k := k) (oldContentAppendTo D Sc cut ν i ν₁ h₁))
          (inductionModuleAdjunction (k := k) (oldContentAppendTo D Sc cut ν₁ i ν₂ h₂))
          (inductionModuleCross (oldContentAppendTo D Sc cut ν i ν₁ h₁)
            (oldContentAppendTo D Sc cut ν₁ i ν₂ h₂)
            (oldAppendToEqualCross_supernatural D Sc cut ν i h₁ h₂))).app q N.obj := by
  rw [nativeMate_app, nativeMate_app]
  exact map_ite_square (oldModuleReindex D Sc cut h₁) _ _ _ _
    (oldReindexLoopModuleHom_mate D Sc cut ν i h₁ h₂ ((reindexInv).obj N).obj) (D.parity i) q

private theorem mate_component_square (q : ZMod 2)
    (N : ProbeEvaluatedModules D Sc m ν₁) :
    (((probeReindexLoopFunctor D Sc m ν i h₁).map (probeEvaluatedLocalMate D Sc m ν i)).app q N).hom ≫
        (((upperIso).hom.total N).hom) =
      (((lowerIso).hom.total N).hom) ≫ ((probeAppendToMate D Sc m ν i h₁ h₂).app q N).hom := by
  exact square_of_four_eq
    (transportedMate_app D Sc m ν i h₁ q N)
    (probeReindexUpperLoopSuperIso_hom_total_native D Sc m ν i h₁ h₂ N)
    (probeReindexLowerLoopSuperIso_hom_total_native D Sc m ν i h₁ N)
    (probeAppendToMate_app D Sc m ν i h₁ h₂ q N)
    (native_mate_square D Sc m ν i h₁ h₂ q N)

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
