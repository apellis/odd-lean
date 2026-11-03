import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToLocalFields
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexLocal

/-! # Whole reindexing on homogeneous module components

Brundan–Ellis (1.13)–(1.14): actual certificate reindexing retains all
components of whole natural transformations. The standard chosen mate is
formed from the original evaluated adjunctions and negative crossing.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {ν₁ : List I} (h₁ : (i :: ν).Perm ν₁)
local notation "cut" => probeCutoff D m
local notation "J₀" => oldContentAppendTo D Sc cut ν i (i :: ν) (List.Perm.refl _)
local notation "K₀" => oldContentAppendTo D Sc cut (i :: ν) i (i :: i :: ν) (List.Perm.refl _)
local notation "hγ₀" => oldAppendToEqualCross_supernatural D Sc cut ν i
  (List.Perm.refl (i :: ν)) (List.Perm.refl (i :: i :: ν))

/-- Certificate transport acts on each entire component by the original restriction. -/
theorem probeReindexLoopFunctor_app_hom
    {F G : Superfunctor k (ProbeEvaluatedModules D Sc m (i :: ν))
      (ProbeEvaluatedModules D Sc m (i :: ν))}
    (f : F ⟶ G) (q : ZMod 2) (N : ProbeEvaluatedModules D Sc m ν₁) :
    (((probeReindexLoopFunctor D Sc m ν i h₁).map f).app q N).hom =
      (oldModuleReindex D Sc cut h₁).map
        ((f.app q ((probeEvaluatedReindex D Sc m h₁.symm).obj N)).hom) := rfl

/-- The original evaluated negative crossing mate at standard consecutive contents. -/
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

/-- Reindexing a standard mate component retains its specified OLD map. -/
theorem mapped_probeEvaluatedLocalMate_app (q : ZMod 2)
    (M : ProbeEvaluatedModules D Sc m (i :: ν)) :
    (oldModuleReindex D Sc cut h₁).map (((probeEvaluatedLocalMate D Sc m ν i).app q M).hom) =
      (oldModuleReindex D Sc cut h₁).map
        ((SKM.rouquierMate (inductionModuleAdjunction (k := k) J₀)
          (inductionModuleAdjunction (k := k) K₀) (inductionModuleCross J₀ K₀ hγ₀)).app q M.obj) := by
  exact congrArg
    (fun f : induced J₀ ((restriction J₀).obj M.obj) ⟶
        (restriction K₀).obj (induced K₀ M.obj) => (oldModuleReindex D Sc cut h₁).map f)
    (probeEvaluatedLocalMate_app D Sc m ν i q M)
end OddMath.QuiverHecke
