import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexMate
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRouquierFields

/-! # The chosen mate comparison as an OLD module map

Brundan–Ellis (1.13)–(1.14): lift the single-coend reindexing square to
entire module maps. The two comparison maps remain the prescribed append
adjunction comparisons, and the crossing mate retains its negative sign.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u
attribute [local irreducible] oldAppendReindexLinear oldAppendReindexIso orderedGridMateLinear

private theorem restriction_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (t : C) :
    ((restriction Q).map f).total t = f.total (Q.obj t) := rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "J₀" => oldContentAppendTo D Sc cutoff ν i (i :: ν) (List.Perm.refl _)
local notation "K₀" => oldContentAppendTo D Sc cutoff (i :: ν) i (i :: i :: ν) (List.Perm.refl _)
local notation "J" => oldContentAppendTo D Sc cutoff ν i ν₁ h₁
local notation "K" => oldContentAppendTo D Sc cutoff ν₁ i ν₂ h₂
local notation "Q⁻¹" => oldContentReindex D Sc cutoff h₁.symm
local notation "R₁" => oldModuleReindex D Sc cutoff h₁
local notation "hγ₀" => oldAppendToEqualCross_supernatural D Sc cutoff ν i
  (List.Perm.refl (i :: ν)) (List.Perm.refl (i :: i :: ν))
local notation "hγ" => oldAppendToEqualCross_supernatural D Sc cutoff ν i h₁ h₂

/-- The lower loop map is the selected lower append comparison. -/
def oldReindexLowerLoopModuleHom
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (R₁).obj (induced J₀ ((restriction J₀).obj N)) ⟶
      induced J ((restriction J).obj ((R₁).obj N)) :=
  (oldAppendReindexIso D Sc cutoff (List.Perm.refl ν) i
    (List.Perm.refl (i :: ν)) h₁ h₁).hom.app ((restriction J₀).obj N)

/-- The upper loop map is the selected upper append comparison under restriction. -/
def oldReindexUpperLoopModuleHom
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (R₁).obj ((restriction K₀).obj (induced K₀ N)) ⟶
      (restriction K).obj (induced K ((R₁).obj N)) :=
  (restriction K).map
    ((oldAppendReindexIso D Sc cutoff h₁ i (List.Perm.refl (i :: i :: ν)) h₂
      ((h₁.cons i).trans h₂)).hom.app N)

theorem oldReindexLowerLoopModuleHom_total
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff ν₁) :
    (oldReindexLowerLoopModuleHom D Sc cutoff ν i h₁ N).total t =
      oldReindexLowerLoopLinear D Sc cutoff ν i h₁ N t := by
  unfold oldReindexLowerLoopModuleHom oldReindexLowerLoopLinear oldAppendReindexLinear
  rfl

theorem oldReindexUpperLoopModuleHom_total
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff ν₁) :
    (oldReindexUpperLoopModuleHom D Sc cutoff ν i h₁ h₂ N).total t =
      oldReindexUpperLoopLinear D Sc cutoff ν i h₁ h₂ N t := by
  unfold oldReindexUpperLoopModuleHom oldReindexUpperLoopLinear oldAppendReindexLinear
  rfl

/-- The same prescribed negative mate square on complete OLD module maps. -/
theorem oldReindexLoopModuleHom_mate
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (R₁).map (orderedGridMateComponent J₀ K₀ hγ₀ N) ≫
        oldReindexUpperLoopModuleHom D Sc cutoff ν i h₁ h₂ N =
      oldReindexLowerLoopModuleHom D Sc cutoff ν i h₁ N ≫
        orderedGridMateComponent J K hγ ((R₁).obj N) := by
  let V := (R₁).obj (induced J₀ ((restriction J₀).obj N))
  let W := (restriction K).obj (induced K ((R₁).obj N))
  apply HomogeneousSuperfunctorIso.total_ext (F := V) (G := W)
  intro t
  rw [Superfunctor.comp_total, Superfunctor.comp_total,
    oldReindexLowerLoopModuleHom_total, oldReindexUpperLoopModuleHom_total]
  change oldReindexUpperLoopLinear D Sc cutoff ν i h₁ h₂ N t ∘ₗ
      ((restriction Q⁻¹).map (orderedGridMateComponent J₀ K₀ hγ₀ N)).total t =
    (orderedGridMateComponent J K hγ ((R₁).obj N)).total t ∘ₗ
      oldReindexLowerLoopLinear D Sc cutoff ν i h₁ N t
  rw [restriction_total]
  have h := oldReindexLoopLinear_mate D Sc cutoff ν i h₁ h₂ N t
  unfold orderedGridMateLinear at h
  exact h
end OddMath.QuiverHecke
