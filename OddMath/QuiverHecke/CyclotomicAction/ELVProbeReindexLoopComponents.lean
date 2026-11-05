import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexLocal
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexMateNatural

/-! # Components of the chosen evaluated loop comparisons

Brundan–Ellis (1.13)–(1.14): the even lower and upper loop comparisons
retain their prescribed OLD module maps after forgetting only scalar
evaluation certificates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
attribute [local irreducible] oldAppendReindexIso
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "cut" => probeCutoff D m
local notation "reindexInv" => probeEvaluatedReindex D Sc m h₁.symm
local notation "lowerIso" => probeReindexLowerLoopSuperIso D Sc m ν i h₁
local notation "upperIso" => probeReindexUpperLoopSuperIso D Sc m ν i h₁ h₂

/-- Forgetting the evaluated lower comparison retains the selected OLD map. -/
theorem probeReindexLowerLoopSuperIso_hom_total_eq
    (N : ProbeEvaluatedModules D Sc m ν₁) :
    ((lowerIso).hom.total N).hom = oldReindexLowerLoopModuleHom D Sc cut ν i h₁
      ((reindexInv).obj N).obj := by
  rw [probeReindexLowerLoopSuperIso_hom_total]
  unfold probeReindexLowerLoopIso oldReindexLowerLoopModuleHom
  rfl

/-- Forgetting the evaluated upper comparison retains the selected OLD map. -/
theorem probeReindexUpperLoopSuperIso_hom_total_eq
    (N : ProbeEvaluatedModules D Sc m ν₁) :
    ((upperIso).hom.total N).hom = oldReindexUpperLoopModuleHom D Sc cut ν i h₁ h₂
      ((reindexInv).obj N).obj := by
  rw [probeReindexUpperLoopSuperIso_hom_total]
  unfold probeReindexUpperLoopIso oldReindexUpperLoopModuleHom
  rfl

end OddMath.QuiverHecke
