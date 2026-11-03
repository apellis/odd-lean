import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexInduction
import OddMath.Algebra.HomogeneousSuperfunctorIso

/-! # The two local E/F loops under a probe representative change

Brundan–Ellis (1.13)–(1.14): the canonical even append adjunction
comparisons identify both local loops at arbitrary stored content lists.
The chosen append and restriction functors, with their original units and
counits, are retained in the comparison.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "reindex" => probeEvaluatedReindex D Sc m h₁
local notation "reindexInv" => probeEvaluatedReindex D Sc m h₁.symm
local notation "E₀" => probeEvaluatedInduction D Sc m ν i
local notation "F₀" => probeEvaluatedRestriction D Sc m ν i
local notation "E₁" => probeEvaluatedInduction D Sc m (i :: ν) i
local notation "F₁" => probeEvaluatedRestriction D Sc m (i :: ν) i
local notation "Ec₀" => probeEvaluatedAppendTo D Sc m ν i ν₁ h₁
local notation "Fc₀" => probeEvaluatedRestrictTo D Sc m ν i ν₁ h₁
local notation "Ec₁" => probeEvaluatedAppendTo D Sc m ν₁ i ν₂ h₂
local notation "Fc₁" => probeEvaluatedRestrictTo D Sc m ν₁ i ν₂ h₂

/-- The lower local loop comparison is the selected lower append comparison. -/
def probeReindexLowerLoopIso :
    reindexInv ⋙ (F₀ ⋙ E₀) ⋙ reindex ≅ Fc₀ ⋙ Ec₀ :=
  Functor.isoWhiskerLeft Fc₀
    (probeAppendReindexIso D Sc m (List.Perm.refl ν) i
      (List.Perm.refl (i :: ν)) h₁ h₁)

/-- The upper local loop comparison is the selected upper append comparison. -/
def probeReindexUpperLoopIso :
    reindexInv ⋙ (E₁ ⋙ F₁) ⋙ reindex ≅ Ec₁ ⋙ Fc₁ :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft reindexInv
      (probeAppendReindexIso D Sc m h₁ i (List.Perm.refl (i :: i :: ν)) h₂
        ((h₁.cons i).trans h₂))) Fc₁

theorem probeReindexLowerLoopIso_hom_mem (N : ProbeEvaluatedModules D Sc m ν₁) :
    (probeReindexLowerLoopIso D Sc m ν i h₁).hom.app N ∈ parity (R := k) _ _ 0 :=
  probeAppendReindexIso_hom_mem D Sc m (List.Perm.refl ν) i
    (List.Perm.refl (i :: ν)) h₁ h₁ ((Fc₀).obj N)

theorem probeReindexUpperLoopIso_hom_mem (N : ProbeEvaluatedModules D Sc m ν₁) :
    (probeReindexUpperLoopIso D Sc m ν i h₁ h₂).hom.app N ∈ parity (R := k) _ _ 0 :=
  Supercategory.map_mem Fc₁
    (probeAppendReindexIso_hom_mem D Sc m h₁ i (List.Perm.refl (i :: i :: ν)) h₂
      ((h₁.cons i).trans h₂) ((reindexInv).obj N))
end OddMath.QuiverHecke
