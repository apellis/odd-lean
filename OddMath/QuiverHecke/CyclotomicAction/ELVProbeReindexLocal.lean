import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedLocal
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexLoops
import OddMath.SKM.RouquierHomPostInverse
/-! # Coordinates of the evaluated local inverse under reindexing

Brundan–Ellis (1.13)–(1.14): reindex the selected finite inverse data by the
even lower and upper loop comparisons. These coordinate data retain all
old inverse entries; comparison with the chosen target mate and dotted
unit/counit rows is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u v w x y
section Generic
variable {k : Type u} [CommRing k] {C : Type v} {A : Type w}
  [Category.{x} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{y} A] [Preadditive A] [Linear k A] [Supercategory k A]
  (L : Superfunctor k A C) (R : Superfunctor k C A)
private def superEndReindex : Superfunctor k C C ⥤ Superfunctor k A A where
  obj F := L.comp (F.comp R)
  map f := Superfunctor.whiskerLeft L (Superfunctor.whiskerRight f R)
  map_id F := by rw [Superfunctor.id_whiskerRight, Superfunctor.whiskerLeft_id]
  map_comp f g := by rw [Superfunctor.comp_whiskerRight, Superfunctor.whiskerLeft_comp]
instance : (superEndReindex L R).Additive where
  map_add := by
    intro F G f g
    change Superfunctor.whiskerLeft L (Superfunctor.whiskerRight (f + g) R) = _
    rw [Superfunctor.add_whiskerRight, Superfunctor.whiskerLeft_add]
    rfl
instance : (superEndReindex L R).Linear k where
  map_smul f r := by
    change Superfunctor.whiskerLeft L (Superfunctor.whiskerRight (r • f) R) = _
    rw [Superfunctor.smul_whiskerRight, Superfunctor.whiskerLeft_smul]
    rfl
instance : IsSuperfunctor k (superEndReindex L R) where
  map_mem hf := Superfunctor.whiskerLeft_mem L (Superfunctor.whiskerRight_mem hf R)
private def evenNaturalIso {F G : Superfunctor k C A} (e : F.toFunctor ≅ G.toFunctor)
    (he : ∀ N, e.hom.app N ∈ parity (R := k) _ _ 0) : F ≅ G :=
  OddMath.HomogeneousSuperfunctorIso.ofComponents e.app
    (IsSupernatural.of_twist he (by
      intro N M f
      rw [twist_zero]
      exact e.hom.naturality f))
private theorem evenNaturalIso_hom_mem {F G : Superfunctor k C A}
    (e : F.toFunctor ≅ G.toFunctor) (he : ∀ N, e.hom.app N ∈ parity (R := k) _ _ 0) :
    (evenNaturalIso e he).hom ∈ parity (R := k) _ _ 0 :=
  OddMath.HomogeneousSuperfunctorIso.ofComponents_hom_mem e.app _

private theorem evenNaturalIso_hom_total {F G : Superfunctor k C A}
    (e : F.toFunctor ≅ G.toFunctor) (he : ∀ N, e.hom.app N ∈ parity (R := k) _ _ 0) (N : C) :
    (evenNaturalIso e he).hom.total N = e.hom.app N :=
  OddMath.HomogeneousSuperfunctorIso.ofComponents_hom_total e.app _ N

end Generic
open ELVOld ELVOld.BalancedInduction CyclotomicAction
section Probe
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "sourceCategory" => ProbeEvaluatedModules D Sc m (i :: ν)
local notation "targetCategory" => ProbeEvaluatedModules D Sc m ν₁
local notation "reindex" => probeEvaluatedReindex D Sc m h₁
local notation "reindexInv" => probeEvaluatedReindex D Sc m h₁.symm
private abbrev standardLowerLoop : Superfunctor k sourceCategory sourceCategory :=
  ⟨probeEvaluatedRestriction D Sc m ν i ⋙ probeEvaluatedInduction D Sc m ν i⟩
private abbrev standardUpperLoop : Superfunctor k sourceCategory sourceCategory :=
  ⟨probeEvaluatedInduction D Sc m (i :: ν) i ⋙ probeEvaluatedRestriction D Sc m (i :: ν) i⟩
private abbrev storedLowerLoop : Superfunctor k targetCategory targetCategory :=
  ⟨probeEvaluatedRestrictTo D Sc m ν i ν₁ h₁ ⋙ probeEvaluatedAppendTo D Sc m ν i ν₁ h₁⟩
private abbrev storedUpperLoop : Superfunctor k targetCategory targetCategory :=
  ⟨probeEvaluatedAppendTo D Sc m ν₁ i ν₂ h₂ ⋙ probeEvaluatedRestrictTo D Sc m ν₁ i ν₂ h₂⟩
local notation "oldLower" => standardLowerLoop D Sc m ν i
local notation "oldUpper" => standardUpperLoop D Sc m ν i
local notation "newLower" => storedLowerLoop D Sc m ν i h₁
local notation "newUpper" => storedUpperLoop D Sc m i h₂

/-- Reindex whole supernatural transformations of local endofunctors. -/
abbrev probeReindexLoopFunctor :
    Superfunctor k sourceCategory sourceCategory ⥤ Superfunctor k targetCategory targetCategory :=
  superEndReindex (⟨reindexInv⟩ : Superfunctor k targetCategory sourceCategory)
    (⟨reindex⟩ : Superfunctor k sourceCategory targetCategory)

/-- The selected lower loop comparison as an even superfunctor isomorphism. -/
def probeReindexLowerLoopSuperIso :
    (probeReindexLoopFunctor D Sc m ν i h₁).obj oldLower ≅ newLower :=
  evenNaturalIso (F := (probeReindexLoopFunctor D Sc m ν i h₁).obj oldLower)
    (G := newLower) (probeReindexLowerLoopIso D Sc m ν i h₁)
    (probeReindexLowerLoopIso_hom_mem D Sc m ν i h₁)

/-- The selected upper loop comparison as an even superfunctor isomorphism. -/
def probeReindexUpperLoopSuperIso :
    (probeReindexLoopFunctor D Sc m ν i h₁).obj oldUpper ≅ newUpper :=
  evenNaturalIso (F := (probeReindexLoopFunctor D Sc m ν i h₁).obj oldUpper)
    (G := newUpper) (probeReindexUpperLoopIso D Sc m ν i h₁ h₂)
    (probeReindexUpperLoopIso_hom_mem D Sc m ν i h₁ h₂)

/-- Certificate reindexing preserves the identity local loop strictly. -/
def probeReindexIdentityLoopIso :
    (probeReindexLoopFunctor D Sc m ν i h₁).obj (Superfunctor.id k sourceCategory) ≅
      Superfunctor.id k targetCategory := Iso.refl _

theorem probeReindexLowerLoopSuperIso_hom_mem :
    (probeReindexLowerLoopSuperIso D Sc m ν i h₁).hom ∈ parity (R := k) _ _ 0 :=
  evenNaturalIso_hom_mem (F := (probeReindexLoopFunctor D Sc m ν i h₁).obj oldLower)
    (G := newLower) (probeReindexLowerLoopIso D Sc m ν i h₁)
    (probeReindexLowerLoopIso_hom_mem D Sc m ν i h₁)

theorem probeReindexUpperLoopSuperIso_hom_mem :
    (probeReindexUpperLoopSuperIso D Sc m ν i h₁ h₂).hom ∈ parity (R := k) _ _ 0 :=
  evenNaturalIso_hom_mem (F := (probeReindexLoopFunctor D Sc m ν i h₁).obj oldUpper)
    (G := newUpper) (probeReindexUpperLoopIso D Sc m ν i h₁ h₂)
    (probeReindexUpperLoopIso_hom_mem D Sc m ν i h₁ h₂)

theorem probeReindexLowerLoopSuperIso_hom_total (N : targetCategory) :
    (probeReindexLowerLoopSuperIso D Sc m ν i h₁).hom.total N =
      (probeReindexLowerLoopIso D Sc m ν i h₁).hom.app N :=
  evenNaturalIso_hom_total (F := (probeReindexLoopFunctor D Sc m ν i h₁).obj oldLower)
    (G := newLower) (probeReindexLowerLoopIso D Sc m ν i h₁)
    (probeReindexLowerLoopIso_hom_mem D Sc m ν i h₁) N

theorem probeReindexUpperLoopSuperIso_hom_total (N : targetCategory) :
    (probeReindexUpperLoopSuperIso D Sc m ν i h₁ h₂).hom.total N =
      (probeReindexUpperLoopIso D Sc m ν i h₁ h₂).hom.app N :=
  evenNaturalIso_hom_total (F := (probeReindexLoopFunctor D Sc m ν i h₁).obj oldUpper)
    (G := newUpper) (probeReindexUpperLoopIso D Sc m ν i h₁ h₂)
    (probeReindexUpperLoopIso_hom_mem D Sc m ν i h₁ h₂) N

local notation "height" => -CyclotomicCrossingTensor.contentCrossingHeight
  D (probeCutoff D m) i ((i :: ν : List I) : Multiset I)

/-- Reindex every entry of the prescribed positive-height local inverse. -/
def probeReindexInvPos (hh : 0 ≤ height) :=
  ((probeEvaluatedLoc D Sc m ν i).invPos hh).mapCoordinates
    (probeReindexLoopFunctor D Sc m ν i h₁)
    (probeReindexLowerLoopSuperIso D Sc m ν i h₁).symm
    (probeReindexUpperLoopSuperIso D Sc m ν i h₁ h₂).symm
    (probeReindexIdentityLoopIso D Sc m ν i h₁).symm
    (inv_mem _ (probeReindexLowerLoopSuperIso_hom_mem D Sc m ν i h₁))
    (inv_mem _ (probeReindexUpperLoopSuperIso_hom_mem D Sc m ν i h₁ h₂))
    (id_mem _)

/-- Reindex every entry of the prescribed negative-height local inverse. -/
def probeReindexInvNeg (hh : height ≤ 0) :=
  ((probeEvaluatedLoc D Sc m ν i).invNeg hh).mapCoordinates
    (probeReindexLoopFunctor D Sc m ν i h₁)
    (probeReindexUpperLoopSuperIso D Sc m ν i h₁ h₂).symm
    (probeReindexLowerLoopSuperIso D Sc m ν i h₁).symm
    (probeReindexIdentityLoopIso D Sc m ν i h₁).symm
    (inv_mem _ (probeReindexUpperLoopSuperIso_hom_mem D Sc m ν i h₁ h₂))
    (inv_mem _ (probeReindexLowerLoopSuperIso_hom_mem D Sc m ν i h₁))
    (id_mem _)
end Probe
end OddMath.QuiverHecke
