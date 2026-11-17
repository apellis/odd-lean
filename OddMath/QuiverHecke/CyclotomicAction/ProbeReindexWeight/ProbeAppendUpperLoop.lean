import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexWeight.ProbeMissingCoefficients
import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexWeight.ProbeReindexDot

/-!
# Probe reindex weight

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The single upper loop at an arbitrary stored probe representative

Brundan–Ellis (1.13)–(1.14): the even append comparison identifies the
upper loop and every prescribed dotted unit column without assuming a
lower predecessor. This is the chart needed at a missing-colour boundary.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u
attribute [local irreducible] oldAppendReindexIso
section Generic
variable {k C B : Type*} [CommRing k]
  [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category B] [Preadditive B] [Linear k B] [Supercategory k B]
  {F G : Superfunctor k C B}
private def evenNaturalIso (e : F.toFunctor ≅ G.toFunctor)
    (he : ∀ N, e.hom.app N ∈ parity (R := k) _ _ 0) : F ≅ G :=
  HomogeneousSuperfunctorIso.ofComponents e.app
    (IsSupernatural.of_twist he (by
      intro N M f
      rw [twist_zero]
      exact e.hom.naturality f))
private theorem evenNaturalIso_hom_mem (e : F.toFunctor ≅ G.toFunctor)
    (he : ∀ N, e.hom.app N ∈ parity (R := k) _ _ 0) :
    (evenNaturalIso e he).hom ∈ parity (R := k) _ _ 0 :=
  HomogeneousSuperfunctorIso.ofComponents_hom_mem e.app _
private theorem evenNaturalIso_hom_total (e : F.toFunctor ≅ G.toFunctor)
    (he : ∀ N, e.hom.app N ∈ parity (R := k) _ _ 0) (N : C) :
    (evenNaturalIso e he).hom.total N = e.hom.app N :=
  HomogeneousSuperfunctorIso.ofComponents_hom_total e.app _ N
end Generic
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (γ : List I) (i : I) {μ : List I} (h : (i :: γ).Perm μ)
local notation "cut" => probeCutoff D m
local notation "K₀" => oldContentAppendTo D Sc cut γ i (i :: γ) (List.Perm.refl _)
local notation "K" => oldContentAppendTo D Sc cut γ i μ h
local notation "e" => probeAppendReindexIso D Sc m (List.Perm.refl γ) i
  (List.Perm.refl (i :: γ)) h h
local notation "eOld" => oldAppendReindexIso D Sc cut (List.Perm.refl γ) i
  (List.Perm.refl (i :: γ)) h h
private abbrev standard : Superfunctor k (ProbeEvaluatedModules D Sc m γ) (ProbeEvaluatedModules D Sc m γ) :=
  ⟨probeEvaluatedInduction D Sc m γ i ⋙ probeEvaluatedRestriction D Sc m γ i⟩
private abbrev stored : Superfunctor k (ProbeEvaluatedModules D Sc m γ) (ProbeEvaluatedModules D Sc m γ) :=
  ⟨probeEvaluatedAppendTo D Sc m γ i μ h ⋙ probeEvaluatedRestrictTo D Sc m γ i μ h⟩

/-- The ordinary upper-loop chart does not use a lower predecessor. -/
def probeAppendUpperLoopIso :
    (standard D Sc m γ i).toFunctor ≅ (stored D Sc m γ i h).toFunctor :=
  Functor.isoWhiskerRight e (probeEvaluatedRestrictTo D Sc m γ i μ h)
theorem probeAppendUpperLoopIso_hom_mem (N : ProbeEvaluatedModules D Sc m γ) :
    (probeAppendUpperLoopIso D Sc m γ i h).hom.app N ∈ parity (R := k) _ _ 0 :=
  Supercategory.map_mem (probeEvaluatedRestrictTo D Sc m γ i μ h)
    (probeAppendReindexIso_hom_mem D Sc m (List.Perm.refl γ) i
      (List.Perm.refl (i :: γ)) h h N)

/-- The same selected chart as an even supernatural isomorphism. -/
def probeAppendUpperLoopSuperIso : standard D Sc m γ i ≅ stored D Sc m γ i h :=
  evenNaturalIso (probeAppendUpperLoopIso D Sc m γ i h)
    (probeAppendUpperLoopIso_hom_mem D Sc m γ i h)
theorem probeAppendUpperLoopSuperIso_hom_mem :
    (probeAppendUpperLoopSuperIso D Sc m γ i h).hom ∈ parity (R := k) _ _ 0 :=
  evenNaturalIso_hom_mem (probeAppendUpperLoopIso D Sc m γ i h)
    (probeAppendUpperLoopIso_hom_mem D Sc m γ i h)
theorem probeAppendUpperLoopSuperIso_hom_total (N : ProbeEvaluatedModules D Sc m γ) :
    ((probeAppendUpperLoopSuperIso D Sc m γ i h).hom.total N).hom =
      (restriction K).map ((eOld).hom.app N.obj) := by
  rw [probeAppendUpperLoopSuperIso, evenNaturalIso_hom_total]
  rfl

/-- The total evaluated column is the prescribed OLD unit/dot column. -/
theorem probeAppendToUnitColumn_total_eq (n : ℕ) (N : ProbeEvaluatedModules D Sc m γ) :
    ((probeAppendToUnitColumn D Sc m γ i h n).total N).hom =
      unitDotColumn K (probeAppendToDot_supernatural D Sc m γ i μ h) N.obj n := by
  change ((probeAppendToUnitColumn D Sc m γ i h n).app 0 N).hom +
    ((probeAppendToUnitColumn D Sc m γ i h n).app 1 N).hom = _
  rw [probeAppendToUnitColumn_app, probeAppendToUnitColumn_app]
  change (oldAppendToUnitColumn D Sc m γ i h n).total N.obj = _
  rw [oldAppendToUnitColumn_eq, gridUnitColumnTransformation_total]

/-- Every dotted unit follows the selected single-edge upper-loop chart. -/
theorem probeAppendUpperLoop_unitColumn (n : ℕ) :
    probeAppendToUnitColumn D Sc m γ i (List.Perm.refl (i :: γ)) n ≫
      (probeAppendUpperLoopSuperIso D Sc m γ i h).hom =
        probeAppendToUnitColumn D Sc m γ i h n := by
  apply HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [Superfunctor.comp_total]
  apply InducedCategory.hom_ext
  change ((probeAppendToUnitColumn D Sc m γ i (List.Perm.refl (i :: γ)) n).total N).hom ≫
    ((probeAppendUpperLoopSuperIso D Sc m γ i h).hom.total N).hom =
      ((probeAppendToUnitColumn D Sc m γ i h n).total N).hom
  rw [probeAppendToUnitColumn_total_eq, probeAppendToUnitColumn_total_eq,
    probeAppendUpperLoopSuperIso_hom_total]
  exact oldAppendReindexIso_unitColumn D Sc m γ i (List.Perm.refl γ) h N.obj n

/-- `probeAppendUpperLoop_unitColumn`, stated with the composition and the chart in the hom
category of the probe bicategory, as `RouquierBoundaryTransport.ofIso` uses them. -/
theorem probeAppendUpperLoop_cup (n : ℕ) :
    @CategoryStruct.comp (probeEvaluatedTarget D Sc m γ ⟶ probeEvaluatedTarget D Sc m γ) _ _ _ _
      (SKM.RouquierBoundary.cup
        (probeAppendToRightAdjunction D Sc m γ i (i :: γ) (List.Perm.refl _))
        (probeAppendToInductionDot D Sc m γ i (i :: γ) (List.Perm.refl _)) n)
      ((probeAppendUpperLoopSuperIso D Sc m γ i h :
        (probeAppendToE D Sc m γ i (i :: γ) (List.Perm.refl _) ≫
          probeAppendToF D Sc m γ i (i :: γ) (List.Perm.refl _)) ≅
        (probeAppendToE D Sc m γ i μ h ≫ probeAppendToF D Sc m γ i μ h)).hom) =
      SKM.RouquierBoundary.cup (probeAppendToRightAdjunction D Sc m γ i μ h)
        (probeAppendToInductionDot D Sc m γ i μ h) n :=
  probeAppendUpperLoop_unitColumn D Sc m γ i h n

end OddMath.QuiverHecke
end

end
