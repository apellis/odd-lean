import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendUpperLoop
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitDotComponents

/-! # Restricted probe dots through the upper-loop chart

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
the same OLD append comparison used for the cap source preserves the
raw restricted induction dot at every input module.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
universe u
attribute [local irreducible] oldAppendReindexIso
private theorem restriction_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (w : C) :
    ((restriction Q).map f).total w = f.total (Q.obj w) := rfl

private theorem transform_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    {J : C ⥤ A} [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ v, J.obj v ⟶ J.obj v} (hα : IsSupernatural k p α)
    (N : Superfunctor k C (SVec k)) (w : A) :
    (transformComponent hα N).total w = transformLinear hα N w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (γ : List I) (i : I) {μ : List I} (h : (i :: γ).Perm μ)
local notation "cut" => probeCutoff D m
local notation "K₀" => oldContentAppendTo D Sc cut γ i (i :: γ) (List.Perm.refl _)
local notation "K" => oldContentAppendTo D Sc cut γ i μ h
local notation "e" => oldAppendReindexIso D Sc cut (List.Perm.refl γ) i
  (List.Perm.refl (i :: γ)) h h

/-- The actual restricted signed dots commute with the selected even
upper-loop comparison before choosing the original regular probe. -/
theorem oldAppendUpperLoop_dot
    (N : Superfunctor k (OldContentCategory D Sc cut γ) (SVec k)) :
    restrictedDotEnd K₀
      (probeAppendToDot_supernatural D Sc m γ i (i :: γ) (List.Perm.refl _)) N ≫
        (restriction K).map ((e).hom.app N) =
      (restriction K).map ((e).hom.app N) ≫
        restrictedDotEnd K (probeAppendToDot_supernatural D Sc m γ i μ h) N := by
  have hd := oldAppendReindexIso_dot D Sc m (List.Perm.refl γ) i
    (List.Perm.refl (i :: γ)) h h N
  have hm := congrArg (restriction K).map hd
  apply HomogeneousSuperfunctorIso.total_ext
  intro w
  have hw := congrArg (fun f => f.total w) hm
  simp only [restrictedDotEnd, Functor.mapEnd_apply, dotEnd, Functor.map_comp,
    Superfunctor.comp_total, restriction_total, transform_total] at hw ⊢
  convert hw using 1 <;> rfl

end OddMath.QuiverHecke
