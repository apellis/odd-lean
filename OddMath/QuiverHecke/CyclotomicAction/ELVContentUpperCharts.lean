import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixRows

/-! # Following E/F and value charts on arbitrary output content

DeformedMatrixComparison (4) at missing-colour and empty outputs needs only
the following E/F chart and value chart. Unlike the two-letter grid, these
charts require no predecessor content or occurrence of the moving colour.
They transport all prescribed unscaled unit/dot columns.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
namespace BalancedInduction
private theorem contentUpper_restriction_total_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (t : C)
    (z : ((restriction Q).obj M).obj t) :
    ((restriction Q).map f).total t z = f.total (Q.obj t) z := rfl
private theorem unitDotLinear_apply_power
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (n : ℕ) (w : C) (b : M.obj w) :
    unitDotLinear J hα M n w b =
      ((transformLinear hα M (J.obj w) : Module.End k (Obj J M.toFunctor (J.obj w))) ^ n)
        (unit J M.toFunctor w b) := rfl
private theorem unitDotLinear_intertwine
    {k C A W : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [AddCommMonoid W] [Module k W]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (w : C)
    (L : Obj J M.toFunctor (J.obj w) →ₗ[k] W) (g : Module.End k W)
    (hd : L ∘ₗ transformLinear hα M (J.obj w) = g ∘ₗ L) (n : ℕ) (b : M.obj w) :
    L (unitDotLinear J hα M n w b) = (g ^ n) (L (unit J M.toFunctor w b)) := by
  exact LinearMap.congr_fun (intertwine_pow _ _ _ hd n) (unit J M.toFunctor w b)

end BalancedInduction
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (γ : List I) (i : I)
local notation "K" => oldContentAppend D Sc cutoff γ i
local notation "Q" => oldContentInclusion D Sc cutoff γ
local notation "J" => append D Sc cutoff i
local notation "dK" => oldContentAppendDot_supernatural D Sc cutoff γ i
local notation "dJ" => oldAppendDot_supernatural D Sc cutoff i
variable (N : Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k))
local notation "G" => induced Q N

/-- The selected following F/E equivalence requires no preceding colour. -/
def oldContentFEChart (t : OldContentCategory D Sc cutoff γ) :
    Obj K N.toFunctor ((K).obj t) ≃ₗ[k] Obj J (G).toFunctor ((J).obj t.obj) :=
  moduleIsoLinearEquiv ((oldContentFERestrictionNaturalIso D Sc cutoff γ i).app N) t

/-- The value chart is the fully faithful inclusion unit on arbitrary output. -/
def oldContentValueChart (t : OldContentCategory D Sc cutoff γ) :
    N.obj t ≃ₗ[k] Obj Q N.toFunctor t.obj :=
  moduleIsoLinearEquiv (oldContentExtensionUnitIso D Sc cutoff γ N) t

theorem oldContentFEChart_apply (t : OldContentCategory D Sc cutoff γ)
    (z : Obj K N.toFunctor ((K).obj t)) :
    oldContentFEChart D Sc cutoff γ i N t z =
      oldContentAppendRestrictionLinear D Sc cutoff γ i N ((K).obj t) z := by
  change ((oldContentFERestrictionNaturalIso D Sc cutoff γ i).hom.app N).total t z = _
  rw [oldContentFERestrictionNaturalIso_hom_app]
  exact BalancedInduction.contentUpper_restriction_total_apply K
    (oldContentAppendRestrictionIso D Sc cutoff γ i N).hom t z

theorem oldContentValueChart_apply (t : OldContentCategory D Sc cutoff γ) (b : N.obj t) :
    oldContentValueChart D Sc cutoff γ N t b = tensor Q N.toFunctor t (𝟙 t.obj) b := by
  change (fullyFaithfulUnitIso Q N).hom.total t b = _
  rw [fullyFaithfulUnitIso_hom]
  exact unit_total_apply Q N t b

/-- Every unscaled dotted unit column is preserved, including genuine empty
output and content in which i is absent. -/
theorem oldContentFEChart_unitDot (t : OldContentCategory D Sc cutoff γ) (n : ℕ) (b : N.obj t) :
    oldContentFEChart D Sc cutoff γ i N t (unitDotLinear K dK N n t b) =
      unitDotLinear J dJ G n t.obj (oldContentValueChart D Sc cutoff γ N t b) := by
  let g := inductionDot D Sc cutoff i G ((K).obj t).obj
  have hd := oldContentAppendRestrictionIso_dot D Sc cutoff γ i N ((K).obj t)
  have hp := BalancedInduction.unitDotLinear_intertwine K dK N t _ _ hd n b
  have hu := oldContentAppendRestrictionIso_unit D Sc cutoff γ i N t b
  have hv := oldContentValueChart_apply D Sc cutoff γ N t b
  change oldContentValueChart D Sc cutoff γ N t b = unit Q N.toFunctor t b at hv
  have hunit := congrArg (fun x => (g ^ n) x) hu
  have hvalue := congrArg (fun x => (g ^ n) (unit J (G).toFunctor t.obj x)) hv
  have he := oldContentFEChart_apply D Sc cutoff γ i N t (unitDotLinear K dK N n t b)
  have hraw := hp.trans (hunit.trans hvalue.symm)
  have ht := BalancedInduction.unitDotLinear_apply_power J dJ G n t.obj
    (oldContentValueChart D Sc cutoff γ N t b)
  dsimp only [g, inductionDot] at hraw
  dsimp only [oldContentAppend] at he hraw ht ⊢
  exact he.trans (hraw.trans ht.symm)

end OddMath.QuiverHecke.ELVOld
