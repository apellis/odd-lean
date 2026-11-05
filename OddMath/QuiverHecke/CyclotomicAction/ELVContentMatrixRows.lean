import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixCharts
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixRows

/-! # Prescribed dotted columns under chosen content charts

DeformedMatrixComparison (4), (5) requires the given ordinary unit/dot
fields through the selected content comparisons. All dot powers are
retained before applying the canonical finite parity coordinates. The
corresponding cap-row comparison remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
namespace BalancedInduction
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
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i
local notation "d₁" => oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i
local notation "d" => oldAppendDot_supernatural D Sc cutoff i

/-- The old matrix's given unit field is literally the generic ordinary
unit/dot column used by the changing-content grid. -/
theorem moduleUnitColumn_eq_unitDotColumn
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) :
    moduleUnitColumn D Sc cutoff i M n = unitDotColumn J d M n := rfl

/-- The old matrix's given cap field is literally the generic ordinary
dot/counit row; no normalization change is made. -/
theorem moduleCapRow_eq_capDotRow
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) :
    moduleCapRow D Sc cutoff i M n = capDotRow J d M n := rfl

/-- Every prescribed unit/dot column is transported through the selected
following E/F and value charts, with no rescaling. -/
theorem oldContentFELinearEquiv_unitDot
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) (n : ℕ) (b : N.obj t) :
    oldContentFELinearEquiv D Sc cutoff ν i N t (unitDotLinear J₁ d₁ N n t b) =
      unitDotLinear J d (induced Q₁ N) n t.obj
        (oldContentValueLinearEquiv D Sc cutoff ν i N t b) := by
  let g := inductionDot D Sc cutoff i (induced Q₁ N) ((J₁).obj t).obj
  have hd := oldContentAppendRestrictionIso_dot D Sc cutoff (i :: ν) i N ((J₁).obj t)
  have hp := BalancedInduction.unitDotLinear_intertwine J₁ d₁ N t _ _ hd n b
  have hu := oldContentAppendRestrictionIso_unit D Sc cutoff (i :: ν) i N t b
  have hv := oldContentValueLinearEquiv_apply D Sc cutoff ν i N t b
  change oldContentValueLinearEquiv D Sc cutoff ν i N t b = unit Q₁ N.toFunctor t b at hv
  have hunit := congrArg (fun x => (g ^ n) x) hu
  have hvalue := congrArg (fun x => (g ^ n) (unit J (induced Q₁ N).toFunctor t.obj x)) hv
  have he := oldContentFELinearEquiv_apply D Sc cutoff ν i N t
    (unitDotLinear J₁ d₁ N n t b)
  have hraw := hp.trans (hunit.trans hvalue.symm)
  have ht := BalancedInduction.unitDotLinear_apply_power J d (induced Q₁ N) n t.obj
    (oldContentValueLinearEquiv D Sc cutoff ν i N t b)
  dsimp only [g, inductionDot] at hraw
  dsimp only [oldContentAppend] at he hraw ht ⊢
  have hr := hraw.trans ht.symm
  have hfinal := he.trans hr
  exact hfinal

end OddMath.QuiverHecke.ELVOld
