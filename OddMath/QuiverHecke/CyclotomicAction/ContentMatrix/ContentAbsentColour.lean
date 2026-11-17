import Mathlib.CategoryTheory.Whiskering
import OddMath.Algebra.FiniteZeroCoordinate
import OddMath.QuiverHecke.CyclotomicAction.ContentAppend.ContentAppendMate
import OddMath.QuiverHecke.CyclotomicAction.WeightedAppend.WeightedMatrixRows
import OddMath.SKM.RouquierCoupled

/-!
# Content matrix

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Missing-colour support and the zero predecessor boundary

DeformedMatrixComparison (4) at an output content containing no i has zero
lower E/F term. Full-content extension is zero after restriction by append i,
so the principal shifted source coordinate is zero. Off-diagonal Cartan signs
also give the required nonnegative height, including the genuinely empty
output content. This is separate from an empty predecessor with output[i].
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u

/-- A balanced induction coend of zero input values has only the zero vector. -/
theorem obj_subsingleton_of_values_subsingleton
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] (J : C ⥤ A) (M : C ⥤ SVec k)
    (hM : ∀ s, Subsingleton (M.obj s)) (w : A) : Subsingleton (Obj J M w) := by
  have hz : (LinearMap.id : Obj J M w →ₗ[k] Obj J M w) = 0 := by
    apply hom_ext J M
    intro s g b
    change tensor J M s g b = 0
    rw [(hM s).elim b 0, tensor_zero_right]
  exact ⟨fun x y => (LinearMap.congr_fun hz x).trans (LinearMap.congr_fun hz y).symm⟩

end OddMath.QuiverHecke.ELV.BalancedInduction
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X)

private theorem absentCartanSum_nonpos (i : I) :
    ∀ γ : List I, i ∉ γ → (γ.map (fun j => D.h i (D.α j))).sum ≤ 0 := by
  intro γ
  induction γ with
  | nil => intro _; simp only [List.map_nil, List.sum_nil, le_refl]
  | cons j γ ih =>
    intro hi
    have hij : i ≠ j := fun h => hi (by simp only [h, List.mem_cons, true_or])
    have hγ : i ∉ γ := fun hm => hi (List.mem_cons_of_mem j hm)
    have hj := D.d_nonneg hij
    dsimp only [SKM.Datum.d] at hj
    have hj' : D.h i (D.α j) ≤ 0 := neg_nonneg.mp hj
    simpa only [List.map_cons, List.sum_cons] using add_nonpos hj' (ih hγ)

/-- Missing i forces nonnegative Cartan height, for every cutoff and also γ=[]. -/
theorem contentCrossingHeight_nonneg_of_not_mem (cutoff : I → ℕ) (γ : List I) (i : I)
    (hi : i ∉ γ) : 0 ≤ contentCrossingHeight D cutoff i (γ : Multiset I) := by
  rw [contentCrossingHeight_coe]
  have hs := absentCartanSum_nonpos D i γ hi
  have hc : (0 : ℤ) ≤ cutoff i := Int.natCast_nonneg _
  omega

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (γ : List I) (i : I) (hi : i ∉ γ)
  (N : Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k))
include hi
local notation "Q" => oldContentInclusion D Sc cutoff γ
local notation "J" => append D Sc cutoff i
local notation "G" => induced Q N

/-- An appended i can never lie in an output block lacking i. -/
theorem oldContentAppend_offContent_of_not_mem (v : OldCategory D Sc cutoff) :
    (((J).obj v).word : Multiset I) ≠ (γ : Multiset I) := by
  intro he
  have hm : i ∈ (((J).obj v).word : Multiset I) := by
    change i ∈ (v.word ++ [i] : List I)
    simp only [List.mem_append, List.mem_singleton, or_true]
  have hmγ : i ∈ (γ : Multiset I) := by
    rw [← he]
    exact hm
  exact hi hmγ

/-- The actual append restriction of the full-content extension is zero on
all old words, not just on the chosen output object. -/
theorem oldContentRestriction_subsingleton_of_not_mem (v : OldCategory D Sc cutoff) :
    Subsingleton (((restriction J).obj G).obj v) :=
  oldContentExtension_supported D Sc cutoff γ N ((J).obj v)
    (oldContentAppend_offContent_of_not_mem D Sc cutoff γ i hi v)

/-- The actual lower E/F coend is zero throughout a missing-colour block. -/
theorem oldContentIndRes_subsingleton_of_not_mem (w : OldCategory D Sc cutoff) :
    Subsingleton ((induced J ((restriction J).obj G)).obj w) :=
  obj_subsingleton_of_values_subsingleton J ((restriction J).obj G).toFunctor
    (oldContentRestriction_subsingleton_of_not_mem D Sc cutoff γ i hi N) w

local instance absentColourGlobalPi : PiSupercategory k
    (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) := supermodulePiSupercategory

/-- The principal canonical source slot of the GIVEN global unit matrix is
zero; it can be dropped without an inverse or compatibility hypothesis. -/
theorem oldContentUnitPrincipal_subsingleton_of_not_mem
    (b : ℕ) (w : OldCategory D Sc cutoff) :
    Subsingleton ((unitMatrixFamily D Sc cutoff i G b none).obj w) := by
  have := oldContentIndRes_subsingleton_of_not_mem D Sc cutoff γ i hi N w
  exact Function.Injective.subsingleton
    (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
      (induced J ((restriction J).obj G))) w).injective

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Invertible component charts for the chosen content matrices

DeformedMatrixComparison (2), (4) transports the prescribed finite matrices
through the selected preceding and following E/F comparisons. These are
linear equivalences obtained from the given module isomorphisms, without
an invertibility hypothesis on any comparison map.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u
namespace BalancedInduction
private theorem restriction_total_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (t : C)
    (z : ((restriction Q).obj M).obj t) :
    ((restriction Q).map f).total t z = f.total (Q.obj t) z := rfl
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i

/-- The actual preceding E/F chart is a linear equivalence on its full coend. -/
def oldContentEFLinearEquiv
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    BalancedInduction.Obj J₀ ((BalancedInduction.restriction J₀).obj N).toFunctor t ≃ₗ[k]
      BalancedInduction.Obj J ((BalancedInduction.restriction J).obj
        (BalancedInduction.induced Q₁ N)).toFunctor t.obj :=
  moduleIsoLinearEquiv ((oldContentEFRestrictionNaturalIso D Sc cutoff ν i).app N) t

/-- Its forward map is exactly the selected chart used in the mate comparison. -/
theorem oldContentEFLinearEquiv_hom
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap =
      oldContentEFRestrictionLinear D Sc cutoff ν i N t := rfl

/-- The actual following F/E chart is a linear equivalence on the full coend. -/
def oldContentFELinearEquiv
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    BalancedInduction.Obj J₁ N.toFunctor ((J₁).obj t) ≃ₗ[k]
      BalancedInduction.Obj J (BalancedInduction.induced Q₁ N).toFunctor ((J).obj t.obj) :=
  moduleIsoLinearEquiv ((oldContentFERestrictionNaturalIso D Sc cutoff (i :: ν) i).app N) t

/-- The value summand uses precisely the fully faithful inclusion unit. -/
def oldContentValueLinearEquiv
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    N.obj t ≃ₗ[k] BalancedInduction.Obj Q₁ N.toFunctor t.obj :=
  moduleIsoLinearEquiv (oldContentExtensionUnitIso D Sc cutoff (i :: ν) N) t

/-- The following-composite equivalence is the very same selected map
appearing on the output side of the prescribed mate tensor square. -/
theorem oldContentFELinearEquiv_apply
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (z : BalancedInduction.Obj J₁ N.toFunctor ((J₁).obj t)) :
    oldContentFELinearEquiv D Sc cutoff ν i N t z =
      oldContentAppendRestrictionLinear D Sc cutoff (i :: ν) i N ((J₁).obj t) z := by
  change ((oldContentFERestrictionNaturalIso D Sc cutoff (i :: ν) i).hom.app N).total t z = _
  rw [oldContentFERestrictionNaturalIso_hom_app]
  exact BalancedInduction.restriction_total_apply J₁
    (oldContentAppendRestrictionIso D Sc cutoff (i :: ν) i N).hom t z

/-- The value equivalence inserts the literal identity tensor. -/
theorem oldContentValueLinearEquiv_apply
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) (b : N.obj t) :
    oldContentValueLinearEquiv D Sc cutoff ν i N t b =
      BalancedInduction.tensor Q₁ N.toFunctor t (𝟙 t.obj) b := by
  change (BalancedInduction.fullyFaithfulUnitIso Q₁ N).hom.total t b = _
  rw [BalancedInduction.fullyFaithfulUnitIso_hom]
  exact BalancedInduction.unit_total_apply Q₁ N t b

/-- The genuine source and target charts carry the prescribed content mate
to the literal first old matrix entry on every balanced generator. -/
theorem oldContentMatrixCharts_mate_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (g : (J).obj s.obj ⟶ t.obj) (b : N.obj ((J₀).obj s)) :
    (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap
      (BalancedInduction.orderedGridMateLinear J₀ J₁
        (oldContentEqualCross_supernatural D Sc cutoff ν i) N t
        (BalancedInduction.tensor J₀ ((BalancedInduction.restriction J₀).obj N).toFunctor s g b)) =
    (matrixMateComponent D Sc cutoff i (BalancedInduction.induced Q₁ N)).total t.obj
      ((oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap
        (BalancedInduction.tensor J₀ ((BalancedInduction.restriction J₀).obj N).toFunctor s g b)) := by
  rw [oldContentEFLinearEquiv_hom]
  have he := oldContentFELinearEquiv_apply D Sc cutoff ν i N t
    (BalancedInduction.orderedGridMateLinear J₀ J₁
      (oldContentEqualCross_supernatural D Sc cutoff ν i) N t
      (BalancedInduction.tensor J₀ ((BalancedInduction.restriction J₀).obj N).toFunctor s g b))
  have hm := oldContentAppendRestrictionLinear_mate_tensor D Sc cutoff ν i N s t g b
  exact he.trans hm

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Prescribed dotted columns under chosen content charts

DeformedMatrixComparison (4), (5) requires the given ordinary unit/dot
fields through the selected content comparisons. All dot powers are
retained before applying the canonical finite parity coordinates. The
corresponding cap-row comparison remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Following E/F and value charts on arbitrary output content

DeformedMatrixComparison (4) at missing-colour and empty outputs needs only
the following E/F chart and value chart. Unlike the two-letter grid, these
charts require no predecessor content or occurrence of the moving colour.
They transport all prescribed unscaled unit/dot columns.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
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
private theorem unitDotLinear_apply_power_2
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (n : ℕ) (w : C) (b : M.obj w) :
    unitDotLinear J hα M n w b =
      ((transformLinear hα M (J.obj w) : Module.End k (Obj J M.toFunctor (J.obj w))) ^ n)
        (unit J M.toFunctor w b) := rfl
private theorem unitDotLinear_intertwine_2
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

end OddMath.QuiverHecke.ELV
end

end
