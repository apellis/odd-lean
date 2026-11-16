import OddMath.QuiverHecke.CyclotomicAction.WeightedMatrix
import OddMath.QuiverHecke.CyclotomicAction.WeightedKernel
import OddMath.QuiverHecke.CyclotomicAction.ContentTriple
import OddMath.SKM.AugmentedInverseNaturality
import OddMath.SKM.RouquierHomPostNaturalInverse
import OddMath.QuiverHecke.CyclotomicAction.CoefficientPowerSeries
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts
import OddMath.QuiverHecke.CyclotomicAction.RouquierPowerWords
import Mathlib.Data.Nat.Choose.Sum
import OddMath.QuiverHecke.CyclotomicAction.VacuumTensorFaithful
import OddMath.QuiverHecke.CyclotomicAction.VacuumGrading
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop
import OddMath.QuiverHecke.CyclotomicAction.ContentModules
import OddMath.QuiverHecke.CyclotomicAction.ContentMatrix
import OddMath.QuiverHecke.CyclotomicAction.IndRes
import OddMath.QuiverHecke.CyclotomicAction.KernelEntryDegrees
import OddMath.QuiverHecke.CyclotomicAction.CategoryGrading

/-!
# Weighted power

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Weighted inverse coefficients as canonical-content module maps

The coefficient cap in `SwappedVacuumCoordinates.md`, §6, must be a
homogeneous module map, retaining its signed naturality on coefficient
arrows. Project the actual prescribed content matrix inverse and remove
its original source parity shift; its empty component is the exact
weighted coefficient row already attached to the literal A/T vacuum.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor
universe u

private def weightedCoefficientProjectionNat
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V : ι → Superfunctor k C (SVec k)) (a : ι) :
    (OddMath.FiniteSupermodule.product V).toFunctor ⟶ (V a).toFunctor where
  app t := LinearMap.proj a
  naturality _ _ _ := by apply LinearMap.ext; intro x; rfl

private theorem weightedCoefficientProjectionNat_mem
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V : ι → Superfunctor k C (SVec k)) (a : ι) (t : C) :
    (weightedCoefficientProjectionNat V a).app t ∈ parity (R := k) _ _ 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro q x hx
  rw [add_zero]
  change x a ∈ ((V a).obj t).part q
  change x ∈ (OddMath.FiniteSuperspace.product fun b => (V b).obj t).part q at hx
  exact (OddMath.FiniteSuperspace.mem_product_part _ q x).mp hx a

private def weightedCoefficientProjection
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V : ι → Superfunctor k C (SVec k)) (a : ι) :
    OddMath.FiniteSupermodule.product V ⟶ V a :=
  SuperNatTrans.ofNatTrans (weightedCoefficientProjectionNat V a) (weightedCoefficientProjectionNat_mem V a)

private theorem weightedCoefficientProjection_total
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} (V : ι → Superfunctor k C (SVec k)) (a : ι) (t : C) :
    (weightedCoefficientProjection V a).total t = LinearMap.proj a := by
  change (LinearMap.proj a : (OddMath.FiniteSupermodule.product V).obj t →ₗ[k] (V a).obj t) + 0 = _
  exact add_zero _

private theorem weightedCoefficientRestriction_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {F G : Superfunctor k A (SVec k)} (f : F ⟶ G) (t : C) :
    ((restriction Q).map f).total t = f.total (Q.obj t) := rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "T" => truncatedAppend D Sc cutoff N [i]
local instance weightedContentCoefficientPi :
    PiSupercategory k (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :=
  supermodulePiSupercategory

/-- Project the given weighted content matrix inverse and remove exactly
the original r-th source shift. This is an actual module morphism. -/
def weightedContentCoefficientMap (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (r : Fin (contentUnitCount D cutoff i β)) :
    (restriction (contentInclusion D Sc cutoff N β)).obj
      ((restriction T).obj ((induction T).obj M)) ⟶
    (restriction (contentInclusion D Sc cutoff N β)).obj M :=
  (weightedContentUnitMatrixIso D Sc cutoff N i M β hh).inv ≫
    (restriction (contentInclusion D Sc cutoff N β)).map
      (weightedCoefficientProjection (weightedUnitMatrixFamily D Sc cutoff N i M _) (some r) ≫
        ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom)

/-- At genuine empty output, the canonical-content inverse has exactly
the given weighted component inverse; equality follows from its forward
field, rather than from an inverse compatibility premise. -/
theorem weightedContentUnitMatrixIso_vacuum_inv_total
    (hh : 0 ≤ contentCrossingHeight D cutoff i (0 : Multiset I)) :
    (weightedContentUnitMatrixIso D Sc cutoff N i M 0 hh).inv.total
      (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff N 0) =
    (weightedUnitMatrixComponentIso D Sc cutoff N i M (⟨[]⟩ : OldCategory D Sc cutoff) hh).inv := by
  have he : SVec.isoOfLinearEquiv
      (moduleIsoLinearEquiv (weightedContentUnitMatrixIso D Sc cutoff N i M 0 hh)
        (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff N 0)) =
      weightedUnitMatrixComponentIso D Sc cutoff N i M (⟨[]⟩ : OldCategory D Sc cutoff) hh := by
    apply Iso.ext
    change (weightedContentUnitMatrixIso D Sc cutoff N i M 0 hh).hom.total
        (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff N 0) = _
    rw [weightedContentUnitMatrixIso_hom_total, weightedUnitMatrixComponentIso_hom]
    rfl
  have hi := congrArg Iso.inv he
  exact hi

/-- The module row's genuine empty component is the literal normalized
weighted inverse coefficient, with its prescribed source unshift. -/
theorem weightedContentCoefficientMap_vacuum_total
    (hh : 0 ≤ contentCrossingHeight D cutoff i (0 : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (0 : Multiset I)))
    (z : (((restriction T).obj ((induction T).obj M)).obj
      ((oldTruncateFunctor D Sc cutoff N).obj (⟨[]⟩ : OldCategory D Sc cutoff)))) :
    (weightedContentCoefficientMap D Sc cutoff N i M 0 hh r).total
      (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff N 0) z =
      weightedUnitCoefficient D Sc cutoff N i M (⟨[]⟩ : OldCategory D Sc cutoff) hh r z := by
  simp only [weightedContentCoefficientMap, Superfunctor.comp_total,
    weightedCoefficientRestriction_total, weightedCoefficientProjection_total, SVec.comp_apply]
  rw [weightedContentUnitMatrixIso_vacuum_inv_total]
  rfl

namespace PowerVacuumCoefficient
variable [Fintype I] (L : I × ℕ → ℕ)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "W" => weightedVacuum D Sc cutoff L
local notation "Q₀" => contentInclusion D Sc cutoff bound (0 : Multiset I)
local notation "T₀" => truncatedAppend D Sc cutoff bound [i]

omit [Fintype I] in
private theorem coefficientCap_height :
    0 ≤ contentCrossingHeight D cutoff i (0 : Multiset I) := by
  simp [contentCrossingHeight]
private def coefficientCap_top (hN : 0 < cutoff i) : Fin (contentUnitCount D cutoff i (0 : Multiset I)) :=
  ⟨cutoff i - 1, by
    change cutoff i - 1 < contentUnitCount D cutoff i (([] : List I) : Multiset I)
    rw [VacuumCoefficient.count]
    omega⟩

/-- The actual weighted last inverse row as a canonical-content module
map on the literal descended A/T vacuum. -/
def weightedCoefficientCap (hN : 0 < cutoff i) :
    (restriction Q₀).obj ((restriction T₀).obj ((induction T₀).obj W)) ⟶
      (restriction Q₀).obj W :=
  weightedContentCoefficientMap D Sc cutoff bound i W 0
    (coefficientCap_height D cutoff i) (coefficientCap_top D cutoff i hN)

/-- The literal-T scalar-valued row is the actual canonical-content
module cap at empty output, with its original even empty coordinate. -/
theorem weightedFunctional_coefficientCap (hN : 0 < cutoff i)
    (z : (((restriction T₀).obj ((induction T₀).obj W)).obj
      ((oldTruncateFunctor D Sc cutoff bound).obj (⟨[]⟩ : OldCategory D Sc cutoff)))) :
    weightedFunctional D Sc cutoff L i hN z =
      (weightedEmptyEquiv D Sc cutoff L).symm
        ((weightedCoefficientCap D Sc cutoff i L hN).total
          (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff bound 0) z) := by
  have h := weightedContentCoefficientMap_vacuum_total D Sc cutoff bound i W
    (coefficientCap_height D cutoff i) (coefficientCap_top D cutoff i hN) z
  exact (congrArg (weightedEmptyEquiv D Sc cutoff L).symm h).symm

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELV
end

end

section

/-! # Coefficient rows at the empty-content boundary

BE (1.14) and SwappedVacuumCoordinates: the coefficient row transported
through the selected full-inclusion charts is the row of the inverse of
the given unit/dot columns. No finite-matrix inverse compatibility is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor
universe u v w

private theorem if_identity_total_apply
    {k C : Type u} [CommRing k] [Category.{u} C] [Preadditive C]
    [Linear k C] [Supercategory k C] (F : Superfunctor k C (SVec k))
    (b : Prop) [Decidable b] (w : C) (z : F.obj w) :
    ((if b then 𝟙 F else 0) : F ⟶ F).total w z = if b then z else 0 := by
  split_ifs
  · simp only [SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one,
      add_zero, SVec.id_apply]
  · simp only [SuperNatTrans.total, Superfunctor.zero_app, zero_add]
    rfl

private theorem conjugate_column_window
    {k : Type u} {C : Type v} [CommRing k] [Category.{w} C] [Preadditive C]
    [Linear k C] {A B V W : C} (a : A ≅ B) (c : V ≅ W)
    (g : V ⟶ A) (h : W ⟶ B) (r : B ⟶ W) (b : Prop) [Decidable b]
    (hs : g ≫ a.hom = c.hom ≫ h) (hr : h ≫ r = if b then 𝟙 W else 0) :
    g ≫ (a.hom ≫ r ≫ c.inv) = if b then 𝟙 V else 0 := by
  rw [← Category.assoc g, hs, Category.assoc c.hom, ← Category.assoc h, hr]
  split_ifs <;> simp

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem emptyContent_eq (w : ContentCategory D Sc cutoff N 0) :
    w = ⟨⟨[]⟩, rfl⟩ := by
  rcases w with ⟨⟨w⟩, hw⟩
  have he : w = [] := by simpa only [Multiset.coe_eq_zero] using hw
  subst w
  rfl

/-- On every weighted input module, the given coefficient module map
extracts the given unit/dot columns as a whole module identity. -/
theorem weightedContentCoefficientMap_unitDotColumn
    (i : I) (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (hh : 0 ≤ contentCrossingHeight D cutoff i (0 : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (0 : Multiset I)))
    (a : ℕ) (ha : a < contentUnitCount D cutoff i (0 : Multiset I)) :
    (restriction (contentInclusion D Sc cutoff N (0 : Multiset I))).map
        (unitDotColumn (truncatedAppend D Sc cutoff N [i])
          (truncatedDot_supernatural D Sc cutoff N i) M a) ≫
      weightedContentCoefficientMap D Sc cutoff N i M 0 hh r =
        if a = r.val then 𝟙 _ else 0 := by
  apply FiniteSupermodule.hom_ext_total
  intro w
  rw [emptyContent_eq D Sc cutoff N w]
  apply SVec.hom_ext
  intro z
  rw [Superfunctor.comp_total]
  change (weightedContentCoefficientMap D Sc cutoff N i M 0 hh r).total
      ⟨⟨[]⟩, rfl⟩
      ((unitDotColumn (truncatedAppend D Sc cutoff N [i])
        (truncatedDot_supernatural D Sc cutoff N i) M a).total
        ((oldTruncateFunctor D Sc cutoff N).obj ⟨[]⟩) z) = _
  rw [weightedContentCoefficientMap_vacuum_total]
  rw [weightedUnitCoefficient_unitDotColumn D Sc cutoff N i M ⟨[]⟩ hh r a ha z]
  exact (if_identity_total_apply _ _ _ z).symm

variable (i : I) (M : ContentModules D Sc cutoff N (0 : Multiset I))
local notation "β" => (0 : Multiset I)
local notation "γ" => β + ([i] : Multiset I)
local notation "hK" => contentBlockCanonicalSum β [i]
local notation "K" => contentAppendTo D Sc cutoff N β [i] γ hK
local notation "Q" => contentInclusion D Sc cutoff N β
local notation "U" => contentInclusion D Sc cutoff N γ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sq" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hK
local notation "P" => induced Q M
local notation "FE" => Functor.obj (restriction T) (induced T P)
local notation "Target" => fullSquareTargetRetargetIso K U Q T sq M FE FE
  (contentAppendToRestrictionSquare D Sc cutoff N β [i] γ hK (induced T P)) (Iso.refl FE)
local notation "Value" => contentExtensionUnitIso D Sc cutoff N β M
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i

/-- Transport the prescribed weighted inverse row through the same selected
upper and value charts as the given canonical-content unit columns. -/
def contentVacuumCoefficientMap
    (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (r : Fin (contentUnitCount D cutoff i β)) :
    (restriction K).obj (induced K M) ⟶ M :=
  (Target).hom ≫ weightedContentCoefficientMap D Sc cutoff N i P β hh r ≫ (Value).inv

/-- The transported row extracts the literal canonical-content columns,
including the empty lower-predecessor boundary. -/
theorem contentVacuumCoefficientMap_unitDotColumn
    (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (r : Fin (contentUnitCount D cutoff i β))
    (a : ℕ) (ha : a < contentUnitCount D cutoff i β) :
    unitDotColumn K hDot M a ≫ contentVacuumCoefficientMap D Sc cutoff N i M hh r =
      if a = r.val then 𝟙 M else 0 :=
  conjugate_column_window (k := k) Target Value _ _ _ _
    (contentUnitDotColumn_square D Sc cutoff N β i M a)
    (weightedContentCoefficientMap_unitDotColumn D Sc cutoff N i P hh r a ha)

/-- Every inverse of the given boundary columns has this same coefficient
row. This uses the proved joint-epimorphism identities, with no additional
inverse or matrix-comparison hypothesis. -/
theorem contentVacuumCoefficientMap_eq_inverseRow
    (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (r : Fin (contentUnitCount D cutoff i β))
    (J : SKM.SuperSumInvFrom (k := k)
      (0 : elvZeroModule D Sc cutoff N β ⟶ (restriction K).obj (induced K M))
      (unitDotColumn K hDot M) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i β)) :
    contentVacuumCoefficientMap D Sc cutoff N i M hh r = J.g' r.val := by
  apply J.hom_ext
  · simp only [Limits.zero_comp]
  · intro a ha
    rw [contentVacuumCoefficientMap_unitDotColumn D Sc cutoff N i M hh r a ha]
    exact (J.gg a r.val ha r.isLt).symm

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Input-module naturality of the induction matrix fields

Brundan–Ellis (1.13)–(1.14) require the ordinary unit/dot columns,
dot/counit rows, and signed crossing mate to be natural in every input
module map. These families are proved before any quotient specialization.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  {q : ZMod 2} {δ : ∀ s, A.obj s ⟶ A.obj s} (hδ : IsSupernatural k q δ)

/-- Dot powers retain signed naturality for arbitrary homogeneous input maps. -/
theorem dotEnd_power_supernatural (n : ℕ) :
    IsSupernatural k (n • q) (F := induction A) (G := induction A)
      (fun M => dotEnd A hδ M ^ n) := by
  have hd := transformComponent_supernatural hδ
  induction n with
  | zero => simpa only [zero_nsmul, pow_zero, End.one_def] using
      (isSupernatural_id (R := k) (F := induction A))
  | succ n ih =>
    simpa only [pow_succ, End.mul_def, succ_nsmul, add_comm, dotEnd] using hd.comp ih

/-- The given ordinary unit followed by each dot power is supernatural. -/
theorem unitDotColumn_supernatural (n : ℕ) :
    IsSupernatural k (n • q) (F := 𝟭 (Superfunctor k C (SVec k)))
      (G := induction A ⋙ restriction A) (fun M => unitDotColumn A hδ M n) := by
  have hu := isSupernatural_of_natTrans (R := k) (adjunctionUnit A) (adjunctionUnit_mem A)
  simpa only [zero_add, unitDotColumn, adjunction] using hu.comp
    ((dotEnd_power_supernatural A hδ n).whiskerRight (restriction A))

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Literal power-vacuum coordinates for the boundary inverse row

SwappedVacuumCoordinates §6: the actual supported power vacuum is recovered
from its empty content by the selected inclusion counit. The induced upper
chart attaches the boundary inverse coefficient to its given weighted row.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor
universe u

private theorem unitDotColumn_input_even
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (J : C ⥤ C) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    {M P : Superfunctor k C (SVec k)} (f : M ⟶ P)
    (hf : f ∈ parity (R := k) M P 0) (n : ℕ) :
    unitDotColumn J hα M n ≫ (restriction J).map ((induction J).map f) =
      f ≫ unitDotColumn J hα P n := by
  have h := (unitDotColumn_supernatural J hα n).naturality hf
  rw [mul_zero, sign_zero, one_smul] at h
  exact h.symm

private theorem content_counit_triangle
    {k C E : Type u} [CommRing k] [Category.{u} C] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (Q : C ⥤ E) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q] [Q.Full] [Q.Faithful]
    (M : Superfunctor k E (SVec k)) :
    (fullyFaithfulUnitIso Q ((restriction Q).obj M)).hom ≫
      (restriction Q).map ((adjunctionCounit Q).app M) = 𝟙 _ := by
  rw [fullyFaithfulUnitIso_hom]
  exact (adjunction Q).right_triangle_components M

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (W : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
  (hW : ContentSupported D Sc cutoff N 0 W)
local notation "β" => (0 : Multiset I)
local notation "γ" => β + ([i] : Multiset I)
local notation "hK" => contentBlockCanonicalSum β [i]
local notation "K" => contentAppendTo D Sc cutoff N β [i] γ hK
local notation "Q" => contentInclusion D Sc cutoff N β
local notation "U" => contentInclusion D Sc cutoff N γ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sq" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hK
local notation "M" => Functor.obj (restriction Q) W
local notation "P" => induced Q M
local notation "FE" => Functor.obj (restriction T) (induced T P)
local notation "Target" => fullSquareTargetRetargetIso K U Q T sq M FE FE
  (contentAppendToRestrictionSquare D Sc cutoff N β [i] γ hK (induced T P)) (Iso.refl FE)
local notation "Value" => contentExtensionUnitIso D Sc cutoff N β M
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "counitIso" => contentSupportedCounitIso D Sc cutoff N β W hW

/-- The selected upper chart followed by induction of the actual supported
inclusion counit is a genuine isomorphism to the given global F/E value. -/
def contentVacuumTargetIso :
    (restriction K).obj (induced K M) ≅ (restriction Q).obj ((restriction T).obj (induced T W)) :=
  Target ≪≫ (restriction Q).mapIso ((restriction T).mapIso ((induction T).mapIso counitIso))

/-- The given native columns become exactly the given global columns,
without a rescaling or a substituted coefficient extractor. -/
theorem contentVacuumTargetIso_unitDotColumn (a : ℕ) :
    unitDotColumn K hDot M a ≫ (contentVacuumTargetIso D Sc cutoff N i W hW).hom =
      (restriction Q).map (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) W a) := by
  change unitDotColumn K hDot M a ≫ ((Target).hom ≫
    (restriction Q).map ((restriction T).map ((induction T).map (counitIso).hom))) = _
  rw [← Category.assoc, contentUnitDotColumn_square D Sc cutoff N β i M a,
    Category.assoc, ← Functor.map_comp]
  rw [unitDotColumn_input_even T (truncatedDot_supernatural D Sc cutoff N i) (counitIso).hom
    (by rw [contentSupportedCounitIso_hom]; exact adjunctionCounit_mem Q W) a]
  rw [Functor.map_comp, ← Category.assoc, contentSupportedCounitIso_hom]
  have ht := content_counit_triangle Q W
  change (Value).hom ≫ (restriction Q).map ((adjunctionCounit Q).app W) = 𝟙 _ at ht
  rw [ht, Category.id_comp]

/-- The prescribed boundary inverse row, transported by the genuine
power-vacuum chart, is the given weighted coefficient row on that same
vacuum. This is an equality of whole module maps. -/
theorem contentVacuumCoefficientMap_target_compare
    (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (r : Fin (contentUnitCount D cutoff i β)) :
    contentVacuumCoefficientMap D Sc cutoff N i M hh r =
      (contentVacuumTargetIso D Sc cutoff N i W hW).hom ≫
        weightedContentCoefficientMap D Sc cutoff N i W β hh r := by
  let J := Classical.choice
    (contentAbsentUnitInverse_nonempty D Sc cutoff N β i (by simp) M)
  apply J.hom_ext
  · simp only [Limits.zero_comp]
  · intro a ha
    rw [contentVacuumCoefficientMap_unitDotColumn D Sc cutoff N i M hh r a ha,
      ← Category.assoc, contentVacuumTargetIso_unitDotColumn D Sc cutoff N i W hW a,
      weightedContentCoefficientMap_unitDotColumn D Sc cutoff N i W hh r a ha]

namespace PowerVacuumCoefficient
variable [Fintype I] (L : I × ℕ → ℕ)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1

/-- The descended vacuum has the same literal nonempty-word zero values
as the regular A/T vacuum; descent does not replace its coefficient quotient. -/
theorem weightedVacuum_contentSupported :
    ContentSupported D Sc cutoff bound 0 (weightedVacuum D Sc cutoff L) := by
  intro w hw
  have hword : w.word ≠ [] := by
    intro he
    exact hw (by rw [he]; rfl)
  have hz (z : (weightedVacuum D Sc cutoff L).obj w) : z = 0 := by
    exact coefficientPowerVacuum_support D Sc cutoff L ⟨w.word⟩ hword z
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

local notation "WM" => weightedVacuum D Sc cutoff L
local notation "Q₀" => contentInclusion D Sc cutoff bound (0 : Multiset I)
local notation "K₀" => contentAppendTo D Sc cutoff bound (0 : Multiset I) [i]
  ((0 : Multiset I) + ([i] : Multiset I)) (contentBlockCanonicalSum 0 [i])
local notation "M₀" => Functor.obj (restriction Q₀) WM
local notation "nativeFE" => Functor.obj (restriction K₀) (induced K₀ M₀)
local notation "C₀" => contentVacuumTargetIso D Sc cutoff bound i WM
  (weightedVacuum_contentSupported D Sc cutoff L)

/-- The normalized cap is the given weighted cap through the genuine
supported power-vacuum chart; it will be identified with the native row. -/
def contentPowerVacuumCap (hN : 0 < cutoff i) : nativeFE ⟶ M₀ :=
  (C₀).hom ≫ weightedCoefficientCap D Sc cutoff i L hN

/-- The normalized cap is literally the final coordinate of every inverse
of the prescribed boundary unit columns, with its original unshift. -/
theorem contentPowerVacuumCap_eq_inverseRow (hN : 0 < cutoff i)
    (J : SKM.SuperSumInvFrom (k := k)
      (0 : elvZeroModule D Sc cutoff bound (0 : Multiset I) ⟶ nativeFE)
      (unitDotColumn K₀ (contentBlockMatrixDot_supernatural D Sc cutoff bound 0 i) M₀)
      (D.parity i) (fun n => n • D.parity i) (contentUnitCount D cutoff i 0)) :
    contentPowerVacuumCap D Sc cutoff i L hN = J.g' (cutoff i - 1) := by
  have hh : 0 ≤ contentCrossingHeight D cutoff i (0 : Multiset I) := by
    simp [contentCrossingHeight]
  let r : Fin (contentUnitCount D cutoff i (0 : Multiset I)) :=
    ⟨cutoff i - 1, by simp only [contentUnitCount, contentCrossingHeight,
      Multiset.map_zero, Multiset.sum_zero, sub_zero, Int.toNat_natCast]; omega⟩
  have hc := contentVacuumCoefficientMap_target_compare D Sc cutoff bound i WM
    (weightedVacuum_contentSupported D Sc cutoff L) hh r
  change contentVacuumCoefficientMap D Sc cutoff bound i M₀ hh r =
    contentPowerVacuumCap D Sc cutoff i L hN at hc
  exact hc.symm.trans
    (contentVacuumCoefficientMap_eq_inverseRow D Sc cutoff bound i M₀ hh r J)

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELV
end

end

section

/-! # Full coefficient action on the actual weighted power vacuum

`SwappedVacuumCoordinates.md`, §§1, 3 and 6 retains the literal A/T
coefficient action through weighted descent. The given empty coordinate
commutes with that action. The actual inverse coefficient cap therefore
has its full signed A/T-linearity, in the original left multiplication order.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor
universe u

private theorem even_module_total_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (f : F ⟶ G)
    (hf : f ∈ parity (R := k) F G 0) {v w : C} (g : v ⟶ w) (b : F.obj v) :
    f.total w (F.map g b) = G.map g (f.total v b) := by
  have ht (t : C) : f.total t = f.app 0 t := by
    rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) t,
      add_zero]
  rw [ht v, ht w]
  have h := ((Superfunctor.toSuperNatTrans f).isSupernatural 0).naturality_zero g
  simpa only [SVec.comp_apply] using congrArg (fun a : F.obj v ⟶ G.obj w => a b) h

namespace PowerVacuumCoefficient
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  [Fintype I] (L : I × ℕ → ℕ)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "WM" => weightedVacuum D Sc cutoff L
local notation "OM" => coefficientPowerVacuum D Sc cutoff L
local notation "RM" => weightedRestriction D Sc cutoff bound WM
local notation "Q" => oldTruncateFunctor D Sc cutoff bound
local notation "AQ" => CoefficientPowerQuotient (k := k) D cutoff L
/-- The class in the literal full coefficient power quotient. -/
abbrev coefficientClass (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) : AQ :=
  (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a

private theorem powerVacuum_killsWeighted : KillsWeightedCoefficients D Sc cutoff bound OM :=
  (coefficientWeightedIdeal_le_annihilator_iff D Sc cutoff bound OM).mp
    ((weighted_le_elementaryPowerIdeal D cutoff L).trans
      (coefficientPowerVacuumObject D Sc cutoff L).property)

/-- The actual identity-component restriction/descent comparison already
used by the typed weighted empty coordinate. -/
def weightedRestrictionIso : RM ≅ OM :=
  weightedRestrictionModuleIso D Sc cutoff bound OM (powerVacuum_killsWeighted D Sc cutoff L)

private theorem weightedRestrictionIso_inv_mem :
    (weightedRestrictionIso D Sc cutoff L).inv ∈ parity (R := k) OM RM 0 := by
  exact moduleIsoOfEvenNatIso_inv_mem _ _ _ _ _

/-- The original typed empty coordinate uses the inverse of that same
selected descent comparison, without a scalar or a coefficient reversal. -/
theorem weightedEmptyEquiv_apply (x : AQ) :
    weightedEmptyEquiv D Sc cutoff L x =
      (weightedRestrictionIso D Sc cutoff L).inv.total (⟨[]⟩ : OldCategory D Sc cutoff)
        (coefficientPowerVacuumEmptyEquiv D Sc cutoff L x) := rfl

/-- The literal full coefficient arrow in the actual weighted category. -/
def weightedCoefficientEnd (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    ((Q).obj (⟨[]⟩ : OldCategory D Sc cutoff)) ⟶ ((Q).obj (⟨[]⟩ : OldCategory D Sc cutoff)) :=
  (Q).map (coefficientEndomorphism D Sc cutoff [] a)

/-- The actual weighted empty coordinate intertwines every full coefficient
with its original left action on the literal power quotient. -/
theorem weightedEmptyEquiv_coefficient_action
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (x : AQ) :
    (WM).map (weightedCoefficientEnd D Sc cutoff L a) (weightedEmptyEquiv D Sc cutoff L x) =
      weightedEmptyEquiv D Sc cutoff L (coefficientClass D cutoff L a * x) := by
  have hn := even_module_total_apply (weightedRestrictionIso D Sc cutoff L).inv
    (weightedRestrictionIso_inv_mem D Sc cutoff L)
    (coefficientEndomorphism D Sc cutoff [] a) (coefficientPowerVacuumEmptyEquiv D Sc cutoff L x)
  have ha := empty_coefficient_action D Sc cutoff L a x
  rw [weightedEmptyEquiv_apply, weightedEmptyEquiv_apply]
  exact hn.symm.trans (congrArg ((weightedRestrictionIso D Sc cutoff L).inv.total ⟨[]⟩) ha)

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELV
end

end

section

/-! # All-power moment maps of the actual weighted inverse cap

The reservoir series in `SwappedVacuumNonpositiveBubbles.md`, §2, uses
actual cap/unit/dot fields. The selected even descent and given append
chart carry every dotted-unit column to that same weighted field. Its
actual weighted inverse cap therefore has the proved literal A/T moment
maps, including the full chi/delta series and the cutoff-parity sign.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor
universe u

private theorem unitDotColumn_input_even_2
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (J : C ⥤ C) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    {M P : Superfunctor k C (SVec k)} (f : M ⟶ P)
    (hf : f ∈ parity (R := k) M P 0) (n : ℕ) (w : C) (b : M.obj w) :
    (((restriction J).map ((induction J).map f)).total w)
        ((unitDotColumn J hα M n).total w b) =
      (unitDotColumn J hα P n).total w (f.total w b) := by
  have h := (unitDotColumn_supernatural J hα n).naturality hf
  rw [mul_zero, sign_zero, one_smul] at h
  change f ≫ unitDotColumn J hα P n = unitDotColumn J hα M n ≫
    (restriction J).map ((induction J).map f) at h
  have ht := congrArg (fun g => g.total w) h
  rw [Superfunctor.comp_total, Superfunctor.comp_total] at ht
  have hb := congrArg (fun g => g b) ht
  simpa only [SVec.comp_apply] using hb.symm

private theorem iso_unitDotColumn_chart
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (J : C ⥤ C) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M P : Superfunctor k C (SVec k)) (e : M ≅ P)
    (he : e.hom ∈ parity (R := k) M P 0) (n : ℕ) (w : C)
    (V : Type u) [AddCommGroup V] [Module k V]
    (c : Obj J P.toFunctor (J.obj w) ≃ₗ[k] V) (b : M.obj w) :
    ((moduleIsoLinearEquiv ((restriction J).mapIso ((induction J).mapIso e)) w).trans c)
        ((unitDotColumn J hα M n).total w b) =
      c ((unitDotColumn J hα P n).total w (e.hom.total w b)) := by
  have h := unitDotColumn_input_even_2 J hα e.hom he n w b
  exact congrArg c h

namespace PowerVacuumCoefficient
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  [Fintype I] (L : I × ℕ → ℕ)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "WM" => weightedVacuum D Sc cutoff L
local notation "OM" => coefficientPowerVacuum D Sc cutoff L
local notation "RM" => weightedRestriction D Sc cutoff bound WM
local notation "Q" => oldTruncateFunctor D Sc cutoff bound
local notation "AQ" => CoefficientPowerQuotient (k := k) D cutoff L

private theorem weightedTargetChart_def (i : I) :
    weightedTargetChart D Sc cutoff L i =
      (moduleIsoLinearEquiv
        ((restriction (append D Sc cutoff i)).mapIso
          ((induction (append D Sc cutoff i)).mapIso
            (weightedRestrictionIso D Sc cutoff L).symm))
        (⟨[]⟩ : OldCategory D Sc cutoff)).trans
        (weightedMateTargetLinearEquiv D Sc cutoff bound i WM ⟨[]⟩) := rfl

/-- Every actual dotted-unit column on the literal power vacuum is
carried to the given weighted column, using the same even descent iso. -/
theorem weightedTargetChart_unitDotColumn (i : I) (n : ℕ) (a : AQ) :
    weightedTargetChart D Sc cutoff L i
      ((moduleUnitColumn D Sc cutoff i OM n).total (⟨[]⟩ : OldCategory D Sc cutoff)
        (coefficientPowerVacuumEmptyEquiv D Sc cutoff L a)) =
      (unitDotColumn (truncatedAppend D Sc cutoff bound [i])
        (truncatedDot_supernatural D Sc cutoff bound i) WM n).total
          ((Q).obj (⟨[]⟩ : OldCategory D Sc cutoff)) (weightedEmptyEquiv D Sc cutoff L a) := by
  have he : (weightedRestrictionIso D Sc cutoff L).inv ∈ parity (R := k) OM RM 0 := by
    exact moduleIsoOfEvenNatIso_inv_mem _ _ _ _ _
  have h := iso_unitDotColumn_chart (append D Sc cutoff i)
    (oldAppendDot_supernatural D Sc cutoff i) OM RM (weightedRestrictionIso D Sc cutoff L).symm he
    n (⟨[]⟩ : OldCategory D Sc cutoff) _
    (weightedMateTargetLinearEquiv D Sc cutoff bound i WM ⟨[]⟩)
    (coefficientPowerVacuumEmptyEquiv D Sc cutoff L a)
  have hu := weightedUnitColumnValue_compare D Sc cutoff bound i WM ⟨[]⟩ n
    ((weightedRestrictionIso D Sc cutoff L).inv.total ⟨[]⟩
      (coefficientPowerVacuumEmptyEquiv D Sc cutoff L a))
  rw [oldUnitColumn_eq] at hu
  rw [← weightedEmptyEquiv_apply] at hu
  simp only [Iso.symm_hom] at h
  rw [← weightedEmptyEquiv_apply] at h
  have hboth := h.trans hu
  rw [weightedTargetChart_def, oldUnitColumn_eq]
  exact hboth

/-- The actual weighted n-th unit/dot column followed by its prescribed
inverse cap, on every vector of the literal coefficient power quotient. -/
def weightedMomentMap (i : I) (hN : 0 < cutoff i) (n : ℕ) : Module.End k AQ :=
  (weightedFunctional D Sc cutoff L i hN) ∘ₗ
    SVec.toLinearMap ((unitDotColumn (truncatedAppend D Sc cutoff bound [i])
      (truncatedDot_supernatural D Sc cutoff bound i) WM n).total
        ((Q).obj (⟨[]⟩ : OldCategory D Sc cutoff))) ∘ₗ
      (weightedEmptyEquiv D Sc cutoff L).toLinearMap

omit [Fintype I] in
private theorem momentMap_unitColumn (i : I) (hN : 0 < cutoff i) (n : ℕ) (a : AQ) :
    functional D Sc cutoff L i hN
      ((moduleUnitColumn D Sc cutoff i OM n).total (⟨[]⟩ : OldCategory D Sc cutoff)
        (coefficientPowerVacuumEmptyEquiv D Sc cutoff L a)) =
      momentMap D Sc cutoff L i hN n a := by
  have hc := LinearMap.congr_fun (moduleUnitColumn_total D Sc cutoff i OM ⟨[]⟩ n)
    (coefficientPowerVacuumEmptyEquiv D Sc cutoff L a)
  exact congrArg (functional D Sc cutoff L i hN) hc

/-- Actual weighted cap/unit/dot moments equal the original proved
literal power-vacuum moment maps on every coefficient vector. -/
theorem weightedMomentMap_apply_eq (i : I) (hN : 0 < cutoff i) (n : ℕ) (a : AQ) :
    weightedMomentMap D Sc cutoff L i hN n a = momentMap D Sc cutoff L i hN n a := by
  have hcol := weightedTargetChart_unitDotColumn D Sc cutoff L i n a
  have hc := weightedFunctional_compare D Sc cutoff L i hN
    ((moduleUnitColumn D Sc cutoff i OM n).total (⟨[]⟩ : OldCategory D Sc cutoff)
      (coefficientPowerVacuumEmptyEquiv D Sc cutoff L a))
  exact (congrArg (weightedFunctional D Sc cutoff L i hN) hcol.symm).trans
    (hc.trans (momentMap_unitColumn D Sc cutoff L i hN n a))

/-- The all-power comparison is an equality of the actual A/T operators,
not only a calculation at the ground vector one. -/
theorem weightedMomentMap_eq_momentMap (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    weightedMomentMap D Sc cutoff L i hN n = momentMap D Sc cutoff L i hN n := by
  apply LinearMap.ext
  intro a
  exact weightedMomentMap_apply_eq D Sc cutoff L i hN n a

/-- Every actual weighted moment is original left multiplication by the
proved scalar moment, on all homogeneous and inhomogeneous A/T vectors. -/
theorem weightedMomentMap_apply (i : I) (hN : 0 < cutoff i) (n : ℕ) (a : AQ) :
    weightedMomentMap D Sc cutoff L i hN n a = signedMoment D Sc cutoff L i hN n * a := by
  rw [weightedMomentMap_eq_momentMap]
  exact momentMap_apply D Sc cutoff L i hN n a

/-- All even-index odd-colour moments of the actual weighted fields are
the complete coefficients of the existing raw reservoir series. -/
theorem weightedMomentMap_even (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    weightedMomentMap D Sc cutoff L i hN (cutoff i - 1 + 2 * r) =
      LinearMap.mulLeft k (completeCoefficient D cutoff L i r) := by
  rw [weightedMomentMap_eq_momentMap]
  exact momentMap_even D Sc cutoff L i hi hN r

/-- All odd-index moments retain the original left exterior coefficient
and the prescribed cutoff-parity normalization sign. -/
theorem weightedMomentMap_odd (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    weightedMomentMap D Sc cutoff L i hN (cutoff i - 1 + (2 * r + 1)) =
      LinearMap.mulLeft k ((-1 : k) ^ (cutoff i + 1) •
        (coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩) *
          completeCoefficient D cutoff L i r)) := by
  rw [weightedMomentMap_eq_momentMap]
  exact momentMap_odd D Sc cutoff L i hi hN r

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELV
end

end

section

/-! # Polynomial caps of the actual weighted power vacuum

The coefficient cap lambda(D^2+1)^M in
`SwappedVacuumNonpositiveBubbles.md`, §§3–4, is a literal module map:
apply the polynomial in the given restricted module dot, then the
prescribed weighted inverse row. Its unit/dot closures are evaluated on
every A/T vector. Identification with the mixed inverse cap remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor
universe u

namespace PowerVacuumCoefficient
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  [Fintype I] (L : I × ℕ → ℕ)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "WM" => weightedVacuum D Sc cutoff L
local notation "Q" => oldTruncateFunctor D Sc cutoff bound
local notation "Q₀" => contentInclusion D Sc cutoff bound (0 : Multiset I)
local notation "AQ" => CoefficientPowerQuotient (k := k) D cutoff L

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELV
end

end

section

/-!
# Grading of the old cyclotomic quotient over a graded base ring

Let `R` be a commutative `K`-algebra graded by `𝒜`, with a coefficient-graded homogeneous quiver
Hecke presentation over `R`. The old cyclotomic ideal is homogeneous for the grading
`QuiverHecke.elvHomGradingOver` (`ELV.ideal_dproj_mem_over`), so the old quotient category is
a graded supercategory over `K` (`ELV.oldCategoryGradedSupercategoryOver`): the degree parts
are the images of the degree parts of the ELV coefficient category, and the degree projections
descend to the quotient as additive maps.

For `K = R` with the trivial grading this is `ELV.oldCategoryGradedSupercategory`.
-/

-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory StringDiagrams OddMath.Diagrams GradedSupercategory

namespace OddMath.QuiverHecke.ELV

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ)

/-- The degree projection on the old quotient over a graded base, as an additive map. -/
def oldDprojOver (v w : List I) (n : ℤ) : Old D Sc cutoff v w →+ Old D Sc cutoff v w :=
  letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
  QuotientAddGroup.map (ideal D Sc cutoff v w).toAddSubgroup
    (ideal D Sc cutoff v w).toAddSubgroup (dproj K n).toAddMonoidHom
    (fun _ hf => ideal_dproj_mem_over D sy 𝒜 Sc hP cutoff hf n)

theorem oldDprojOver_mk (v w : List I) (n : ℤ) (f : hom D Sc cutoff v w) :
    oldDprojOver D sy 𝒜 Sc hP cutoff v w n ((ideal D Sc cutoff v w).mkQ f) =
      (ideal D Sc cutoff v w).mkQ
        (letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
        letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
        letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
        dproj K n f) :=
  rfl

/-- The degree-`n` part of a Hom module of the old quotient category over a graded base. -/
def oldDegreeOver (v w : OldCategory D Sc cutoff) (n : ℤ) :
    letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
    Submodule K (v ⟶ w) :=
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  { carrier := {f | ∃ a ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff v.word w.word n,
      (ideal D Sc cutoff v.word w.word).mkQ a = f}
    add_mem' := by
      rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, add_mem ha hb, map_add _ a b⟩
    zero_mem' := ⟨0, zero_mem _, map_zero _⟩
    smul_mem' := by
      rintro c _ ⟨a, ha, rfl⟩
      refine ⟨algebraMap K R c • a, ?_, map_smul _ _ a⟩
      simpa using smul_mem_elvHomDegreeOver D sy 𝒜 Sc hP cutoff
        (SetLike.algebraMap_mem_graded 𝒜 c) ha }

theorem mkQ_mem_oldDegreeOver {v w : OldCategory D Sc cutoff} {n : ℤ}
    {a : hom D Sc cutoff v.word w.word} (ha : a ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff v.word w.word n) :
    ((ideal D Sc cutoff v.word w.word).mkQ a : v ⟶ w) ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v w n :=
  ⟨a, ha, rfl⟩

theorem oldDprojOver_of_mem {v w : OldCategory D Sc cutoff} {m : ℤ} {f : v ⟶ w}
    (hf : f ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v w m) (n : ℤ) :
    oldDprojOver D sy 𝒜 Sc hP cutoff v.word w.word n f = if m = n then f else 0 := by
  letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
  obtain ⟨a, ha, rfl⟩ := hf
  rw [oldDprojOver_mk]
  split_ifs with h
  · subst n
    rw [dproj_of_mem ha]
  · rw [dproj_of_mem_ne ha h, map_zero]

/-- The degree parts of the old quotient over a graded base form an internal direct sum. -/
theorem oldDegreeOver_internal (v w : OldCategory D Sc cutoff) :
    letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
    DirectSum.IsInternal (oldDegreeOver D sy 𝒜 Sc hP cutoff v w) := by
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s f hf he n hn
    have hh := congrArg (oldDprojOver D sy 𝒜 Sc hP cutoff v.word w.word n) he
    rw [map_sum, map_zero] at hh
    have hsum : (∑ i ∈ s, oldDprojOver D sy 𝒜 Sc hP cutoff v.word w.word n (f i)) = f n := by
      calc
        _ = ∑ i ∈ s, if i = n then f i else 0 :=
          Finset.sum_congr rfl (fun i hi => oldDprojOver_of_mem D sy 𝒜 Sc hP cutoff (hf i hi) n)
        _ = f n := by simp [hn]
    exact hsum.symm.trans hh
  · classical
    refine Submodule.eq_top_iff'.2 fun f => ?_
    obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
    letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
    letI := degreeDecomposition K (obj D Sc cutoff v.word) (obj D Sc cutoff w.word)
    rw [← DirectSum.sum_support_decompose
      (GradedSupercategory.degree (R := K) (obj D Sc cutoff v.word) (obj D Sc cutoff w.word)) a,
      map_sum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i (mkQ_mem_oldDegreeOver D sy 𝒜 Sc hP cutoff
        (DirectSum.decompose (GradedSupercategory.degree (R := K) (obj D Sc cutoff v.word)
          (obj D Sc cutoff w.word)) a i).2)

/-- **The old quotient category over a graded base is a graded supercategory over `K`.** -/
@[instance_reducible]
def oldCategoryGradedSupercategoryOver :
    letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
    letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
    GradedSupercategory K (OldCategory D Sc cutoff) :=
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  { degree := oldDegreeOver D sy 𝒜 Sc hP cutoff
    isInternal_degree := oldDegreeOver_internal D sy 𝒜 Sc hP cutoff
    proj_mem_degree := by
      rintro v w n _ p ⟨a, ha, rfl⟩
      letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
      rw [Supercategory.proj_restrictScalars K R (OldCategory D Sc cutoff),
        oldCategory_proj, oldProj_mk]
      refine mkQ_mem_oldDegreeOver D sy 𝒜 Sc hP cutoff ?_
      rw [← Supercategory.proj_restrictScalars K R (ELVCoefficientCategory D Sc cutoff)]
      exact proj_mem_degree p ha
    id_mem_degree := fun v => by
      letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
      exact mkQ_mem_oldDegreeOver D sy 𝒜 Sc hP cutoff (id_mem_degree (R := K) (obj D Sc cutoff v.word))
    comp_mem_degree := by
      rintro v t w m n _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
      exact mkQ_mem_oldDegreeOver D sy 𝒜 Sc hP cutoff (comp_mem_degree ha hb) }

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# Bounded degree support of the truncated quotient over a graded base ring

Over a commutative `K`-algebra `R` graded by `𝒜` in degrees `0, …, b`, every Hom module of the
coefficient-truncated quotient has bounded degree support
(`ELV.truncatedContent_boundedOver`). As over a ring, the proof is an induction on the source
word: the vacuum support (`ELV.truncatedVacuum_support_of_boundOver`) starts it, and the
finite append spanning family, whose maps shift degrees by explicit amounts
(`ELV.appendBoundedOldMap_mem_degreeOver`), propagates finite support from a word to the
word with one more strand.

For `K = R` with the trivial grading (`b = 0`) this is `ELV.truncatedContent_bounded`.
-/

-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory StringDiagrams OddMath.Diagrams GradedSupercategory MonoidalCategory

namespace OddMath.QuiverHecke.ELV

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ) (N : ℕ)

/-- An affine diagram with a unit coefficient keeps its degree, over a graded base. -/
theorem affineUnit_mem_degreeOver {v w : List I} {d : ℤ}
    {f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)}
    (hf : f ∈ CoefficientGrading.presentedPart 𝒜 (gdeg D sy) (pres D Sc) (ob D v) (ob D w) d) :
    affineUnit D Sc cutoff v w f ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff v w d := by
  letI := Linear.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  letI := Supercategory.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  haveI : ∀ A B : SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff),
      IsScalarTower K R (A ⟶ B) :=
    Linear.isScalarTower_restrictScalars K R _
  letI := elvCoefficientCategoryGradingOver D sy 𝒜 cutoff
  letI := Linear.restrictScalars K R (H D Sc)
  letI := Supercategory.restrictScalars K R (H D Sc)
  letI := quiverHeckeGradingOver D sy 𝒜 Sc hP
  have h := BoxProdCoefficient.tmulHom_mem_homDegree (X := obj D Sc cutoff v)
    (Y := obj D Sc cutoff w) (id_mem_degree (R := K) (obj D Sc cutoff v).fst) hf
  rw [zero_add] at h
  exact h

/-- Right whiskering keeps degrees, over a graded base. -/
theorem rightContext_mem_degreeOver (σ : List I) {v w : List I} {n : ℤ}
    {f : hom D Sc cutoff v w} (hf : f ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff v w n) :
    rightContext D Sc cutoff σ v w f ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff (v ++ σ) (w ++ σ) n := by
  letI := Linear.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  letI := Supercategory.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  haveI : ∀ A B : SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff),
      IsScalarTower K R (A ⟶ B) :=
    Linear.isScalarTower_restrictScalars K R _
  letI := elvCoefficientCategoryGradingOver D sy 𝒜 cutoff
  letI := Linear.restrictScalars K R (H D Sc)
  letI := Supercategory.restrictScalars K R (H D Sc)
  letI := quiverHeckeGradingOver D sy 𝒜 Sc hP
  refine BoxProdCoefficient.homDegree_induction (X := obj D Sc cutoff v)
    (Y := obj D Sc cutoff w) (motive := fun y => rightContext D Sc cutoff σ v w y ∈
      elvHomDegreeOver D sy 𝒜 Sc hP cutoff (v ++ σ) (w ++ σ) n) ?_ ?_ ?_ ?_ hf
  · rw [map_zero]
    exact zero_mem _
  · intro y y' hy hy'
    rw [map_add]
    exact add_mem hy hy'
  · intro c y hy
    rw [map_smul]
    exact BoxProdCoefficient.algebraMap_smul_mem_homDegree (X := obj D Sc cutoff (v ++ σ))
      (Y := obj D Sc cutoff (w ++ σ)) c hy
  · rintro p q rfl a ha g hg
    exact BoxProdCoefficient.tmulHom_mem_homDegree (X := obj D Sc cutoff (v ++ σ))
      (Y := obj D Sc cutoff (w ++ σ)) ha
      (CoefficientGrading.wR_mem_presentedPart hg (ob D σ))

/-- The powers of the dot on the new strand, over a graded base. -/
theorem appendSourcePower_mem_degreeOver (i : I) (v : List I) (n : ℕ) :
    appendSourcePower D Sc cutoff i v n ∈
      elvHomDegreeOver D sy 𝒜 Sc hP cutoff (v ++ [i]) (v ++ [i]) (2 * sy.d i * n) := by
  rw [appendSourcePower_whisker]
  apply affineUnit_mem_degreeOver D sy 𝒜 Sc hP cutoff
  have h : (dotE D Sc [i] 0 ^ n : End _) ∈ CoefficientGrading.presentedPart 𝒜 (gdeg D sy)
      (pres D Sc) (ob D [i]) (ob D [i]) (2 * sy.d i * n) := by
    simpa only [firstDotPower, dotE_pow, List.map_replicate] using
      firstDotPower_mem_presentedPart D sy 𝒜 Sc i [] n
  exact CoefficientGrading.wL_mem_presentedPart (ob D v) h

/-- The tail diagram has the sum of its generator degrees, over a graded base. -/
theorem appendTail_mem_presentedPart {i : I} {v w : List I} (x : AppendIdx i v w) :
    appendTail D Sc x ∈ CoefficientGrading.presentedPart 𝒜 (gdeg D sy) (pres D Sc)
      (ob D (x.oldTarget ++ [i])) (ob D w) (appendTailDegree D sy x) :=
  CoefficientGrading.lin_mem_presentedPart
    (CoefficientGrading.of_mem_part' _ (degree_gdeg_mkD D sy _ _))

/-- The source dots, the smaller old Hom and the tail contribute additively, over a graded
base. -/
theorem appendBoundedOldMap_mem_degreeOver (i : I) (v t w : List I)
    (j : ℕ) {h : hom D Sc cutoff (t ++ [i]) w} {a b : ℤ}
    (hh : h ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff (t ++ [i]) w b)
    {r : (⟨v⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨t⟩}
    (hr : r ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨t⟩ a) :
    (appendBoundedOldMap D Sc cutoff N i v t w j h r :
        (⟨v ++ [i]⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨w⟩) ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v ++ [i]⟩ ⟨w⟩ (2 * sy.d i * j + (a + b)) := by
  obtain ⟨r, hr, rfl⟩ := hr
  rw [appendBoundedOldMap_mk]
  refine mkQ_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ?_
  letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
  exact comp_mem_degree (appendSourcePower_mem_degreeOver D sy 𝒜 Sc hP cutoff i v j)
    (comp_mem_degree (rightContext_mem_degreeOver D sy 𝒜 Sc hP cutoff [i] hr) hh)

/-- Finite smaller supports propagate through the finite append spanning family, over a
graded base. -/
theorem truncatedAppend_finite_supportOver (i : I) (v w : List I)
    (ih : ∀ t : List I, ∃ S : Set ℤ, S.Finite ∧
      ∀ z : (⟨v⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨t⟩,
        letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
        z ∈ ⨆ n ∈ S, truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨t⟩ n) :
    ∃ S : Set ℤ, S.Finite ∧
      ∀ z : (⟨v ++ [i]⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨w⟩,
        letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
        z ∈ ⨆ n ∈ S, truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v ++ [i]⟩ ⟨w⟩ n := by
  classical
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  choose S hfin hs using ih
  let T : Set ℤ := ⋃ (q : AppendCrossingSkeleton i v w),
    ⋃ (j : Fin (monicELVEndpointProduct D Sc cutoff i v).natDegree),
      (fun a => 2 * sy.d i * j.val + (a + appendTailDegree D sy q.index)) '' S q.index.oldTarget
  refine ⟨T, Set.finite_iUnion fun q => Set.finite_iUnion fun j =>
    (hfin q.index.oldTarget).image _, fun z => ?_⟩
  have hz : z ∈ appendFiniteRangeSpan D Sc cutoff N i v w := by
    rw [appendFiniteRangeSpan_eq_top]
    trivial
  unfold appendFiniteRangeSpan at hz
  induction hz using Submodule.iSup_induction' with
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | mem q x hx =>
    induction hx using Submodule.iSup_induction' with
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | mem j x hx =>
      obtain ⟨r, rfl⟩ := hx
      have hr := hs q.index.oldTarget r
      induction hr using Submodule.iSup_induction' with
      | zero => rw [map_zero]; exact zero_mem _
      | add r r' _ _ hr hr' => rw [map_add]; exact add_mem hr hr'
      | mem a r hr =>
        induction hr using Submodule.iSup_induction' with
        | zero => rw [map_zero]; exact zero_mem _
        | add r r' _ _ hr hr' => rw [map_add]; exact add_mem hr hr'
        | mem ha r hr =>
          exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem
            (Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨j, ⟨a, ha, rfl⟩⟩⟩ :
              2 * sy.d i * j.val + (a + appendTailDegree D sy q.index) ∈ T)
            (appendBoundedOldMap_mem_degreeOver D sy 𝒜 Sc hP cutoff N i v
              q.index.oldTarget w j.val
              (affineUnit_mem_degreeOver D sy 𝒜 Sc hP cutoff
                (appendTail_mem_presentedPart D sy 𝒜 Sc q.index)) hr))

/-- Finite support at arbitrary strand content, over a base ring graded in degrees
`0, …, b`. -/
theorem truncatedContent_finite_support_of_boundOver (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (v w : List I) :
    ∃ S : Set ℤ, S.Finite ∧
      ∀ z : (⟨v⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨w⟩,
        letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
        z ∈ ⨆ n ∈ S, truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨w⟩ n := by
  induction v using List.reverseRecOn generalizing w with
  | nil => exact ⟨Set.Icc 0 (b + M * N), Set.finite_Icc _ _,
      truncatedVacuum_support_of_boundOver D sy 𝒜 Sc hP cutoff N b h𝒜 M hM hbound w⟩
  | append_singleton v i ih =>
      exact truncatedAppend_finite_supportOver D sy 𝒜 Sc hP cutoff N i v w ih

/-- A homogeneous part outside a spanning support vanishes, over a graded base. -/
theorem truncatedDegreeOver_eq_bot_of_support (v w : List I) (S : Set ℤ)
    (hS : ∀ z : (⟨v⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨w⟩,
      letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
      z ∈ ⨆ n ∈ S, truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨w⟩ n)
    (n : ℤ) (hn : n ∉ S) :
    truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨w⟩ n = ⊥ := by
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  apply bot_unique
  intro z hz
  have hzero : ∀ y : (⟨v⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨w⟩,
      y ∈ ⨆ m ∈ S, truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨w⟩ m →
        truncatedDprojOver D sy 𝒜 Sc hP cutoff N v w n y = 0 := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | zero => exact map_zero _
    | add y y' _ _ hy hy' => rw [map_add, hy, hy', add_zero]
    | mem m y hy =>
      induction hy using Submodule.iSup_induction' with
      | zero => exact map_zero _
      | add y y' _ _ hy hy' => rw [map_add, hy, hy', add_zero]
      | mem hm y hy =>
        rw [truncatedDprojOver_of_mem D sy 𝒜 Sc hP cutoff N hy n]
        exact ite_eq_right fun h : m = n => hn (by rw [← h]; exact hm)
  have he := truncatedDprojOver_of_mem D sy 𝒜 Sc hP cutoff N hz n
  rw [ite_eq_left rfl, hzero z (hS z)] at he
  exact he.symm

/-- **Bounded degree support over a graded base.** If `𝒜` lives in degrees `0, …, b` and the
coefficient degrees are bounded by a multiple of the coefficient weights, every Hom module of
the coefficient-truncated quotient has bounded degree support. -/
theorem truncatedContent_bounded_of_boundOver (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (v w : List I) :
    ∃ B : ℕ, ∀ n : ℤ, (n < -(B : ℤ) ∨ (B : ℤ) < n) →
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨w⟩ n = ⊥ := by
  classical
  obtain ⟨S, hf, hs⟩ :=
    truncatedContent_finite_support_of_boundOver D sy 𝒜 Sc hP cutoff N b h𝒜 M hM hbound v w
  refine ⟨hf.toFinset.sup Int.natAbs, fun n hn =>
    truncatedDegreeOver_eq_bot_of_support D sy 𝒜 Sc hP cutoff N v w S hs n ?_⟩
  intro hmem
  have hnat : n.natAbs ≤ hf.toFinset.sup Int.natAbs :=
    Finset.le_sup (f := Int.natAbs) (hf.mem_toFinset.mpr hmem)
  have habs : |n| ≤ ((hf.toFinset.sup Int.natAbs : ℕ) : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hnat
  have := abs_le.mp habs
  omega

/-- Bounded degree support over a base ring graded in degrees `0, …, b`, for finitely many
colours. -/
theorem truncatedContent_boundedOver [Finite I] (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (v w : List I) :
    ∃ B : ℕ, ∀ n : ℤ, (n < -(B : ℤ) ∨ (B : ℤ) < n) →
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨w⟩ n = ⊥ := by
  obtain ⟨M, hM, hb⟩ := SKM.SYM.exists_coefficientDegree_bound D sy
  exact truncatedContent_bounded_of_boundOver D sy 𝒜 Sc hP cutoff N b h𝒜 M hM hb v w

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# Positive-degree nilpotence in the truncated quotient over a graded base ring

Over a commutative `K`-algebra `R` graded by `𝒜` in degrees `0, …, b`, every endomorphism of
positive degree of a word in the coefficient-truncated quotient is nilpotent, with an exponent
depending only on the content of the word
(`ELV.truncatedContent_positive_pow_zero_of_boundOver`). The exponent comes from the bounded
degree support of the endomorphism module (`ELV.truncatedContent_bounded_of_boundOver`):
the `e`-th power of an endomorphism of degree `d > 0` has degree `e d`, which lies outside the
support once `e` is large. Positioned dots and the appended last-strand dot are endomorphisms
of positive degree, so they are nilpotent too.

For `K = R` with the trivial grading (`b = 0`) these are the statements of
`OddMath.QuiverHecke.CyclotomicAction.ContentMatrix`.
-/

-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory StringDiagrams OddMath.Diagrams GradedSupercategory MonoidalCategory

namespace OddMath.QuiverHecke.ELV

universe u

/-- Powers of a homogeneous endomorphism in a graded supercategory are homogeneous, of the
multiplied degree. -/
theorem endPow_mem_degree {K : Type*} [CommRing K] {C : Type*} [Category C] [Preadditive C]
    [Linear K C] [Supercategory K C] [GradedSupercategory K C] {Y : C} {d : ℤ} {f : End Y}
    (hf : f ∈ degree (R := K) Y Y d) (n : ℕ) : f ^ n ∈ degree (R := K) Y Y (n • d) := by
  induction n with
  | zero => simpa using id_mem_degree (R := K) Y
  | succ n ih =>
    rw [pow_succ, End.mul_def, succ_nsmul']
    exact comp_mem_degree hf ih

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ) (N : ℕ)

/-- Powers of a homogeneous endomorphism of the truncated quotient over a graded base. -/
theorem truncatedEnd_pow_mem_degreeOver {v : List I} {d : ℤ} {f : TruncatedEnd D Sc cutoff N v}
    (hf : f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨v⟩ d) (n : ℕ) :
    f ^ n ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨v⟩ (n • d) := by
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  letI := Supercategory.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  letI := truncatedGradedSupercategoryOver D sy 𝒜 Sc hP cutoff N
  exact endPow_mem_degree (K := K) hf n

/-- **Positive-degree nilpotence over a graded base.** If `𝒜` lives in degrees `0, …, b` and
coefficient degrees are bounded linearly by coefficient weights, all endomorphisms of positive
degree of the words of a fixed content have a common nilpotence exponent. -/
theorem truncatedContent_positive_pow_zero_of_boundOver (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (ν : List I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (v : List I), v.Perm ν → ∀ (d : ℤ), 0 < d →
      ∀ f : TruncatedEnd D Sc cutoff N v,
        f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨v⟩ d → f ^ e = 0 := by
  classical
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  choose B hB using fun v : List I =>
    truncatedContent_bounded_of_boundOver D sy 𝒜 Sc hP cutoff N b h𝒜 M hM hbound v v
  let L := ν.permutations.toFinset.sup B
  refine ⟨L + 1, by omega, ?_⟩
  intro v hv d hd f hf
  have hv' : v ∈ ν.permutations.toFinset := by simpa using hv
  have hb : B v ≤ L := Finset.le_sup hv'
  have hp := truncatedEnd_pow_mem_degreeOver D sy 𝒜 Sc hP cutoff N hf (L + 1)
  have hdeg : (B v : ℤ) < (L + 1) • d := by
    rw [nsmul_eq_mul]
    have hcast : (B v : ℤ) ≤ L := by exact_mod_cast hb
    have hk : (0 : ℤ) ≤ L := Nat.cast_nonneg L
    push_cast
    nlinarith
  rw [hB v _ (Or.inr hdeg)] at hp
  exact (Submodule.mem_bot K).mp hp

/-- Positive-degree nilpotence over a base ring graded in degrees `0, …, b`, for finitely many
colours. -/
theorem truncatedContent_positive_pow_zeroOver [Finite I] (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (ν : List I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (v : List I), v.Perm ν → ∀ (d : ℤ), 0 < d →
      ∀ f : TruncatedEnd D Sc cutoff N v,
        f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨v⟩ d → f ^ e = 0 := by
  obtain ⟨M, hM, hb⟩ := SKM.SYM.exists_coefficientDegree_bound D sy
  exact truncatedContent_positive_pow_zero_of_boundOver D sy 𝒜 Sc hP cutoff N b h𝒜 M hM hb ν

/-- A dot on an active position has its symmetrizer degree, over a graded base. -/
theorem dotE_mem_presentedPart {v : List I} {r : ℕ} {i : I} (hi : v[r]? = some i) :
    dotE D Sc v r ∈ CoefficientGrading.presentedPart 𝒜 (gdeg D sy) (pres D Sc) (ob D v) (ob D v)
      (2 * sy.d i) := by
  unfold dotE genE
  split_ifs with h
  · obtain ⟨hr, rfl⟩ := List.getElem?_eq_some_iff.mp hi
    have hld : (PG.dot r).ld v = [(v.take r, Shape.dot v[r], v.drop (r + 1))] := by
      simp only [PG.ld]
      rw [List.drop_eq_getElem_cons hr]
    have hdeg : ((pl v [PG.dot r]).map fun x => gdeg D sy x.2.1).sum = 2 * sy.d v[r] := by
      rw [pl_cons, pl_nil, List.append_nil, hld, List.map_singleton, List.sum_singleton]
      rfl
    rw [← hdeg]
    exact cl_mem_presentedPart D sy 𝒜 Sc [PG.dot r] h
  · exact zero_mem _

/-- The appended last-strand dot has its symmetrizer degree, over a graded base. -/
theorem truncatedAppendDot_degreeOver (i : I) (v : TruncatedCategory D Sc cutoff N) :
    (truncatedAppendDot D Sc cutoff N i).app (D.parity i) v ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v.word ++ [i]⟩ ⟨v.word ++ [i]⟩
        (2 * sy.d i) := by
  rw [truncatedAppendDot_app]
  exact mkQ_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N
    (affineUnit_mem_degreeOver D sy 𝒜 Sc hP cutoff
      (CoefficientGrading.wL_mem_presentedPart (ob D v.word)
        (dotE_mem_presentedPart D sy 𝒜 Sc (v := [i]) (r := 0) rfl)))

include sy 𝒜 hP in
/-- The appended last-strand dot is nilpotent, uniformly on the source content, over a base
ring graded in degrees `0, …, b`. -/
theorem truncatedAppendDot_pow_zeroOver [Finite I] (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (ν : List I) (i : I) :
    ∃ e : ℕ, 0 < e ∧ ∀ v : TruncatedCategory D Sc cutoff N, v.word.Perm ν →
      let f : TruncatedEnd D Sc cutoff N (v.word ++ [i]) :=
        (truncatedAppendDot D Sc cutoff N i).app (D.parity i) v
      f ^ e = 0 := by
  obtain ⟨e, he, hp⟩ :=
    truncatedContent_positive_pow_zeroOver D sy 𝒜 Sc hP cutoff N b h𝒜 (ν ++ [i])
  refine ⟨e, he, fun v hv => hp _ (hv.append (List.Perm.refl _)) _ ?_ _
    (truncatedAppendDot_degreeOver D sy 𝒜 Sc hP cutoff N i v)⟩
  have := sy.pos i
  omega

include sy 𝒜 hP in
/-- Over a base ring graded in degrees `0, …, b`, coefficient-graded homogeneous parameters give
nilpotence of the appended dot. -/
theorem truncatedAppendDotNilpotentOver [Finite I] (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) : TruncatedAppendDotNilpotent D Sc cutoff N :=
  ⟨truncatedAppendDot_pow_zeroOver D sy 𝒜 Sc hP cutoff N b h𝒜⟩

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# Degrees of the represented kernel matrix entries over a graded base ring

Over a commutative `K`-algebra `R` graded by `𝒜`, the old quotient category is a graded
supercategory over `K` (`ELV.oldCategoryGradedSupercategoryOver`). The append functor
preserves its degrees (`oldAppend_mem_degreeOver`), the appended dot has degree `2 dᵢ` and the
equal-colour crossing has degree `-2 dᵢ`. The represented kernels carry the integer degree of
`IndResKernel.integerDegreeOver`, and the signed mate, the induction dot, the counit, the
dot/cap rows and the unit/dot columns shift it as in the field case
(`OddMath.QuiverHecke.CyclotomicAction.KernelEntryDegrees`).
-/

-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory StringDiagrams Supercategory GradedSupercategory OddMath.Diagrams

namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ)

omit [Algebra K R] in
/-- A sign multiple stays in an additive subgroup. -/
private theorem sign_smul_mem {M : Type*} {_ : AddCommGroup M} {_ : Module R M}
    {_ : Module K M} (S : Submodule K M) (q : ZMod 2) {x : M} (hx : x ∈ S) : sign R q • x ∈ S := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · simpa using hx
  · simpa using S.neg_mem hx

/-- The equal-colour crossing of the last two strands has degree `-2 dᵢ`, over a graded base. -/
theorem crossLast_mem_presentedPart (s : List I) (i : I) :
    crossLast D Sc s i i ∈ CoefficientGrading.presentedPart 𝒜 (gdeg D sy) (pres D Sc)
      (ob D (s ++ [i] ++ [i])) (ob D (s ++ [i] ++ [i])) (-2 * sy.d i) := by
  have h := cl_mem_presentedPart D sy 𝒜 Sc (t := s ++ [i] ++ [i]) (t' := s ++ [i] ++ [i])
    [PG.cross s.length] (by simpa using sChain_crossAt s [] i i)
  unfold crossLast
  convert h using 1
  symm
  simp [pl, PG.ld, gdeg, SKM.Datum.d_self]
  ring_nf

/-- The append functor preserves degrees of the old quotient, over a graded base. -/
theorem oldAppend_mem_degreeOver (i : I) {v w : OldCategory D Sc cutoff} {n : ℤ} {f : v ⟶ w}
    (hf : f ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v w n) :
    (append D Sc cutoff i).map f ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
        ((append D Sc cutoff i).obj w) n := by
  obtain ⟨a, ha, rfl⟩ := hf
  exact ⟨_, rightContext_mem_degreeOver D sy 𝒜 Sc hP cutoff [i] ha, rfl⟩

/-- Parity twists preserve degrees of the old quotient, over a graded base. -/
theorem oldTwist_mem_degreeOver {v t : OldCategory D Sc cutoff} {n : ℤ} (p : ZMod 2)
    (f : v ⟶ t) (hf : f ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t n) :
    twist R p f ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t n := by
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  letI := oldCategoryGradedSupercategoryOver D sy 𝒜 Sc hP cutoff
  have hf' : f ∈ degree (R := K) v t n := hf
  rw [twist_apply, ← Supercategory.proj_restrictScalars K R (OldCategory D Sc cutoff) 0 f,
    ← Supercategory.proj_restrictScalars K R (OldCategory D Sc cutoff) 1 f]
  exact Submodule.add_mem _ (proj_mem_degree (R := K) 0 hf')
    (sign_smul_mem _ _ (proj_mem_degree (R := K) 1 hf'))

/-- Composition adds degrees in the old quotient, over a graded base. -/
theorem oldComp_mem_degreeOver {v t w : OldCategory D Sc cutoff} {m n : ℤ}
    {f : v ⟶ t} {g : t ⟶ w}
    (hf : f ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t m)
    (hg : g ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff t w n) :
    f ≫ g ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v w (m + n) := by
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  letI := oldCategoryGradedSupercategoryOver D sy 𝒜 Sc hP cutoff
  exact comp_mem_degree (R := K) (C := OldCategory D Sc cutoff) hf hg

/-- The prescribed last dot has degree `2 dᵢ`, over a graded base. -/
theorem oldAppendDotComponent_degreeOver (i : I) (s : OldCategory D Sc cutoff) :
    oldAppendDotComponent D Sc cutoff i s ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj s)
        ((append D Sc cutoff i).obj s) (2 * sy.d i) :=
  mkQ_mem_oldDegreeOver D sy 𝒜 Sc hP cutoff
    (affineUnit_mem_degreeOver D sy 𝒜 Sc hP cutoff
      (CoefficientGrading.wL_mem_presentedPart (ob D s.word)
        (dotE_mem_presentedPart D sy 𝒜 Sc (v := [i]) (r := 0) rfl)))

/-- The prescribed last equal crossing has degree `-2 dᵢ`, over a graded base. -/
theorem equalCrossComponent_degreeOver (i : I) (s : OldCategory D Sc cutoff) :
    equalCrossComponent D Sc cutoff i s ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj ((append D Sc cutoff i).obj s))
        ((append D Sc cutoff i).obj ((append D Sc cutoff i).obj s)) (-2 * sy.d i) :=
  mkQ_mem_oldDegreeOver D sy 𝒜 Sc hP cutoff
    (affineUnit_mem_degreeOver D sy 𝒜 Sc hP cutoff (crossLast_mem_presentedPart D sy 𝒜 Sc s.word i))

/-- The represented lower-loop degree over a graded base: the sum of the two Hom degrees. -/
abbrev representedKernelDegreeOver (i : I) (v t : OldCategory D Sc cutoff) (n : ℤ) :=
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  letI := oldCategoryGradedSupercategoryOver D sy 𝒜 Sc hP cutoff
  letI : ∀ X Y : OldCategory D Sc cutoff, IsScalarTower K R (X ⟶ Y) :=
    Linear.isScalarTower_restrictScalars K R _
  IndResKernel.integerDegreeOver (K := K) (R := R) (append D Sc cutoff i) v t n

/-- The chosen signed mate has degree `-2 dᵢ` on represented kernels, over a graded base. -/
theorem mateKernelComponent_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    {n : ℤ} {x : IndResKernel.Component (k := R) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t n) :
    mateKernelComponent D Sc cutoff i v t x ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
        ((append D Sc cutoff i).obj t) (n - 2 * sy.d i) := by
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  letI := oldCategoryGradedSupercategoryOver D sy 𝒜 Sc hP cutoff
  let _ : ∀ X Y : OldCategory D Sc cutoff, IsScalarTower K R (X ⟶ Y) :=
    Linear.isScalarTower_restrictScalars K R _
  refine ((IndResKernel.integerDegreeOver_le_iff (K := K) (R := R) (append D Sc cutoff i) v t n
    ((oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
      ((append D Sc cutoff i).obj t) (n - 2 * sy.d i)).comap
      ((mateKernelComponent D Sc cutoff i v t).restrictScalars K))).2 ?_) hx
  intro s q r hqr g hg b hb
  simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars]
  rw [IndResKernel.componentTensor, mateKernelComponent_tensor]
  have hd := oldComp_mem_degreeOver D sy 𝒜 Sc hP cutoff
    (oldAppend_mem_degreeOver D sy 𝒜 Sc hP cutoff i hb)
    (oldComp_mem_degreeOver D sy 𝒜 Sc hP cutoff
      (equalCrossComponent_degreeOver D sy 𝒜 Sc hP cutoff i s)
      (oldTwist_mem_degreeOver D sy 𝒜 Sc hP cutoff (D.parity i) _
        (oldAppend_mem_degreeOver D sy 𝒜 Sc hP cutoff i hg)))
  rw [show n - 2 * sy.d i = r + (-2 * sy.d i + q) by omega]
  exact Submodule.neg_mem _ hd

/-- The chosen induction dot raises represented degree by `2 dᵢ`, over a graded base. -/
theorem dotKernelComponent_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    {n : ℤ} {x : IndResKernel.Component (k := R) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t n) :
    dotKernelComponent D Sc cutoff i v t x ∈
      representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t (n + 2 * sy.d i) := by
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  letI := oldCategoryGradedSupercategoryOver D sy 𝒜 Sc hP cutoff
  let _ : ∀ X Y : OldCategory D Sc cutoff, IsScalarTower K R (X ⟶ Y) :=
    Linear.isScalarTower_restrictScalars K R _
  refine ((IndResKernel.integerDegreeOver_le_iff (K := K) (R := R) (append D Sc cutoff i) v t n
    ((representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t (n + 2 * sy.d i)).comap
      ((dotKernelComponent D Sc cutoff i v t).restrictScalars K))).2 ?_) hx
  intro s q r hqr g hg b hb
  simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars]
  rw [IndResKernel.componentTensor, dotKernelComponent_tensor]
  have hnew := oldComp_mem_degreeOver D sy 𝒜 Sc hP cutoff
    (oldAppendDotComponent_degreeOver D sy 𝒜 Sc hP cutoff i s)
    (oldTwist_mem_degreeOver D sy 𝒜 Sc hP cutoff (D.parity i) g hg)
  have hd := IndResKernel.componentTensor_mem_integerDegreeOver (K := K) (R := R)
    (append D Sc cutoff i) v t s
    (oldAppendDotComponent D Sc cutoff i s ≫ twist R (D.parity i) g) b hnew hb
  rw [show n + 2 * sy.d i = 2 * sy.d i + q + r by omega]
  exact hd

/-- The induction dot powers have their multiple degree, over a graded base. -/
theorem dotKernelComponent_power_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (m : ℕ) {n : ℤ} {x : IndResKernel.Component (k := R) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t n) :
    (dotKernelComponent D Sc cutoff i v t ^ m) x ∈
      representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t (n + 2 * sy.d i * m) := by
  induction m with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, mul_zero, add_zero] using hx
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := dotKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t ih
    rw [show n + 2 * sy.d i * ((m + 1 : ℕ) : ℤ) = n + 2 * sy.d i * (m : ℤ) + 2 * sy.d i by
      push_cast; ring]
    exact h

/-- The chosen counit has represented degree zero, over a graded base. -/
theorem counitKernelComponent_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    {n : ℤ} {x : IndResKernel.Component (k := R) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t n) :
    counitKernelComponent D Sc cutoff i v t x ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t n := by
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  letI := oldCategoryGradedSupercategoryOver D sy 𝒜 Sc hP cutoff
  let _ : ∀ X Y : OldCategory D Sc cutoff, IsScalarTower K R (X ⟶ Y) :=
    Linear.isScalarTower_restrictScalars K R _
  refine ((IndResKernel.integerDegreeOver_le_iff (K := K) (R := R) (append D Sc cutoff i) v t n
    ((oldDegreeOver D sy 𝒜 Sc hP cutoff v t n).comap
      ((counitKernelComponent D Sc cutoff i v t).restrictScalars K))).2 ?_) hx
  intro s q r hqr g hg b hb
  simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars]
  rw [IndResKernel.componentTensor, counitKernelComponent_tensor]
  rw [show n = r + q by omega]
  exact oldComp_mem_degreeOver D sy 𝒜 Sc hP cutoff hb hg

/-- Every dot/cap row has degree `2 dᵢ m`, over a graded base. -/
theorem capKernelComponent_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (m : ℕ) {n : ℤ} {x : IndResKernel.Component (k := R) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t n) :
    capKernelComponent D Sc cutoff i m v t x ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff v t (n + 2 * sy.d i * m) :=
  counitKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t
    (dotKernelComponent_power_degreeOver D sy 𝒜 Sc hP cutoff i v t m hx)

/-- Every unit/dot column has degree `2 dᵢ m`, including its sign, over a graded base. -/
theorem unitKernelComponent_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (m : ℕ) {n : ℤ} {b : v ⟶ t}
    (hb : b ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t n) :
    unitKernelComponent D Sc cutoff i m v t b ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
        ((append D Sc cutoff i).obj t) (n + 2 * sy.d i * m) := by
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  cases v with
  | mk v =>
    cases t with
    | mk t =>
      change inductionUnitDotColumn D Sc cutoff i v t m b ∈ _
      rw [inductionUnitDotColumn_comp]
      have hm : ((ideal D Sc cutoff (t ++ [i]) (t ++ [i])).mkQ
          (appendMovingPower D Sc cutoff i t m) :
            (append D Sc cutoff i).obj (⟨t⟩ : OldCategory D Sc cutoff) ⟶
              (append D Sc cutoff i).obj (⟨t⟩ : OldCategory D Sc cutoff)) ∈
          oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj ⟨t⟩)
            ((append D Sc cutoff i).obj ⟨t⟩) (2 * sy.d i * m) := by
        refine mkQ_mem_oldDegreeOver D sy 𝒜 Sc hP cutoff ?_
        rw [appendMovingPower_whisker, ← appendSourcePower_whisker]
        exact appendSourcePower_mem_degreeOver D sy 𝒜 Sc hP cutoff i t m
      rw [inductionUnitDotSign]
      exact sign_smul_mem _ _ (oldComp_mem_degreeOver D sy 𝒜 Sc hP cutoff
        (oldAppend_mem_degreeOver D sy 𝒜 Sc hP cutoff i hb) hm)

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-!
# Integer degrees of the represented matrix inverses over a graded base ring

Over a commutative `K`-algebra `R` graded by `𝒜`, the Hom modules of the old quotient carry the
`K`-linear degrees of `ELV.oldCategoryGradedSupercategoryOver`, and the represented kernels
carry `IndResKernel.integerDegreeOver`. The finite unit/cap matrices have degree zero after the
prescribed coordinate shifts (`positiveKernelMap_degreeOver`,
`negativeKernelMap_degreeOver`), so their proved bijectivity gives homogeneous inverses,
with principal inverse degree `+2 dᵢ`, and the unit-inverse-cap closures have degree
`2 dᵢ (r + s + 1)` (`positiveKernelClosure_degreeOver`, `negativeKernelClosure_degreeOver`). The comparison only uses the additive structure
(`IntegerMatrix.Coordinates.toInt`), since the matrices are `R`-linear and the degrees are
`K`-linear.

For `K = R` with the trivial grading these are the statements of
`OddMath.QuiverHecke.CyclotomicAction.KernelEntryDegrees`.
-/

noncomputable section

open CategoryTheory Opposite StringDiagrams Supercategory GradedSupercategory OddMath.Diagrams
open OddMath.IntegerMatrix

namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ)

/-- Homogeneous scalars shift degrees of the old quotient, over a graded base. -/
theorem oldSmul_mem_degreeOver {v w : OldCategory D Sc cutoff} {a n : ℤ} {r : R} {f : v ⟶ w}
    (hr : r ∈ 𝒜 a) (hf : f ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v w n) :
    r • f ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v w (a + n) := by
  obtain ⟨b, hb, rfl⟩ := hf
  exact ⟨r • b, smul_mem_elvHomDegreeOver D sy 𝒜 Sc hP cutoff hr hb, map_smul _ r b⟩

/-- The coefficient Hom grading of the old quotient over a graded base, as additive
coordinates. -/
def oldHomIntegerCoordinatesOver (v t : OldCategory D Sc cutoff) :
    Coordinates (k := ℤ) (v ⟶ t) :=
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  letI := oldCategoryGradedSupercategoryOver D sy 𝒜 Sc hP cutoff
  Coordinates.toInt
    { degree := degree (R := K) v t
      projection := fun n => dproj K n
      projection_mem := fun n x => dproj_mem n x
      projection_of_mem := fun {m n} {x} hx => by
        by_cases h : m = n
        · subst m
          rw [ite_eq_left rfl]
          exact dproj_of_mem hx
        · rw [ite_eq_right h]
          exact dproj_of_mem_ne hx h
      spanning := (isInternal_degree v t).submodule_iSup_eq_top }

/-- The integer degree of the represented lower loop over a graded base, as additive
coordinates. -/
def representedKernelCoordinatesOver (i : I) (v t : OldCategory D Sc cutoff) :
    Coordinates (k := ℤ) (IndResKernel.Component (k := R) (append D Sc cutoff i) v t) :=
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  letI := oldCategoryGradedSupercategoryOver D sy 𝒜 Sc hP cutoff
  letI : ∀ X Y : OldCategory D Sc cutoff, IsScalarTower K R (X ⟶ Y) :=
    Linear.isScalarTower_restrictScalars K R _
  Coordinates.toInt
    { degree := IndResKernel.integerDegreeOver (K := K) (R := R) (append D Sc cutoff i) v t
      projection := IndResKernel.integerProjectionOver 𝒜 (append D Sc cutoff i)
        (fun hf => oldAppend_mem_degreeOver D sy 𝒜 Sc hP cutoff i hf)
        (fun hr hf => oldSmul_mem_degreeOver D sy 𝒜 Sc hP cutoff hr hf) v t
      projection_mem := IndResKernel.integerProjectionOver_mem 𝒜 _ _ _ v t
      projection_of_mem := fun hx => IndResKernel.integerProjectionOver_of_mem 𝒜 _ _ _ v t hx
      spanning := IndResKernel.iSup_integerDegreeOver_eq_top (K := K) (R := R) _ v t }

private def positiveEntryCoordinatesOver (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff) :
    ∀ a, Coordinates (k := ℤ) ((positiveKernelFamily D Sc cutoff i m t a).obj (op v))
  | none => representedKernelCoordinatesOver D sy 𝒜 Sc hP cutoff i v t
  | some _ => oldHomIntegerCoordinatesOver D sy 𝒜 Sc hP cutoff v t

private def negativeEntryCoordinatesOver (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff) :
    ∀ a, Coordinates (k := ℤ) ((negativeKernelFamily D Sc cutoff i m t a).obj (op v))
  | none => oldHomIntegerCoordinatesOver D sy 𝒜 Sc hP cutoff
      ((append D Sc cutoff i).obj v) ((append D Sc cutoff i).obj t)
  | some _ => oldHomIntegerCoordinatesOver D sy 𝒜 Sc hP cutoff v t

/-- The positive finite source has its prescribed shifted decomposition, over a graded base. -/
def positiveKernelIntegerCoordinatesOver (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff) :
    Coordinates (k := ℤ) ((BalancedKernelTensor.piKernel
      (positiveKernelFamily D Sc cutoff i m t)).obj (op v)) :=
  Coordinates.shiftedFamily (positiveEntryCoordinatesOver D sy 𝒜 Sc hP cutoff i m v t)
    (positiveKernelShift D sy i m)

/-- The negative finite target has its prescribed shifted decomposition, over a graded base. -/
def negativeKernelIntegerCoordinatesOver (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff) :
    Coordinates (k := ℤ) ((BalancedKernelTensor.piKernel
      (negativeKernelFamily D Sc cutoff i m t)).obj (op v)) :=
  Coordinates.shiftedFamily (negativeEntryCoordinatesOver D sy 𝒜 Sc hP cutoff i m v t)
    (negativeKernelShift D sy i m)

/-- The positive matrix preserves the shifted integer degree, over a graded base. -/
theorem positiveKernelMap_degreeOver (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff)
    {n : ℤ}
    {z : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)).obj (op v)}
    (hz : z ∈ (positiveKernelIntegerCoordinatesOver D sy 𝒜 Sc hP cutoff i m v t).degree n) :
    (positiveKernelMap D Sc cutoff i m t).app (op v) z ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
        ((append D Sc cutoff i).obj t) n := by
  have hz' := (Coordinates.mem_shiftedDegree
    (positiveEntryCoordinatesOver D sy 𝒜 Sc hP cutoff i m v t)
    (positiveKernelShift D sy i m) n z).1 hz
  rw [positiveKernelMap_apply]
  apply add_mem
  · have h0 : z none ∈ representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t
        (n + 2 * sy.d i) := hz' none
    have h := mateKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t h0
    rwa [add_sub_cancel_right] at h
  · apply sum_mem
    intro r _
    have h0 : z (some r) ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t
        (n + -(2 * sy.d i * r.val)) := hz' (some r)
    have h := unitKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t r.val h0
    rwa [neg_add_cancel_right] at h

/-- The negative matrix preserves the shifted integer degree, over a graded base. -/
theorem negativeKernelMap_degreeOver (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff)
    {n : ℤ} {z : IndResKernel.Component (k := R) (append D Sc cutoff i) v t}
    (hz : z ∈ representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t n) :
    (negativeKernelMap D Sc cutoff i m t).app (op v) z ∈
      (negativeKernelIntegerCoordinatesOver D sy 𝒜 Sc hP cutoff i m v t).degree n := by
  apply (Coordinates.mem_shiftedDegree
    (negativeEntryCoordinatesOver D sy 𝒜 Sc hP cutoff i m v t)
    (negativeKernelShift D sy i m) n _).2
  intro a
  cases a with
  | none =>
    rw [negativeKernelMap_none]
    have h := mateKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t hz
    rw [sub_eq_add_neg] at h
    exact h
  | some r =>
    rw [negativeKernelMap_some]
    exact capKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t r.val hz

/-- The positive inverse preserves the shifted coordinate degrees, over a graded base. -/
theorem positiveKernelEquiv_inverse_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) {n : ℤ}
    {y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t}
    (hy : y ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
      ((append D Sc cutoff i).obj t) n) :
    (positiveKernelEquiv D Sc cutoff i v t hh).symm y ∈
      (positiveKernelIntegerCoordinatesOver D sy 𝒜 Sc hP cutoff i
        (contentUnitCount D cutoff i (t.word : Multiset I)) v t).degree n :=
  Coordinates.inverse_mem _ (oldHomIntegerCoordinatesOver D sy 𝒜 Sc hP cutoff _ _)
    (positiveKernelEquiv D Sc cutoff i v t hh).toAddEquiv.toIntLinearEquiv
    (fun _ _ hx => positiveKernelMap_degreeOver D sy 𝒜 Sc hP cutoff i _ v t hx) hy

/-- The negative inverse preserves the shifted coordinate degrees, over a graded base. -/
theorem negativeKernelEquiv_inverse_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) {n : ℤ} {y}
    (hy : y ∈ (negativeKernelIntegerCoordinatesOver D sy 𝒜 Sc hP cutoff i
      (contentCapCount D cutoff i (t.word : Multiset I)) v t).degree n) :
    (negativeKernelEquiv D Sc cutoff i v t hh).symm y ∈
      representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t n :=
  Coordinates.inverse_mem (representedKernelCoordinatesOver D sy 𝒜 Sc hP cutoff i v t) _
    (negativeKernelEquiv D Sc cutoff i v t hh).toAddEquiv.toIntLinearEquiv
    (fun _ _ hx => negativeKernelMap_degreeOver D sy 𝒜 Sc hP cutoff i _ v t hx) hy

/-- The principal positive inverse raises degree by `2 dᵢ`, over a graded base. -/
theorem positiveKernelPrincipalInverse_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) {n : ℤ}
    {y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t}
    (hy : y ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
      ((append D Sc cutoff i).obj t) n) :
    positiveKernelPrincipalInverse D Sc cutoff i v t hh y ∈
      representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t (n + 2 * sy.d i) :=
  (Coordinates.mem_shiftedDegree _ _ _ _).1
    (positiveKernelEquiv_inverse_degreeOver D sy 𝒜 Sc hP cutoff i v t hh hy) none

/-- The principal negative inverse also raises degree by `2 dᵢ`, over a graded base. -/
theorem negativeKernelPrincipalInverse_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) {n : ℤ}
    {y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t}
    (hy : y ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
      ((append D Sc cutoff i).obj t) n) :
    negativeKernelPrincipalInverse D Sc cutoff i v t hh y ∈
      representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t (n + 2 * sy.d i) := by
  apply negativeKernelEquiv_inverse_degreeOver D sy 𝒜 Sc hP cutoff i v t hh
  apply (Coordinates.mem_shiftedDegree _ _ _ _).2
  intro a
  cases a with
  | none =>
    change y ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
      ((append D Sc cutoff i).obj t) (n + 2 * sy.d i + -(2 * sy.d i))
    simpa only [add_neg_cancel_right] using hy
  | some r =>
    change (Pi.single none y : ∀ a, (negativeKernelFamily D Sc cutoff i
      (contentCapCount D cutoff i (t.word : Multiset I)) t a).obj (op v)) (some r) ∈ _
    rw [Pi.single_eq_of_ne (by simp)]
    exact zero_mem _

/-- The positive represented closure has degree `2 dᵢ (r + s + 1)`, over a graded base. -/
theorem positiveKernelClosure_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) (r s : ℕ)
    {n : ℤ} {b : v ⟶ t} (hb : b ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t n) :
    positiveKernelClosure D Sc cutoff i v t hh r s b ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff v t (n + 2 * sy.d i * (r + s + 1 : ℕ)) := by
  have h := capKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t s
    (positiveKernelPrincipalInverse_degreeOver D sy 𝒜 Sc hP cutoff i v t hh
      (unitKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t r hb))
  have he : n + 2 * sy.d i * r + 2 * sy.d i + 2 * sy.d i * s =
      n + 2 * sy.d i * (r + s + 1 : ℕ) := by push_cast; ring
  simpa only [positiveKernelClosure, LinearMap.comp_apply, he] using h

/-- The negative represented closure has the same degree, over a graded base. -/
theorem negativeKernelClosure_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) (r s : ℕ)
    {n : ℤ} {b : v ⟶ t} (hb : b ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t n) :
    negativeKernelClosure D Sc cutoff i v t hh r s b ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff v t (n + 2 * sy.d i * (r + s + 1 : ℕ)) := by
  have h := capKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t s
    (negativeKernelPrincipalInverse_degreeOver D sy 𝒜 Sc hP cutoff i v t hh
      (unitKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t r hb))
  have he : n + 2 * sy.d i * r + 2 * sy.d i + 2 * sy.d i * s =
      n + 2 * sy.d i * (r + s + 1 : ℕ) := by push_cast; ring
  simpa only [negativeKernelClosure, LinearMap.comp_apply, he] using h

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-!
# Coefficient image on exact-content ELV supermodules over a graded base ring

Over a commutative `K`-algebra `R` graded by `𝒜`, central families on the exact-content source
category are graded by the degree of their components in the truncated quotient over `K`
(`ELV.contentCoefficientDegreeOver`). Their images on the exact-content module category form
a coefficient grading (`ELV.contentModuleCoeffGradingOver`). If `𝒜` lives in degrees
`0, …, b` and there are finitely many colours, bounded degree support of the source category
(`ELV.contentCategory_end_boundedOver`) makes every coefficient of high degree vanish, so
these coefficients generate a jointly nilpotent coefficient ideal
(`ELV.contentModuleCoefficientIdealOver`).

For `K = R` with the trivial grading these are the constructions of
`OddMath.QuiverHecke.CyclotomicAction.CategoryGrading`.
-/

-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory StringDiagrams Supercategory OddMath.Diagrams

namespace OddMath.QuiverHecke.ELV

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ) (N : ℕ)

theorem id_mem_truncatedDegreeOver (v : TruncatedCategory D Sc cutoff N) :
    𝟙 v ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v v 0 := by
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  letI := Supercategory.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  letI := truncatedGradedSupercategoryOver D sy 𝒜 Sc hP cutoff N
  exact GradedSupercategory.id_mem_degree (R := K) v

theorem comp_mem_truncatedDegreeOver {u v w : TruncatedCategory D Sc cutoff N} {m n : ℤ}
    {f : u ⟶ v} {g : v ⟶ w} (hf : f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N u v m)
    (hg : g ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v w n) :
    f ≫ g ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N u w (m + n) := by
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  letI := Supercategory.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  letI := truncatedGradedSupercategoryOver D sy 𝒜 Sc hP cutoff N
  exact GradedSupercategory.comp_mem_degree (R := K) hf hg

variable (β : Multiset I)

/-- Integer degrees of source central families over a graded base: every component lies in the
given degree of the truncated quotient. -/
def contentCoefficientDegreeOver (n : ℤ) : Set (ContentCoefficient D Sc cutoff N β) :=
  {c | ∀ (p : ZMod 2) (v : ContentCategory D Sc cutoff N β),
    c.app p v ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v.obj v.obj n}

/-- The image of the source coefficient degree on the exact-content module target, over a
graded base. -/
def contentModuleCoeffGradingOver :
    SwappedAssembly.ProbeWindow.CoeffGrading R (contentModuleTarget D Sc cutoff N β) where
  deg n := {t | ∃ c ∈ contentCoefficientDegreeOver D sy 𝒜 Sc hP cutoff N β n,
    contentRealize D Sc cutoff N β c = t}
  id_mem := by
    refine ⟨_, ?_, contentRealize_id D Sc cutoff N β⟩
    intro p v
    change (if p = 0 then 𝟙 v else 0) ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v.obj v.obj 0
    split_ifs
    · exact id_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v.obj
    · exact Submodule.zero_mem _
  comp_mem := by
    rintro m n x y ⟨c, hc', rfl⟩ ⟨d, hd, rfl⟩
    refine ⟨c ≫ d, ?_, contentRealize_comp D Sc cutoff N β c d⟩
    intro p v
    rw [Superfunctor.comp_app]
    exact Submodule.add_mem _
      (comp_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N (hc' 0 v) (hd p v))
      (comp_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N (hc' 1 v) (hd _ v))
  proj_mem := by
    rintro n p x ⟨c, hc', rfl⟩
    refine ⟨proj R p c, ?_, contentRealize_proj D Sc cutoff N β p c⟩
    intro q v
    rw [Superfunctor.proj_app]
    split_ifs
    · exact hc' _ v
    · exact Submodule.zero_mem _

/-- One degree threshold for all words of the fixed content, over a base ring graded in degrees
`0, …, b`. -/
theorem contentCategory_end_boundedOver [Finite I] (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) :
    ∃ B : ℕ, ∀ (v : ContentCategory D Sc cutoff N β) (n : ℤ), (B : ℤ) ≤ n →
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v.obj v.obj n = ⊥ := by
  classical
  choose B hB using fun v : List I =>
    truncatedContent_boundedOver D sy 𝒜 Sc hP cutoff N b h𝒜 v v
  let S := β.toList.permutations.toFinset
  refine ⟨S.sup B + 1, fun v n hn => hB v.obj.word n (Or.inr ?_)⟩
  have hv : v.obj.word ∈ S := by
    change v.obj.word ∈ β.toList.permutations.toFinset
    simp only [List.mem_toFinset, List.mem_permutations]
    apply Multiset.coe_eq_coe.mp
    exact v.content.trans (Multiset.coe_toList β).symm
  have hle := Finset.le_sup (f := B) hv
  have hle' : (B v.obj.word : ℤ) ≤ ((S.sup B : ℕ) : ℤ) := by exact_mod_cast hle
  omega

/-- Source support annihilates every high-degree central family simultaneously, over a graded
base. -/
theorem contentCoefficient_eq_zeroOver [Finite I] (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (n : ℤ)
    (hn : ((contentCategory_end_boundedOver D sy 𝒜 Sc hP cutoff N β b h𝒜).choose : ℤ) ≤ n)
    (c : ContentCoefficient D Sc cutoff N β)
    (h : c ∈ contentCoefficientDegreeOver D sy 𝒜 Sc hP cutoff N β n) : c = 0 := by
  apply Superfunctor.hom_ext
  intro p v
  have hv := h p v
  rw [(contentCategory_end_boundedOver D sy 𝒜 Sc hP cutoff N β b h𝒜).choose_spec v n hn] at hv
  exact hv

/-- High-degree coefficients vanish on the exact-content module category, over a graded base. -/
theorem contentModule_coefficient_eq_zeroOver [Finite I] (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (n : ℤ)
    (hn : ((contentCategory_end_boundedOver D sy 𝒜 Sc hP cutoff N β b h𝒜).choose : ℤ) ≤ n)
    (t : 𝟙 (contentModuleTarget D Sc cutoff N β) ⟶ 𝟙 (contentModuleTarget D Sc cutoff N β))
    (ht : t ∈ (contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β).deg n) : t = 0 := by
  obtain ⟨c, hc', rfl⟩ := ht
  rw [contentCoefficient_eq_zeroOver D sy 𝒜 Sc hP cutoff N β b h𝒜 n hn c hc']
  exact (contentRealizeLinear D Sc cutoff N β).map_zero

/-- Jointly nilpotent coefficient ideal on functors into the exact-content module category,
over a base ring graded in degrees `0, …, b`. -/
def contentModuleCoefficientIdealOver [Finite I] (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (T : PiSCat R) :
    SwappedAssembly.ProbeWindow.CoefficientIdeal (T ⟶ contentModuleTarget D Sc cutoff N β) :=
  SwappedAssembly.ProbeWindow.reservoirCoefficientIdeal T
    (contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β)
    (contentCategory_end_boundedOver D sy 𝒜 Sc hP cutoff N β b h𝒜).choose
    (contentModule_coefficient_eq_zeroOver D sy 𝒜 Sc hP cutoff N β b h𝒜)

end OddMath.QuiverHecke.ELV
end

end
