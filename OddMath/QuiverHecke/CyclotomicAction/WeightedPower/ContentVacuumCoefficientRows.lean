import Mathlib.Data.Nat.Choose.Sum
import OddMath.QuiverHecke.CyclotomicAction.CoefficientPowerSeries.CoefficientPowerMomentMaps
import OddMath.QuiverHecke.CyclotomicAction.WeightedPower.WeightedCoefficientMaps

/-!
# Weighted power

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

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
