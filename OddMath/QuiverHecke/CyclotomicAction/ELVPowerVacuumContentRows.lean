import OddMath.QuiverHecke.CyclotomicAction.ELVContentVacuumCoefficientRows
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionMatrixNaturality

/-! # Literal power-vacuum coordinates for the boundary inverse row

SwappedVacuumCoordinates §6: the actual supported power vacuum is recovered
from its empty content by the selected inclusion counit. The induced upper
chart attaches the boundary inverse coefficient to its given weighted row.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
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
end OddMath.QuiverHecke.ELVOld
