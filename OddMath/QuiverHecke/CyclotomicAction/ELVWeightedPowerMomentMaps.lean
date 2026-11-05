import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerCoefficients
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerMomentMaps
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionMatrixNaturality

/-! # All-power moment maps of the actual weighted inverse cap

The reservoir series in `SwappedVacuumNonpositiveBubbles.md`, §2, uses
actual cap/unit/dot fields. The selected even descent and given append
chart carry every dotted-unit column to that same weighted field. Its
actual weighted inverse cap therefore has the proved literal A/T moment
maps, including the full chi/delta series and the cutoff-parity sign.
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
  have h := unitDotColumn_input_even J hα e.hom he n w b
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
end OddMath.QuiverHecke.ELVOld
