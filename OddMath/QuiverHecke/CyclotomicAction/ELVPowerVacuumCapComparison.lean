import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedCoefficientRows
import OddMath.QuiverHecke.CyclotomicAction.ELVContentCapNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerRows
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerSandwich

/-! # The literal power-vacuum coefficient cap in the selected weighted chart

`SwappedVacuumCoordinates.md`, §6, keeps the paper's actual coefficient
power quotient. The upper power/weight containment descends that same
module on unchanged carriers. The selected append chart then identifies
its actual weighted inverse row with its original A/T-valued coefficient
functional. No quotient equality or extra inverse is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
private theorem inductionRestrictionIsoChart_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (M P : Superfunctor k C (SVec k)) (e : M ≅ P) (w : C)
    (V : Type u) [AddCommGroup V] [Module k V]
    (c : Obj J P.toFunctor (J.obj w) ≃ₗ[k] V)
    (z : Obj J M.toFunctor (J.obj w)) :
    ((moduleIsoLinearEquiv ((restriction J).mapIso ((induction J).mapIso e)) w).trans c) z =
      c ((((restriction J).map ((induction J).map e.hom)).total w) z) := rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The original vacuum coefficient row is natural against every even
input-module map. The odd-map version retains the full row-degree sign
in `contentUnitCoefficientMap_supernatural`. -/
theorem moduleUnitCoefficient_vacuum_naturality_even
    {M P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)} {f : M ⟶ P}
    (hf : f ∈ parity (R := k) M P 0) (i : I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (([] : List I) : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (([] : List I) : Multiset I)))
    (z : mateTargetSpace D Sc cutoff i M (⟨[]⟩ : OldCategory D Sc cutoff)) :
    moduleUnitCoefficient D Sc cutoff P i ⟨[]⟩ hh r
      ((((restriction (append D Sc cutoff i)).map
        ((induction (append D Sc cutoff i)).map f)).total ⟨[]⟩) z) =
      f.total ⟨[]⟩ (moduleUnitCoefficient D Sc cutoff M i ⟨[]⟩ hh r z) := by
  have h := (contentUnitCoefficientMap_supernatural D Sc cutoff i [] hh r).naturality hf
  rw [mul_zero, sign_zero, one_smul] at h
  have ht := congrArg
    (fun g => g.total (⟨⟨[]⟩, List.Perm.refl _⟩ : OldContentCategory D Sc cutoff [])) h
  rw [Superfunctor.comp_total, Superfunctor.comp_total] at ht
  have hz := LinearMap.congr_fun ht z
  change (contentUnitCoefficientMap D Sc cutoff P i [] hh r).total
      (⟨⟨[]⟩, List.Perm.refl _⟩ : OldContentCategory D Sc cutoff [])
      ((((restriction (append D Sc cutoff i)).map
        ((induction (append D Sc cutoff i)).map f)).total ⟨[]⟩) z) =
    f.total ⟨[]⟩ ((contentUnitCoefficientMap D Sc cutoff M i [] hh r).total
      (⟨⟨[]⟩, List.Perm.refl _⟩ : OldContentCategory D Sc cutoff []) z) at hz
  rw [contentUnitCoefficientMap_vacuum_total, contentUnitCoefficientMap_vacuum_total] at hz
  exact hz

section Descent
variable (N : ℕ) (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
  (hM : KillsWeightedCoefficients D Sc cutoff N M)
local notation "W" => weightedModule D Sc cutoff N M hM
local notation "RM" => weightedRestriction D Sc cutoff N W
local notation "descentIso" => weightedRestrictionModuleIso D Sc cutoff N M hM

private theorem descentComparison_inv_mem :
    (descentIso).inv ∈ parity (R := k) M RM 0 := by
  exact moduleIsoOfEvenNatIso_inv_mem _ _ _ _ _

/-- The selected append chart on the original annihilated old module.
The first comparison is the actual descent/restriction isomorphism, whose
components are identities on the unchanged module values. -/
def weightedDescentMateTargetEquiv (i : I) (w : OldCategory D Sc cutoff) :
    mateTargetSpace D Sc cutoff i M w ≃ₗ[k]
      (((restriction (truncatedAppend D Sc cutoff N [i])).obj
        ((induction (truncatedAppend D Sc cutoff N [i])).obj W)).obj
          ((oldTruncateFunctor D Sc cutoff N).obj w)) :=
  (moduleIsoLinearEquiv
    ((restriction (append D Sc cutoff i)).mapIso
      ((induction (append D Sc cutoff i)).mapIso (descentIso).symm)) w).trans
    (weightedMateTargetLinearEquiv D Sc cutoff N i W w)

/-- The weighted inverse row on the selected actual descent chart equals
the original vacuum inverse row, before choosing a coefficient quotient. -/
theorem weightedDescentVacuumCoefficient_compare (i : I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (([] : List I) : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (([] : List I) : Multiset I)))
    (z : mateTargetSpace D Sc cutoff i M (⟨[]⟩ : OldCategory D Sc cutoff)) :
    (moduleIsoLinearEquiv descentIso (⟨[]⟩ : OldCategory D Sc cutoff))
      (weightedUnitCoefficient D Sc cutoff N i W ⟨[]⟩ hh r
        (weightedDescentMateTargetEquiv D Sc cutoff N M hM i ⟨[]⟩ z)) =
      moduleUnitCoefficient D Sc cutoff M i ⟨[]⟩ hh r z := by
  have hc := weightedUnitCoefficient_compare D Sc cutoff N i W ⟨[]⟩ hh r
  let f : M ⟶ RM := (descentIso).inv
  have hn := moduleUnitCoefficient_vacuum_naturality_even D Sc cutoff
    (descentComparison_inv_mem D Sc cutoff N M hM) i hh r z
  let z' := (((restriction (append D Sc cutoff i)).map
    ((induction (append D Sc cutoff i)).map f)).total (⟨[]⟩ : OldCategory D Sc cutoff)) z
  have hc' := LinearMap.congr_fun hc z'
  dsimp only [z', f] at hc'
  simp only [LinearMap.comp_apply] at hc'
  have hboth := hc'.trans hn
  have hout := congrArg (moduleIsoLinearEquiv descentIso (⟨[]⟩ : OldCategory D Sc cutoff)) hboth
  have hcancel := (moduleIsoLinearEquiv descentIso (⟨[]⟩ : OldCategory D Sc cutoff)).apply_symm_apply
    (moduleUnitCoefficient D Sc cutoff M i ⟨[]⟩ hh r z)
  unfold weightedDescentMateTargetEquiv
  rw [inductionRestrictionIsoChart_apply, Iso.symm_hom]
  exact hout.trans hcancel

end Descent

namespace PowerVacuumCoefficient
variable [Fintype I] (L : I × ℕ → ℕ)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "M" => coefficientPowerVacuum D Sc cutoff L

private theorem killsWeighted : KillsWeightedCoefficients D Sc cutoff bound M :=
  (coefficientWeightedIdeal_le_annihilator_iff D Sc cutoff bound M).mp
    ((weighted_le_elementaryPowerIdeal D cutoff L).trans
      (coefficientPowerVacuumObject D Sc cutoff L).property)

/-- The actual power-to-weighted comparison functor applied to the literal
regular A/T vacuum; it introduces no replacement coefficient quotient. -/
def weightedVacuum : Superfunctor k (TruncatedCategory D Sc cutoff bound) (SVec k) :=
  (elementaryPowerToWeighted D Sc cutoff L).obj (coefficientPowerVacuumObject D Sc cutoff L)

omit [Fintype I] in
private theorem height (i : I) :
    0 ≤ contentCrossingHeight D cutoff i (([] : List I) : Multiset I) := by
  simp [contentCrossingHeight]

private def topSlot (i : I) (hN : 0 < cutoff i) :
    Fin (contentUnitCount D cutoff i (([] : List I) : Multiset I)) :=
  ⟨cutoff i - 1, by rw [VacuumCoefficient.count]; omega⟩

/-- The original literal A/T empty coordinate followed by the inverse
identity-component descent comparison. Its target is the actual weighted
vacuum value, so no carrier identification is silently inferred. -/
def weightedEmptyEquiv : CoefficientPowerQuotient (k := k) D cutoff L ≃ₗ[k]
    (weightedVacuum D Sc cutoff L).obj ((oldTruncateFunctor D Sc cutoff bound).obj ⟨[]⟩) :=
  (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).trans
    (moduleIsoLinearEquiv
      (weightedRestrictionModuleIso D Sc cutoff bound M (killsWeighted D Sc cutoff L))
        (⟨[]⟩ : OldCategory D Sc cutoff)).symm

/-- The prescribed selected weighted append chart starts on the unchanged
literal A/T vacuum induction component. -/
def weightedTargetChart (i : I) :
    mateTargetSpace D Sc cutoff i M (⟨[]⟩ : OldCategory D Sc cutoff) ≃ₗ[k]
      (((restriction (truncatedAppend D Sc cutoff bound [i])).obj
        ((induction (truncatedAppend D Sc cutoff bound [i])).obj
          (weightedVacuum D Sc cutoff L))).obj
            ((oldTruncateFunctor D Sc cutoff bound).obj ⟨[]⟩)) :=
  weightedDescentMateTargetEquiv D Sc cutoff bound M (killsWeighted D Sc cutoff L) i ⟨[]⟩

/-- Decode the actual prescribed weighted last inverse row into literal
A/T using the original empty-vacuum coordinate. -/
def weightedFunctional (i : I) (hN : 0 < cutoff i) :
    (((restriction (truncatedAppend D Sc cutoff bound [i])).obj
      ((induction (truncatedAppend D Sc cutoff bound [i])).obj
        (weightedVacuum D Sc cutoff L))).obj
          ((oldTruncateFunctor D Sc cutoff bound).obj ⟨[]⟩)) →ₗ[k]
      CoefficientPowerQuotient (k := k) D cutoff L :=
  (weightedEmptyEquiv D Sc cutoff L).symm.toLinearMap ∘ₗ
    weightedUnitCoefficient D Sc cutoff bound i (weightedVacuum D Sc cutoff L) ⟨[]⟩
      (height D cutoff i) (topSlot D cutoff i hN)

/-- The original literal-power-vacuum λ is the selected weighted inverse
cap, with exactly the given row, source unshift and empty coordinate. -/
theorem weightedFunctional_compare (i : I) (hN : 0 < cutoff i)
    (z : mateTargetSpace D Sc cutoff i M (⟨[]⟩ : OldCategory D Sc cutoff)) :
    weightedFunctional D Sc cutoff L i hN (weightedTargetChart D Sc cutoff L i z) =
      functional D Sc cutoff L i hN z := by
  have hc := weightedDescentVacuumCoefficient_compare D Sc cutoff bound M
    (killsWeighted D Sc cutoff L) i (height D cutoff i) (topSlot D cutoff i hN) z
  exact congrArg (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).symm hc

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELVOld
