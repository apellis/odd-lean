import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVQuotientInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp

/-! # Comparison of old and weighted-truncated append induction
The quotient-induction counit, ordinary composition of balanced induction
and the literal append/quotient square give the reservoir-side comparison
needed by SwappedVacuumCoordinates §6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]

def inducedIsoOfFunctorEq (J K : C ⥤ D)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (h : J = K) (M : Superfunctor k C (SVec k)) :
    induced J M ≅ induced K M := by
  subst K
  exact Iso.refl _

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
local notation "Q" => oldTruncateFunctor D Sc cutoff N

theorem weightedRestrictionModule_map
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M)
    (v w : OldCategory D Sc cutoff) (f : v ⟶ w) :
    (weightedRestriction D Sc cutoff N (weightedModule D Sc cutoff N M hM)).map f =
      M.map f := by
  obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
  rfl

/-- Restricting the descended module retains its old action. -/
def weightedRestrictionModuleIso
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    weightedRestriction D Sc cutoff N (weightedModule D Sc cutoff N M hM) ≅ M :=
  moduleIsoOfEvenNatIso _ _
    (NatIso.ofComponents (fun v => Iso.refl (M.obj v)) (fun f => by
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      rw [Category.comp_id, Category.id_comp]
      exact weightedRestrictionModule_map D Sc cutoff N M hM _ _ f))
    (fun v => id_mem (M.obj v)) (fun v => id_mem (M.obj v))

/-- Induction along the quotient identifies an annihilated old module
with its literal descended module. -/
def quotientInducedWeightedModuleIso
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    BalancedInduction.induced Q M ≅ weightedModule D Sc cutoff N M hM :=
  ((BalancedInduction.induction Q).mapIso
    (weightedRestrictionModuleIso D Sc cutoff N M hM)).symm ≪≫
      quotientInductionCounitIso D Sc cutoff N (weightedModule D Sc cutoff N M hM)

/-- Append commutes with the actual further quotient, on all old arrows. -/
theorem oldAppend_truncate (i : I) :
    CyclotomicCrossingTensor.append D Sc cutoff i ⋙ Q =
      Q ⋙ truncatedAppend D Sc cutoff N [i] := by
  refine Functor.hext (F := CyclotomicCrossingTensor.append D Sc cutoff i ⋙ Q)
    (G := Q ⋙ truncatedAppend D Sc cutoff N [i]) (fun _ => rfl) ?_
  intro v w f
  obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
  rfl

/-- Old append induction of a restricted truncated module, descended by
the weighted annihilator theorem, is isomorphic to the existing truncated
append induction. Every comparison is an actual adjunction/composition map. -/
def appendWeightedModuleIso (i : I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    weightedInducedModule D Sc cutoff N i
      (weightedRestriction D Sc cutoff N M)
      (weightedRestriction_kills D Sc cutoff N M) ≅
    BalancedInduction.induced (truncatedAppend D Sc cutoff N [i]) M :=
  let J := CyclotomicCrossingTensor.append D Sc cutoff i
  let T := truncatedAppend D Sc cutoff N [i]
  let R := weightedRestriction D Sc cutoff N M
  let F := BalancedInduction.induced J R
  let hF := induced_killsWeightedCoefficients D Sc cutoff N i R
    (weightedRestriction_kills D Sc cutoff N M)
  (quotientInducedWeightedModuleIso D Sc cutoff N F hF).symm ≪≫
    (BalancedInduction.inductionComp J Q).app R ≪≫
      BalancedInduction.inducedIsoOfFunctorEq (J ⋙ Q) (Q ⋙ T)
        (oldAppend_truncate D Sc cutoff N i) R ≪≫
      ((BalancedInduction.inductionComp Q T).app R).symm ≪≫
      (BalancedInduction.induction T).mapIso (quotientInductionCounitIso D Sc cutoff N M)

end OddMath.QuiverHecke.ELVOld
