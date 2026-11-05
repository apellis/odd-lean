import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerSandwich
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendTensors

/-! # Scheduled word modules in the chosen content categories

SwappedVacuumCoordinates §§4–6 require the actual regular-power word modules
in the truncated content categories used by the chosen Rouquier generators.
The explicit upper coefficient-power bound supplies the required descent;
the actual inclusion counit recovers each supported module.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordContent
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- Explicit coefficient-weight cutoff of the literal power quotient. -/
abbrev powerBound : ℕ := SKM.SYM.elvPowerWeightBound D cutoff L + 1

theorem word_killsWeighted (ν : List I) :
    KillsWeightedCoefficients D Sc cutoff (powerBound D cutoff L) (powerWordModule D Sc cutoff L ν) :=
  (coefficientWeightedIdeal_le_annihilator_iff D Sc cutoff _ _).mp
    ((weighted_le_elementaryPowerIdeal D cutoff L).trans (powerWordObject D Sc cutoff L ν).property)

/-- Literal weighted descent on the unchanged regular-power word carriers. -/
def weightedWord (ν : List I) :
    Superfunctor k (TruncatedCategory D Sc cutoff (powerBound D cutoff L)) (SVec k) :=
  weightedModule D Sc cutoff (powerBound D cutoff L) (powerWordModule D Sc cutoff L ν)
    (word_killsWeighted D Sc cutoff L ν)

/-- Support is proved from the literal old Homs, not assumed of the model. -/
theorem weightedWord_supported (ν : List I) :
    ContentSupported D Sc cutoff (powerBound D cutoff L) (ν : Multiset I)
      (weightedWord D Sc cutoff L ν) := by
  intro w hw
  have hz : ∀ x : (powerWordModule D Sc cutoff L ν).obj (OldCategory.mk w.word), x = 0 := by
    intro x
    obtain ⟨g, rfl⟩ := powerWordGenerator_surjective D Sc cutoff L ν (OldCategory.mk w.word) x
    have hg : g = 0 := oldCategory_hom_eq_zero_of_content_ne D Sc cutoff (f := g) (Ne.symm hw)
    rw [hg, map_zero]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The word module in the actual exact-content category. -/
def contentWord (ν : List I) :
    ContentModules D Sc cutoff (powerBound D cutoff L) (ν : Multiset I) :=
  (BalancedInduction.restriction (contentInclusion D Sc cutoff (powerBound D cutoff L) (ν : Multiset I))).obj
    (weightedWord D Sc cutoff L ν)

/-- The selected even inclusion counit recovers this actual supported module. -/
def contentExtensionIso (ν : List I) :
    BalancedInduction.induced (contentInclusion D Sc cutoff (powerBound D cutoff L) (ν : Multiset I))
      (contentWord D Sc cutoff L ν) ≅ weightedWord D Sc cutoff L ν :=
  contentSupportedCounitIso D Sc cutoff (powerBound D cutoff L) (ν : Multiset I)
    (weightedWord D Sc cutoff L ν) (weightedWord_supported D Sc cutoff L ν)

/-- The chosen truncated append induction is identified with the next actual
word module by the existing quotient/composition comparisons. -/
def weightedAppendIso (ν : List I) (i : I) :
    BalancedInduction.induced (truncatedAppend D Sc cutoff (powerBound D cutoff L) [i])
      (weightedWord D Sc cutoff L ν) ≅ weightedWord D Sc cutoff L (ν ++ [i]) :=
  let N := powerBound D cutoff L
  let M := weightedWord D Sc cutoff L ν
  let R := weightedRestriction D Sc cutoff N M
  let A := append D Sc cutoff i
  let F := BalancedInduction.induced A R
  let hF := induced_killsWeightedCoefficients D Sc cutoff N i R
    (weightedRestriction_kills D Sc cutoff N M)
  (appendWeightedModuleIso D Sc cutoff N i M).symm ≪≫
    weightedModuleIso D Sc cutoff N F (powerWordModule D Sc cutoff L (ν ++ [i])) hF
      (word_killsWeighted D Sc cutoff L (ν ++ [i]))
      ((BalancedInduction.induction A).mapIso
        (weightedRestrictionModuleIso D Sc cutoff N (powerWordModule D Sc cutoff L ν)
          (word_killsWeighted D Sc cutoff L ν)) ≪≫ powerWordAppendIso D Sc cutoff L ν i)

/-- The independently chosen exact-content E sends the chosen content word
to its actual next-word module through the prescribed extension comparison. -/
def contentAppendIso (ν : List I) (i : I) :
    BalancedInduction.induced
      (contentAppendTo D Sc cutoff (powerBound D cutoff L) (ν : Multiset I) [i]
        ((ν ++ [i] : List I) : Multiset I) (Multiset.coe_add ν [i])) (contentWord D Sc cutoff L ν) ≅
    contentWord D Sc cutoff L (ν ++ [i]) :=
  contentAppendToRestrictionIso D Sc cutoff (powerBound D cutoff L) (ν : Multiset I) [i]
      ((ν ++ [i] : List I) : Multiset I) (Multiset.coe_add ν [i]) (contentWord D Sc cutoff L ν) ≪≫
    (BalancedInduction.restriction
      (contentInclusion D Sc cutoff (powerBound D cutoff L) ((ν ++ [i] : List I) : Multiset I))).mapIso
      ((BalancedInduction.induction (truncatedAppend D Sc cutoff (powerBound D cutoff L) [i])).mapIso
        (contentExtensionIso D Sc cutoff L ν) ≪≫ weightedAppendIso D Sc cutoff L ν i)

end OddMath.QuiverHecke.ELVOld.PowerWordContent
