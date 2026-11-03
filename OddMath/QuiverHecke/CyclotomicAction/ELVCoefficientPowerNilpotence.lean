import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerSandwich
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelDegree
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVContentInductionNilpotence

/-! # Fixed-content dot nilpotence on coefficient-power modules

The positive-dot input in `SwappedNondegeneracy.md`, §2, follows from the
proved power/weight sandwich and the existing positive integer-degree bound.
The literal T-annihilated old modules and their signed coend dots are retained.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ)

private theorem truncated_off_content {v w : TruncatedCategory D Sc cutoff N}
    (h : ¬ w.word.Perm v.word) (f : v ⟶ w) : f = 0 := by
  obtain ⟨a, rfl⟩ := (truncatedIdeal D Sc cutoff N v.word w.word).mkQ_surjective f
  rw [hom_eq_zero_of_not_perm D Sc cutoff h a, map_zero]

private def truncatedCoendDot (i : I)
    (M : TruncatedModules D Sc cutoff N) (w : TruncatedCategory D Sc cutoff N) :=
  BalancedInduction.transformLinear
    (truncatedAppendComponent_supernatural D Sc cutoff N (by
      simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)) M w

include sy hc in
/-- One exponent works on every module and every output with prescribed
successor content. Off-content source generators are zero, rather than
requiring a uniform exponent over all source contents. -/
private theorem truncatedCoendDot_pow_zero [Finite I] (ν : List I) (i : I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (M : TruncatedModules D Sc cutoff N)
      (w : TruncatedCategory D Sc cutoff N), w.word.Perm (ν ++ [i]) →
        truncatedCoendDot D Sc cutoff N i M w ^ e = 0 := by
  obtain ⟨e, he, hp⟩ := truncatedAppendDot_pow_zero D Sc cutoff sy hc N ν i
  refine ⟨e, he, fun M w hw => ?_⟩
  apply BalancedInduction.hom_ext
  intro v g m
  by_cases hv : v.word.Perm ν
  · rw [truncatedCoendDot, BalancedInduction.transformLinear_pow_tensor]
    have hz := hp v hv
    rw [truncatedAppendDot_app] at hz
    rw [hz, Limits.zero_comp]
    simp [BalancedInduction.tensor]
  · have hg : g = 0 := truncated_off_content D Sc cutoff N (f := g) (by
      change ¬ w.word.Perm (v.word ++ [i])
      intro h
      have he : (v.word : Multiset I) + ([i] : Multiset I) =
          (ν : Multiset I) + ([i] : Multiset I) :=
        Multiset.coe_eq_coe.mpr (h.symm.trans hw)
      exact hv (Multiset.coe_eq_coe.mp (add_right_cancel he)))
    rw [hg, BalancedInduction.tensor_zero_left, map_zero]
    rfl

private theorem restriction_descent_eq
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    weightedRestriction D Sc cutoff N (weightedModule D Sc cutoff N M hM) = M := by
  apply Superfunctor.ext
  apply Functor.hext
    (F := (weightedRestriction D Sc cutoff N (weightedModule D Sc cutoff N M hM)).toFunctor)
    (G := M.toFunctor) (fun _ => rfl)
  intro v w f
  exact heq_of_eq (weightedRestrictionModule_map D Sc cutoff N M hM v w f)

private theorem nilpotent_of_injective_intertwiner
    {U V : Type u} [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    (f : U →ₗ[k] V) (hf : Function.Injective f)
    (a : Module.End k U) (b : Module.End k V) (h : f.comp a = b.comp f)
    (n : ℕ) (hb : b ^ n = 0) : a ^ n = 0 := by
  have hpow := Module.End.commute_pow_left_of_commute h.symm n
  rw [hb, LinearMap.zero_comp] at hpow
  apply LinearMap.ext
  intro z
  apply hf
  have hv := LinearMap.congr_fun hpow z
  simpa only [LinearMap.zero_apply, LinearMap.comp_apply, map_zero] using hv.symm

include sy hc in
private theorem weightedRestrictedInductionDot_pow_zero [Finite I] (ν : List I) (i : I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (T : TruncatedModules D Sc cutoff N)
      (w : OldCategory D Sc cutoff), w.word.Perm (ν ++ [i]) →
        actualInductionDot D Sc cutoff i (weightedRestriction D Sc cutoff N T) w ^ e = 0 := by
  obtain ⟨e, he, hp⟩ := truncatedCoendDot_pow_zero D Sc cutoff sy hc N ν i
  refine ⟨e, he, fun T w hw => ?_⟩
  let R := weightedRestriction D Sc cutoff N T
  let Q := oldTruncateFunctor D Sc cutoff N
  let A : TruncatedModules D Sc cutoff N := weightedInducedModule D Sc cutoff N i R
    (weightedRestriction_kills D Sc cutoff N T)
  let B : TruncatedModules D Sc cutoff N :=
    BalancedInduction.induced (truncatedAppend D Sc cutoff N [i]) T
  let eIso : A ≅ B := appendWeightedModuleIso D Sc cutoff N i T
  let E : A.obj (Q.obj w) ≃ₗ[k] B.obj (Q.obj w) :=
    moduleIsoLinearEquiv (k := k) eIso (Q.obj w)
  let da : Module.End k (A.obj (Q.obj w)) := actualInductionDot D Sc cutoff i R w
  let db : Module.End k (B.obj (Q.obj w)) := truncatedCoendDot D Sc cutoff N i T (Q.obj w)
  have h := appendWeightedModuleIso_hom_dot D Sc cutoff N i T w
  have hE : E.toLinearMap.comp da = db.comp E.toLinearMap := by
    dsimp only [E, moduleIsoLinearEquiv, eIso, da, db, Q]
    dsimp only [weightedAppendComparisonLinear, Q] at h
    exact h
  have hb : db ^ e = 0 := hp T (Q.obj w) hw
  have ha := nilpotent_of_injective_intertwiner E.toLinearMap E.injective da db hE e hb
  change da ^ e = 0
  exact ha

include sy hc in
/-- The existing signed old coend dot has the fixed-content exponent on
modules annihilated by the weighted coefficient ideal. The chosen weighted
comparison is used only as an invertible intertwiner. -/
theorem weightedOldInductionDot_pow_zero [Finite I] (ν : List I) (i : I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)),
      KillsWeightedCoefficients D Sc cutoff N M →
      ∀ (w : OldCategory D Sc cutoff), w.word.Perm (ν ++ [i]) →
        actualInductionDot D Sc cutoff i M w ^ e = 0 := by
  obtain ⟨e, he, hp⟩ := weightedRestrictedInductionDot_pow_zero D Sc cutoff sy hc N ν i
  refine ⟨e, he, fun M hM w hw => ?_⟩
  have hz := hp (weightedModule D Sc cutoff N M hM) w hw
  have hR := restriction_descent_eq D Sc cutoff N M hM
  exact Eq.mp (congrArg (fun P : Superfunctor k (OldCategory D Sc cutoff) (SVec k) =>
    actualInductionDot D Sc cutoff i P w ^ e = 0) hR) hz

variable [Fintype I]
include sy hc in
/-- The literal power-annihilated old modules have locally nilpotent signed
induction dots, with one positive exponent at each fixed output content.
The exponent is independent of the module and no power ideal is replaced. -/
theorem coefficientPowerInductionDot_pow_zero (L : I × ℕ → ℕ)
    (ν : List I) (i : I) :
    ∃ e : ℕ, 0 < e ∧ ∀ M : CoefficientPowerModules D Sc cutoff
        (elementaryCoefficients (k := k) D cutoff) L,
      ∀ (w : OldCategory D Sc cutoff), w.word.Perm (ν ++ [i]) →
        actualInductionDot D Sc cutoff i M.obj w ^ e = 0 := by
  obtain ⟨e, he, hp⟩ := weightedOldInductionDot_pow_zero D Sc cutoff sy hc
    (SKM.SYM.elvPowerWeightBound D cutoff L + 1) ν i
  refine ⟨e, he, fun M w hw => hp M.obj ?_ w hw⟩
  exact (coefficientWeightedIdeal_le_annihilator_iff D Sc cutoff _ M.obj).mp
    ((weighted_le_elementaryPowerIdeal D cutoff L).trans M.property)

end OddMath.QuiverHecke.ELVOld
