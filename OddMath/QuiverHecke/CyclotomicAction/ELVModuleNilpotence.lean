/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedNilpotence
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleAdjunction

/-! # Nilpotence on ELV modules

The quotient support theorem gives a uniform exponent for the evaluated dot
on every module at fixed content. The restriction dot is the previously
constructed supernatural transformation, including its odd naturality signs.
Evaluation on balanced induction is a special case. No integer grading of
arbitrary module-category Homs is introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ)

/-- The uniform quotient exponent works on all modules, without a support
hypothesis on those modules. Endomorphism multiplication is not reversed. -/
theorem module_positive_pow_zero [Finite I] (ν : List I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (v : List I), v.Perm ν → ∀ (d : ℤ), 0 < d →
      ∀ f : TruncatedEnd D Sc cutoff N v,
        f ∈ truncatedEndDegree D Sc cutoff N sy hc v d →
        ∀ M : TruncatedModules D Sc cutoff N,
          (M.toFunctor.mapEnd (⟨v⟩ : TruncatedCategory D Sc cutoff N) f) ^ e = 0 := by
  obtain ⟨e, he, hp⟩ := truncatedContent_positive_pow_zero D Sc cutoff sy hc N ν
  refine ⟨e, he, fun v hv d hd f hf M => ?_⟩
  rw [← map_pow, hp v hv d hd f hf]
  exact M.toFunctor.map_zero _ _

include sy hc in
/-- The existing restriction dot is nilpotent at every fixed-content component,
with an exponent independent of the module. Its supernatural signs are unchanged. -/
theorem moduleRestrictionDot_pow_zero [Finite I] (ν : List I) (i : I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (M : TruncatedModules D Sc cutoff N)
      (v : TruncatedCategory D Sc cutoff N), v.word.Perm ν →
      let f : End (M.obj ((truncatedAppend D Sc cutoff N [i]).obj v)) :=
        ((moduleRestrictionDot D Sc cutoff N i).app (D.parity i) M).app (D.parity i) v
      f ^ e = 0 := by
  obtain ⟨e, he, hp⟩ := truncatedAppendDot_pow_zero D Sc cutoff sy hc N ν i
  refine ⟨e, he, fun M v hv => ?_⟩
  dsimp only
  rw [moduleRestrictionDot, moduleRestrictionTransform_app]
  let f : TruncatedEnd D Sc cutoff N (v.word ++ [i]) :=
    (truncatedAppendDot D Sc cutoff N i).app (D.parity i) v
  have hf : f ^ e = 0 := hp v hv
  have hm := congrArg (M.toFunctor.mapEnd (⟨v.word ++ [i]⟩ : TruncatedCategory D Sc cutoff N)) hf
  rw [map_pow] at hm
  simpa only [Functor.mapEnd_apply, Functor.map_zero, f, truncatedAppendDot_app] using hm

/-- Evaluation of a positive-degree quotient endomorphism on the actual balanced
induction module. This is the target-word action, not an identification with a
normalized reservoir induction-dot transformation. -/
theorem moduleInduction_positive_pow_zero [Finite I] (ν : List I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (v : List I), v.Perm ν → ∀ (d : ℤ), 0 < d →
      ∀ f : TruncatedEnd D Sc cutoff N v,
        f ∈ truncatedEndDegree D Sc cutoff N sy hc v d →
        ∀ (σ : List I) (M : TruncatedModules D Sc cutoff N),
          (((moduleInduction D Sc cutoff N σ).obj M).toFunctor.mapEnd
            (⟨v⟩ : TruncatedCategory D Sc cutoff N) f) ^ e = 0 := by
  obtain ⟨e, he, hp⟩ := module_positive_pow_zero D Sc cutoff sy hc N ν
  exact ⟨e, he, fun v hv d hd f hf σ M => hp v hv d hd f hf
    ((moduleInduction D Sc cutoff N σ).obj M)⟩

end OddMath.QuiverHecke.ELVOld
