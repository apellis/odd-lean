/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedAppendTransform
import StringDiagrams.Super.SVec

/-! # Restriction on ELV supermodules

The all-supermodule target is the superfunctor category from the truncated
ELV category to `SVec k`. Restriction along right append and evaluation of
its homogeneous transformations are constructed, including naturality
against odd module maps. This supplies the restriction side of
`DeformedActionAssembly.md` §5. Induction, its adjunction, integer grading,
and the normalized factor action remain separate constructions.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Parity-graded modules on the coefficient-truncated ELV category. -/
abbrev TruncatedModules :=
  Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec.{u} k)

/-- Restriction along right append, on all supernatural module maps. -/
def moduleRestriction (σ : List I) :
    TruncatedModules D Sc cutoff N ⥤ TruncatedModules D Sc cutoff N where
  obj M := (⟨truncatedAppend D Sc cutoff N σ⟩ :
    Superfunctor k (TruncatedCategory D Sc cutoff N) (TruncatedCategory D Sc cutoff N)).comp M
  map f := Superfunctor.whiskerLeft ⟨truncatedAppend D Sc cutoff N σ⟩ f
  map_id M := Superfunctor.whiskerLeft_id _ M
  map_comp f g := Superfunctor.whiskerLeft_comp _ f g

instance moduleRestriction_additive (σ : List I) :
    (moduleRestriction D Sc cutoff N σ).Additive where
  map_add := Superfunctor.whiskerLeft_add _ _ _

instance moduleRestriction_linear (σ : List I) :
    (moduleRestriction D Sc cutoff N σ).Linear k where
  map_smul f c := Superfunctor.whiskerLeft_smul _ c f

instance moduleRestriction_super (σ : List I) :
    IsSuperfunctor k (moduleRestriction D Sc cutoff N σ) where
  map_mem := Superfunctor.whiskerLeft_mem _

end OddMath.QuiverHecke.ELVOld
