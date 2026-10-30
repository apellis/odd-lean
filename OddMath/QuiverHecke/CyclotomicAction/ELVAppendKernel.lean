/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedAppend

/-! # Graded endomorphism kernels of full ELV right append

The append functor supplies an algebra map on the actual truncated word
endomorphisms. Restricting either action of its target regular bimodule gives
the induction and restriction kernels for this map, with their independent
integer and total super gradings. These are word corners, not an assertion
of the all-content cyclotomic local inversion or a support bound.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Right append on the ordinary endomorphism algebras, retaining reverse
categorical composition as multiplication. -/
def truncatedAppendAlgHom (v σ : List I) :
    TruncatedEnd D Sc cutoff N v →ₐ[k] TruncatedEnd D Sc cutoff N (v ++ σ) where
  toFun := (truncatedAppend D Sc cutoff N σ).map
  map_one' := (truncatedAppend D Sc cutoff N σ).map_id _
  map_mul' f g := (truncatedAppend D Sc cutoff N σ).map_comp g f
  map_zero' := (truncatedAppend D Sc cutoff N σ).map_zero _ _
  map_add' := fun _ _ => (truncatedAppend D Sc cutoff N σ).map_add
  commutes' c := by
    change (truncatedAppend D Sc cutoff N σ).map (c • 𝟙 _) = c • 𝟙 _
    rw [Functor.map_smul, (truncatedAppend D Sc cutoff N σ).map_id]

/-- Append preserves total coefficient-plus-diagram parity. -/
theorem truncatedAppendAlgHom_mem_parity (v σ : List I) {p : ZMod 2}
    {a : TruncatedEnd D Sc cutoff N v} (ha : a ∈ truncatedEndParity D Sc cutoff N v p) :
    truncatedAppendAlgHom D Sc cutoff N v σ a ∈
      truncatedEndParity D Sc cutoff N (v ++ σ) p :=
  IsSuperfunctor.map_mem (R := k) (F := truncatedAppend D Sc cutoff N σ) ha

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- Append preserves integer degree, separately from parity. -/
theorem truncatedAppendAlgHom_mem_degree (v σ : List I) {d : ℤ}
    {a : TruncatedEnd D Sc cutoff N v}
    (ha : a ∈ truncatedEndDegree D Sc cutoff N sy hc v d) :
    truncatedAppendAlgHom D Sc cutoff N v σ a ∈
      truncatedEndDegree D Sc cutoff N sy hc (v ++ σ) d :=
  truncatedAppend_mem_degree D Sc cutoff N sy hc σ ha

/-- The induction word corner, with ordinary right action through append. -/
def truncatedAppendInduction (v σ : List I) :
    GradedSuperBimodule (truncatedEndGSuperAlg D Sc cutoff N sy hc (v ++ σ)).gsa
      (truncatedEndGSuperAlg D Sc cutoff N sy hc v).gsa := by
  let A := truncatedEndGSuperAlg D Sc cutoff N sy hc (v ++ σ)
  let R := GradedSuperBimodule.regular A.gsa
  let f := truncatedAppendAlgHom D Sc cutoff N v σ
  exact
    { toSuperBimodule :=
        { toSVec := R.toSuperBimodule.toSVec
          lact := R.toSuperBimodule.lact
          ract := R.toSuperBimodule.ract.comp f.toLinearMap
          lact_one := R.toSuperBimodule.lact_one
          lact_mul := R.toSuperBimodule.lact_mul
          ract_one := by
            change R.toSuperBimodule.ract (f 1) = _
            rw [map_one, R.toSuperBimodule.ract_one]
          ract_mul := fun a b => by
            change R.toSuperBimodule.ract (f (a * b)) = _
            rw [map_mul, R.toSuperBimodule.ract_mul]
            rfl
          lact_ract := fun a b => R.toSuperBimodule.lact_ract a (f b)
          lact_mem := R.toSuperBimodule.lact_mem
          ract_mem := fun p a ha => R.toSuperBimodule.ract_mem p (f a)
            (truncatedAppendAlgHom_mem_parity D Sc cutoff N v σ ha) }
      deg := R.deg
      isInternal_deg := R.isInternal_deg
      odd_mem := R.odd_mem
      lact_mem := R.lact_mem
      ract_mem := fun {_ _} ha {_ _} hm => R.ract_mem
        (truncatedAppendAlgHom_mem_degree D Sc cutoff N sy hc v σ ha) hm }

/-- The restriction word corner, with left action through append. -/
def truncatedAppendRestriction (v σ : List I) :
    GradedSuperBimodule (truncatedEndGSuperAlg D Sc cutoff N sy hc v).gsa
      (truncatedEndGSuperAlg D Sc cutoff N sy hc (v ++ σ)).gsa := by
  let A := truncatedEndGSuperAlg D Sc cutoff N sy hc (v ++ σ)
  let R := GradedSuperBimodule.regular A.gsa
  let f := truncatedAppendAlgHom D Sc cutoff N v σ
  exact
    { toSuperBimodule :=
        { toSVec := R.toSuperBimodule.toSVec
          lact := R.toSuperBimodule.lact.comp f.toLinearMap
          ract := R.toSuperBimodule.ract
          lact_one := by
            change R.toSuperBimodule.lact (f 1) = _
            rw [map_one, R.toSuperBimodule.lact_one]
          lact_mul := fun a b => by
            change R.toSuperBimodule.lact (f (a * b)) = _
            rw [map_mul, R.toSuperBimodule.lact_mul]
            rfl
          ract_one := R.toSuperBimodule.ract_one
          ract_mul := R.toSuperBimodule.ract_mul
          lact_ract := fun a b => R.toSuperBimodule.lact_ract (f a) b
          lact_mem := fun p a ha => R.toSuperBimodule.lact_mem p (f a)
            (truncatedAppendAlgHom_mem_parity D Sc cutoff N v σ ha)
          ract_mem := R.toSuperBimodule.ract_mem }
      deg := R.deg
      isInternal_deg := R.isInternal_deg
      odd_mem := R.odd_mem
      lact_mem := fun {_ _} ha {_ _} hm => R.lact_mem
        (truncatedAppendAlgHom_mem_degree D Sc cutoff N sy hc v σ ha) hm
      ract_mem := R.ract_mem }

/-- The right action on the induction corner is the prescribed appended
endomorphism, with no replacement of the coefficient superalgebra by scalars. -/
@[simp] theorem truncatedAppendInduction_ract (v σ : List I)
    (a : TruncatedEnd D Sc cutoff N v)
    (z : TruncatedEnd D Sc cutoff N (v ++ σ)) :
    (truncatedAppendInduction D Sc cutoff N sy hc v σ).toSuperBimodule.ract a z =
      z * truncatedAppendAlgHom D Sc cutoff N v σ a := rfl

/-- The left action on restriction uses the same append map. -/
@[simp] theorem truncatedAppendRestriction_lact (v σ : List I)
    (a : TruncatedEnd D Sc cutoff N v)
    (z : TruncatedEnd D Sc cutoff N (v ++ σ)) :
    (truncatedAppendRestriction D Sc cutoff N sy hc v σ).toSuperBimodule.lact a z =
      truncatedAppendAlgHom D Sc cutoff N v σ a * z := rfl

end OddMath.QuiverHecke.ELVOld
