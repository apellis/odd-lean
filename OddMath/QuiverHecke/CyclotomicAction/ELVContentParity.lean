/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVCategoryCoefficients
import StringDiagrams.Super.PiTwo

/-! # Parity shifts on the full-ELV content module categories

The factor target in `DeformedActionAssembly.md` §5 is a product of
Pi-supercategories of full-ELV content modules. This module supplies that
structure on the existing `ContentModules`, rather than replacing those
modules by the older ordinary-polynomial module construction.

Postcomposition with the parity shift of super vector spaces and its odd
isomorphism supplies the parity shift of the entire module supercategory.
The source category need not admit a parity shift.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u v w
section Supermodules
variable {k : Type u} [CommRing k]
  {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C] [Supercategory k C]

/-- Parity shift of a module is the actual postcomposition with vector parity. -/
def supermoduleParityObj (M : Superfunctor k C (SVec.{u} k)) :
    Superfunctor k C (SVec.{u} k) :=
  M.comp (PiSCat.piHom (PiSCat.of k (SVec.{u} k)))

/-- The odd vector parity isomorphism is whiskered by the entire module. -/
def supermoduleParityIso (M : Superfunctor k C (SVec.{u} k)) :
    supermoduleParityObj M ≅ M where
  hom := Superfunctor.whiskerLeft M (PiSCat.ζHom (PiSCat.of k (SVec.{u} k))).hom
  inv := Superfunctor.whiskerLeft M (PiSCat.ζHom (PiSCat.of k (SVec.{u} k))).inv
  hom_inv_id := by
    rw [← Superfunctor.whiskerLeft_comp, Iso.hom_inv_id, Superfunctor.whiskerLeft_id]
    rfl
  inv_hom_id := by
    rw [← Superfunctor.whiskerLeft_comp, Iso.inv_hom_id, Superfunctor.whiskerLeft_id]
    rfl

theorem supermoduleParityIso_hom_mem (M : Superfunctor k C (SVec.{u} k)) :
    (supermoduleParityIso M).hom ∈ parity (R := k) (supermoduleParityObj M) M 1 :=
  Superfunctor.whiskerLeft_mem M
    (Superfunctor.IsSupernatural.toSuperNatTrans_mem
      (PiSupercategory.ζ_isSupernatural (R := k) (C := SVec.{u} k)))

/-- Full supernatural module maps, including odd maps, form a Pi-supercategory. -/
@[instance_reducible]
def supermodulePiSupercategory :
    PiSupercategory k (Superfunctor k C (SVec.{u} k)) :=
  PiSupercategory.ofIso supermoduleParityObj supermoduleParityIso
    supermoduleParityIso_hom_mem

end Supermodules

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

end OddMath.QuiverHecke.ELVOld
