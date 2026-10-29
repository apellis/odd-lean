/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendBalance

/-!
# Descent of the full ELV old-generator map

Precomposition by the prescribed crossing word followed by the full ELV relation
maps the prepend-old relation span into the append-old relation span. This gives
P between the two old-only quotients. No injectivity, exactness, or polynomial
module linearity is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The prescribed morphism carries an inserted old ideal element into the append span. -/
theorem appendW_insert_ideal (i : I) {v t : List I}
    {r : hom D Sc cutoff v t} (hr : r ∈ ideal D Sc cutoff v t) :
    appendW D Sc cutoff i v ≫ insert D Sc cutoff i v t r ∈
      appendRelations D Sc cutoff i v (i :: t) := by
  have he := appendError_mem_appendRelations D Sc cutoff i
    (twist k (appendQ D cutoff i v) r)
  rw [appendError_apply, twist_twist] at he
  have hi := appendRelations_mem D Sc cutoff i
    (twist_ideal D Sc cutoff (appendQ D cutoff i v) hr) (appendW D Sc cutoff i t)
  have h := Submodule.sub_mem (appendRelations D Sc cutoff i v (i :: t)) hi he
  simpa only [sub_sub_cancel] using h

/-- All old composites and ambient continuations are respected by the prescribed map. -/
theorem appendW_relations (i : I) {v w : List I}
    {h : hom D Sc cutoff (i :: v) w} (hh : h ∈ relations D Sc cutoff i v w) :
    appendW D Sc cutoff i v ≫ h ∈ appendRelations D Sc cutoff i v w := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨t, r, hr, a, rfl⟩ := hh
    rw [← Category.assoc]
    exact appendRelations_comp D Sc cutoff i (appendW_insert_ideal D Sc cutoff i hr) a
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Preadditive.comp_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [Linear.comp_smul]
    exact Submodule.smul_mem _ c ha

/-- P on old-only quotient coordinates, with the prescribed W and no balance hypothesis. -/
def pMap (i : I) (v w : List I) :
    Target D Sc cutoff i v w →ₗ[k] AppendTarget D Sc cutoff i v w :=
  (relations D Sc cutoff i v w).mapQ (appendRelations D Sc cutoff i v w)
    (Linear.leftComp k _ (appendW D Sc cutoff i v))
    (fun _ hh => appendW_relations D Sc cutoff i hh)

/-- The descended map is precomposition by W, not an unspecified quotient lift. -/
@[simp] theorem pMap_projection (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w) :
    pMap D Sc cutoff i v w (projection D Sc cutoff i v w h) =
      appendProjection D Sc cutoff i v w
        ((affineUnit D Sc cutoff (v ++ [i]) (i :: v) (lastToFirstHom D Sc i v) ≫
          relation D Sc cutoff i v) ≫ h) := rfl

end OddMath.QuiverHecke.ELVOld
