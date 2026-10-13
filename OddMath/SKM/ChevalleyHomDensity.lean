/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.ChevalleyGradedHom

/-!
# Even degree-zero density of the Chevalley hom functor

`chevHom_gradedEvenlyDense` supplies an explicit original object preimage and
an even degree-zero isomorphism for every target object. It is the density
input to `chevHomGradedEquivalence`.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Supercategory GradedSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

/-- The original flipped word, with double-negated boundaries returned to their source weights. -/
def chevHomObjectPreimage {a b : UGr D Sc sy hc}
    (Y : SOp k (negWeight a ⟶ negWeight b)) : a ⟶ b where
  obj := (chevMap D).obj Y.unop.obj
  start_eq := by
    change -(show X from Y.unop.obj.start) = a.region
    rw [Y.unop.start_eq]
    exact neg_neg (show X from a.region)
  wf := (chevMap D).ok_map Y.unop.wf
  endR_eq := by
    rw [(chevMap D).obj_endR, Y.unop.endR_eq]
    exact neg_neg (show X from b.region)

/-- Surjectivity uses the actual original relabelling, not a chosen equivalent category. -/
theorem chevHom_obj_preimage {a b : UGr D Sc sy hc}
    (Y : SOp k (negWeight a ⟶ negWeight b)) :
    (chevHom a b).obj (chevHomObjectPreimage Y) = Y := by
  apply SOp.ext
  apply Presentation.Bicat.Hom.ext
  exact chevObj_square Y.unop.obj

/-- Every original target object has an even degree-zero equality isomorphism from the image. -/
theorem chevHom_gradedEvenlyDense (a b : UGr D Sc sy hc) :
    GradedEvenlyDense k (chevHom a b) := by
  intro Y
  have eq_mem {V W : SOp k (negWeight a ⟶ negWeight b)} (e : V = W) :
      (eqToIso e).hom ∈ parity (R := k) V W 0 ∧
        (eqToIso e).hom ∈ degree (R := k) V W 0 := by
    subst W
    exact ⟨id_mem V, id_mem_degree V⟩
  exact ⟨chevHomObjectPreimage Y, eqToIso (chevHom_obj_preimage Y),
    eq_mem (chevHom_obj_preimage Y)⟩

end OddMath.SKM
