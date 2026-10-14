/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyGradedHom

/-!
# The Chevalley involution on `Q`-shifted hom categories

[BE2] J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Lemma 9.1 and
Proposition 9.3: on the hom categories of the `Q`-envelope, `ω̃` sends `Qᵐ F` to `Q⁻ᵐ ω(F)` and
acts by `ω` on 2-morphisms (`chevQHom`). The shift is negated because the target is the
super-opposite, in which the roles of `q` and `q⁻¹` are interchanged; total degree is preserved
(`chevQHom_graded`).
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

/-- The Chevalley hom functor on `Q`-envelopes, negating shifts. -/
def chevQHom (a b : UGr D Sc sy hc) :
    QEnvelope k (a ⟶ b) ⥤ SOp k (QEnvelope k (negWeight a ⟶ negWeight b)) where
  obj f := ⟨⟨-f.shift, chevHomObj f.obj⟩⟩
  map η := SOp.mk' (QEnvelope.ofHom (SOp.unsop ((chevHom a b).map (QEnvelope.toHom η))))
  map_id f := by
    apply SOp.hom_ext
    exact congrArg (SOp.unsop (C := (negWeight a ⟶ negWeight b)))
      ((chevHom a b).map_id f.obj)
  map_comp {f g h} η θ := by
    apply SOp.hom_ext
    exact congrArg (SOp.unsop (C := (negWeight a ⟶ negWeight b)))
      ((chevHom a b).map_comp (QEnvelope.toHom η) (QEnvelope.toHom θ))

instance chevQHom_additive (a b : UGr D Sc sy hc) : (chevQHom a b).Additive where
  map_add {f g} η θ := by
    apply SOp.hom_ext
    exact congrArg (SOp.unsop (C := (negWeight a ⟶ negWeight b)))
      ((chevHom a b).map_add (f := QEnvelope.toHom η)
      (g := QEnvelope.toHom θ))

instance chevQHom_linear (a b : UGr D Sc sy hc) : (chevQHom a b).Linear k where
  map_smul {f g} η r := by
    apply SOp.hom_ext
    exact congrArg (SOp.unsop (C := (negWeight a ⟶ negWeight b)))
      ((chevHom a b).map_smul r (QEnvelope.toHom η))

instance chevQHom_super (a b : UGr D Sc sy hc) : IsSuperfunctor k (chevQHom a b) where
  map_mem h := (chevHom_super a b).map_mem h

/-- Reversing the integer shift preserves total degree in the super-opposite. -/
instance chevQHom_graded (a b : UGr D Sc sy hc) : IsGradedSuperfunctor k (chevQHom a b) where
  map_mem_degree {f g n η} h := by
    change SOp.unsop ((chevHom a b).map (QEnvelope.toHom η)) ∈
      degree (R := k) (chevHomObj g.obj) (chevHomObj f.obj)
        (n + (-g.shift - -f.shift))
    rw [show n + (-g.shift - -f.shift) = n + (f.shift - g.shift) by ring]
    exact (chevHom_graded a b).map_mem_degree h

/-- The object formula `Qᵐ F ↦ Q⁻ᵐ ω(F)`. -/
theorem chevQHom_obj (a b : UGr D Sc sy hc) (f : QEnvelope k (a ⟶ b)) :
    ((chevQHom a b).obj f).unop = ⟨-f.shift, chevHomObj f.obj⟩ := rfl

/-- On 2-morphisms, `chevQHom` acts by `ω`. -/
theorem chevQHom_map {a b : UGr D Sc sy hc} {f g : QEnvelope k (a ⟶ b)} (η : f ⟶ g) :
    QEnvelope.toHom (SOp.unsop ((chevQHom a b).map η)) =
      SOp.unsop ((chevHom a b).map (QEnvelope.toHom η)) := rfl
end OddMath.SKM
