/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.PiSOpBridge
import OddMath.SKM.ChevalleyQEquivalence

/-!
# The Chevalley involution on `(Q,Π)`-shifted hom categories

[BE2] J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Lemma 9.1,
Remark 9.2 and Proposition 9.3: on the hom categories of the `(Q,Π)`-envelope, `ω̃` sends `Qᵐ Πᵃ
F` to `Q⁻ᵐ Πᵃ ω(F)` and a 2-morphism `x` of parity `p` from `Πᵃ` to `Πᵇ` to `ω(x)` times the
sign `(-1)^{a(a+b)+(a+b)p}` of `PiSOp.correction` (`chevQPiHom`, `chevQPiHom_obj`). It is a
graded superequivalence (`chevQPiHomGradedEquivalence`).

The sign differs from the one displayed in Remark 9.2 by `(-1)^{a+b}`, that is, by conjugation
with the even degree-zero automorphisms `(-1)^a` of the objects `Πᵃ F`.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

/-- The Chevalley hom functor on `(Q,Π)`-envelopes. -/
def chevQPiHom (a b : UGr D Sc sy hc) :
    QPiEnvelope k (a ⟶ b) ⥤ SOp k (QPiEnvelope k (negWeight a ⟶ negWeight b)) :=
  Envelope.map k (chevQHom a b) ⋙ PiSOp.bridge

instance chevQPiHom_additive (a b : UGr D Sc sy hc) : (chevQPiHom a b).Additive :=
  inferInstanceAs (Envelope.map k (chevQHom a b) ⋙ PiSOp.bridge).Additive

instance chevQPiHom_linear (a b : UGr D Sc sy hc) : (chevQPiHom a b).Linear k :=
  inferInstanceAs ((Envelope.map k (chevQHom a b) ⋙ PiSOp.bridge).Linear k)

instance chevQPiHom_super (a b : UGr D Sc sy hc) : IsSuperfunctor k (chevQPiHom a b) :=
  inferInstanceAs (IsSuperfunctor k (Envelope.map k (chevQHom a b) ⋙ PiSOp.bridge))

instance chevQPiHom_graded (a b : UGr D Sc sy hc) : IsGradedSuperfunctor k (chevQPiHom a b) where
  map_mem_degree {X Y n f} hf := by
    apply (PiSOp.bridge_graded (R := k)).map_mem_degree
    exact (chevQHom_graded a b).map_mem_degree hf

instance chevQPiHom_full (a b : UGr D Sc sy hc) : (chevQPiHom a b).Full := by
  let : (Envelope.map k (chevQHom a b)).Full :=
    ⟨fun η => ⟨Envelope.ofHom ((chevQHom a b).preimage (Envelope.toHom η)),
      (chevQHom a b).map_preimage (Envelope.toHom η)⟩⟩
  exact inferInstanceAs (Envelope.map k (chevQHom a b) ⋙ PiSOp.bridge).Full

instance chevQPiHom_faithful (a b : UGr D Sc sy hc) : (chevQPiHom a b).Faithful := by
  let : (Envelope.map k (chevQHom a b)).Faithful :=
    ⟨fun h => (chevQHom a b).map_injective h⟩
  exact inferInstanceAs (Envelope.map k (chevQHom a b) ⋙ PiSOp.bridge).Faithful

/-- The object formula `Qᵐ Πᵃ F ↦ Q⁻ᵐ Πᵃ ω(F)`. -/
theorem chevQPiHom_obj (a b : UGr D Sc sy hc) (f : QPiEnvelope k (a ⟶ b)) :
    SOp.unop ((chevQPiHom a b).obj f) = ⟨f.par, ⟨-f.obj.shift, chevHomObj f.obj.obj⟩⟩ := rfl

/-- `chevQPiHom` is surjective on objects. -/
theorem chevQPiHom_obj_surjective (a b : UGr D Sc sy hc) :
    Function.Surjective (chevQPiHom a b).obj := by
  intro Y
  obtain ⟨f, hf⟩ := chevQHom_obj_surjective a b (SOp.mk Y.unop.obj)
  refine ⟨⟨Y.unop.par, f⟩, ?_⟩
  apply SOp.ext
  apply Envelope.ext
  · rfl
  · exact congrArg SOp.unop hf

/-- Every object of the target is an image, via an even degree-zero isomorphism. -/
theorem chevQPiHom_gradedEvenlyDense (a b : UGr D Sc sy hc) :
    GradedEvenlyDense k (chevQPiHom a b) := by
  intro Y
  obtain ⟨f, hf⟩ := chevQPiHom_obj_surjective a b Y
  subst Y
  exact ⟨f, Iso.refl _, id_mem _, id_mem_degree _⟩

/-- Each `(Q,Π)`-shifted hom functor of `ω̃` is a graded superequivalence. -/
def chevQPiHomGradedEquivalence (a b : UGr D Sc sy hc) :
    GradedSuperequivalence k (chevQPiHom a b) :=
  GradedSuperequivalence.ofFullyFaithful (chevQPiHom a b) (chevQPiHom_gradedEvenlyDense a b)
end OddMath.SKM
