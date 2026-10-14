/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQReverseHom

/-!
# Linearity and grading of the inverse hom functors

The hom functors of `G_q` are additive, `k`-linear, superfunctors and preserve degrees.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

instance chevalleyQReverseHom_additive
    (c d : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) :
    (chevalleyQReverseHom c d).Additive where
  map_add {f g η θ} := by
    change (chevQHomGradedEquivalence (negWeight c.unop.as)
      (negWeight d.unop.as)).inverse.map ((chevalleyQReverseTransport c d).map (η + θ)) = _
    have ht := (chevQEndpointTransport_additive (chevQ_negWeight_square c.unop.as).symm
      (chevQ_negWeight_square d.unop.as).symm).map_add (f := η) (g := θ)
    change (chevalleyQReverseTransport c d).map (η + θ) = _ at ht
    rw [ht]
    exact (chevQHomGradedEquivalence (negWeight c.unop.as)
      (negWeight d.unop.as)).inverse_additive.map_add

instance chevalleyQReverseHom_linear
    (c d : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) :
    (chevalleyQReverseHom c d).Linear k where
  map_smul η r := by
    change (chevQHomGradedEquivalence (negWeight c.unop.as)
      (negWeight d.unop.as)).inverse.map ((chevalleyQReverseTransport c d).map (r • η)) = _
    have ht := (chevQEndpointTransport_linear (chevQ_negWeight_square c.unop.as).symm
      (chevQ_negWeight_square d.unop.as).symm).map_smul η r
    change (chevalleyQReverseTransport c d).map (r • η) = _ at ht
    rw [ht]
    exact (chevQHomGradedEquivalence (negWeight c.unop.as)
      (negWeight d.unop.as)).inverse_linear.map_smul _ r

instance chevalleyQReverseHom_super
    (c d : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) :
    IsSuperfunctor k (chevalleyQReverseHom c d) where
  map_mem h := chevalleyQReverseHom_mem_parity h

instance chevalleyQReverseHom_graded
    (c d : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) :
    IsGradedSuperfunctor k (chevalleyQReverseHom c d) where
  map_mem_degree h := chevalleyQReverseHom_mem_degree h

end OddMath.SKM
