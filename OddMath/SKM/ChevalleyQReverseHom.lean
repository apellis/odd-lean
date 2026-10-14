/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQTwoGraded

/-!
# The inverse of `ω_q` on hom categories

The graded hom functors of the inverse `G_q : 𝔘_q(𝔤)^{sop} → 𝔘_q(𝔤)` of the `Q`-envelope `ω_q = chevalleyQTwo` of the Chevalley involution, at arbitrary weights: the inverse of `chevHomGradedEquivalence` composed with transport along `-(-λ) = λ`.

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

/-- The weight negation is involutive as an equality of objects. -/
theorem chevQ_negWeight_square (a : UGr D Sc sy hc) : negWeight (negWeight a) = a := by
  apply Presentation.Bicat.ext
  exact neg_neg (show X from a.region)

/-- Transport the super-opposite Q-hom category along endpoint equalities. -/
def chevQEndpointTransport {a b a' b' : UGr D Sc sy hc} (p : a = a') (q : b = b') :
    SOp k (QEnvelope k (a ⟶ b)) ⥤ SOp k (QEnvelope k (a' ⟶ b')) := by
  subst a' b'
  exact 𝟭 _

instance chevQEndpointTransport_additive {a b a' b' : UGr D Sc sy hc}
    (p : a = a') (q : b = b') : (chevQEndpointTransport p q).Additive := by
  subst a' b'
  exact inferInstanceAs (𝟭 (SOp k (QEnvelope k (a ⟶ b)))).Additive

instance chevQEndpointTransport_linear {a b a' b' : UGr D Sc sy hc}
    (p : a = a') (q : b = b') : (chevQEndpointTransport p q).Linear k := by
  subst a' b'
  exact inferInstanceAs ((𝟭 (SOp k (QEnvelope k (a ⟶ b)))).Linear k)

instance chevQEndpointTransport_graded {a b a' b' : UGr D Sc sy hc}
    (p : a = a') (q : b = b') : IsGradedSuperfunctor k (chevQEndpointTransport p q) := by
  subst a' b'
  exact inferInstanceAs (IsGradedSuperfunctor k (𝟭 (SOp k (QEnvelope k (a ⟶ b)))))

/-- Explicit reverse object, not a choice from essential surjectivity. -/
def chevalleyQReverseObj (c : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) :
    QTwoEnvelope k (UGr D Sc sy hc) := ⟨negWeight c.unop.as⟩

/-- The forward functor returns the target weight exactly. -/
theorem chevalleyQReverseObj_forward (c : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) :
    chevalleyQTwo.obj (chevalleyQReverseObj c) = c := by
  apply congrArg TwoSOp.mk
  apply QTwoEnvelope.ext
  exact chevQ_negWeight_square c.unop.as

/-- Canonical double-negation transport into the inverse's domain. -/
def chevalleyQReverseTransport (c d : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) :
    (c ⟶ d) ⥤
      SOp k (QEnvelope k (negWeight (negWeight c.unop.as) ⟶
        negWeight (negWeight d.unop.as))) :=
  chevQEndpointTransport (chevQ_negWeight_square c.unop.as).symm
    (chevQ_negWeight_square d.unop.as).symm

/-- Graded reverse hom functor at arbitrary target weights. -/
def chevalleyQReverseHom (c d : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) :
    (c ⟶ d) ⥤ (chevalleyQReverseObj c ⟶ chevalleyQReverseObj d) :=
  chevalleyQReverseTransport c d ⋙
    (chevQHomGradedEquivalence (negWeight c.unop.as) (negWeight d.unop.as)).inverse

/-- Degree preservation for the reverse on arbitrary target weights. -/
theorem chevalleyQReverseHom_mem_degree
    {c d : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))} {f g : c ⟶ d}
    {n : ℤ} {η : f ⟶ g} (h : η ∈ degree (R := k) f g n) :
    (chevalleyQReverseHom c d).map η ∈ degree (R := k) _ _ n := by
  apply (chevQHomGradedEquivalence (negWeight c.unop.as)
    (negWeight d.unop.as)).inverse_isGraded.map_mem_degree
  exact (chevQEndpointTransport_graded (chevQ_negWeight_square c.unop.as).symm
    (chevQ_negWeight_square d.unop.as).symm).map_mem_degree h

/-- Parity preservation for the same reverse. -/
theorem chevalleyQReverseHom_mem_parity
    {c d : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))} {f g : c ⟶ d}
    {p : ZMod 2} {η : f ⟶ g} (h : η ∈ parity (R := k) f g p) :
    (chevalleyQReverseHom c d).map η ∈ parity (R := k) _ _ p := by
  apply (chevQHomGradedEquivalence (negWeight c.unop.as)
    (negWeight d.unop.as)).inverse_isSuperfunctor.map_mem
  exact (chevQEndpointTransport_graded (chevQ_negWeight_square c.unop.as).symm
    (chevQ_negWeight_square d.unop.as).symm).map_mem h

/-- Counit at an arbitrary target arrow, with its canonical endpoint transport. -/
def chevalleyQReverseHomCounit {c d : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))}
    (f : c ⟶ d) :
    chevalleyQTwo.map ((chevalleyQReverseHom c d).obj f) ≅
      (chevalleyQReverseTransport c d).obj f :=
  (chevQHomGradedEquivalence (negWeight c.unop.as) (negWeight d.unop.as)).counitIso.app
    ((chevalleyQReverseTransport c d).obj f)

/-- The transported counit has degree zero, without any new hypothesis. -/
theorem chevalleyQReverseHomCounit_degree
    {c d : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))} (f : c ⟶ d) :
    (chevalleyQReverseHomCounit f).hom ∈ degree (R := k) _ _ 0 :=
  (chevQHomGradedEquivalence (negWeight c.unop.as) (negWeight d.unop.as)).counitIso_mem_degree
    ((chevalleyQReverseTransport c d).obj f)

/-- The transported counit is even on every arrow. -/
theorem chevalleyQReverseHomCounit_even
    {c d : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))} (f : c ⟶ d) :
    (chevalleyQReverseHomCounit f).hom ∈ parity (R := k) _ _ 0 :=
  (chevQHomGradedEquivalence (negWeight c.unop.as) (negWeight d.unop.as)).counitIso_mem
    ((chevalleyQReverseTransport c d).obj f)

/-- Counit naturality on arbitrary morphisms, not just homogeneous components. -/
theorem chevalleyQReverseHomCounit_naturality
    {c d : TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))} {f g : c ⟶ d} (η : f ⟶ g) :
    chevalleyQTwo.map₂ ((chevalleyQReverseHom c d).map η) ≫
      (chevalleyQReverseHomCounit g).hom =
    (chevalleyQReverseHomCounit f).hom ≫ (chevalleyQReverseTransport c d).map η :=
  (chevQHomGradedEquivalence (negWeight c.unop.as) (negWeight d.unop.as)).counitIso.hom.naturality
    ((chevalleyQReverseTransport c d).map η)
end OddMath.SKM
