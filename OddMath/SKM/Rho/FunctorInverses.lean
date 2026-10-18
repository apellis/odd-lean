import OddMath.SKM.Rho.MapInverses
import OddMath.SKM.Rho.InverseComparisons
import StringDiagrams.Super.TwoEnvelopeEquivalence

/-!
# Functor Inverses for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
Both literal TwoSuperfunctor inverse identities compare all five data fields:
obj, map, map₂, mapComp and mapId. They use the corrected +t odd–odd crossing,
the +t odd dot, and zero added F parity shift.
-/

noncomputable section
namespace OddMath.SKM.RhoFunctorLaws
open CategoryTheory StringDiagrams BicategoryStruct RhoExtension RhoInverse
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

private theorem transport_heq {C : Type*} [Category C] {x' y' x y : C}
    (hx : x' = x) (hy : y' = y) (η : x ⟶ y) :
    HEq (eqToHom hx ≫ η ≫ eqToHom hy.symm) η := by
  cases hx
  cases hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

private theorem equalityIso_heq_refl {C : Type*} [Category C] {x y z : C}
    (h : x = y) (e : y = z) : HEq (eqToIso h) (Iso.refl z) := by
  cases e
  cases h
  rfl

theorem rhoEnvelope_comp_inverse (t : k) (ht : t ^ 2 = -1) :
    (rhoEnvelope (sy := sy) (hc := hc) t ht).comp (rhoInverse t ht) =
      TwoSuperfunctor.id k (Uqπ D Sc sy hc) := by
  apply TwoEnvelope.twoSuperfunctor_ext
    (F := (rhoEnvelope t ht).comp (rhoInverse t ht))
    (G := TwoSuperfunctor.id k (Uqπ D Sc sy hc)) rfl
  · apply heq_of_eq
    funext a b f
    exact rhoInverse_rho_map t ht f
  · apply Function.hfunext rfl; intro a a' ha; cases ha
    apply Function.hfunext rfl; intro b b' hb; cases hb
    apply Function.hfunext rfl; intro f f' hf; cases hf
    apply Function.hfunext rfl; intro g g' hg; cases hg
    apply Function.hfunext rfl; intro η η' hη; cases hη
    exact (heq_of_eq (RhoMapInverses.rhoForwardInverse_map₂ t ht η)).trans
      (transport_heq (rhoInverse_rho_map t ht f) (rhoInverse_rho_map t ht g) η)
  · apply Function.hfunext rfl; intro a a' ha; cases ha
    apply Function.hfunext rfl; intro b b' hb; cases hb
    apply Function.hfunext rfl; intro c c' hc'; cases hc'
    apply Function.hfunext rfl; intro f f' hf; cases hf
    apply Function.hfunext rfl; intro g g' hg; cases hg
    rw [rhoForwardInverse_mapComp]
    exact equalityIso_heq_refl _ (rhoInverse_rho_map t ht (f ≫ g))
  · apply Function.hfunext rfl; intro a a' ha; cases ha
    rw [rhoForwardInverse_mapId]
    exact equalityIso_heq_refl _ (rhoInverse_rho_map t ht (𝟙 a))

theorem rhoInverse_comp_envelope (t : k) (ht : t ^ 2 = -1) :
    (rhoInverse (sy := sy) (hc := hc) t ht).comp (rhoEnvelope t ht) =
      TwoSuperfunctor.id k (TwoSRev k (Uqπ D Sc sy hc)) := by
  apply TwoEnvelope.twoSuperfunctor_ext
    (F := (rhoInverse t ht).comp (rhoEnvelope t ht))
    (G := TwoSuperfunctor.id k (TwoSRev k (Uqπ D Sc sy hc))) rfl
  · apply heq_of_eq
    funext a b f
    exact rho_rhoInverse_map t ht f
  · apply Function.hfunext rfl; intro a a' ha; cases ha
    apply Function.hfunext rfl; intro b b' hb; cases hb
    apply Function.hfunext rfl; intro f f' hf; cases hf
    apply Function.hfunext rfl; intro g g' hg; cases hg
    apply Function.hfunext rfl; intro η η' hη; cases hη
    exact (heq_of_eq (RhoMapInverses.rhoInverseForward_map₂ t ht η)).trans
      (transport_heq (rho_rhoInverse_map t ht f) (rho_rhoInverse_map t ht g) η)
  · apply Function.hfunext rfl; intro a a' ha; cases ha
    apply Function.hfunext rfl; intro b b' hb; cases hb
    apply Function.hfunext rfl; intro c c' hc'; cases hc'
    apply Function.hfunext rfl; intro f f' hf; cases hf
    apply Function.hfunext rfl; intro g g' hg; cases hg
    rw [rhoInverseForward_mapComp]
    exact equalityIso_heq_refl _ (rho_rhoInverse_map t ht (f ≫ g))
  · apply Function.hfunext rfl; intro a a' ha; cases ha
    rw [rhoInverseForward_mapId]
    exact equalityIso_heq_refl _ (rho_rhoInverse_map t ht (𝟙 a))

end OddMath.SKM.RhoFunctorLaws
