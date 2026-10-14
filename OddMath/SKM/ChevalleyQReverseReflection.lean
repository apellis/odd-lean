/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQReverseComparisons

/-!
# Reflection of degree and parity through `ω_q`

A 2-morphism of `𝔘_q(𝔤)` has a given degree or parity once its image under the hom functor of `ω_q` does.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}
local notation "F" => chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)

/-- Degree reflection on the hom category of the global Q action. -/
theorem q_bundled_reflect_degree (a b : QTwoEnvelope k (UGr D Sc sy hc))
    {f g : a ⟶ b} {n : ℤ} {η : f ⟶ g}
    (h : (F).map₂ η ∈ degree (R := k) _ _ n) : η ∈ degree (R := k) f g n := by
  let : IsGradedSuperfunctor k ((F).mapFunctor a b) :=
    { map_mem_degree hη := chevalleyQTwo_isGraded.map₂_mem_degree hη }
  let : ((F).mapFunctor a b).Faithful :=
    inferInstanceAs (chevQHom a.as b.as).Faithful
  exact mem_degree_of_map_mem ((F).mapFunctor a b) h

/-- Parity reflection through the same bundled hom functor. -/
theorem q_bundled_reflect_parity (a b : QTwoEnvelope k (UGr D Sc sy hc))
    {f g : a ⟶ b} {t : ZMod 2} {η : f ⟶ g}
    (h : (F).map₂ η ∈ parity (R := k) _ _ t) : η ∈ parity (R := k) f g t := by
  let : ((F).mapFunctor a b).Faithful :=
    inferInstanceAs (chevQHom a.as b.as).Faithful
  exact mem_of_map_mem ((F).mapFunctor a b) h
end OddMath.SKM
