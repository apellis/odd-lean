/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.LayerEntries

/-! # The super interchange law in the swapped layer representation

A 2-representation of the Kac–Moody 2-supercategory must respect the super interchange law
(Brundan–Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, (1.4)–(1.5), used for the
Kac–Moody 2-supercategories of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Definition 1.5): two generators `g` and `g'` placed side by side may be
applied in either order, at the cost of the Koszul sign `(-1)^{|g||g'|}`.

This file proves `InterchangeLaw` for the swapped layer representation of
`OddMath/QuiverHecke/SwappedAssembly/Matrices.lean` from the supernaturality of the generator
images (`GeneratorsSupernatural`): every matrix entry `gens.image g p p'` is a homogeneous
supernatural transformation, of the parity of `g`, between the path functors of `p` and `p'`
(`docs/Nondegeneracy/SwappedActionAssembly.md`, end of §3: "each local entry is supernatural of
its declared parity").

The entry of either composite at an output path `pu · qa · pm · qb · pr` is a double sum over
the paths `pa`, `pb` of the bottom boundaries of `g` and `g'`. Termwise, the two composites
differ by moving the component `F_{pm}(η)` of `g'` past the component `γ` of `g`, which is the
supernaturality of `γ` (`eqToHom_map_comp_exchange`). When one of the four layers is ill
formed, so is a layer of the other composite (`valid_interchange_of_valid`), and both sides
vanish.

Main declarations: `valid_interchange_of_valid`, `eqToHom_map_comp_exchange`,
`ProbeReservoir.GeneratorsSupernatural`, `ProbeReservoir.interchangeLaw`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams Supercategory OddMath.SKM

universe u uB v w

section Valid

variable {S : Signature.{u, u, u}}

/-- Exchanging the boundaries of two generators separated by `m` preserves well-formedness of
the two layers. -/
theorem valid_interchange_of_valid {s : S.Region} {l m r : List S.Colour} {g g' : S.Gen}
    {A A' B B' : List S.Colour}
    (hA' : S.ok (S.left g) A' ∧ S.endR (S.left g) A' = S.right g)
    (hB' : S.ok (S.left g') B' ∧ S.endR (S.left g') B' = S.right g')
    (hA : S.endR (S.left g) A = S.right g)
    (h1 : (⟨s, l, g, m ++ (B ++ r)⟩ : Layer S).Valid)
    (h2 : (⟨s, l ++ (A ++ m), g', r⟩ : Layer S).Valid) :
    (⟨s, l, g, m ++ (B' ++ r)⟩ : Layer S).Valid ∧
      (⟨s, l ++ (A' ++ m), g', r⟩ : Layer S).Valid := by
  obtain ⟨h1lo, h1le, h1do, h1de, h1co, h1ce, h1ro⟩ := h1
  obtain ⟨h2lo, h2le, h2do, h2de, h2co, h2ce, h2ro⟩ := h2
  simp only [Signature.ok_append, Signature.endR_append] at *
  refine ⟨⟨h1lo, h1le, h1do, h1de, h1co, h1ce, ?_⟩, ⟨?_, ?_, h2do, h2de, h2co, h2ce, h2ro⟩⟩
  all_goals
    dsimp only
    rw [h1le, hA] at h2le h2lo
    simp only [Signature.ok_append, Signature.endR_append, h1le, hA', h2le, hB'.2, h1lo,
      h1ro.1, h2ro, hB'.1, and_self]

end Valid

section Entry

variable {k : Type*} [CommRing k]

end Entry

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable {P : ProbeReservoir k B D Sc} {Gs Ys : ∀ s, P.H s}

/-- An ill-formed layer acts by zero. -/
theorem layerMap_of_not_valid (gens : P.Generators) {L : Layer (SKM.sig D)} (hL : ¬ L.Valid) :
    layerMap (Gs := Gs) (Ys := Ys) gens L = 0 := by
  ext x
  funext sl sr q
  simp only [layerMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
  unfold layerFun
  split_ifs
  rfl

omit [AddCommGroup X] in
/-- Reassociation of a concatenation of five paths. -/
theorem heq_assoc₁ {l a m b r : List (Col I X)} {s₀ s₁ s₂ s₃ s₄ s₅ : Sector I}
    (pu : SPath l s₀ s₁) (pa : SPath a s₁ s₂) (pm : SPath m s₂ s₃) (pb : SPath b s₃ s₄)
    (pr : SPath r s₄ s₅) :
    HEq (((pu.append (pa.append pm)).append pb).append pr)
      (pu.append (pa.append (pm.append (pb.append pr)))) :=
  (SPath.append_assoc_heq _ pb pr).trans ((SPath.append_assoc_heq pu _ _).trans
    (SPath.append_heq_right pu (by simp) (SPath.append_assoc_heq pa pm _)))

omit [AddCommGroup X] in
/-- Reassociation of a concatenation of five paths. -/
theorem heq_assoc₂ {l a m b r : List (Col I X)} {s₀ s₁ s₂ s₃ s₄ s₅ : Sector I}
    (pu : SPath l s₀ s₁) (pa : SPath a s₁ s₂) (pm : SPath m s₂ s₃) (pb : SPath b s₃ s₄)
    (pr : SPath r s₄ s₅) :
    HEq ((pu.append pa).append (pm.append (pb.append pr)))
      (((pu.append (pa.append pm)).append pb).append pr) :=
  (SPath.append_assoc_heq pu pa _).trans (heq_assoc₁ pu pa pm pb pr).symm

/-- The Koszul sign of an interchange is the parity sign of the product of the parities. -/
theorem interchange_sign (s : (SKM.sig D).Region) (g g' : (SKM.sig D).Gen)
    (m : List (SKM.sig D).Colour) :
    (((⟨s, g, m, g'⟩ : InterchangeData (SKM.sig D)).sign : ℤ) : k) =
      sign k (g.1.parity D * g'.1.parity D) := by
  simp only [InterchangeData.sign, SKM.sig]
  rcases parity_eq_zero_or_one (g.1.parity D) with h | h <;>
    rcases parity_eq_zero_or_one (g'.1.parity D) with h' | h' <;>
    simp [h, h', sign]

theorem layerRep_act (gens : P.Generators) (L : Layer (SKM.sig D)) :
    (P.layerRep Gs Ys gens).act L = layerMap gens L := rfl

/-- Every matrix entry of every generator image is a homogeneous supernatural transformation,
of the parity of the generator, between the functors of the two summand paths. -/
def GeneratorsSupernatural (gens : P.Generators) : Prop :=
  ∀ (g : (SKM.sig D).Gen) {t s : Sector I} (p : SPath (wd D g.2 g.1.dom) t s)
    (p' : SPath (wd D g.2 g.1.cod) t s),
    IsSupernatural k (g.1.parity D) (fun Z => gens.image g p p' Z)

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
