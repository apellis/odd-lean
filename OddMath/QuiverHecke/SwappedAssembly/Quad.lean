/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Zigzag

/-! # The quadratic relations in the swapped layer representation

The relations `quadEq`, `quadZero` and `quadNe` of `OddMath.SKM.Presentation` are (1.7) of
Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5: the square
of the upward crossing `τ : Eᵢ Eⱼ → Eⱼ Eᵢ` followed by `τ : Eⱼ Eᵢ → Eᵢ Eⱼ` is `0` for `i = j`,
`t_ij` for `d_ij = 0`, and the parameter polynomial `Q_ij` in the dots otherwise.

In the swapped layer representation each relation is one matrix identity per pair of
summand paths `p`, `q` of the word `Eᵢ Eⱼ` and object `Z`. The entry of the two-crossing
diagram is the matrix product `crossCross`: the sum over the summand paths `m` of `Eⱼ Eᵢ` of the
two crossing entries (`compList_crossCross`). The entries of the dots on one strand of a
two-letter word are the dot image on that strand, conjugated by the comparison of the path
functor of the word with the composite of the path functors of its letters (`leftDot`,
`rightDot`, `compDiag_dotsLeft`, `compDiag_dotsRight`).

`CrossQuad gens` states the three matrix identities; `quadRelations` derives
`QuadRelations` from it.

Main declarations: `ProbeReservoir.compLayer_eq_of_path`, `ProbeReservoir.crossCross`,
`ProbeReservoir.CrossQuad`, `ProbeReservoir.quadRelations`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u

variable {I X : Type u}

namespace SPath

/-- Appending the empty path to a path of a two-letter word. -/
theorem append_nil_pair {c₁ c₂ : Col I X} {s t : Sector I} (p : SPath [c₁, c₂] s t) :
    p.append (.nil t) = p := by
  cases p with
  | cons _ _ _ _ p =>
    cases p with
    | cons _ _ _ _ p =>
      cases p
      rfl

end SPath

variable [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable {P : ProbeReservoir k B D Sc}

/-- **The entry of a layer at paths with given decompositions**: the image of the generator
in the middle, conjugated by the comparisons of the path functors. -/
theorem compLayer_eq_of_path (gens : P.Generators) (L : Layer (SKM.sig D))
    {s x y t : Sector I} (pu : SPath L.left s x) (pg : SPath ((SKM.sig D).dom L.gen) x y)
    (qg : SPath ((SKM.sig D).cod L.gen) x y) (pv : SPath L.right y t)
    (p : SPath L.dom.word s t) (q : SPath L.cod.word s t) (hp : (pu.append pg).append pv = p)
    (hq : (pu.append qg).append pv = q) (Z : P.H t) :
    compLayer gens L p q Z =
      eqToHom (by rw [← hp, P.pathFunctor_append_append_obj]) ≫
        (P.pathFunctor pu).map (gens.image L.gen pg qg ((P.pathFunctor pv).obj Z)) ≫
        eqToHom (by rw [← hq, P.pathFunctor_append_append_obj]) := by
  subst hp hq
  exact compLayer_eq gens L pu pg qg pv Z

/-- The entry of a crossing layer without strands on either side is the crossing image. -/
theorem compLayer_cross (gens : P.Generators) (i j : I) (ν : X) {s t : Sector I}
    (p : SPath (wd D ν [up i, up j]) s t) (q : SPath (wd D ν [up j, up i]) s t) (Z : P.H t) :
    compLayer gens (SKM.lay D ν [] (SKM.Shape.cross i j) []) p q Z = gens.cross i j ν p q Z := by
  rw [compLayer_eq_of_path gens (SKM.lay D ν [] (SKM.Shape.cross i j) []) (.nil s) p q (.nil t)
    p q (SPath.append_nil_pair p)
    (SPath.append_nil_pair q) Z]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

open Classical in
/-- **The entry of two crossings** `τ : Eᵢ Eⱼ → Eⱼ Eᵢ`, then `τ : Eⱼ Eᵢ → Eᵢ Eⱼ`: the matrix
product of the two crossing images. -/
def crossCross (gens : P.Generators) (i j : I) (ν : X) {s t : Sector I}
    (p q : SPath (wd D ν [up i, up j]) s t) (Z : P.H t) :
    (P.pathFunctor p).obj Z ⟶ (P.pathFunctor q).obj Z :=
  letI : Fintype (SPath (wd D ν (SKM.Shape.cross i j).cod) s t) := Fintype.ofFinite _
  ∑ m, gens.cross i j ν p m Z ≫ gens.cross j i ν m q Z

theorem compList_crossCross (gens : P.Generators) (i j : I) (ν : X)
    (h : Chain (SKM.ob D ν [up i, up j]) (SKM.layList D ν (SKM.crossL [] i j [] ++ SKM.crossL [] j i []))
      (SKM.ob D ν [up i, up j]))
    {s t : Sector I} (p q : SPath (wd D ν [up i, up j]) s t) (Z : P.H t) :
    compList gens _ h p q Z = crossCross gens i j ν p q Z := by
  classical
  obtain ⟨hv, h₁, hc⟩ := h
  erw [compList.eq_2]
  simp only [SKM.layList, SKM.crossL, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, compList_one, SPath.cast_self, eqToHom_refl, Category.id_comp,
    Category.comp_id]
  unfold crossCross
  refine Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun m _ => ?_
  erw [compLayer_cross, compLayer_cross]

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
