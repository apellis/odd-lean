/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SwappingEntries
import OddMath.SKM.RouquierHomDistinctMixedDots

/-! # The swapping block `W_A` of the same-colour sideways crossing is invertible

The entry `W_A` of `docs/Nondegeneracy/AugmentedSectorBlocks.md` §2 of the sideways crossing
`σ = sigmaL i i : Eᵢ Fᵢ → Fᵢ Eᵢ` of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Definition 1.5, (1.11), between the summand paths `[R, P]` and `[P, R]`,
is the mate of the mixed interchange `J` under the probe adjunction: unit, `J`, counit. Up to
the transport of objects along equalities of weights, this is `homDistinctMixedPreMate`, whose
inverse is the explicit word (15) of `OddMath.SKM.homDistinctMixedPreMate_inv_products`.

## Main results

* `OddMath.SKM.isIso_homContentDistinctMixedPreMate`: the mate of `J` for the content-shifted
  precomposition adjunctions is invertible.
* `OddMath.SKM.isIso_homContentDistinctMixedPreMate_of_eq`: the same, with the unit taken at a
  weight equal to that of the counit and the objects matched along equalities.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams

universe r u v w

section Mate
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) (W : X → B) (L : RouquierLeftAdjoints (k := k) T)
  (i : I)

/-- The mate of the mixed interchange `J` for the content-shifted precomposition adjunctions
is invertible, with inverse the word (15). -/
theorem isIso_homContentDistinctMixedPreMate {muM muM' muP nuP : X}
    (h : -nuP + D.α i = -muP) (E' : W muM ⟶ W muM') (t u : ZMod 2)
    (H : homWeightSector T.obj W nuP muM) :
    IsIso (homDistinctMixedPreMate (T.E i h) E' t u (homContentPreAdjunction T W L i muM' h)
      (homContentPreAdjunction T W L i muM h) H) :=
  ⟨⟨_, homDistinctMixedPreMate_inv_products (L.adjL i h)
    (fun Y => homContentPreAdjunction_unit_app T W i muM' h L Y)
    (fun Z => homContentPreAdjunction_counit_app T W i muM h L Z) H⟩⟩

/-- The mate of `J` is invertible when the unit is taken at a weight `b'` equal to the weight
`b` of the counit, with all objects matched along equalities. -/
theorem isIso_homContentDistinctMixedPreMate_of_eq {nuP muM muM' b b' : X} (eb : b = b')
    (h : -nuP + D.α i = -b) (h' : -nuP + D.α i = -b') (E' : W muM ⟶ W muM')
    (tsh u : ZMod 2)
    {A0 A1 A2 Y A5 A6 A7 A9 A10 A15 A16 : homWeightSector T.obj W b' muM'}
    {U : homWeightSector T.obj W nuP muM'}
    {Zj V₁ : homWeightSector T.obj W b muM} {V Y₂ V' : homWeightSector T.obj W nuP muM}
    (J : (homContentPreE T W i muM' h).obj
        ((homPost (k := k) E' ⋙ homParityShift (k := k) tsh).obj Zj) ⟶
      (homPost (k := k) E' ⋙ homParityShift (k := k) u).obj
        ((homContentPreE T W i muM h).obj Zj))
    (hJ : J = (homMixedInterchange (k := k) (T.E i h) E' tsh u Zj).hom)
    (x₁ : A0 = A1) (x₂ : A1 = A2) (x₃ : A2 = Y)
    (x₄ : (homContentPreE T W i muM' h').obj Y = U)
    (x₅ : (homContentPreF T W i muM' h').obj U = A5) (x₆ : A5 = A6) (x₇ : A6 = A7)
    (x₈ : A7 = (homContentPreF T W i muM' h').obj ((homContentPreE T W i muM' h).obj
        ((homPost (k := k) E' ⋙ homParityShift (k := k) tsh).obj Zj)))
    (x₉ : (homContentPreF T W i muM' h').obj
      ((homPost (k := k) E' ⋙ homParityShift (k := k) u).obj
        ((homContentPreE T W i muM h).obj Zj)) = A9) (x₁₀ : A9 = A10)
    (x₁₁ : A10 = (homContentPreF T W i muM' h').obj
      ((homPost (k := k) E' ⋙ homParityShift (k := k) u).obj V))
    (x₁₂ : V = (homContentPreE T W i muM h).obj V₁)
    (x₁₃ : V₁ = (homContentPreF T W i muM h).obj Y₂) (x₁₄ : Y₂ = V')
    (x₁₅ : (homContentPreF T W i muM' h').obj
      ((homPost (k := k) E' ⋙ homParityShift (k := k) u).obj V') = A15) (x₁₆ : A15 = A16)
    (xY : HEq Y ((homPost (k := k) E' ⋙ homParityShift (k := k) tsh).obj Zj))
    (xZ : Zj = V₁) :
    IsIso (eqToHom x₁ ≫ eqToHom x₂ ≫ eqToHom x₃ ≫
      (homContentPreAdjunction T W L i muM' h').unit.app Y ≫
      (homContentPreF T W i muM' h').map (eqToHom x₄) ≫ eqToHom x₅ ≫ eqToHom x₆ ≫
      eqToHom x₇ ≫ eqToHom x₈ ≫ (homContentPreF T W i muM' h').map J ≫
      eqToHom x₉ ≫ eqToHom x₁₀ ≫ eqToHom x₁₁ ≫
      (homContentPreF T W i muM' h').map ((homPost (k := k) E' ⋙ homParityShift (k := k) u).map
        (eqToHom x₁₂ ≫ (homContentPreE T W i muM h).map (eqToHom x₁₃) ≫
          (homContentPreAdjunction T W L i muM h).counit.app Y₂ ≫ eqToHom x₁₄)) ≫
      eqToHom x₁₅ ≫ eqToHom x₁₆) := by
  subst eb
  obtain rfl : h' = h := rfl
  obtain rfl := eq_of_heq xY
  subst hJ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₁₆ x₁₅ x₁₄ x₁₃ xZ x₁₂ x₁₁ x₁₀
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.map_id]
  rw [← Functor.map_comp]
  erw [Category.id_comp]
  exact isIso_homContentDistinctMixedPreMate T W L i h' E' tsh u Y₂

end Mate

end OddMath.SKM
