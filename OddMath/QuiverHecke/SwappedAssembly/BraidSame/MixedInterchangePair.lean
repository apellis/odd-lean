/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Generators.Cross

/-! # A crossing of two probe letters passes through a pair of mixed interchanges

Equation (5A) of `docs/Nondegeneracy/ThreeStrandSectorBraid.md`, proved in
`docs/Nondegeneracy/PairedHomInterchange.md` §3, for the relation (1.9) of Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5, at `Eᵢ Eᵢ Eᵢ`.

* `homMixedInterchange_pair`: in the composite of two mixed interchanges moving two letters
  `E₁ E₂` past one shifted letter, the inner shift removal and insertion cancel ((4) there).
* `homMixedInterchange_pair_whiskerRight`: a homogeneous 2-morphism on `E₁ ≫ E₂` passes through
  this composite without sign, when the outer shifts agree: the exchanges with the outer shift
  removal (super-interchange) and insertion (naturality of the shift) cancel.
* `ProbeReservoir.preCrossSame_mixedJ_pair`: (5A) for the paths `PPR`, `PRP`, `RPP`; the outer
  content shifts `κ` and `κ + 2pᵢ` agree.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams BicategoryStruct Supercategory

universe u v w r

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b b' c d : B}

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
include k in
/-- The coherence step of the paired interchange: a 2-morphism on `E₁ ≫ E₂`, whiskered by
`Z ≫ F`, moves past the two inverse associators of the pair. -/
@[reassoc]
theorem pairAssociator_whiskerRight (E₁ : a ⟶ b) (E₂ : b ⟶ b') (Z : b' ⟶ c) (F : c ⟶ d)
    (η : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    (associator E₁ E₂ (Z ≫ F)).inv ≫ η ▷ (Z ≫ F) ≫ (associator E₁ E₂ (Z ≫ F)).hom ≫
        E₁ ◁ (associator E₂ Z F).inv ≫ (associator E₁ (E₂ ≫ Z) F).inv =
      E₁ ◁ (associator E₂ Z F).inv ≫ (associator E₁ (E₂ ≫ Z) F).inv ≫
        ((associator E₁ E₂ Z).inv ≫ η ▷ Z ≫ (associator E₁ E₂ Z).hom) ▷ F := by
  have hp : E₁ ◁ (associator E₂ Z F).inv ≫ (associator E₁ (E₂ ≫ Z) F).inv =
      (associator E₁ E₂ (Z ≫ F)).inv ≫ (associator (E₁ ≫ E₂) Z F).inv ≫
        (associator E₁ E₂ Z).hom ▷ F := by
    rw [← TwoSupercategory.pentagon_inv_assoc (R := k)]
    simp only [TwoSupercategory.inv_hom_whiskerRight (R := k), Category.comp_id]
  rw [hp, Iso.hom_inv_id_assoc, TwoSupercategory.associator_inv_naturality_left_assoc (R := k),
    TwoSupercategory.comp_whiskerRight (R := k), TwoSupercategory.comp_whiskerRight (R := k)]
  rw [TwoSupercategory.pentagon_inv_assoc (R := k)]

/-- The pair of mixed interchanges moving two letters past one reservoir letter: the inner
shift removal and insertion cancel. -/
theorem homMixedInterchange_pair (E₁ : a ⟶ b) (E₂ : b ⟶ b') (Z : b' ⟶ c) (F : c ⟶ d)
    (κ τ : ZMod 2) :
    E₁ ◁ (homMixedInterchange (k := k) E₂ F κ τ Z).hom ≫
        (homMixedInterchange (k := k) E₁ F τ κ (E₂ ≫ Z)).hom =
      E₁ ◁ E₂ ◁ ((homParityShiftDatum (k := k) κ).iso (Z ≫ F)).hom ≫
        E₁ ◁ (associator E₂ Z F).inv ≫ (associator E₁ (E₂ ≫ Z) F).inv ≫
          ((homParityShiftDatum (k := k) κ).iso ((E₁ ≫ E₂ ≫ Z) ≫ F)).inv := by
  simp only [homMixedInterchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, homPre,
    TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc,
    TwoSupercategory.whiskerLeft_inv_hom_assoc (R := k)]

/-- (5A): a homogeneous 2-morphism on the two probe letters, reassociated onto the word
`E₁ E₂ Πᵏ(Z F)`, passes through the pair of mixed interchanges with the same outer shift as
its reassociation onto `Z` followed by `F` and the shift, without sign: the two exchanges
with the outer shift removal and insertion cancel. The outer shifts `κ`, `κ'` are equal; they
are separate arguments since at two sectors they agree only propositionally. -/
theorem homMixedInterchange_pair_whiskerRight (E₁ : a ⟶ b) (E₂ : b ⟶ b') (Z : b' ⟶ c)
    (F : c ⟶ d) (κ τ κ' : ZMod 2) (hκ : κ = κ') {p : ZMod 2} {η : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}
    (hη : η ∈ parity (R := k) _ _ p) :
    ((associator E₁ E₂ ((homParityShift (k := k) κ).obj (Z ≫ F))).inv ≫
        η ▷ (homParityShift (k := k) κ).obj (Z ≫ F) ≫
          (associator E₁ E₂ ((homParityShift (k := k) κ).obj (Z ≫ F))).hom) ≫
        E₁ ◁ (homMixedInterchange (k := k) E₂ F κ τ Z).hom ≫
          (homMixedInterchange (k := k) E₁ F τ κ' (E₂ ≫ Z)).hom =
      E₁ ◁ (homMixedInterchange (k := k) E₂ F κ τ Z).hom ≫
        (homMixedInterchange (k := k) E₁ F τ κ' (E₂ ≫ Z)).hom ≫
          (homParityShift (k := k) κ').map
            (((associator E₁ E₂ Z).inv ≫ η ▷ Z ≫ (associator E₁ E₂ Z).hom) ▷ F) := by
  subst hκ
  rw [← Category.assoc (E₁ ◁ _), homMixedInterchange_pair]
  simp only [Category.assoc]
  rw [← TwoSupercategory.associator_naturality_right_assoc (R := k),
    TwoSupercategory.super_interchange_assoc (R := k) hη
      ((homParityShiftDatum (k := k) κ).hom_mem _),
    Linear.comp_smul, ← TwoSupercategory.associator_inv_naturality_right_assoc (R := k),
    pairAssociator_whiskerRight_assoc (k := k)]
  have hθ : ((associator E₁ E₂ Z).inv ≫ η ▷ Z ≫ (associator E₁ E₂ Z).hom) ▷ F ∈
      parity (R := k) _ _ p := by
    refine TwoSupercategory.whiskerRight_mem F ?_
    simpa only [zero_add, add_zero, Category.assoc] using comp_mem
      (comp_mem (inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) E₁ E₂ Z))
        (TwoSupercategory.whiskerRight_mem Z hη))
      (TwoSupercategory.associator_hom_mem (R := k) E₁ E₂ Z)
  rw [(homParityShiftDatum (k := k) κ).inv_naturality hθ]
  simp only [Linear.comp_smul, smul_smul, ← koszulSign_smul (R := k)]
  rw [koszulSign_comm κ p, koszulSign_mul_self, one_smul]

end OddMath.SKM

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory

universe u

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-- (5A) of `docs/Nondegeneracy/ThreeStrandSectorBraid.md` for the paths `PPR`, `PRP`, `RPP`
of `Eᵢ Eᵢ Eᵢ`: the probe crossing on the two left letters of `PPR` is carried by the two mixed
interchanges `PPR → PRP → RPP` to the probe crossing on the two right letters of `RPP`. -/
theorem preCrossSame_mixedJ_pair (i : I) (t : Sector I)
    (hR : StepValid (true, i) false (nextSector (true, i) true (nextSector (true, i) true t)))
    (Z : P.H (nextSector (true, i) false
      (nextSector (true, i) true (nextSector (true, i) true t)))) :
    P.preCrossSame i t ((P.step (true, i) false _ hR).obj Z) ≫
        (P.step (true, i) true t trivial).map
          (P.mixedJ i i (nextSector (true, i) true t) hR Z).hom ≫
        (P.mixedJ i i t hR ((P.step (true, i) true _ trivial).obj Z)).hom =
      (P.step (true, i) true t trivial).map
          (P.mixedJ i i (nextSector (true, i) true t) hR Z).hom ≫
        (P.mixedJ i i t hR ((P.step (true, i) true _ trivial).obj Z)).hom ≫
        (P.step (true, i) false t hR).map (P.preCrossSame i (nextSector (true, i) false t) Z) := by
  simp only [preCrossSame, mixedJ, step, homContentPreE, homContentPostE, Functor.comp_map,
    homPre, homPost, Functor.map_zsmul, Linear.smul_comp, Linear.comp_smul,
    TwoSupercategory.zsmul_whiskerRight (R := k)]
  congr 1
  refine homMixedInterchange_pair_whiskerRight (k := k) _ _ _ _ _ _ _ ?_
    (P.T.cross_mem i i _ _ _ _)
  simp only [nextSector]
  rw [homContentShift_add_single, homContentShift_add_single, add_assoc,
    SKM.zmod2_add_self, add_zero]

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
