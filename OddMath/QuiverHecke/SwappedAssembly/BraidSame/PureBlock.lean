/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.MixedBlock

/-! # The braid relation on the probe path `PPP` of `Eᵢ Eᵢ Eᵢ`

For the relation (1.9) of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Definition 1.5, at `Eᵢ Eᵢ Eᵢ`, the path `PPP` with three probe summands is the only path to its
endpoint. On it the left and right crossings of the swapped generators are the probe crossings
`preCrossSame`, which are `-q` times the factor crossing of `T` whiskered by the remaining
object. The braid relation on `PPP` is the factor braid relation `T.braid`, whiskered on the
right and transported through the associators (`whisker_braid`, using the pentagon).

## Main results

* `ProbeReservoir.preCrossSame_braid`: the braid relation for the probe crossings.
* `ProbeReservoir.ppp_braid`: (1.9) on the path `PPP` of the colour pattern `iii`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct

universe u

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

section Whisker

/-- A braid relation between `x ⊗ 1` and `1 ⊗ y` on `E₁ E₂ E₃` survives whiskering on the
right by `Z`, with the crossings reassociated to act on `E₁ (E₂ (E₃ Z))`. -/
theorem whisker_braid (R : Type*) [CommRing R] {C : Type*} [BicategoryStruct C]
    [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
    [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C] {a b c d e : C}
    {E₁ : a ⟶ b} {E₂ : b ⟶ c} {E₃ : c ⟶ d} (Z : d ⟶ e)
    (x : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (y : E₂ ≫ E₃ ⟶ E₂ ≫ E₃)
    (hb : E₁ ◁ y ≫ ((associator E₁ E₂ E₃).inv ≫ x ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
        E₁ ◁ y =
      ((associator E₁ E₂ E₃).inv ≫ x ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ y ≫
        ((associator E₁ E₂ E₃).inv ≫ x ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    ((associator E₁ E₂ (E₃ ≫ Z)).inv ≫ x ▷ (E₃ ≫ Z) ≫ (associator E₁ E₂ (E₃ ≫ Z)).hom) ≫
        E₁ ◁ ((associator E₂ E₃ Z).inv ≫ y ▷ Z ≫ (associator E₂ E₃ Z).hom) ≫
        ((associator E₁ E₂ (E₃ ≫ Z)).inv ≫ x ▷ (E₃ ≫ Z) ≫ (associator E₁ E₂ (E₃ ≫ Z)).hom) =
      E₁ ◁ ((associator E₂ E₃ Z).inv ≫ y ▷ Z ≫ (associator E₂ E₃ Z).hom) ≫
        ((associator E₁ E₂ (E₃ ≫ Z)).inv ≫ x ▷ (E₃ ≫ Z) ≫ (associator E₁ E₂ (E₃ ≫ Z)).hom) ≫
        E₁ ◁ ((associator E₂ E₃ Z).inv ≫ y ▷ Z ≫ (associator E₂ E₃ Z).hom) := by
  -- the whiskered associator `α ▷ Z` as an isomorphism
  let A : ((E₁ ≫ E₂) ≫ E₃) ≫ Z ≅ (E₁ ≫ E₂ ≫ E₃) ≫ Z :=
    { hom := (associator E₁ E₂ E₃).hom ▷ Z
      inv := (associator E₁ E₂ E₃).inv ▷ Z
      hom_inv_id := by
        rw [← TwoSupercategory.comp_whiskerRight (R := R), Iso.hom_inv_id,
          TwoSupercategory.id_whiskerRight (R := R)]
      inv_hom_id := by
        rw [← TwoSupercategory.comp_whiskerRight (R := R), Iso.inv_hom_id,
          TwoSupercategory.id_whiskerRight (R := R)] }
  -- the reassociation `(E₁ (E₂ E₃)) Z ≅ E₁ (E₂ (E₃ Z))`
  let Ψ : (E₁ ≫ E₂ ≫ E₃) ≫ Z ≅ E₁ ≫ E₂ ≫ E₃ ≫ Z :=
    associator E₁ (E₂ ≫ E₃) Z ≪≫
      { hom := E₁ ◁ (associator E₂ E₃ Z).hom
        inv := E₁ ◁ (associator E₂ E₃ Z).inv
        hom_inv_id := by
          rw [← TwoSupercategory.whiskerLeft_comp (R := R), Iso.hom_inv_id,
            TwoSupercategory.whiskerLeft_id (R := R)]
        inv_hom_id := by
          rw [← TwoSupercategory.whiskerLeft_comp (R := R), Iso.inv_hom_id,
            TwoSupercategory.whiskerLeft_id (R := R)] }
  have hpent : A ≪≫ Ψ = associator (E₁ ≫ E₂) E₃ Z ≪≫ associator E₁ E₂ (E₃ ≫ Z) :=
    Iso.ext (by
      simpa [A, Ψ, Category.assoc] using TwoSupercategory.pentagon (R := R) E₁ E₂ E₃ Z)
  have hpinv := congrArg Iso.inv hpent
  simp only [Iso.trans_inv] at hpinv
  -- the two crossings as conjugates of whiskered crossings
  have hR : E₁ ◁ ((associator E₂ E₃ Z).inv ≫ y ▷ Z ≫ (associator E₂ E₃ Z).hom) =
      Ψ.inv ≫ (E₁ ◁ y) ▷ Z ≫ Ψ.hom := by
    rw [TwoSupercategory.whisker_assoc (R := R)]
    simp only [Ψ, Iso.trans_hom, Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc,
      TwoSupercategory.whiskerLeft_comp (R := R)]
  have hL : (associator E₁ E₂ (E₃ ≫ Z)).inv ≫ x ▷ (E₃ ≫ Z) ≫
        (associator E₁ E₂ (E₃ ≫ Z)).hom =
      Ψ.inv ≫ ((associator E₁ E₂ E₃).inv ≫ x ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ▷ Z ≫ Ψ.hom := by
    have hhom := congrArg Iso.hom hpent
    simp only [Iso.trans_hom] at hhom
    rw [TwoSupercategory.whiskerRight_comp (R := R), TwoSupercategory.comp_whiskerRight (R := R),
      TwoSupercategory.comp_whiskerRight (R := R)]
    simp only [Category.assoc]
    change _ = Ψ.inv ≫ A.inv ≫ (x ▷ E₃) ▷ Z ≫ A.hom ≫ Ψ.hom
    rw [← Category.assoc Ψ.inv, hpinv, hhom]
    simp only [Category.assoc]
  rw [hR, hL]
  generalize ((associator E₁ E₂ E₃).inv ≫ x ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) = t at hb ⊢
  have key : (E₁ ◁ y) ▷ Z ≫ t ▷ Z ≫ (E₁ ◁ y) ▷ Z = t ▷ Z ≫ (E₁ ◁ y) ▷ Z ≫ t ▷ Z := by
    simp only [← TwoSupercategory.comp_whiskerRight (R := R), hb]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% key]

end Whisker

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-- **The braid relation for the probe crossings** on `PPP`: the factor braid relation
`T.braid`, whiskered by the remaining object. -/
theorem preCrossSame_braid (i : I) (t : Sector I)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) true
      (nextSector (true, i) true t)))) :
    P.preCrossSame i t ((P.step (true, i) true _ trivial).obj Z) ≫
        (P.step (true, i) true t trivial).map (P.preCrossSame i _ Z) ≫
        P.preCrossSame i t ((P.step (true, i) true _ trivial).obj Z) =
      (P.step (true, i) true t trivial).map (P.preCrossSame i _ Z) ≫
        P.preCrossSame i t ((P.step (true, i) true _ trivial).obj Z) ≫
        (P.step (true, i) true t trivial).map (P.preCrossSame i _ Z) := by
  simp only [preCrossSame, Functor.map_smul, Linear.smul_comp, Linear.comp_smul, smul_smul]
  congr 1
  exact whisker_braid k Z _ _ (P.T.braid i (P.muP_preE i t) (P.muP_preE i _) (P.muP_preE i _))

variable (ν : X) (i : I) (t : Sector I)

/-- The path `PPP` of `Eᵢ Eᵢ Eᵢ`. -/
def pppPath : SPath (wd D ν [up i, up i, up i]) t
    (nextSector (true, i) true (nextSector (true, i) true (nextSector (true, i) true t))) :=
  .cons _ true t trivial (.cons _ true _ trivial (.cons _ true _ trivial (.nil _)))

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- `PPP` is the only path of `Eᵢ Eᵢ Eᵢ` to its endpoint. -/
theorem eq_pppPath (p : SPath (wd D ν [up i, up i, up i]) t
    (nextSector (true, i) true (nextSector (true, i) true (nextSector (true, i) true t)))) :
    p = pppPath (D := D) ν i t := by
  suffices h : ∀ (t' : Sector I) (p : SPath (wd D ν [up i, up i, up i]) t t')
      (h : t' = nextSector (true, i) true
        (nextSector (true, i) true (nextSector (true, i) true t))),
      h ▸ p = pppPath ν i t from h _ p rfl
  intro t' p h
  cases p with
  | cons _ σ₁ _ hv₁ p =>
    cases p with
    | cons _ σ₂ _ hv₂ p =>
      cases p with
      | cons _ σ₃ _ hv₃ p =>
        cases p
        have h₁ := congrArg (fun x : Sector I => x.1 i) h
        cases σ₁ <;> cases σ₂ <;> cases σ₃ <;>
          first
            | rfl
            | (exfalso; simp [nextSector] at h₁ <;> omega)

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- A sum over the paths of `Eᵢ Eᵢ Eᵢ` to the endpoint of `PPP` is its `PPP` term. -/
theorem sum_pppPath {M : Type*} [AddCommMonoid M]
    {_ : Fintype (SPath (wd D ν [up i, up i, up i]) t
      (nextSector (true, i) true (nextSector (true, i) true (nextSector (true, i) true t))))}
    (f : SPath (wd D ν [up i, up i, up i]) t
      (nextSector (true, i) true (nextSector (true, i) true (nextSector (true, i) true t))) →
        M) :
    ∑ p, f p = f (pppPath ν i t) :=
  Fintype.sum_eq_single _ fun p hp => absurd (eq_pppPath ν i t p) hp

variable {P} (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (Z : P.H (nextSector (true, i) true (nextSector (true, i) true
    (nextSector (true, i) true t))))

/-- The left crossing on `PPP` is the probe crossing of the two left letters. -/
theorem pppLeft_entry :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (pppPath ν i t) (pppPath ν i t) Z =
      P.preCrossSame i t ((P.step (true, i) true _ trivial).obj Z) := by
  refine (crossEntry_left (P.swappedGens c L) ν i i i
    (.cons _ true t trivial (.cons _ true _ trivial (.nil _)))
    (.cons _ true t trivial (.cons _ true _ trivial (.nil _)))
    (.cons _ true _ trivial (.nil _)) Z).trans ?_
  rw [swappedGens_cross_self]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- The right crossing on `PPP` is the probe crossing of the two right letters. -/
theorem pppRight_entry :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (pppPath ν i t) (pppPath ν i t) Z =
      (P.step (true, i) true t trivial).map (P.preCrossSame i _ Z) := by
  refine (crossEntry_right (P.swappedGens c L) ν i i i (s := t) true trivial
    (.cons _ true _ trivial (.cons _ true _ trivial (.nil _)))
    (.cons _ true _ trivial (.cons _ true _ trivial (.nil _))) Z).trans ?_
  rw [swappedGens_cross_self]
  rfl

/-- **(1.9) on the path `PPP` of the colour pattern `iii`.** -/
theorem ppp_braid :
    braidLeft (P.swappedGens c L) i i i ν (pppPath ν i t) (pppPath ν i t) Z =
      braidRight (P.swappedGens c L) i i i ν (pppPath ν i t) (pppPath ν i t) Z := by
  unfold braidLeft braidRight
  simp only [sum_pppPath ν i t, pppLeft_entry, pppRight_entry, Category.assoc]
  exact P.preCrossSame_braid i t Z

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
