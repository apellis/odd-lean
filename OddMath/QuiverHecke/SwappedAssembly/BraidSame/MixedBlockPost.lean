/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.SectorDotsPost
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.MixedBlock

/-! # The braid relation on the mixed block `PRR`, `RPR`, `RRP` of `Eᵢ Eᵢ Eᵢ`

For the relation (1.9) of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Definition 1.5, at `Eᵢ Eᵢ Eᵢ`, the paths with one probe summand and two reservoir summands
form a block (`blockPathPost`). Transported to the first path `PRR` by `Φ₀ = 1`, `Φ₁`, `Φ₂`
(`blockIsoPost`), the left and right crossings of the swapped generators become the matrices
`sectorV D δ` and `sectorU D γ` over the opposite of `End PRR` (`blockLeftPost_eq`,
`blockRightPost_eq`; `docs/Nondegeneracy/ThreeStrandSectorBraid.md`, (1)–(5B)). Here `D` is the
reservoir crossing of the two right letters; the right crossing on `RRP` is carried to `D` by
(5B). The braid relation on the block follows from `sectorBraid` and the dot algebra of
`SectorDotsPost`, with the dots `(x₁, x₂, z) = (-z, -y, -x)` at an even colour and
`(z, y, x)` at an odd colour.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

section Transport

variable {C : Type*} [Category C] [Preadditive C] {A A' : C}

omit [Preadditive C] in
/-- Squaring a conjugate, in the opposite endomorphism ring. -/
theorem op_conj_sq (φ : A ≅ A') (a : A' ⟶ A') :
    (MulOpposite.op (φ.hom ≫ a ≫ a ≫ φ.inv) : (End A)ᵐᵒᵖ) =
      (MulOpposite.op (φ.hom ≫ a ≫ φ.inv) : (End A)ᵐᵒᵖ) *
        (MulOpposite.op (φ.hom ≫ a ≫ φ.inv) : (End A)ᵐᵒᵖ) := by
  rw [op_mul_op_end]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The relations of `sectorBraid` at an even colour, for the dots `(x₁, x₂, z) = (-z, -y, -x)`
of a block whose crossing `D` slides past `y` and `z`. -/
theorem op_sectorRelations_even_neg {D x y z γ δ : A ⟶ A} (hD : D ≫ D = 0)
    (hzy : z ≫ y = y ≫ z) (hzx : z ≫ x = x ≫ z) (hyx : y ≫ x = x ≫ y) (hDx : D ≫ x = x ≫ D)
    (hs₁ : y ≫ D - D ≫ z = 𝟙 A) (hs₂ : D ≫ y - z ≫ D = 𝟙 A)
    (hγ : γ ≫ (z - x) = 𝟙 A ∧ (z - x) ≫ γ = 𝟙 A)
    (hδ : δ ≫ (y - x) = 𝟙 A ∧ (y - x) ≫ δ = 𝟙 A) :
    SectorRelations (MulOpposite.op D : (End A)ᵐᵒᵖ) (MulOpposite.op γ) (MulOpposite.op δ) := by
  refine op_sectorRelations_even (x₁ := -z) (x₂ := -y) (z := -x) hD ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg] using hzy
  · simpa only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg] using hzx
  · simpa only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg] using hyx
  · simpa only [Preadditive.neg_comp, Preadditive.comp_neg, neg_inj] using hDx
  · rw [Preadditive.neg_comp, Preadditive.comp_neg, sub_neg_eq_add, neg_add_eq_sub]
    exact hs₂
  · rw [Preadditive.neg_comp, Preadditive.comp_neg, sub_neg_eq_add, neg_add_eq_sub]
    exact hs₁
  · rw [neg_sub_neg]
    exact hγ
  · rw [neg_sub_neg]
    exact hδ

end Transport

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc) (ν : X) (i : I) (t : Sector I)
  (hv : StepValid (true, i) false t)
  (hw : StepValid (true, i) false (nextSector (true, i) false t))
  (Z : P.H (nextSector (true, i) false (nextSector (true, i) false
    (nextSector (true, i) true t))))

/-- The three paths `PRR`, `RPR`, `RRP` of `Eᵢ Eᵢ Eᵢ` with one probe summand. -/
def blockPathPost : Fin 3 → SPath (wd D ν [up i, up i, up i]) t
    (nextSector (true, i) false (nextSector (true, i) false (nextSector (true, i) true t)))
  | 0 => .cons _ true t trivial (.cons _ false (nextSector (true, i) true t) hv
      (.cons _ false (nextSector (true, i) false (nextSector (true, i) true t)) hw (.nil _)))
  | 1 => .cons _ false t hv (.cons _ true (nextSector (true, i) false t) trivial
      (.cons _ false (nextSector (true, i) true (nextSector (true, i) false t)) hw (.nil _)))
  | 2 => .cons _ false t hv (.cons _ false (nextSector (true, i) false t) hw
      (.cons _ true _ trivial (.nil _)))

/-- The transports `Φ₀ = 1`, `Φ₁`, `Φ₂` from the first path to the paths of the block. -/
def blockIsoPost :
    (l : Fin 3) →
      P.prrObj i t hv hw Z ≅ (P.pathFunctor (blockPathPost (D := D) ν i t hv hw l)).obj Z
  | 0 => Iso.refl _
  | 1 => P.prrToRprIso i t hv hw Z
  | 2 => P.prrToRrpIso i t hv hw Z

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- Transports along equalities of an object with itself are trivial. -/
private theorem eqToHom_conj_self' {C : Type*} [Category C] {A A' : C} (h₁ : A = A)
    (h₂ : A' = A') (f : A ⟶ A') : eqToHom h₁ ≫ f ≫ eqToHom h₂ = f := by
  simp

variable {P}

variable (c : P.CrossCoeff Sc) (L : P.LeftwardData)

/-- The sectors after two letters of the paths `PRR` and `RRP` differ. -/
private theorem sector_ne_post :
    (⟨nextSector (true, i) false (nextSector (true, i) true t),
        (.cons _ false (nextSector (true, i) false (nextSector (true, i) true t)) hw (.nil _) :
          SPath (wd D ν [up i]) _ _)⟩ :
        Σ z, SPath (wd D ν [up i]) z
          (nextSector (true, i) false (nextSector (true, i) false (nextSector (true, i) true t)))) ≠
      ⟨nextSector (true, i) false (nextSector (true, i) false t),
        (.cons _ true _ trivial (.nil _) : SPath (wd D ν [up i]) _ _)⟩ := by
  intro h
  have h' := congrArg (fun x => x.1.1 i) h
  simp [nextSector] at h'

/-! ## The entries of the left crossing -/

theorem blockLeftPost_entry_00 :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPathPost ν i t hv hw 0)
        (blockPathPost ν i t hv hw 0) Z =
      -((P.mixedJ i i t hv (P.prrRest i t hw Z)).hom ≫ c.a i t hv (P.prrRest i t hw Z) ≫
        (P.mixedJ i i t hv (P.prrRest i t hw Z)).inv) := by
  refine (crossEntry_left (P.swappedGens c L) ν i i i
    (.cons _ true t trivial (.cons _ false (nextSector (true, i) true t) hv (.nil _)))
    (.cons _ true t trivial (.cons _ false (nextSector (true, i) true t) hv (.nil _)))
    (.cons _ false (nextSector (true, i) false (nextSector (true, i) true t)) hw (.nil _))
    Z).trans ((eqToHom_conj_self' _ _ _).trans ?_)
  rw [swappedGens_cross_self]
  rfl

theorem blockLeftPost_entry_01 :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPathPost ν i t hv hw 0)
        (blockPathPost ν i t hv hw 1) Z =
      (P.mixedJ i i t hv (P.prrRest i t hw Z)).hom := by
  refine (crossEntry_left (P.swappedGens c L) ν i i i
    (.cons _ true t trivial (.cons _ false (nextSector (true, i) true t) hv (.nil _)))
    (.cons _ false t hv (.cons _ true (nextSector (true, i) false t) trivial (.nil _)))
    (.cons _ false (nextSector (true, i) false (nextSector (true, i) true t)) hw (.nil _))
    Z).trans ((eqToHom_conj_self' _ _ _).trans ?_)
  rw [swappedGens_cross_self]
  rfl

theorem blockLeftPost_entry_02 :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPathPost ν i t hv hw 0)
        (blockPathPost ν i t hv hw 2) Z = 0 :=
  crossEntry_left_eq_zero (P.swappedGens c L) ν i i i
    (.cons _ true t trivial (.cons _ false (nextSector (true, i) true t) hv (.nil _)))
    (.cons _ false t hv (.cons _ false (nextSector (true, i) false t) hw (.nil _)))
    (.cons _ false (nextSector (true, i) false (nextSector (true, i) true t)) hw (.nil _))
    (.cons _ true _ trivial (.nil _)) (sector_ne_post ν i t hw) Z

theorem blockLeftPost_entry_10 :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPathPost ν i t hv hw 1)
        (blockPathPost ν i t hv hw 0) Z =
      -(c.a i t hv (P.prrRest i t hw Z) ≫ c.a i t hv (P.prrRest i t hw Z) ≫
        (P.mixedJ i i t hv (P.prrRest i t hw Z)).inv) := by
  refine (crossEntry_left (P.swappedGens c L) ν i i i
    (.cons _ false t hv (.cons _ true (nextSector (true, i) false t) trivial (.nil _)))
    (.cons _ true t trivial (.cons _ false (nextSector (true, i) true t) hv (.nil _)))
    (.cons _ false (nextSector (true, i) false (nextSector (true, i) true t)) hw (.nil _))
    Z).trans ((eqToHom_conj_self' _ _ _).trans ?_)
  rw [swappedGens_cross_self]
  rfl

theorem blockLeftPost_entry_11 :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPathPost ν i t hv hw 1)
        (blockPathPost ν i t hv hw 1) Z =
      c.a i t hv (P.prrRest i t hw Z) := by
  refine (crossEntry_left (P.swappedGens c L) ν i i i
    (.cons _ false t hv (.cons _ true (nextSector (true, i) false t) trivial (.nil _)))
    (.cons _ false t hv (.cons _ true (nextSector (true, i) false t) trivial (.nil _)))
    (.cons _ false (nextSector (true, i) false (nextSector (true, i) true t)) hw (.nil _))
    Z).trans ((eqToHom_conj_self' _ _ _).trans ?_)
  rw [swappedGens_cross_self]
  rfl

theorem blockLeftPost_entry_12 :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPathPost ν i t hv hw 1)
        (blockPathPost ν i t hv hw 2) Z = 0 :=
  crossEntry_left_eq_zero (P.swappedGens c L) ν i i i
    (.cons _ false t hv (.cons _ true (nextSector (true, i) false t) trivial (.nil _)))
    (.cons _ false t hv (.cons _ false (nextSector (true, i) false t) hw (.nil _)))
    (.cons _ false (nextSector (true, i) false (nextSector (true, i) true t)) hw (.nil _))
    (.cons _ true _ trivial (.nil _)) (sector_ne_post ν i t hw) Z

theorem blockLeftPost_entry_20 :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPathPost ν i t hv hw 2)
        (blockPathPost ν i t hv hw 0) Z = 0 :=
  crossEntry_left_eq_zero (P.swappedGens c L) ν i i i
    (.cons _ false t hv (.cons _ false (nextSector (true, i) false t) hw (.nil _)))
    (.cons _ true t trivial (.cons _ false (nextSector (true, i) true t) hv (.nil _)))
    (.cons _ true _ trivial (.nil _))
    (.cons _ false (nextSector (true, i) false (nextSector (true, i) true t)) hw (.nil _))
    (sector_ne_post ν i t hw).symm Z

theorem blockLeftPost_entry_21 :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPathPost ν i t hv hw 2)
        (blockPathPost ν i t hv hw 1) Z = 0 :=
  crossEntry_left_eq_zero (P.swappedGens c L) ν i i i
    (.cons _ false t hv (.cons _ false (nextSector (true, i) false t) hw (.nil _)))
    (.cons _ false t hv (.cons _ true (nextSector (true, i) false t) trivial (.nil _)))
    (.cons _ true _ trivial (.nil _))
    (.cons _ false (nextSector (true, i) false (nextSector (true, i) true t)) hw (.nil _))
    (sector_ne_post ν i t hw).symm Z

theorem blockLeftPost_entry_22 :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPathPost ν i t hv hw 2)
        (blockPathPost ν i t hv hw 2) Z =
      P.postCrossSame i t hv hw (P.prrTail i t Z) := by
  refine (crossEntry_left (P.swappedGens c L) ν i i i
    (.cons _ false t hv (.cons _ false (nextSector (true, i) false t) hw (.nil _)))
    (.cons _ false t hv (.cons _ false (nextSector (true, i) false t) hw (.nil _)))
    (.cons _ true _ trivial (.nil _)) Z).trans ((eqToHom_conj_self' _ _ _).trans ?_)
  rw [swappedGens_cross_self]
  rfl

/-! ## The entries of the right crossing -/

theorem blockRightPost_entry_00 :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPathPost ν i t hv hw 0)
        (blockPathPost ν i t hv hw 0) Z = P.prrCross i t hv hw Z := by
  refine (crossEntry_right (P.swappedGens c L) ν i i i (s := t) true trivial
    (.cons _ false (nextSector (true, i) true t) hv
      (.cons _ false (nextSector (true, i) false (nextSector (true, i) true t)) hw (.nil _)))
    (.cons _ false (nextSector (true, i) true t) hv
      (.cons _ false (nextSector (true, i) false (nextSector (true, i) true t)) hw (.nil _)))
    Z).trans ?_
  rw [swappedGens_cross_self]
  rfl

theorem blockRightPost_entry_01 :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPathPost ν i t hv hw 0)
        (blockPathPost ν i t hv hw 1) Z = 0 :=
  crossEntry_right_eq_zero (P.swappedGens c L) ν i i i (s := t) true false (by decide) trivial hv
    (.cons _ false (nextSector (true, i) true t) hv
      (.cons _ false (nextSector (true, i) false (nextSector (true, i) true t)) hw (.nil _)))
    (.cons _ true (nextSector (true, i) false t) trivial
      (.cons _ false (nextSector (true, i) true (nextSector (true, i) false t)) hw (.nil _))) Z

theorem blockRightPost_entry_02 :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPathPost ν i t hv hw 0)
        (blockPathPost ν i t hv hw 2) Z = 0 :=
  crossEntry_right_eq_zero (P.swappedGens c L) ν i i i (s := t) true false (by decide) trivial hv
    (.cons _ false (nextSector (true, i) true t) hv
      (.cons _ false (nextSector (true, i) false (nextSector (true, i) true t)) hw (.nil _)))
    (.cons _ false (nextSector (true, i) false t) hw (.cons _ true _ trivial (.nil _))) Z

theorem blockRightPost_entry_10 :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPathPost ν i t hv hw 1)
        (blockPathPost ν i t hv hw 0) Z = 0 :=
  crossEntry_right_eq_zero (P.swappedGens c L) ν i i i (s := t) false true (by decide) hv trivial
    (.cons _ true (nextSector (true, i) false t) trivial
      (.cons _ false (nextSector (true, i) true (nextSector (true, i) false t)) hw (.nil _)))
    (.cons _ false (nextSector (true, i) true t) hv
      (.cons _ false (nextSector (true, i) false (nextSector (true, i) true t)) hw (.nil _))) Z

theorem blockRightPost_entry_11 :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPathPost ν i t hv hw 1)
        (blockPathPost ν i t hv hw 1) Z =
      (P.step (true, i) false t hv).map
        (-((P.mixedJ i i (nextSector (true, i) false t) hw Z).hom ≫
          c.a i (nextSector (true, i) false t) hw Z ≫
          (P.mixedJ i i (nextSector (true, i) false t) hw Z).inv)) := by
  refine (crossEntry_right (P.swappedGens c L) ν i i i (s := t) false hv
    (.cons _ true (nextSector (true, i) false t) trivial
      (.cons _ false (nextSector (true, i) true (nextSector (true, i) false t)) hw (.nil _)))
    (.cons _ true (nextSector (true, i) false t) trivial
      (.cons _ false (nextSector (true, i) true (nextSector (true, i) false t)) hw (.nil _)))
    Z).trans ?_
  rw [swappedGens_cross_self]
  rfl

theorem blockRightPost_entry_12 :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPathPost ν i t hv hw 1)
        (blockPathPost ν i t hv hw 2) Z =
      (P.step (true, i) false t hv).map (P.mixedJ i i (nextSector (true, i) false t) hw Z).hom := by
  refine (crossEntry_right (P.swappedGens c L) ν i i i (s := t) false hv
    (.cons _ true (nextSector (true, i) false t) trivial
      (.cons _ false (nextSector (true, i) true (nextSector (true, i) false t)) hw (.nil _)))
    (.cons _ false (nextSector (true, i) false t) hw (.cons _ true _ trivial (.nil _)))
    Z).trans ?_
  rw [swappedGens_cross_self]
  rfl

theorem blockRightPost_entry_20 :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPathPost ν i t hv hw 2)
        (blockPathPost ν i t hv hw 0) Z = 0 :=
  crossEntry_right_eq_zero (P.swappedGens c L) ν i i i (s := t) false true (by decide) hv trivial
    (.cons _ false (nextSector (true, i) false t) hw (.cons _ true _ trivial (.nil _)))
    (.cons _ false (nextSector (true, i) true t) hv
      (.cons _ false (nextSector (true, i) false (nextSector (true, i) true t)) hw (.nil _))) Z

theorem blockRightPost_entry_21 :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPathPost ν i t hv hw 2)
        (blockPathPost ν i t hv hw 1) Z =
      (P.step (true, i) false t hv).map
        (-(c.a i (nextSector (true, i) false t) hw Z ≫ c.a i (nextSector (true, i) false t) hw Z ≫
          (P.mixedJ i i (nextSector (true, i) false t) hw Z).inv)) := by
  refine (crossEntry_right (P.swappedGens c L) ν i i i (s := t) false hv
    (.cons _ false (nextSector (true, i) false t) hw (.cons _ true _ trivial (.nil _)))
    (.cons _ true (nextSector (true, i) false t) trivial
      (.cons _ false (nextSector (true, i) true (nextSector (true, i) false t)) hw (.nil _)))
    Z).trans ?_
  rw [swappedGens_cross_self]
  rfl

theorem blockRightPost_entry_22 :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPathPost ν i t hv hw 2)
        (blockPathPost ν i t hv hw 2) Z =
      (P.step (true, i) false t hv).map (c.a i (nextSector (true, i) false t) hw Z) := by
  refine (crossEntry_right (P.swappedGens c L) ν i i i (s := t) false hv
    (.cons _ false (nextSector (true, i) false t) hw (.cons _ true _ trivial (.nil _)))
    (.cons _ false (nextSector (true, i) false t) hw (.cons _ true _ trivial (.nil _)))
    Z).trans ?_
  rw [swappedGens_cross_self]
  rfl

/-! ## The block paths -/

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- The three block paths are distinct. -/
theorem blockPathPost_injective : Function.Injective (blockPathPost (D := D) ν i t hv hw) := by
  intro l m h
  fin_cases l <;> fin_cases m <;> first | rfl | (simp [blockPathPost] at h)

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- Every path of `Eᵢ Eᵢ Eᵢ` with one probe summand and two reservoir summands is a block
path. -/
theorem blockPathPost_surjective : Function.Surjective (blockPathPost (D := D) ν i t hv hw) := by
  suffices h : ∀ (t' : Sector I) (p : SPath (wd D ν [up i, up i, up i]) t t')
      (h : t' = nextSector (true, i) false
        (nextSector (true, i) false (nextSector (true, i) true t))),
      ∃ l, blockPathPost ν i t hv hw l = h ▸ p from fun p => h _ p rfl
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
            | exact ⟨0, rfl⟩
            | exact ⟨1, rfl⟩
            | exact ⟨2, rfl⟩
            | (exfalso; simp [nextSector] at h₁ <;> omega)

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- A sum over the paths of the block is a sum over `Fin 3`. -/
theorem sum_blockPathPost {M : Type*} [AddCommMonoid M]
    {_ : Fintype (SPath (wd D ν [up i, up i, up i]) t
      (nextSector (true, i) false (nextSector (true, i) false (nextSector (true, i) true t))))}
    (f : SPath (wd D ν [up i, up i, up i]) t
      (nextSector (true, i) false (nextSector (true, i) false (nextSector (true, i) true t))) →
        M) :
    ∑ p, f p = ∑ l, f (blockPathPost ν i t hv hw l) :=
  (Fintype.sum_bijective _
    ⟨blockPathPost_injective ν i t hv hw, blockPathPost_surjective ν i t hv hw⟩ _ _
    (fun _ => rfl)).symm

/-! ## The transported crossings -/

/-- The left crossing of the swapped generators on the block, transported to `PRR`. -/
def blockLeftPost : Matrix (Fin 3) (Fin 3) (End (P.prrObj i t hv hw Z))ᵐᵒᵖ :=
  transportMatrix (P.blockIsoPost ν i t hv hw Z) fun l l' =>
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPathPost ν i t hv hw l)
      (blockPathPost ν i t hv hw l') Z

/-- The right crossing of the swapped generators on the block, transported to `PRR`. -/
def blockRightPost : Matrix (Fin 3) (Fin 3) (End (P.prrObj i t hv hw Z))ᵐᵒᵖ :=
  transportMatrix (P.blockIsoPost ν i t hv hw Z) fun l l' =>
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPathPost ν i t hv hw l)
      (blockPathPost ν i t hv hw l') Z

/-- **The left crossing on the block is `sectorV D δ`.** -/
theorem blockLeftPost_eq :
    blockLeftPost ν i t hv hw Z c L =
      sectorV (MulOpposite.op (P.prrCross i t hv hw Z))
        (MulOpposite.op (P.prrLeftCoeff i t hv hw Z c)) := by
  ext m n
  fin_cases m <;> fin_cases n <;>
    simp [blockLeftPost, transportMatrix, sectorV, blockIsoPost, blockLeftPost_entry_00,
      blockLeftPost_entry_01, blockLeftPost_entry_02, blockLeftPost_entry_10,
      blockLeftPost_entry_11, blockLeftPost_entry_12, blockLeftPost_entry_20,
      blockLeftPost_entry_21, blockLeftPost_entry_22, prrLeftCoeff, prrToRprIso,
      prrToRrpIso_conj_postCrossSame] <;>
    first
    | rfl
    | (erw [Category.comp_id]; done)
    | (erw [Category.comp_id]; exact op_conj_sq _ _)

/-- **The right crossing on the block is `sectorU D γ`.** -/
theorem blockRightPost_eq :
    blockRightPost ν i t hv hw Z c L =
      sectorU (MulOpposite.op (P.prrCross i t hv hw Z))
        (MulOpposite.op (P.prrRightCoeff i t hv hw Z c)) := by
  ext m n
  fin_cases m <;> fin_cases n <;>
    simp [blockRightPost, transportMatrix, sectorU, blockIsoPost, blockRightPost_entry_00,
      blockRightPost_entry_01, blockRightPost_entry_02, blockRightPost_entry_10,
      blockRightPost_entry_11, blockRightPost_entry_12, blockRightPost_entry_20,
      blockRightPost_entry_21, blockRightPost_entry_22, prrRightCoeff, prrToRrpIso,
      prrToRprIso] <;>
    first
    | rfl
    | (erw [Category.comp_id])
    | (refine (congrArg MulOpposite.op ?_).trans (op_mul_op_end _ _).symm
       simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.map_inv_hom_id_assoc])

/-- The left side of (1.9) on the block, as a product of transported matrices. -/
theorem blockPost_braidLeft (m n : Fin 3) :
    braidLeft (P.swappedGens c L) i i i ν (blockPathPost ν i t hv hw m)
        (blockPathPost ν i t hv hw n) Z =
      (P.blockIsoPost ν i t hv hw Z m).inv ≫
        MulOpposite.unop ((blockLeftPost ν i t hv hw Z c L * blockRightPost ν i t hv hw Z c L *
          blockLeftPost ν i t hv hw Z c L) m n) ≫ (P.blockIsoPost ν i t hv hw Z n).hom := by
  unfold braidLeft
  simp only [sum_blockPathPost ν i t hv hw]
  exact transportMatrix_mul_mul (P.blockIsoPost ν i t hv hw Z)
    (fun l l' => crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPathPost ν i t hv hw l)
      (blockPathPost ν i t hv hw l') Z)
    (fun l l' => crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPathPost ν i t hv hw l)
      (blockPathPost ν i t hv hw l') Z)
    (fun l l' => crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPathPost ν i t hv hw l)
      (blockPathPost ν i t hv hw l') Z) m n

/-- The right side of (1.9) on the block, as a product of transported matrices. -/
theorem blockPost_braidRight (m n : Fin 3) :
    braidRight (P.swappedGens c L) i i i ν (blockPathPost ν i t hv hw m)
        (blockPathPost ν i t hv hw n) Z =
      (P.blockIsoPost ν i t hv hw Z m).inv ≫
        MulOpposite.unop ((blockRightPost ν i t hv hw Z c L * blockLeftPost ν i t hv hw Z c L *
          blockRightPost ν i t hv hw Z c L) m n) ≫ (P.blockIsoPost ν i t hv hw Z n).hom := by
  unfold braidRight
  simp only [sum_blockPathPost ν i t hv hw]
  exact transportMatrix_mul_mul (P.blockIsoPost ν i t hv hw Z)
    (fun l l' => crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPathPost ν i t hv hw l)
      (blockPathPost ν i t hv hw l') Z)
    (fun l l' => crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPathPost ν i t hv hw l)
      (blockPathPost ν i t hv hw l') Z)
    (fun l l' => crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPathPost ν i t hv hw l)
      (blockPathPost ν i t hv hw l') Z) m n

/-- The relations of `sectorBraid` for `D`, `γ`, `δ` on the first path `PRR`. -/
theorem prr_sectorRelations (hc : c.IsInverse) (h : P.CrossCoeffInputs) :
    SectorRelations (MulOpposite.op (P.prrCross i t hv hw Z) : (End (P.prrObj i t hv hw Z))ᵐᵒᵖ)
      (MulOpposite.op (P.prrRightCoeff i t hv hw Z c))
      (MulOpposite.op (P.prrLeftCoeff i t hv hw Z c)) := by
  have hsl := P.prrCross_slides i t hv hw Z
  have hzy := P.prrPostDot_comp_prPostDot i t hv hw Z
  have hzx := P.prrPostDot_comp_prPreDot i t hv hw Z
  have hyx := P.prPostDot_comp_prPreDot_prr i t hv hw Z
  have hDx := P.prrCross_comp_prPreDot i t hv hw Z
  have hD := P.prrCross_sq i t hv hw Z
  obtain hi | hi : D.parity i = 0 ∨ D.parity i = 1 := by
    generalize D.parity i = p
    fin_cases p <;> simp
  · simp only [hi, Supercategory.koszulSign_zero_left, one_smul] at hsl hzy hzx hyx hDx
    exact op_sectorRelations_even_neg hD hzy hzx hyx hDx hsl.1 hsl.2
      (P.prrRightCoeff_even i t hv hw Z c hc hi) (P.prrLeftCoeff_even i t hv hw Z c hc hi)
  · simp only [hi, Supercategory.koszulSign_one_one, neg_smul, one_smul, sub_neg_eq_add]
      at hsl hzy hzx hyx hDx
    refine op_sectorRelations_odd (x₁ := P.prrPostDot i t hv hw Z)
      (x₂ := P.prPostDot i i t hv (P.prrRest i t hw Z))
      (z := P.prPreDot i i t hv (P.prrRest i t hw Z)) hD hzy hzx hyx hDx ?_ ?_
      (P.prrRightDenom_isUnit i t hv hw Z h hi) (P.prrLeftDenom_isUnit i t hv hw Z h hi)
      (P.prrRightCoeff_odd i t hv hw Z c hc hi) (P.prrLeftCoeff_odd i t hv hw Z c hc hi)
    · rw [add_comm]
      exact hsl.2
    · rw [add_comm]
      exact hsl.1

/-- **(1.9) on the block `{PRR, RPR, RRP}` of the colour pattern `iii`.** -/
theorem blockPost_braid (hc : c.IsInverse) (h : P.CrossCoeffInputs) (m n : Fin 3) :
    braidLeft (P.swappedGens c L) i i i ν (blockPathPost ν i t hv hw m)
        (blockPathPost ν i t hv hw n) Z =
      braidRight (P.swappedGens c L) i i i ν (blockPathPost ν i t hv hw m)
        (blockPathPost ν i t hv hw n) Z := by
  obtain ⟨hD, hB, hC, h₁, h₂⟩ := prr_sectorRelations i t hv hw Z c hc h
  rw [blockPost_braidLeft, blockPost_braidRight, blockLeftPost_eq, blockRightPost_eq,
    sectorBraid hD hB hC h₁ h₂]

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
