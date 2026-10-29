/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.SectorDots
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.SectorAlgebra
import OddMath.QuiverHecke.SwappedAssembly.BraidEntries
import OddMath.QuiverHecke.SwappedAssembly.QuadSame

/-! # The braid relation on the mixed block `PPR`, `PRP`, `RPP` of `Eᵢ Eᵢ Eᵢ`

For the relation (1.9) of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Definition 1.5, at `Eᵢ Eᵢ Eᵢ`, the paths with two probe summands and one reservoir summand
form a block (`blockPath`). Transported to the first path `PPR` by `Φ₀ = 1`, `Φ₁`, `Φ₂`
(`blockIso`), the left and right crossings of the swapped generators become the matrices
`sectorU D γ` and `sectorV D δ` over the opposite of `End PPR` (`blockLeft_eq`,
`blockRight_eq`; `docs/Nondegeneracy/ThreeStrandSectorBraid.md`, (1)–(5A)). The braid
relation on the block follows from `sectorBraid` and the dot algebra of `SectorDots`.
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

variable {C : Type*} [Category C] [Preadditive C] {A : C} {O : Fin 3 → C}

omit [Preadditive C] in
/-- Multiplication in the opposite of `End A` is composition in diagrammatic order. -/
theorem unop_mul_end (x y : (End A)ᵐᵒᵖ) :
    @MulOpposite.unop (A ⟶ A) (x * y) = MulOpposite.unop x ≫ MulOpposite.unop y :=
  rfl

omit [Preadditive C] in
/-- Products in `(End A)ᵐᵒᵖ` of opposites are opposites of composites. -/
theorem op_mul_op_end (x y : A ⟶ A) :
    (MulOpposite.op x : (End A)ᵐᵒᵖ) * (MulOpposite.op y : (End A)ᵐᵒᵖ) =
      (MulOpposite.op (x ≫ y) : (End A)ᵐᵒᵖ) := rfl

omit [Preadditive C] in
/-- Squaring a conjugate under a functor, in the opposite endomorphism ring. -/
theorem op_map_conj_sq {C' : Type*} [Category C'] (F : C' ⥤ C) {X Y : C'} (J : X ≅ Y)
    (y : Y ⟶ Y) :
    (MulOpposite.op (F.map J.hom ≫ F.map y ≫ F.map y ≫ F.map J.inv) : (End (F.obj X))ᵐᵒᵖ) =
      (MulOpposite.op (F.map J.hom ≫ F.map y ≫ F.map J.inv) : (End (F.obj X))ᵐᵒᵖ) *
        (MulOpposite.op (F.map J.hom ≫ F.map y ≫ F.map J.inv) : (End (F.obj X))ᵐᵒᵖ) := by
  rw [op_mul_op_end]
  simp only [Category.assoc, Iso.map_inv_hom_id_assoc]

/-- The matrix over the opposite of `End A` of a family of morphisms between the objects
`O l`, transported to `A` by isomorphisms `Φ l : A ≅ O l`. -/
def transportMatrix (Φ : ∀ l, A ≅ O l) (F : ∀ l l', O l ⟶ O l') :
    Matrix (Fin 3) (Fin 3) (End A)ᵐᵒᵖ :=
  Matrix.of fun l l' => MulOpposite.op ((Φ l).hom ≫ F l l' ≫ (Φ l').inv)

/-- A threefold composite of families of morphisms is the product of their transported
matrices. -/
theorem transportMatrix_mul_mul (Φ : ∀ l, A ≅ O l) (F G H : ∀ l l', O l ⟶ O l')
    (m n : Fin 3) :
    (∑ l₂, (∑ l₁, F m l₁ ≫ G l₁ l₂) ≫ H l₂ n) =
      (Φ m).inv ≫ MulOpposite.unop ((transportMatrix Φ F * transportMatrix Φ G * transportMatrix Φ H) m n) ≫
        (Φ n).hom := by
  simp only [Matrix.mul_apply, transportMatrix, Matrix.of_apply, Finset.unop_sum,
    unop_mul_end, MulOpposite.unop_op, Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The relations among `D`, `γ`, `δ` used by `sectorBraid`. -/
def SectorRelations {R : Type*} [Ring R] (D γ δ : R) : Prop :=
  D * D = 0 ∧ D * γ = δ * D + γ * δ ∧ D * δ = γ * D - δ * γ ∧
    γ * (δ * δ) = δ * δ * γ ∧ γ * γ * δ = δ * (γ * γ)

/-- The relations of `sectorBraid` for the opposites of morphisms satisfying the relations of
the block at an even colour. -/
theorem op_sectorRelations_even {D x₁ x₂ z γ δ : A ⟶ A} (hD : D ≫ D = 0)
    (h12 : x₁ ≫ x₂ = x₂ ≫ x₁) (h1z : x₁ ≫ z = z ≫ x₁) (h2z : x₂ ≫ z = z ≫ x₂)
    (hDz : D ≫ z = z ≫ D) (hs₁ : x₁ ≫ D - D ≫ x₂ = 𝟙 A) (hs₂ : D ≫ x₁ - x₂ ≫ D = 𝟙 A)
    (hγ : γ ≫ (z - x₁) = 𝟙 A ∧ (z - x₁) ≫ γ = 𝟙 A)
    (hδ : δ ≫ (z - x₂) = 𝟙 A ∧ (z - x₂) ≫ δ = 𝟙 A) :
    SectorRelations (MulOpposite.op D : (End A)ᵐᵒᵖ) (MulOpposite.op γ) (MulOpposite.op δ) := by
  have op_eq {f g : A ⟶ A} (h : f = g) :
      (MulOpposite.op f : (End A)ᵐᵒᵖ) = MulOpposite.op g := congrArg _ h
  exact ⟨op_eq hD, sectorRelations_even (z := (MulOpposite.op z : (End A)ᵐᵒᵖ))
    (x₁ := (MulOpposite.op x₁ : (End A)ᵐᵒᵖ)) (x₂ := (MulOpposite.op x₂ : (End A)ᵐᵒᵖ))
    (op_eq h12) (op_eq h1z) (op_eq h2z) (op_eq hDz) (op_eq hs₁) (op_eq hs₂) (op_eq hγ.1)
    (op_eq hγ.2) (op_eq hδ.1) (op_eq hδ.2)⟩

/-- The relations of `sectorBraid` for the opposites of morphisms satisfying the relations of
the block at an odd colour. -/
theorem op_sectorRelations_odd {D x₁ x₂ z γ δ : A ⟶ A} (hD : D ≫ D = 0)
    (h12 : x₁ ≫ x₂ = -(x₂ ≫ x₁)) (h1z : x₁ ≫ z = -(z ≫ x₁)) (h2z : x₂ ≫ z = -(z ≫ x₂))
    (hDz : D ≫ z = -(z ≫ D)) (hs₁ : x₁ ≫ D + D ≫ x₂ = 𝟙 A) (hs₂ : D ≫ x₁ + x₂ ≫ D = 𝟙 A)
    (hN₁ : IsUnit (M := End A) (x₁ ≫ x₁ - z ≫ z)) (hN₂ : IsUnit (M := End A) (x₂ ≫ x₂ - z ≫ z))
    (hγ : γ ≫ (x₁ ≫ x₁ - z ≫ z) = x₁ - z) (hδ : δ ≫ (x₂ ≫ x₂ - z ≫ z) = z - x₂) :
    SectorRelations (MulOpposite.op D : (End A)ᵐᵒᵖ) (MulOpposite.op γ) (MulOpposite.op δ) := by
  have op_eq {f g : A ⟶ A} (h : f = g) :
      (MulOpposite.op f : (End A)ᵐᵒᵖ) = MulOpposite.op g := congrArg _ h
  exact ⟨op_eq hD, sectorRelations_odd (z := (MulOpposite.op z : (End A)ᵐᵒᵖ))
    (x₁ := (MulOpposite.op x₁ : (End A)ᵐᵒᵖ)) (x₂ := (MulOpposite.op x₂ : (End A)ᵐᵒᵖ))
    (op_eq h12) (op_eq h1z) (op_eq h2z) (op_eq hDz) (op_eq hs₁) (op_eq hs₂) hN₁.op hN₂.op
    (op_eq hγ) (op_eq hδ)⟩

end Transport

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc) (ν : X) (i : I) (t : Sector I)
  (hR : StepValid (true, i) false (nextSector (true, i) true (nextSector (true, i) true t)))
  (Z : P.H (nextSector (true, i) false
    (nextSector (true, i) true (nextSector (true, i) true t))))

/-- The three paths `PPR`, `PRP`, `RPP` of `Eᵢ Eᵢ Eᵢ` with two probe summands. -/
def blockPath : Fin 3 → SPath (wd D ν [up i, up i, up i]) t
    (nextSector (true, i) false (nextSector (true, i) true (nextSector (true, i) true t)))
  | 0 => .cons _ true t trivial (.cons _ true _ trivial (.cons _ false _ hR (.nil _)))
  | 1 => .cons _ true t trivial (.cons _ false _ hR (.cons _ true _ trivial (.nil _)))
  | 2 => .cons _ false t hR (.cons _ true _ trivial (.cons _ true _ trivial (.nil _)))

/-- The object of the first path `PPR`. -/
abbrev pprObj : P.H t :=
  (P.step (true, i) true t trivial).obj ((P.step (true, i) true _ trivial).obj
    ((P.step (true, i) false _ hR).obj Z))

/-- The transports `Φ₀ = 1`, `Φ₁`, `Φ₂` from the first path to the paths of the block. -/
def blockIso :
    (l : Fin 3) → P.pprObj i t hR Z ≅ (P.pathFunctor (blockPath (D := D) ν i t hR l)).obj Z
  | 0 => Iso.refl _
  | 1 => P.pprToPrpIso i t hR Z
  | 2 => P.pprToRppIso i t hR Z

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- Transports along equalities of an object with itself are trivial. -/
private theorem eqToHom_conj_self {C : Type*} [Category C] {A A' : C} (h₁ : A = A)
    (h₂ : A' = A') (f : A ⟶ A') : eqToHom h₁ ≫ f ≫ eqToHom h₂ = f := by
  simp

variable {P}

variable (c : P.CrossCoeff Sc) (L : P.LeftwardData)

/-- The sectors after two letters of the paths `PPR` and `PRP` differ. -/
private theorem sector_ne :
    (⟨nextSector (true, i) true (nextSector (true, i) true t),
        (.cons _ false _ hR (.nil _) : SPath (wd D ν [up i]) _ _)⟩ :
        Σ z, SPath (wd D ν [up i]) z
          (nextSector (true, i) false (nextSector (true, i) true (nextSector (true, i) true t)))) ≠
      ⟨nextSector (true, i) false (nextSector (true, i) true t),
        (.cons _ true _ trivial (.nil _) : SPath (wd D ν [up i]) _ _)⟩ := by
  intro h
  have h' := congrArg (fun x => x.1.1 i) h
  simp [nextSector] at h'

theorem blockLeft_entry_00 :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPath ν i t hR 0)
        (blockPath ν i t hR 0) Z =
      P.preCrossSame i t ((P.step (true, i) false _ hR).obj Z) := by
  refine (crossEntry_left (P.swappedGens c L) ν i i i
    (.cons _ true t trivial (.cons _ true _ trivial (.nil _)))
    (.cons _ true t trivial (.cons _ true _ trivial (.nil _)))
    (.cons _ false _ hR (.nil _)) Z).trans ((eqToHom_conj_self _ _ _).trans ?_)
  rw [swappedGens_cross_self]
  rfl

theorem blockLeft_entry_01 :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPath ν i t hR 0)
        (blockPath ν i t hR 1) Z = 0 :=
  crossEntry_left_eq_zero (P.swappedGens c L) ν i i i
    (.cons _ true t trivial (.cons _ true _ trivial (.nil _)))
    (.cons _ true t trivial (.cons _ false _ hR (.nil _)))
    (.cons _ false _ hR (.nil _)) (.cons _ true _ trivial (.nil _)) (sector_ne ν i t hR) Z

theorem blockLeft_entry_02 :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPath ν i t hR 0)
        (blockPath ν i t hR 2) Z = 0 :=
  crossEntry_left_eq_zero (P.swappedGens c L) ν i i i
    (.cons _ true t trivial (.cons _ true _ trivial (.nil _)))
    (.cons _ false t hR (.cons _ true _ trivial (.nil _)))
    (.cons _ false _ hR (.nil _)) (.cons _ true _ trivial (.nil _)) (sector_ne ν i t hR) Z

theorem blockLeft_entry_10 :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPath ν i t hR 1)
        (blockPath ν i t hR 0) Z = 0 :=
  crossEntry_left_eq_zero (P.swappedGens c L) ν i i i
    (.cons _ true t trivial (.cons _ false _ hR (.nil _)))
    (.cons _ true t trivial (.cons _ true _ trivial (.nil _)))
    (.cons _ true _ trivial (.nil _)) (.cons _ false _ hR (.nil _)) (sector_ne ν i t hR).symm Z

theorem blockLeft_entry_11 :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPath ν i t hR 1)
        (blockPath ν i t hR 1) Z =
      -((P.mixedJ i i t hR ((P.step (true, i) true _ trivial).obj Z)).hom ≫ c.a i t hR ((P.step (true, i) true _ trivial).obj Z) ≫ (P.mixedJ i i t hR ((P.step (true, i) true _ trivial).obj Z)).inv) := by
  refine (crossEntry_left (P.swappedGens c L) ν i i i
    (.cons _ true t trivial (.cons _ false _ hR (.nil _)))
    (.cons _ true t trivial (.cons _ false _ hR (.nil _)))
    (.cons _ true _ trivial (.nil _)) Z).trans ((eqToHom_conj_self _ _ _).trans ?_)
  rw [swappedGens_cross_self]
  rfl

theorem blockLeft_entry_12 :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPath ν i t hR 1)
        (blockPath ν i t hR 2) Z =
      (P.mixedJ i i t hR ((P.step (true, i) true _ trivial).obj Z)).hom := by
  refine (crossEntry_left (P.swappedGens c L) ν i i i
    (.cons _ true t trivial (.cons _ false _ hR (.nil _)))
    (.cons _ false t hR (.cons _ true _ trivial (.nil _)))
    (.cons _ true _ trivial (.nil _)) Z).trans ((eqToHom_conj_self _ _ _).trans ?_)
  rw [swappedGens_cross_self]
  rfl

theorem blockLeft_entry_20 :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPath ν i t hR 2)
        (blockPath ν i t hR 0) Z = 0 :=
  crossEntry_left_eq_zero (P.swappedGens c L) ν i i i
    (.cons _ false t hR (.cons _ true _ trivial (.nil _)))
    (.cons _ true t trivial (.cons _ true _ trivial (.nil _)))
    (.cons _ true _ trivial (.nil _)) (.cons _ false _ hR (.nil _)) (sector_ne ν i t hR).symm Z

theorem blockLeft_entry_21 :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPath ν i t hR 2)
        (blockPath ν i t hR 1) Z =
      -(c.a i t hR ((P.step (true, i) true _ trivial).obj Z) ≫ c.a i t hR ((P.step (true, i) true _ trivial).obj Z) ≫ (P.mixedJ i i t hR ((P.step (true, i) true _ trivial).obj Z)).inv) := by
  refine (crossEntry_left (P.swappedGens c L) ν i i i
    (.cons _ false t hR (.cons _ true _ trivial (.nil _)))
    (.cons _ true t trivial (.cons _ false _ hR (.nil _)))
    (.cons _ true _ trivial (.nil _)) Z).trans ((eqToHom_conj_self _ _ _).trans ?_)
  rw [swappedGens_cross_self]
  rfl

theorem blockLeft_entry_22 :
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPath ν i t hR 2)
        (blockPath ν i t hR 2) Z =
      c.a i t hR ((P.step (true, i) true _ trivial).obj Z) := by
  refine (crossEntry_left (P.swappedGens c L) ν i i i
    (.cons _ false t hR (.cons _ true _ trivial (.nil _)))
    (.cons _ false t hR (.cons _ true _ trivial (.nil _)))
    (.cons _ true _ trivial (.nil _)) Z).trans ((eqToHom_conj_self _ _ _).trans ?_)
  rw [swappedGens_cross_self]
  rfl

theorem blockRight_entry_00 :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPath ν i t hR 0)
        (blockPath ν i t hR 0) Z =
      (P.step (true, i) true t trivial).map (-((P.mixedJ i i (nextSector (true, i) true t) hR Z).hom ≫ c.a i (nextSector (true, i) true t) hR Z ≫ (P.mixedJ i i (nextSector (true, i) true t) hR Z).inv)) := by
  refine (crossEntry_right (P.swappedGens c L) ν i i i (s := t) true trivial
    (.cons _ true _ trivial (.cons _ false _ hR (.nil _)))
    (.cons _ true _ trivial (.cons _ false _ hR (.nil _))) Z).trans ?_
  rw [swappedGens_cross_self]
  rfl

theorem blockRight_entry_01 :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPath ν i t hR 0)
        (blockPath ν i t hR 1) Z =
      (P.step (true, i) true t trivial).map (P.mixedJ i i (nextSector (true, i) true t) hR Z).hom := by
  refine (crossEntry_right (P.swappedGens c L) ν i i i (s := t) true trivial
    (.cons _ true _ trivial (.cons _ false _ hR (.nil _)))
    (.cons _ false _ hR (.cons _ true _ trivial (.nil _))) Z).trans ?_
  rw [swappedGens_cross_self]
  rfl

theorem blockRight_entry_02 :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPath ν i t hR 0)
        (blockPath ν i t hR 2) Z = 0 :=
  crossEntry_right_eq_zero (P.swappedGens c L) ν i i i (s := t) true false (by decide) trivial hR
    (.cons _ true _ trivial (.cons _ false _ hR (.nil _)))
    (.cons _ true _ trivial (.cons _ true _ trivial (.nil _))) Z

theorem blockRight_entry_10 :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPath ν i t hR 1)
        (blockPath ν i t hR 0) Z =
      (P.step (true, i) true t trivial).map (-(c.a i (nextSector (true, i) true t) hR Z ≫ c.a i (nextSector (true, i) true t) hR Z ≫ (P.mixedJ i i (nextSector (true, i) true t) hR Z).inv)) := by
  refine (crossEntry_right (P.swappedGens c L) ν i i i (s := t) true trivial
    (.cons _ false _ hR (.cons _ true _ trivial (.nil _)))
    (.cons _ true _ trivial (.cons _ false _ hR (.nil _))) Z).trans ?_
  rw [swappedGens_cross_self]
  rfl

theorem blockRight_entry_11 :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPath ν i t hR 1)
        (blockPath ν i t hR 1) Z =
      (P.step (true, i) true t trivial).map (c.a i (nextSector (true, i) true t) hR Z) := by
  refine (crossEntry_right (P.swappedGens c L) ν i i i (s := t) true trivial
    (.cons _ false _ hR (.cons _ true _ trivial (.nil _)))
    (.cons _ false _ hR (.cons _ true _ trivial (.nil _))) Z).trans ?_
  rw [swappedGens_cross_self]
  rfl

theorem blockRight_entry_12 :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPath ν i t hR 1)
        (blockPath ν i t hR 2) Z = 0 :=
  crossEntry_right_eq_zero (P.swappedGens c L) ν i i i (s := t) true false (by decide) trivial hR
    (.cons _ false _ hR (.cons _ true _ trivial (.nil _)))
    (.cons _ true _ trivial (.cons _ true _ trivial (.nil _))) Z

theorem blockRight_entry_20 :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPath ν i t hR 2)
        (blockPath ν i t hR 0) Z = 0 :=
  crossEntry_right_eq_zero (P.swappedGens c L) ν i i i (s := t) false true (by decide) hR trivial
    (.cons _ true _ trivial (.cons _ true _ trivial (.nil _)))
    (.cons _ true _ trivial (.cons _ false _ hR (.nil _))) Z

theorem blockRight_entry_21 :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPath ν i t hR 2)
        (blockPath ν i t hR 1) Z = 0 :=
  crossEntry_right_eq_zero (P.swappedGens c L) ν i i i (s := t) false true (by decide) hR trivial
    (.cons _ true _ trivial (.cons _ true _ trivial (.nil _)))
    (.cons _ false _ hR (.cons _ true _ trivial (.nil _))) Z

theorem blockRight_entry_22 :
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPath ν i t hR 2)
        (blockPath ν i t hR 2) Z =
      (P.step (true, i) false t hR).map (P.preCrossSame i (nextSector (true, i) false t) Z) := by
  refine (crossEntry_right (P.swappedGens c L) ν i i i (s := t) false hR
    (.cons _ true _ trivial (.cons _ true _ trivial (.nil _)))
    (.cons _ true _ trivial (.cons _ true _ trivial (.nil _))) Z).trans ?_
  rw [swappedGens_cross_self]
  rfl

/-! ## The block paths -/

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- The three block paths are distinct. -/
theorem blockPath_injective : Function.Injective (blockPath (D := D) ν i t hR) := by
  intro l m h
  fin_cases l <;> fin_cases m <;> first | rfl | (simp [blockPath] at h)

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- Every path of `Eᵢ Eᵢ Eᵢ` with two probe summands and one reservoir summand is a block
path. -/
theorem blockPath_surjective : Function.Surjective (blockPath (D := D) ν i t hR) := by
  suffices h : ∀ (t' : Sector I) (p : SPath (wd D ν [up i, up i, up i]) t t')
      (h : t' = nextSector (true, i) false
        (nextSector (true, i) true (nextSector (true, i) true t))),
      ∃ l, blockPath ν i t hR l = h ▸ p from fun p => h _ p rfl
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
theorem sum_blockPath {M : Type*} [AddCommMonoid M]
    {_ : Fintype (SPath (wd D ν [up i, up i, up i]) t
      (nextSector (true, i) false (nextSector (true, i) true (nextSector (true, i) true t))))}
    (f : SPath (wd D ν [up i, up i, up i]) t
      (nextSector (true, i) false (nextSector (true, i) true (nextSector (true, i) true t))) →
        M) :
    ∑ p, f p = ∑ l, f (blockPath ν i t hR l) :=
  (Fintype.sum_bijective _ ⟨blockPath_injective ν i t hR, blockPath_surjective ν i t hR⟩ _ _
    (fun _ => rfl)).symm

/-! ## The transported crossings -/


/-- Conjugating the right-letter crossing on `RPP` back to `PPR` gives `D`; this is (5A). -/
private theorem pprToRppIso_conj_preCrossSame :
    (P.pprToRppIso i t hR Z).hom ≫
        (P.step (true, i) false t hR).map (P.preCrossSame i (nextSector (true, i) false t) Z) ≫
          (P.pprToRppIso i t hR Z).inv =
      P.preCrossSame i t ((P.step (true, i) false _ hR).obj Z) := by
  rw [← Category.assoc, Iso.comp_inv_eq]
  simp only [pprToRppIso, pprToPrpIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  exact (P.preCrossSame_mixedJ_pair i t hR Z).symm

/-- The left crossing of the swapped generators on the block, transported to `PPR`. -/
def blockLeft : Matrix (Fin 3) (Fin 3) (End (P.pprObj i t hR Z))ᵐᵒᵖ :=
  transportMatrix (P.blockIso ν i t hR Z) fun l l' =>
    crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPath ν i t hR l)
      (blockPath ν i t hR l') Z

/-- The right crossing of the swapped generators on the block, transported to `PPR`. -/
def blockRight : Matrix (Fin 3) (Fin 3) (End (P.pprObj i t hR Z))ᵐᵒᵖ :=
  transportMatrix (P.blockIso ν i t hR Z) fun l l' =>
    crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPath ν i t hR l)
      (blockPath ν i t hR l') Z

/-- **The left crossing on the block is `sectorU D γ`.** -/
theorem blockLeft_eq :
    blockLeft ν i t hR Z c L =
      sectorU (MulOpposite.op (P.preCrossSame i t ((P.step (true, i) false _ hR).obj Z)))
        (MulOpposite.op (P.pprLeftCoeff i t hR Z c)) := by
  ext m n
  fin_cases m <;> fin_cases n <;>
    simp [blockLeft, transportMatrix, sectorU, blockIso, blockLeft_entry_00, blockLeft_entry_01,
      blockLeft_entry_02, blockLeft_entry_10, blockLeft_entry_11, blockLeft_entry_12,
      blockLeft_entry_20, blockLeft_entry_21, blockLeft_entry_22, pprLeftCoeff, pprToRppIso] <;>
    first
    | rfl
    | (erw [Category.comp_id])
    | (refine (congrArg MulOpposite.op ?_).trans (op_mul_op_end _ _).symm
       simp only [Category.assoc, Iso.inv_hom_id_assoc]
       first | done | rfl)

/-- **The right crossing on the block is `sectorV D δ`.** -/
theorem blockRight_eq :
    blockRight ν i t hR Z c L =
      sectorV (MulOpposite.op (P.preCrossSame i t ((P.step (true, i) false _ hR).obj Z)))
        (MulOpposite.op (P.pprRightCoeff i t hR Z c)) := by
  ext m n
  fin_cases m <;> fin_cases n <;>
    simp [blockRight, transportMatrix, sectorV, blockIso, blockRight_entry_00,
      blockRight_entry_01, blockRight_entry_02, blockRight_entry_10, blockRight_entry_11,
      blockRight_entry_12, blockRight_entry_20, blockRight_entry_21, blockRight_entry_22,
      pprRightCoeff, pprToPrpIso,
      pprToRppIso_conj_preCrossSame] <;>
    first
    | rfl
    | (erw [Category.comp_id])
  all_goals exact op_map_conj_sq _ _ _

/-- The left side of (1.9) on the block, as a product of transported matrices. -/
theorem block_braidLeft (m n : Fin 3) :
    braidLeft (P.swappedGens c L) i i i ν (blockPath ν i t hR m) (blockPath ν i t hR n) Z =
      (P.blockIso ν i t hR Z m).inv ≫
        MulOpposite.unop ((blockLeft ν i t hR Z c L * blockRight ν i t hR Z c L *
          blockLeft ν i t hR Z c L) m n) ≫ (P.blockIso ν i t hR Z n).hom := by
  unfold braidLeft
  simp only [sum_blockPath ν i t hR]
  exact transportMatrix_mul_mul (P.blockIso ν i t hR Z)
    (fun l l' => crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPath ν i t hR l)
      (blockPath ν i t hR l') Z)
    (fun l l' => crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPath ν i t hR l)
      (blockPath ν i t hR l') Z)
    (fun l l' => crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPath ν i t hR l)
      (blockPath ν i t hR l') Z) m n

/-- The right side of (1.9) on the block, as a product of transported matrices. -/
theorem block_braidRight (m n : Fin 3) :
    braidRight (P.swappedGens c L) i i i ν (blockPath ν i t hR m) (blockPath ν i t hR n) Z =
      (P.blockIso ν i t hR Z m).inv ≫
        MulOpposite.unop ((blockRight ν i t hR Z c L * blockLeft ν i t hR Z c L *
          blockRight ν i t hR Z c L) m n) ≫ (P.blockIso ν i t hR Z n).hom := by
  unfold braidRight
  simp only [sum_blockPath ν i t hR]
  exact transportMatrix_mul_mul (P.blockIso ν i t hR Z)
    (fun l l' => crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPath ν i t hR l)
      (blockPath ν i t hR l') Z)
    (fun l l' => crossEntry (P.swappedGens c L) ν [] i i [up i] (blockPath ν i t hR l)
      (blockPath ν i t hR l') Z)
    (fun l l' => crossEntry (P.swappedGens c L) ν [up i] i i [] (blockPath ν i t hR l)
      (blockPath ν i t hR l') Z) m n

/-- **(1.9) on the block `{PPR, PRP, RPP}` of the colour pattern `iii`.** -/
theorem block_braid (hc : c.IsInverse) (h : P.CrossCoeffInputs) (m n : Fin 3) :
    braidLeft (P.swappedGens c L) i i i ν (blockPath ν i t hR m) (blockPath ν i t hR n) Z =
      braidRight (P.swappedGens c L) i i i ν (blockPath ν i t hR m) (blockPath ν i t hR n) Z := by
  have hrel : SectorRelations
      (MulOpposite.op (P.preCrossSame i t ((P.step (true, i) false _ hR).obj Z)) :
        (End (P.pprObj i t hR Z))ᵐᵒᵖ)
      (MulOpposite.op (P.pprLeftCoeff i t hR Z c)) (MulOpposite.op (P.pprRightCoeff i t hR Z c)) := by
    have hsl := P.preCrossSame_slides i t ((P.step (true, i) false _ hR).obj Z)
    have h12 := P.ppLeftDot_comp_ppRightDot i t hR Z
    have h1z := P.ppLeftDot_comp_pprPostDot i t hR Z
    have h2z := P.ppRightDot_comp_pprPostDot i t hR Z
    have hDz := P.preCrossSame_comp_pprPostDot i t hR Z
    have hD := P.preCrossSame_sq i t ((P.step (true, i) false _ hR).obj Z)
    obtain hi | hi : D.parity i = 0 ∨ D.parity i = 1 := by
      generalize D.parity i = p
      fin_cases p <;> simp
    · rw [hi, Supercategory.koszulSign_zero_left, one_smul] at h12 h1z h2z hDz
      rw [hi, Supercategory.koszulSign_zero_left, one_smul, one_smul] at hsl
      exact op_sectorRelations_even hD h12 h1z h2z hDz hsl.1 hsl.2
        (P.pprLeftCoeff_even i t hR Z c hc hi) (P.pprRightCoeff_even i t hR Z c hc hi)
    · rw [hi, Supercategory.koszulSign_one_one, neg_smul, one_smul] at h12 h1z h2z hDz
      rw [hi, Supercategory.koszulSign_one_one, neg_smul, one_smul, neg_smul, one_smul, sub_neg_eq_add,
        sub_neg_eq_add] at hsl
      exact op_sectorRelations_odd hD h12 h1z h2z hDz hsl.1 hsl.2
        (P.pprLeftDenom_isUnit i t hR Z h hi) (P.pprRightDenom_isUnit i t hR Z h hi)
        (P.pprLeftCoeff_odd i t hR Z c hc hi) (P.pprRightCoeff_odd i t hR Z c hc hi)
  obtain ⟨hD, hB, hC, h₁, h₂⟩ := hrel
  rw [block_braidLeft, block_braidRight, blockLeft_eq, blockRight_eq,
    sectorBraid hD hB hC h₁ h₂]

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
