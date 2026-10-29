/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Braid
import OddMath.QuiverHecke.SwappedAssembly.Slides
import OddMath.QuiverHecke.SwappedAssembly.Generators

/-! # Entries of the crossing relations at explicit summand paths -/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u

variable {I X : Type u}

namespace SPath

/-- The path of a two-letter word through the summands `σ₁`, `σ₂`, ending at a given
sector. -/
def mk₂ {c₁ c₂ : Col I X} {t t' : Sector I} (σ₁ σ₂ : Bool) (hv₁ : StepValid c₁.l σ₁ t)
    (hv₂ : StepValid c₂.l σ₂ (nextSector c₁.l σ₁ t))
    (e : nextSector c₂.l σ₂ (nextSector c₁.l σ₁ t) = t') : SPath [c₁, c₂] t t' :=
  .cons c₁ σ₁ t hv₁ (.cons c₂ σ₂ _ hv₂ (e ▸ .nil _))

/-- Every path of a two-letter word is `mk₂` of its two summands. -/
theorem exists_eq_mk₂ {c₁ c₂ : Col I X} {t t' : Sector I} (p : SPath [c₁, c₂] t t') :
    ∃ σ₁ σ₂ hv₁ hv₂ e, p = mk₂ (c₁ := c₁) (c₂ := c₂) σ₁ σ₂ hv₁ hv₂ e := by
  cases p with
  | cons _ σ₁ _ hv₁ p =>
    cases p with
    | cons _ σ₂ _ hv₂ p =>
      cases p
      exact ⟨σ₁, σ₂, hv₁, hv₂, rfl, rfl⟩

end SPath

/-- Two raising strands of colour `i` add the number of probe summands to the `i`-th probe
content. -/
theorem nextSector_fst_same (i : I) (σ₁ σ₂ : Bool) (s : Sector I) :
    (nextSector (true, i) σ₂ (nextSector (true, i) σ₁ s)).1 i =
      s.1 i + (if σ₁ then 1 else 0) + (if σ₂ then 1 else 0) := by
  cases σ₁ <;> cases σ₂ <;> simp [nextSector, add_assoc]

variable [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}


namespace ProbeReservoir

variable {P : ProbeReservoir k B D Sc}

theorem leftDot_cons (gens : P.Generators) (i j : I) (ν : X) (s : Sector I) (σ₁ σ₂ : Bool)
    (hv₁ : StepValid (true, i) σ₁ s) (hv₂ : StepValid (true, j) σ₂ (nextSector (true, i) σ₁ s))
    (Z : P.H (nextSector (true, j) σ₂ (nextSector (true, i) σ₁ s))) :
    leftDot gens i j ν (.cons _ σ₁ s hv₁ (.cons _ σ₂ _ hv₂ (.nil _))) Z =
      gens.dot i (SKM.wt D ν [up j]) (.cons _ σ₁ s hv₁ (.nil _)) (.cons _ σ₁ s hv₁ (.nil _))
        ((P.step (true, j) σ₂ _ hv₂).obj Z) := by
  unfold leftDot
  refine (compLayer_eq_of_path gens (SKM.lay D ν [] (SKM.Shape.dot i) [up j]) (.nil s)
    (.cons _ σ₁ s hv₁ (.nil _)) (.cons _ σ₁ s hv₁ (.nil _))
    (.cons _ σ₂ _ hv₂ (.nil _) : SPath (SKM.wd D ν [up j]) _ _) _ _ rfl rfl Z).trans ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

theorem rightDot_cons (gens : P.Generators) (i j : I) (ν : X) (s : Sector I) (σ₁ σ₂ : Bool)
    (hv₁ : StepValid (true, i) σ₁ s) (hv₂ : StepValid (true, j) σ₂ (nextSector (true, i) σ₁ s))
    (Z : P.H (nextSector (true, j) σ₂ (nextSector (true, i) σ₁ s))) :
    rightDot gens i j ν (.cons _ σ₁ s hv₁ (.cons _ σ₂ _ hv₂ (.nil _))) Z =
      (P.step (true, i) σ₁ s hv₁).map
        (gens.dot j ν (.cons _ σ₂ _ hv₂ (.nil _)) (.cons _ σ₂ _ hv₂ (.nil _)) Z) := by
  unfold rightDot
  refine (compLayer_eq_of_path gens (SKM.lay D ν [up i] (SKM.Shape.dot j) [])
    (.cons _ σ₁ s hv₁ (.nil _) : SPath (SKM.wd D (SKM.wt D ν [up j]) [up i]) _ _)
    (.cons _ σ₂ _ hv₂ (.nil _)) (.cons _ σ₂ _ hv₂ (.nil _)) (.nil _) _ _ rfl rfl Z).trans ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
