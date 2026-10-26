/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.InductionFunctorComparison
import OddMath.QuiverHecke.CyclotomicAction.SuperCrossing
import StringDiagrams.Super.Functor

/-!
# The crossing on composed cyclotomic superinduction

Ports the crossing of `Categorification/KLR/CyclotomicAction/Induction.lean`
through the even comparison of `CyclotomicAction/Comparison.lean`.
The transformation below is obtained from `compositionSuperCrossing`, not from
an assumed crossing operator. Only its parity and supernatural naturality are
asserted; no square, braid, inversion or KKO relations are asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i j : I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "P" => compositionCorner D Sc i j a ha n
local notation "Q" => compositionCorner D Sc j i a ha n
local notation "F" => cyclotomicSuperInduction D Sc j a ha n ⋙
  cyclotomicSuperInduction D Sc i a ha (n + 1)
local notation "G" => cyclotomicSuperInduction D Sc i a ha n ⋙
  cyclotomicSuperInduction D Sc j a ha (n + 1)
local notation "d" => D.parity i * D.parity j
local notation "e" => inductionFunctorComparison D Sc i j a ha n
local notation "e'" => inductionFunctorComparison D Sc j i a ha n

/-- Transport the corner crossing along the two even comparison isomorphisms. -/
def inductionCrossingApp (M : CyclotomicSupermodules D Sc a ha n) : (F).obj M ⟶ (G).obj M :=
  (e).hom.app M ≫ whiskerRight (compositionSuperCrossing D Sc i j a ha n) M ≫ (e').inv.app M

/-- The transported crossing has parity `|i||j|`. -/
theorem inductionCrossingApp_mem (M : CyclotomicSupermodules D Sc a ha n) :
    inductionCrossingApp D Sc i j a ha n M ∈ parity (R := k) _ _ d := by
  change ((inductionFunctorComparisonApp D Sc i j a ha n M).hom ≫
    whiskerRight (compositionSuperCrossing D Sc i j a ha n) M ≫
      (inductionFunctorComparisonApp D Sc j i a ha n M).inv) ∈
        parity (R := k) ((F).obj M) ((G).obj M) d
  simpa only [zero_add, add_zero] using comp_mem
    (inductionFunctorComparisonApp_hom_mem D Sc i j a ha n M)
    (comp_mem (whiskerRight_mem P (compositionSuperCrossing_parity D Sc i j a ha n) M)
      (inductionFunctorComparisonApp_inv_mem D Sc j i a ha n M))

/-- The comparison introduces no additional naturality sign. -/
theorem inductionCrossingApp_naturality
    {M N : CyclotomicSupermodules D Sc a ha n} {q : ZMod 2} (f : M ⟶ N)
    (hf : f ∈ parity (R := k) M N q) :
    (F).map f ≫ inductionCrossingApp D Sc i j a ha n N =
      koszulSign d q • (inductionCrossingApp D Sc i j a ha n M ≫ (G).map f) := by
  have hcross : whiskerLeft P f ≫ whiskerRight (compositionSuperCrossing D Sc i j a ha n) N =
      koszulSign d q • (whiskerRight (compositionSuperCrossing D Sc i j a ha n) M ≫
        whiskerLeft Q f) := by
    rw [super_interchange P f (compositionSuperCrossing_parity D Sc i j a ha n) hf,
      koszulSign_smul_smul]
  have he := (e).hom.naturality f
  have he' := (e').inv.naturality f
  change (F).map f ≫ (e).hom.app N = (e).hom.app M ≫ whiskerLeft P f at he
  change whiskerLeft Q f ≫ (e').inv.app N = (e').inv.app M ≫ (G).map f at he'
  unfold inductionCrossingApp
  rw [← Category.assoc, he, Category.assoc, ← Category.assoc (whiskerLeft P f),
    hcross, Linear.smul_comp, Linear.comp_smul, Category.assoc, he']
  simp only [Category.assoc]

/-- The homogeneous supernatural crossing between the composed induction superfunctors. -/
def cyclotomicSuperInductionCrossing : SuperNatTrans k F G where
  app p M := if p = d then inductionCrossingApp D Sc i j a ha n M else 0
  app_mem p M := by
    split_ifs with h
    · subst p
      exact inductionCrossingApp_mem D Sc i j a ha n M
    · exact Submodule.zero_mem _
  naturality p M N q f hf := by
    split_ifs with h
    · subst p
      exact inductionCrossingApp_naturality D Sc i j a ha n f hf
    · simp

/-- All components except parity `|i||j|` vanish. -/
theorem cyclotomicSuperInductionCrossing_homogeneous :
    (cyclotomicSuperInductionCrossing D Sc i j a ha n).IsHomogeneous d := by
  intro q h
  funext M
  simp [cyclotomicSuperInductionCrossing, h]

/-- The component of parity `|i||j|` is precisely the transported corner crossing. -/
@[simp] theorem cyclotomicSuperInductionCrossing_app
    (M : CyclotomicSupermodules D Sc a ha n) :
    (cyclotomicSuperInductionCrossing D Sc i j a ha n).app d M =
      (e).hom.app M ≫ whiskerRight (compositionSuperCrossing D Sc i j a ha n) M ≫
        (e').inv.app M := by
  simp [cyclotomicSuperInductionCrossing, inductionCrossingApp]

end OddMath.QuiverHecke
