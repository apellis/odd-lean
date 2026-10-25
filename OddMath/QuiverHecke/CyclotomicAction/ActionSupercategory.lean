/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.SuperAdjunction
import OddMath.QuiverHecke.CyclotomicAction.SuperDot
import OddMath.SKM.RouquierData
import StringDiagrams.Super.SCat
import StringDiagrams.Super.TwoSCat

/-!
# Cyclotomic induction and restriction in the supercategory of supercategories

Ports the adjunction packaging of
`Categorification/TwoRep/CyclotomicRouqAdjunction.lean` to `SKM.SuperAdjunction`.
The objects are the cyclotomic supermodule categories, and the 1-morphisms are
balanced-tensor induction and restriction. The unit and counit have only an even
component; the dot has the parity of its colour. The ambient bundled `TwoSCat`
is the existing `SCat` 2-supercategory, retaining supernatural transformations
and super-interchange. No local inversion, crossing, or vacuum extension is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The ambient 2-supercategory for the cyclotomic supermodule action. -/
abbrev cyclotomicActionTarget : TwoSCat k := TwoSCat.of k (SCat.{u, u, u + 1} k)

variable (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

/-- The cyclotomic supermodule category, as an object of the action target. -/
abbrev cyclotomicActionObject : cyclotomicActionTarget (k := k) :=
  SCat.of k (CyclotomicSupermodules D Sc a ha n)

variable (i : I)

/-- Balanced-tensor induction as a 1-morphism. -/
def cyclotomicActionInduction :
    cyclotomicActionObject D Sc a ha n ⟶ cyclotomicActionObject D Sc a ha (n + 1) :=
  ⟨cyclotomicSuperInduction D Sc i a ha n⟩

/-- Balanced-tensor restriction as a 1-morphism. -/
def cyclotomicActionRestriction :
    cyclotomicActionObject D Sc a ha (n + 1) ⟶ cyclotomicActionObject D Sc a ha n :=
  ⟨cyclotomicSuperRestriction D Sc i a ha n⟩

local notation "F" => cyclotomicActionInduction D Sc a ha n i
local notation "E" => cyclotomicActionRestriction D Sc a ha n i

/-- The cyclotomic unit as an even supernatural transformation. -/
def cyclotomicActionUnit : 𝟙 (cyclotomicActionObject D Sc a ha n) ⟶ F ≫ E :=
  SuperNatTrans.ofNatTrans (cyclotomicSuperUnit D Sc i a ha n)
    (superUnitComponent_mem D Sc i a ha n)

/-- The cyclotomic counit as an even supernatural transformation. -/
def cyclotomicActionCounit : E ≫ F ⟶ 𝟙 (cyclotomicActionObject D Sc a ha (n + 1)) :=
  SuperNatTrans.ofNatTrans (cyclotomicSuperCounit D Sc i a ha n)
    (superCounitComponent_mem D Sc i a ha n)

/-- The even adjunction in the existing Rouquier interface. -/
def cyclotomicActionAdjunction : SKM.SuperAdjunction (k := k) F E where
  unit := cyclotomicActionUnit D Sc a ha n i
  counit := cyclotomicActionCounit D Sc a ha n i
  unit_mem := Superfunctor.mem_parity_iff_isHomogeneous.2
    (SuperNatTrans.ofNatTrans_isHomogeneous _ _)
  counit_mem := Superfunctor.mem_parity_iff_isHomogeneous.2
    (SuperNatTrans.ofNatTrans_isHomogeneous _ _)
  left_triangle := by
    simp only [SCat.leftUnitor_inv, SCat.associator_hom, SCat.rightUnitor_hom]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    apply Superfunctor.hom_ext_parity
    · intro M
      change _ = 𝟙 ((cyclotomicSuperInduction D Sc i a ha n).obj M)
      simpa [cyclotomicActionUnit, cyclotomicActionCounit, SuperNatTrans.ofNatTrans,
        Superfunctor.whiskerRight_app, Superfunctor.whiskerLeft_app,
        Superfunctor.comp_app_zero, cyclotomicActionInduction, Superfunctor.map,
        Superfunctor.obj] using superInduction_triangle D Sc i a ha n M
    · intro M
      simp [cyclotomicActionUnit, cyclotomicActionCounit, SuperNatTrans.ofNatTrans]
  right_triangle := by
    simp only [SCat.rightUnitor_inv, SCat.associator_inv, SCat.leftUnitor_hom]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    apply Superfunctor.hom_ext_parity
    · intro M
      change _ = 𝟙 ((cyclotomicSuperRestriction D Sc i a ha n).obj M)
      simpa [cyclotomicActionUnit, cyclotomicActionCounit, SuperNatTrans.ofNatTrans,
        Superfunctor.whiskerRight_app, Superfunctor.whiskerLeft_app,
        Superfunctor.comp_app_zero, cyclotomicActionRestriction, Superfunctor.map,
        Superfunctor.obj] using superRestriction_triangle D Sc i a ha n M
    · intro M
      simp [cyclotomicActionUnit, cyclotomicActionCounit, SuperNatTrans.ofNatTrans]

/-- The last dot as a 2-endomorphism of induction. -/
def cyclotomicActionDot : F ⟶ F := cyclotomicSuperInductionDot D Sc i a ha n

/-- The 2-endomorphism has the colour parity, including for odd colours. -/
theorem cyclotomicActionDot_mem :
    cyclotomicActionDot D Sc a ha n i ∈ parity (R := k) F F (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.2
    (cyclotomicSuperInductionDot_homogeneous D Sc i a ha n)

end OddMath.QuiverHecke
