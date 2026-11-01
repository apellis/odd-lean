import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuperAdjunction
import OddMath.QuiverHecke.CyclotomicAction.GlobalRouquierMateKernel

/-! # The old module adjunction and its ordered crossing mate

The module category uses its canonical vector-parity structure, the
adjunction is the existing balanced-induction adjunction, and the crossing
is the signed double-induction crossing. The generic SCat mate expansion
is applied to these constructed maps. This remains an old/untruncated
construction; coefficient-truncated exact-content transport is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- One underlying category record is shared by both ambient views. -/
def oldModuleCategory : SCat.{u, u, u + 1} k :=
  SCat.of k (Superfunctor k (OldCategory D Sc cutoff) (SVec k))

def oldModulePiCategory : PiSCat.{u, u, u + 1} k where
  toSCat := oldModuleCategory D Sc cutoff
  pi := by
    change PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    exact supermodulePiSupercategory (k := k) (C := OldCategory D Sc cutoff)

def oldInduction (i : I) :
    oldModuleCategory D Sc cutoff ⟶ oldModuleCategory D Sc cutoff :=
  show Superfunctor k (Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) from
      ⟨BalancedInduction.induction (k := k) (append D Sc cutoff i)⟩

def oldRestriction (i : I) :
    oldModuleCategory D Sc cutoff ⟶ oldModuleCategory D Sc cutoff :=
  show Superfunctor k (Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) from
      ⟨BalancedInduction.restriction (k := k) (append D Sc cutoff i)⟩

def oldInductionPi (i : I) :
    oldModulePiCategory D Sc cutoff ⟶ oldModulePiCategory D Sc cutoff :=
  oldInduction D Sc cutoff i

def oldRestrictionPi (i : I) :
    oldModulePiCategory D Sc cutoff ⟶ oldModulePiCategory D Sc cutoff :=
  oldRestriction D Sc cutoff i

def oldAppendPiAdjunction (i : I) :
    SKM.SuperAdjunction (k := k) (B := PiSCat.{u, u, u + 1} k)
      (oldInductionPi D Sc cutoff i) (oldRestrictionPi D Sc cutoff i) :=
  ordinaryEvenSuperAdjunction (k := k) (oldInductionPi D Sc cutoff i) (oldRestrictionPi D Sc cutoff i)
    (BalancedInduction.adjunction (append D Sc cutoff i))
    (BalancedInduction.adjunctionUnit_mem (append D Sc cutoff i))
    (BalancedInduction.adjunctionCounit_mem (append D Sc cutoff i))

/-- Forgetting Π changes none of the constructed adjunction maps or triangles. -/
def oldAppendAdjunction (i : I) :
    SKM.SuperAdjunction (k := k) (B := SCat.{u, u, u + 1} k)
      (a := oldModuleCategory D Sc cutoff) (b := oldModuleCategory D Sc cutoff)
      (oldInduction D Sc cutoff i) (oldRestriction D Sc cutoff i) where
  unit := (oldAppendPiAdjunction D Sc cutoff i).unit
  counit := (oldAppendPiAdjunction D Sc cutoff i).counit
  unit_mem := (oldAppendPiAdjunction D Sc cutoff i).unit_mem
  counit_mem := (oldAppendPiAdjunction D Sc cutoff i).counit_mem
  left_triangle := (oldAppendPiAdjunction D Sc cutoff i).left_triangle
  right_triangle := (oldAppendPiAdjunction D Sc cutoff i).right_triangle

theorem oldAppendAdjunction_unit_app (i : I) (q : ZMod 2)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (oldAppendAdjunction D Sc cutoff i).unit.app q M =
      if q = 0 then (BalancedInduction.adjunctionUnit (append D Sc cutoff i)).app M else 0 := rfl

theorem oldAppendAdjunction_counit_app (i : I) (q : ZMod 2)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (oldAppendAdjunction D Sc cutoff i).counit.app q M =
      if q = 0 then (BalancedInduction.adjunctionCounit (append D Sc cutoff i)).app M else 0 := rfl

def oldSignedCross (i : I) :
    oldInduction D Sc cutoff i ≫ oldInduction D Sc cutoff i ⟶
      oldInduction D Sc cutoff i ≫ oldInduction D Sc cutoff i :=
  signedEqualInductionCross D Sc cutoff i

/-- The ordered cup-crossing-cap mate of the constructed adjunction and crossing. -/
def oldModuleMate (i : I) :
    oldRestriction D Sc cutoff i ≫ oldInduction D Sc cutoff i ⟶
      oldInduction D Sc cutoff i ≫ oldRestriction D Sc cutoff i :=
  SKM.rouquierMate (k := k) (B := SCat.{u, u, u + 1} k) (oldAppendAdjunction D Sc cutoff i) (oldAppendAdjunction D Sc cutoff i)
    (oldSignedCross D Sc cutoff i)

/-- The existing generic mate expansion, specialized without an adjunction premise. -/
theorem oldModuleMate_app (i : I) (r : ZMod 2)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (oldModuleMate D Sc cutoff i).app r M =
      (BalancedInduction.adjunctionUnit (append D Sc cutoff i)).app
        ((BalancedInduction.induction (k := k) (append D Sc cutoff i)).obj
          ((BalancedInduction.restriction (k := k) (append D Sc cutoff i)).obj M)) ≫
        (BalancedInduction.restriction (k := k) (append D Sc cutoff i)).map
          ((signedEqualInductionCross D Sc cutoff i).app r
            ((BalancedInduction.restriction (k := k) (append D Sc cutoff i)).obj M)) ≫
        (BalancedInduction.restriction (k := k) (append D Sc cutoff i)).map
          ((BalancedInduction.induction (k := k) (append D Sc cutoff i)).map
            ((BalancedInduction.adjunctionCounit (append D Sc cutoff i)).app M)) := by
  have h := CyclotomicAction.scat_rouquierMate_app (k := k)
    (a := oldModuleCategory D Sc cutoff) (b := oldModuleCategory D Sc cutoff)
    (c := oldModuleCategory D Sc cutoff)
    (E₁ := oldInduction D Sc cutoff i) (F₁ := oldRestriction D Sc cutoff i)
    (E₂ := oldInduction D Sc cutoff i) (F₂ := oldRestriction D Sc cutoff i)
    (oldAppendAdjunction D Sc cutoff i) (oldAppendAdjunction D Sc cutoff i)
    (oldSignedCross D Sc cutoff i)
    (fun Z => by simp only [oldAppendAdjunction_unit_app, one_ne_zero, ↓reduceIte])
    (fun Z => by simp only [oldAppendAdjunction_counit_app, one_ne_zero, ↓reduceIte]) r M
  exact h

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

