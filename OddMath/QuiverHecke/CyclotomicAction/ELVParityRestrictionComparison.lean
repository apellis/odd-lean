import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleAdjunction
import OddMath.SKM.RouquierNormalizedHomAdjunction

/-! # Canonical parity coordinates under module restriction comparison

The shifted unit/cap entries of DeformedMatrixComparison (5), (6) use the
existing parity shifts with their full module actions. Restricting the
ordinary shifted module and then comparing its value must agree with the
chosen old shifted target. The bridge below uses the canonical
`homParityShiftCommute`; its two odd coordinate maps cancel their degrees.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u v w
variable {k C D : Type u} [CommRing k] [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (Q : C ⥤ D) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
local instance sourceModulePi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory
local instance targetModulePi : PiSupercategory k (Superfunctor k D (SVec k)) :=
  supermodulePiSupercategory
local notation "S₀" => SKM.homParityShift (k := k) (C := Superfunctor k C (SVec k))
local notation "S₁" => SKM.homParityShift (k := k) (C := Superfunctor k D (SVec k))
local notation "P₀" => SKM.homParityShiftDatum (k := k) (C := Superfunctor k C (SVec k))
local notation "P₁" => SKM.homParityShiftDatum (k := k) (C := Superfunctor k D (SVec k))

section Components
variable (M : Superfunctor k D (SVec k)) (N : Superfunctor k C (SVec k))
  (e : (restriction Q).obj M ≅ N)

/-- Move the actual ordinary shift through restriction, then apply the shift
functor to the specified module comparison. -/
def parityRestrictionIso (q : ZMod 2) :
    (restriction Q).obj ((S₁ q).obj M) ≅ (S₀ q).obj N :=
  (SKM.homParityShiftCommute (k := k) (restriction Q) q).symm.app M ≪≫
    (S₀ q).mapIso e

/-- For an even comparison the canonical bridge is precisely the two given
parity coordinates with the original value comparison between them. -/
theorem parityRestrictionIso_eq_chain (q : ZMod 2)
    (he : e.hom ∈ parity (R := k) _ _ 0) :
    (parityRestrictionIso Q M N e q).hom =
      (restriction Q).map ((P₁ q).iso M).hom ≫ e.hom ≫ ((P₀ q).iso N).inv := by
  change (SKM.homParityShiftCommute (k := k) (restriction Q) q).inv.app M ≫
    (S₀ q).map e.hom = _
  rw [SKM.homParityShiftCommute_inv_app]
  have hn := (P₀ q).inv_naturality he
  simp only [mul_zero, sign_zero, one_smul] at hn
  simpa only [Category.assoc] using congrArg
    (fun f => (restriction Q).map ((P₁ q).iso M).hom ≫ f) hn.symm

/-- The two parity-coordinate degrees cancel; the chosen bridge is even. -/
theorem parityRestrictionIso_hom_mem (q : ZMod 2)
    (he : e.hom ∈ parity (R := k) _ _ 0) :
    (parityRestrictionIso Q M N e q).hom ∈ parity (R := k) _ _ 0 := by
  rw [parityRestrictionIso_eq_chain Q M N e q he]
  have hp := comp_mem (map_mem (restriction Q) ((P₁ q).hom_mem M))
    (comp_mem he ((P₀ q).inv_mem N))
  simpa only [zero_add, SKM.zmod2_add_self] using hp

/-- The inverse of the same canonical bridge is even. -/
theorem parityRestrictionIso_inv_mem (q : ZMod 2)
    (he : e.hom ∈ parity (R := k) _ _ 0) :
    (parityRestrictionIso Q M N e q).inv ∈ parity (R := k) _ _ 0 :=
  inv_mem _ (parityRestrictionIso_hom_mem Q M N e q he)

/-- The prescribed target-coordinate square, before evaluating module values. -/
theorem parityRestrictionIso_hom_coordinate (q : ZMod 2)
    (he : e.hom ∈ parity (R := k) _ _ 0) :
    (parityRestrictionIso Q M N e q).hom ≫ ((P₀ q).iso N).hom =
      (restriction Q).map ((P₁ q).iso M).hom ≫ e.hom := by
  rw [parityRestrictionIso_eq_chain Q M N e q he]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Removing the ordinary target coordinate and then using the bridge is the
same as comparing original values and using the old target coordinate. -/
theorem parityRestrictionIso_inv_coordinate (q : ZMod 2)
    (he : e.hom ∈ parity (R := k) _ _ 0) :
    (restriction Q).map ((P₁ q).iso M).inv ≫ (parityRestrictionIso Q M N e q).hom =
      e.hom ≫ ((P₀ q).iso N).inv := by
  rw [parityRestrictionIso_eq_chain Q M N e q he]
  rw [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, (restriction Q).map_id, Category.id_comp]

end Components

section Families
variable {X : Type v} [Category.{w} X]
  (F : X ⥤ Superfunctor k D (SVec k)) (G : X ⥤ Superfunctor k C (SVec k))
  (e : F ⋙ restriction Q ≅ G)

/-- The same canonical shift bridge for an entire input-natural comparison.
Naturality is on every input map, including odd module maps. -/
def parityRestrictionNatIso (q : ZMod 2) :
    (F ⋙ S₁ q) ⋙ restriction Q ≅ G ⋙ S₀ q :=
  Functor.isoWhiskerLeft F (SKM.homParityShiftCommute (k := k) (restriction Q) q).symm ≪≫
    Functor.isoWhiskerRight e (S₀ q)

/-- The family bridge has exactly the specified pointwise canonical component. -/
theorem parityRestrictionNatIso_app (q : ZMod 2) (x : X) :
    (parityRestrictionNatIso Q F G e q).app x =
      parityRestrictionIso Q (F.obj x) (G.obj x) (e.app x) q := rfl

/-- Even input-natural comparisons give even bridge components at every input. -/
theorem parityRestrictionNatIso_hom_mem (q : ZMod 2)
    (he : ∀ x, e.hom.app x ∈ parity (R := k) _ _ 0) (x : X) :
    (parityRestrictionNatIso Q F G e q).hom.app x ∈ parity (R := k) _ _ 0 :=
  parityRestrictionIso_hom_mem Q (F.obj x) (G.obj x) (e.app x) q (he x)

end Families
end OddMath.QuiverHecke.ELVOld.BalancedInduction
