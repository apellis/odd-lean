import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirPostUnitCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitDotComponents

/-! # The chosen reservoir post-unit in canonical append coordinates

SwappedActionAssembly F2: remove the stored successor content only by
its actual content equality, retaining the raw unit and every dot power.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicAction
universe u
local instance postStandardHomPi {k : Type u} [CommRing k] (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- The ordinary canonical append has exactly the given last-dot family. -/
theorem canonicalAppendDot_supernatural (β : Multiset I) (i : I) :
    IsSupernatural k (D.parity i)
      (contentAppendToComponent D Sc cutoff bound (β := β) rfl rfl (dotE D Sc [i] 0)) :=
  contentAppendTo_supernatural D Sc cutoff bound rfl rfl (by
    simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)

/-- The stored upper-loop object agrees with canonical append/restrict.
No equivalence is chosen beyond the specified successor-content equality. -/
theorem storedAppendUpper_obj (β : Multiset I) (i : I) (γ : Multiset I)
    (hγ : β + ([i] : Multiset I) = γ) (M : ContentModules D Sc cutoff bound β) :
    (restriction (contentAppendTo D Sc cutoff bound β [i] γ hγ)).obj
        ((induction (contentAppendTo D Sc cutoff bound β [i] γ hγ)).obj M) =
      (restriction (contentAppend D Sc cutoff bound β [i])).obj
        ((induction (contentAppend D Sc cutoff bound β [i])).obj M) := by
  subst γ
  rfl

/-- Every stored dotted unit column becomes the native dotted unit under
this literal target chart. -/
theorem storedAppendUnit_column (β : Multiset I) (i : I) (γ : Multiset I)
    (hγ : β + ([i] : Multiset I) = γ) (M : ContentModules D Sc cutoff bound β) (r : ℕ) :
    unitDotColumn (contentAppendTo D Sc cutoff bound β [i] γ hγ)
        (contentAppendTo_supernatural D Sc cutoff bound hγ hγ (by
          simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)) M r ≫
      eqToHom (storedAppendUpper_obj D Sc cutoff bound β i γ hγ M) =
    (adjunction (contentAppend D Sc cutoff bound β [i])).unit.app M ≫
      restrictedDotEnd (contentAppend D Sc cutoff bound β [i])
        (canonicalAppendDot_supernatural D Sc cutoff bound β i) M ^ r := by
  subst γ
  simp only [eqToHom_refl, Category.comp_id]
  convert unitDotColumn_eq_restrictedDotEnd (contentAppend D Sc cutoff bound β [i])
    (canonicalAppendDot_supernatural D Sc cutoff bound β i) M r using 1; rfl

variable (Λ : X) (hc : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (T : X → PiSCat.{u,u,u+1} k) (i : I) (β : I →₀ ℕ) (muP : X)
  {a b : X} (h : a + D.α i = b)
local notation "W" => elvRouquierFamily D Sc cutoff bound Λ hc

/-- The actual content-shifted post-Hom cup is the native reservoir unit
and raw restricted-dot power at every source block. -/
theorem reservoirPostCup_canonical (r : ℕ) (Z : SKM.homWeightSector T (W).obj muP a)
    (N : T (-muP)) (δ : WeightBlocks D Λ a) :
    ((SKM.homContentPostCup T W i β muP h r Z).total N) δ ≫
      ((SKM.homContentPostTargetIso T W i β muP h Z).hom.total N) δ ≫
      eqToHom (elvWeightFollowing_obj D Sc cutoff bound i Λ h δ (Z.obj N)) ≫
      eqToHom (storedAppendUpper_obj D Sc cutoff bound δ.1 i
        (blockSucc D Λ i h δ).1 (elvBlockSucc_content_eq D i Λ h δ) ((Z.obj N) δ)) =
    (adjunction (contentAppend D Sc cutoff bound δ.1 [i])).unit.app ((Z.obj N) δ) ≫
      restrictedDotEnd (contentAppend D Sc cutoff bound δ.1 [i])
        (canonicalAppendDot_supernatural D Sc cutoff bound δ.1 i) ((Z.obj N) δ) ^ r := by
  rw [← storedAppendUnit_column D Sc cutoff bound δ.1 i
    (blockSucc D Λ i h δ).1 (elvBlockSucc_content_eq D i Λ h δ) ((Z.obj N) δ) r]
  rw [← reservoirPostCup_block D Sc cutoff bound Λ hc T i β muP h r Z N δ]
  simp only [Category.assoc]

end OddMath.QuiverHecke.ELVOld
