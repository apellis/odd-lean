import OddMath.QuiverHecke.CyclotomicAction.ELVModuleZeroBoundary
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedAdjunction

/-! # The zero lower cell inside the evaluated OLD probe category

Brundan–Ellis (1.14): the empty-product OLD zero module evaluates every
coefficient literally and defines a zero endocell in the existing full
probe category. Its zero identity, postcomposition and even adjunction
retain the actual evaluated category and all independently chosen E maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (γ : List I)
local notation "C" => OldContentCategory D Sc (probeCutoff D m) γ
local notation "P" => ProbeEvaluatesCoefficients D m Sc γ
local notation "T₀" => probeEvaluatedTarget D Sc m γ

/-- The empty-product module satisfies the exact scalar coefficient equations. -/
theorem zeroModule_evaluatesCoefficients : P (zeroModule (k := k) C) := by
  intro s c
  apply SVec.hom_ext
  intro x
  funext e
  exact Empty.elim e

/-- The original OLD zero module, with only its coefficient-evaluation certificate added. -/
def probeEvaluatedZeroModule : ProbeEvaluatedModules D Sc m γ :=
  ⟨zeroModule C, zeroModule_evaluatesCoefficients D Sc m γ⟩

/-- The zero object remains inside the given evaluated module category. -/
theorem probeEvaluatedZeroModule_id :
    (𝟙 (probeEvaluatedZeroModule D Sc m γ) : _ ⟶ _) = 0 := by
  apply InducedCategory.hom_ext
  exact zeroModule_id C

theorem probeEvaluatedZeroModule_isZero : Limits.IsZero (probeEvaluatedZeroModule D Sc m γ) :=
  (Limits.IsZero.iff_id_eq_zero _).mpr (probeEvaluatedZeroModule_id D Sc m γ)

/-- The constant zero functor sends every homogeneous input map to zero. -/
def probeEvaluatedZeroFunctor : ProbeEvaluatedModules D Sc m γ ⥤ ProbeEvaluatedModules D Sc m γ where
  obj _ := probeEvaluatedZeroModule D Sc m γ
  map _ := 0
  map_id _ := (probeEvaluatedZeroModule_id D Sc m γ).symm
  map_comp _ _ := by simp

instance probeEvaluatedZeroFunctor_additive : (probeEvaluatedZeroFunctor D Sc m γ).Additive where
  map_add := by intros; exact (add_zero _).symm
instance probeEvaluatedZeroFunctor_linear : (probeEvaluatedZeroFunctor D Sc m γ).Linear k where
  map_smul _ _ := (smul_zero _).symm
instance probeEvaluatedZeroFunctor_super : IsSuperfunctor k (probeEvaluatedZeroFunctor D Sc m γ) where
  map_mem _ := Submodule.zero_mem _

/-- The zero endocell uses the actual evaluated target, without replacing its category. -/
def probeEvaluatedZeroCell : T₀ ⟶ T₀ :=
  show Superfunctor k (ProbeEvaluatedModules D Sc m γ) (ProbeEvaluatedModules D Sc m γ) from
    ⟨probeEvaluatedZeroFunctor D Sc m γ⟩

/-- Both parity components of the endocell identity have their actual zero values. -/
theorem probeEvaluatedZeroCell_id : (𝟙 (probeEvaluatedZeroCell D Sc m γ) : _ ⟶ _) = 0 := by
  apply Superfunctor.hom_ext_parity
  · intro N
    exact probeEvaluatedZeroModule_id D Sc m γ
  · intro N
    rfl

private theorem map_zero_identity {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Preadditive B] (F : A ⥤ B) [F.Additive]
    (s : A) (hs : (𝟙 s : s ⟶ s) = 0) : (𝟙 (F.obj s) : _ ⟶ _) = 0 := by
  rw [← F.map_id, hs, F.map_zero]

/-- Postcomposition by every given evaluated-target cell preserves the zero identity. -/
theorem probeEvaluatedZeroCell_comp_id (B : PiSCat.{u,u,u+1} k) (H : T₀ ⟶ B) :
    (𝟙 (probeEvaluatedZeroCell D Sc m γ ≫ H) : _ ⟶ _) = 0 := by
  apply Superfunctor.hom_ext_parity
  · intro N
    exact map_zero_identity H.toFunctor (probeEvaluatedZeroModule D Sc m γ)
      (probeEvaluatedZeroModule_id D Sc m γ)
  · intro N
    rfl

/-- The same zero endocell is evenly self-adjoint in the existing evaluated target. -/
def probeEvaluatedZeroAdjunction :
    SKM.SuperAdjunction (k := k) (probeEvaluatedZeroCell D Sc m γ) (probeEvaluatedZeroCell D Sc m γ) where
  unit := 0
  counit := 0
  unit_mem := Submodule.zero_mem _
  counit_mem := Submodule.zero_mem _
  left_triangle := by
    simp only [TwoSupercategory.zero_whiskerRight (R := k), Limits.comp_zero,
      Limits.zero_comp, probeEvaluatedZeroCell_id]
  right_triangle := by
    simp only [TwoSupercategory.whiskerLeft_zero (R := k), Limits.comp_zero,
      Limits.zero_comp, probeEvaluatedZeroCell_id]
end OddMath.QuiverHecke
