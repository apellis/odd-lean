import Mathlib.CategoryTheory.EqToHom
import OddMath.QuiverHecke.CyclotomicAction.ContentModule.ContentModuleQuadratic
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate.InductionSquareTensors

/-!
# Induction grid mate

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Actual shifted coefficient supermodule and canonical source transport

The prescribed coefficient(1) functor is packaged as its actual supermodule,
using its independently proved action/projection comparison. The resulting
even module isomorphism is mapped through actual induction. Composition with
the canonical parity source isomorphism gives whole coend transport and
an equality with the actual adjunction counit.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem coefficientOne_obj_part (i : I) (v : List I) (s : OldCategory D Sc cutoff)
    (q : ZMod 2) :
    ((coefficient D Sc cutoff 1 i v).obj s).part q =
      ((parityRestrictedRepresentable D Sc cutoff i v).obj s).part q := by
  ext b
  rw [SVec.mem_part_iff, SVec.mem_part_iff, coefficientOne_obj_proj]
  rfl

instance coefficientOne_additive (i : I) (v : List I) :
    (coefficient D Sc cutoff 1 i v).Additive where
  map_add {s t} f g := by
    apply LinearMap.ext
    intro b
    change (coefficient D Sc cutoff 1 i v).map (f + g) b =
      (coefficient D Sc cutoff 1 i v).map f b + (coefficient D Sc cutoff 1 i v).map g b
    rw [coefficientOne_map, coefficientOne_map, coefficientOne_map]
    exact congrArg (fun h => h b)
      ((parityRestrictedRepresentable D Sc cutoff i v).toFunctor.map_add (f := f) (g := g))

instance coefficientOne_linear (i : I) (v : List I) :
    (coefficient D Sc cutoff 1 i v).Linear k where
  map_smul {s t} f r := by
    apply LinearMap.ext
    intro b
    change (coefficient D Sc cutoff 1 i v).map (r • f) b =
      r • (coefficient D Sc cutoff 1 i v).map f b
    rw [coefficientOne_map, coefficientOne_map]
    exact congrArg (fun h => h b)
      ((parityRestrictedRepresentable D Sc cutoff i v).toFunctor.map_smul r f)

instance coefficientOne_super (i : I) (v : List I) :
    IsSuperfunctor k (coefficient D Sc cutoff 1 i v) where
  map_mem := by
    intro s t p f hf
    apply SVec.mem_parityHom_of_apply_mem
    intro q b hb
    change b ∈ ((coefficient D Sc cutoff 1 i v).obj s).part q at hb
    rw [coefficientOne_obj_part] at hb
    change (coefficient D Sc cutoff 1 i v).map f b ∈
      ((coefficient D Sc cutoff 1 i v).obj t).part (q + p)
    rw [coefficientOne_obj_part, coefficientOne_map]
    exact SVec.apply_mem_part
      (map_mem (parityRestrictedRepresentable D Sc cutoff i v).toFunctor hf) hb

def coefficientOneModule (i : I) (v : List I) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  ⟨coefficient D Sc cutoff 1 i v⟩

def coefficientModuleForward (i : I) (v : List I) :
    coefficientOneModule D Sc cutoff i v ⟶ parityRestrictedRepresentable D Sc cutoff i v :=
  Superfunctor.homMk (IsSupernatural.toSuperNatTrans (p := 0)
    (x := fun s => (coefficientParityIso D Sc cutoff i v).hom.app s) {
      mem := coefficientParityIso_hom_mem D Sc cutoff i v
      naturality := by
        intro s t q f hf
        simp only [zero_mul, Supercategory.sign_zero, one_smul]
        exact (coefficientParityIso D Sc cutoff i v).hom.naturality f })

def coefficientModuleBackward (i : I) (v : List I) :
    parityRestrictedRepresentable D Sc cutoff i v ⟶ coefficientOneModule D Sc cutoff i v :=
  Superfunctor.homMk (IsSupernatural.toSuperNatTrans (p := 0)
    (x := fun s => (coefficientParityIso D Sc cutoff i v).inv.app s) {
      mem := by
        intro s q
        change LinearMap.id ∘ₗ
            ((parityRestrictedRepresentable D Sc cutoff i v).obj s).proj q =
          ((coefficient D Sc cutoff 1 i v).obj s).proj (q + 0) ∘ₗ LinearMap.id
        rw [add_zero, LinearMap.id_comp, LinearMap.comp_id]
        exact (coefficientOne_obj_proj D Sc cutoff i v s q).symm
      naturality := by
        intro s t q f hf
        simp only [zero_mul, Supercategory.sign_zero, one_smul]
        exact (coefficientParityIso D Sc cutoff i v).inv.naturality f })

@[simp] theorem coefficientModuleForward_app (i : I) (v : List I)
    (p : ZMod 2) (s : OldCategory D Sc cutoff) :
    (coefficientModuleForward D Sc cutoff i v).app p s =
      if p = 0 then LinearMap.id else 0 := rfl

@[simp] theorem coefficientModuleBackward_app (i : I) (v : List I)
    (p : ZMod 2) (s : OldCategory D Sc cutoff) :
    (coefficientModuleBackward D Sc cutoff i v).app p s =
      if p = 0 then LinearMap.id else 0 := rfl

def coefficientParityModuleIso (i : I) (v : List I) :
    coefficientOneModule D Sc cutoff i v ≅ parityRestrictedRepresentable D Sc cutoff i v where
  hom := coefficientModuleForward D Sc cutoff i v
  inv := coefficientModuleBackward D Sc cutoff i v
  hom_inv_id := by
    apply Superfunctor.hom_ext
    intro p s
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp only [Superfunctor.comp_app, coefficientModuleForward_app,
        coefficientModuleBackward_app, Superfunctor.id_app_zero, Superfunctor.id_app_one,
        ↓reduceIte, zero_add, one_ne_zero, SVec.zmod2_one_add_one]
    all_goals
      ext b
      simp <;> rfl
  inv_hom_id := by
    apply Superfunctor.hom_ext
    intro p s
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp only [Superfunctor.comp_app, coefficientModuleForward_app,
        coefficientModuleBackward_app, Superfunctor.id_app_zero, Superfunctor.id_app_one,
        ↓reduceIte, zero_add, one_ne_zero, SVec.zmod2_one_add_one]
    all_goals
      ext b
      simp <;> rfl

/-- The prescribed moving-parity coefficient is packaged before taking its coend. -/
instance movingCoefficient_additive (j : {j : I // D.parity j = 1}) (v : List I) :
    (coefficient D Sc cutoff (D.parity j.1) j.1 v).Additive := by
  simpa only [j.property] using coefficientOne_additive D Sc cutoff j.1 v

instance movingCoefficient_linear (j : {j : I // D.parity j = 1}) (v : List I) :
    (coefficient D Sc cutoff (D.parity j.1) j.1 v).Linear k := by
  simpa only [j.property] using coefficientOne_linear D Sc cutoff j.1 v

instance movingCoefficient_super (j : {j : I // D.parity j = 1}) (v : List I) :
    IsSuperfunctor k (coefficient D Sc cutoff (D.parity j.1) j.1 v) := by
  simpa only [j.property] using coefficientOne_super D Sc cutoff j.1 v

def movingCoefficientModule (j : {j : I // D.parity j = 1}) (v : List I) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  ⟨coefficient D Sc cutoff (D.parity j.1) j.1 v⟩

def movingCoefficientForward (j : {j : I // D.parity j = 1}) (v : List I) :
    movingCoefficientModule D Sc cutoff j v ⟶ coefficientOneModule D Sc cutoff j.1 v :=
  Superfunctor.homMk (IsSupernatural.toSuperNatTrans (p := 0)
    (x := fun _ => LinearMap.id) {
      mem := by
        intro s q
        change LinearMap.id ∘ₗ
            ((coefficient D Sc cutoff (D.parity j.1) j.1 v).obj s).proj q =
          ((coefficient D Sc cutoff 1 j.1 v).obj s).proj (q + 0) ∘ₗ LinearMap.id
        rw [add_zero, LinearMap.id_comp, LinearMap.comp_id, j.property]
      naturality := by
        intro s t q f hf
        simp only [zero_mul, Supercategory.sign_zero, one_smul]
        change LinearMap.id ∘ₗ (coefficient D Sc cutoff (D.parity j.1) j.1 v).map f =
          (coefficient D Sc cutoff 1 j.1 v).map f ∘ₗ LinearMap.id
        rw [LinearMap.id_comp, LinearMap.comp_id, j.property] })

def movingCoefficientBackward (j : {j : I // D.parity j = 1}) (v : List I) :
    coefficientOneModule D Sc cutoff j.1 v ⟶ movingCoefficientModule D Sc cutoff j v :=
  Superfunctor.homMk (IsSupernatural.toSuperNatTrans (p := 0)
    (x := fun _ => LinearMap.id) {
      mem := by
        intro s q
        change LinearMap.id ∘ₗ ((coefficient D Sc cutoff 1 j.1 v).obj s).proj q =
          ((coefficient D Sc cutoff (D.parity j.1) j.1 v).obj s).proj (q + 0) ∘ₗ LinearMap.id
        rw [add_zero, LinearMap.id_comp, LinearMap.comp_id, j.property]
      naturality := by
        intro s t q f hf
        simp only [zero_mul, Supercategory.sign_zero, one_smul]
        change LinearMap.id ∘ₗ (coefficient D Sc cutoff 1 j.1 v).map f =
          (coefficient D Sc cutoff (D.parity j.1) j.1 v).map f ∘ₗ LinearMap.id
        rw [LinearMap.id_comp, LinearMap.comp_id, j.property] })

@[simp] theorem movingCoefficientForward_app (j : {j : I // D.parity j = 1})
    (v : List I) (q : ZMod 2) (s : OldCategory D Sc cutoff) :
    (movingCoefficientForward D Sc cutoff j v).app q s =
      if q = 0 then LinearMap.id else 0 := rfl

@[simp] theorem movingCoefficientBackward_app (j : {j : I // D.parity j = 1})
    (v : List I) (q : ZMod 2) (s : OldCategory D Sc cutoff) :
    (movingCoefficientBackward D Sc cutoff j v).app q s =
      if q = 0 then LinearMap.id else 0 := rfl

/-- The coefficient comparison is pointwise identity; it is formed before induction. -/
def movingCoefficientIso (j : {j : I // D.parity j = 1}) (v : List I) :
    movingCoefficientModule D Sc cutoff j v ≅ coefficientOneModule D Sc cutoff j.1 v where
  hom := movingCoefficientForward D Sc cutoff j v
  inv := movingCoefficientBackward D Sc cutoff j v
  hom_inv_id := by
    apply Superfunctor.hom_ext
    intro q s
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
      simp only [Superfunctor.comp_app, movingCoefficientForward_app,
        movingCoefficientBackward_app, Superfunctor.id_app_zero, Superfunctor.id_app_one,
        ↓reduceIte, zero_add, one_ne_zero, SVec.zmod2_one_add_one]
    all_goals
      ext b
      simp <;> rfl
  inv_hom_id := by
    apply Superfunctor.hom_ext
    intro q s
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
      simp only [Superfunctor.comp_app, movingCoefficientForward_app,
        movingCoefficientBackward_app, Superfunctor.id_app_zero, Superfunctor.id_app_one,
        ↓reduceIte, zero_add, one_ne_zero, SVec.zmod2_one_add_one]
    all_goals
      ext b
      simp <;> rfl

/-- The actual induction of the moving coefficient has literally the prescribed
source carrier. The comparison is induced from the pointwise coefficient iso;
no equality recursor transports a coend. -/
def coefficientOneSourceEquiv (j : {j : I // D.parity j = 1}) (v t : List I) :
    BalancedInduction.Obj (append D Sc cutoff j.1)
      (coefficient D Sc cutoff 1 j.1 v) (⟨t⟩ : OldCategory D Sc cutoff) ≃ₗ[k]
      Source D Sc cutoff j.1 v t :=
  moduleIsoLinearEquiv
    (((BalancedInduction.induction (append D Sc cutoff j.1)).mapIso
      (movingCoefficientIso D Sc cutoff j v)).symm)
    (⟨t⟩ : OldCategory D Sc cutoff)

/-- Canonical actual module transport into induction of the prescribed
coefficient(1), whose underlying coend is the independently defined source. -/
def shiftedSourceParityIso (i : I) (v : List I) :
    (BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) ≅
    (BalancedInduction.induction (append D Sc cutoff i)).obj (coefficientOneModule D Sc cutoff i v) :=
  BalancedInduction.adjunctionParitySourceIso (append D Sc cutoff i)
    (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) ≪≫
      ((BalancedInduction.induction (append D Sc cutoff i)).mapIso
        (coefficientParityModuleIso D Sc cutoff i v)).symm

/-- Actual counit at the parity-shifted representable, expressed on the
prescribed coefficient module and with the canonical output parity map. -/
def shiftedSourceCounit (i : I) (v : List I) :
    (BalancedInduction.induction (append D Sc cutoff i)).obj
      (coefficientOneModule D Sc cutoff i v) ⟶
      oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff) :=
  ((BalancedInduction.induction (append D Sc cutoff i)).mapIso
      (coefficientParityModuleIso D Sc cutoff i v)).hom ≫
    (BalancedInduction.adjunctionCounit (append D Sc cutoff i)).app
      (supermoduleParityObj (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) ≫
    (supermoduleParityIso (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).hom

theorem shiftedSourceParityIso_counit (i : I) (v : List I) :
    (shiftedSourceParityIso D Sc cutoff i v).hom ≫ shiftedSourceCounit D Sc cutoff i v =
      (BalancedInduction.adjunctionCounit (append D Sc cutoff i)).app
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) := by
  change ((BalancedInduction.adjunctionParitySourceIso (append D Sc cutoff i)
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).hom ≫
    ((BalancedInduction.induction (append D Sc cutoff i)).mapIso
      (coefficientParityModuleIso D Sc cutoff i v)).inv) ≫
    (((BalancedInduction.induction (append D Sc cutoff i)).mapIso
      (coefficientParityModuleIso D Sc cutoff i v)).hom ≫
      ((BalancedInduction.adjunctionCounit (append D Sc cutoff i)).app
        (supermoduleParityObj (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) ≫
        (supermoduleParityIso (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).hom)) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact BalancedInduction.adjunctionParitySourceIso_counit (append D Sc cutoff i)
    (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Homogeneous transformations on iterated induction

The equal-colour crossing in DeformedMatrixComparison (2), (4) is obtained
from its literal two-letter transformation using the chosen induction
flattening. The tensor formula below keeps its parity twist on the complete
composite coefficient arrow.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C A B : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {α : ∀ v, (J ⋙ K).obj v ⟶ (J ⋙ K).obj v}
  (hα : IsSupernatural k p α) (M : Superfunctor k C (SVec k))

private def flattenLinear (w : B) :
    Obj K (induced J M).toFunctor w →ₗ[k] Obj (J ⋙ K) M.toFunctor w :=
  ((inductionComp J K).hom.app M).total w

private def unflattenLinear (w : B) :
    Obj (J ⋙ K) M.toFunctor w →ₗ[k] Obj K (induced J M).toFunctor w :=
  ((inductionComp J K).inv.app M).total w

private theorem flattenLinear_tensor (s : C) (v : A) (w : B)
    (a : J.obj s ⟶ v) (g : K.obj v ⟶ w) (b : M.obj s) :
    flattenLinear J K M w
      (tensor K (induced J M).toFunctor v g (tensor J M.toFunctor s a b)) =
    tensor (J ⋙ K) M.toFunctor s (K.map a ≫ g) b := by
  have h := inductionComp_hom_total_tensor J K M s v w g a b
  set_option backward.dsimp.instances true in
    dsimp only [flattenLinear, induction] at h ⊢
  exact h

private theorem unflattenLinear_tensor (s : C) (w : B)
    (g : K.obj (J.obj s) ⟶ w) (b : M.obj s) :
    unflattenLinear J K M w (tensor (J ⋙ K) M.toFunctor s g b) =
      tensor K (induced J M).toFunctor (J.obj s) g
        (tensor J M.toFunctor s (𝟙 _) b) := by
  have h := inductionComp_inv_total_tensor J K M s w g b
  set_option backward.dsimp.instances true in
    dsimp only [unflattenLinear, induction] at h ⊢
  exact h

/-- The homogeneous two-letter transform, conjugated by the selected
induction-composition isomorphism on the literal iterated coends. -/
def doubleTransformLinear (w : B) :
    Obj K (induced J M).toFunctor w →ₗ[k] Obj K (induced J M).toFunctor w :=
  unflattenLinear J K M w ∘ₗ transformLinear hα M w ∘ₗ flattenLinear J K M w

/-- The inverse flattening inserts a unit in the first induction; the
transformation twists the entire old composite coefficient, in its order. -/
theorem doubleTransformLinear_tensor (s : C) (v : A) (w : B)
    (a : J.obj s ⟶ v) (g : K.obj v ⟶ w) (b : M.obj s) :
    doubleTransformLinear J K hα M w
      (tensor K (induced J M).toFunctor v g (tensor J M.toFunctor s a b)) =
      tensor K (induced J M).toFunctor (J.obj s)
        (α s ≫ twist k p (K.map a ≫ g)) (tensor J M.toFunctor s (𝟙 _) b) := by
  rw [doubleTransformLinear, LinearMap.comp_apply, LinearMap.comp_apply,
    flattenLinear_tensor, transformLinear_tensor, unflattenLinear_tensor]

private theorem transformComponent_total (w : B) :
    (transformComponent hα M).total w = transformLinear hα M w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

/-- This literal coend operator is the total map of the given homogeneous
module transformation conjugated by the two selected flattenings. -/
theorem doubleTransformLinear_eq_total (w : B)
    (b : Obj K (induced J M).toFunctor w) :
    doubleTransformLinear J K hα M w b =
      (((inductionComp J K).hom.app M ≫ transformComponent hα M ≫
        (inductionComp J K).inv.app M).total w) b := by
  rw [Superfunctor.comp_total, SVec.comp_apply, Superfunctor.comp_total,
    SVec.comp_apply, transformComponent_total]
  unfold doubleTransformLinear
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  unfold flattenLinear unflattenLinear
  rfl

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # The ordered crossing mate between changing content categories

The first crossing-derived entry of DeformedMatrixComparison (2), (4)
uses the unit for the upper append adjunction, the prescribed signed
crossing, and induction of the lower append counit. Keeping the three
categories distinct gives the mate needed by the scalar and fixed-content
matrix charts in DeformedActionAssembly §§5–6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C A B : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hα : IsSupernatural k p α)

/-- The given homogeneous crossing conjugated by both chosen flattenings. -/
def gridDoubleCrossComponent (M : Superfunctor k C (SVec k)) :
    (induction J ⋙ induction K).obj M ⟶ (induction J ⋙ induction K).obj M :=
  (inductionComp J K).hom.app M ≫ transformComponent hα M ≫
    (inductionComp J K).inv.app M

private theorem gridDoubleCrossComponent_total_tensor
    (M : Superfunctor k C (SVec k)) (s : C) (v : A) (w : B)
    (a : J.obj s ⟶ v) (g : K.obj v ⟶ w) (b : M.obj s) :
    (((inductionComp J K).hom.app M ≫ transformComponent hα M ≫
      (inductionComp J K).inv.app M).total w)
      (tensor K (induced J M).toFunctor v g (tensor J M.toFunctor s a b)) =
      tensor K (induced J M).toFunctor (J.obj s)
        (α s ≫ twist k p (K.map a ≫ g)) (tensor J M.toFunctor s (𝟙 _) b) :=
  (doubleTransformLinear_eq_total J K hα M w
    (tensor K (induced J M).toFunctor v g (tensor J M.toFunctor s a b))).symm.trans
      (doubleTransformLinear_tensor J K hα M s v w a g b)

private def gridModuleUnit (M : Superfunctor k A (SVec k)) :
    M ⟶ (restriction K).obj (induced K M) := (adjunctionUnit K).app M

private def gridModuleCounit (N : Superfunctor k A (SVec k)) :
    induced J ((restriction J).obj N) ⟶ N := (adjunctionCounit J).app N

private def gridInducedCounit (N : Superfunctor k A (SVec k)) :
    induced K (induced J ((restriction J).obj N)) ⟶ induced K N :=
  (induction K).map (gridModuleCounit J N)

private theorem gridUnit_total_apply (M : Superfunctor k A (SVec k)) (t : A) (b : M.obj t) :
    (gridModuleUnit K M).total t b = unit K M.toFunctor t b := by
  simp only [gridModuleUnit, adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    unitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  rfl

private theorem gridCounit_total_tensor (N : Superfunctor k A (SVec k))
    (s : C) (t : A) (g : J.obj s ⟶ t) (b : N.obj (J.obj s)) :
    (gridModuleCounit J N).total t
      (tensor J ((restriction J).obj N).toFunctor s g b) = N.map g b := by
  simp only [gridModuleCounit, adjunctionCounit, Superfunctor.homMk, SuperNatTrans.total,
    counitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  exact counit_tensor J N.toFunctor t s g b

private theorem gridRestriction_total_apply
    {M N : Superfunctor k B (SVec k)} (f : M ⟶ N) (t : A) (b : M.obj (K.obj t)) :
    ((restriction K).map f).total t b = f.total (K.obj t) b := rfl

private theorem gridNeg_total_apply
    {M N : Superfunctor k B (SVec k)} (f : M ⟶ N) (t : B) (b : M.obj t) :
    (-f).total t b = -(f.total t b) := by
  change -(f.app 0 t b) + -(f.app 1 t b) = -(f.app 0 t b + f.app 1 t b)
  exact (neg_add _ _).symm

private theorem gridInduction_map_even_tensor
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N)
    (hf : f ∈ parity (R := k) M N 0)
    (s : A) (t : B) (g : K.obj s ⟶ t) (b : M.obj s) :
    ((induction K).map f).total t (tensor K M.toFunctor s g b) =
      tensor K N.toFunctor s g (f.total s b) := by
  have h1 := Superfunctor.app_eq_zero_of_mem hf (show (1 : ZMod 2) ≠ 0 by decide)
  change (moduleMap K f).total t _ = _
  rw [moduleMap_total_tensor, h1]
  simp only [SuperNatTrans.total, h1, add_zero]
  change tensor K N.toFunctor s g (f.app 0 s b) +
    tensor K N.toFunctor s (twist k 1 g) 0 = _
  rw [tensor_zero_right, add_zero]

/-- The ordinary-adjunction mate, with the upper append unit, prescribed
signed crossing, and induced lower append counit in their given order. -/
def orderedGridMateComponent (N : Superfunctor k A (SVec k)) :
    induced J ((restriction J).obj N) ⟶ (restriction K).obj (induced K N) :=
  gridModuleUnit K (induced J ((restriction J).obj N)) ≫
    (restriction K).map (-gridDoubleCrossComponent J K hα ((restriction J).obj N)) ≫
    (restriction K).map (gridInducedCounit J K N)

private theorem orderedGridMateComponent_total (N : Superfunctor k A (SVec k))
    (t : A) (x : (induced J ((restriction J).obj N)).obj t) :
    (orderedGridMateComponent J K hα N).total t x =
      (gridInducedCounit J K N).total (K.obj t)
        ((-gridDoubleCrossComponent J K hα ((restriction J).obj N)).total (K.obj t)
          (unit K (induced J ((restriction J).obj N)).toFunctor t x)) := by
  rw [orderedGridMateComponent, Superfunctor.comp_total, Superfunctor.comp_total]
  simp only [SVec.comp_apply]
  rw [gridUnit_total_apply, gridRestriction_total_apply, gridRestriction_total_apply]
  rfl

/-- The mate retains the extra minus and twists the complete appended
coefficient arrow. No homogeneity condition is imposed on that arrow. -/
theorem orderedGridMateComponent_total_tensor (N : Superfunctor k A (SVec k))
    (s : C) (t : A) (g : J.obj s ⟶ t) (b : N.obj (J.obj s)) :
    (orderedGridMateComponent J K hα N).total t
      (tensor J ((restriction J).obj N).toFunctor s g b) =
      -tensor K N.toFunctor (J.obj s) (α s ≫ twist k p (K.map g)) b := by
  rw [orderedGridMateComponent_total, unit_apply, gridNeg_total_apply]
  unfold gridDoubleCrossComponent
  rw [gridDoubleCrossComponent_total_tensor, map_neg]
  have he := gridInduction_map_even_tensor K
    (M := induced J ((restriction J).obj N)) (N := N)
    (gridModuleCounit J N) (adjunctionCounit_mem J N)
    (J.obj s) (K.obj t) (α s ≫ twist k p (K.map g ≫ 𝟙 _))
    (tensor J ((restriction J).obj N).toFunctor s (𝟙 _) b)
  have hc := gridCounit_total_tensor J N s (J.obj s) (𝟙 _) b
  have hi : N.map (𝟙 (J.obj s)) b = b := by
    change (N.toFunctor.map (𝟙 (J.obj s))) b = b
    rw [N.toFunctor.map_id]
    rfl
  have hr := congrArg (fun x : N.obj (J.obj s) =>
    tensor K N.toFunctor (J.obj s) (α s ≫ twist k p (K.map g ≫ 𝟙 _)) x) (hc.trans hi)
  have hn := congrArg Neg.neg (he.trans hr)
  simp only [Category.comp_id] at hn
  simp only [Category.comp_id]
  exact hn

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Literal coend values of the chosen changing-content crossing mate

The scalar and fixed-content comparisons of the prescribed first matrix
entry in DeformedMatrixComparison (2), (4) need the same given mate on raw
coends. These formulas expose its carriers before substituting concrete
append functors and put the extra minus into the coefficient arrow.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C A B : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

/-- The literal coend map of the chosen unit, signed crossing and counit. -/
def orderedGridMateLinear
    {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
    (hα : IsSupernatural k p α) (N : Superfunctor k A (SVec k)) (t : A) :
    Obj J ((restriction J).obj N).toFunctor t →ₗ[k] Obj K N.toFunctor (K.obj t) :=
  (orderedGridMateComponent J K hα N).total t

/-- The extra minus belongs to the complete crossed coefficient; neither
coefficient arrow nor module vector needs to be homogeneous. -/
theorem orderedGridMateLinear_tensor
    {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
    (hα : IsSupernatural k p α) (N : Superfunctor k A (SVec k))
    (s : C) (t : A) (g : J.obj s ⟶ t) (b : N.obj (J.obj s)) :
    orderedGridMateLinear J K hα N t
      (tensor J ((restriction J).obj N).toFunctor s g b) =
      tensor K N.toFunctor (J.obj s) (-(α s ≫ twist k p (K.map g))) b := by
  have h := orderedGridMateComponent_total_tensor J K hα N s t g b
  have hn : tensor K N.toFunctor (J.obj s) (-(α s ≫ twist k p (K.map g))) b =
      -tensor K N.toFunctor (J.obj s) (α s ≫ twist k p (K.map g)) b := by
    change inclusion K N.toFunctor (K.obj t) (J.obj s)
        ((-(α s ≫ twist k p (K.map g))) ⊗ₜ[k] b) =
      -inclusion K N.toFunctor (K.obj t) (J.obj s)
        ((α s ≫ twist k p (K.map g)) ⊗ₜ[k] b)
    rw [TensorProduct.neg_tmul, map_neg]
  set_option backward.dsimp.instances true in
    dsimp only [orderedGridMateLinear, induction] at h ⊢
  exact h.trans hn.symm

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Generator formula for a canonically transported induction transformation

The existing induction-composition isomorphism conjugates a homogeneous
transformation of a double functor. Its action on nested balanced tensors
retains the ordered composite and the full parity twist. The comparison
is exactly the existing canonical `inductionComp`, in both directions.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
variable (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
variable {p : ZMod 2} {α : ∀ s, (A ⋙ A).obj s ⟶ (A ⋙ A).obj s}
  (hα : IsSupernatural k p α)

private theorem transform_total (M : Superfunctor k C (SVec k))
    (w : C) :
    (BalancedInduction.transformComponent (hα) M).total w =
      BalancedInduction.transformLinear (hα) M w := by
  rcases parity_eq_zero_or_one p with h | h
  · simp only [SuperNatTrans.total, BalancedInduction.transformComponent_app, h,
      ↓reduceIte, one_ne_zero, add_zero]
  · simp only [SuperNatTrans.total, BalancedInduction.transformComponent_app, h,
      ↓reduceIte, zero_ne_one, zero_add]

private def flatten (M : Superfunctor k C (SVec k)) :
    BalancedInduction.induced A
      (BalancedInduction.induced A M) ⟶
    BalancedInduction.induced (A ⋙ A) M :=
  (BalancedInduction.inductionComp (k := k) A
    A).hom.app M

private def unflatten (M : Superfunctor k C (SVec k)) :
    BalancedInduction.induced (A ⋙ A) M ⟶
    BalancedInduction.induced A
      (BalancedInduction.induced A M) :=
  (BalancedInduction.inductionComp (k := k) A
    A).inv.app M

private theorem flatten_tensor (M : Superfunctor k C (SVec k))
    (s w t : C) (g : A.obj w ⟶ t) (h : A.obj s ⟶ w) (b : M.obj s) :
    (flatten A M).total t
      (tensor A (induced A M).toFunctor w g (tensor A M.toFunctor s h b)) =
    tensor (A ⋙ A) M.toFunctor s (A.map h ≫ g) b :=
  inductionComp_hom_total_tensor A A M s w t g h b

private theorem unflatten_tensor (M : Superfunctor k C (SVec k))
    (s t : C) (g : (A ⋙ A).obj s ⟶ t) (b : M.obj s) :
    (unflatten A M).total t (tensor (A ⋙ A) M.toFunctor s g b) =
    tensor A (induced A M).toFunctor (A.obj s) g (tensor A M.toFunctor s (𝟙 _) b) :=
  inductionComp_inv_total_tensor A A M s t g b

def doubleCrossComponent (M : Superfunctor k C (SVec k)) :
    End (BalancedInduction.induced A
      (BalancedInduction.induced A M)) :=
  flatten A M ≫
    BalancedInduction.transformComponent (hα) M ≫
      unflatten A M

private theorem doubleCrossComponent_total (M : Superfunctor k C (SVec k))
    (t : C) (x : Obj A (induced A M).toFunctor t) :
    (doubleCrossComponent A hα M).total t x =
      (unflatten A M).total t
        ((transformComponent hα M).total t ((flatten A M).total t x)) := by
  rw [doubleCrossComponent, Superfunctor.comp_total, Superfunctor.comp_total]
  rfl

theorem doubleCrossComponent_total_tensor (M : Superfunctor k C (SVec k))
    (s w t : C)
    (g : A.obj w ⟶ t)
    (h : A.obj s ⟶ w) (b : M.obj s) :
    (doubleCrossComponent A hα M).total t
      (BalancedInduction.tensor A
        (BalancedInduction.induced A M).toFunctor w g
          (BalancedInduction.tensor A M.toFunctor s h b)) =
    BalancedInduction.tensor A
      (BalancedInduction.induced A M).toFunctor
      (A.obj s)
      (α s ≫
        twist k p (A.map h ≫ g))
      (BalancedInduction.tensor A M.toFunctor s (𝟙 _) b) := by
  rw [doubleCrossComponent_total, flatten_tensor]
  have ht := congrArg
    (fun f : Obj (A ⋙ A) M.toFunctor t →ₗ[k] Obj (A ⋙ A) M.toFunctor t =>
      f (tensor (A ⋙ A) M.toFunctor s (A.map h ≫ g) b)) (transform_total A hα M t)
  have he := transformLinear_tensor hα M t s (A.map h ≫ g) b
  have hx := congrArg (fun x : Obj (A ⋙ A) M.toFunctor t =>
    (unflatten A M).total t x) (ht.trans he)
  exact hx.trans (unflatten_tensor A M s t (α s ≫ twist k p (A.map h ≫ g)) b)

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Homogeneous transformations under a commuting induction square

The generator transport in DeformedActionAssembly §§5–6 compares the
literal old/truncated coends before comparing their chosen isomorphisms.
A commuting square gives a canonical map of coends. It intertwines every
homogeneous append transformation whose coefficient arrows map through the
square, retaining the full parity twist of arbitrary coefficient arrows.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u

section Coends
variable {k : Type u} [CommRing k]
  {C A B D : Type u} [Category.{u} C] [Category.{u} A]
  [Category.{u} B] [Category.{u} D]
  [Preadditive A] [Linear k A] [Preadditive D] [Linear k D]
  (J : C ⥤ A) (U : A ⥤ D) [U.Additive] [U.Linear k]
  (Q : C ⥤ B) (T : B ⥤ D) (h : J ⋙ U = Q ⋙ T)

/-- The coefficient arrow of the canonical coend map through the square. -/
def coendSquareCoefficient (v : C) (w : A) :
    (J.obj v ⟶ w) →ₗ[k] (T.obj (Q.obj v) ⟶ U.obj w) where
  toFun g := eqToHom (congrArg (fun F : C ⥤ D => F.obj v) h).symm ≫ U.map g
  map_add' g g' := by rw [U.map_add, Preadditive.comp_add]
  map_smul' r g := by
    rw [U.map_smul, Linear.comp_smul]
    rfl

theorem coendSquareCoefficient_balance {v v' : C} (f : v ⟶ v')
    (w : A) (g : J.obj v' ⟶ w) :
    coendSquareCoefficient (k := k) J U Q T h v w (J.map f ≫ g) =
      T.map (Q.map f) ≫ coendSquareCoefficient (k := k) J U Q T h v' w g := by
  have hn := (eqToHom h.symm : Q ⋙ T ⟶ J ⋙ U).naturality f
  simp only [eqToHom_app, Functor.comp_map] at hn
  change eqToHom _ ≫ U.map (J.map f ≫ g) =
    T.map (Q.map f) ≫ (eqToHom _ ≫ U.map g)
  rw [U.map_comp, ← Category.assoc, ← hn, Category.assoc]

variable (M : B ⥤ SVec k)

private def coendSquareTensor (w : A) (v : C) :
    (J.obj v ⟶ w) ⊗[k] (Q ⋙ M).obj v →ₗ[k] Obj T M (U.obj w) :=
  inclusion T M (U.obj w) (Q.obj v) ∘ₗ
    TensorProduct.map (coendSquareCoefficient (k := k) J U Q T h v w) LinearMap.id

private theorem coendSquareTensor_tmul (w : A) (v : C)
    (g : J.obj v ⟶ w) (b : M.obj (Q.obj v)) :
    coendSquareTensor J U Q T h M w v (g ⊗ₜ[k] b) =
      tensor T M (Q.obj v) (coendSquareCoefficient (k := k) J U Q T h v w g) b := rfl

/-- The canonical map on literal coends induced by a commuting functor square.
No fullness, flatness or evenness assumption on coefficient arrows is needed. -/
def coendSquareMap (w : A) : Obj J (Q ⋙ M) w →ₗ[k] Obj T M (U.obj w) :=
  lift J (Q ⋙ M) w (coendSquareTensor J U Q T h M w) (by
    intro v v' f g b
    rw [coendSquareTensor_tmul, coendSquareTensor_tmul,
      coendSquareCoefficient_balance (k := k)]
    exact balance T M (Q.map f) (coendSquareCoefficient (k := k) J U Q T h v' w g) b)

@[simp] theorem coendSquareMap_tensor (w : A) (v : C)
    (g : J.obj v ⟶ w) (b : M.obj (Q.obj v)) :
    coendSquareMap J U Q T h M w (tensor J (Q ⋙ M) v g b) =
      tensor T M (Q.obj v)
        (eqToHom (congrArg (fun F : C ⥤ D => F.obj v) h).symm ≫ U.map g) b := by
  rw [coendSquareMap, lift_tensor, coendSquareTensor_tmul]
  rfl

end Coends

section Transform
variable {k : Type u} [CommRing k]
  {C A B D : Type u} [Category.{u} C] [Category.{u} A]
  [Category.{u} B] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (J K : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (U : A ⥤ D) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
  (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (T S : B ⥤ D) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  [S.Additive] [S.Linear k] [IsSuperfunctor k S]
  (hJ : J ⋙ U = Q ⋙ T) (hK : K ⋙ U = Q ⋙ S)
  (M : Superfunctor k B (SVec k))
  {p : ZMod 2} {α : ∀ v, J.obj v ⟶ K.obj v} {β : ∀ v, T.obj v ⟶ S.obj v}
  (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β)

end Transform
end OddMath.QuiverHecke.ELV.BalancedInduction
end

end
