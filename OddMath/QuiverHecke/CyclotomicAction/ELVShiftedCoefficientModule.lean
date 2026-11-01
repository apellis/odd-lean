import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedCoefficientComparison

/-! # Actual shifted coefficient supermodule and canonical source transport

The prescribed coefficient(1) functor is packaged as its actual supermodule,
using its independently proved action/projection comparison. The resulting
even module isomorphism is mapped through actual induction. Composition with
the canonical parity source isomorphism gives whole coend transport and
an equality with the actual adjunction counit.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem coefficientOne_obj_part (i : I) (v : List I) (s : OldCategory D Sc cutoff)
    (q : ZMod 2) :
    ((coefficient D Sc cutoff 1 i v).obj s).part q =
      ((parityRestrictedRepresentable D Sc cutoff i v).obj s).part q := by
  ext b
  rw [SVec.mem_part_iff, SVec.mem_part_iff, coefficientOne_obj_proj]

instance coefficientOne_additive (i : I) (v : List I) :
    (coefficient D Sc cutoff 1 i v).Additive where
  map_add {s t} f g := by
    apply LinearMap.ext
    intro b
    change (coefficient D Sc cutoff 1 i v).map (f + g) b =
      (coefficient D Sc cutoff 1 i v).map f b + (coefficient D Sc cutoff 1 i v).map g b
    rw [coefficientOne_map, coefficientOne_map, coefficientOne_map]
    exact congrArg (fun h => h b)
      ((parityRestrictedRepresentable D Sc cutoff i v).toFunctor.map_add f g)

instance coefficientOne_linear (i : I) (v : List I) :
    (coefficient D Sc cutoff 1 i v).Linear k where
  map_smul {s t} f r := by
    apply LinearMap.ext
    intro b
    change (coefficient D Sc cutoff 1 i v).map (r • f) b =
      r • (coefficient D Sc cutoff 1 i v).map f b
    rw [coefficientOne_map, coefficientOne_map]
    exact congrArg (fun h => h b)
      ((parityRestrictedRepresentable D Sc cutoff i v).toFunctor.map_smul f r)

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
      simp
  inv_hom_id := by
    apply Superfunctor.hom_ext
    intro p s
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp only [Superfunctor.comp_app, coefficientModuleForward_app,
        coefficientModuleBackward_app, Superfunctor.id_app_zero, Superfunctor.id_app_one,
        ↓reduceIte, zero_add, one_ne_zero, SVec.zmod2_one_add_one]
    all_goals
      ext b
      simp


/-- Its actual induced carrier is the prescribed balanced source at odd colour.
The equivalence is literal identity after the moving parity equality. -/
def coefficientOneSourceEquiv (j : {j : I // D.parity j = 1}) (v t : List I) :
    ((BalancedInduction.induction (append D Sc cutoff j.1)).obj
      (coefficientOneModule D Sc cutoff j.1 v)).obj (⟨t⟩ : OldCategory D Sc cutoff) ≃ₗ[k]
      Source D Sc cutoff j.1 v t := by
  change BalancedInduction.Obj (append D Sc cutoff j.1)
      (coefficient D Sc cutoff 1 j.1 v) (⟨t⟩ : OldCategory D Sc cutoff) ≃ₗ[k]
    BalancedInduction.Obj (append D Sc cutoff j.1)
      (coefficient D Sc cutoff (D.parity j.1) j.1 v) (⟨t⟩ : OldCategory D Sc cutoff)
  rw [j.property]
  exact LinearEquiv.refl k _

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

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
