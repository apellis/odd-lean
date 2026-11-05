import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.QuiverHecke.CyclotomicAction.ELVMatrixEntryNaturality

/-! # Whole prescribed matrices natural in input modules

DeformedMatrixComparison section 4, finite-family assembly of the unit/cap
entries. This assembly includes odd and inhomogeneous input maps.
The fixed-content inverse construction is in ELVContentMatrixFunctorInverse;
identification with the chosen content E/F composites remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The prescribed shifted unit coordinate map, with explicit endpoint transport. -/
def unitMatrixCoordinateMap (i : I) (m : ℕ)
    {M N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)} (f : M ⟶ N)
    (a : Option (Fin m)) :
    unitMatrixFamily D Sc cutoff i M m a ⟶ unitMatrixFamily D Sc cutoff i N m a :=
  eqToHom (unitMatrixSummandFunctor_obj D Sc cutoff i m a M).symm ≫
    (unitMatrixSummandFunctor D Sc cutoff i m a).map f ≫
      eqToHom (unitMatrixSummandFunctor_obj D Sc cutoff i m a N)

/-- The prescribed shifted cap coordinate map, with explicit endpoint transport. -/
def capMatrixCoordinateMap (i : I) (m : ℕ)
    {M N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)} (f : M ⟶ N)
    (a : Option (Fin m)) :
    capMatrixFamily D Sc cutoff i M m a ⟶ capMatrixFamily D Sc cutoff i N m a :=
  eqToHom (capMatrixSummandFunctor_obj D Sc cutoff i m a M).symm ≫
    (capMatrixSummandFunctor D Sc cutoff i m a).map f ≫
      eqToHom (capMatrixSummandFunctor_obj D Sc cutoff i m a N)

/-- The full finite unit source is functorial on every supernatural module map. -/
def unitMatrixSourceFunctor (i : I) (m : ℕ) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) ⥤
      Superfunctor k (OldCategory D Sc cutoff) (SVec k) where
  obj M := FiniteSupermodule.product (unitMatrixFamily D Sc cutoff i M m)
  map f := FiniteSupermodule.productMap (unitMatrixCoordinateMap D Sc cutoff i m f)
  map_id M := by
    rw [show unitMatrixCoordinateMap D Sc cutoff i m (𝟙 M) =
      (fun a => 𝟙 (unitMatrixFamily D Sc cutoff i M m a)) by
        funext a
        cases a <;> simp [unitMatrixCoordinateMap]]
    exact FiniteSupermodule.productMap_id _
  map_comp f g := by
    rw [← FiniteSupermodule.productMap_comp]
    congr 1
    funext a
    cases a <;> simp [unitMatrixCoordinateMap]

/-- The full finite cap target is functorial on every supernatural module map. -/
def capMatrixTargetFunctor (i : I) (m : ℕ) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) ⥤
      Superfunctor k (OldCategory D Sc cutoff) (SVec k) where
  obj M := FiniteSupermodule.product (capMatrixFamily D Sc cutoff i M m)
  map f := FiniteSupermodule.productMap (capMatrixCoordinateMap D Sc cutoff i m f)
  map_id M := by
    rw [show capMatrixCoordinateMap D Sc cutoff i m (𝟙 M) =
      (fun a => 𝟙 (capMatrixFamily D Sc cutoff i M m a)) by
        funext a
        cases a <;> simp [capMatrixCoordinateMap]]
    exact FiniteSupermodule.productMap_id _
  map_comp f g := by
    rw [← FiniteSupermodule.productMap_comp]
    congr 1
    funext a
    cases a <;> simp [capMatrixCoordinateMap]

instance (i : I) (m : ℕ) : (unitMatrixSourceFunctor D Sc cutoff i m).Additive where
  map_add {M N f g} := by
    change FiniteSupermodule.productMap (unitMatrixCoordinateMap D Sc cutoff i m (f + g)) =
      FiniteSupermodule.productMap (unitMatrixCoordinateMap D Sc cutoff i m f) +
        FiniteSupermodule.productMap (unitMatrixCoordinateMap D Sc cutoff i m g)
    rw [← FiniteSupermodule.productMap_add]
    congr 1
    funext a
    cases a <;> simp [unitMatrixCoordinateMap]

instance (i : I) (m : ℕ) : (capMatrixTargetFunctor D Sc cutoff i m).Additive where
  map_add {M N f g} := by
    change FiniteSupermodule.productMap (capMatrixCoordinateMap D Sc cutoff i m (f + g)) =
      FiniteSupermodule.productMap (capMatrixCoordinateMap D Sc cutoff i m f) +
        FiniteSupermodule.productMap (capMatrixCoordinateMap D Sc cutoff i m g)
    rw [← FiniteSupermodule.productMap_add]
    congr 1
    funext a
    cases a <;> simp [capMatrixCoordinateMap]

instance (i : I) (m : ℕ) : (unitMatrixSourceFunctor D Sc cutoff i m).Linear k where
  map_smul f r := by
    change FiniteSupermodule.productMap (unitMatrixCoordinateMap D Sc cutoff i m (r • f)) =
      r • FiniteSupermodule.productMap (unitMatrixCoordinateMap D Sc cutoff i m f)
    rw [← FiniteSupermodule.productMap_smul]
    congr 1
    funext a
    cases a <;> simp [unitMatrixCoordinateMap]

instance (i : I) (m : ℕ) : (capMatrixTargetFunctor D Sc cutoff i m).Linear k where
  map_smul f r := by
    change FiniteSupermodule.productMap (capMatrixCoordinateMap D Sc cutoff i m (r • f)) =
      r • FiniteSupermodule.productMap (capMatrixCoordinateMap D Sc cutoff i m f)
    rw [← FiniteSupermodule.productMap_smul]
    congr 1
    funext a
    cases a <;> simp [capMatrixCoordinateMap]

instance (i : I) (m : ℕ) : IsSuperfunctor k (unitMatrixSourceFunctor D Sc cutoff i m) where
  map_mem {M N p f} hf := by
    apply FiniteSupermodule.productMap_mem
    intro a
    exact (show unitMatrixCoordinateMap D Sc cutoff i m f a ∈ parity (R := k) _ _ p from by
      simpa only [unitMatrixCoordinateMap, zero_add, add_zero] using
        comp_mem (eqToHom_mem (R := k)
          (unitMatrixSummandFunctor_obj D Sc cutoff i m a M).symm)
          (comp_mem (IsSuperfunctor.map_mem
            (F := unitMatrixSummandFunctor D Sc cutoff i m a) hf)
            (eqToHom_mem (R := k) (unitMatrixSummandFunctor_obj D Sc cutoff i m a N))))

instance (i : I) (m : ℕ) : IsSuperfunctor k (capMatrixTargetFunctor D Sc cutoff i m) where
  map_mem {M N p f} hf := by
    apply FiniteSupermodule.productMap_mem
    intro a
    exact (show capMatrixCoordinateMap D Sc cutoff i m f a ∈ parity (R := k) _ _ p from by
      simpa only [capMatrixCoordinateMap, zero_add, add_zero] using
        comp_mem (eqToHom_mem (R := k)
          (capMatrixSummandFunctor_obj D Sc cutoff i m a M).symm)
          (comp_mem (IsSuperfunctor.map_mem
            (F := capMatrixSummandFunctor D Sc cutoff i m a) hf)
            (eqToHom_mem (R := k) (capMatrixSummandFunctor_obj D Sc cutoff i m a N))))

/-- The literal finite unit matrix as an even module map. -/
def unitMatrixModuleMap (i : I) (m : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (unitMatrixSourceFunctor D Sc cutoff i m).obj M ⟶
      (BalancedInduction.induction (append D Sc cutoff i) ⋙
        BalancedInduction.restriction (append D Sc cutoff i)).obj M :=
  FiniteSupermodule.columnsHom (unitMatrixEntry D Sc cutoff i M m)
    (unitMatrixEntry_mem D Sc cutoff i M m)

/-- The literal finite cap matrix as an even module map. -/
def capMatrixModuleMap (i : I) (m : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (BalancedInduction.restriction (append D Sc cutoff i) ⋙
      BalancedInduction.induction (append D Sc cutoff i)).obj M ⟶
        (capMatrixTargetFunctor D Sc cutoff i m).obj M :=
  FiniteSupermodule.rowsHom (capMatrixEntry D Sc cutoff i M m)
    (capMatrixEntry_mem D Sc cutoff i M m)

/-- The whole finite unit matrix is natural in arbitrary input-module maps. -/
def unitMatrixModuleNatTrans (i : I) (m : ℕ) :
    unitMatrixSourceFunctor D Sc cutoff i m ⟶
      BalancedInduction.induction (append D Sc cutoff i) ⋙
        BalancedInduction.restriction (append D Sc cutoff i) where
  app := unitMatrixModuleMap D Sc cutoff i m
  naturality M N f := by
    apply FiniteSupermodule.productMap_columnsHom
    intro a
    cases a with
    | none => simpa [unitMatrixCoordinateMap, unitMatrixEntryNatTrans_app] using
        (unitMatrixEntryNatTrans D Sc cutoff i m none).naturality f
    | some r => simpa [unitMatrixCoordinateMap, unitMatrixEntryNatTrans_app] using
        (unitMatrixEntryNatTrans D Sc cutoff i m (some r)).naturality f

/-- The whole finite cap matrix is natural in arbitrary input-module maps. -/
def capMatrixModuleNatTrans (i : I) (m : ℕ) :
    BalancedInduction.restriction (append D Sc cutoff i) ⋙
      BalancedInduction.induction (append D Sc cutoff i) ⟶
        capMatrixTargetFunctor D Sc cutoff i m where
  app := capMatrixModuleMap D Sc cutoff i m
  naturality M N f := by
    symm
    apply FiniteSupermodule.rowsHom_productMap
    intro a
    cases a with
    | none => simpa [capMatrixCoordinateMap, capMatrixEntryNatTrans_app] using
        ((capMatrixEntryNatTrans D Sc cutoff i m none).naturality f).symm
    | some r => simpa [capMatrixCoordinateMap, capMatrixEntryNatTrans_app] using
        ((capMatrixEntryNatTrans D Sc cutoff i m (some r)).naturality f).symm

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
