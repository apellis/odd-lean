import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixFunctor
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedContentMatrixInverse

/-! # Weighted finite matrix inverses natural in input modules

Brundan–Ellis (1.13)–(1.14): assemble the specified parity-shifted fields
on all input-module maps and retain their canonical-content inverses.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- The prescribed shifted unit coordinate map, with explicit endpoint transport. -/
def weightedUnitMatrixCoordinateMap (i : I) (m : ℕ)
    {M L : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)} (f : M ⟶ L)
    (a : Option (Fin m)) :
    weightedUnitMatrixFamily D Sc cutoff N i M m a ⟶ weightedUnitMatrixFamily D Sc cutoff N i L m a :=
  eqToHom (weightedUnitMatrixSummandFunctor_obj D Sc cutoff N i M m a).symm ≫
    (weightedUnitMatrixSummandFunctor D Sc cutoff N i m a).map f ≫
      eqToHom (weightedUnitMatrixSummandFunctor_obj D Sc cutoff N i L m a)

/-- The prescribed shifted cap coordinate map, with explicit endpoint transport. -/
def weightedCapMatrixCoordinateMap (i : I) (m : ℕ)
    {M L : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)} (f : M ⟶ L)
    (a : Option (Fin m)) :
    weightedCapMatrixFamily D Sc cutoff N i M m a ⟶ weightedCapMatrixFamily D Sc cutoff N i L m a :=
  eqToHom (weightedCapMatrixSummandFunctor_obj D Sc cutoff N i M m a).symm ≫
    (weightedCapMatrixSummandFunctor D Sc cutoff N i m a).map f ≫
      eqToHom (weightedCapMatrixSummandFunctor_obj D Sc cutoff N i L m a)

/-- The full finite unit source is functorial on every supernatural module map. -/
def weightedUnitMatrixSourceFunctor (i : I) (m : ℕ) :
    Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k) ⥤
      Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k) where
  obj M := FiniteSupermodule.product (weightedUnitMatrixFamily D Sc cutoff N i M m)
  map f := FiniteSupermodule.productMap (weightedUnitMatrixCoordinateMap D Sc cutoff N i m f)
  map_id M := by
    rw [show weightedUnitMatrixCoordinateMap D Sc cutoff N i m (𝟙 M) =
      (fun a => 𝟙 (weightedUnitMatrixFamily D Sc cutoff N i M m a)) by
        funext a
        cases a <;> simp [weightedUnitMatrixCoordinateMap]]
    exact FiniteSupermodule.productMap_id _
  map_comp f g := by
    rw [← FiniteSupermodule.productMap_comp]
    congr 1
    funext a
    cases a <;> simp [weightedUnitMatrixCoordinateMap]

/-- The full finite cap target is functorial on every supernatural module map. -/
def weightedCapMatrixTargetFunctor (i : I) (m : ℕ) :
    Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k) ⥤
      Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k) where
  obj M := FiniteSupermodule.product (weightedCapMatrixFamily D Sc cutoff N i M m)
  map f := FiniteSupermodule.productMap (weightedCapMatrixCoordinateMap D Sc cutoff N i m f)
  map_id M := by
    rw [show weightedCapMatrixCoordinateMap D Sc cutoff N i m (𝟙 M) =
      (fun a => 𝟙 (weightedCapMatrixFamily D Sc cutoff N i M m a)) by
        funext a
        cases a <;> simp [weightedCapMatrixCoordinateMap]]
    exact FiniteSupermodule.productMap_id _
  map_comp f g := by
    rw [← FiniteSupermodule.productMap_comp]
    congr 1
    funext a
    cases a <;> simp [weightedCapMatrixCoordinateMap]

instance (i : I) (m : ℕ) : (weightedUnitMatrixSourceFunctor D Sc cutoff N i m).Additive where
  map_add {M L f g} := by
    change FiniteSupermodule.productMap (weightedUnitMatrixCoordinateMap D Sc cutoff N i m (f + g)) =
      FiniteSupermodule.productMap (weightedUnitMatrixCoordinateMap D Sc cutoff N i m f) +
        FiniteSupermodule.productMap (weightedUnitMatrixCoordinateMap D Sc cutoff N i m g)
    rw [← FiniteSupermodule.productMap_add]
    congr 1
    funext a
    cases a <;> simp [weightedUnitMatrixCoordinateMap]

instance (i : I) (m : ℕ) : (weightedCapMatrixTargetFunctor D Sc cutoff N i m).Additive where
  map_add {M L f g} := by
    change FiniteSupermodule.productMap (weightedCapMatrixCoordinateMap D Sc cutoff N i m (f + g)) =
      FiniteSupermodule.productMap (weightedCapMatrixCoordinateMap D Sc cutoff N i m f) +
        FiniteSupermodule.productMap (weightedCapMatrixCoordinateMap D Sc cutoff N i m g)
    rw [← FiniteSupermodule.productMap_add]
    congr 1
    funext a
    cases a <;> simp [weightedCapMatrixCoordinateMap]

instance (i : I) (m : ℕ) : (weightedUnitMatrixSourceFunctor D Sc cutoff N i m).Linear k where
  map_smul f r := by
    change FiniteSupermodule.productMap (weightedUnitMatrixCoordinateMap D Sc cutoff N i m (r • f)) =
      r • FiniteSupermodule.productMap (weightedUnitMatrixCoordinateMap D Sc cutoff N i m f)
    rw [← FiniteSupermodule.productMap_smul]
    congr 1
    funext a
    cases a <;> simp [weightedUnitMatrixCoordinateMap]

instance (i : I) (m : ℕ) : (weightedCapMatrixTargetFunctor D Sc cutoff N i m).Linear k where
  map_smul f r := by
    change FiniteSupermodule.productMap (weightedCapMatrixCoordinateMap D Sc cutoff N i m (r • f)) =
      r • FiniteSupermodule.productMap (weightedCapMatrixCoordinateMap D Sc cutoff N i m f)
    rw [← FiniteSupermodule.productMap_smul]
    congr 1
    funext a
    cases a <;> simp [weightedCapMatrixCoordinateMap]

instance (i : I) (m : ℕ) : IsSuperfunctor k (weightedUnitMatrixSourceFunctor D Sc cutoff N i m) where
  map_mem {M L p f} hf := by
    apply FiniteSupermodule.productMap_mem
    intro a
    exact (show weightedUnitMatrixCoordinateMap D Sc cutoff N i m f a ∈ parity (R := k) _ _ p from by
      simpa only [weightedUnitMatrixCoordinateMap, zero_add, add_zero] using
        comp_mem (eqToHom_mem (R := k)
          (weightedUnitMatrixSummandFunctor_obj D Sc cutoff N i M m a).symm)
          (comp_mem (IsSuperfunctor.map_mem
            (F := weightedUnitMatrixSummandFunctor D Sc cutoff N i m a) hf)
            (eqToHom_mem (R := k) (weightedUnitMatrixSummandFunctor_obj D Sc cutoff N i L m a))))

instance (i : I) (m : ℕ) : IsSuperfunctor k (weightedCapMatrixTargetFunctor D Sc cutoff N i m) where
  map_mem {M L p f} hf := by
    apply FiniteSupermodule.productMap_mem
    intro a
    exact (show weightedCapMatrixCoordinateMap D Sc cutoff N i m f a ∈ parity (R := k) _ _ p from by
      simpa only [weightedCapMatrixCoordinateMap, zero_add, add_zero] using
        comp_mem (eqToHom_mem (R := k)
          (weightedCapMatrixSummandFunctor_obj D Sc cutoff N i M m a).symm)
          (comp_mem (IsSuperfunctor.map_mem
            (F := weightedCapMatrixSummandFunctor D Sc cutoff N i m a) hf)
            (eqToHom_mem (R := k) (weightedCapMatrixSummandFunctor_obj D Sc cutoff N i L m a))))

/-- The whole finite unit matrix is natural in arbitrary input-module maps. -/
def weightedUnitMatrixModuleNatTrans (i : I) (m : ℕ) :
    weightedUnitMatrixSourceFunctor D Sc cutoff N i m ⟶
      BalancedInduction.induction (truncatedAppend D Sc cutoff N [i]) ⋙
        BalancedInduction.restriction (truncatedAppend D Sc cutoff N [i]) where
  app := fun M => weightedUnitMatrixModuleMap D Sc cutoff N i M m
  naturality M L f := by
    apply FiniteSupermodule.productMap_columnsHom
    intro a
    cases a with
    | none => simpa [weightedUnitMatrixCoordinateMap, weightedUnitMatrixEntryNatTrans_app] using
        (weightedUnitMatrixEntryNatTrans D Sc cutoff N i m none).naturality f
    | some r => simpa [weightedUnitMatrixCoordinateMap, weightedUnitMatrixEntryNatTrans_app] using
        (weightedUnitMatrixEntryNatTrans D Sc cutoff N i m (some r)).naturality f

/-- The whole finite cap matrix is natural in arbitrary input-module maps. -/
def weightedCapMatrixModuleNatTrans (i : I) (m : ℕ) :
    BalancedInduction.restriction (truncatedAppend D Sc cutoff N [i]) ⋙
      BalancedInduction.induction (truncatedAppend D Sc cutoff N [i]) ⟶
        weightedCapMatrixTargetFunctor D Sc cutoff N i m where
  app := fun M => weightedCapMatrixModuleMap D Sc cutoff N i M m
  naturality M L f := by
    symm
    apply FiniteSupermodule.rowsHom_productMap
    intro a
    cases a with
    | none => simpa [weightedCapMatrixCoordinateMap, weightedCapMatrixEntryNatTrans_app] using
        ((weightedCapMatrixEntryNatTrans D Sc cutoff N i m none).naturality f).symm
    | some r => simpa [weightedCapMatrixCoordinateMap, weightedCapMatrixEntryNatTrans_app] using
        ((weightedCapMatrixEntryNatTrans D Sc cutoff N i m (some r)).naturality f).symm


/-- The prescribed weighted unit matrix inverse is natural in every input-module map. -/
def weightedContentUnitMatrixFunctorNatIso (i : I) (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) :
    (weightedUnitMatrixSourceFunctor D Sc cutoff N i (contentUnitCount D cutoff i β) ⋙
      restriction (contentInclusion D Sc cutoff N β)) ≅
    ((induction (truncatedAppend D Sc cutoff N [i]) ⋙ restriction (truncatedAppend D Sc cutoff N [i])) ⋙
      restriction (contentInclusion D Sc cutoff N β)) :=
  NatIso.ofComponents (fun M => weightedContentUnitMatrixIso D Sc cutoff N i M β hh) (by
    intro M L f
    simp only [weightedContentUnitMatrixIso_hom, weightedContentUnitMatrixMap, Functor.comp_map]
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun g => (restriction (contentInclusion D Sc cutoff N β)).map g)
      ((weightedUnitMatrixModuleNatTrans D Sc cutoff N i (contentUnitCount D cutoff i β)).naturality f))

/-- The prescribed weighted cap matrix inverse is natural in every input-module map. -/
def weightedContentCapMatrixFunctorNatIso (i : I) (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) :
    ((restriction (truncatedAppend D Sc cutoff N [i]) ⋙ induction (truncatedAppend D Sc cutoff N [i])) ⋙
      restriction (contentInclusion D Sc cutoff N β)) ≅
    (weightedCapMatrixTargetFunctor D Sc cutoff N i (contentCapCount D cutoff i β) ⋙
      restriction (contentInclusion D Sc cutoff N β)) :=
  NatIso.ofComponents (fun M => weightedContentCapMatrixIso D Sc cutoff N i M β hh) (by
    intro M L f
    simp only [weightedContentCapMatrixIso_hom, weightedContentCapMatrixMap, Functor.comp_map]
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun g => (restriction (contentInclusion D Sc cutoff N β)).map g)
      ((weightedCapMatrixModuleNatTrans D Sc cutoff N i (contentCapCount D cutoff i β)).naturality f))

/-- The unit functor isomorphism retains the given weighted forward matrix. -/
theorem weightedContentUnitMatrixFunctorNatIso_hom_total (i : I) (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (w : ContentCategory D Sc cutoff N β) :
    ((weightedContentUnitMatrixFunctorNatIso D Sc cutoff N i β hh).hom.app M).total w =
      weightedUnitMatrixComponent D Sc cutoff N i M (contentUnitCount D cutoff i β) w.obj :=
  weightedContentUnitMatrixIso_hom_total D Sc cutoff N i M β hh w

/-- The cap functor isomorphism retains the given weighted forward matrix. -/
theorem weightedContentCapMatrixFunctorNatIso_hom_total (i : I) (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (w : ContentCategory D Sc cutoff N β) :
    ((weightedContentCapMatrixFunctorNatIso D Sc cutoff N i β hh).hom.app M).total w =
      weightedCapMatrixComponent D Sc cutoff N i M (contentCapCount D cutoff i β) w.obj :=
  weightedContentCapMatrixIso_hom_total D Sc cutoff N i M β hh w

theorem weightedContentUnitMatrixFunctorNatIso_even (i : I) (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (weightedContentUnitMatrixFunctorNatIso D Sc cutoff N i β hh).hom.app M ∈ parity (R := k) _ _ 0 ∧
      (weightedContentUnitMatrixFunctorNatIso D Sc cutoff N i β hh).inv.app M ∈ parity (R := k) _ _ 0 := by
  constructor
  · rw [show (weightedContentUnitMatrixFunctorNatIso D Sc cutoff N i β hh).hom.app M =
      weightedContentUnitMatrixMap D Sc cutoff N i M β from weightedContentUnitMatrixIso_hom D Sc cutoff N i M β hh]
    exact weightedContentUnitMatrixMap_mem D Sc cutoff N i M β
  · exact weightedContentUnitMatrixIso_inv_mem D Sc cutoff N i M β hh

theorem weightedContentCapMatrixFunctorNatIso_even (i : I) (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (weightedContentCapMatrixFunctorNatIso D Sc cutoff N i β hh).hom.app M ∈ parity (R := k) _ _ 0 ∧
      (weightedContentCapMatrixFunctorNatIso D Sc cutoff N i β hh).inv.app M ∈ parity (R := k) _ _ 0 := by
  constructor
  · rw [show (weightedContentCapMatrixFunctorNatIso D Sc cutoff N i β hh).hom.app M =
      weightedContentCapMatrixMap D Sc cutoff N i M β from weightedContentCapMatrixIso_hom D Sc cutoff N i M β hh]
    exact weightedContentCapMatrixMap_mem D Sc cutoff N i M β
  · exact weightedContentCapMatrixIso_inv_mem D Sc cutoff N i M β hh

end OddMath.QuiverHecke.ELVOld
