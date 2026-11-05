import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixComponentInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockExtension
import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.Algebra.SupermoduleIsoOfBijectiveTotals

/-! # Weighted matrix isomorphisms on canonical content modules

Brundan–Ellis (1.13)–(1.14): the specified finite weighted module matrices
are invertible after restriction to their canonical output content block.
The proof uses the established inverses of those exact forward components.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u

private theorem columnsHom_even {k : Type u} [CommRing k]
    {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} [Fintype ι] {V : ι → Superfunctor k C (SVec k)}
    {T : Superfunctor k C (SVec k)} (f : ∀ a, V a ⟶ T)
    (hf : ∀ a, f a ∈ parity (R := k) _ _ 0) :
    OddMath.FiniteSupermodule.columnsHom f hf ∈ parity (R := k) _ _ 0 :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr (SuperNatTrans.ofNatTrans_isHomogeneous _ _)

private theorem rowsHom_even {k : Type u} [CommRing k]
    {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} {V : ι → Superfunctor k C (SVec k)}
    {T : Superfunctor k C (SVec k)} (f : ∀ a, T ⟶ V a)
    (hf : ∀ a, f a ∈ parity (R := k) _ _ 0) :
    OddMath.FiniteSupermodule.rowsHom f hf ∈ parity (R := k) _ _ 0 :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr (SuperNatTrans.ofNatTrans_isHomogeneous _ _)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))

/-- The prescribed finite unit columns, as one module morphism. -/
def weightedUnitMatrixModuleMap (m : ℕ) :=
  OddMath.FiniteSupermodule.columnsHom (weightedUnitMatrixEntry D Sc cutoff N i M m)
    (weightedUnitMatrixEntry_mem D Sc cutoff N i M m)
/-- The prescribed finite cap rows, as one module morphism. -/
def weightedCapMatrixModuleMap (m : ℕ) :=
  OddMath.FiniteSupermodule.rowsHom (weightedCapMatrixEntry D Sc cutoff N i M m)
    (weightedCapMatrixEntry_mem D Sc cutoff N i M m)

theorem weightedUnitMatrixModuleMap_mem (m : ℕ) :
    weightedUnitMatrixModuleMap D Sc cutoff N i M m ∈ parity (R := k) _ _ 0 :=
  columnsHom_even _ _
theorem weightedCapMatrixModuleMap_mem (m : ℕ) :
    weightedCapMatrixModuleMap D Sc cutoff N i M m ∈ parity (R := k) _ _ 0 :=
  rowsHom_even _ _

/-- Evaluation is exactly the specified unit forward matrix. -/
theorem weightedUnitMatrixModuleMap_total (m : ℕ) (w : TruncatedCategory D Sc cutoff N) :
    (weightedUnitMatrixModuleMap D Sc cutoff N i M m).total w =
      weightedUnitMatrixComponent D Sc cutoff N i M m w := by
  ext x
  exact OddMath.FiniteSupermodule.columnsHom_total_apply _ _ w x

/-- Evaluation is exactly the specified cap forward matrix. -/
theorem weightedCapMatrixModuleMap_total (m : ℕ) (w : TruncatedCategory D Sc cutoff N) :
    (weightedCapMatrixModuleMap D Sc cutoff N i M m).total w =
      weightedCapMatrixComponent D Sc cutoff N i M m w := by
  apply LinearMap.ext
  intro x
  funext a
  exact OddMath.FiniteSupermodule.rowsHom_total_apply _ _ w x a

private theorem weightedUnitMatrix_bijectiveAtCount (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (m : ℕ) (hm : contentUnitCount D cutoff i (w.word : Multiset I) = m) :
    Function.Bijective ((weightedUnitMatrixModuleMap D Sc cutoff N i M m).total
      ((oldTruncateFunctor D Sc cutoff N).obj w)) := by
  subst m
  rw [weightedUnitMatrixModuleMap_total]
  exact weightedUnitMatrixComponent_bijective D Sc cutoff N i M w hh

private theorem weightedCapMatrix_bijectiveAtCount (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0)
    (m : ℕ) (hm : contentCapCount D cutoff i (w.word : Multiset I) = m) :
    Function.Bijective ((weightedCapMatrixModuleMap D Sc cutoff N i M m).total
      ((oldTruncateFunctor D Sc cutoff N).obj w)) := by
  subst m
  rw [weightedCapMatrixModuleMap_total]
  exact weightedCapMatrixComponent_bijective D Sc cutoff N i M w hh

/-- Restrict the specified unit map to its canonical output content. -/
def weightedContentUnitMatrixMap (β : Multiset I) :=
  (restriction (contentInclusion D Sc cutoff N β)).map
    (weightedUnitMatrixModuleMap D Sc cutoff N i M (contentUnitCount D cutoff i β))
/-- Restrict the specified cap map to its canonical output content. -/
def weightedContentCapMatrixMap (β : Multiset I) :=
  (restriction (contentInclusion D Sc cutoff N β)).map
    (weightedCapMatrixModuleMap D Sc cutoff N i M (contentCapCount D cutoff i β))

theorem weightedContentUnitMatrixMap_mem (β : Multiset I) :
    weightedContentUnitMatrixMap D Sc cutoff N i M β ∈ parity (R := k) _ _ 0 :=
  map_mem (restriction (contentInclusion D Sc cutoff N β))
    (weightedUnitMatrixModuleMap_mem D Sc cutoff N i M _)
theorem weightedContentCapMatrixMap_mem (β : Multiset I) :
    weightedContentCapMatrixMap D Sc cutoff N i M β ∈ parity (R := k) _ _ 0 :=
  map_mem (restriction (contentInclusion D Sc cutoff N β))
    (weightedCapMatrixModuleMap_mem D Sc cutoff N i M _)

theorem weightedContentUnitMatrixMap_bijective (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β) :
    Function.Bijective ((weightedContentUnitMatrixMap D Sc cutoff N i M β).total w) := by
  exact weightedUnitMatrix_bijectiveAtCount D Sc cutoff N i M ⟨w.obj.word⟩
    (by simpa only [w.content] using hh) _
    (congrArg (contentUnitCount D cutoff i) w.content)

theorem weightedContentCapMatrixMap_bijective (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β) :
    Function.Bijective ((weightedContentCapMatrixMap D Sc cutoff N i M β).total w) := by
  exact weightedCapMatrix_bijectiveAtCount D Sc cutoff N i M ⟨w.obj.word⟩
    (by simpa only [w.content] using hh) _
    (congrArg (contentCapCount D cutoff i) w.content)

/-- The prescribed unit matrix is an isomorphism on its canonical content block. -/
def weightedContentUnitMatrixIso (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) :=
  OddMath.HomogeneousSuperfunctorIso.ofBijectiveTotals
    (weightedContentUnitMatrixMap D Sc cutoff N i M β)
    (weightedContentUnitMatrixMap_mem D Sc cutoff N i M β)
    (weightedContentUnitMatrixMap_bijective D Sc cutoff N i M β hh)

/-- The prescribed cap matrix is an isomorphism on its canonical content block. -/
def weightedContentCapMatrixIso (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) :=
  OddMath.HomogeneousSuperfunctorIso.ofBijectiveTotals
    (weightedContentCapMatrixMap D Sc cutoff N i M β)
    (weightedContentCapMatrixMap_mem D Sc cutoff N i M β)
    (weightedContentCapMatrixMap_bijective D Sc cutoff N i M β hh)

theorem weightedContentUnitMatrixIso_hom (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) :
    (weightedContentUnitMatrixIso D Sc cutoff N i M β hh).hom =
      weightedContentUnitMatrixMap D Sc cutoff N i M β :=
  OddMath.HomogeneousSuperfunctorIso.ofBijectiveTotals_hom _ _ _
theorem weightedContentCapMatrixIso_hom (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) :
    (weightedContentCapMatrixIso D Sc cutoff N i M β hh).hom =
      weightedContentCapMatrixMap D Sc cutoff N i M β :=
  OddMath.HomogeneousSuperfunctorIso.ofBijectiveTotals_hom _ _ _

theorem weightedContentUnitMatrixIso_hom_total (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β) :
    (weightedContentUnitMatrixIso D Sc cutoff N i M β hh).hom.total w =
      weightedUnitMatrixComponent D Sc cutoff N i M (contentUnitCount D cutoff i β) w.obj := by
  rw [weightedContentUnitMatrixIso_hom]
  exact weightedUnitMatrixModuleMap_total D Sc cutoff N i M _ w.obj

theorem weightedContentCapMatrixIso_hom_total (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β) :
    (weightedContentCapMatrixIso D Sc cutoff N i M β hh).hom.total w =
      weightedCapMatrixComponent D Sc cutoff N i M (contentCapCount D cutoff i β) w.obj := by
  rw [weightedContentCapMatrixIso_hom]
  exact weightedCapMatrixModuleMap_total D Sc cutoff N i M _ w.obj

end OddMath.QuiverHecke.ELVOld
