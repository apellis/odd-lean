import OddMath.Algebra.FiniteSuperspace
import OddMath.QuiverHecke.CyclotomicAction.ELVActualMatrixFamilies

/-! # Actual finite matrix component maps and their parity
Brundan--Ellis (1.13)--(1.14) assemble the prescribed even module
entries on the actual finite parity-shifted superspace families.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.MatrixComponentParity
universe u
variable {k : Type u} [CommRing k]
variable {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

private theorem total_even {F G : Superfunctor k C (SVec k)}
    (f : F ⟶ G) (hf : f ∈ parity (R := k) F G 0) (t : C) :
    f.total t ∈ parity (R := k) (F.obj t) (G.obj t) 0 := by
  have hz := Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) t
  have ht : f.total t = f.app 0 t := by
    rw [SuperNatTrans.total, hz, add_zero]
  rw [ht]
  exact f.app_mem 0 t

private theorem inverse_precompose_total {F G H : Superfunctor k C (SVec k)}
    (e : F ≅ G) (f : F ⟶ H) (t : C) (z : G.obj t) :
    f.total t ((moduleIsoLinearEquiv e t).symm z) = (e.inv ≫ f).total t z := by
  rw [Superfunctor.comp_total]
  rfl

private theorem postcompose_total {F G H : Superfunctor k C (SVec k)}
    (e : G ≅ H) (f : F ⟶ G) (t : C) (z : F.obj t) :
    moduleIsoLinearEquiv e t (f.total t z) = (f ≫ e.hom).total t z := by
  rw [Superfunctor.comp_total]
  rfl

end OddMath.QuiverHecke.ELVOld.MatrixComponentParity

namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The actual finite source superspace with its pointwise shifted grading. -/
def unitMatrixSourceSpace (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff) : SVec k :=
  OddMath.FiniteSuperspace.product fun a => (unitMatrixFamily D Sc cutoff i M m a).obj t

/-- The actual finite target superspace with its pointwise shifted grading. -/
def capMatrixTargetSpace (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff) : SVec k :=
  OddMath.FiniteSuperspace.product fun a => (capMatrixFamily D Sc cutoff i M m a).obj t

/-- Finite assembly of the actual unit-family entries. -/
def unitMatrixComponent (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff) :
    unitMatrixSourceSpace D Sc cutoff i M m t ⟶
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj M)).obj t :=
  OddMath.FiniteSuperspace.assembleColumns _ _
    fun a => (unitMatrixEntry D Sc cutoff i M m a).total t

/-- Finite assembly of the actual cap-family entries. -/
def capMatrixComponent (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff) :
    ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t ⟶
        capMatrixTargetSpace D Sc cutoff i M m t :=
  OddMath.FiniteSuperspace.assembleRows _ _
    fun a => (capMatrixEntry D Sc cutoff i M m a).total t

/-- The actual finite unit matrix is even, for every old module. -/
theorem unitMatrixComponent_even (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff) :
    unitMatrixComponent D Sc cutoff i M m t ∈ parity (R := k) _ _ 0 := by
  apply OddMath.FiniteSuperspace.assembleColumns_even
  intro a
  exact MatrixComponentParity.total_even _ (unitMatrixEntry_mem D Sc cutoff i M m a) t

/-- The actual finite cap matrix is even, for every old module. -/
theorem capMatrixComponent_even (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff) :
    capMatrixComponent D Sc cutoff i M m t ∈ parity (R := k) _ _ 0 := by
  apply OddMath.FiniteSuperspace.assembleRows_even
  intro a
  exact MatrixComponentParity.total_even _ (capMatrixEntry_mem D Sc cutoff i M m a) t

local instance finiteMatrixComponentsPi :
    PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) := supermodulePiSupercategory

/-- The canonical first source parity isomorphism with fixed literal module endpoints. -/
def unitMatrixFirstSourceIso (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    unitMatrixFamily D Sc cutoff i M m none ≅
      (BalancedInduction.induction (append D Sc cutoff i)).obj
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) :=
  (SKM.homParityShiftDatum (k := k) (D.parity i)).iso
    ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M))

/-- Removing the canonical first source shift gives the actual mate as a module map. -/
theorem unitMatrixEntry_none_unshifted (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    (unitMatrixFirstSourceIso D Sc cutoff i M m).inv ≫
      unitMatrixEntry D Sc cutoff i M m none = matrixMateComponent D Sc cutoff i M := by
  rw [unitMatrixFirstSourceIso, unitMatrixEntry_none, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The literal first unit entry agrees with the mate after the canonical source coordinate. -/
theorem unitMatrixEntry_none_inverse_apply (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff)
    (z : ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t) :
    (unitMatrixEntry D Sc cutoff i M m none).total t
      ((moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i M m) t).symm z) =
      (matrixMateComponent D Sc cutoff i M).total t z := by
  have h := MatrixComponentParity.inverse_precompose_total
    (unitMatrixFirstSourceIso D Sc cutoff i M m)
    (unitMatrixEntry D Sc cutoff i M m none) t z
  rw [unitMatrixEntry_none_unshifted] at h
  exact h

/-- The first literal unit entry uses the canonical source parity coordinate. -/
theorem unitMatrixEntry_none_apply (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff)
    (b : (unitMatrixFamily D Sc cutoff i M m none).obj t) :
    (unitMatrixEntry D Sc cutoff i M m none).total t b =
      (matrixMateComponent D Sc cutoff i M).total t
        (moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i M m) t b) := by
  have h := unitMatrixEntry_none_inverse_apply D Sc cutoff i M m t
    (moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i M m) t b)
  simpa only [LinearEquiv.symm_apply_apply] using h

/-- The canonical first target parity isomorphism with fixed literal module endpoints. -/
def capMatrixFirstTargetIso (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    capMatrixFamily D Sc cutoff i M m none ≅
      (BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj M) :=
  (SKM.homParityShiftDatum (k := k) (D.parity i)).iso
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj
      ((BalancedInduction.induction (append D Sc cutoff i)).obj M))

/-- The literal first cap entry before evaluating components. -/
theorem capMatrixEntry_none (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    capMatrixEntry D Sc cutoff i M m none =
      matrixMateComponent D Sc cutoff i M ≫ (capMatrixFirstTargetIso D Sc cutoff i M m).inv := rfl

/-- Removing the canonical first target parity gives the actual mate as a module map. -/
theorem capMatrixEntry_none_unshifted (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    capMatrixEntry D Sc cutoff i M m none ≫ (capMatrixFirstTargetIso D Sc cutoff i M m).hom =
      matrixMateComponent D Sc cutoff i M := by
  rw [capMatrixEntry_none, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The literal first cap entry uses the canonical target parity coordinate. -/
theorem capMatrixEntry_none_apply (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ)
    (t : OldCategory D Sc cutoff)
    (z : ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t) :
    moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t
      ((capMatrixEntry D Sc cutoff i M m none).total t z) =
      (matrixMateComponent D Sc cutoff i M).total t z := by
  have h := MatrixComponentParity.postcompose_total (capMatrixFirstTargetIso D Sc cutoff i M m)
    (capMatrixEntry D Sc cutoff i M m none) t z
  rw [capMatrixEntry_none_unshifted] at h
  exact h

/-- The earlier plain source coordinates use the same named first parity isomorphism. -/
theorem unitFamilyPlainCoordinates_fst (i : I) (v t : List I) (m : ℕ)
    (x : unitMatrixSourceSpace D Sc cutoff i
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩) :
    (unitFamilyPlainCoordinates D Sc cutoff i v t m x).1 =
      moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m) ⟨t⟩ (x none) := rfl

/-- The earlier plain source coordinates use the canonical coefficient parity isomorphisms. -/
theorem unitFamilyPlainCoordinates_snd (i : I) (v t : List I) (m : ℕ)
    (x : unitMatrixSourceSpace D Sc cutoff i
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩) (r : Fin m) :
    (unitFamilyPlainCoordinates D Sc cutoff i v t m x).2 r =
      moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) ⟨t⟩ (x (some r)) := rfl

private def matrixUpperCoordinates (i : I) (v t : List I) :
    (((BalancedInduction.restriction (append D Sc cutoff i)).obj
      ((BalancedInduction.induction (append D Sc cutoff i)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  (OldInductionRepresentable.upperHomEquiv D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).toLinearMap

/-- Literal Old quotient coordinates for the actual assembled unit matrix. -/
def unitMatrixComponentRow (i : I) (v t : List I) (m : ℕ) :
    unitMatrixSourceSpace D Sc cutoff i
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩ →ₗ[k]
        Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  (matrixUpperCoordinates D Sc cutoff i v t).comp
    (SVec.toLinearMap (unitMatrixComponent D Sc cutoff i
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩))

/-- Actual unit entries give exactly the mate and ordinary unit columns in canonical coordinates. -/
theorem unitMatrixComponentRow_apply (i : I) (v t : List I) (m : ℕ)
    (x : unitMatrixSourceSpace D Sc cutoff i
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩) :
    unitMatrixComponentRow D Sc cutoff i v t m x =
      matrixMateRow D Sc cutoff i v t (unitFamilyPlainCoordinates D Sc cutoff i v t m x).1 +
        ∑ r : Fin m, inductionUnitDotColumn D Sc cutoff i v t r.val
          ((unitFamilyPlainCoordinates D Sc cutoff i v t m x).2 r) := by
  classical
  change matrixUpperCoordinates D Sc cutoff i v t
    (∑ a : Option (Fin m), (unitMatrixEntry D Sc cutoff i
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).total ⟨t⟩ (x a)) = _
  rw [map_sum, Fintype.sum_option]
  have hn : matrixUpperCoordinates D Sc cutoff i v t
      ((unitMatrixEntry D Sc cutoff i
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m none).total ⟨t⟩ (x none)) =
      matrixMateRow D Sc cutoff i v t (unitFamilyPlainCoordinates D Sc cutoff i v t m x).1 := by
    rw [unitMatrixEntry_none_apply, unitFamilyPlainCoordinates_fst]
    rfl
  rw [hn]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [unitFamilyPlainCoordinates_snd]
  exact unitMatrixEntry_some_upper D Sc cutoff i v t m r (x (some r))

/-- First canonical target coordinate with the literal named parity isomorphism. -/
theorem capFamilyComponentCoordinates_fst (i : I) (v t : List I) (m : ℕ)
    (x : capMatrixTargetSpace D Sc cutoff i
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩) :
    (capFamilyComponentCoordinates D Sc cutoff i v t m x).1 =
      matrixUpperCoordinates D Sc cutoff i v t
        (moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m) ⟨t⟩ (x none)) := rfl

/-- Remaining canonical target coordinates are the literal coefficient parity isomorphisms. -/
theorem capFamilyComponentCoordinates_snd (i : I) (v t : List I) (m : ℕ)
    (x : capMatrixTargetSpace D Sc cutoff i
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩) (r : Fin m) :
    (capFamilyComponentCoordinates D Sc cutoff i v t m x).2 r =
      moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) ⟨t⟩ (x (some r)) := rfl

/-- Actual assembled cap entries give the actual mate and ordinary module cap rows. -/
theorem capMatrixComponent_coordinates (i : I) (v t : List I) (m : ℕ)
    (z : (actualUnshiftedSourceModule D Sc cutoff i v).obj (⟨t⟩ : OldCategory D Sc cutoff)) :
    capFamilyComponentCoordinates D Sc cutoff i v t m
      (capMatrixComponent D Sc cutoff i
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩ z) =
      (matrixMateRow D Sc cutoff i v t z,
        fun r : Fin m => (moduleCapRow D Sc cutoff i
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) r.val).total ⟨t⟩ z) := by
  apply Prod.ext
  · rw [capFamilyComponentCoordinates_fst]
    change matrixUpperCoordinates D Sc cutoff i v t
      (moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m) ⟨t⟩
          ((capMatrixEntry D Sc cutoff i
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m none).total ⟨t⟩ z)) = _
    rw [capMatrixEntry_none_apply]
    rfl
  · funext r
    rw [capFamilyComponentCoordinates_snd]
    exact capMatrixEntry_some_total D Sc cutoff i
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) ⟨t⟩ m r z

/-- The actual odd unit matrix component is an isomorphism on representables. -/
def unitMatrixComponentIso (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m) :
    (unitMatrixSourceSpace D Sc cutoff j.1 (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩) ≅
    (((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.induction (append D Sc cutoff j.1)).obj (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj ⟨t⟩) :=
  SVec.isoOfLinearEquiv ((unitFamilyComponentEquiv D Sc cutoff p j v t m hm).trans
      (OldInductionRepresentable.upperHomEquiv D Sc cutoff j.1
        (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).symm)

/-- The isomorphism's forward map is the literal assembled matrix, without coordinate replacements. -/
theorem unitMatrixComponentIso_hom (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m) :
    (unitMatrixComponentIso D Sc cutoff p j v t m hm).hom = unitMatrixComponent D Sc cutoff j.1 (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩ := by
  ext x
  apply (OldInductionRepresentable.upperHomEquiv D Sc cutoff j.1
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).injective
  change (OldInductionRepresentable.upperHomEquiv D Sc cutoff j.1
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff))
      ((OldInductionRepresentable.upperHomEquiv D Sc cutoff j.1
        (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).symm
          (unitFamilyComponentEquiv D Sc cutoff p j v t m hm x)) = unitMatrixComponentRow D Sc cutoff j.1 v t m x
  rw [LinearEquiv.apply_symm_apply, unitFamilyComponentEquiv_actual, unitMatrixComponentRow_apply]

/-- The inverse of the actual unit component preserves its specified parity grading. -/
theorem unitMatrixComponentIso_inv_even (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m) :
    (unitMatrixComponentIso D Sc cutoff p j v t m hm).inv ∈ parity (R := k) _ _ 0 := by
  apply Supercategory.inv_mem (unitMatrixComponentIso D Sc cutoff p j v t m hm)
  rw [unitMatrixComponentIso_hom]
  exact unitMatrixComponent_even D Sc cutoff j.1 (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩

/-- The actual odd cap matrix component is an isomorphism on representables. -/
def capMatrixComponentIso (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (((BalancedInduction.induction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj ⟨t⟩) ≅
    (capMatrixTargetSpace D Sc cutoff j.1 (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩) :=
  SVec.isoOfLinearEquiv (capFamilyComponentEquiv D Sc cutoff p j v t m hm)

/-- The isomorphism's forward map is the literal assembled matrix, without coordinate replacements. -/
theorem capMatrixComponentIso_hom (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (capMatrixComponentIso D Sc cutoff p j v t m hm).hom = capMatrixComponent D Sc cutoff j.1 (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩ := by
  ext z
  apply (capFamilyComponentCoordinates D Sc cutoff j.1 v t m).injective
  change capFamilyComponentCoordinates D Sc cutoff j.1 v t m
    (capFamilyComponentEquiv D Sc cutoff p j v t m hm z) = _
  rw [capFamilyComponentEquiv_actual, capMatrixComponent_coordinates]

/-- The inverse of the actual cap component preserves its specified parity grading. -/
theorem capMatrixComponentIso_inv_even (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (capMatrixComponentIso D Sc cutoff p j v t m hm).inv ∈ parity (R := k) _ _ 0 := by
  apply Supercategory.inv_mem (capMatrixComponentIso D Sc cutoff p j v t m hm)
  rw [capMatrixComponentIso_hom]
  exact capMatrixComponent_even D Sc cutoff j.1 (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩

/-- The actual even unit matrix component is an isomorphism on representables. -/
def evenUnitMatrixComponentIso (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff i.1 v = outputSDegree D i.1 v + m) :
    (unitMatrixSourceSpace D Sc cutoff i.1 (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩) ≅
    (((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
      ((BalancedInduction.induction (append D Sc cutoff i.1)).obj (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj ⟨t⟩) :=
  SVec.isoOfLinearEquiv ((evenUnitFamilyComponentEquiv D Sc cutoff p i v t m hm).trans
      (OldInductionRepresentable.upperHomEquiv D Sc cutoff i.1
        (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).symm)

/-- The isomorphism's forward map is the literal assembled matrix, without coordinate replacements. -/
theorem evenUnitMatrixComponentIso_hom (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff i.1 v = outputSDegree D i.1 v + m) :
    (evenUnitMatrixComponentIso D Sc cutoff p i v t m hm).hom = unitMatrixComponent D Sc cutoff i.1 (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩ := by
  ext x
  apply (OldInductionRepresentable.upperHomEquiv D Sc cutoff i.1
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).injective
  change (OldInductionRepresentable.upperHomEquiv D Sc cutoff i.1
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff))
      ((OldInductionRepresentable.upperHomEquiv D Sc cutoff i.1
        (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).symm
          (evenUnitFamilyComponentEquiv D Sc cutoff p i v t m hm x)) = unitMatrixComponentRow D Sc cutoff i.1 v t m x
  rw [LinearEquiv.apply_symm_apply, evenUnitFamilyComponentEquiv_actual, unitMatrixComponentRow_apply]

/-- The inverse of the actual unit component preserves its specified parity grading. -/
theorem evenUnitMatrixComponentIso_inv_even (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff i.1 v = outputSDegree D i.1 v + m) :
    (evenUnitMatrixComponentIso D Sc cutoff p i v t m hm).inv ∈ parity (R := k) _ _ 0 := by
  apply Supercategory.inv_mem (evenUnitMatrixComponentIso D Sc cutoff p i v t m hm)
  rw [evenUnitMatrixComponentIso_hom]
  exact unitMatrixComponent_even D Sc cutoff i.1 (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩

/-- The actual even cap matrix component is an isomorphism on representables. -/
def evenCapMatrixComponentIso (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m) :
    (((BalancedInduction.induction (append D Sc cutoff i.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj ⟨t⟩) ≅
    (capMatrixTargetSpace D Sc cutoff i.1 (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩) :=
  SVec.isoOfLinearEquiv (evenCapFamilyComponentEquiv D Sc cutoff p i v t m hm)

/-- The isomorphism's forward map is the literal assembled matrix, without coordinate replacements. -/
theorem evenCapMatrixComponentIso_hom (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m) :
    (evenCapMatrixComponentIso D Sc cutoff p i v t m hm).hom = capMatrixComponent D Sc cutoff i.1 (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩ := by
  ext z
  apply (capFamilyComponentCoordinates D Sc cutoff i.1 v t m).injective
  change capFamilyComponentCoordinates D Sc cutoff i.1 v t m
    (evenCapFamilyComponentEquiv D Sc cutoff p i v t m hm z) = _
  rw [evenCapFamilyComponentEquiv_actual, capMatrixComponent_coordinates]

/-- The inverse of the actual cap component preserves its specified parity grading. -/
theorem evenCapMatrixComponentIso_inv_even (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m) :
    (evenCapMatrixComponentIso D Sc cutoff p i v t m hm).inv ∈ parity (R := k) _ _ 0 := by
  apply Supercategory.inv_mem (evenCapMatrixComponentIso D Sc cutoff p i v t m hm)
  rw [evenCapMatrixComponentIso_hom]
  exact capMatrixComponent_even D Sc cutoff i.1 (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m ⟨t⟩

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

