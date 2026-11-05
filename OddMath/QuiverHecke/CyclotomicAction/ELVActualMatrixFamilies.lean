import OddMath.QuiverHecke.CyclotomicAction.ELVEvenUnitFamilyCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenCapFamilyCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVMatrixEntryTotals
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenMateFirstRow

/-! # The actual mate in shifted finite matrix component inverses
DeformedMatrixComparison section 4 identifies the inverted first
coordinate with the fixed ordered categorical mate. The unit columns
remain the ordinary unscaled columns, with canonical source coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The typed actual mate component has exactly the inverted first-row normalization. -/
theorem matrixMateComponent_firstRow (j : {j : I // D.parity j = 1}) (v t : List I)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    OldInductionRepresentable.upperHomEquiv D Sc cutoff j.1
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
      ((matrixMateComponent D Sc cutoff j.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
          (⟨t⟩ : OldCategory D Sc cutoff) z) =
      -toCyclotomic D Sc cutoff j.1 v t (shiftedSourceCanonicalEquiv D Sc cutoff j v t z) := by
  have hc := congrArg (fun q => (oldModuleMate D Sc cutoff j.1).app q
    (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) j.property
  change OldInductionRepresentable.upperHomEquiv D Sc cutoff j.1
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
    (((oldModuleMate D Sc cutoff j.1).app (D.parity j.1)
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
        (⟨t⟩ : OldCategory D Sc cutoff) z) = _
  rw [hc]
  exact oldModuleMate_firstRow D Sc cutoff j v t z

/-- The actual mate as a linear row with literal Old quotient coordinates. -/
def matrixMateRow (i : I) (v t : List I) :
    (unshiftedSourceModule D Sc cutoff i v).obj
      (⟨t⟩ : OldCategory D Sc cutoff) →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  (OldInductionRepresentable.upperHomEquiv D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).toLinearMap.comp
      (SVec.toLinearMap ((matrixMateComponent D Sc cutoff i
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
          (⟨t⟩ : OldCategory D Sc cutoff)))

theorem matrixMateRow_apply (j : {j : I // D.parity j = 1}) (v t : List I)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    matrixMateRow D Sc cutoff j.1 v t z =
      -toCyclotomic D Sc cutoff j.1 v t (shiftedSourceCanonicalEquiv D Sc cutoff j v t z) := by
  exact matrixMateComponent_firstRow D Sc cutoff j v t z

/-- The positive component inverse has the actual ordered mate and unscaled ordinary unit columns. -/
theorem unitFamilyComponentEquiv_actual (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m)
    (x : (a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff j.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) :
    unitFamilyComponentEquiv D Sc cutoff p j v t m hm x =
      matrixMateRow D Sc cutoff j.1 v t
        (unitFamilyPlainCoordinates D Sc cutoff j.1 v t m x).1 +
      ∑ r : Fin m, inductionUnitDotColumn D Sc cutoff j.1 v t r.val
        ((unitFamilyPlainCoordinates D Sc cutoff j.1 v t m x).2 r) := by
  rw [matrixMateRow_apply, unitFamilyComponentEquiv_apply]

/-- The negative component inverse has the actual ordered mate and ordinary module cap rows. -/
theorem capFamilyComponentEquiv_actual (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    capFamilyComponentCoordinates D Sc cutoff j.1 v t m
      (capFamilyComponentEquiv D Sc cutoff p j v t m hm z) =
      (matrixMateRow D Sc cutoff j.1 v t z,
        fun r : Fin m => (moduleCapRow D Sc cutoff j.1
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) r.val).total
            (⟨t⟩ : OldCategory D Sc cutoff) z) := by
  apply Prod.ext
  · rw [capFamilyComponentEquiv_fst, matrixMateRow_apply]
  · funext r
    rw [capFamilyComponentEquiv_cap]
    have h := LinearMap.congr_fun (moduleCapRow_total D Sc cutoff j.1
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) ⟨t⟩ r.val) z
    change (moduleCapRow D Sc cutoff j.1
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) r.val).total
        (⟨t⟩ : OldCategory D Sc cutoff) z =
      ((BalancedInduction.adjunctionCounit (append D Sc cutoff j.1)).app
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
          (⟨t⟩ : OldCategory D Sc cutoff)
          (((inductionDot D Sc cutoff j.1
            ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
              (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
            (⟨t⟩ : OldCategory D Sc cutoff)) ^ r.val) z) at h
    rw [Module.End.pow_apply] at h
    exact h.symm

/-- The even typed mate row has the canonical coefficient-zero source normalization. -/
theorem matrixMateRow_even_apply (i : {i : I // D.parity i = 0}) (v t : List I)
    (z : (unshiftedSourceModule D Sc cutoff i.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    matrixMateRow D Sc cutoff i.1 v t z =
      -toCyclotomic D Sc cutoff i.1 v t (evenSourceEquiv D Sc cutoff i v t z) := by
  have hc := congrArg (fun q => (oldModuleMate D Sc cutoff i.1).app q
    (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) i.property
  change OldInductionRepresentable.upperHomEquiv D Sc cutoff i.1
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
    (((oldModuleMate D Sc cutoff i.1).app (D.parity i.1)
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
        (⟨t⟩ : OldCategory D Sc cutoff) z) = _
  rw [hc]
  exact evenModuleMate_firstRow D Sc cutoff i v t z

/-- Even positive components use the fixed actual mate and unscaled ordinary unit columns. -/
theorem evenUnitFamilyComponentEquiv_actual (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff i.1 v = outputSDegree D i.1 v + m)
    (x : (a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff i.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) :
    evenUnitFamilyComponentEquiv D Sc cutoff p i v t m hm x =
      matrixMateRow D Sc cutoff i.1 v t
        (unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).1 +
      ∑ r : Fin m, inductionUnitDotColumn D Sc cutoff i.1 v t r.val
        ((unitFamilyPlainCoordinates D Sc cutoff i.1 v t m x).2 r) := by
  rw [matrixMateRow_even_apply, evenUnitFamilyComponentEquiv_apply]

/-- Even negative components use the actual mate and ordinary unscaled module cap rows. -/
theorem evenCapFamilyComponentEquiv_actual (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff i.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    capFamilyComponentCoordinates D Sc cutoff i.1 v t m
      (evenCapFamilyComponentEquiv D Sc cutoff p i v t m hm z) =
      (matrixMateRow D Sc cutoff i.1 v t z,
        fun r : Fin m => (moduleCapRow D Sc cutoff i.1
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) r.val).total
            (⟨t⟩ : OldCategory D Sc cutoff) z) := by
  apply Prod.ext
  · rw [evenCapFamilyComponentEquiv_fst, matrixMateRow_even_apply]
  · funext r
    rw [evenCapFamilyComponentEquiv_cap]
    have h := LinearMap.congr_fun (moduleCapRow_total D Sc cutoff i.1
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) ⟨t⟩ r.val) z
    change (moduleCapRow D Sc cutoff i.1
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) r.val).total
        (⟨t⟩ : OldCategory D Sc cutoff) z =
      ((BalancedInduction.adjunctionCounit (append D Sc cutoff i.1)).app
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
          (⟨t⟩ : OldCategory D Sc cutoff)
          (((inductionDot D Sc cutoff i.1
            ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
              (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
            (⟨t⟩ : OldCategory D Sc cutoff)) ^ r.val) z) at h
    rw [Module.End.pow_apply] at h
    exact h.symm

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
