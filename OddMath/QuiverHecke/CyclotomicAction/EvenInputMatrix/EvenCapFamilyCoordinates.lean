import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Pi
import OddMath.QuiverHecke.CyclotomicAction.EvenInputMatrix.EvenCounitInverse
import OddMath.QuiverHecke.CyclotomicAction.WeightedAppend.MateFirstRow

/-!
# Even input matrix

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Even shifted cap-family component inverse
DeformedMatrixComparison section 4 has the same canonical cap target
family for the even-moving case, with ordinary unscaled dotted counits.
Only representable component inversion is asserted here.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Even negative-height inverse on the literal finite shifted cap target. -/
def evenCapFamilyComponentEquiv (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m) :
    (unshiftedSourceModule D Sc cutoff i.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff) ≃ₗ[k]
    ((a : Option (Fin m)) →
      (capMatrixFamily D Sc cutoff i.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) :=
  (evenCounitMatrixEquiv D Sc cutoff p i v t m hm).trans
    (capFamilyComponentCoordinates D Sc cutoff i.1 v t m).symm

/-- The canonical coordinates give the actual ordinary even counit matrix. -/
theorem evenCapFamilyComponentEquiv_coordinates (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff i.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    capFamilyComponentCoordinates D Sc cutoff i.1 v t m
      (evenCapFamilyComponentEquiv D Sc cutoff p i v t m hm z) =
      evenCounitMatrixEquiv D Sc cutoff p i v t m hm z := by
  exact (capFamilyComponentCoordinates D Sc cutoff i.1 v t m).apply_symm_apply _

/-- The first canonical coordinate remains the specified signed crossing. -/
theorem evenCapFamilyComponentEquiv_fst (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff i.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    (capFamilyComponentCoordinates D Sc cutoff i.1 v t m
      (evenCapFamilyComponentEquiv D Sc cutoff p i v t m hm z)).1 =
      -toCyclotomic D Sc cutoff i.1 v t (evenSourceEquiv D Sc cutoff i v t z) := by
  rw [evenCapFamilyComponentEquiv_coordinates, evenCounitMatrixEquiv_fst]

/-- Each remaining canonical coordinate is the ordinary dotted counit. -/
theorem evenCapFamilyComponentEquiv_cap (p : ZMod 2) (i : {i : I // D.parity i = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D i.1 v = endpointQPDegree D cutoff i.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff i.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) (r : Fin m) :
    (capFamilyComponentCoordinates D Sc cutoff i.1 v t m
      (evenCapFamilyComponentEquiv D Sc cutoff p i v t m hm z)).2 r =
      unshiftedCounitComponent D Sc cutoff i.1 v t
        ((inductionDot D Sc cutoff i.1 (restrictedRepresentable D Sc cutoff i.1 v)
          (⟨t⟩ : OldCategory D Sc cutoff))^[r.val] z) := by
  rw [evenCapFamilyComponentEquiv_coordinates]
  exact evenCounitMatrixEquiv_cap D Sc cutoff p i v t m hm z r

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # The actual even mate is the canonical first crossing row

The coefficient(0) source comparison has no parity shift or tensor twist.
The fixed signed mate evaluates to minus toCyclotomic after this actual J0.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem evenModuleMate_firstRow_tensor (i : {i : I // D.parity i = 0})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [i.1]) t)
    (b : Old D Sc cutoff v (s ++ [i.1])) :
    OldInductionRepresentable.upperHomEquiv D Sc cutoff i.1
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
      (((oldModuleMate D Sc cutoff i.1).app 0
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
        (⟨t⟩ : OldCategory D Sc cutoff)
        (BalancedInduction.tensor (append D Sc cutoff i.1)
          ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor
          (⟨s⟩ : OldCategory D Sc cutoff) g b)) =
    -toCyclotomic D Sc cutoff i.1 v t
      (evenSourceEquiv D Sc cutoff i v t
        (BalancedInduction.tensor (append D Sc cutoff i.1)
          ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor
          (⟨s⟩ : OldCategory D Sc cutoff) g b)) := by
  have hp : D.parity i.1 * D.parity i.1 = 0 := by rw [i.property]; decide
  have hc := congrArg (fun q => (oldModuleMate D Sc cutoff i.1).app q
    (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) hp.symm
  have hJ := evenSourceEquiv_tensor D Sc cutoff i v s t g b
  dsimp only [restrictedRepresentable] at hJ
  rw [hJ, hc, oldModuleMate_upper_tensor D Sc cutoff i.1 v s t g b,
    toCyclotomic_tensor D Sc cutoff i.1 v s t g b,
    pairing_eq_append_comp D Sc cutoff i.1 v s t g b, hp, twist_zero]

theorem evenModuleMate_firstRow (i : {i : I // D.parity i = 0}) (v t : List I)
    (z : ((BalancedInduction.induction (append D Sc cutoff i.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj (⟨t⟩ : OldCategory D Sc cutoff)) :
    OldInductionRepresentable.upperHomEquiv D Sc cutoff i.1
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
      (((oldModuleMate D Sc cutoff i.1).app 0
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
        (⟨t⟩ : OldCategory D Sc cutoff) z) =
    -toCyclotomic D Sc cutoff i.1 v t (evenSourceEquiv D Sc cutoff i v t z) := by
  exact coend_total_ext (append D Sc cutoff i.1)
    ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
    ((BalancedInduction.restriction (append D Sc cutoff i.1)).obj
      ((BalancedInduction.induction (append D Sc cutoff i.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))))
    ((oldModuleMate D Sc cutoff i.1).app 0
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
    (⟨t⟩ : OldCategory D Sc cutoff)
    (OldInductionRepresentable.upperHomEquiv D Sc cutoff i.1
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).toLinearMap
    (toCyclotomic D Sc cutoff i.1 v t)
    (evenSourceEquiv D Sc cutoff i v t).toLinearMap
    (fun s g b => by
      cases s with
      | mk s => exact evenModuleMate_firstRow_tensor D Sc cutoff i v s t g b) z

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # The actual mate in shifted finite matrix component inverses
DeformedMatrixComparison section 4 identifies the inverted first
coordinate with the fixed ordered categorical mate. The unit columns
remain the ordinary unscaled columns, with canonical source coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
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
theorem unitFamilyComponentEquiv_eq (p : ZMod 2) (j : {j : I // D.parity j = 1})
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
theorem capFamilyComponentEquiv_eq (p : ZMod 2) (j : {j : I // D.parity j = 1})
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
theorem evenUnitFamilyComponentEquiv_eq (p : ZMod 2) (i : {i : I // D.parity i = 0})
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
theorem evenCapFamilyComponentEquiv_eq (p : ZMod 2) (i : {i : I // D.parity i = 0})
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

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Ordinary-right covariance of the actual normalized mate kernel

The right coefficient action is ordinary precomposition b ↦ a ≫ b for
every arrow a, including inhomogeneous arrows. The actual mate formula
keeps b untwisted. Its co-Yoneda component therefore defines a natural map
between the concrete IndRes and upper Hom coefficient presheaves.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private def kernelNatTrans
    {C : Type u} [Category.{u} C] (K L : C ⥤ ModuleCat k)
    (f : ∀ v, K.obj v →ₗ[k] L.obj v)
    (hf : ∀ {v w} (a : v ⟶ w), (f w).comp (K.map a).hom = (L.map a).hom.comp (f v)) : K ⟶ L where
  app v := ModuleCat.ofHom (f v)
  naturality _ _ a := by
    apply ModuleCat.hom_ext
    exact hf a

/-- The representable coefficient functors agree literally in the old category. -/
def oldSourceKernelEquiv (i : I) (v t : OldCategory D Sc cutoff) :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t ≃ₗ[k]
      ((BalancedInduction.induction (append D Sc cutoff i)).obj
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj
          (oldRepresentable D Sc cutoff v))).obj t :=
  LinearEquiv.refl k _

@[simp] theorem oldSourceKernelEquiv_tensor (i : I) (v s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t)
    (b : v ⟶ (append D Sc cutoff i).obj s) :
    oldSourceKernelEquiv D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b) =
      BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj
          (oldRepresentable D Sc cutoff v)).toFunctor s g b := rfl

/-- Source comparison with the precise domain expected by the stored mate row. -/
def oldSourceKernelLinear (i : I) (v t : List I) :
    IndResKernel.Component (k := k) (append D Sc cutoff i)
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff) →ₗ[k]
      (unshiftedSourceModule D Sc cutoff i v).obj
        (⟨t⟩ : OldCategory D Sc cutoff) :=
  (oldSourceKernelEquiv D Sc cutoff i ⟨v⟩ ⟨t⟩).toLinearMap

theorem oldSourceKernelLinear_tensor (i : I) (v s t : List I)
    (g : (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff) ⟶
      (⟨t⟩ : OldCategory D Sc cutoff))
    (b : (⟨v⟩ : OldCategory D Sc cutoff) ⟶ (append D Sc cutoff i).obj ⟨s⟩) :
    oldSourceKernelLinear D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) ⟨v⟩) ⟨s⟩ g b) =
      BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj
          (oldRepresentable D Sc cutoff ⟨v⟩)).toFunctor ⟨s⟩ g b :=
  oldSourceKernelEquiv_tensor D Sc cutoff i ⟨v⟩ ⟨s⟩ ⟨t⟩ g b

private theorem matrixMateRow_total (i : I) (v t : List I)
    (z : (unshiftedSourceModule D Sc cutoff i v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    matrixMateRow D Sc cutoff i v t z =
      OldInductionRepresentable.upperHomEquiv D Sc cutoff i
        (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
        ((matrixMateComponent D Sc cutoff i
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
            (⟨t⟩ : OldCategory D Sc cutoff) z) := rfl

/-- The chosen actual mate, evaluated in canonical upper-Hom coordinates. -/
def mateKernelComponent (i : I) (v t : OldCategory D Sc cutoff) :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k]
      ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) := by
  cases v with
  | mk v =>
    cases t with
    | mk t =>
      exact (matrixMateRow D Sc cutoff i v t).comp
        (oldSourceKernelLinear D Sc cutoff i v t)

/-- The stored row and its source linear map share the same module endpoint. -/
theorem mateKernelComponent_row (i : I) (v t : List I)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i)
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)) :
    mateKernelComponent D Sc cutoff i ⟨v⟩ ⟨t⟩ z =
      matrixMateRow D Sc cutoff i v t (oldSourceKernelLinear D Sc cutoff i v t z) := rfl

@[simp] theorem mateKernelComponent_tensor (i : I)
    (v s t : OldCategory D Sc cutoff) (g : (append D Sc cutoff i).obj s ⟶ t)
    (b : v ⟶ (append D Sc cutoff i).obj s) :
    mateKernelComponent D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b) =
    -((append D Sc cutoff i).map b ≫ equalCrossComponent D Sc cutoff i s ≫
      twist k (D.parity i) ((append D Sc cutoff i).map g)) := by
  cases v with
  | mk v =>
    cases s with
    | mk s =>
      cases t with
      | mk t =>
        rw [mateKernelComponent_row]
        rw [oldSourceKernelLinear_tensor, matrixMateRow_total]
        have hp : D.parity i * D.parity i = D.parity i := by
          rcases parity_eq_zero_or_one (D.parity i) with h | h <;> simp [h]
        have ht := oldModuleMate_upper_tensor D Sc cutoff i v s t g b
        rw [hp] at ht
        exact ht

theorem mateKernelComponent_precompose (i : I)
    {v w : OldCategory D Sc cutoff} (a : v ⟶ w) (t : OldCategory D Sc cutoff) :
    (mateKernelComponent D Sc cutoff i v t).comp
      (IndResKernel.precompose (k := k) (append D Sc cutoff i) a t) =
    (Linear.leftComp k ((append D Sc cutoff i).obj t) ((append D Sc cutoff i).map a)).comp
      (mateKernelComponent D Sc cutoff i w t) := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, IndResKernel.precompose_tensor,
    mateKernelComponent_tensor]
  change -((append D Sc cutoff i).map (a ≫ b) ≫ equalCrossComponent D Sc cutoff i s ≫
      twist k (D.parity i) ((append D Sc cutoff i).map g)) =
    (append D Sc cutoff i).map a ≫
      (-((append D Sc cutoff i).map b ≫ equalCrossComponent D Sc cutoff i s ≫
        twist k (D.parity i) ((append D Sc cutoff i).map g)))
  rw [Functor.map_comp, Preadditive.comp_neg, Category.assoc]

/-- The same actual mate coefficient with literal kernel-object endpoints. -/
def mateKernelLinear (i : I) (v : (OldCategory D Sc cutoff)ᵒᵖ)
    (t : OldCategory D Sc cutoff) :
    (IndResKernel.kernel (k := k) (append D Sc cutoff i) t).obj v →ₗ[k]
      (BalancedKernelTensor.inductionKernel (k := k) (append D Sc cutoff i)
        ((append D Sc cutoff i).obj t)).obj v :=
  mateKernelComponent D Sc cutoff i v.unop t

/-- The typed kernel-object coefficient is the fixed actual mate coefficient. -/
theorem mateKernelLinear_eq_component (i : I) (v : (OldCategory D Sc cutoff)ᵒᵖ)
    (t : OldCategory D Sc cutoff) :
    mateKernelLinear D Sc cutoff i v t =
      mateKernelComponent D Sc cutoff i v.unop t := rfl

/-- The actual normalized first entry is ordinary-right natural, not merely even-arrow natural. -/
def mateKernel (i : I) (t : OldCategory D Sc cutoff) :
    IndResKernel.kernel (k := k) (append D Sc cutoff i) t ⟶
      BalancedKernelTensor.inductionKernel (k := k) (append D Sc cutoff i)
        ((append D Sc cutoff i).obj t) :=
  kernelNatTrans _ _ (fun v => mateKernelLinear D Sc cutoff i v t)
    (fun a => mateKernelComponent_precompose D Sc cutoff i a.unop t)

@[simp] theorem mateKernel_apply (i : I) (v t : OldCategory D Sc cutoff)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    (mateKernel D Sc cutoff i t).app (op v) z =
      mateKernelComponent D Sc cutoff i v t z := by
  change mateKernelLinear D Sc cutoff i (op v) t z = _
  rw [mateKernelLinear_eq_component]
  simp only [Opposite.unop_op]
  exact LinearMap.congr_fun
    (rfl : mateKernelComponent D Sc cutoff i v t =
      mateKernelComponent D Sc cutoff i v t) z

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Ordinary-right covariance of the actual counit-dot rows

The source action is ordinary coefficient precomposition for all arrows.
The actual induction dot changes only the first tensor factor, and the
ordinary counit composes the untwisted coefficient with that factor.
Consequently every actual ordinary counit/dot-power row is right natural.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private def transportEnd {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (e : V ≃ₗ[k] W) (T : Module.End k W) : Module.End k V :=
  e.symm.toLinearMap.comp (T.comp e.toLinearMap)

private theorem transportEnd_apply {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (e : V ≃ₗ[k] W) (T : Module.End k W) (x : V) :
    transportEnd e T x = e.symm (T (e x)) := rfl

private theorem transportEnd_pow_apply {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (e : V ≃ₗ[k] W) (T : Module.End k W) (n : ℕ) (x : V) :
    e ((transportEnd e T ^ n) x) = (T ^ n) (e x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, transportEnd_apply,
      e.apply_symm_apply, pow_succ, Module.End.mul_apply]

private theorem pow_intertwining {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (q : V →ₗ[k] W) (S : Module.End k V) (T : Module.End k W)
    (h : T.comp q = q.comp S) (n : ℕ) : (T ^ n).comp q = q.comp (S ^ n) := by
  have hs : Function.Semiconj q S T := fun x => (LinearMap.congr_fun h x).symm
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, Module.End.pow_apply]
  exact (hs.iterate_right n x).symm

@[simp] theorem oldSourceKernelEquiv_symm_tensor (i : I) (v s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : v ⟶ (append D Sc cutoff i).obj s) :
    (oldSourceKernelEquiv D Sc cutoff i v t).symm
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj
          (oldRepresentable D Sc cutoff v)).toFunctor s g b) =
    BalancedInduction.tensor (append D Sc cutoff i)
      ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b := rfl

def dotKernelComponent (i : I) (v t : OldCategory D Sc cutoff) :
    Module.End k (IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :=
  transportEnd (oldSourceKernelEquiv D Sc cutoff i v t)
    (inductionDot D Sc cutoff i
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        (oldRepresentable D Sc cutoff v)) t)

@[simp] theorem dotKernelComponent_tensor (i : I) (v s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : v ⟶ (append D Sc cutoff i).obj s) :
    dotKernelComponent D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b) =
    BalancedInduction.tensor (append D Sc cutoff i)
      ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s
      (oldAppendDotComponent D Sc cutoff i s ≫ twist k (D.parity i) g) b := by
  rw [dotKernelComponent, transportEnd_apply, oldSourceKernelEquiv_tensor]
  have h := inductionDot_tensor D Sc cutoff i
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj
      (oldRepresentable D Sc cutoff v)) s t g b
  exact (congrArg (oldSourceKernelEquiv D Sc cutoff i v t).symm h).trans
    (oldSourceKernelEquiv_symm_tensor D Sc cutoff i v s t
      (oldAppendDotComponent D Sc cutoff i s ≫ twist k (D.parity i) g) b)

theorem dotKernelComponent_precompose (i : I)
    {v w : OldCategory D Sc cutoff} (a : v ⟶ w) (t : OldCategory D Sc cutoff) :
    (dotKernelComponent D Sc cutoff i v t).comp
      (IndResKernel.precompose (k := k) (append D Sc cutoff i) a t) =
    (IndResKernel.precompose (k := k) (append D Sc cutoff i) a t).comp
      (dotKernelComponent D Sc cutoff i w t) := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, IndResKernel.precompose_tensor, dotKernelComponent_tensor]

def counitKernelComponent (i : I) (v t : OldCategory D Sc cutoff) :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k] (v ⟶ t) :=
  (unshiftedCounitComponent D Sc cutoff i v.word t.word).comp
    (oldSourceKernelEquiv D Sc cutoff i v t).toLinearMap

theorem counitKernelComponent_apply (i : I) (v t : OldCategory D Sc cutoff)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    counitKernelComponent D Sc cutoff i v t z =
      unshiftedCounitComponent D Sc cutoff i v.word t.word
        (oldSourceKernelEquiv D Sc cutoff i v t z) := rfl

@[simp] theorem counitKernelComponent_tensor (i : I) (v s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : v ⟶ (append D Sc cutoff i).obj s) :
    counitKernelComponent D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b) = b ≫ g := by
  rw [counitKernelComponent_apply, oldSourceKernelEquiv_tensor]
  cases v with
  | mk v =>
    cases s with
    | mk s =>
      cases t with
      | mk t => exact unshiftedCounitComponent_tensor D Sc cutoff i v s t g b

theorem counitKernelComponent_precompose (i : I)
    {v w : OldCategory D Sc cutoff} (a : v ⟶ w) (t : OldCategory D Sc cutoff) :
    (counitKernelComponent D Sc cutoff i v t).comp
      (IndResKernel.precompose (k := k) (append D Sc cutoff i) a t) =
    (Linear.leftComp k t a).comp (counitKernelComponent D Sc cutoff i w t) := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, IndResKernel.precompose_tensor,
    counitKernelComponent_tensor]
  exact Category.assoc a b g

/-- Underlying coefficient component of the actual ordinary counit/dot-power row. -/
def capKernelComponent (i : I) (n : ℕ) (v t : OldCategory D Sc cutoff) :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k] (v ⟶ t) :=
  (counitKernelComponent D Sc cutoff i v t).comp
    (dotKernelComponent D Sc cutoff i v t ^ n)

theorem capKernelComponent_precompose (i : I) (n : ℕ)
    {v w : OldCategory D Sc cutoff} (a : v ⟶ w) (t : OldCategory D Sc cutoff) :
    (capKernelComponent D Sc cutoff i n v t).comp
      (IndResKernel.precompose (k := k) (append D Sc cutoff i) a t) =
    (Linear.leftComp k t a).comp (capKernelComponent D Sc cutoff i n w t) := by
  have hd := pow_intertwining
    (IndResKernel.precompose (k := k) (append D Sc cutoff i) a t)
    (dotKernelComponent D Sc cutoff i w t) (dotKernelComponent D Sc cutoff i v t)
    (dotKernelComponent_precompose D Sc cutoff i a t) n
  rw [capKernelComponent, capKernelComponent, LinearMap.comp_assoc,
    hd, ← LinearMap.comp_assoc, counitKernelComponent_precompose, LinearMap.comp_assoc]

private theorem moduleCapRow_total_apply (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (n : ℕ)
    (z : ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t) :
    (moduleCapRow D Sc cutoff i M n).total t z =
      ((BalancedInduction.adjunction (append D Sc cutoff i)).counit.app M).total t
        ((inductionDot D Sc cutoff i
          ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) t ^ n) z) := by
  have h := LinearMap.congr_fun (moduleCapRow_total D Sc cutoff i M t n) z
  change (moduleCapRow D Sc cutoff i M n).total t z =
    ((BalancedInduction.adjunction (append D Sc cutoff i)).counit.app M).total t
      ((inductionDot D Sc cutoff i
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) t ^ n) z) at h
  exact h

/-- The kernel row is the fixed actual moduleCapRow, not an assumed substitute. -/
theorem capKernelComponent_moduleCapRow (i : I) (n : ℕ) (v t : OldCategory D Sc cutoff)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    capKernelComponent D Sc cutoff i n v t z =
      (moduleCapRow D Sc cutoff i (oldRepresentable D Sc cutoff v) n).total t
        (oldSourceKernelEquiv D Sc cutoff i v t z) := by
  rw [capKernelComponent, LinearMap.comp_apply, counitKernelComponent_apply]
  have he := transportEnd_pow_apply (oldSourceKernelEquiv D Sc cutoff i v t)
    (inductionDot D Sc cutoff i
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        (oldRepresentable D Sc cutoff v)) t) n z
  have hc := congrArg (unshiftedCounitComponent D Sc cutoff i v.word t.word) he
  exact hc.trans (moduleCapRow_total_apply D Sc cutoff i
    (oldRepresentable D Sc cutoff v) t n (oldSourceKernelEquiv D Sc cutoff i v t z)).symm

/-- Every fixed ordinary counit/dot-power row is an ordinary-right kernel map. -/
def capKernel (i : I) (n : ℕ) (t : OldCategory D Sc cutoff) :
    IndResKernel.kernel (k := k) (append D Sc cutoff i) t ⟶
      BalancedKernelTensor.inductionKernel (k := k) (𝟭 (OldCategory D Sc cutoff)) t where
  app v := ModuleCat.ofHom (capKernelComponent D Sc cutoff i n v.unop t)
  naturality _ _ a := by
    apply ModuleCat.hom_ext
    exact capKernelComponent_precompose D Sc cutoff i n a.unop t

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end
