import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedMatrixFamilies
import OddMath.QuiverHecke.CyclotomicAction.ELVCounitInputInverse

/-! # Shifted cap-family component coordinates
The cap-row profile of DeformedMatrixComparison section 4, after removing
the common source parity shift, has targets Pi^p(Res Ind M) and Pi^(r p)M.
These are canonical component coordinates and the representable component
inverse. The actual mate evaluation and arbitrary-module transfer remain separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local instance capFamilyPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- Canonical target parity isomorphisms on the actual cap family. -/
def capFamilyPlainCoordinates (i : I) (v t : List I) (m : ℕ) :
    ((a : Option (Fin m)) →
      (capMatrixFamily D Sc cutoff i
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
    ((((BalancedInduction.restriction (append D Sc cutoff i)).obj
      ((BalancedInduction.induction (append D Sc cutoff i)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) × (Fin m → Old D Sc cutoff v t)) :=
  (LinearEquiv.piOptionEquivProd k).trans
    ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))))) ⟨t⟩).prodCongr
      (LinearEquiv.piCongrRight fun r : Fin m =>
        moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) ⟨t⟩))

/-- Canonical upper-Hom and parity coordinates for the finite cap target. -/
def capFamilyComponentCoordinates (i : I) (v t : List I) (m : ℕ) :
    ((a : Option (Fin m)) →
      (capMatrixFamily D Sc cutoff i
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
    (Old D Sc cutoff (v ++ [i]) (t ++ [i]) × (Fin m → Old D Sc cutoff v t)) :=
  (capFamilyPlainCoordinates D Sc cutoff i v t m).trans
    ((OldInductionRepresentable.upperHomEquiv D Sc cutoff i
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).prodCongr
        (LinearEquiv.refl k _))

/-- Odd negative-height inverse with the literal shifted finite cap target. -/
def capFamilyComponentEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff) ≃ₗ[k]
    ((a : Option (Fin m)) →
      (capMatrixFamily D Sc cutoff j.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) :=
  (counitInputMatrixEquiv D Sc cutoff p j v t m hm).trans
    (capFamilyComponentCoordinates D Sc cutoff j.1 v t m).symm

/-- In canonical coordinates the map is the already checked ordinary counit matrix. -/
theorem capFamilyComponentEquiv_coordinates (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    capFamilyComponentCoordinates D Sc cutoff j.1 v t m
      (capFamilyComponentEquiv D Sc cutoff p j v t m hm z) =
      counitInputMatrixEquiv D Sc cutoff p j v t m hm z := by
  exact (capFamilyComponentCoordinates D Sc cutoff j.1 v t m).apply_symm_apply _

/-- The first canonical target coordinate is the specified signed balanced crossing. -/
theorem capFamilyComponentEquiv_fst (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    (capFamilyComponentCoordinates D Sc cutoff j.1 v t m
      (capFamilyComponentEquiv D Sc cutoff p j v t m hm z)).1 =
      -toCyclotomic D Sc cutoff j.1 v t (shiftedSourceCanonicalEquiv D Sc cutoff j v t z) := by
  rw [capFamilyComponentEquiv_coordinates, counitInputMatrixEquiv_fst]

/-- Every remaining canonical target coordinate is the ordinary counit after the dot power. -/
theorem capFamilyComponentEquiv_cap (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) (r : Fin m) :
    (capFamilyComponentCoordinates D Sc cutoff j.1 v t m
      (capFamilyComponentEquiv D Sc cutoff p j v t m hm z)).2 r =
      ((BalancedInduction.adjunctionCounit (append D Sc cutoff j.1)).app
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
          (⟨t⟩ : OldCategory D Sc cutoff)
          ((inductionDot D Sc cutoff j.1
            ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
              (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
            (⟨t⟩ : OldCategory D Sc cutoff))^[r.val] z) := by
  rw [capFamilyComponentEquiv_coordinates]
  exact counitInputMatrixEquiv_cap D Sc cutoff p j v t m hm z r

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

