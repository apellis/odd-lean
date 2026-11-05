import OddMath.QuiverHecke.CyclotomicAction.ELVCapFamilyCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenCounitInverse

/-! # Even shifted cap-family component inverse
DeformedMatrixComparison section 4 has the same canonical cap target
family for the even-moving case, with ordinary unscaled dotted counits.
Only representable component inversion is asserted here.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
