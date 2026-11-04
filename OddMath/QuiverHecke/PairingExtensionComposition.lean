import OddMath.QuiverHecke.PairingExtensionPBW
import StringDiagrams.Super.BoxProductMonoidal

/-! # Koszul composition under the pairing extension

The transport in `SwappedVacuumCoordinates.md` §7 must carry the exact
two-sided observation ideal, so it must respect coefficient-extended
composition, including the Koszul sign. This is the box product of the
identity on the polynomial/exterior model and the even affine functor.
-/
noncomputable section
namespace OddMath.QuiverHecke.PairingExtension
open CategoryTheory StringDiagrams StringDiagrams.Supercategory
open scoped TensorProduct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
local notation "Dₑ" => ReservoirWeights.pairingExtension D
local notation "Scₑ" => ReservoirWeights.pairingExtensionScalars D Sc

instance presentationFunctor_super : Supercategory.IsSuperfunctor k (presentationFunctor D Sc) where
  map_mem hf :=
    LayerMap.lift_mem_homDeg (inclusion D).whiskerData (fun _ => trivial)
      (fun _ => inclusion_relation D Sc)
      (fun _ _ hx => (inclusion D).toPresented_interchange (pres Dₑ Scₑ)
        (fun _ => 1) (fun _ => rfl) hx) () (fun _ => rfl) hf

/-- The raw affine presentation map, with its proved parity preservation. -/
def affineSuperfunctor : Superfunctor k (H D Sc) (H Dₑ Scₑ) where
  toFunctor := presentationFunctor D Sc

private def coefficientSuperfunctor : Superfunctor k (CoefficientH D Sc) (CoefficientH Dₑ Scₑ) :=
  BoxProd.map (Superfunctor.id k (SuperalgebraCat (SKM.SYM.polynomialExteriorParity D k)))
    (affineSuperfunctor D Sc)

private theorem coefficientHomEquiv_map {s t : List I}
    (f : coefficientObj D Sc s ⟶ coefficientObj D Sc t) :
    coefficientHomEquiv D Sc s t f = (coefficientSuperfunctor D Sc).map f := by
  induction f using TensorProduct.inductionOn with
  | zero => simp only [map_zero, Superfunctor.map, Functor.map_zero]
  | tmul a f =>
    change a ⊗ₜ[k] affineEquiv D Sc s t f = a ⊗ₜ[k] (presentationFunctor D Sc).map f
    rw [affineEquiv_apply]
  | add f g hf hg => simp only [map_add, Superfunctor.map, Functor.map_add, hf, hg]

/-- Composition compatibility retains the box-product Koszul convention. -/
theorem coefficientHomEquiv_comp {r s t : List I}
    (f : coefficientObj D Sc r ⟶ coefficientObj D Sc s)
    (g : coefficientObj D Sc s ⟶ coefficientObj D Sc t) :
    coefficientHomEquiv D Sc r t (f ≫ g) =
      coefficientHomEquiv D Sc r s f ≫ coefficientHomEquiv D Sc s t g := by
  rw [coefficientHomEquiv_map, coefficientHomEquiv_map, coefficientHomEquiv_map]
  exact (coefficientSuperfunctor D Sc).toFunctor.map_comp f g

theorem coefficientHomEquiv_id (s : List I) :
    coefficientHomEquiv D Sc s s (𝟙 (coefficientObj D Sc s)) = 𝟙 (coefficientObj (k := k) Dₑ Scₑ s) := by
  rw [coefficientHomEquiv_map]
  exact (coefficientSuperfunctor D Sc).toFunctor.map_id _

end OddMath.QuiverHecke.PairingExtension
