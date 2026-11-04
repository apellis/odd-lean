import OddMath.QuiverHecke.SwappedAssembly.SupportedPresentation

/-! # Single layers on the literal supported matrix modules

SwappedVacuumCoordinates §5: the existing supported local interpretation
keeps exactly the native chosen-factor layer map under `matrixEquiv`.
This is the single-layer attachment needed for the fixed-source tensor
row observation; it adds no relation, inverse or generator-comparison
hypothesis.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance supportedMatrixLayerHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ) (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR

/-- A supported single-layer operator is the unchanged literal factor layer matrix. -/
theorem interpretation_layer (gens : (P).Generators) (L : Layer (SKM.sig D))
    (x : matrixModule D Sc m cutoff bound ΛP ΛR Gs Ys L.dom) :
    matrixEquiv D Sc m cutoff bound ΛP ΛR hP hR Gs Ys L.cod
      ((interpretation D Sc m cutoff bound ΛP ΛR hP hR Gs Ys gens).res L.cod
        ((interpretation D Sc m cutoff bound ΛP ΛR hP hR Gs Ys gens).op L
          ((interpretation D Sc m cutoff bound ΛP ΛR hP hR Gs Ys gens).ext L.dom x))) =
      (P).layerMap gens L (matrixEquiv D Sc m cutoff bound ΛP ΛR hP hR Gs Ys L.dom x) := by
  change (matrixEquiv D Sc m cutoff bound ΛP ΛR hP hR Gs Ys L.cod)
    ((matrixEquiv D Sc m cutoff bound ΛP ΛR hP hR Gs Ys L.cod).symm
      (((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj) gens).toLocal.res L.cod
        ((((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj) gens).toLocal.op L)
          ((((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj) gens).toLocal.ext L.dom)
            (matrixEquiv D Sc m cutoff bound ΛP ΛR hP hR Gs Ys L.dom x))))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact LayerRep.toLocal_layer _ L _

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
