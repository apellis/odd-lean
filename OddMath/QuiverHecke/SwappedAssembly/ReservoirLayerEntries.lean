import OddMath.QuiverHecke.SwappedAssembly.LayerEntries
import OddMath.QuiverHecke.SwappedAssembly.WhiskerReduction
import OddMath.QuiverHecke.SwappedAssembly.VacuumPaths

/-! # Literal layer entries at reservoir paths

SwappedActionAssembly §6 and SwappedVacuumCoordinates §§2–6: at probe
content zero an upward layer's actual matrix sum has one reservoir term.
Both statements refer to the existing layerMap and layerEntry, retaining
their generator maps and all path-append equality transports.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc) {Gs Ys : ∀ s, P.H s}

/-- The literal upward layer matrix at probe content zero has a single
input path. No condition on its coefficient entry is imposed. -/
theorem layerMap_reservoir (gens : P.Generators) (L : Layer (SKM.sig D)) (hL : L.Valid)
    (hw : ∀ a ∈ L.dom.word, a.l.1 = true) (x : P.Mod Gs Ys L.dom)
    (sl : Sector I) (sr : {t : Sector I // P.wt t = L.cod.endR}) (ht : sr.1.1 = 0)
    (p : SPath L.dom.word sl sr.1) (q : SPath L.cod.word sl sr.1) :
    P.layerMap gens L x sl sr q =
      x sl ⟨sr.1, sr.2.trans hL.endR_eq⟩ p ≫ P.compLayer gens L p q (Ys sr.1) := by
  let := Fintype.ofFinite (SPath L.dom.word sl sr.1)
  rw [P.layerMap_apply gens L hL x sl sr q]
  exact SPath.sum_of_upward_probe_zero hw ht _ p

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
