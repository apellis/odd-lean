import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorDotEntries

/-! # Literal supported tensor dot entries in quotient classes

SwappedVacuumCoordinates §§2–7: pull the literal chosen dot entry back
through its derived selected-Hom chart and the proved endpoint transport.
This identifies the entry used by every quotient-class observation without
a supplied generator-comparison hypothesis.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorDotClassHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR

section Dot
variable (ν : X) (u v : List (Letter I)) (i : I)
  {cL c : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
  (pL : SPath (SKM.lay D ν u (SKM.Shape.dot i) v).left (0,cL) (0,c))
  (hl : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.dot i) v).left, a.l.1 = true)
  (pR : SPath (SKM.lay D ν u (SKM.Shape.dot i) v).right (0,c - Finsupp.single i 1) (0,0))
  (hr : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.dot i) v).right, a.l.1 = true)
local notation "pg" => SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false (0,c) hv (SPath.nil _)
local notation "p" => SPath.append (SPath.append pL pg) pR
local notation "Z" => ObjectProperty.FullSubcategory.obj (tensorVacuum D Sc m cutoff L ΛP ΛR)
local notation "h" => ProbeReservoir.reservoirVacuumEdge (P) i c hv

/-- The literal chosen dot cell pulled back through its selected tensor-Hom chart. -/
def tensorLayerDotRaw (a : (P).CrossCoeff) :
    End (ReservoirLayerCells.dotRawHom D Sc m cutoff L ΛP ΛR pL hl pR hr i h) :=
  (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.preimage
    ((tensorLayerDotIso D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr).inv ≫
      (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (SKM.Shape.dot i) v) p p Z ≫
        (tensorLayerDotIso D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr).hom)

/-- The pulled-back literal matrix entry is the original contextual factor dot. -/
theorem tensorLayerDotRaw_eq (a : (P).CrossCoeff) :
    tensorLayerDotRaw D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr a =
      ReservoirLayerCells.dotRaw D Sc m cutoff L ΛP ΛR pL hl pR hr i h := by
  let e := tensorLayerDotIso D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr
  let E := (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor
  have he := tensorLayerDot_square D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr a
  change (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (SKM.Shape.dot i) v) p p Z ≫ e.hom =
    e.hom ≫ E.map (ReservoirLayerCells.dotRaw D Sc m cutoff L ΛP ΛR pL hl pR hr i h) at he
  have hc : e.inv ≫ (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (SKM.Shape.dot i) v) p p Z ≫ e.hom =
      E.map (ReservoirLayerCells.dotRaw D Sc m cutoff L ΛP ΛR pL hl pR hr i h) := by
    rw [he]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change E.preimage _ = _
  rw [hc,Functor.preimage_map]

local notation "νR" => (List.reverse (List.map (fun a => Prod.snd (SKM.Col.l a)) (Layer.right (SKM.lay D ν u (SKM.Shape.dot i) v))))
local notation "ηL" => (List.reverse (List.map (fun a => Prod.snd (SKM.Col.l a)) (Layer.left (SKM.lay D ν u (SKM.Shape.dot i) v))))

end Dot
end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
