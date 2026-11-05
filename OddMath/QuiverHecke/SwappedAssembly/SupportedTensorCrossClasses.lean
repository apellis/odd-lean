import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCrossEntries

/-! # Literal supported crossing entries in quotient coordinates

SwappedVacuumCoordinates §§2–7: pull the chosen supported crossing matrix
through its derived selected-Hom chart and its proved endpoint transport,
retaining arbitrary coefficient components and both reservoir contexts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorCrossClassHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR
local notation "Z" => ObjectProperty.FullSubcategory.obj (tensorVacuum D Sc m cutoff L ΛP ΛR)

section Same
variable (ν : X) (u v : List (Letter I)) (i : I)
  {cL c : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
  (hw : StepValid (true,i) false (nextSector (true,i) false (0,c)))
  (pL : SPath (SKM.lay D ν u (SKM.Shape.cross i i) v).left (0,cL) (0,c))
  (hl : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.cross i i) v).left, a.l.1 = true)
  (pR : SPath (SKM.lay D ν u (SKM.Shape.cross i i) v).right
    (0,c - Finsupp.single i 1 - Finsupp.single i 1) (0,0))
  (hr : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.cross i i) v).right, a.l.1 = true)
local notation "pg" => SPath.cons (Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up i]))
  false (0,c) hv (SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false _ hw (SPath.nil _))
local notation "p" => SPath.append (SPath.append pL pg) pR
local notation "h₁" => ProbeReservoir.reservoirVacuumEdge (P) i (c - Finsupp.single i 1) hw
local notation "h₂" => ProbeReservoir.reservoirVacuumEdge (P) i c hv

/-- The literal equal-colour crossing pulled back through its selected-Hom chart. -/
def tensorLayerSameCrossRaw (a : (P).CrossCoeff) :
    End (ReservoirLayerCells.crossRawHom D Sc m cutoff L ΛP ΛR pL hl pR hr i i h₁ h₂) :=
  (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.preimage
    ((tensorLayerSameCrossIso D Sc m cutoff L ΛP ΛR hP hR ν u v i hv hw pL hl pR hr).inv ≫
      (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (SKM.Shape.cross i i) v) p p Z ≫
        (tensorLayerSameCrossIso D Sc m cutoff L ΛP ΛR hP hR ν u v i hv hw pL hl pR hr).hom)

/-- Pulling back the literal equal-colour entry gives the original contextual crossing. -/
theorem tensorLayerSameCrossRaw_eq (a : (P).CrossCoeff) :
    tensorLayerSameCrossRaw D Sc m cutoff L ΛP ΛR hP hR ν u v i hv hw pL hl pR hr a =
      ReservoirLayerCells.crossRaw D Sc m cutoff L ΛP ΛR pL hl pR hr i i h₁ h₂ h₁ h₂ := by
  let e := tensorLayerSameCrossIso D Sc m cutoff L ΛP ΛR hP hR ν u v i hv hw pL hl pR hr
  let E := (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor
  have he := tensorLayerSameCross_square D Sc m cutoff L ΛP ΛR hP hR ν u v i hv hw pL hl pR hr a
  change (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (SKM.Shape.cross i i) v) p p Z ≫ e.hom =
    e.hom ≫ E.map (ReservoirLayerCells.crossRaw D Sc m cutoff L ΛP ΛR pL hl pR hr i i h₁ h₂ h₁ h₂) at he
  have hc : e.inv ≫ (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (SKM.Shape.cross i i) v) p p Z ≫ e.hom =
      E.map (ReservoirLayerCells.crossRaw D Sc m cutoff L ΛP ΛR pL hl pR hr i i h₁ h₂ h₁ h₂) := by
    rw [he]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change E.preimage _ = _
  rw [hc,Functor.preimage_map]

local notation "νR" => (List.reverse (List.map (fun a => Prod.snd (SKM.Col.l a)) (Layer.right (SKM.lay D ν u (SKM.Shape.cross i i) v))))
local notation "ηL" => (List.reverse (List.map (fun a => Prod.snd (SKM.Col.l a)) (Layer.left (SKM.lay D ν u (SKM.Shape.cross i i) v))))
omit [Fintype I] in
private theorem sameSourceEdge
    (pR : SPath (SKM.lay D ν u (SKM.Shape.cross i i) v).right
      (0,c - Finsupp.single i 1 - Finsupp.single i 1) (0,0))
    (hr : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.cross i i) v).right, a.l.1 = true)
    (hE : ReservoirWord.weight D ΛR (c - Finsupp.single i 1 - Finsupp.single i 1) + D.α i =
      ReservoirWord.weight D ΛR (c - Finsupp.single i 1)) : PowerWordWeight.wordWeight D ΛR νR + D.α i =
    ReservoirWord.weight D ΛR (c - Finsupp.single i 1) :=
  (congrArg (fun x => x + D.α i) (TensorReservoirWords.path_weight D ΛR pR hr)).symm.trans hE
local notation "hC" => sameSourceEdge D ΛR ν u v i pR hr h₁
end Same
private def crossRightPath {r : List (Col I X)} {cR cR' : I →₀ ℕ}
    (h : cR = cR') (pR : SPath r (0,cR') (0,0)) : SPath r (0,cR) (0,0) := by
  subst cR'
  exact pR

section Distinct
variable (ν : X) (u v : List (Letter I)) (i j : I)
  {cL c : I →₀ ℕ}
  (hv₁ : StepValid (true,i) false (0,c))
  (hv₂ : StepValid (true,j) false (nextSector (true,i) false (0,c)))
  (hw₁ : StepValid (true,j) false (0,c))
  (hw₂ : StepValid (true,i) false (nextSector (true,j) false (0,c)))
  (hEnd : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
    nextSector (true,i) false (nextSector (true,j) false (0,c)))
  (pL : SPath (SKM.lay D ν u (SKM.Shape.cross i j) v).left (0,cL) (0,c))
  (hl : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.cross i j) v).left, a.l.1 = true)
  (pR : SPath (SKM.lay D ν u (SKM.Shape.cross i j) v).right
    (0,c - Finsupp.single j 1 - Finsupp.single i 1) (0,0))
  (hr : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.cross i j) v).right, a.l.1 = true)
local notation "ps" => SPath.two (c₁ := Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up j]))
  (c₂ := Col.mk (up j) (SKM.wt D ν v)) false false hv₁ hv₂ hEnd
local notation "pt" => SPath.two (c₁ := Col.mk (up j) (SKM.wt D (SKM.wt D ν v) [up i]))
  (c₂ := Col.mk (up i) (SKM.wt D ν v)) false false hw₁ hw₂ rfl
local notation "p" => SPath.append (SPath.append pL ps) pR
local notation "q" => SPath.append (SPath.append pL pt) pR
local notation "r" => crossRightPath (congrArg Prod.snd hEnd) pR
local notation "h₁" => ProbeReservoir.reservoirVacuumEdge (P) j (c - Finsupp.single i 1) hv₂
local notation "h₂" => ProbeReservoir.reservoirVacuumEdge (P) i c hv₁
local notation "h₄" => ProbeReservoir.reservoirVacuumEdge (P) j c hw₁

private theorem tensorCrossEdge
    (hw₂ : StepValid (true,i) false (nextSector (true,j) false (0,c)))
    (hEnd : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
      nextSector (true,i) false (nextSector (true,j) false (0,c))) :
    (P).muM (0,c - Finsupp.single i 1 - Finsupp.single j 1) + D.α i =
      (P).muM (0,c - Finsupp.single j 1) := by
  change (P).muM (nextSector (true,j) false (nextSector (true,i) false (0,c))) + D.α i = _
  rw [hEnd]
  exact (P).reservoirVacuumEdge i (c - Finsupp.single j 1) hw₂
local notation "h₃" => tensorCrossEdge D Sc m cutoff L ΛP ΛR hP hR i j hw₂ hEnd

/-- The literal distinct-colour crossing pulled back through the selected tensor Hom.
The original source endpoint cast is retained in both charts. -/
def tensorLayerCrossRaw (a : (P).CrossCoeff) :
    ReservoirLayerCells.crossRawHom D Sc m cutoff L ΛP ΛR pL hl r hr i j h₁ h₂ ⟶
      ReservoirLayerCells.crossRawHom D Sc m cutoff L ΛP ΛR pL hl r hr j i h₃ h₄ :=
  (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.preimage
    ((tensorLayerCrossSourceIso D Sc m cutoff L ΛP ΛR hP hR ν u v i j hv₁ hv₂ hEnd pL hl pR hr).inv ≫
      (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (SKM.Shape.cross i j) v) p q Z ≫
        (tensorLayerCrossTargetIso D Sc m cutoff L ΛP ΛR hP hR ν u v i j hw₁ hw₂ hEnd pL hl pR hr).hom)

/-- Pulling back the literal distinct-colour entry gives the original contextual crossing. -/
theorem tensorLayerCrossRaw_eq (a : (P).CrossCoeff) (hij : i ≠ j) :
    tensorLayerCrossRaw D Sc m cutoff L ΛP ΛR hP hR ν u v i j
      hv₁ hv₂ hw₁ hw₂ hEnd pL hl pR hr a =
      ReservoirLayerCells.crossRaw D Sc m cutoff L ΛP ΛR pL hl r hr i j h₁ h₂ h₃ h₄ := by
  let eS := tensorLayerCrossSourceIso D Sc m cutoff L ΛP ΛR hP hR ν u v i j hv₁ hv₂ hEnd pL hl pR hr
  let eT := tensorLayerCrossTargetIso D Sc m cutoff L ΛP ΛR hP hR ν u v i j hw₁ hw₂ hEnd pL hl pR hr
  let E := (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor
  have he := tensorLayerCross_square D Sc m cutoff L ΛP ΛR hP hR ν u v i j
    hv₁ hv₂ hw₁ hw₂ hEnd pL hl pR hr a hij
  change (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (SKM.Shape.cross i j) v) p q Z ≫ eT.hom =
    eS.hom ≫ E.map (ReservoirLayerCells.crossRaw D Sc m cutoff L ΛP ΛR pL hl r hr i j h₁ h₂ h₃ h₄) at he
  have hc : eS.inv ≫ (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (SKM.Shape.cross i j) v) p q Z ≫ eT.hom =
      E.map (ReservoirLayerCells.crossRaw D Sc m cutoff L ΛP ΛR pL hl r hr i j h₁ h₂ h₃ h₄) := by
    rw [he]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change E.preimage _ = _
  rw [hc,Functor.preimage_map]

local notation "νR" => (List.reverse (List.map (fun a => Prod.snd (SKM.Col.l a)) (Layer.right (SKM.lay D ν u (SKM.Shape.cross i j) v))))
local notation "ηL" => (List.reverse (List.map (fun a => Prod.snd (SKM.Col.l a)) (Layer.left (SKM.lay D ν u (SKM.Shape.cross i j) v))))
omit [Fintype I] in
private theorem crossSourceEdge
    (qR : SPath (SKM.lay D ν u (SKM.Shape.cross i j) v).right
      (0,c - Finsupp.single i 1 - Finsupp.single j 1) (0,0))
    (hr : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.cross i j) v).right, a.l.1 = true)
    (hE : ReservoirWord.weight D ΛR (c - Finsupp.single i 1 - Finsupp.single j 1) + D.α j =
      ReservoirWord.weight D ΛR (c - Finsupp.single i 1)) : PowerWordWeight.wordWeight D ΛR νR + D.α j =
    ReservoirWord.weight D ΛR (c - Finsupp.single i 1) :=
  (congrArg (fun x => x + D.α j) (TensorReservoirWords.path_weight D ΛR qR hr)).symm.trans hE
omit [Fintype I] in
private theorem crossTargetEdge
    (qR : SPath (SKM.lay D ν u (SKM.Shape.cross i j) v).right
      (0,c - Finsupp.single i 1 - Finsupp.single j 1) (0,0))
    (hr : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.cross i j) v).right, a.l.1 = true)
    (hE : ReservoirWord.weight D ΛR (c - Finsupp.single i 1 - Finsupp.single j 1) + D.α i =
      ReservoirWord.weight D ΛR (c - Finsupp.single j 1)) : PowerWordWeight.wordWeight D ΛR νR + D.α i =
    ReservoirWord.weight D ΛR (c - Finsupp.single j 1) :=
  (congrArg (fun x => x + D.α i) (TensorReservoirWords.path_weight D ΛR qR hr)).symm.trans hE

class under the literal supported cell, retaining its source endpoint cast. -/

local notation "hS" => crossSourceEdge D ΛR ν u v i j r hr h₁
local notation "hT" => crossTargetEdge D ΛR ν u v i j r hr h₃
end Distinct
end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
