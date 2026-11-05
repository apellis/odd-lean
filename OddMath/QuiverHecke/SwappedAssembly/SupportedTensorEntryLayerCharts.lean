import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorEntryLayers
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorDotClasses
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCrossClasses

/-! # Global and local charts on the literal original tensor layer

SwappedVacuumCoordinates §§5–7: canonical whole-Hom chart changes
conjugate the native matrix layer to its prescribed local dot and
crossing operators. Compatibility after regular-probe evaluation is
recorded separately from these whole-Hom squares.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorEntryLayerChartsHomPi {k : Type u} [CommRing k]
    (A C : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s : List I)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "cS" => tensorSourceContent D ΛP ΛR s
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR
local notation "E" => tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cS)
local notation "Q" => interpretation D Sc m cutoff N ΛP ΛR hP hR
  (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L)
attribute [local irreducible] Finsupp.single Finsupp.zipWith Finsupp.onFinset contentWeight
  tensorHomEquivalence

private def proofProposition {Φ : Prop} (_ : Φ) : Prop := Φ

section Dot
variable (ν : X) (u v : List (Letter I)) (i : I)
  {cL c : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
  (pL : SPath (SKM.lay D ν u (.dot i) v).left (0,cL) (0,c))
  (hl : ∀ a ∈ (SKM.lay D ν u (.dot i) v).left, a.l.1 = true)
  (pR : SPath (SKM.lay D ν u (.dot i) v).right (0,c - Finsupp.single i 1) (0,0))
  (hr : ∀ a ∈ (SKM.lay D ν u (.dot i) v).right, a.l.1 = true)
local notation "pg" => SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false (0,c) hv (SPath.nil _)
local notation "p" => SPath.append (SPath.append pL pg) pR
local notation "e" => tensorLayerDotIso D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr
local notation "h" => ProbeReservoir.reservoirVacuumEdge (P) i c hv
local notation "F" => ReservoirLayerCells.dotRawHom D Sc m cutoff L ΛP ΛR pL hl pR hr i h
local notation "Z" => ObjectProperty.FullSubcategory.obj (tensorVacuum D Sc m cutoff L ΛP ΛR)
local notation "E0" => tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)

attribute [local irreducible] TensorReservoirWords.pathHom ReservoirLayerCells.dotRawHom
  tensorLayerDotRaw

/-- The frozen local dot operator is the canonical whole-Hom arrow
for the full chosen action's literal dot entry. -/
theorem tensorLayerDotRaw_arrow (a : (P).CrossCoeff) (leftward : (P).LeftwardData) :
    tensorLayerDotRaw D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr a =
      TensorEntryPullback.arrow (E0) (A := F) (B := F)
        (X := ((P).pathFunctor p).obj Z) (Y := ((P).pathFunctor p).obj Z) e e
        ((P).compLayer ((P).swappedGens a leftward) (SKM.lay D ν u (.dot i) v) p p Z) := by
  unfold tensorLayerDotRaw TensorEntryPullback.arrow
  rfl

end Dot

section Same
variable (ν : X) (u v : List (Letter I)) (i : I)
  {cL c : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
  (hw : StepValid (true,i) false (nextSector (true,i) false (0,c)))
  (pL : SPath (SKM.lay D ν u (.cross i i) v).left (0,cL) (0,c))
  (hl : ∀ a ∈ (SKM.lay D ν u (.cross i i) v).left, a.l.1 = true)
  (pR : SPath (SKM.lay D ν u (.cross i i) v).right
    (0,c - Finsupp.single i 1 - Finsupp.single i 1) (0,0))
  (hr : ∀ a ∈ (SKM.lay D ν u (.cross i i) v).right, a.l.1 = true)
local notation "pg" => SPath.cons (Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up i]))
  false (0,c) hv (SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false _ hw (SPath.nil _))
local notation "p" => SPath.append (SPath.append pL pg) pR
local notation "h₁" => ProbeReservoir.reservoirVacuumEdge (P) i (c - Finsupp.single i 1) hw
local notation "h₂" => ProbeReservoir.reservoirVacuumEdge (P) i c hv
local notation "F" => ReservoirLayerCells.crossRawHom D Sc m cutoff L ΛP ΛR pL hl pR hr i i h₁ h₂
local notation "Z" => ObjectProperty.FullSubcategory.obj (tensorVacuum D Sc m cutoff L ΛP ΛR)
local notation "E0" => tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)
local notation "e" => tensorLayerSameCrossIso D Sc m cutoff L ΛP ΛR hP hR ν u v i hv hw pL hl pR hr

/-- The frozen local equal-colour crossing is the original-Hom arrow
of the complete action's literal crossing entry. -/
theorem tensorLayerSameCrossRaw_arrow (a : (P).CrossCoeff) (leftward : (P).LeftwardData) :
    tensorLayerSameCrossRaw D Sc m cutoff L ΛP ΛR hP hR ν u v i hv hw pL hl pR hr a =
      TensorEntryPullback.arrow (E0) (A := F) (B := F)
        (X := ((P).pathFunctor p).obj Z) (Y := ((P).pathFunctor p).obj Z) e e
        ((P).compLayer ((P).swappedGens a leftward) (SKM.lay D ν u (.cross i i) v) p p Z) := by
  unfold tensorLayerSameCrossRaw TensorEntryPullback.arrow
  rfl

end Same

section Cross
variable (ν : X) (u v : List (Letter I)) (i j : I)
  {cL c : I →₀ ℕ}
  (hv₁ : StepValid (true,i) false (0,c))
  (hv₂ : StepValid (true,j) false (nextSector (true,i) false (0,c)))
  (hw₁ : StepValid (true,j) false (0,c))
  (hw₂ : StepValid (true,i) false (nextSector (true,j) false (0,c)))
  (hEnd : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
    nextSector (true,i) false (nextSector (true,j) false (0,c)))
  (pL : SPath (SKM.lay D ν u (.cross i j) v).left (0,cL) (0,c))
  (hl : ∀ a ∈ (SKM.lay D ν u (.cross i j) v).left, a.l.1 = true)
  (pR : SPath (SKM.lay D ν u (.cross i j) v).right
    (0,c - Finsupp.single j 1 - Finsupp.single i 1) (0,0))
  (hr : ∀ a ∈ (SKM.lay D ν u (.cross i j) v).right, a.l.1 = true)
private def rightPath {r : List (Col I X)} {cR cR' : I →₀ ℕ}
    (h : cR = cR') (pR : SPath r (0,cR') (0,0)) : SPath r (0,cR) (0,0) := by
  subst cR'
  exact pR
private theorem targetEdge
    (hw₂ : StepValid (true,i) false (nextSector (true,j) false (0,c)))
    (hEnd : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
      nextSector (true,i) false (nextSector (true,j) false (0,c))) :
    (P).muM (0,c - Finsupp.single i 1 - Finsupp.single j 1) + D.α i =
      (P).muM (0,c - Finsupp.single j 1) := by
  change (P).muM (nextSector (true,j) false (nextSector (true,i) false (0,c))) + D.α i = _
  rw [hEnd]
  exact (P).reservoirVacuumEdge i (c - Finsupp.single j 1) hw₂
local notation "ps" => SPath.two (c₁ := Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up j]))
  (c₂ := Col.mk (up j) (SKM.wt D ν v)) false false hv₁ hv₂ hEnd
local notation "pt" => SPath.two (c₁ := Col.mk (up j) (SKM.wt D (SKM.wt D ν v) [up i]))
  (c₂ := Col.mk (up i) (SKM.wt D ν v)) false false hw₁ hw₂ rfl
local notation "p" => SPath.append (SPath.append pL ps) pR
local notation "q" => SPath.append (SPath.append pL pt) pR
local notation "r" => rightPath (congrArg Prod.snd hEnd) pR
local notation "h₁" => ProbeReservoir.reservoirVacuumEdge (P) j (c - Finsupp.single i 1) hv₂
local notation "h₂" => ProbeReservoir.reservoirVacuumEdge (P) i c hv₁
local notation "h₃" => targetEdge D Sc m cutoff ΛP ΛR L hP hR i j hw₂ hEnd
local notation "h₄" => ProbeReservoir.reservoirVacuumEdge (P) j c hw₁
local notation "F" => ReservoirLayerCells.crossRawHom D Sc m cutoff L ΛP ΛR pL hl r hr i j h₁ h₂
local notation "G" => ReservoirLayerCells.crossRawHom D Sc m cutoff L ΛP ΛR pL hl r hr j i h₃ h₄
local notation "Z" => ObjectProperty.FullSubcategory.obj (tensorVacuum D Sc m cutoff L ΛP ΛR)
local notation "E0" => tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)
local notation "eS" => tensorLayerCrossSourceIso D Sc m cutoff L ΛP ΛR hP hR ν u v i j hv₁ hv₂ hEnd pL hl pR hr
local notation "eT" => tensorLayerCrossTargetIso D Sc m cutoff L ΛP ΛR hP hR ν u v i j hw₁ hw₂ hEnd pL hl pR hr

/-- The frozen local crossing between the two words is the exact
original-Hom arrow of the complete action's crossing entry. -/
theorem tensorLayerCrossRaw_arrow (a : (P).CrossCoeff) (leftward : (P).LeftwardData) :
    tensorLayerCrossRaw D Sc m cutoff L ΛP ΛR hP hR ν u v i j
      hv₁ hv₂ hw₁ hw₂ hEnd pL hl pR hr a =
    TensorEntryPullback.arrow (E0) (A := F) (B := G)
      (X := ((P).pathFunctor p).obj Z) (Y := ((P).pathFunctor q).obj Z) eS eT
      ((P).compLayer ((P).swappedGens a leftward) (SKM.lay D ν u (.cross i j) v) p q Z) := by
  unfold tensorLayerCrossRaw TensorEntryPullback.arrow
  rfl

end Cross

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
