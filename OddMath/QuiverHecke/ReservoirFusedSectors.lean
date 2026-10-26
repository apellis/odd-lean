/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.ReservoirFusedDetection
import OddMath.SKM.RouquierMateSectors

/-! # Fused vacuum bubble sectors from sector summands

Ports the use of the coproduct sectors of
`Categorification/TwoRep/RouqCoproduct.lean` in
`Categorification/KLR/Unfurling/VacuumRouqBubbles.lean`: the bubble sectors
of the fused vacuum are built from the reservoir and probe summands of the two
coupled raising functors, with their own adjunctions and dots.

`VacuumSectorBubble` takes the reservoir and probe summands
(`SKM.SourceSector`, `SKM.TargetSector`), the upward slide of the coupled
crossing, inverses of the two probe dots and nilpotence of the two reservoir
dots. The mate projection coordinates are then the actual dotted sector cups
and caps, and F's `MateProjectionFormula.of_sectors` proves the projection
formula (`toSector_mateProjection`). The reservoir coefficients are capped
dotted reservoir cups, the probe coefficients capped probe caps with powers of
the inverse probe dot. `upward_independence_of_fused_sector_actions` therefore
has no mate projection hypothesis: only the sector data and slide (action),
the fused bubble identification (fusion inversion) and the regular
identification remain.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open scoped BigOperators
universe u v w
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : SKM.Datum I X} {Sc : SKM.Scalars D k} {cs : SKM.CScalars Sc}

/-- Separated sector summands at the vacuum, for one coefficient generator `g`.
The fields `slide`, `w`/`hw`, `z`/`hz`, `hnC`/`hnD` are exactly the inputs of
`SKM.SuperRouquierLoc.MateProjectionFormula.of_sectors`. `fused` is the fusion
inversion output; `probe`, `reservoirValue` and `normalize` are the vacuum
values of the two factors, as in `VacuumBubbleSector`. -/
structure VacuumSectorBubble {μ : X} (W : FusedVacuumWords D Sc cs μ)
    (reservoir : ∀ t, SKM.SYM D k →ₐ[k] Module.End k (W.V t)) (g : SKM.SYM D k)
    (B : Type v) [BicategoryStruct.{w,w} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
    [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B] where
  a : B
  b : B
  c : B
  E₁ : a ⟶ b
  F₁ : b ⟶ a
  E₂ : b ⟶ c
  F₂ : c ⟶ b
  A₁ : SKM.SuperAdjunction (k := k) E₁ F₁
  A₂ : SKM.SuperAdjunction (k := k) E₂ F₂
  x₁ : E₁ ⟶ E₁
  x₂ : E₂ ⟶ E₂
  cross : E₁ ≫ E₂ ⟶ E₁ ≫ E₂
  p : ZMod 2
  slide : cross ≫ E₁ ◁ x₂ - koszulSign p p • (x₁ ▷ E₂ ≫ cross) = 𝟙 (E₁ ≫ E₂)
  RA : SKM.SourceSector A₁ x₁
  RB : SKM.SourceSector A₁ x₁
  TA : SKM.TargetSector A₂ x₂
  TB : SKM.TargetSector A₂ x₂
  w : RB.E ⟶ RB.E
  hw : w ≫ RB.dot = 𝟙 RB.E
  z : TB.E ⟶ TB.E
  hz : TB.dot ≫ z = 𝟙 TB.E
  nC : ℕ
  nD : ℕ
  hnC : SKM.rouquierPower TA.dot nC = 0
  hnD : SKM.rouquierPower RA.dot nD = 0
  probeCup : 𝟙 b ⟶ RB.F ≫ RB.E
  reservoirCap : TA.E ≫ TA.F ⟶ 𝟙 b
  eval : ∀ t, End (𝟙 b) →+* Module.End k (W.V t)
  fused : ∀ t, eval t (probeCup ≫ SKM.sectorIn RB.iE RB.iF ≫
    (-(koszulSign p p) • SKM.rouquierMate A₁ A₂ cross) ≫
      SKM.sectorOut TA.pE TA.pF ≫ reservoirCap) = W.bubbles t g
  probeCoeff : ℕ → k
  res : ℕ → SKM.SYM D k
  probe : ∀ t (r : ℕ), eval t (probeCup ≫ SKM.probeCap RB w (-(r : ℤ) - 1)) =
    algebraMap k _ (probeCoeff r)
  reservoirValue : ∀ t (r : ℕ), eval t (TA.cup r ≫ reservoirCap) = reservoir t (res r)
  normalize : ∑ r ∈ Finset.range nC, (koszulSign p p) ^ r • (probeCoeff r • res r) = g

namespace VacuumSectorBubble
variable {μ : X} {W : FusedVacuumWords D Sc cs μ}
  {reservoir : ∀ t, SKM.SYM D k →ₐ[k] Module.End k (W.V t)} {g : SKM.SYM D k}
  {B : Type v} [BicategoryStruct.{w,w} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  (S : VacuumSectorBubble W reservoir g B)

/-- The bubble sector with the actual dotted sector cups and caps as mate
projection coordinates. -/
def toSector : VacuumBubbleSector W reservoir g B where
  a := S.a
  b := S.b
  c := S.c
  E₁ := S.E₁
  F₁ := S.F₁
  E₂ := S.E₂
  F₂ := S.F₂
  A₁ := S.A₁
  A₂ := S.A₂
  cross := S.cross
  p := S.p
  XA := S.RA.F ≫ S.RA.E
  XB := S.RB.F ≫ S.RB.E
  YA := S.TA.E ≫ S.TA.F
  YB := S.TB.E ≫ S.TB.F
  inA := SKM.sectorIn S.RA.iE S.RA.iF
  inB := SKM.sectorIn S.RB.iE S.RB.iF
  outA := SKM.sectorOut S.TA.pE S.TA.pF
  outB := SKM.sectorOut S.TB.pE S.TB.pF
  uA := S.TA.cup
  vA := S.RA.cap
  uB := SKM.probeCup S.TB S.z
  vB := SKM.probeCap S.RB S.w
  nC := S.nC
  nD := S.nD
  probeCup := S.probeCup
  reservoirCap := S.reservoirCap
  eval := S.eval
  fused := S.fused
  probeCoeff := S.probeCoeff
  res := S.res
  probe := S.probe
  reservoirValue := S.reservoirValue
  normalize := S.normalize

/-- The mate projection formula of the sector is proved, by F's
`MateProjectionFormula.of_sectors`. -/
theorem toSector_mateProjection : S.toSector.mateProjection :=
  SKM.SuperRouquierLoc.MateProjectionFormula.of_sectors S.cross S.p S.slide
    S.RA S.RB S.TA S.TB S.w S.hw S.z S.hz S.nC S.nD S.hnC S.hnD

include S in
/-- The fused bubble of the generator acts as its reservoir coefficient. -/
theorem bubbles_eq (t : List I) : W.bubbles t g = reservoir t g :=
  VacuumBubbleSector.bubbles_eq S.toSector S.toSector_mateProjection t

end VacuumSectorBubble

section Field
variable {K : Type u} [Field K] {S : SKM.Scalars D K} {cK : SKM.CScalars S}

variable (D S cK) in
/-- The action and fusion-inversion outputs at the external weight `μ`, with
bubble sectors given by sector summands. -/
structure FusedSectorAction (μ : X) (B : Type v) [BicategoryStruct.{w,w} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear K (a ⟶ b)]
    [∀ a b : B, Supercategory K (a ⟶ b)] [TwoSupercategory K B] where
  family : FusedRegularVacuumFamily D S cK μ (fun j => D.h j μ)
  sectors : ∀ m (g : SKM.SYMGen D),
    VacuumSectorBubble (family.words m) (family.regular m).reservoir (SKM.SYM.ι D K g) B

variable {B : Type v} [BicategoryStruct.{w,w} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear K (a ⟶ b)]
  [∀ a b : B, Supercategory K (a ⟶ b)] [TwoSupercategory K B]

/-- Forget the sector summands, keeping the proved mate projection formulas. -/
def FusedSectorAction.toVacuumAction {μ : X} (A : FusedSectorAction D S cK μ B) :
    FusedVacuumAction D S cK μ B where
  family := A.family
  sectors m := ⟨fun g => (A.sectors m g).toSector⟩

theorem FusedSectorAction.mateProjections {μ : X} (A : FusedSectorAction D S cK μ B) :
    A.toVacuumAction.MateProjections :=
  fun m g => (A.sectors m g).toSector_mateProjection

/-- **Detection from fused sector vacua.** No mate projection hypothesis:
upward independence follows from the sector summands with slide, probe
inverses and reservoir nilpotence, the fused bubble identification, and the
regular identification of the vacuum words. -/
theorem upward_independence_of_fused_sector_actions
    (A : ∀ μ, FusedSectorAction D S cK μ B) : SKM.WeakMate.UpwardIndependence cK :=
  upward_independence_of_fused_vacuum_actions (fun μ => (A μ).toVacuumAction)
    fun μ => (A μ).mateProjections

end Field
end OddMath.QuiverHecke
