import OddMath.SKM.RouquierCoupledMate
import OddMath.QuiverHecke.ReservoirFusedSectors

/-!
# Fused vacuum sectors from coupled separated factors

Ports the use of the coproduct assembly of
`Categorification/TwoRep/RouqCoproduct.lean` in
`Categorification/KLR/Unfurling/VacuumRouqBubbles.lean`: the bubble sector of
the fused vacuum is built from two separated factors through the coupled
adjunction, dots and crossing of `SKM.CoupledFactors`.

`CoupledSectorBubble.toVacuumSectorBubble` fills every structural field of
`VacuumSectorBubble`: the coupled 1-morphisms, adjunctions, dots and crossing,
its slide (`SKM.CoupledFactors.slide`), the four sector summands, the probe
inverses and the reservoir nilpotence. What remains is

* the factor data of `SKM.CoupledFactors`: the sector decompositions of the
  coupled raising and lowering 1-morphisms, the sector adjunctions, dots and
  diagonal crossings with their slides, the sector-swapping blocks, probe-dot
  inverses and reservoir-dot nilpotence (A0 factor actions and A1 shifted
  adjunctions);
* the vacuum values and normalization `probe`, `reservoirValue`, `normalize`
  (as in `VacuumSectorBubble`);
* `fusedBlock`, the fusion inversion output: the sector mate of the rational
  probe-to-reservoir block `rationalPR`, closed by the probe cup and the
  reservoir cap, acts as the fused bubble. The `fused` field of
  `VacuumSectorBubble` follows (`CoupledSectorBubble.fused`) because the
  projected coupled mate is that block's sector mate
  (`SKM.CoupledFactors.probe_mate_reservoir`).
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open scoped BigOperators
universe u v w
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : SKM.Datum I X} {Sc : SKM.Scalars D k} {cs : SKM.CScalars Sc}

/-- The bubble sector of one coefficient generator at the vacuum, from coupled
separated factors. The coupled structure is constructed; the remaining fields
are the action outputs listed in the module docstring. -/
structure CoupledSectorBubble {μ : X} (W : FusedVacuumWords D Sc cs μ)
    (reservoir : ∀ t, SKM.SYM D k →ₐ[k] Module.End k (W.V t)) (g : SKM.SYM D k)
    (B : Type v) [BicategoryStruct.{w,w} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
    [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B] where
  a : B
  b : B
  c : B
  factors : SKM.CoupledFactors (k := k) a b c
  probeCup : 𝟙 b ⟶ factors.P₁ SKM.CoupledSector.probe ≫ factors.O₁ SKM.CoupledSector.probe
  reservoirCap :
    factors.O₂ SKM.CoupledSector.reservoir ≫ factors.P₂ SKM.CoupledSector.reservoir ⟶ 𝟙 b
  eval : ∀ t, End (𝟙 b) →+* Module.End k (W.V t)
  fusedBlock : ∀ t, eval t (probeCup ≫
    (-(koszulSign factors.p factors.p) •
      SKM.rouquierMate (factors.adj₁ SKM.CoupledSector.probe)
        (factors.adj₂ SKM.CoupledSector.reservoir) factors.rationalPR) ≫
    reservoirCap) = W.bubbles t g
  probeCoeff : ℕ → k
  res : ℕ → SKM.SYM D k
  probe : ∀ t (r : ℕ), eval t (probeCup ≫
    SKM.probeCap (factors.sourceSector SKM.CoupledSector.probe) factors.inv₁ (-(r : ℤ) - 1)) =
      algebraMap k _ (probeCoeff r)
  reservoirValue : ∀ t (r : ℕ),
    eval t ((factors.targetSector SKM.CoupledSector.reservoir).cup r ≫ reservoirCap) =
      reservoir t (res r)
  normalize : ∑ r ∈ Finset.range factors.N,
    (koszulSign factors.p factors.p) ^ r • (probeCoeff r • res r) = g

namespace CoupledSectorBubble
variable {μ : X} {W : FusedVacuumWords D Sc cs μ}
  {reservoir : ∀ t, SKM.SYM D k →ₐ[k] Module.End k (W.V t)} {g : SKM.SYM D k}
  {B : Type v} [BicategoryStruct.{w,w} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  (S : CoupledSectorBubble W reservoir g B)

/-- The fused bubble identification for the coupled mate, from the one for the
rational probe-to-reservoir block (`SKM.CoupledFactors.probe_mate_reservoir`). -/
theorem fused (t : List I) : S.eval t (S.probeCup ≫
    SKM.sectorIn (S.factors.DE₁.inc SKM.CoupledSector.probe)
      (S.factors.DF₁.inc SKM.CoupledSector.probe) ≫
    (-(koszulSign S.factors.p S.factors.p) •
      SKM.rouquierMate S.factors.A₁ S.factors.A₂ S.factors.coupledCross) ≫
    SKM.sectorOut (S.factors.DE₂.proj SKM.CoupledSector.reservoir)
      (S.factors.DF₂.proj SKM.CoupledSector.reservoir) ≫
    S.reservoirCap) = W.bubbles t g := by
  rw [← S.fusedBlock t, ← S.factors.probe_mate_reservoir]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]

/-- The sector bubble whose coupled adjunctions, dots, crossing, slide, sector
summands, probe inverses and reservoir nilpotence are those of the coupled
separated factors. -/
def toVacuumSectorBubble : VacuumSectorBubble W reservoir g B where
  a := S.a
  b := S.b
  c := S.c
  E₁ := S.factors.E₁
  F₁ := S.factors.F₁
  E₂ := S.factors.E₂
  F₂ := S.factors.F₂
  A₁ := S.factors.A₁
  A₂ := S.factors.A₂
  x₁ := S.factors.x₁
  x₂ := S.factors.x₂
  cross := S.factors.coupledCross
  p := S.factors.p
  slide := S.factors.slide
  RA := S.factors.sourceSector SKM.CoupledSector.reservoir
  RB := S.factors.sourceSector SKM.CoupledSector.probe
  TA := S.factors.targetSector SKM.CoupledSector.reservoir
  TB := S.factors.targetSector SKM.CoupledSector.probe
  w := S.factors.inv₁
  hw := S.factors.inv₁_dot₁
  z := S.factors.inv₂
  hz := S.factors.dot₂_inv₂
  nC := S.factors.N
  nD := S.factors.N
  hnC := S.factors.nil₂
  hnD := S.factors.nil₁
  probeCup := S.probeCup
  reservoirCap := S.reservoirCap
  eval := S.eval
  fused := S.fused
  probeCoeff := S.probeCoeff
  res := S.res
  probe := S.probe
  reservoirValue := S.reservoirValue
  normalize := S.normalize

include S in
/-- The fused bubble of the generator acts as its reservoir coefficient. -/
theorem bubbles_eq (t : List I) : W.bubbles t g = reservoir t g :=
  VacuumSectorBubble.bubbles_eq S.toVacuumSectorBubble t

end CoupledSectorBubble

section Field
variable {K : Type u} [Field K] {S : SKM.Scalars D K} {cK : SKM.CScalars S}

variable (D S cK) in
/-- The action and fusion-inversion outputs at the external weight `μ`, with
bubble sectors from coupled separated factors. -/
structure FusedCoupledAction (μ : X) (B : Type v) [BicategoryStruct.{w,w} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear K (a ⟶ b)]
    [∀ a b : B, Supercategory K (a ⟶ b)] [TwoSupercategory K B] where
  family : FusedRegularVacuumFamily D S cK μ (fun j => D.h j μ)
  sectors : ∀ m (g : SKM.SYMGen D),
    CoupledSectorBubble (family.words m) (family.regular m).reservoir (SKM.SYM.ι D K g) B

variable {B : Type v} [BicategoryStruct.{w,w} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear K (a ⟶ b)]
  [∀ a b : B, Supercategory K (a ⟶ b)] [TwoSupercategory K B]

/-- Forget the coupled factors, keeping the constructed sector summands. -/
def FusedCoupledAction.toSectorAction {μ : X} (A : FusedCoupledAction D S cK μ B) :
    FusedSectorAction D S cK μ B where
  family := A.family
  sectors m g := (A.sectors m g).toVacuumSectorBubble

/-- **Detection from coupled separated factors.** The coupled crossing, its
slide and the sector summands are constructed; the remaining inputs are the
factor data, the vacuum values, the fused bubble identification and the
regular identification of the vacuum words. -/
theorem upward_independence_of_fused_coupled_actions
    (A : ∀ μ, FusedCoupledAction D S cK μ B) : SKM.WeakMate.UpwardIndependence cK :=
  upward_independence_of_fused_sector_actions fun μ => (A μ).toSectorAction

end Field
end OddMath.QuiverHecke
