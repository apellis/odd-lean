/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.ReservoirFusedBubbles

/-! # Upward independence from fused vacua and the mate projection formula

Ports the assembly step of
`Categorification/KLR/Unfurling/GenericVacuumWordCoordinates.lean` and
`Categorification/KLR/Unfurling/GenericKLBubbles.lean`: generic vacuum
coordinates together with the generic bubble values detect the upward
spaces.

`FusedVacuumAction` collects, at one external weight, exactly the outputs of
the action and of fusion inversion on the cofinal reservoir vacua: the vacuum
word modules (A0/A1), their identification with the connected regular
modules (A0/A1), and the separated bubble sectors (`fused`: A2;
probe/reservoir values and normalization: A0/A1). It contains no detection,
injectivity or bubble formula. The theorem
`upward_independence_of_fused_vacuum_actions` assumes only these data and
F's `SuperRouquierLoc.MateProjectionFormula` for every sector, and derives
`NormalizedBubbleFormula` and the categorical cover before applying
`upward_independence_of_fused_fixed_weight_families`.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u v w
variable {I X K : Type u} [AddCommGroup X] [Field K]
  {D : SKM.Datum I X} {S : SKM.Scalars D K} {cK : SKM.CScalars S}

variable (D S cK) in
/-- The action and fusion-inversion outputs at the external weight `μ`, on
the balanced reservoir vacua `reservoirLevel (⟨h_j, μ⟩) m`. -/
structure FusedVacuumAction (μ : X) (B : Type v) [BicategoryStruct.{w,w} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear K (a ⟶ b)]
    [∀ a b : B, Supercategory K (a ⟶ b)] [TwoSupercategory K B] where
  family : FusedRegularVacuumFamily D S cK μ (fun j => D.h j μ)
  sectors : ∀ m, VacuumBubbleSectors (family.words m) (family.regular m).reservoir B

namespace FusedVacuumAction
variable {B : Type v} [BicategoryStruct.{w,w} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear K (a ⟶ b)]
  [∀ a b : B, Supercategory K (a ⟶ b)] [TwoSupercategory K B]
  {μ : X} (A : FusedVacuumAction D S cK μ B)

/-- F's mate projection obligation for every sector of every level. -/
def MateProjections : Prop := ∀ m, (A.sectors m).MateProjections

/-- The derived bubble formula at every reservoir level. -/
theorem normalizedBubbleFormula (hM : A.MateProjections) (m : ℕ) :
    ((A.family.words m).evaluation (fun j => D.h j μ) m
      (A.family.regular m)).NormalizedBubbleFormula :=
  (A.family.words m).evaluation_normalizedBubbleFormula _ m _
    ((A.sectors m).fused_bubbles_eq_reservoir (hM m))

/-- The fused fixed-weight family, with `covers` and `affine_coordinates`
constructed and the bubble formula derived. -/
def toFamily (hM : A.MateProjections) : FusedFixedWeightFamily D S cK μ :=
  A.family.toFamily (A.normalizedBubbleFormula hM)

end FusedVacuumAction

/-- **Detection from fused vacua.** Upward independence holds at every
weight, assuming only the action and fusion-inversion outputs on the
reservoir vacua and the mate projection formula of every separated sector. -/
theorem upward_independence_of_fused_vacuum_actions
    {B : Type v} [BicategoryStruct.{w,w} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear K (a ⟶ b)]
    [∀ a b : B, Supercategory K (a ⟶ b)] [TwoSupercategory K B]
    (A : ∀ μ, FusedVacuumAction D S cK μ B) (hM : ∀ μ, (A μ).MateProjections) :
    SKM.WeakMate.UpwardIndependence cK :=
  upward_independence_of_fused_fixed_weight_families D S cK fun μ => (A μ).toFamily (hM μ)

end OddMath.QuiverHecke
