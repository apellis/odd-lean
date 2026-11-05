import OddMath.QuiverHecke.SwappedAssembly.SupportedAction
import OddMath.QuiverHecke.SwappedAssembly.SupportedMatrixLayers

/-! # Presented layers in the complete supported action

SwappedVacuumCoordinates §§5–7 and Brundan–Ellis Definition 1.5:
the complete upward module action evaluates a presented single layer
by the literal supported local operator. This attaches the action
used by bounded recovery to the native tensor-row layer formulas.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance supportedActionLayerHomPi {k : Type u} [CommRing k]
    (A C : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ) (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  [Finite I] (sy : Symmetrizer D) (hc : Sc.Homogeneous)
  (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local notation "c" => elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR
    (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
      (parameterTwist_homogeneous D Sc hc) bound)
local notation "leftward" => pointwiseLeftwardData D Sc m cutoff bound ΛP ΛR hP hR
        (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
          (parameterTwist_homogeneous D Sc hc) bound)
local notation "gens" => ProbeReservoir.swappedGens (P) c leftward
local notation "Q" => interpretation D Sc m cutoff bound ΛP ΛR hP hR Gs Ys gens
local notation "action" => pointwiseUpwardModuleAction D Sc m cutoff bound ΛP ΛR hP hR
        (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
          (parameterTwist_homogeneous D Sc hc) bound)
        (reservoirWindowIdeal D Sc m cutoff bound ΛP ΛR hP hR sy hc) Gs Ys
attribute [local irreducible] elvProbeCrossCoeffOf

/-- The complete action of a presented layer is the actual supported
local operator, with no remaining presentation-obligation premise. -/
theorem pointwiseUpwardModuleAction_act_layer (μ : X) (t t' : List I)
    (A : Layer (SKM.sig D)) (hA : A.Valid)
    (hdom : A.dom = SKM.ob D μ (upWord t))
    (hcod : A.cod = SKM.ob D μ (upWord t')) :
    (action μ).act t t' ((SKM.pres D Sc).diag (Diagram.layer A hA hdom hcod)) =
      (Q).res (SKM.ob D μ (upWord t')) ∘ₗ (Q).op A ∘ₗ
        (Q).ext (SKM.ob D μ (upWord t)) := by
  change ((functorOfObligations D Sc m cutoff bound ΛP ΛR hP hR Gs Ys gens
    (pointwiseObligations D Sc m cutoff bound ΛP ΛR hP hR
        (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
          (parameterTwist_homogeneous D Sc hc) bound)
        (reservoirWindowIdeal D Sc m cutoff bound ΛP ΛR hP hR sy hc) Gs Ys)).map
      ((SKM.pres D Sc).diag (Diagram.layer A hA hdom hcod))).hom = _
  unfold functorOfObligations
  rw [Presentation.lift_diag]
  exact LocalInterpretation.functor_map_layer_hom (Q) A hA hdom hcod

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
