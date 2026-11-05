import OddMath.QuiverHecke.SwappedAssembly.SupportedActionLayers

/-! # Generating layers of `H` in the complete supported action

SwappedVacuumCoordinates §§5–7 and Brundan–Ellis (11.7): a generating layer
`L` of the quiver Hecke supercategory, pushed through the upward functor `α`
at weight `μ`, acts in `pointwiseUpwardModuleAction` by the literal supported
local operator of its weight labelling `(label D μ).layer L`. This is the
form of the layer action consumed by the corner square of
`VacuumCornerEvaluation`.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance supportedActionAlphaLayerHomPi {k : Type u} [CommRing k]
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
local notation "action" => pointwiseUpwardModuleAction D Sc m cutoff bound ΛP ΛR hP hR sy hc Gs Ys
attribute [local irreducible] elvProbeCrossCoeffOf

/-- A generating layer of `H`, pushed through `α` at weight `μ`, acts by the
supported local operator of its weight labelling. -/
theorem pointwiseUpwardModuleAction_act_ofLayer (μ : X)
    (L : Layer (QuiverHecke.sig D)) (hv : L.Valid) :
    (action μ).act L.dom.word L.cod.word
        ((QuiverHecke.alpha D Sc μ).map
          ((QuiverHecke.pres D Sc).diag (Diagram.ofLayer L hv))) =
      (Q).res (SKM.ob D μ (upWord L.cod.word)) ∘ₗ (Q).op ((QuiverHecke.label D μ).layer L) ∘ₗ
        (Q).ext (SKM.ob D μ (upWord L.dom.word)) := by
  rw [QuiverHecke.alpha_diag, LayerMap.map_ofLayer]
  exact pointwiseUpwardModuleAction_act_layer D Sc m cutoff bound ΛP ΛR hP hR sy hc Gs Ys μ
    L.dom.word L.cod.word _ _ _ _

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
