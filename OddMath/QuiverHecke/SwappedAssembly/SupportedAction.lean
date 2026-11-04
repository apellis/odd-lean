import OddMath.QuiverHecke.SwappedAssembly.Action
import OddMath.QuiverHecke.SwappedAssembly.QuadNe
import OddMath.QuiverHecke.SwappedAssembly.SlideAssembly
import OddMath.QuiverHecke.SwappedAssembly.BraidAssembly
import OddMath.QuiverHecke.SwappedAssembly.CupCapZigzag
import OddMath.QuiverHecke.SwappedAssembly.SupportedAugmentedInverse
import OddMath.QuiverHecke.SwappedAssembly.SupportedInversionRelations
import OddMath.QuiverHecke.SwappedAssembly.SupportedSupernaturality
import OddMath.QuiverHecke.SwappedAssembly.SupportedPresentation
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeSigmaPermutation

/-! # The native presentation obligations on supported inputs

Brundan–Ellis Definition 1.5 and (2.6), `SwappedActionAssembly.md` F4:
the constructed pointwise leftward entries give the exact native
obligations for supported source and target families. Local inverse
and naturality theorems are used only on the supported objects reached
by context paths. An intermediate assembly isolates the distinct-colour
permutation input; the chosen ELV permutation theorem supplies it in
the final obligations and resulting upward module action.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance supportedActionHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local notation "c" "[" sy "," hc "]" =>
  elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc
local notation "L" "[" sy "," hc "]" =>
  pointwiseLeftwardData D Sc m cutoff bound ΛP ΛR hP hR sy hc
attribute [local irreducible] elvProbeReservoir elvProbeCrossCoeff

/-- Intermediate assembly with only the distinct-colour permutation input
still explicit; no raw-global equal-colour inversion premise is required. -/
theorem pointwiseObligations_of_sigmaPermutation [Finite I]
    (sy : Symmetrizer D) (hc : Sc.Homogeneous)
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
    (hσ : ∀ i j ν, i ≠ j → (P).SigmaPermutation c[sy,hc] i j ν) :
    SwappedObligations Sc ((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj)
      ((P).swappedGens c[sy,hc] L[sy,hc])) where
  quad := ProbeReservoir.quadRelations ((P).swappedGens_crossQuad c[sy,hc] L[sy,hc])
  slide := ProbeReservoir.slideRelations ((P).swappedGens_crossSlide c[sy,hc]
    (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc)
    (elvProbeCrossDenominatorUnits D Sc m cutoff bound ΛP ΛR hP hR sy hc) L[sy,hc])
  braid := (P).braidRelationsOfDenominatorUnits c[sy,hc] L[sy,hc]
    (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc)
    (elvProbeCrossDenominatorUnits D Sc m cutoff bound ΛP ΛR hP hR sy hc)
  zigzag := ProbeReservoir.zigzagRelations ((P).cupCapZigzag_swappedGens c[sy,hc] L[sy,hc])
  inversion := inversionRelations_of_supportedInverse D Sc m cutoff bound ΛP ΛR hP hR
    Gs Ys c[sy,hc] L[sy,hc] hσ (pointwiseLeftward_isInverseAt D Sc m cutoff bound ΛP ΛR hP hR sy hc)
  windowZero := ProbeReservoir.windowZeroRelations (fun s => (Gs s).obj) (fun s => (Ys s).obj)
    ((P).swappedGens_windowZero c[sy,hc] L[sy,hc])
  interchange := pointwiseLeftward_interchangeLaw D Sc m cutoff bound ΛP ΛR hP hR sy hc Gs Ys hσ

/-- The chosen supported Hom construction satisfies the exact native obligations. -/
theorem pointwiseObligations [Finite I]
    (sy : Symmetrizer D) (hc : Sc.Homogeneous)
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s) :
    SwappedObligations Sc ((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj)
      ((P).swappedGens c[sy,hc] L[sy,hc])) :=
  pointwiseObligations_of_sigmaPermutation D Sc m cutoff bound ΛP ΛR hP hR sy hc Gs Ys
    (fun i j ν hij => elvProbeSigmaPermutation D Sc m cutoff bound ΛP ΛR hP hR sy hc i j ν hij)

/-- The resulting supported upward module action used by the vacuum observations. -/
def pointwiseUpwardModuleAction [Finite I]
    (sy : Symmetrizer D) (hc : Sc.Homogeneous)
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s) (μ : X) :
    UpwardModuleAction D Sc μ :=
  upwardModuleActionOfObligations D Sc m cutoff bound ΛP ΛR hP hR Gs Ys
    ((P).swappedGens c[sy,hc] L[sy,hc])
    (pointwiseObligations D Sc m cutoff bound ΛP ΛR hP hR sy hc Gs Ys) μ

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
