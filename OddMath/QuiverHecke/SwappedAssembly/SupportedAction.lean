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
variable [Finite I] (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound)
  (hwin : ReservoirWindowIdeal D Sc m cutoff bound ΛP ΛR hP hR)
local notation "c" => elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot
local notation "L" => pointwiseLeftwardData D Sc m cutoff bound ΛP ΛR hP hR hdot
attribute [local irreducible] elvProbeCrossCoeffOf

private theorem pointwiseQuad
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s) :
    QuadRelations Sc ((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj)
      ((P).swappedGens c L)) :=
  ProbeReservoir.quadRelations («P» := P) (Gs := fun s => (Gs s).obj)
    (Ys := fun s => (Ys s).obj) ((P).swappedGens_crossQuad c L)

private theorem pointwiseSlide
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s) :
    SlideRelations Sc ((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj)
      ((P).swappedGens c L)) :=
  ProbeReservoir.slideRelations («P» := P) (Gs := fun s => (Gs s).obj)
    (Ys := fun s => (Ys s).obj) ((P).swappedGens_crossSlide c
      (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hP hR
    hdot)
      (elvProbeCrossDenominatorUnitsOf D Sc m cutoff bound ΛP ΛR hP hR
      hdot) L)

private theorem pointwiseBraid
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s) :
    BraidRelations Sc ((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj)
      ((P).swappedGens c L)) :=
  (P).braidRelationsOfDenominatorUnits c L
    (Gs := fun s => (Gs s).obj) (Ys := fun s => (Ys s).obj)
    (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hP hR
    hdot)
    (elvProbeCrossDenominatorUnitsOf D Sc m cutoff bound ΛP ΛR hP hR
      hdot)

private theorem pointwiseZigzag
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s) :
    ZigzagRelations Sc ((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj)
      ((P).swappedGens c L)) :=
  ProbeReservoir.zigzagRelations («P» := P) (Gs := fun s => (Gs s).obj)
    (Ys := fun s => (Ys s).obj) ((P).cupCapZigzag_swappedGens c L)

private theorem pointwiseWindowZero
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s) :
    WindowZeroRelations Sc ((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj)
      ((P).swappedGens c L)) :=
  ProbeReservoir.windowZeroRelations («P» := P) (fun s => (Gs s).obj) (fun s => (Ys s).obj)
    ((P).swappedGens_windowZero c L)

include hwin in
/-- Intermediate assembly with only the distinct-colour permutation input
still explicit; no raw-global equal-colour inversion premise is required. -/
theorem pointwiseObligations_of_sigmaPermutation
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
    (hσ : ∀ i j ν, i ≠ j → (P).SigmaPermutation c i j ν) :
    SwappedObligations Sc ((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj)
      ((P).swappedGens c L)) where
  quad := pointwiseQuad D Sc m cutoff bound ΛP ΛR hP hR hdot Gs Ys
  slide := pointwiseSlide D Sc m cutoff bound ΛP ΛR hP hR hdot Gs Ys
  braid := pointwiseBraid D Sc m cutoff bound ΛP ΛR hP hR hdot Gs Ys
  zigzag := pointwiseZigzag D Sc m cutoff bound ΛP ΛR hP hR hdot Gs Ys
  inversion := inversionRelations_of_supportedInverse D Sc m cutoff bound ΛP ΛR hP hR
    Gs Ys c L hσ (pointwiseLeftward_isInverseAt D Sc m cutoff bound ΛP ΛR hP hR
        hdot
        hwin)
  windowZero := pointwiseWindowZero D Sc m cutoff bound ΛP ΛR hP hR hdot Gs Ys
  interchange := pointwiseLeftward_interchangeLaw D Sc m cutoff bound ΛP ΛR hP hR
        hdot
        hwin Gs Ys
    (fun i j hij ν => hσ i j ν hij)

include hwin in
/-- The chosen supported Hom construction satisfies the exact native obligations. -/
theorem pointwiseObligations
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s) :
    SwappedObligations Sc ((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj)
      ((P).swappedGens c L)) :=
  pointwiseObligations_of_sigmaPermutation D Sc m cutoff bound ΛP ΛR hP hR hdot hwin Gs Ys
    (fun i j ν hij => elvProbeSigmaPermutation D Sc m cutoff bound ΛP ΛR hP hR hdot i j ν hij)

include hwin in
/-- The resulting supported upward module action used by the vacuum observations. -/
def pointwiseUpwardModuleAction
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s) (μ : X) :
    UpwardModuleAction D Sc μ :=
  upwardModuleActionOfObligations D Sc m cutoff bound ΛP ΛR hP hR Gs Ys
    ((P).swappedGens c L)
    (pointwiseObligations D Sc m cutoff bound ΛP ΛR hP hR hdot hwin Gs Ys) μ

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
