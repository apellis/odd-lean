import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCoefficientUnitObservation
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorMatrixRowCoefficients

/-! # Full matrix coefficients in the canonical observation

SwappedVacuumCoordinates §§6–7: the unchanged canonical matrix
observation carries the actual full source-coefficient matrix action to
the original signed word coefficient on its charted source-unit value.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
attribute [local irreducible] tensorMatrixQuotientObservation tensorPathValueChart
  tensorOriginalWordEntry tensorOriginalSourceUnit tensorMatrixCoefficientAction
  PowerWordQuotientCoordinates.coordinate
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s : List I)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "R₀" => WeightTensorVacuum.regularProbe D Tw m ΛP
local notation "cS" => tensorSourceContent D ΛP ΛR s
local notation "βS" => tensorSourceWordBlock D ΛP ΛR s
local notation "wS" => PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl

/-- The actual full matrix coefficient action has its unchanged canonical
quotient observation, with no generator or chart-comparison premise.
Every raw coefficient, including mixed parity, acts by the same signed
word coefficient on the charted original row at its prescribed unit. -/
theorem tensorMatrixCoefficient_observation {b : Obj (SKM.sig D)}
    (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) = b.endR)
    (p : SPath b.word (0,cS) (0,0)) (hup : ∀ d ∈ b.word, d.l.1 = true)
    (a : SYM D k)
    (x : matrixModule D Sc m cutoff N ΛP ΛR
      (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L) b) :
    tensorMatrixQuotientObservation D Sc m cutoff ΛP ΛR L hP hR s hEnd p hup
      (tensorMatrixCoefficientAction D Sc m cutoff ΛP ΛR L s b a x) =
    PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (b.word.map (fun d => d.l.2))
      ((tensorWordCoefficientArrow D Sc cutoff ΛR L (ReservoirWord.weight D ΛR cS)
        (b.word.map (fun d => d.l.2)).reverse a βS).total wS
        (((tensorPathValueChart D Sc m cutoff ΛP ΛR L p hup).hom βS).total wS
          (((tensorOriginalWordEntry D Sc m cutoff ΛP ΛR L hP hR s hEnd p hup x).total R₀ βS).total wS
            (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s)))) := by
  unfold tensorMatrixQuotientObservation
  rw [tensorOriginalWordEntry_coefficient D Sc m cutoff ΛP ΛR L hP hR s hEnd p hup a x]
  generalize hf : tensorOriginalWordEntry D Sc m cutoff ΛP ΛR L hP hR s hEnd p hup x = f at ⊢
  clear hf
  generalize hz : tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s = z at ⊢
  clear hz
  exact tensorOriginalWordCoefficient_observation D Sc m cutoff ΛP ΛR L s p hup f z a
end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
