import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCoefficientChart

/-! # Coefficients at the canonical source-unit observation

SwappedVacuumCoordinates §§6–7: postcomposition on the actual original-row
Hom has the prescribed full coefficient value under the canonical source
unit and quotient coordinate. No supported-matrix action comparison is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
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

/-- Raw source coefficients act by postcomposition on the entire original
row Hom; its canonical source-unit observation has the same coefficient
under the prescribed global path chart and quotient coordinate. -/
theorem tensorOriginalWordCoefficient_observation {b : Obj (SKM.sig D)}
    (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) = b.endR)
    (p : SPath b.word (0,cS) (0,0)) (hup : ∀ d ∈ b.word, d.l.1 = true)
    (x : matrixModule D Sc m cutoff N ΛP ΛR
      (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L) b)
    (a : SYM D k) :
    PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (b.word.map (fun d => d.l.2))
      (((tensorPathValueChart D Sc m cutoff ΛP ΛR L p hup).hom βS).total wS
        (((VacuumTensorCoefficientMaps.pathHomCoefficientAction D Tw m cutoff L ΛP ΛR p hup
          (tensorOriginalRowSource D Sc m cutoff ΛP ΛR L s) a
          (tensorOriginalWordEntry D Sc m cutoff ΛP ΛR L hP hR s hEnd p hup x)).total R₀ βS).total wS
            (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s))) =
    PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (b.word.map (fun d => d.l.2))
      ((tensorWordCoefficientArrow D Sc cutoff ΛR L (ReservoirWord.weight D ΛR cS)
        (b.word.map (fun d => d.l.2)).reverse a βS).total wS
        (((tensorPathValueChart D Sc m cutoff ΛP ΛR L p hup).hom βS).total wS
          (((tensorOriginalWordEntry D Sc m cutoff ΛP ΛR L hP hR s hEnd p hup x).total R₀ βS).total wS
            (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s)))) := by
  let f := tensorOriginalWordEntry D Sc m cutoff ΛP ΛR L hP hR s hEnd p hup x
  let z := tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s
  have heval :
      ((VacuumTensorCoefficientMaps.pathHomCoefficientAction D Tw m cutoff L ΛP ΛR p hup
        (tensorOriginalRowSource D Sc m cutoff ΛP ΛR L s) a f).total R₀ βS).total wS z =
      ((VacuumTensorCoefficientMaps.pathCoefficientAction D Tw m cutoff L ΛP ΛR p hup a).total R₀ βS).total wS
        ((f.total R₀ βS).total wS z) := by
    change (((f ≫ VacuumTensorCoefficientMaps.pathCoefficientAction D Tw m cutoff L ΛP ΛR p hup a).total R₀ βS).total wS z) = _
    rw [Superfunctor.comp_total]
    change (((f.total R₀ βS) ≫
      (VacuumTensorCoefficientMaps.pathCoefficientAction D Tw m cutoff L ΛP ΛR p hup a).total R₀ βS).total wS z) = _
    rw [Superfunctor.comp_total]
    rfl
  change _ = PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (b.word.map (fun d => d.l.2))
    ((tensorWordCoefficientArrow D Sc cutoff ΛR L (ReservoirWord.weight D ΛR cS)
        (b.word.map (fun d => d.l.2)).reverse a βS).total wS
      (((tensorPathValueChart D Sc m cutoff ΛP ΛR L p hup).hom βS).total wS
        ((f.total R₀ βS).total wS z)))
  rw [heval]
  exact congrArg (PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (b.word.map (fun d => d.l.2)))
    (tensorPathCoefficient_square_apply D Sc m cutoff ΛP ΛR L p hup a βS wS ((f.total R₀ βS).total wS z))
end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
