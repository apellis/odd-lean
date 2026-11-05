import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCoefficientChart

/-! # Coefficients at the canonical source-unit observation

SwappedVacuumCoordinates §§6–7: postcomposition on the actual original-row
Hom has the prescribed full coefficient value on every source vector,
including the canonical source unit, under its quotient coordinate. No supported-matrix action comparison is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
attribute [local irreducible] tensorPathValueChart PowerWordQuotientCoordinates.coordinate
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (s : List I)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "R₀" => WeightTensorVacuum.regularProbe D Tw m ΛP
local notation "cS" => tensorSourceContent D ΛP ΛR s
local notation "βS" => tensorSourceWordBlock D ΛP ΛR s
local notation "wS" => PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl

private theorem originalWordCoefficient_value {l : List (Col I X)}
    (p : SPath l (0,cS) (0,0)) (hup : ∀ d ∈ l, d.l.1 = true)
    (f : tensorOriginalRowSource D Sc m cutoff ΛP ΛR L s ⟶
      TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p hup)
    (z : (((tensorOriginalRowSource D Sc m cutoff ΛP ΛR L s).obj R₀) βS).obj wS)
    (a : SYM D k) :
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

/-- Raw source coefficients act by postcomposition on the entire original
row Hom; evaluation at every source vector has the same coefficient
under the prescribed global path chart and quotient coordinate. -/
theorem tensorOriginalWordCoefficient_observation {l : List (Col I X)}
    (p : SPath l (0,cS) (0,0)) (hup : ∀ d ∈ l, d.l.1 = true)
    (f : tensorOriginalRowSource D Sc m cutoff ΛP ΛR L s ⟶
      TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p hup)
    (z : (((tensorOriginalRowSource D Sc m cutoff ΛP ΛR L s).obj R₀) βS).obj wS)
    (a : SYM D k) :
    PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (l.map (fun d => d.l.2))
      (((tensorPathValueChart D Sc m cutoff ΛP ΛR L p hup).hom βS).total wS
        (((VacuumTensorCoefficientMaps.pathHomCoefficientAction D Tw m cutoff L ΛP ΛR p hup
          (tensorOriginalRowSource D Sc m cutoff ΛP ΛR L s) a
          f).total R₀ βS).total wS
            z)) =
    PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (l.map (fun d => d.l.2))
      ((tensorWordCoefficientArrow D Sc cutoff ΛR L (ReservoirWord.weight D ΛR cS)
        (l.map (fun d => d.l.2)).reverse a βS).total wS
        (((tensorPathValueChart D Sc m cutoff ΛP ΛR L p hup).hom βS).total wS
          ((f.total R₀ βS).total wS
            z))) := by
  rw [originalWordCoefficient_value D Sc m cutoff ΛP ΛR L s p hup f z a]
  generalize hQ : PowerWordQuotientCoordinates.coordinate D Sc cutoff L s
    (l.map (fun d => d.l.2)) = q at ⊢
  clear hQ
  apply congrArg q
  exact tensorPathCoefficient_square_apply D Sc m cutoff ΛP ΛR L p hup a βS wS
    ((f.total R₀ βS).total wS z)
end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
