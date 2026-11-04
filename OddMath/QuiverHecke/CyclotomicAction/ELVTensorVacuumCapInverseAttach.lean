/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedVacuumCapInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumColumnMoments
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumWholeInput

/-! # Odd moments of the chosen vacuum cap inverse

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8.

At formal content zero and positive height `h = P_i - N_i`, the supported vacuum
input is the tensor input (`tensorSectorInput_eq_supported`), and its selected
output block is the tensor vacuum probe functor (`tensorOutputAt_empty`). The
actual positive factor matrix therefore supplies a cap-window inverse `(j, A)` of
the evaluated odd bend with native rows `x ^ n ≫ v`, `n < h`
(`vacuumCapInverse_native_odd`), and its last padded column `A (h - 1)` has the
substituted-series moments of `tensorVacuumCapInverse_odd_moments`. This is the
positive-height odd bubble identity on the chosen inverse of the vacuum
adjunction. No inverse, moment or bubble value is assumed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open CyclotomicAction SwappedAssembly ProbeVacuumCap BalancedInduction PowerVacuumCoefficient
universe u

local instance tensorVacuumAttachHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (i : I)
local notation "bound" => PowerWordContent.powerBound D cutoff L
local notation "R₀" => contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)
local notation "H" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff bound
  ((BalancedInduction.restriction
    (contentInclusion D (parameterTwist D Sc) cutoff bound (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D (parameterTwist D Sc) cutoff L))
local notation "V" => Superfunctor.obj H (probeOldVacuumRegular D (parameterTwist D Sc) m)
local notation "star" =>
  (⟨⟨[]⟩, rfl⟩ : ContentCategory D (parameterTwist D Sc) cutoff bound 0)

omit [Fintype I] in
private theorem odd_probeCutoff (hi : D.parity i = 1) : probeCutoff D m i = 2 * m i := by
  simp [probeCutoff, probeDotExponent, hi]

include hcP hcR sy hc in
/-- **Positive-height odd bubble moments of the vacuum adjunction.** For an odd
colour with `0 < N_i < P_i`, the actual positive factor matrix of the supported
vacuum sector supplies an entrywise inverse `(j, A)` of the native cap window
`[bend; x ^ n ≫ v]_(n < P_i - N_i)` of the evaluated tensor vacuum bend, and the
last padded column of `A` has the substituted-series moments: the even shifts give
the coefficients of the substituted probe series and the odd shifts give them
multiplied by the reservoir odd coefficient. -/
theorem tensorVacuum_chosenCapInverse_odd_moments (hi : D.parity i = 1)
    (hN : 0 < cutoff i) (hlt : cutoff i < probeCutoff D m i) :
    ∃ (j : _) (A : Fin (probeCutoff D m i - cutoff i) →
        (V ⟶ shiftedPreSourceObject D (parameterTwist D Sc) m R₀ i H)),
      ProbeWindow.IsCapInverse
        (evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i (hN.trans hlt) H)
        (fun n : Fin (probeCutoff D m i - cutoff i) =>
          (shiftedPreDot D (parameterTwist D Sc) m R₀ i H ^ (n : ℕ)) ≫
            shiftedPreCap D (parameterTwist D Sc) m R₀ i (hN.trans hlt) H) j A ∧
      ∀ (s : ℕ) (z : (V).obj star),
        tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
            ((A ⟨probeCutoff D m i - cutoff i - 1, by omega⟩ ≫
              (shiftedPreDot D (parameterTwist D Sc) m R₀ i H ^
                (probeCutoff D m i - cutoff i - 1 + 2 * s)) ≫
              shiftedPreCap D (parameterTwist D Sc) m R₀ i (hN.trans hlt) H).total star z) =
          polynomialToPower D cutoff L (PowerSeries.coeff s
              (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
            tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z ∧
        tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
            ((A ⟨probeCutoff D m i - cutoff i - 1, by omega⟩ ≫
              (shiftedPreDot D (parameterTwist D Sc) m R₀ i H ^
                (probeCutoff D m i - cutoff i + 2 * s)) ≫
              shiftedPreCap D (parameterTwist D Sc) m R₀ i (hN.trans hlt) H).total star z) =
          ((-1 : k) ^ (cutoff i + 1) •
              coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
            (polynomialToPower D cutoff L (PowerSeries.coeff s
              (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
              tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z) := by
  classical
  have hP : 0 < probeCutoff D m i := hN.trans hlt
  have hlen := SupportedSectors.vacuum_positive_window_length D Sc m cutoff bound ΛP ΛR
    hcP hcR i
  have hh : 0 ≤ D.h i ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR).wt
      ((0, 0) : Sector I)) := by
    rw [SupportedSectors.vacuum_height_eq D Sc m cutoff bound ΛP ΛR hcP hcR i]
    omega
  have hex := vacuumCapInverse_native_odd D Sc m cutoff bound ΛP ΛR hcP hcR
    (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) sy hc i
    (SupportedSectors.tensorVacuum D Sc m cutoff L ΛP ΛR)
    (tensorSectorInput_eq_supported D Sc m cutoff L ΛR ΛP hcP hcR).symm hP hi hh
  rw [show vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR
      (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) = H from
    tensorOutputAt_empty D (parameterTwist D Sc) m cutoff L ΛR, hlen] at hex
  obtain ⟨j, A, hA⟩ := hex
  have hhN : probeCutoff D m i - cutoff i + cutoff i = 2 * m i := by
    rw [← odd_probeCutoff D m i hi]
    omega
  exact ⟨j, A, hA, fun s z =>
    tensorVacuumCapInverse_odd_moments D (parameterTwist D Sc) m cutoff L sy
      (parameterTwist_homogeneous D Sc hc) i hi hP hN _ (by omega) hhN j A hA s z⟩

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
