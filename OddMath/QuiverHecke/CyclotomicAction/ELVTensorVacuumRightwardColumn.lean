/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumCapMoments

/-! # The rightward unit columns of the tensor vacuum

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8.

For a family `B` of maps into the tensor vacuum value `V`, the unit column
`η ≫ xᵉ ≫ B n : V ⟶ V` (`rightwardUnitColumn`) is the product of the native unit row
`η xᵉ` of the cup window with the `n`-th column of `B`. For an entrywise inverse
`(j, B)` of the cup window at an odd colour with `0 < 2 M < N`, the last unit column
has the decoded moments of `tensorVacuumNegativeCap_odd_moments_even/odd`
(`rightwardUnitColumn_odd_moments`). The column is named so that statements made with
other hom-category instances refer to this one composite.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor PowerVacuumCoefficient ProbeVacuumCap
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (m : I → ℕ) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "W₀" => Functor.obj (restriction (contentInclusion D Sc cutoff bound (0 : Multiset I)))
  (weightedVacuum D Sc cutoff L)
local notation "H" => VacuumTensor.probeFunctor D Sc m cutoff bound W₀
local notation "R₀" => contentModuleTarget D Sc cutoff bound (0 : Multiset I)
local notation "N₀" => probeOldVacuumRegular D Sc m
local notation "V" => Superfunctor.obj H N₀
local notation "star" => (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff bound 0)

variable (i : I)

local notation "K" => contentAppend D Sc cutoff bound (0 : Multiset I) [i]

/-- The unit column `u ≫ xᵉ ≫ B n` of a family `B` of maps out of the object of an
endomorphism `x`, for a unit `u` into that object. It is generic in its objects, so its
instances are never written out. -/
abbrev rightwardUnitColumn {C : Type*} {_ : Category C} {Y Z : C} (u : Y ⟶ Z) (x : End Z)
    {w : ℕ} (B : Fin w → (Z ⟶ Y)) (e : ℕ) (n : Fin w) : Y ⟶ Y :=
  u ≫ (x ^ e) ≫ B n

include sy hc in
/-- **Odd colour, negative height: even moments of the last unit column.** For an
entrywise inverse `(j, B)` of the cup window of the A6 bend with `0 < 2 M < N`, the shift
`N - 2M - 1 + 2r` of the last unit column decodes to multiplication by the `r`-th
coefficient of `(1 + w)^M / C(-w)`. -/
theorem rightwardUnitColumn_odd_moments_even
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V))
    (hB : SwappedAssembly.ProbeWindow.IsCupInverse
      (evaluatedMixedBend D Sc m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n.val))
      j B)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((rightwardUnitColumn ((adjunction K).unit.app V)
          (evaluatedPostDot D Sc m cutoff bound i H) B (cutoff i - 2 * m i - 1 + 2 * r)
          ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z :=
  tensorVacuumNegativeCap_odd_moments_even D Sc m cutoff L sy hc i hi hP
    (Nat.pos_of_ne_zero (by omega)) hPN j B hB r z

include sy hc in
/-- **Odd colour, negative height: odd moments of the last unit column.** Under the
hypotheses of `rightwardUnitColumn_odd_moments_even`, the shift `N - 2M - 1 + (2r + 1)`
decodes to the `r`-th coefficient of `(1 + w)^M / C(-w)` times the normalized odd
coefficient `(-1)^(N+1) δ`. -/
theorem rightwardUnitColumn_odd_moments_odd
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V))
    (hB : SwappedAssembly.ProbeWindow.IsCupInverse
      (evaluatedMixedBend D Sc m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n.val))
      j B)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((rightwardUnitColumn ((adjunction K).unit.app V)
          (evaluatedPostDot D Sc m cutoff bound i H) B (cutoff i - 2 * m i - 1 + (2 * r + 1))
          ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z) =
      coefficientPowerQuotientMap D cutoff L
          ((-1 : k) ^ (cutoff i + 1) • SKM.SYM.delta D k ⟨i, hi⟩) *
        (polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
          tensorVacuumDecodeLinear D Sc m cutoff L z) := by
  rw [map_smul]
  exact tensorVacuumNegativeCap_odd_moments_odd D Sc m cutoff L sy hc i hi hP
    (Nat.pos_of_ne_zero (by omega)) hPN j B hB r z

include sy hc in
/-- **Odd colour, negative height: the last unit column.** Both moment identities of
`rightwardUnitColumn_odd_moments_even` and `rightwardUnitColumn_odd_moments_odd`. -/
theorem rightwardUnitColumn_odd_moments
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V))
    (hB : SwappedAssembly.ProbeWindow.IsCupInverse
      (evaluatedMixedBend D Sc m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n.val))
      j B)
    (r : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((rightwardUnitColumn ((adjunction K).unit.app V)
          (evaluatedPostDot D Sc m cutoff bound i H) B (cutoff i - 2 * m i - 1 + 2 * r)
          ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z ∧
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((rightwardUnitColumn ((adjunction K).unit.app V)
          (evaluatedPostDot D Sc m cutoff bound i H) B (cutoff i - 2 * m i - 1 + (2 * r + 1))
          ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z) =
      coefficientPowerQuotientMap D cutoff L
          ((-1 : k) ^ (cutoff i + 1) • SKM.SYM.delta D k ⟨i, hi⟩) *
        (polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
          tensorVacuumDecodeLinear D Sc m cutoff L z) :=
  ⟨rightwardUnitColumn_odd_moments_even D Sc m cutoff L sy hc i hi hP hPN j B hB r z,
    rightwardUnitColumn_odd_moments_odd D Sc m cutoff L sy hc i hi hP hPN j B hB r z⟩

/-- The decoded value of the last unit column `η xᵉ ≫ B (N - 2M - 1)` at shift `e`. -/
def rightwardLastColumnDecode (hPN : 2 * m i < cutoff i)
    (B : Fin (cutoff i - 2 * m i) → ((induction K ⋙ restriction K).obj V ⟶ V)) (e : ℕ) (z : (V).obj star) :
    CoefficientPowerQuotient (k := k) D cutoff L :=
  tensorVacuumDecodeLinear D Sc m cutoff L
    ((rightwardUnitColumn ((adjunction K).unit.app V)
      (evaluatedPostDot D Sc m cutoff bound i H) B e
      ⟨cutoff i - 2 * m i - 1, by omega⟩).total star z)

/-- The normalized odd coefficient `(-1)^(N+1) δ_i` in the coefficient power quotient. -/
def rightwardOddScalar (hi : D.parity i = 1) : CoefficientPowerQuotient (k := k) D cutoff L :=
  (-1 : k) ^ (cutoff i + 1) • coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)

include sy hc in
/-- `rightwardUnitColumn_odd_moments_even` for `rightwardLastColumnDecode`. -/
theorem rightwardLastColumnDecode_even
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V))
    (hB : SwappedAssembly.ProbeWindow.IsCupInverse
      (evaluatedMixedBend D Sc m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n.val))
      j B)
    (r : ℕ) (z : (V).obj star) :
    rightwardLastColumnDecode D Sc m cutoff L i hPN B (cutoff i - 2 * m i - 1 + 2 * r) z =
      polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z := by
  unfold rightwardLastColumnDecode
  exact tensorVacuumNegativeCap_odd_moments_even D Sc m cutoff L sy hc i hi hP
    (Nat.pos_of_ne_zero (by omega)) hPN j B hB r z

include sy hc in
/-- `rightwardUnitColumn_odd_moments_odd` for `rightwardLastColumnDecode`. -/
theorem rightwardLastColumnDecode_odd
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i) (hPN : 2 * m i < cutoff i)
    (j : _ ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (B : Fin (cutoff i - 2 * m i) → (_ ⟶ V))
    (hB : SwappedAssembly.ProbeWindow.IsCupInverse
      (evaluatedMixedBend D Sc m cutoff bound i hP H)
      (fun n => (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ n.val))
      j B)
    (r : ℕ) (z : (V).obj star) :
    rightwardLastColumnDecode D Sc m cutoff L i hPN B (cutoff i - 2 * m i - 1 + (2 * r + 1)) z =
      rightwardOddScalar D cutoff L i hi *
        (polynomialToPower D cutoff L (PowerSeries.coeff r
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)) *
          tensorVacuumDecodeLinear D Sc m cutoff L z) := by
  unfold rightwardLastColumnDecode rightwardOddScalar
  exact tensorVacuumNegativeCap_odd_moments_odd D Sc m cutoff L sy hc i hi hP
    (Nat.pos_of_ne_zero (by omega)) hPN j B hB r z

end OddMath.QuiverHecke.ELVOld
