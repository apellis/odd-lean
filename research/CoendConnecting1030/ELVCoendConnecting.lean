/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVSourcePolynomialQuotient
import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicCrossCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryPolynomial

/-! # Connecting map for the prescribed balanced columns

The connecting map in the Mackey boundary diagram takes values in the independently
balanced cyclotomic coend. Its recovery and injectivity use the crossing decoder,
the corrected long section, and injectivity of P, without a snake lemma hypothesis.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The section-defined row agrees with the odd boundary when the moving colour is odd. -/
theorem evenPolynomialBoundary_eq_odd (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) :
    evenPolynomialBoundary D Sc cutoff p j.1 v = outputPolynomialBoundary D Sc cutoff p j v := by
  apply LinearMap.ext
  intro f
  change appendC0 D Sc cutoff j.1 v v
    (pMap D Sc cutoff j.1 v (v ++ [j.1]) (outputLongSection D Sc cutoff p j.1 v f)) = _
  rw [appendC0_pMap, outputLongExtraction_section]

/-- Correcting the long section does not change its polynomial P row. -/
theorem appendC0_pMap_sourceLongSection (p : ZMod 2) (i : I) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    appendC0 D Sc cutoff i v v
      (pMap D Sc cutoff i v (v ++ [i]) (sourceLongSection D Sc cutoff p i v f)) =
        evenPolynomialBoundary D Sc cutoff p i v f := by
  rw [evenPolynomialBoundary_factor, outputLongExtraction_sourceLongSection]

/-- Recovery in the crossing column on its proved kernel, for every append class. -/
theorem shortCross_decode_of_appendC0_eq_zero (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i]))
    (hz : appendC0 D Sc cutoff i v t z = 0) :
    shortCross D Sc cutoff i v t (ShortCrossCoordinates.decode D Sc cutoff i v t z) = z := by
  have h : z ∈ LinearMap.range (shortCross D Sc cutoff i v t) := by
    rw [ShortCrossCoordinates.range_shortCross, ← appendC0_ker]
    exact hz
  obtain ⟨a, rfl⟩ := h
  rw [ShortCrossCoordinates.decode_shortCross]

/-- The concrete connecting map into the independently prescribed cyclotomic coend. -/
def coendConnecting (p : ZMod 2) (i : I) (v : List I) :
    LinearMap.ker (evenPolynomialBoundary D Sc cutoff p i v) →ₗ[k] Source D Sc cutoff i v v :=
  q D Sc cutoff i v v ∘ₗ ShortCrossCoordinates.decode D Sc cutoff i v v ∘ₗ
    pMap D Sc cutoff i v (v ++ [i]) ∘ₗ sourceLongSection D Sc cutoff p i v ∘ₗ
      (LinearMap.ker (evenPolynomialBoundary D Sc cutoff p i v)).subtype

/-- The decoded short representative recovers P of the corrected long section. -/
theorem coendConnecting_recovery (p : ZMod 2) (i : I) (v : List I)
    (f : LinearMap.ker (evenPolynomialBoundary D Sc cutoff p i v)) :
    shortCross D Sc cutoff i v v (ShortCrossCoordinates.decode D Sc cutoff i v v
      (pMap D Sc cutoff i v (v ++ [i]) (sourceLongSection D Sc cutoff p i v f.1))) =
        pMap D Sc cutoff i v (v ++ [i]) (sourceLongSection D Sc cutoff p i v f.1) := by
  apply shortCross_decode_of_appendC0_eq_zero
  rw [appendC0_pMap_sourceLongSection]
  exact f.2

/-- No connecting-isomorphism or exactness premise is required for injectivity. -/
theorem coendConnecting_injective (p : ZMod 2) (i : I) (v : List I) :
    Function.Injective (coendConnecting D Sc cutoff p i v) := by
  apply (LinearMap.ker_eq_bot (f := coendConnecting D Sc cutoff p i v)).mp
  apply le_antisymm
  · intro f hf
    have hq : ShortCrossCoordinates.decode D Sc cutoff i v v
        (pMap D Sc cutoff i v (v ++ [i]) (sourceLongSection D Sc cutoff p i v f.1)) ∈
        LinearMap.ker (q D Sc cutoff i v v) := hf
    rw [← range_pprime_eq_ker_q] at hq
    obtain ⟨a, ha⟩ := hq
    have hp := congrArg (shortCross D Sc cutoff i v v) ha
    rw [coendConnecting_recovery] at hp
    have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff i v v) a
    have he := pMap_injective D Sc cutoff i v (v ++ [i]) (hs.trans hp)
    have hb := congrArg (outputLongExtraction D Sc cutoff p i v) he
    rw [outputLongExtraction_alpha, outputLongExtraction_sourceLongSection] at hb
    exact (Submodule.mem_bot k).mpr (Subtype.ext hb.symm)
  · exact bot_le

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
