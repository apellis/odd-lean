/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.LongOutputDotTransport
import OddMath.QuiverHecke.CyclotomicAction.ELVPrependCoordinates

/-!
# Full-coefficient long coordinates of output dots

The signed output-to-input dot transport gives a triangular comparison for the
bare long moving crossing, retaining arbitrary exterior coefficients over `k`.
The last-output-dot specialization evaluates its sign and input position.
These are affine PBW coefficients, not a descended Mackey extraction: transport
of arbitrary output-old arrows and the short-image inclusion remain necessary
for `DeformedMackeyBoundary.md` (2) and (5).
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The full coefficient long coordinate annihilates lower crossing errors. -/
theorem prependAffineEquiv_long_low (i : I) (s t : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (f : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t))
    (hf : f ∈ Low D Sc (i :: s) t s.length)
    (x : PrependIdx i s t) (hx : x.1.2.2.2 = longPrependShuffle s.length) :
    prependAffineEquiv D Sc cutoff i s t (a ⊗ₜ[k] f) x = 0 := by
  rw [prependAffineEquiv_tmul,
    prependBasis_long_repr_eq_zero_of_low D Sc i s t f hf x hx, zero_smul]

/-- Output dots on the long crossing have the signed input coordinates,
with the full exterior coefficient retained over the ground ring. -/
theorem prependAffineEquiv_long_output_dots (i : I) (s t : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (ps : List ℕ) (hp : ∀ p ∈ ps, p < s.length + 1)
    (h : SChain (i :: s)
      (pl (i :: s) (cw (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹) ++
        ps.map PG.dot)) t) :
    ∃ h' : SChain (i :: s)
      (pl (i :: s) ((ps.map (sourceDotPosition
        (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹))).map PG.dot ++
        cw (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹))) t,
      ∀ (x : PrependIdx i s t), x.1.2.2.2 = longPrependShuffle s.length →
      prependAffineEquiv D Sc cutoff i s t
        (a ⊗ₜ[k] cl D Sc _ _ _ h) x =
      sourceDotsSign D (k := k) (i :: s)
        (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹) ps •
      prependAffineEquiv D Sc cutoff i s t
        (a ⊗ₜ[k] cl D Sc _ _ _ h') x := by
  obtain ⟨h', he⟩ := dots_down_signed D Sc [] (show (i :: s).length = s.length + 1 from rfl)
    (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹)
    (validWord_canWord _ _) ps hp [] (by simpa using h)
  simp only [List.nil_append, List.append_nil, tgt_nil, crossCount_nil,
    Nat.zero_add, Nat.add_zero, length_canWord, length_inv,
    length_longPrependShuffle] at he h'
  refine ⟨h', ?_⟩
  intro x hx
  have hz := prependBasis_long_repr_eq_zero_of_low D Sc i s t _ he x hx
  simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
    smul_eq_mul] at hz
  rw [sub_eq_zero] at hz
  rw [prependAffineEquiv_tmul, prependAffineEquiv_tmul, hz, mul_smul]
/-- The actual last-output-dot monomial has the evaluated moving parity sign.
No dot on the first input has been substituted in the left-hand side. -/
theorem prependAffineEquiv_long_last_dots (i : I) (s t : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (m : ℕ)
    (h : SChain (i :: s)
      (pl (i :: s) (cw (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹) ++
        (List.replicate m s.length).map PG.dot)) t) :
    ∃ h' : SChain (i :: s)
      (pl (i :: s) ((List.replicate m 0).map PG.dot ++
        cw (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹))) t,
      ∀ (x : PrependIdx i s t), x.1.2.2.2 = longPrependShuffle s.length →
      prependAffineEquiv D Sc cutoff i s t
        (a ⊗ₜ[k] cl D Sc _ _ _ h) x =
      (SKM.zsign k (D.parity i * wordSumParity D s)) ^ m •
      prependAffineEquiv D Sc cutoff i s t
        (a ⊗ₜ[k] cl D Sc _ _ _ h') x := by
  have hp : ∀ p ∈ List.replicate m s.length, p < s.length + 1 := by
    intro p hp
    have he : p = s.length := (List.mem_replicate.mp hp).2
    omega
  obtain ⟨h', he⟩ := prependAffineEquiv_long_output_dots D Sc cutoff i s t a
    (List.replicate m s.length) hp h
  simpa only [List.map_replicate, sourceDotPosition_longPrependShuffle_last,
    sourceDotsSign, sourceDotSign_longPrependShuffle_last, List.prod_replicate] using
    (show ∃ h', ∀ (x : PrependIdx i s t), x.1.2.2.2 = longPrependShuffle s.length →
      prependAffineEquiv D Sc cutoff i s t (a ⊗ₜ[k] cl D Sc _ _ _ h) x =
        sourceDotsSign D (k := k) (i :: s)
          (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹)
          (List.replicate m s.length) •
        prependAffineEquiv D Sc cutoff i s t (a ⊗ₜ[k] cl D Sc _ _ _ h') x from ⟨h', he⟩)

end OddMath.QuiverHecke.ELVOld
