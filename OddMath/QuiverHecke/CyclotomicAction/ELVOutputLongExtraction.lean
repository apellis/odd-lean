/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputDotCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVPrependDescent

/-!
# Long output coordinate functionals on the old-only quotient

`outputLongCoordinate` is a prescribed ground-ring-linear functional on the
existing `Target`, obtained from old-quotient extraction and the evaluated
output-dot sign. `prependOldCoordinate_long_last_dots` descends the bare-long
output-dot comparison through the old-only relations, with full exterior
coefficients and arbitrary balance parity.

This is the coordinate-functional step toward `DeformedMackeyBoundary.md` (2).
Finite polynomial assembly, output-old-arrow transport, the relative short
kernel, corrected-rho intertwining and moving-chain extraction are not asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem prependExtractOld_congr_long (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (hx : x.1.2.2.2 = longPrependShuffle v.length)
    (f g : hom D Sc cutoff (i :: v) w)
    (h : ∀ y : PrependIdx i v w, y.1.2.2.2 = longPrependShuffle v.length →
      prependAffineEquiv D Sc cutoff i v w f y = prependAffineEquiv D Sc cutoff i v w g y) :
    prependExtractOld D Sc cutoff p x f = prependExtractOld D Sc cutoff p x g := by
  unfold prependExtractOld
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  congr 3
  ext y
  simp only [Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply]
  apply h
  exact hx

private theorem long_canWord_one (n : ℕ) : canWord n 1 = [] := by
  apply List.length_eq_zero_iff.mp
  rw [length_canWord, Categorification.TypeA.length_one]

def longOutputIndex (i : I) (v : List I) (m : ℕ) : PrependIdx i v (v ++ [i]) :=
  ⟨(m, [], 1, longPrependShuffle v.length), by simp, by simp, by
    simp only [prependCrossingWord, long_canWord_one, shiftWord, List.map_nil,
      List.append_nil]
    rw [canWord_longPrependShuffle]
    have hw := leadingMoveWord_eq_descRun ([] : List I) v
    simp only [List.length_nil] at hw
    rw [← hw]
    exact tgt_eq (leadingMoveWord_sChain i [] v)⟩

@[simp] theorem longOutputIndex_oldTarget (i : I) (v : List I) (m : ℕ) :
    (longOutputIndex i v m).oldTarget = v := by
  simp [longOutputIndex, PrependIdx.oldTarget, long_canWord_one, cw]

/-- One normalized long coordinate, on the old-only quotient itself. -/
def outputLongCoordinate (p : ZMod 2) (i : I) (v : List I) (m : ℕ) :
    Target D Sc cutoff i v (v ++ [i]) →ₗ[k] Old D Sc cutoff v v :=
  Eq.mp (congrArg (fun t => Target D Sc cutoff i v (v ++ [i]) →ₗ[k]
      Old D Sc cutoff v t) (longOutputIndex_oldTarget i v m))
    ((SKM.zsign k (D.parity i * wordSumParity D v)) ^ m •
      prependOldCoordinate D Sc cutoff p (longOutputIndex i v m))

/-- The output/input triangular comparison descends through the old-only relations. -/
theorem prependOldCoordinate_long_last_dots (p : ZMod 2) (i : I) (s t : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (m : ℕ)
    (h : SChain (i :: s)
      (pl (i :: s) (cw (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹) ++
        (List.replicate m s.length).map PG.dot)) t) :
    ∃ h' : SChain (i :: s)
      (pl (i :: s) ((List.replicate m 0).map PG.dot ++
        cw (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹))) t,
      ∀ (x : PrependIdx i s t), x.1.2.2.2 = longPrependShuffle s.length →
      prependOldCoordinate D Sc cutoff p x
        (projection D Sc cutoff i s t (a ⊗ₜ[k] cl D Sc _ _ _ h)) =
      (SKM.zsign k (D.parity i * wordSumParity D s)) ^ m •
      prependOldCoordinate D Sc cutoff p x
        (projection D Sc cutoff i s t (a ⊗ₜ[k] cl D Sc _ _ _ h')) := by
  obtain ⟨h', he⟩ := prependAffineEquiv_long_last_dots D Sc cutoff i s t a m h
  refine ⟨h', ?_⟩
  intro x hx
  let f : hom D Sc cutoff (i :: s) t := a ⊗ₜ[k] cl D Sc _ _ _ h
  let g : hom D Sc cutoff (i :: s) t := a ⊗ₜ[k] cl D Sc _ _ _ h'
  let c : k := (SKM.zsign k (D.parity i * wordSumParity D s)) ^ m
  have hc := prependExtractOld_congr_long D Sc cutoff p x hx f (c • g) (by
    intro y hy
    rw [(prependAffineEquiv D Sc cutoff i s t).map_smul, Finsupp.smul_apply]
    exact he y hy)
  rw [(prependExtractOld D Sc cutoff p x).map_smul] at hc
  change (ideal D Sc cutoff s x.oldTarget).mkQ
      (prependExtractOld D Sc cutoff p x f) =
    c • (ideal D Sc cutoff s x.oldTarget).mkQ
      (prependExtractOld D Sc cutoff p x g)
  rw [hc, map_smul]

end OddMath.QuiverHecke.ELVOld
