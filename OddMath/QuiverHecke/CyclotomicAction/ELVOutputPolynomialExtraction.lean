/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputLongExtraction

/-!
# Finite normalized long-coordinate extraction

`outputLongExtraction` assembles the prescribed long coordinate functionals into
an actual finitely supported polynomial row over the old quotient, as required
for `DeformedMackeyBoundary.md` (2). Finite support is proved from the affine
PBW support of an arbitrary quotient representative, not assumed.

The coefficients retain the evaluated bare-long last-output-dot normalization.
Arbitrary output-old-arrow triangularity, the relative-short kernel, moving-chain
S evaluation and corrected-rho compatibility remain separate obligations.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem castCoordinate_zero (i : I) (v w t t' : List I) (e : t = t')
    (f : Target D Sc cutoff i v w →ₗ[k] Old D Sc cutoff v t)
    (z : Target D Sc cutoff i v w) (hz : f z = 0) :
    (Eq.mp (congrArg (fun t => Target D Sc cutoff i v w →ₗ[k]
      Old D Sc cutoff v t) e) f) z = 0 := by
  cases e
  exact hz

theorem outputLongCoordinate_finite_support (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) :
    ∃ N : ℕ, ∀ m, N ≤ m → outputLongCoordinate D Sc cutoff p i v m z = 0 := by
  obtain ⟨f, rfl⟩ := projection_surjective D Sc cutoff i v (v ++ [i]) z
  let c := prependAffineEquiv D Sc cutoff i v (v ++ [i]) f
  refine ⟨c.support.sup (fun x => x.1.1) + 1, ?_⟩
  intro m hm
  unfold outputLongCoordinate
  apply castCoordinate_zero D Sc cutoff i v (v ++ [i]) _ v
    (longOutputIndex_oldTarget i v m)
  rw [LinearMap.smul_apply]
  suffices hz : prependOldCoordinate D Sc cutoff p (longOutputIndex i v m)
      (projection D Sc cutoff i v (v ++ [i]) f) = 0 by rw [hz, smul_zero]
  rw [prependOldCoordinate_projection]
  have he : Finsupp.lcomapDomain (R := k) (longOutputIndex i v m).replaceOld
      (longOutputIndex i v m).replaceOld_injective c = 0 := by
    ext y
    simp only [Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply, Finsupp.zero_apply]
    apply Finsupp.notMem_support_iff.mp
    intro hy
    have hd := Finset.le_sup (f := fun x : PrependIdx i v (v ++ [i]) => x.1.1) hy
    have hdegree : ((longOutputIndex i v m).replaceOld y).1.1 = m := rfl
    rw [hdegree] at hd
    omega
  change (ideal D Sc cutoff v (longOutputIndex i v m).oldTarget).mkQ
    (prependExtractOld D Sc cutoff p (longOutputIndex i v m) f) = 0
  unfold prependExtractOld
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  change (ideal D Sc cutoff v (longOutputIndex i v m).oldTarget).mkQ
    ((twist k p) ((oldAffineEquiv D Sc cutoff v (longOutputIndex i v m).oldTarget).symm
      ((Finsupp.mapRange.linearMap (coefficientTwist D cutoff
        (prependTailParity D (longOutputIndex i v m))))
        (Finsupp.lcomapDomain (R := k) (longOutputIndex i v m).replaceOld
          (longOutputIndex i v m).replaceOld_injective c)))) = 0
  rw [he, map_zero, map_zero, map_zero, map_zero]
/-- All prescribed normalized long coefficients, as a finite polynomial row. -/
def outputLongExtraction (p : ZMod 2) (i : I) (v : List I) :
    Target D Sc cutoff i v (v ++ [i]) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) where
  toFun z := Finsupp.ofSupportFinite
    (fun m => outputLongCoordinate D Sc cutoff p i v m z) (by
      obtain ⟨N, hN⟩ := outputLongCoordinate_finite_support D Sc cutoff p i v z
      apply (Finset.finite_toSet (Finset.range N)).subset
      intro m hm
      simp only [Finset.mem_coe, Finset.mem_range]
      by_contra h
      exact hm (hN m (by omega)))
  map_add' z z' := by
    ext m
    exact (outputLongCoordinate D Sc cutoff p i v m).map_add z z'
  map_smul' c z := by
    ext m
    exact (outputLongCoordinate D Sc cutoff p i v m).map_smul c z

@[simp] theorem outputLongExtraction_apply (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) (m : ℕ) :
    outputLongExtraction D Sc cutoff p i v z m =
      outputLongCoordinate D Sc cutoff p i v m z := rfl

end OddMath.QuiverHecke.ELVOld
