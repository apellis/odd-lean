/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.SmallerTailNormalization
import OddMath.QuiverHecke.CyclotomicAction.ELVChronologicalShort
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputPolynomialExtraction

/-!
# Full-ELV chronological short kernel

`chronologicalShortSpan_le_ker_outputLongExtraction` proves the short-to-kernel
containment for the actual finite extractor on `Target`. Homogeneous tensor
induction lifts smaller-tail scalar normalization with the full Koszul sign.
All exterior coefficients and arbitrary total balance parity are retained.
This supplies one inclusion in `DeformedMackeyBoundary.md` (2), not equality of
the kernel with the short span, a canonical splitting, or the boundary S formula.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem chronological_induction {v w : List I}
    {P : hom D Sc cutoff v w → Prop} (x : hom D Sc cutoff v w) (zero : P 0)
    (tmul : ∀ (p q : ZMod 2) (a : (obj D Sc cutoff v).fst ⟶ (obj D Sc cutoff w).fst)
      (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)),
      a ∈ parity (R := k) _ _ p → f ∈ parity (R := k) _ _ q → P (BoxProd.tmulHom a f))
    (add : ∀ x y, P x → P y → P (x + y)) : P x :=
  BoxProd.induction_on_homogeneous (P := P) x zero tmul add

/-- Every long affine coordinate vanishes on chronological short generators,
with unrestricted full ELV coefficients. -/
theorem chronological_long_zero {i j : I} {v s t : List I}
    (r : hom D Sc cutoff v (s ++ [j])) (h : hom D Sc cutoff (i :: s) t)
    (x : PrependIdx i v (t ++ [j]))
    (hx : x.1.2.2.2 = longPrependShuffle v.length) :
    prependAffineEquiv D Sc cutoff i v (t ++ [j])
      (insert D Sc cutoff i v (s ++ [j]) r ≫
        rightContext D Sc cutoff [j] (i :: s) t h) x = 0 := by
  induction r using chronological_induction D Sc cutoff with
  | zero => simp only [map_zero, Limits.zero_comp, Finsupp.zero_apply]
  | add r r' hr hr' =>
    simp only [map_add, Preadditive.add_comp, Finsupp.add_apply, hr, hr', add_zero]
  | tmul p q a f ha hf =>
    induction h using chronological_induction D Sc cutoff with
    | zero => simp only [map_zero, Limits.comp_zero, Finsupp.zero_apply]
    | add h h' hh hh' =>
      simp only [map_add, Preadditive.comp_add, Finsupp.add_apply, hh, hh', add_zero]
    | tmul r z b g hb hg =>
      have hi : affineRightContext D Sc [j] (i :: s) t g ∈ parity (R := k) _ _ z :=
        MonoidalSupercategory.whiskerRight_mem ((pres D Sc).obj (ob D [j])) hg
      change prependAffineEquiv D Sc cutoff i v (t ++ [j])
        (BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
          (Y := obj D Sc cutoff (i :: (s ++ [j]))) a (affineInsert D Sc i v (s ++ [j]) f) ≫
        BoxProd.tmulHom (X := obj D Sc cutoff (i :: (s ++ [j])))
          (Y := obj D Sc cutoff (t ++ [j])) b (affineRightContext D Sc [j] (i :: s) t g)) x = 0
      erw [BoxProd.tmulHom_comp_tmulHom
        (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: (s ++ [j])))
        (Z := obj D Sc cutoff (t ++ [j])) ha _ b hi]
      rw [map_zsmul]
      change koszulSign p z • (prependAffineEquiv D Sc cutoff i v (t ++ [j])
        (_ ⊗ₜ[k] (affineInsert D Sc i v (s ++ [j]) f ≫
          (g ▷ (pres D Sc).obj (ob D [j])))) x) = 0
      erw [prependAffineEquiv_tmul]
      erw [SmallerTailNormalization.chronological_scalar_long_zero D Sc f g x hx]
      simp only [zero_smul]
      exact zsmul_zero _

/-- Total-parity-normalized extraction vanishes before taking the old quotient. -/
theorem chronological_prependExtractOld_zero (p : ZMod 2) {i j : I} {v s t : List I}
    (r : hom D Sc cutoff v (s ++ [j])) (h : hom D Sc cutoff (i :: s) t)
    (x : PrependIdx i v (t ++ [j]))
    (hx : x.1.2.2.2 = longPrependShuffle v.length) :
    prependExtractOld D Sc cutoff p x
      (insert D Sc cutoff i v (s ++ [j]) r ≫
        rightContext D Sc cutoff [j] (i :: s) t h) = 0 := by
  have he := prependExtractOld_congr_long D Sc cutoff p x hx
    (insert D Sc cutoff i v (s ++ [j]) r ≫
      rightContext D Sc cutoff [j] (i :: s) t h) 0 (by
        intro y hy
        rw [chronological_long_zero D Sc cutoff r h y hy, map_zero, Finsupp.zero_apply])
  simpa only [map_zero] using he

private theorem chronological_cast_zero (i : I) (v w t t' : List I) (e : t = t')
    (f : Target D Sc cutoff i v w →ₗ[k] Old D Sc cutoff v t)
    (z : Target D Sc cutoff i v w) (hz : f z = 0) :
    (Eq.mp (congrArg (fun t => Target D Sc cutoff i v w →ₗ[k]
      Old D Sc cutoff v t) e) f) z = 0 := by
  cases e
  exact hz

/-- The actual finite normalized long extraction kills each full-coefficient
chronological short generator. -/
theorem outputLongExtraction_chronological_generator (p : ZMod 2) (i : I)
    (v s : List I) (r : hom D Sc cutoff v (s ++ [i]))
    (h : hom D Sc cutoff (i :: s) v) :
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i])
        (insert D Sc cutoff i v (s ++ [i]) r ≫
          rightContext D Sc cutoff [i] (i :: s) v h)) = 0 := by
  ext m
  rw [outputLongExtraction_apply, Finsupp.zero_apply]
  unfold outputLongCoordinate
  apply chronological_cast_zero D Sc cutoff i v (v ++ [i]) _ v
    (longOutputIndex_oldTarget i v m)
  rw [LinearMap.smul_apply, prependOldCoordinate_projection]
  change _ • (ideal D Sc cutoff v (longOutputIndex i v m).oldTarget).mkQ
    (prependExtractOld D Sc cutoff p (longOutputIndex i v m) _) = 0
  rw [chronological_prependExtractOld_zero D Sc cutoff p r h
    (longOutputIndex i v m) rfl, map_zero, smul_zero]

/-- Unconditional containment in the kernel of the actual finite extraction map. -/
theorem chronologicalShortSpan_le_ker_outputLongExtraction (p : ZMod 2) (i : I)
    (v : List I) :
    chronologicalShortSpan D Sc cutoff i v v ≤
      LinearMap.ker (outputLongExtraction D Sc cutoff p i v) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, r, h, rfl⟩
  exact outputLongExtraction_chronological_generator D Sc cutoff p i v s r h

end OddMath.QuiverHecke.ELVOld
