/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVChronologicalKernel
import OddMath.QuiverHecke.CyclotomicAction.ELVShortTailSpan

/-!
# The chronological kernel of long output extraction

The finite old-quotient coordinate decomposition identifies the kernel with the
chronological short span, as required in `DeformedMackeyBoundary.md` (2).
All exterior coefficients, total balance parities and commutative ground rings
are retained. The S/rho and balanced output-order comparisons are separate.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem same_tail_coordinate (p : ZMod 2) {i : I} {v w : List I}
    (x y : PrependIdx i v w) (h : x.tailKey = y.tailKey)
    (z : Target D Sc cutoff i v w) :
    HEq (prependOldCoordinate D Sc cutoff p x z)
      (prependOldCoordinate D Sc cutoff p y z) := by
  obtain ⟨f, rfl⟩ := projection_surjective D Sc cutoff i v w z
  rw [prependOldCoordinate_projection, prependOldCoordinate_projection]
  have ht := x.oldTarget_eq_of_tailKey_eq y h
  have hn := congrArg Prod.fst h
  have hd := congrArg Prod.snd h
  change x.1.1 = y.1.1 at hn
  change x.1.2.2.2 = y.1.2.2.2 at hd
  have hp : prependTailParity D x = prependTailParity D y := by
    unfold prependTailParity
    rw [ht, hn, hd]
  have hr : HEq x.replaceOld y.replaceOld := by
    apply Function.hfunext (congrArg (NFIdx v) ht)
    intro a b hab
    apply heq_of_eq
    apply Subtype.ext
    have val_heq {t t' : List I} (e : t = t') (a : NFIdx v t) (b : NFIdx v t')
        (ha : HEq a b) : a.val = b.val := by
      subst t'
      cases ha
      rfl
    have hv := val_heq ht a b hab
    change (x.1.1, a.1.1, a.1.2, x.1.2.2.2) =
      (y.1.1, b.1.1, b.1.2, y.1.2.2.2)
    rw [hn, hd, show a.1.1 = b.1.1 from congrArg Prod.fst hv,
      show a.1.2 = b.1.2 from congrArg Prod.snd hv]
  have transport (t t' : List I) (e : t = t') (r r' : ZMod 2) (er : r = r')
      (a : NFIdx v t → PrependIdx i v w) (b : NFIdx v t' → PrependIdx i v w)
      (ha : Function.Injective a) (hb : Function.Injective b) (he : HEq a b) :
      HEq ((ideal D Sc cutoff v t).mkQ ((twist k p)
        ((oldAffineEquiv D Sc cutoff v t).symm
          ((Finsupp.mapRange.linearMap (coefficientTwist D cutoff r))
            ((Finsupp.lcomapDomain (R := k) a ha) (prependAffineEquiv D Sc cutoff i v w f))))))
        ((ideal D Sc cutoff v t').mkQ ((twist k p)
        ((oldAffineEquiv D Sc cutoff v t').symm
          ((Finsupp.mapRange.linearMap (coefficientTwist D cutoff r'))
            ((Finsupp.lcomapDomain (R := k) b hb) (prependAffineEquiv D Sc cutoff i v w f)))))) := by
    subst t'
    subst r'
    cases he
    rfl
  exact transport _ _ ht _ _ hp _ _ x.replaceOld_injective y.replaceOld_injective hr

theorem ker_outputLongExtraction_eq_chronologicalShortSpan
    (p : ZMod 2) (i : I) (v : List I) :
    LinearMap.ker (outputLongExtraction D Sc cutoff p i v) =
      chronologicalShortSpan D Sc cutoff i v v := by
  apply le_antisymm
  · intro z hz
    change outputLongExtraction D Sc cutoff p i v z = 0 at hz
    have hl (m : ℕ) : prependOldCoordinate D Sc cutoff p (longOutputIndex i v m) z = 0 := by
      have hm := congrArg (fun f : ℕ →₀ Old D Sc cutoff v v => f m) hz
      change outputLongCoordinate D Sc cutoff p i v m z = 0 at hm
      have uncast (t t' : List I) (e : t = t')
          (f : Target D Sc cutoff i v (v ++ [i]) →ₗ[k] Old D Sc cutoff v t)
          (h : (Eq.mp (congrArg (fun t => Target D Sc cutoff i v (v ++ [i]) →ₗ[k]
            Old D Sc cutoff v t) e) f) z = 0) : f z = 0 := by
        subst t'
        exact h
      have hs := uncast _ _ (longOutputIndex_oldTarget i v m) _ hm
      change (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m •
        prependOldCoordinate D Sc cutoff p (longOutputIndex i v m) z = 0 at hs
      have hs' := congrArg
        (fun a : Old D Sc cutoff v (longOutputIndex i v m).oldTarget =>
          (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m • a) hs
      simpa only [smul_smul, ← mul_pow, SKM.zsign_mul_self', one_pow, one_smul,
        smul_zero] using hs'
    let f := prependOldCoordinateEquiv D Sc cutoff p i v (v ++ [i]) z
    have hterm (q : PrependIdx.Tail i v (v ++ [i])) :
        pair D Sc cutoff p i
          ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
            prependTail D Sc q.representative) (f q) ∈
          chronologicalShortSpan D Sc cutoff i v v := by
      by_cases hq : q.representative.1.2.2.2 = longPrependShuffle v.length
      · have hk : q.representative.tailKey =
            (longOutputIndex i v q.representative.1.1).tailKey := Prod.ext rfl hq
        have he := same_tail_coordinate D Sc cutoff p q.representative
          (longOutputIndex i v q.representative.1.1) hk z
        have zero_heq (t t' : List I) (e : t = t') :
            HEq (0 : Old D Sc cutoff v t) (0 : Old D Sc cutoff v t') := by
          subst t'
          rfl
        have hc : f q = 0 := by
          rw [prependOldCoordinateEquiv_apply]
          apply eq_of_heq
          rw [hl] at he
          exact he.trans (zero_heq _ _
            (q.representative.oldTarget_eq_of_tailKey_eq _ hk).symm)
        rw [hc, map_zero]
        exact Submodule.zero_mem _
      · obtain ⟨r, hr⟩ := (ideal D Sc cutoff v q.representative.oldTarget).mkQ_surjective (f q)
        rw [← hr]
        erw [pair_mk]
        exact prepend_short_mem D Sc cutoff i v v q.representative hq (twist k p r)
    rw [← prependOldReconstruct_coordinateEquiv D Sc cutoff p i v (v ++ [i]) z]
    exact dfinsuppSumAddHom_mem _ f
      (fun q => (pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc q.representative)).toAddMonoidHom)
      (fun q _ => hterm q)
  · exact chronologicalShortSpan_le_ker_outputLongExtraction D Sc cutoff p i v

end OddMath.QuiverHecke.ELVOld
