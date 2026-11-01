import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalLongCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputKernel

/-! # The chronological kernel of off-diagonal long extraction

The arbitrary-old-Hom form of DeformedMackeyBoundary (2). The actual finite
row on Target(i,v,t++[i]) has precisely the chronological short span as its
kernel, including empty old Homs and full polynomial/exterior coefficients.
No field, flatness, or action hypothesis is introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Rebasing retains the long shuffle, including its source-length transport. -/
theorem longHomIndex_shuffle (i : I) {v t : List I} (y : NFIdx v t) (m : ℕ) :
    (longHomIndex i y m).1.2.2.2 = longPrependShuffle v.length := by
  have hl : v.length = t.length := by
    have hh := congrArg List.length y.tgt_cw
    simpa only [length_tgt] using hh
  have transport {n m : ℕ} (h : n = m) :
      (h.symm ▸ longPrependShuffle m : PrependShuffle n) = longPrependShuffle n := by
    cases h
    rfl
  change (hl.symm ▸ longPrependShuffle t.length : PrependShuffle v.length) =
    longPrependShuffle v.length
  exact transport hl

/-- A long shuffle ending at t++[i] has the actual old target t. -/
theorem oldTarget_eq_of_long_shuffle {i : I} {v t : List I}
    (x : PrependIdx i v (t ++ [i]))
    (hx : x.1.2.2.2 = longPrependShuffle v.length) : x.oldTarget = t := by
  have hl : x.oldTarget.length = v.length := by simp [PrependIdx.oldTarget]
  have he := congrArg Subtype.val
    (prependShuffleTarget_long i (⟨x.oldTarget, hl⟩ : Word I v.length))
  change tgt (i :: x.oldTarget)
      (cw (canWord (v.length + 1) (longPrependShuffle v.length).1⁻¹)) =
    x.oldTarget ++ [i] at he
  have hm := x.moving_target
  rw [hx] at hm
  exact List.append_cancel_right (he.symm.trans hm)

private theorem offDiagonalSameTailCoordinate (p : ZMod 2) {i : I} {v w : List I}
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

private theorem offDiagonalCastCoordinateZero (i : I) (v w t t' : List I) (e : t = t')
    (f : Target D Sc cutoff i v w →ₗ[k] Old D Sc cutoff v t)
    (z : Target D Sc cutoff i v w) (hz : f z = 0) :
    (Eq.mp (congrArg (fun t => Target D Sc cutoff i v w →ₗ[k]
      Old D Sc cutoff v t) e) f) z = 0 := by
  cases e
  exact hz

theorem longHomExtraction_chronological_generator (p : ZMod 2) (i : I)
    {v t : List I} (y : NFIdx v t) (s : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (h : hom D Sc cutoff (i :: s) t) :
    longHomExtraction D Sc cutoff p i y
      (projection D Sc cutoff i v (t ++ [i])
        (insert D Sc cutoff i v (s ++ [i]) r ≫
          rightContext D Sc cutoff [i] (i :: s) t h)) = 0 := by
  ext m
  rw [longHomExtraction_apply, Finsupp.zero_apply]
  unfold longHomCoordinate
  apply offDiagonalCastCoordinateZero D Sc cutoff i v (t ++ [i]) _ t
    (longHomIndex_oldTarget i y m)
  rw [LinearMap.smul_apply, prependOldCoordinate_projection]
  change _ • (ideal D Sc cutoff v (longHomIndex i y m).oldTarget).mkQ
    (prependExtractOld D Sc cutoff p (longHomIndex i y m) _) = 0
  rw [chronological_prependExtractOld_zero D Sc cutoff p r h
    (longHomIndex i y m) (longHomIndex_shuffle i y m), map_zero, smul_zero]

theorem chronologicalShortSpan_le_ker_longHomExtraction (p : ZMod 2) (i : I)
    {v t : List I} (y : NFIdx v t) :
    chronologicalShortSpan D Sc cutoff i v t ≤
      LinearMap.ker (longHomExtraction D Sc cutoff p i y) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, r, h, rfl⟩
  exact longHomExtraction_chronological_generator D Sc cutoff p i y s r h

/-- The finite row has exactly the prescribed chronological short kernel. -/
theorem ker_longHomExtraction_eq_chronologicalShortSpan
    (p : ZMod 2) (i : I) {v t : List I} (y : NFIdx v t) :
    LinearMap.ker (longHomExtraction D Sc cutoff p i y) =
      chronologicalShortSpan D Sc cutoff i v t := by
  apply le_antisymm
  · intro z hz
    change longHomExtraction D Sc cutoff p i y z = 0 at hz
    have hl (m : ℕ) : prependOldCoordinate D Sc cutoff p (longHomIndex i y m) z = 0 := by
      have hm := congrArg (fun f : ℕ →₀ Old D Sc cutoff v t => f m) hz
      change longHomCoordinate D Sc cutoff p i y m z = 0 at hm
      have uncast (s s' : List I) (e : s = s')
          (f : Target D Sc cutoff i v (t ++ [i]) →ₗ[k] Old D Sc cutoff v s)
          (h : (Eq.mp (congrArg (fun s => Target D Sc cutoff i v (t ++ [i]) →ₗ[k]
            Old D Sc cutoff v s) e) f) z = 0) : f z = 0 := by
        subst s'
        exact h
      have hs := uncast _ _ (longHomIndex_oldTarget i y m) _ hm
      change (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m •
        prependOldCoordinate D Sc cutoff p (longHomIndex i y m) z = 0 at hs
      have hs' := congrArg
        (fun a : Old D Sc cutoff v (longHomIndex i y m).oldTarget =>
          (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m • a) hs
      simpa only [smul_smul, ← mul_pow, SKM.zsign_mul_self', one_pow, one_smul,
        smul_zero] using hs'
    let f := prependOldCoordinateEquiv D Sc cutoff p i v (t ++ [i]) z
    have hterm (q : PrependIdx.Tail i v (t ++ [i])) :
        pair D Sc cutoff p i
          ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
            prependTail D Sc q.representative) (f q) ∈
          chronologicalShortSpan D Sc cutoff i v t := by
      by_cases hq : q.representative.1.2.2.2 = longPrependShuffle v.length
      · have hk : q.representative.tailKey =
            (longHomIndex i y q.representative.1.1).tailKey :=
          Prod.ext rfl (hq.trans (longHomIndex_shuffle i y _).symm)
        have he := offDiagonalSameTailCoordinate D Sc cutoff p q.representative
          (longHomIndex i y q.representative.1.1) hk z
        have zero_heq (s s' : List I) (e : s = s') :
            HEq (0 : Old D Sc cutoff v s) (0 : Old D Sc cutoff v s') := by
          subst s'
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
        exact prepend_short_mem D Sc cutoff i v t q.representative hq (twist k p r)
    rw [← prependOldReconstruct_coordinateEquiv D Sc cutoff p i v (t ++ [i]) z]
    exact dfinsuppSumAddHom_mem _ f
      (fun q => (pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc q.representative)).toAddMonoidHom)
      (fun q _ => hterm q)
  · exact chronologicalShortSpan_le_ker_longHomExtraction D Sc cutoff p i y

/-- If the old normal forms are empty, reconstruction consists entirely of short tails. -/
theorem mem_chronologicalShortSpan_of_no_old_normal_form
    (p : ZMod 2) (i : I) (v t : List I) (h : ¬ Nonempty (NFIdx v t))
    (z : Target D Sc cutoff i v (t ++ [i])) :
    z ∈ chronologicalShortSpan D Sc cutoff i v t := by
  let f := prependOldCoordinateEquiv D Sc cutoff p i v (t ++ [i]) z
  have hterm (q : PrependIdx.Tail i v (t ++ [i])) :
      pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc q.representative) (f q) ∈
        chronologicalShortSpan D Sc cutoff i v t := by
    have hq : q.representative.1.2.2.2 ≠ longPrependShuffle v.length := by
      intro hlong
      exact h ⟨oldTarget_eq_of_long_shuffle q.representative hlong ▸ q.representative.old⟩
    obtain ⟨r, hr⟩ := (ideal D Sc cutoff v q.representative.oldTarget).mkQ_surjective (f q)
    rw [← hr]
    erw [pair_mk]
    exact prepend_short_mem D Sc cutoff i v t q.representative hq (twist k p r)
  rw [← prependOldReconstruct_coordinateEquiv D Sc cutoff p i v (t ++ [i]) z]
  exact dfinsuppSumAddHom_mem _ f
    (fun q => (pair D Sc cutoff p i
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        prependTail D Sc q.representative)).toAddMonoidHom)
    (fun q _ => hterm q)

/-- Unconditional arbitrary-old-Hom chronological kernel, with no chosen old index. -/
theorem ker_offDiagonalLongExtraction_eq_chronologicalShortSpan
    (p : ZMod 2) (i : I) (v t : List I) :
    LinearMap.ker (offDiagonalLongExtraction D Sc cutoff p i v t) =
      chronologicalShortSpan D Sc cutoff i v t := by
  by_cases h : Nonempty (NFIdx v t)
  · obtain ⟨y⟩ := h
    rw [offDiagonalLongExtraction_eq D Sc cutoff p i y]
    exact ker_longHomExtraction_eq_chronologicalShortSpan D Sc cutoff p i y
  · rw [offDiagonalLongExtraction, dite_eq_right h, LinearMap.ker_zero]
    apply le_antisymm
    · intro z _
      exact mem_chronologicalShortSpan_of_no_old_normal_form D Sc cutoff p i v t h z
    · exact le_top

end OddMath.QuiverHecke.ELVOld
