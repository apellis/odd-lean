import OddMath.QuiverHecke.CyclotomicAction.ChronologicalTails.ChronologicalShort

/-!
# Output transport

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# Old source action on normalized output coordinates

The coefficient-linearity step toward `DeformedMackeyBoundary.md` (2).
Every old endomorphism acts on every extracted coefficient by old precomposition,
with the prescribed total-parity twist. Full ELV quotients are retained.
This does not yet identify the output balanced action or the boundary polynomial S.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem coordinate_pair_transport (p : ZMod 2) {i : I} {v w : List I}
    (x y : PrependIdx i v w) (e : x.oldTarget = y.oldTarget)
    (ht : HEq (prependTail D Sc x) (prependTail D Sc y))
    (b : Old D Sc cutoff v y.oldTarget) :
    prependOldCoordinate D Sc cutoff p x
      (pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc y) b) = e.symm ▸ b := by
  have transport {t t' : List I} (e : t = t')
      (f : (pres D Sc).obj (ob D (i :: t)) ⟶ (pres D Sc).obj (ob D w))
      (g : (pres D Sc).obj (ob D (i :: t')) ⟶ (pres D Sc).obj (ob D w))
      (hf : HEq f g) (b : Old D Sc cutoff v t') :
      pair D Sc cutoff p i ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] g) b =
      pair D Sc cutoff p i ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f) (e.symm ▸ b) := by
    subst t'
    cases hf
    rfl
  rw [transport e _ _ ht b, prependOldCoordinate_pair]

/-- Every old source endomorphism acts on the extracted old coefficient, with
its total-parity twist. No scalar or homogeneity restriction is imposed. -/
theorem prependOldCoordinate_oldSource (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (c : hom D Sc cutoff v v)
    (z : Target D Sc cutoff i v w) :
    prependOldCoordinate D Sc cutoff p x (oldSourceTarget D Sc cutoff i v w c z) =
      oldPrecomp D Sc cutoff v x.oldTarget (twist k p c)
        (prependOldCoordinate D Sc cutoff p x z) := by
  obtain ⟨f, rfl⟩ := prependOldReconstruct_surjective D Sc cutoff p i v w z
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | of q b =>
    change prependOldCoordinate D Sc cutoff p x
      (oldSourceTarget D Sc cutoff i v w c
        (prependOldReconstruct D Sc cutoff p i v w (DirectSum.lof k _ _ q b))) =
      oldPrecomp D Sc cutoff v x.oldTarget (twist k p c)
        (prependOldCoordinate D Sc cutoff p x
          (prependOldReconstruct D Sc cutoff p i v w (DirectSum.lof k _ _ q b)))
    rw [prependOldReconstruct, DirectSum.toModule_lof, oldSourceTarget_pair]
    by_cases h : x.tailKey = q.representative.tailKey
    · have e := x.oldTarget_eq_of_tailKey_eq q.representative h
      have ht := prependTail_heq_of_tailKey_eq D Sc x q.representative h
      rw [coordinate_pair_transport D Sc cutoff p x q.representative e ht,
        coordinate_pair_transport D Sc cutoff p x q.representative e ht]
      exact (show ∀ {t t' : List I} (e : t = t') (b : Old D Sc cutoff v t'),
        e.symm ▸ oldPrecomp D Sc cutoff v t' (twist k p c) b =
          oldPrecomp D Sc cutoff v t (twist k p c) (e.symm ▸ b) from
        by intro t t' e; subst t'; intro b; rfl) e b
    · rw [prependOldCoordinate_pair_off D Sc cutoff p x q.representative h,
        prependOldCoordinate_pair_off D Sc cutoff p x q.representative h, map_zero]

/-- Normalized output coefficients retain the old source action and its twist. -/
theorem outputLongCoordinate_oldSource (p : ZMod 2) (i : I) (v : List I)
    (m : ℕ) (c : hom D Sc cutoff v v) (z : Target D Sc cutoff i v (v ++ [i])) :
    outputLongCoordinate D Sc cutoff p i v m (oldSourceTarget D Sc cutoff i v (v ++ [i]) c z) =
      oldPrecomp D Sc cutoff v v (twist k p c) (outputLongCoordinate D Sc cutoff p i v m z) := by
  have transport {t t' : List I} (e : t = t')
      (f : Target D Sc cutoff i v (v ++ [i]) →ₗ[k] Old D Sc cutoff v t)
      (h : f (oldSourceTarget D Sc cutoff i v (v ++ [i]) c z) =
        oldPrecomp D Sc cutoff v t (twist k p c) (f z)) :
      (Eq.mp (congrArg (fun t => Target D Sc cutoff i v (v ++ [i]) →ₗ[k]
        Old D Sc cutoff v t) e) f) (oldSourceTarget D Sc cutoff i v (v ++ [i]) c z) =
      oldPrecomp D Sc cutoff v t' (twist k p c)
        ((Eq.mp (congrArg (fun t => Target D Sc cutoff i v (v ++ [i]) →ₗ[k]
          Old D Sc cutoff v t) e) f) z) := by
    subst t'
    exact h
  apply transport (longOutputIndex_oldTarget i v m)
  simp only [LinearMap.smul_apply, prependOldCoordinate_oldSource, map_smul]

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# Moving-chain comparison in long output coordinates

The prescribed moving chain and its collected endpoint polynomial have equal
long output extraction, with arbitrary exterior coefficients. Their difference
is therefore chronological short. This is the polynomial comparison needed
for S evaluation in `DeformedMackeyBoundary.md`; it does not identify the
normalized polynomial coefficients with the corrected rho iterates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem cast_map_apply_eq (i : I) (v t t' : List I) (e : t = t')
    (f : Target D Sc cutoff i v (v ++ [i]) →ₗ[k] Old D Sc cutoff v t)
    (z z' : Target D Sc cutoff i v (v ++ [i])) (h : f z = f z') :
    (Eq.mp (congrArg (fun t => Target D Sc cutoff i v (v ++ [i]) →ₗ[k]
      Old D Sc cutoff v t) e) f) z =
    (Eq.mp (congrArg (fun t => Target D Sc cutoff i v (v ++ [i]) →ₗ[k]
      Old D Sc cutoff v t) e) f) z' := by
  cases e
  exact h

/-- Full exterior coefficients preserve the collected moving-chain comparison. -/
theorem outputLongExtraction_move_endpointPolynomial (p : ZMod 2) (i : I) (v : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i]) (a ⊗ₜ[k] moveHom D Sc i [] v)) =
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i])
        (a ⊗ₜ[k] (leadingMoveEndpointPolynomial D Sc i [] v ≫
          cl D Sc _ _ (cw (leadingMoveWord [] v)) (leadingMoveWord_sChain i [] v)))) := by
  ext m
  simp only [outputLongExtraction_apply]
  unfold outputLongCoordinate
  apply cast_map_apply_eq D Sc cutoff i v _ v (longOutputIndex_oldTarget i v m)
  simp only [LinearMap.smul_apply, prependOldCoordinate_projection]
  apply congrArg (fun b : Old D Sc cutoff v (longOutputIndex i v m).oldTarget =>
    (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m • b)
  change (ideal D Sc cutoff v (longOutputIndex i v m).oldTarget).mkQ
      (prependExtractOld D Sc cutoff p (longOutputIndex i v m) _) =
    (ideal D Sc cutoff v (longOutputIndex i v m).oldTarget).mkQ
      (prependExtractOld D Sc cutoff p (longOutputIndex i v m) _)
  apply congrArg (ideal D Sc cutoff v (longOutputIndex i v m).oldTarget).mkQ
  apply prependExtractOld_congr_long D Sc cutoff p (longOutputIndex i v m) rfl
  intro y hy
  rw [prependAffineEquiv_tmul, prependAffineEquiv_tmul,
    moveHom_long_prepend_repr_endpointPolynomial D Sc i v y hy]

end OddMath.QuiverHecke.ELV
end

end
