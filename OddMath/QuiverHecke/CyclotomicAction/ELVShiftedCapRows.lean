import OddMath.QuiverHecke.CyclotomicAction.ELVActualCapParity
import OddMath.QuiverHecke.CyclotomicAction.ELVCapSignNormalization

/-! # The prescribed dotted row of the shifted counit
DeformedMatrixComparison (5) is proved for the canonical source comparison
and the existing induction dot and counit. Every map below is constructed
from those module functors. The whole output parity and the cap scalar are
retained; no arbitrary source isomorphism or presumed row equality occurs.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem representable_sgn (v t : List I) (p : ZMod 2)
    (b : Old D Sc cutoff v t) :
    ((oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).obj
      (⟨t⟩ : OldCategory D Sc cutoff)).sgn p b = oldTwist D Sc cutoff p v t b := by
  change (Supercategory.homSVec k (OldCategory D Sc cutoff)
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).sgn p b = _
  rw [SVec.sgn_apply, Supercategory.homSVec_proj, Supercategory.homSVec_proj,
    ← oldCategory_twist D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)
      (⟨t⟩ : OldCategory D Sc cutoff) p b, twist_apply]

private theorem even_total_mem
    {M N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)} {f : M ⟶ N}
    (hf : f ∈ parity (R := k) M N 0) (t : OldCategory D Sc cutoff) :
    f.total t ∈ parity (R := k) (M.obj t) (N.obj t) 0 := by
  change f.app 0 t + f.app 1 t ∈ _
  rw [Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide) t, add_zero]
  exact f.app_mem 0 t

/-- The exact cap-row normalization for the actual induction dot, canonical
whole source comparison and actual adjunction counit, at arbitrary old endpoints.
The scalar is exactly (-1)^(n(n+1)/2) by capRowSign_eq. -/
theorem shiftedCapRow_normalization (j : {j : I // D.parity j = 1})
    (v t : List I) (n : ℕ)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    capRowSign (k := k) n • oldTwist D Sc cutoff ((n + 1 : ℕ) : ZMod 2) v t
      (shiftedInputContraction D Sc cutoff j.1 v t
        ((shiftedInputDot D Sc cutoff j v t)^[n]
          ((shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
            (⟨t⟩ : OldCategory D Sc cutoff) z))) =
      ((BalancedInduction.adjunctionCounit (append D Sc cutoff j.1)).app
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
          (⟨t⟩ : OldCategory D Sc cutoff)
          ((inductionDot D Sc cutoff j.1
            ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
              (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
            (⟨t⟩ : OldCategory D Sc cutoff))^[n] z) := by
  let U := (unshiftedSourceModule D Sc cutoff j.1 v).obj
    (⟨t⟩ : OldCategory D Sc cutoff)
  let S := shiftedSourceSpace D Sc cutoff j.1 v t
  let O := (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).obj
    (⟨t⟩ : OldCategory D Sc cutoff)
  let J : U →ₗ[k] S := (shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
    (⟨t⟩ : OldCategory D Sc cutoff)
  let A : S →ₗ[k] O := (shiftedSourceCounit D Sc cutoff j.1 v).total
    (⟨t⟩ : OldCategory D Sc cutoff)
  let C : U →ₗ[k] O := ((BalancedInduction.adjunctionCounit (append D Sc cutoff j.1)).app
    (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
      (⟨t⟩ : OldCategory D Sc cutoff)
  let T : U →ₗ[k] U := inductionDot D Sc cutoff j.1
    ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
    (⟨t⟩ : OldCategory D Sc cutoff)
  let Xs : S →ₗ[k] S := shiftedInputDot D Sc cutoff j v t
  have hJ : J ∈ SVec.parityHom U S 1 :=
    odd_total_mem D Sc cutoff (shiftedSourceParityIso_hom_mem D Sc cutoff j.1 v) _
  have hC : C ∈ SVec.parityHom U O 0 :=
    even_total_mem D Sc cutoff
      (BalancedInduction.adjunctionCounit_mem (append D Sc cutoff j.1)
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) _
  have hT : T ∈ SVec.parityHom U U 1 := inductionDot_mem D Sc cutoff j _ _
  have hJsign (w : U) : S.sgn 1 (J w) = -J (U.sgn 1 w) := by
    have h := congrArg (fun f : U →ₗ[k] S => f w) (SVec.sgn_comp_of_mem hJ 1)
    simpa using h
  have hXJ (w : U) : Xs (J w) = J ((T.comp (U.sgn 1)) w) := by
    change inductionDot D Sc cutoff j.1 (coefficientOneModule D Sc cutoff j.1 v)
      (⟨t⟩ : OldCategory D Sc cutoff) (S.sgn 1 (J w)) = J (T (U.sgn 1 w))
    rw [hJsign, map_neg]
    change -inductionDot D Sc cutoff j.1 (coefficientOneModule D Sc cutoff j.1 v)
        (⟨t⟩ : OldCategory D Sc cutoff)
        ((shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
          (⟨t⟩ : OldCategory D Sc cutoff) (U.sgn 1 w)) =
      (shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
        (⟨t⟩ : OldCategory D Sc cutoff)
        (inductionDot D Sc cutoff j.1
          ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
          (⟨t⟩ : OldCategory D Sc cutoff) (U.sgn 1 w))
    exact neg_eq_iff_eq_neg.mpr
      (inductionDot_sourceParity D Sc cutoff j v t (U.sgn 1 w))
  have hiter (m : ℕ) (w : U) :
      Xs^[m] (J w) = J ((T.comp (U.sgn 1))^[m] w) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, hXJ, Function.iterate_succ_apply']
  have hAJ (w : U) : A (J w) = C w := by
    have h := congrArg (fun f => f.total (⟨t⟩ : OldCategory D Sc cutoff) w)
      (shiftedSourceParityIso_counit D Sc cutoff j.1 v)
    rw [Superfunctor.comp_total] at h
    change (shiftedSourceCounit D Sc cutoff j.1 v).total
        (⟨t⟩ : OldCategory D Sc cutoff)
        ((shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
          (⟨t⟩ : OldCategory D Sc cutoff) w) =
      ((BalancedInduction.adjunctionCounit (append D Sc cutoff j.1)).app
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
        (⟨t⟩ : OldCategory D Sc cutoff) w
    exact h
  have hCsign (q : ZMod 2) (w : U) : O.sgn q (C w) = C (U.sgn q w) := by
    have h := congrArg (fun f : U →ₗ[k] O => f w) (SVec.sgn_comp_of_mem hC q)
    simpa using h
  have hp : ((n + 1 : ℕ) : ZMod 2) + 1 = (n : ZMod 2) := by
    rw [Nat.cast_add, Nat.cast_one, add_assoc, SVec.zmod2_one_add_one, add_zero]
  have hsgn (w : O) :
      O.sgn ((n + 1 : ℕ) : ZMod 2) (O.sgn 1 w) = O.sgn (n : ZMod 2) w := by
    have h := congrArg (fun f : O →ₗ[k] O => f w)
      (SVec.sgn_comp_sgn O ((n + 1 : ℕ) : ZMod 2) 1)
    simpa only [LinearMap.comp_apply, hp] using h
  rw [shiftedInputContraction, LinearMap.comp_apply,
    ← representable_sgn D Sc cutoff v t ((n + 1 : ℕ) : ZMod 2),
    ← representable_sgn D Sc cutoff v t 1]
  change capRowSign (k := k) n •
      O.sgn ((n + 1 : ℕ) : ZMod 2) (O.sgn 1 (A (Xs^[n] (J z)))) = C (T^[n] z)
  rw [hsgn, hiter, hAJ, hCsign, ← map_smul]
  rw [capRowSign_sgn_iterate U T hT n z]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

