import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalCapComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedSourceLinearEquiv
import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedCapRows

/-! # Ordinary dotted-counit input inverse

DeformedMatrixComparison (5) and the input inverse of DeformedRouquierMatrix,
section 4, give the inverse on the canonical induction-restriction carrier.
The cap rows below are the ordinary adjunction counit after induction-dot
powers. The first row is explicitly minus the balanced crossing after the
canonical source equivalence. Its identification with the ordered categorical
mate is a separate obligation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Prescribed whole-output twist and cap scalar, as an invertible row change. -/
def counitInputRowEquiv (v t : List I) (n : ℕ) :
    Old D Sc cutoff v t ≃ₗ[k] Old D Sc cutoff v t :=
  (LinearEquiv.ofInvolutive (oldTwist D Sc cutoff ((n + 1 : ℕ) : ZMod 2) v t)
    (oldTwist_twice D Sc cutoff _ v t)).trans
      (LinearEquiv.smulOfUnit ((-1 : kˣ) ^ (n + 1).choose 2))

@[simp] theorem counitInputRowEquiv_apply (v t : List I) (n : ℕ)
    (b : Old D Sc cutoff v t) :
    counitInputRowEquiv D Sc cutoff v t n b =
      capRowSign (k := k) n • oldTwist D Sc cutoff ((n + 1 : ℕ) : ZMod 2) v t b := by
  change (((-1 : kˣ) ^ (n + 1).choose 2 : kˣ) : k) •
    oldTwist D Sc cutoff ((n + 1 : ℕ) : ZMod 2) v t b = _
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, capRowSign]

/-- The single output change consists of crossing negation and all cap-row changes. -/
def counitInputOutputEquiv (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ) :
    (Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) × (Fin m → Old D Sc cutoff v t)) ≃ₗ[k]
      (Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) × (Fin m → Old D Sc cutoff v t)) :=
  (LinearEquiv.neg k).prodCongr
    (LinearEquiv.piCongrRight fun r : Fin m => counitInputRowEquiv D Sc cutoff v t r.val)

/-- Conjugation of every dot power by the induced coefficient comparison. -/
theorem sourceInputDot_iterate_carrier (j : {j : I // D.parity j = 1})
    (v t : List I) (n : ℕ) (z : shiftedCarrier D Sc cutoff j.1 v t) :
    (sourceInputDot D Sc cutoff j v t)^[n]
        (coefficientOneSourceEquiv D Sc cutoff j v t z) =
      coefficientOneSourceEquiv D Sc cutoff j v t
        ((shiftedInputDot D Sc cutoff j v t)^[n] z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, sourceInputDot_carrier,
      Function.iterate_succ_apply']

/-- Concrete inverse on the ordinary induction-restriction source. -/
def counitInputMatrixEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff) ≃ₗ[k]
      (Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) × (Fin m → Old D Sc cutoff v t)) :=
  ((shiftedSourceCanonicalEquiv D Sc cutoff j v t).trans
    (offDiagonalShiftedInputMatrixEquiv D Sc cutoff p j v t m hm)).trans
      (counitInputOutputEquiv D Sc cutoff j v t m)

@[simp] theorem counitInputMatrixEquiv_fst (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    (counitInputMatrixEquiv D Sc cutoff p j v t m hm z).1 =
      -toCyclotomic D Sc cutoff j.1 v t (shiftedSourceCanonicalEquiv D Sc cutoff j v t z) := rfl

/-- Every remaining row is literally the ordinary adjunction counit after a dot power. -/
theorem counitInputMatrixEquiv_cap (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) (r : Fin m) :
    (counitInputMatrixEquiv D Sc cutoff p j v t m hm z).2 r =
      ((BalancedInduction.adjunctionCounit (append D Sc cutoff j.1)).app
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
          (⟨t⟩ : OldCategory D Sc cutoff)
          ((inductionDot D Sc cutoff j.1
            ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
              (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
            (⟨t⟩ : OldCategory D Sc cutoff))^[r.val] z) := by
  change counitInputRowEquiv D Sc cutoff v t r.val
    (sourceInputContraction D Sc cutoff j v t
      (((sourceInputDot D Sc cutoff j v t) ^ r.val)
        (shiftedSourceCanonicalEquiv D Sc cutoff j v t z))) = _
  rw [counitInputRowEquiv_apply, Module.End.pow_apply,
    shiftedSourceCanonicalEquiv_apply, sourceInputDot_iterate_carrier,
    sourceInputContraction_carrier]
  exact shiftedCapRow_normalization D Sc cutoff j v t r.val z

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
