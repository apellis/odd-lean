/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputOldAction
/-!
# Corrected rho in normalized output coordinates

The operator comparison required by `DeformedMackeyBoundary.md` (2).
The moving term shifts the exponent and twists the whole old coefficient.
The corrected rho recurrence cancels the two output signs but retains the old
delta action in every degree, including zero. All statements concern arbitrary
elements of the full old-only quotient, not just individual scalar tails.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
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

theorem prependOldCoordinate_signedMoving (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (d : ℕ) (z : Target D Sc cutoff i v w) :
    prependOldCoordinate D Sc cutoff p (x.shift d) (signedMovingPowerTarget D Sc cutoff i v w d z) =
      oldTwist D Sc cutoff (d • D.parity i) v x.oldTarget
        (prependOldCoordinate D Sc cutoff p x z) := by
  obtain ⟨f, rfl⟩ := prependOldReconstruct_surjective D Sc cutoff p i v w z
  induction f using DirectSum.induction_on with
  | zero =>
    exact Eq.trans
      (map_zero ((prependOldCoordinate D Sc cutoff p (x.shift d)).comp
        ((signedMovingPowerTarget D Sc cutoff i v w d).comp
          (prependOldReconstruct D Sc cutoff p i v w))))
      (map_zero ((oldTwist D Sc cutoff (d • D.parity i) v x.oldTarget).comp
        ((prependOldCoordinate D Sc cutoff p x).comp
          (prependOldReconstruct D Sc cutoff p i v w)))).symm
  | add f g hf hg =>
    exact (map_add ((prependOldCoordinate D Sc cutoff p (x.shift d)).comp
      ((signedMovingPowerTarget D Sc cutoff i v w d).comp
        (prependOldReconstruct D Sc cutoff p i v w))) f g).trans
      ((congrArg₂ (· + ·) hf hg).trans
        (map_add ((oldTwist D Sc cutoff (d • D.parity i) v x.oldTarget).comp
          ((prependOldCoordinate D Sc cutoff p x).comp
            (prependOldReconstruct D Sc cutoff p i v w))) f g).symm)
  | of q b =>
    change prependOldCoordinate D Sc cutoff p (x.shift d)
      (signedMovingPowerTarget D Sc cutoff i v w d
        (prependOldReconstruct D Sc cutoff p i v w (DirectSum.lof k _ _ q b))) =
      oldTwist D Sc cutoff (d • D.parity i) v x.oldTarget
        (prependOldCoordinate D Sc cutoff p x
          (prependOldReconstruct D Sc cutoff p i v w (DirectSum.lof k _ _ q b)))
    rw [prependOldReconstruct, DirectSum.toModule_lof, signedMovingPower_pair_shift]
    by_cases h : x.tailKey = q.representative.tailKey
    · have e := x.oldTarget_eq_of_tailKey_eq q.representative h
      have ht := prependTail_heq_of_tailKey_eq D Sc x q.representative h
      have hs : (x.shift d).tailKey = (q.representative.shift d).tailKey := by
        have hn := congrArg Prod.fst h
        have hd := congrArg Prod.snd h
        exact Prod.ext (congrArg (d + ·) hn) hd
      rw [coordinate_pair_transport D Sc cutoff p x q.representative e ht]
      calc
        _ = e.symm ▸ oldTwist D Sc cutoff (d • D.parity i) v q.representative.oldTarget b :=
          coordinate_pair_transport D Sc cutoff p (x.shift d) (q.representative.shift d) e
            (prependTail_heq_of_tailKey_eq D Sc (x.shift d) (q.representative.shift d) hs) _
        _ = _ := by
          exact (show ∀ {t t' : List I} (e : t = t') (b : Old D Sc cutoff v t'),
        e.symm ▸ oldTwist D Sc cutoff (d • D.parity i) v t' b =
          oldTwist D Sc cutoff (d • D.parity i) v t (e.symm ▸ b) from
        by intro t t' e; subst t'; intro b; rfl) e b
    · have hs : (x.shift d).tailKey ≠ (q.representative.shift d).tailKey := by
        intro he
        apply h
        have hn := congrArg Prod.fst he
        have hd := congrArg Prod.snd he
        exact Prod.ext (Nat.add_left_cancel hn) hd
      rw [prependOldCoordinate_pair_off D Sc cutoff p x q.representative h, map_zero]
      exact prependOldCoordinate_pair_off D Sc cutoff p (x.shift d) (q.representative.shift d) hs _

theorem outputLongCoordinate_signedMoving (p : ZMod 2) (i : I) (v : List I)
    (m d : ℕ) (z : Target D Sc cutoff i v (v ++ [i])) :
    outputLongCoordinate D Sc cutoff p i v (d + m)
      (signedMovingPowerTarget D Sc cutoff i v (v ++ [i]) d z) =
    (SKM.zsign k (D.parity i * wordSumParity D v)) ^ d •
      oldTwist D Sc cutoff (d • D.parity i) v v (outputLongCoordinate D Sc cutoff p i v m z) := by
  have h := prependOldCoordinate_signedMoving D Sc cutoff p (longOutputIndex i v m) d z
  change prependOldCoordinate D Sc cutoff p (longOutputIndex i v (d + m))
    (signedMovingPowerTarget D Sc cutoff i v (v ++ [i]) d z) =
    oldTwist D Sc cutoff (d • D.parity i) v (longOutputIndex i v m).oldTarget
      (prependOldCoordinate D Sc cutoff p (longOutputIndex i v m) z) at h
  have transport {t t' : List I} (e : t = t')
      (f g : Target D Sc cutoff i v (v ++ [i]) →ₗ[k] Old D Sc cutoff v t)
      (a : Target D Sc cutoff i v (v ++ [i]))
      (h : f a = oldTwist D Sc cutoff (d • D.parity i) v t (g z)) (s : k) :
      (Eq.mp (congrArg (fun t => Target D Sc cutoff i v (v ++ [i]) →ₗ[k]
        Old D Sc cutoff v t) e) (s ^ (d + m) • f)) a =
      s ^ d • oldTwist D Sc cutoff (d • D.parity i) v t'
        ((Eq.mp (congrArg (fun t => Target D Sc cutoff i v (v ++ [i]) →ₗ[k]
          Old D Sc cutoff v t) e) (s ^ m • g)) z) := by
    subst t'
    change s ^ (d + m) • f a = s ^ d • oldTwist D Sc cutoff (d • D.parity i) v t (s ^ m • g z)
    rw [h, map_smul, smul_smul, pow_add]
  exact transport (longOutputIndex_oldTarget i v m) _ _ _ h
    (SKM.zsign k (D.parity i * wordSumParity D v))

/-- Literal corrected-rho recurrence in normalized output coordinates. The
full old coefficient is twisted; the old delta term remains in the same degree. -/
theorem outputLongCoordinate_boundaryRho_succ (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (m : ℕ)
    (z : Target D Sc cutoff j.1 v (v ++ [j.1])) :
    outputLongCoordinate D Sc cutoff p j.1 v (1 + m)
      (boundaryRho D Sc cutoff j v (v ++ [j.1]) z) =
      oldTwist D Sc cutoff (D.parity j.1) v v (outputLongCoordinate D Sc cutoff p j.1 v m z) +
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        ((2 * (-1 : k) ^ cutoff j.1) •
          oldPrecomp D Sc cutoff v v (twist k p (boundaryDelta D Sc cutoff j v))
            (outputLongCoordinate D Sc cutoff p j.1 v (1 + m) z)) := by
  rw [boundaryRho_eq_moving_add_old, map_smul, map_add, map_smul,
    outputLongCoordinate_signedMoving, outputLongCoordinate_oldSource,
    one_nsmul, pow_one, smul_add, smul_smul, SKM.zsign_mul_self', one_smul]

/-- Degree zero receives no contribution from the positive moving power. -/
theorem outputLongCoordinate_signedMoving_zero (p : ZMod 2) (i : I) (v : List I)
    (d : ℕ) (hd : 0 < d) (z : Target D Sc cutoff i v (v ++ [i])) :
    outputLongCoordinate D Sc cutoff p i v 0
      (signedMovingPowerTarget D Sc cutoff i v (v ++ [i]) d z) = 0 := by
  have h : prependOldCoordinate D Sc cutoff p (longOutputIndex i v 0)
      (signedMovingPowerTarget D Sc cutoff i v (v ++ [i]) d z) = 0 := by
    obtain ⟨f, rfl⟩ := prependOldReconstruct_surjective D Sc cutoff p i v (v ++ [i]) z
    induction f using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add f g hf hg => simp only [map_add, hf, hg, add_zero]
    | of q b =>
      change prependOldCoordinate D Sc cutoff p (longOutputIndex i v 0)
        (signedMovingPowerTarget D Sc cutoff i v (v ++ [i]) d
          (prependOldReconstruct D Sc cutoff p i v (v ++ [i]) (DirectSum.lof k _ _ q b))) = 0
      rw [prependOldReconstruct, DirectSum.toModule_lof, signedMovingPower_pair_shift]
      apply prependOldCoordinate_pair_off
      intro he
      have hn := congrArg Prod.fst he
      change 0 = d + q.representative.1.1 at hn
      omega
  have transport {t t' : List I} (e : t = t')
      (f : Target D Sc cutoff i v (v ++ [i]) →ₗ[k] Old D Sc cutoff v t)
      (a : Target D Sc cutoff i v (v ++ [i])) (h : f a = 0) :
      (Eq.mp (congrArg (fun t => Target D Sc cutoff i v (v ++ [i]) →ₗ[k]
        Old D Sc cutoff v t) e) f) a = 0 := by
    subst t'
    exact h
  apply transport (longOutputIndex_oldTarget i v 0)
  simp only [LinearMap.smul_apply, h, smul_zero]

/-- The degree-zero corrected-rho coefficient is the old delta action. -/
theorem outputLongCoordinate_boundaryRho_zero (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (z : Target D Sc cutoff j.1 v (v ++ [j.1])) :
    outputLongCoordinate D Sc cutoff p j.1 v 0
      (boundaryRho D Sc cutoff j v (v ++ [j.1]) z) =
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        ((2 * (-1 : k) ^ cutoff j.1) •
          oldPrecomp D Sc cutoff v v (twist k p (boundaryDelta D Sc cutoff j v))
            (outputLongCoordinate D Sc cutoff p j.1 v 0 z)) := by
  rw [boundaryRho_eq_moving_add_old, map_smul, map_add, map_smul,
    outputLongCoordinate_signedMoving_zero D Sc cutoff p j.1 v 1 (by decide),
    zero_add, outputLongCoordinate_oldSource]

end OddMath.QuiverHecke.ELVOld