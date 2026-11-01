import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalRho
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputRhoCoordinates

/-! # Corrected rho on all off-diagonal old-only classes

The arbitrary-old-Hom extraction comparison of DeformedMackeyBoundary (2).
The coefficient recurrence holds on every Target class, not only the selected
section. All total-parity and source-delta terms are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem longHomCoordinate_oldSource (p : ZMod 2) (i : I) {v t : List I}
    (y : NFIdx v t) (m : ℕ) (c : hom D Sc cutoff v v)
    (z : Target D Sc cutoff i v (t ++ [i])) :
    longHomCoordinate D Sc cutoff p i y m (oldSourceTarget D Sc cutoff i v (t ++ [i]) c z) =
      oldPrecomp D Sc cutoff v t (twist k p c) (longHomCoordinate D Sc cutoff p i y m z) := by
  have transport {s s' : List I} (e : s = s')
      (f : Target D Sc cutoff i v (t ++ [i]) →ₗ[k] Old D Sc cutoff v s)
      (h : f (oldSourceTarget D Sc cutoff i v (t ++ [i]) c z) =
        oldPrecomp D Sc cutoff v s (twist k p c) (f z)) :
      (Eq.mp (congrArg (fun s => Target D Sc cutoff i v (t ++ [i]) →ₗ[k]
        Old D Sc cutoff v s) e) f) (oldSourceTarget D Sc cutoff i v (t ++ [i]) c z) =
      oldPrecomp D Sc cutoff v s' (twist k p c)
        ((Eq.mp (congrArg (fun s => Target D Sc cutoff i v (t ++ [i]) →ₗ[k]
          Old D Sc cutoff v s) e) f) z) := by
    subst s'
    exact h
  apply transport (longHomIndex_oldTarget i y m)
  simp only [LinearMap.smul_apply, prependOldCoordinate_oldSource, map_smul]

theorem longHomCoordinate_signedMoving (p : ZMod 2) (i : I) {v t : List I}
    (y : NFIdx v t) (m d : ℕ) (z : Target D Sc cutoff i v (t ++ [i])) :
    longHomCoordinate D Sc cutoff p i y (d + m)
      (signedMovingPowerTarget D Sc cutoff i v (t ++ [i]) d z) =
    (SKM.zsign k (D.parity i * wordSumParity D v)) ^ d •
      oldTwist D Sc cutoff (d • D.parity i) v t (longHomCoordinate D Sc cutoff p i y m z) := by
  have h := prependOldCoordinate_signedMoving D Sc cutoff p (longHomIndex i y m) d z
  change prependOldCoordinate D Sc cutoff p (longHomIndex i y (d + m))
    (signedMovingPowerTarget D Sc cutoff i v (t ++ [i]) d z) =
    oldTwist D Sc cutoff (d • D.parity i) v (longHomIndex i y m).oldTarget
      (prependOldCoordinate D Sc cutoff p (longHomIndex i y m) z) at h
  have transport {s s' : List I} (e : s = s')
      (f g : Target D Sc cutoff i v (t ++ [i]) →ₗ[k] Old D Sc cutoff v s)
      (a : Target D Sc cutoff i v (t ++ [i]))
      (h : f a = oldTwist D Sc cutoff (d • D.parity i) v s (g z)) (r : k) :
      (Eq.mp (congrArg (fun s => Target D Sc cutoff i v (t ++ [i]) →ₗ[k]
        Old D Sc cutoff v s) e) (r ^ (d + m) • f)) a =
      r ^ d • oldTwist D Sc cutoff (d • D.parity i) v s'
        ((Eq.mp (congrArg (fun s => Target D Sc cutoff i v (t ++ [i]) →ₗ[k]
          Old D Sc cutoff v s) e) (r ^ m • g)) z) := by
    subst s'
    change r ^ (d + m) • f a = r ^ d • oldTwist D Sc cutoff (d • D.parity i) v s (r ^ m • g z)
    rw [h, map_smul, smul_smul, pow_add]
  exact transport (longHomIndex_oldTarget i y m) _ _ _ h
    (SKM.zsign k (D.parity i * wordSumParity D v))

theorem longHomCoordinate_boundaryRho_succ (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) {v t : List I} (y : NFIdx v t) (m : ℕ)
    (z : Target D Sc cutoff j.1 v (t ++ [j.1])) :
    longHomCoordinate D Sc cutoff p j.1 y (1 + m)
      (boundaryRho D Sc cutoff j v (t ++ [j.1]) z) =
      oldTwist D Sc cutoff (D.parity j.1) v t (longHomCoordinate D Sc cutoff p j.1 y m z) +
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        ((2 * (-1 : k) ^ cutoff j.1) •
          oldPrecomp D Sc cutoff v t (twist k p (boundaryDelta D Sc cutoff j v))
            (longHomCoordinate D Sc cutoff p j.1 y (1 + m) z)) := by
  rw [boundaryRho_eq_moving_add_old, map_smul, map_add, map_smul,
    longHomCoordinate_signedMoving, longHomCoordinate_oldSource,
    one_nsmul, pow_one, smul_add, smul_smul, SKM.zsign_mul_self', one_smul]

theorem longHomCoordinate_signedMoving_zero (p : ZMod 2) (i : I) {v t : List I}
    (y : NFIdx v t) (d : ℕ) (hd : 0 < d) (z : Target D Sc cutoff i v (t ++ [i])) :
    longHomCoordinate D Sc cutoff p i y 0
      (signedMovingPowerTarget D Sc cutoff i v (t ++ [i]) d z) = 0 := by
  have h : prependOldCoordinate D Sc cutoff p (longHomIndex i y 0)
      (signedMovingPowerTarget D Sc cutoff i v (t ++ [i]) d z) = 0 := by
    obtain ⟨f, rfl⟩ := prependOldReconstruct_surjective D Sc cutoff p i v (t ++ [i]) z
    induction f using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add f g hf hg => simp only [map_add, hf, hg, add_zero]
    | of q b =>
      change prependOldCoordinate D Sc cutoff p (longHomIndex i y 0)
        (signedMovingPowerTarget D Sc cutoff i v (t ++ [i]) d
          (prependOldReconstruct D Sc cutoff p i v (t ++ [i]) (DirectSum.lof k _ _ q b))) = 0
      rw [prependOldReconstruct, DirectSum.toModule_lof, signedMovingPower_pair_shift]
      apply prependOldCoordinate_pair_off
      intro he
      have hn := congrArg Prod.fst he
      change 0 = d + q.representative.1.1 at hn
      omega
  have transport {s s' : List I} (e : s = s')
      (f : Target D Sc cutoff i v (t ++ [i]) →ₗ[k] Old D Sc cutoff v s)
      (a : Target D Sc cutoff i v (t ++ [i])) (h : f a = 0) :
      (Eq.mp (congrArg (fun s => Target D Sc cutoff i v (t ++ [i]) →ₗ[k]
        Old D Sc cutoff v s) e) f) a = 0 := by
    subst s'
    exact h
  apply transport (longHomIndex_oldTarget i y 0)
  simp only [LinearMap.smul_apply, h, smul_zero]

theorem longHomCoordinate_boundaryRho_zero (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) {v t : List I} (y : NFIdx v t)
    (z : Target D Sc cutoff j.1 v (t ++ [j.1])) :
    longHomCoordinate D Sc cutoff p j.1 y 0
      (boundaryRho D Sc cutoff j v (t ++ [j.1]) z) =
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        ((2 * (-1 : k) ^ cutoff j.1) •
          oldPrecomp D Sc cutoff v t (twist k p (boundaryDelta D Sc cutoff j v))
            (longHomCoordinate D Sc cutoff p j.1 y 0 z)) := by
  rw [boundaryRho_eq_moving_add_old, map_smul, map_add, map_smul,
    longHomCoordinate_signedMoving_zero D Sc cutoff p j.1 y 1 (by decide),
    zero_add, longHomCoordinate_oldSource]

/-- Every old-only class satisfies the actual corrected coefficient recurrence. -/
theorem longHomExtraction_boundaryRho (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) {v t : List I} (y : NFIdx v t)
    (z : Target D Sc cutoff j.1 v (t ++ [j.1])) :
    longHomExtraction D Sc cutoff p j.1 y (boundaryRho D Sc cutoff j v (t ++ [j.1]) z) =
      offDiagonalCoefficientRho D Sc cutoff p j v t (longHomExtraction D Sc cutoff p j.1 y z) := by
  apply Finsupp.ext
  intro m
  cases m with
  | zero =>
    rw [longHomExtraction_apply, longHomCoordinate_boundaryRho_zero]
    simp only [offDiagonalCoefficientRho, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.lmapDomain_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
      longHomExtraction_apply]
    rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp), zero_add]
  | succ m =>
    rw [longHomExtraction_apply]
    have hr := longHomCoordinate_boundaryRho_succ D Sc cutoff p j y m z
    rw [Nat.add_comm 1 m] at hr
    rw [hr]
    simp only [offDiagonalCoefficientRho, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.lmapDomain_apply]
    rw [Finsupp.mapDomain_apply_of_injective Nat.succ_injective]
    rfl

/-- Unconditional recurrence on all arbitrary-endpoint classes, including empty old Homs. -/
theorem offDiagonalLongExtraction_boundaryRho (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (z : Target D Sc cutoff j.1 v (t ++ [j.1])) :
    offDiagonalLongExtraction D Sc cutoff p j.1 v t
      (boundaryRho D Sc cutoff j v (t ++ [j.1]) z) =
      offDiagonalCoefficientRho D Sc cutoff p j v t
        (offDiagonalLongExtraction D Sc cutoff p j.1 v t z) := by
  by_cases h : Nonempty (NFIdx v t)
  · obtain ⟨y⟩ := h
    rw [offDiagonalLongExtraction_eq D Sc cutoff p j.1 y]
    exact longHomExtraction_boundaryRho D Sc cutoff p j y z
  · simp only [offDiagonalLongExtraction, dite_eq_right h, LinearMap.zero_apply, map_zero]

end OddMath.QuiverHecke.ELVOld
