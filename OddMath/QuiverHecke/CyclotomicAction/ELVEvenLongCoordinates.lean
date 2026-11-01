import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalLongCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputRhoCoordinates

/-! # Even moving dots on arbitrary old-Hom long coordinates

The parity-zero specialization of DeformedMackeyBoundary (2)-(3).
The moving dot acts by the ordinary finite coefficient shift, on every
source class and on the specified long section. Full exterior old
coefficients are retained; there is no delta correction at even colour.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Ordinary finite coefficient shift, without a parity involution. -/
def evenLongShift (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  Finsupp.lmapDomain (Old D Sc cutoff v t) k Nat.succ

@[simp] theorem evenLongShift_single (v t : List I) (m : ℕ)
    (b : Old D Sc cutoff v t) :
    evenLongShift D Sc cutoff v t (Finsupp.single m b) = Finsupp.single (m + 1) b := by
  simp only [evenLongShift, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

private theorem evenOldTwist_zero (v t : List I) (b : Old D Sc cutoff v t) :
    oldTwist D Sc cutoff 0 v t b = b := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  change (ideal D Sc cutoff v t).mkQ (twist k 0 b) = _
  rw [twist_zero]

private theorem longHomCoordinate_evenMoving_succ (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) {v t : List I} (y : NFIdx v t) (m : ℕ)
    (z : Target D Sc cutoff i v (t ++ [i])) :
    longHomCoordinate D Sc cutoff p i y (1 + m)
      (movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi]) z) =
      longHomCoordinate D Sc cutoff p i y m z := by
  have h := prependOldCoordinate_signedMoving D Sc cutoff p (longHomIndex i y m) 1 z
  change prependOldCoordinate D Sc cutoff p (longHomIndex i y (1 + m))
    (signedMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1 z) =
    oldTwist D Sc cutoff (1 • D.parity i) v (longHomIndex i y m).oldTarget
      (prependOldCoordinate D Sc cutoff p (longHomIndex i y m) z) at h
  simp only [hi, smul_zero, evenOldTwist_zero] at h
  have transport {s : List I} (e : s = t)
      (f g : Target D Sc cutoff i v (t ++ [i]) →ₗ[k] Old D Sc cutoff v s)
      (a : Target D Sc cutoff i v (t ++ [i])) (h : f a = g z) :
      (Eq.mp (congrArg (fun s => Target D Sc cutoff i v (t ++ [i]) →ₗ[k]
        Old D Sc cutoff v s) e) f) a =
      (Eq.mp (congrArg (fun s => Target D Sc cutoff i v (t ++ [i]) →ₗ[k]
        Old D Sc cutoff v s) e) g) z := by
    subst s
    exact h
  unfold longHomCoordinate
  simp only [hi, zero_mul, SKM.zsign_zero, one_pow, one_smul]
  exact transport (longHomIndex_oldTarget i y m) _ _ _ h

private theorem longHomCoordinate_evenMoving_zero (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) {v t : List I} (y : NFIdx v t)
    (z : Target D Sc cutoff i v (t ++ [i])) :
    longHomCoordinate D Sc cutoff p i y 0
      (movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi]) z) = 0 := by
  have h : prependOldCoordinate D Sc cutoff p (longHomIndex i y 0)
      (movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi]) z) = 0 := by
    obtain ⟨f, rfl⟩ := prependOldReconstruct_surjective D Sc cutoff p i v (t ++ [i]) z
    induction f using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add f g hf hg => simp only [map_add, hf, hg, add_zero]
    | of q b =>
      change prependOldCoordinate D Sc cutoff p (longHomIndex i y 0)
        (movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi])
          (prependOldReconstruct D Sc cutoff p i v (t ++ [i]) (DirectSum.lof k _ _ q b))) = 0
      rw [prependOldReconstruct, DirectSum.toModule_lof, movingPower_pair_shift]
      apply prependOldCoordinate_pair_off
      intro he
      have hn := congrArg Prod.fst he
      change 0 = 1 + q.representative.1.1 at hn
      omega
  have transport {s : List I} (e : s = t)
      (f : Target D Sc cutoff i v (t ++ [i]) →ₗ[k] Old D Sc cutoff v s)
      (a : Target D Sc cutoff i v (t ++ [i])) (h : f a = 0) :
      (Eq.mp (congrArg (fun s => Target D Sc cutoff i v (t ++ [i]) →ₗ[k]
        Old D Sc cutoff v s) e) f) a = 0 := by
    subst s
    exact h
  unfold longHomCoordinate
  simp only [pow_zero, one_smul]
  exact transport (longHomIndex_oldTarget i y 0) _ _ h

theorem longHomExtraction_evenMoving (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    {v t : List I} (y : NFIdx v t) (z : Target D Sc cutoff i v (t ++ [i])) :
    longHomExtraction D Sc cutoff p i y
      (movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi]) z) =
      evenLongShift D Sc cutoff v t (longHomExtraction D Sc cutoff p i y z) := by
  apply Finsupp.ext
  intro m
  cases m with
  | zero =>
    rw [longHomExtraction_apply,
      longHomCoordinate_evenMoving_zero D Sc cutoff p i hi y z]
    simp only [evenLongShift, Finsupp.lmapDomain_apply]
    rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp)]
  | succ m =>
    rw [longHomExtraction_apply]
    have h := longHomCoordinate_evenMoving_succ D Sc cutoff p i hi y m z
    rw [Nat.add_comm 1 m] at h
    rw [h]
    simp only [evenLongShift, Finsupp.lmapDomain_apply]
    rw [Finsupp.mapDomain_apply_of_injective Nat.succ_injective]
    rfl

/-- Every arbitrary-endpoint source class satisfies the even first-dot recurrence. -/
theorem offDiagonalLongExtraction_evenMoving (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (z : Target D Sc cutoff i v (t ++ [i])) :
    offDiagonalLongExtraction D Sc cutoff p i v t
      (movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi]) z) =
      evenLongShift D Sc cutoff v t (offDiagonalLongExtraction D Sc cutoff p i v t z) := by
  by_cases h : Nonempty (NFIdx v t)
  · obtain ⟨y⟩ := h
    simp only [offDiagonalLongExtraction_eq D Sc cutoff p i y]
    exact longHomExtraction_evenMoving D Sc cutoff p i hi y z
  · simp only [offDiagonalLongExtraction, dite_eq_right h, LinearMap.zero_apply, map_zero]

theorem evenMoving_longHomLift (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    {v t : List I} (y : NFIdx v t) (m : ℕ) (b : Old D Sc cutoff v t) :
    movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi])
      (longHomLift D Sc cutoff p i y m b) = longHomLift D Sc cutoff p i y (m + 1) b := by
  have transport {s : List I} (e : s = t)
      (f g : Old D Sc cutoff v s →ₗ[k] Target D Sc cutoff i v (t ++ [i]))
      (h : ∀ b, movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi]) (f b) = g b) :
      ∀ b : Old D Sc cutoff v t,
      movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi])
        ((Eq.mp (congrArg (fun s => Old D Sc cutoff v s →ₗ[k]
          Target D Sc cutoff i v (t ++ [i])) e) f) b) =
      (Eq.mp (congrArg (fun s => Old D Sc cutoff v s →ₗ[k]
        Target D Sc cutoff i v (t ++ [i])) e) g) b := by
    subst s
    exact h
  unfold longHomLift
  simp only [hi, zero_mul, SKM.zsign_zero, one_pow, one_smul]
  apply transport (longHomIndex_oldTarget i y m)
  intro c
  have h := movingPower_pair_shift D Sc cutoff p (longHomIndex i y m) 1 (by simp [hi]) c
  have ht : prependTail D Sc ((longHomIndex i y m).shift 1) =
      prependTail D Sc (longHomIndex i y (m + 1)) :=
    congrArg (fun n : ℕ => (show (pres D Sc).obj (ob D
      (i :: (longHomIndex i y m).oldTarget)) ⟶
        (pres D Sc).obj (ob D (t ++ [i])) from
          prependTail D Sc (longHomIndex i y n))) (Nat.add_comm 1 m)
  rw [ht] at h
  exact h

/-- The prescribed long section intertwines the even moving dot and ordinary shift. -/
theorem evenMoving_offDiagonalLongSection (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi])
      (offDiagonalLongSection D Sc cutoff p i v t f) =
      offDiagonalLongSection D Sc cutoff p i v t (evenLongShift D Sc cutoff v t f) := by
  by_cases h : Nonempty (NFIdx v t)
  · obtain ⟨y⟩ := h
    simp only [offDiagonalLongSection_eq D Sc cutoff p i y]
    induction f using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add f g hf hg => simp only [map_add, hf, hg]
    | single m b =>
      simp only [longHomSection, Finsupp.lsum_single, evenLongShift_single]
      exact evenMoving_longHomLift D Sc cutoff p i hi y m b
  · have hf : f = 0 := by
      ext n
      exact old_eq_zero_of_no_normal_form D Sc cutoff h (f n)
    rw [hf]
    simp only [map_zero]

end OddMath.QuiverHecke.ELVOld
