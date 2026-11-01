import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalRho

/-! # Corrected coordinate basis over arbitrary old Homs

The invertible source-coordinate change needed for off-diagonal row division
in DeformedBoundaryDivision (5). Its forward values are extracted from actual
corrected lifts, not postulated coordinate vectors. The full source delta
and entire old-coefficient twist are retained, including empty old Homs.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def offDiagonalDeltaCoefficient (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) : Old D Sc cutoff v t →ₗ[k] Old D Sc cutoff v t :=
  SKM.zsign k (D.parity j.1 * wordSumParity D v) •
    ((2 * (-1 : k) ^ cutoff j.1) •
      oldPrecomp D Sc cutoff v t (twist k p (boundaryDelta D Sc cutoff j v)))

private theorem offDiagonal_twist_twice (q : ZMod 2) (v t : List I)
    (b : Old D Sc cutoff v t) :
    oldTwist D Sc cutoff q v t (oldTwist D Sc cutoff q v t b) = b := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  change (ideal D Sc cutoff v t).mkQ (twist k q (twist k q b)) = _
  rw [twist_twist]

@[simp] theorem offDiagonalCorrectedLift_zero (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (d : ℕ) :
    offDiagonalCorrectedLift D Sc cutoff p j v t d 0 = 0 := by
  unfold offDiagonalCorrectedLift
  rw [Finsupp.single_zero, map_zero]
  induction d with
  | zero => rfl
  | succ d ih => rw [Function.iterate_succ_apply', ih, map_zero]

private theorem rho_even_longHomLift (p : ZMod 2) (j : {j : I // D.parity j = 1})
    {v t : List I} (y : NFIdx v t) (q : ℕ) (b : Old D Sc cutoff v t) :
    (boundaryRho D Sc cutoff j v (t ++ [j.1]))^[2 * q]
      (longHomLift D Sc cutoff p j.1 y 0 b) =
      longHomLift D Sc cutoff p j.1 y (2 * q) b := by
  have transport {s : List I} (e : s = t)
      (f g : Old D Sc cutoff v s →ₗ[k] Target D Sc cutoff j.1 v (t ++ [j.1]))
      (h : ∀ b, (boundaryRho D Sc cutoff j v (t ++ [j.1]))^[2 * q] (f b) = g b) :
      ∀ b : Old D Sc cutoff v t,
      (boundaryRho D Sc cutoff j v (t ++ [j.1]))^[2 * q]
        ((Eq.mp (congrArg (fun s => Old D Sc cutoff v s →ₗ[k]
          Target D Sc cutoff j.1 v (t ++ [j.1])) e) f) b) =
      (Eq.mp (congrArg (fun s => Old D Sc cutoff v s →ₗ[k]
          Target D Sc cutoff j.1 v (t ++ [j.1])) e) g) b := by
    subst s
    exact h
  have hs : (SKM.zsign k (D.parity j.1 * wordSumParity D v)) ^ (2 * q) = 1 := by
    rw [pow_mul, pow_two, SKM.zsign_mul_self', one_pow]
  unfold longHomLift
  simp only [pow_zero, one_smul, hs]
  apply transport (longHomIndex_oldTarget j.1 y 0)
  intro c
  have h := boundaryRho_iterate_even_pair D Sc cutoff p j (longHomIndex j.1 y 0) q c
  have ht : prependTail D Sc ((longHomIndex j.1 y 0).shift (2 * q)) =
      prependTail D Sc (longHomIndex j.1 y (2 * q)) :=
    congrArg (fun n : ℕ => (show (pres D Sc).obj (ob D
      (j.1 :: (longHomIndex j.1 y 0).oldTarget)) ⟶
        (pres D Sc).obj (ob D (t ++ [j.1])) from
          prependTail D Sc (longHomIndex j.1 y n))) (Nat.add_zero (2 * q))
  rw [ht] at h
  exact h

theorem offDiagonalCorrectedLift_even (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (q : ℕ) (b : Old D Sc cutoff v t) :
    offDiagonalCorrectedLift D Sc cutoff p j v t (2 * q) b =
      offDiagonalLongSection D Sc cutoff p j.1 v t (Finsupp.single (2 * q) b) := by
  by_cases h : Nonempty (NFIdx v t)
  · obtain ⟨y⟩ := h
    unfold offDiagonalCorrectedLift
    simp only [offDiagonalLongSection_eq D Sc cutoff p j.1 y, longHomSection_single]
    exact rho_even_longHomLift D Sc cutoff p j y q b
  · have hb := old_eq_zero_of_no_normal_form D Sc cutoff h b
    simp only [hb, offDiagonalCorrectedLift_zero, Finsupp.single_zero, map_zero]

theorem offDiagonalCorrectedLift_odd (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (q : ℕ) (b : Old D Sc cutoff v t) :
    offDiagonalCorrectedLift D Sc cutoff p j v t (2 * q + 1) b =
      offDiagonalLongSection D Sc cutoff p j.1 v t
        (Finsupp.single (2 * q + 1) (oldTwist D Sc cutoff (D.parity j.1) v t b)) +
      offDiagonalLongSection D Sc cutoff p j.1 v t
        (Finsupp.single (2 * q) (offDiagonalDeltaCoefficient D Sc cutoff p j v t b)) := by
  rw [offDiagonalCorrectedLift, Function.iterate_succ_apply']
  change boundaryRho D Sc cutoff j v (t ++ [j.1])
    (offDiagonalCorrectedLift D Sc cutoff p j v t (2 * q) b) = _
  rw [offDiagonalCorrectedLift_even, boundaryRho_offDiagonalLongSection,
    offDiagonalCoefficientRho_single, map_add]
  simp only [offDiagonalDeltaCoefficient, LinearMap.smul_apply, ← Finsupp.smul_single,
    map_smul]

theorem offDiagonalCorrectedLift_coordinates (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (q : ℕ) (b : Old D Sc cutoff v t) :
    offDiagonalLongExtraction D Sc cutoff p j.1 v t
      (offDiagonalCorrectedLift D Sc cutoff p j v t (2 * q) b) = Finsupp.single (2 * q) b ∧
    offDiagonalLongExtraction D Sc cutoff p j.1 v t
      (offDiagonalCorrectedLift D Sc cutoff p j v t (2 * q + 1) b) =
      Finsupp.single (2 * q + 1) (oldTwist D Sc cutoff (D.parity j.1) v t b) +
      Finsupp.single (2 * q) (offDiagonalDeltaCoefficient D Sc cutoff p j v t b) := by
  constructor
  · rw [offDiagonalCorrectedLift_even, offDiagonalLongExtraction_section]
  · rw [offDiagonalCorrectedLift_odd, map_add, offDiagonalLongExtraction_section,
      offDiagonalLongExtraction_section]

/-- Finite triangular coordinate change on all degrees, with full old coefficients. -/
def offDiagonalCorrectedChange (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  Finsupp.lsum k fun m => if m % 2 = 0 then Finsupp.lsingle m else
    (Finsupp.lsingle m).comp (oldTwist D Sc cutoff (D.parity j.1) v t) +
    (Finsupp.lsingle (m - 1)).comp (offDiagonalDeltaCoefficient D Sc cutoff p j v t)

/-- Explicit inverse triangular coordinate change. -/
def offDiagonalCorrectedChangeInv (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  Finsupp.lsum k fun m => if m % 2 = 0 then Finsupp.lsingle m else
    (Finsupp.lsingle m).comp (oldTwist D Sc cutoff (D.parity j.1) v t) -
    ((Finsupp.lsingle (m - 1)).comp (offDiagonalDeltaCoefficient D Sc cutoff p j v t)).comp
      (oldTwist D Sc cutoff (D.parity j.1) v t)

private theorem corrected_change_single (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (q : ℕ) (b : Old D Sc cutoff v t) :
    offDiagonalCorrectedChange D Sc cutoff p j v t (Finsupp.single (2 * q) b) = Finsupp.single (2 * q) b ∧
    offDiagonalCorrectedChange D Sc cutoff p j v t (Finsupp.single (2 * q + 1) b) =
      Finsupp.single (2 * q + 1) (oldTwist D Sc cutoff (D.parity j.1) v t b) +
      Finsupp.single (2 * q) (offDiagonalDeltaCoefficient D Sc cutoff p j v t b) := by
  have he : 2 * q % 2 = 0 := by omega
  have ho : (2 * q + 1) % 2 ≠ 0 := by omega
  simp only [offDiagonalCorrectedChange, Finsupp.lsum_single, he, ite_true, ho, ite_false,
    LinearMap.add_apply, LinearMap.comp_apply, Finsupp.lsingle_apply, Nat.add_sub_cancel]
  exact ⟨trivial, trivial⟩

private theorem corrected_changeInv_single (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (q : ℕ) (b : Old D Sc cutoff v t) :
    offDiagonalCorrectedChangeInv D Sc cutoff p j v t (Finsupp.single (2 * q) b) = Finsupp.single (2 * q) b ∧
    offDiagonalCorrectedChangeInv D Sc cutoff p j v t (Finsupp.single (2 * q + 1) b) =
      Finsupp.single (2 * q + 1) (oldTwist D Sc cutoff (D.parity j.1) v t b) -
      Finsupp.single (2 * q) (offDiagonalDeltaCoefficient D Sc cutoff p j v t
        (oldTwist D Sc cutoff (D.parity j.1) v t b)) := by
  have he : 2 * q % 2 = 0 := by omega
  have ho : (2 * q + 1) % 2 ≠ 0 := by omega
  simp only [offDiagonalCorrectedChangeInv, Finsupp.lsum_single, he, ite_true, ho, ite_false,
    LinearMap.sub_apply, LinearMap.comp_apply, Finsupp.lsingle_apply, Nat.add_sub_cancel]
  exact ⟨trivial, trivial⟩

/-- The corrected coordinates give a genuine automorphism of all finite rows. -/
def offDiagonalCorrectedCoordinateEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) ≃ₗ[k] (ℕ →₀ Old D Sc cutoff v t) where
  toLinearMap := offDiagonalCorrectedChange D Sc cutoff p j v t
  invFun := offDiagonalCorrectedChangeInv D Sc cutoff p j v t
  left_inv f := by
    change offDiagonalCorrectedChangeInv D Sc cutoff p j v t
      (offDiagonalCorrectedChange D Sc cutoff p j v t f) = f
    induction f using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add f g hf hg => simp only [map_add, hf, hg]
    | single m b =>
      rcases (show ∃ q, m = 2 * q ∨ m = 2 * q + 1 from ⟨m / 2, by omega⟩) with ⟨q, h | h⟩
      · subst m
        rw [(corrected_change_single D Sc cutoff p j v t q b).1,
          (corrected_changeInv_single D Sc cutoff p j v t q b).1]
      · subst m
        rw [(corrected_change_single D Sc cutoff p j v t q b).2, map_add,
          (corrected_changeInv_single D Sc cutoff p j v t q _).2,
          (corrected_changeInv_single D Sc cutoff p j v t q _).1, offDiagonal_twist_twice, sub_add_cancel]
  right_inv f := by
    change offDiagonalCorrectedChange D Sc cutoff p j v t
      (offDiagonalCorrectedChangeInv D Sc cutoff p j v t f) = f
    induction f using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add f g hf hg => simp only [map_add, hf, hg]
    | single m b =>
      rcases (show ∃ q, m = 2 * q ∨ m = 2 * q + 1 from ⟨m / 2, by omega⟩) with ⟨q, h | h⟩
      · subst m
        rw [(corrected_changeInv_single D Sc cutoff p j v t q b).1,
          (corrected_change_single D Sc cutoff p j v t q b).1]
      · subst m
        rw [(corrected_changeInv_single D Sc cutoff p j v t q b).2, map_sub,
          (corrected_change_single D Sc cutoff p j v t q _).2,
          (corrected_change_single D Sc cutoff p j v t q _).1, offDiagonal_twist_twice, add_sub_cancel_right]

/-- The complete corrected coordinate equivalence is extracted from the actual
rho iterates on the bare-long class, at every degree and full old coefficient. -/
theorem offDiagonalCorrectedCoordinateEquiv_single (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ) (b : Old D Sc cutoff v t) :
    offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t (Finsupp.single m b) =
      offDiagonalLongExtraction D Sc cutoff p j.1 v t (offDiagonalCorrectedLift D Sc cutoff p j v t m b) := by
  change offDiagonalCorrectedChange D Sc cutoff p j v t (Finsupp.single m b) = _
  rcases (show ∃ q, m = 2 * q ∨ m = 2 * q + 1 from ⟨m / 2, by omega⟩) with ⟨q, h | h⟩
  · subst m
    rw [(corrected_change_single D Sc cutoff p j v t q b).1,
      (offDiagonalCorrectedLift_coordinates D Sc cutoff p j v t q b).1]
  · subst m
    rw [(corrected_change_single D Sc cutoff p j v t q b).2,
      (offDiagonalCorrectedLift_coordinates D Sc cutoff p j v t q b).2]

end OddMath.QuiverHecke.ELVOld
