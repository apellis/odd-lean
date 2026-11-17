import OddMath.QuiverHecke.CyclotomicAction.BoundaryNumerator.BoundaryRowLeading
import OddMath.QuiverHecke.CyclotomicAction.OffDiagonalLong.OffDiagonalBoundary

/-!
# Off diagonal long

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The actual boundary leading map on arbitrary old Hom coefficients
The base long-section transport is iterated through the actual corrected
rho. Exact C0P factorization and actual output covariance identify every
corrected boundary coefficient with the existing diagonal Phi acting on
the entire off-diagonal coefficient. The specified scalar-unit leading map
therefore extends without a diagonal-corner sufficiency assumption.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELV
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem offDiagonalLongExtraction_rho_iterate (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (d : ℕ)
    (z : Target D Sc cutoff j.1 v (t ++ [j.1])) :
    offDiagonalLongExtraction D Sc cutoff p j.1 v t
      ((boundaryRho D Sc cutoff j v (t ++ [j.1]))^[d] z) =
    (offDiagonalCoefficientRho D Sc cutoff p j v t)^[d]
      (offDiagonalLongExtraction D Sc cutoff p j.1 v t z) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', offDiagonalLongExtraction_boundaryRho,
      ih, Function.iterate_succ_apply']

/-- The exact actual row on arbitrary corrected coefficients is transported
from the independently computed diagonal Phi row. -/
theorem offDiagonalBoundary_corrected_rightAction (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (d : ℕ)
    (c : Old D Sc cutoff v t) :
    offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t
      (offDiagonalLongExtraction D Sc cutoff p j.1 v t
        (offDiagonalCorrectedLift D Sc cutoff p j v t d c)) =
    offDiagonalCoefficientRightAction D Sc cutoff j.1 0 v v t
      (oldTwist D Sc cutoff (p + D.parity j.1 * wordSumParity D v) v t c)
      (outputBoundaryPhi D Sc cutoff p j v d) := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective c
  let g := twist k (p + D.parity j.1 * wordSumParity D v) r
  let z := outputLongSection D Sc cutoff p j.1 v
    (Finsupp.single 0 ((ideal D Sc cutoff v v).mkQ (𝟙 _)))
  have hz : z = projection D Sc cutoff j.1 v (v ++ [j.1])
      (bareUFull D Sc cutoff j.1 v) := by
    dsimp only [z]
    rw [outputLongSection_single, outputLongLift_zero_pair, pair_id]
  have h0 := offDiagonalLongSection_zero_transport D Sc cutoff p j.1 v t r
  rw [← ker_offDiagonalLongExtraction_eq_chronologicalShortSpan D Sc cutoff p j.1 v t,
    LinearMap.mem_ker, map_sub, offDiagonalLongExtraction_section, sub_eq_zero] at h0
  have he0 : offDiagonalLongExtraction D Sc cutoff p j.1 v t
      (act D Sc cutoff j.1 (appendInsert D Sc cutoff j.1 v t g) z) =
      Finsupp.single 0 ((ideal D Sc cutoff v t).mkQ r) := by
    rw [hz]
    exact h0
  have he : offDiagonalLongExtraction D Sc cutoff p j.1 v t
      (act D Sc cutoff j.1 (appendInsert D Sc cutoff j.1 v t g)
        (outputCorrectedLift D Sc cutoff p j v d ((ideal D Sc cutoff v v).mkQ (𝟙 _)))) =
      offDiagonalLongExtraction D Sc cutoff p j.1 v t
        (offDiagonalCorrectedLift D Sc cutoff p j v t d ((ideal D Sc cutoff v t).mkQ r)) := by
    have hstart : outputLongLift D Sc cutoff p j.1 v 0
        ((ideal D Sc cutoff v v).mkQ (𝟙 _)) = z :=
      (outputLongSection_single D Sc cutoff p j.1 v 0
        ((ideal D Sc cutoff v v).mkQ (𝟙 _))).symm
    rw [outputCorrectedLift, hstart]
    rw [← boundaryRho_iterate_act, offDiagonalLongExtraction_rho_iterate,
      he0, offDiagonalLongExtraction_correctedLift]
  have hrow := congrArg (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t) he
  have hphi : appendC0 D Sc cutoff j.1 v v
      (pMap D Sc cutoff j.1 v (v ++ [j.1])
        (outputCorrectedLift D Sc cutoff p j v d ((ideal D Sc cutoff v v).mkQ (𝟙 _)))) =
      outputBoundaryPhi D Sc cutoff p j v d :=
    appendC0_pMap D Sc cutoff p j v _
  have hg : (ideal D Sc cutoff v t).mkQ g =
      oldTwist D Sc cutoff (p + D.parity j.1 * wordSumParity D v) v t
        ((ideal D Sc cutoff v t).mkQ r) := rfl
  have hcov := appendC0_postcomp_general D Sc cutoff j.1 v v t g
    (pMap D Sc cutoff j.1 v (v ++ [j.1])
      (outputCorrectedLift D Sc cutoff p j v d ((ideal D Sc cutoff v v).mkQ (𝟙 _))))
  rw [hg, hphi] at hcov
  calc
    offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t
        (offDiagonalLongExtraction D Sc cutoff p j.1 v t
          (offDiagonalCorrectedLift D Sc cutoff p j v t d ((ideal D Sc cutoff v t).mkQ r))) =
      appendC0 D Sc cutoff j.1 v t
        (pMap D Sc cutoff j.1 v (t ++ [j.1])
          (act D Sc cutoff j.1 (appendInsert D Sc cutoff j.1 v t g)
            (outputCorrectedLift D Sc cutoff p j v d ((ideal D Sc cutoff v v).mkQ (𝟙 _))))) :=
      hrow.symm.trans (appendC0_pMap_offDiagonal D Sc cutoff p j.1 v t _).symm
    _ = _ := by
      rw [pMap_postcomp]
      exact hcov

private theorem hom_twist_add (a b : ZMod 2) (v t : List I)
    (c : Old D Sc cutoff v t) :
    oldTwist D Sc cutoff a v t (oldTwist D Sc cutoff b v t c) =
      oldTwist D Sc cutoff (a + b) v t c := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective c
  change (ideal D Sc cutoff v t).mkQ (twist k a (twist k b c)) = _
  rw [← twist_add]
  rfl

/-- The entire old coefficient is twisted; no right-linearity shortcut is used. -/
theorem offDiagonalBoundary_corrected_coefficient (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (d n : ℕ)
    (c : Old D Sc cutoff v t) :
    offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t
      (offDiagonalLongExtraction D Sc cutoff p j.1 v t
        (offDiagonalCorrectedLift D Sc cutoff p j v t d c)) n =
    oldComp D Sc cutoff v v t (outputBoundaryPhi D Sc cutoff p j v d n)
      (oldTwist D Sc cutoff
        (n • D.parity j.1 + (p + D.parity j.1 * wordSumParity D v)) v t c) := by
  rw [offDiagonalBoundary_corrected_rightAction, offDiagonalCoefficientRightAction_apply,
    zero_add, hom_twist_add]

/-- The prescribed leading equivalence on each arbitrary old Hom space. -/
def offDiagonalBoundaryLeadingEquiv (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (n : ℕ) :
    Old D Sc cutoff v t ≃ₗ[k] Old D Sc cutoff v t :=
  (LinearEquiv.ofInvolutive
    (oldTwist D Sc cutoff
      (n • D.parity j.1 + (p + D.parity j.1 * wordSumParity D v)) v t)
    (oldTwist_twice D Sc cutoff _ v t)).trans
      (LinearEquiv.smulOfUnit (outputBoundaryLeadingUnit D Sc cutoff j v))

theorem offDiagonalBoundary_corrected_above (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (d n : ℕ)
    (c : Old D Sc cutoff v t)
    (hn : d + endpointQPDegree D cutoff j.1 v < n + outputSDegree D j.1 v) :
    offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t
      (offDiagonalLongExtraction D Sc cutoff p j.1 v t
        (offDiagonalCorrectedLift D Sc cutoff p j v t d c)) n = 0 := by
  rw [offDiagonalBoundary_corrected_coefficient]
  have h := outputBoundary_corrected_above D Sc cutoff p j v d n
    ((ideal D Sc cutoff v v).mkQ (𝟙 _)) hn
  change outputBoundaryPhi D Sc cutoff p j v d n = 0 at h
  rw [h, map_zero, LinearMap.zero_apply]

theorem offDiagonalBoundary_corrected_top (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (d n : ℕ)
    (c : Old D Sc cutoff v t)
    (hn : n + outputSDegree D j.1 v = d + endpointQPDegree D cutoff j.1 v) :
    offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t
      (offDiagonalLongExtraction D Sc cutoff p j.1 v t
        (offDiagonalCorrectedLift D Sc cutoff p j v t d c)) n =
      offDiagonalBoundaryLeadingEquiv D Sc cutoff p j v t n c := by
  have ht := outputBoundary_corrected_top D Sc cutoff p j v d n
    ((ideal D Sc cutoff v v).mkQ (𝟙 _)) hn
  change outputBoundaryPhi D Sc cutoff p j v d n =
    outputBoundaryLeadingEquiv D Sc cutoff p j v n ((ideal D Sc cutoff v v).mkQ (𝟙 _)) at ht
  have hid : oldTwist D Sc cutoff
      (n • D.parity j.1 + (p + D.parity j.1 * wordSumParity D v)) v v
      ((ideal D Sc cutoff v v).mkQ (𝟙 _)) = (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
    change (ideal D Sc cutoff v v).mkQ (twist k _ (𝟙 _)) = _
    rw [twist_id]
  have hphi : outputBoundaryPhi D Sc cutoff p j v d n =
      (outputBoundaryLeadingUnit D Sc cutoff j v : k) •
        (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
    rw [ht]
    change (outputBoundaryLeadingUnit D Sc cutoff j v : k) •
      oldTwist D Sc cutoff
        (n • D.parity j.1 + (p + D.parity j.1 * wordSumParity D v)) v v
        ((ideal D Sc cutoff v v).mkQ (𝟙 _)) = _
    rw [hid]
  rw [offDiagonalBoundary_corrected_coefficient, hphi]
  change oldComp D Sc cutoff v v t
      ((outputBoundaryLeadingUnit D Sc cutoff j v : k) •
        (ideal D Sc cutoff v v).mkQ (𝟙 _))
      (oldTwist D Sc cutoff _ v t c) =
    (outputBoundaryLeadingUnit D Sc cutoff j v : k) • oldTwist D Sc cutoff _ v t c
  rw [map_smul, LinearMap.smul_apply]
  congr 1
  obtain ⟨b, hb⟩ := (ideal D Sc cutoff v t).mkQ_surjective
    (oldTwist D Sc cutoff
      (n • D.parity j.1 + (p + D.parity j.1 * wordSumParity D v)) v t c)
  rw [← hb, oldComp_mk, Category.id_comp]

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Corrected coordinate basis over arbitrary old Homs

The invertible source-coordinate change needed for off-diagonal row division
in DeformedBoundaryDivision (5). Its forward values are extracted from actual
corrected lifts, not postulated coordinate vectors. The full source delta
and entire old-coefficient twist are retained, including empty old Homs.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# Division and windows on arbitrary old Hom coefficients

Finite elimination uses the actual corrected-coordinate equivalence and the
proved leading maps on Old(v,t), retaining full exterior coefficients.
The resulting row normal forms feed the arbitrary-Hom snake argument.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELV
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The polynomial boundary in its proved corrected source coordinates. -/
def offDiagonalCorrectedBoundaryRow (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t).comp
    (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t).toLinearMap

@[simp] theorem offDiagonalCorrectedBoundaryRow_single (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (d : ℕ) (c : Old D Sc cutoff v t) :
    offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t (Finsupp.single d c) =
    offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t
      (offDiagonalLongExtraction D Sc cutoff p j.1 v t (offDiagonalCorrectedLift D Sc cutoff p j v t d c)) := by
  simp only [offDiagonalCorrectedBoundaryRow, LinearMap.comp_apply, LinearEquiv.coe_coe,
    offDiagonalCorrectedCoordinateEquiv_single]

/-- Exact low-window kernel, with the height difference left untruncated. -/
theorem offDiagonalCorrectedBoundaryRow_eq_zero_iff (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t f = 0 ↔
      ∀ d ∈ f.support, d + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v := by
  exact OddMath.Algebra.DegreeShiftRow.eq_zero_iff (offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t)
    (offDiagonalBoundaryLeadingEquiv D Sc cutoff p j v t) (outputSDegree D j.1 v) (endpointQPDegree D cutoff j.1 v)
    (by
      intro d n b hn
      rw [offDiagonalCorrectedBoundaryRow_single]
      exact offDiagonalBoundary_corrected_above D Sc cutoff p j v t d n b hn)
    (by
      intro d n b hn
      rw [offDiagonalCorrectedBoundaryRow_single]
      exact offDiagonalBoundary_corrected_top D Sc cutoff p j v t d n b hn) f

/-- In nonnegative height the polynomial boundary is injective. -/
theorem offDiagonalPolynomialBoundary_injective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    Function.Injective (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t) := by
  intro f g hfg
  have hf : offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t (f - g) = 0 := by
    have hs : offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t (f - g) =
        offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t f -
          offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t g :=
      map_sub (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t) f g
    exact hs.trans (sub_eq_zero.mpr hfg)
  let q := (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t).symm (f - g)
  have hq : offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t q = 0 := by
    simpa only [q, offDiagonalCorrectedBoundaryRow, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using hf
  have hb := (offDiagonalCorrectedBoundaryRow_eq_zero_iff D Sc cutoff p j v t q).mp hq
  have hq0 : q = 0 := by
    ext d
    by_contra hd
    have := hb d (Finsupp.mem_support_iff.mpr hd)
    omega
  have he := congrArg (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t) hq0
  apply sub_eq_zero.mp
  simpa only [q, LinearEquiv.apply_symm_apply, map_zero] using he

/-- Finite division by the boundary row. Quotients have no low-kernel coefficients. -/
theorem offDiagonalCorrectedBoundaryRow_division (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    ∃ q r : ℕ →₀ Old D Sc cutoff v t,
      offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t q + r = f ∧
      (∀ d ∈ q.support, outputSDegree D j.1 v ≤ d + endpointQPDegree D cutoff j.1 v) ∧
      (∀ n ∈ r.support, n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v) := by
  exact OddMath.Algebra.DegreeShiftRow.division (offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t)
    (offDiagonalBoundaryLeadingEquiv D Sc cutoff p j v t) (outputSDegree D j.1 v) (endpointQPDegree D cutoff j.1 v)
    (by
      intro d n b hn
      rw [offDiagonalCorrectedBoundaryRow_single]
      exact offDiagonalBoundary_corrected_above D Sc cutoff p j v t d n b hn)
    (by
      intro d n b hn
      rw [offDiagonalCorrectedBoundaryRow_single]
      exact offDiagonalBoundary_corrected_top D Sc cutoff p j v t d n b hn) f

/-- A high corrected input cannot map into the low output window. -/
theorem offDiagonalCorrectedBoundaryRow_separation (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (q r : ℕ →₀ Old D Sc cutoff v t)
    (hq : ∀ d ∈ q.support, outputSDegree D j.1 v ≤ d + endpointQPDegree D cutoff j.1 v)
    (hr : ∀ n ∈ r.support, n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v)
    (h : offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t q + r = 0) : q = 0 ∧ r = 0 := by
  exact OddMath.Algebra.DegreeShiftRow.separation (offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t)
    (offDiagonalBoundaryLeadingEquiv D Sc cutoff p j v t) (outputSDegree D j.1 v) (endpointQPDegree D cutoff j.1 v)
    (by
      intro d n b hn
      rw [offDiagonalCorrectedBoundaryRow_single]
      exact offDiagonalBoundary_corrected_above D Sc cutoff p j v t d n b hn)
    (by
      intro d n b hn
      rw [offDiagonalCorrectedBoundaryRow_single]
      exact offDiagonalBoundary_corrected_top D Sc cutoff p j v t d n b hn) q r hq hr h

/-- The allowed corrected-source quotient coefficients. -/
def offDiagonalBoundaryRowHigh (j : {j : I // D.parity j = 1}) (v t : List I) :
    Submodule k (ℕ →₀ Old D Sc cutoff v t) :=
  Finsupp.supported (Old D Sc cutoff v t) k
    {d | outputSDegree D j.1 v ≤ d + endpointQPDegree D cutoff j.1 v}

/-- The literal polynomial output window below the nonnegative height. -/
def offDiagonalBoundaryRowWindow (j : {j : I // D.parity j = 1}) (v t : List I) :
    Submodule k (ℕ →₀ Old D Sc cutoff v t) :=
  Finsupp.supported (Old D Sc cutoff v t) k
    {n | n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v}

/-- The forward division map uses the boundary itself and literal window inclusion. -/
def offDiagonalBoundaryRowAssembly (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    (offDiagonalBoundaryRowHigh D Sc cutoff j v t × offDiagonalBoundaryRowWindow D Sc cutoff j v t) →ₗ[k]
      (ℕ →₀ Old D Sc cutoff v t) :=
  ((offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t).comp (offDiagonalBoundaryRowHigh D Sc cutoff j v t).subtype).coprod
    (offDiagonalBoundaryRowWindow D Sc cutoff j v t).subtype

theorem offDiagonalBoundaryRowAssembly_bijective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) :
    Function.Bijective (offDiagonalBoundaryRowAssembly D Sc cutoff p j v t) := by
  exact OddMath.Algebra.DegreeShiftRow.assembly_bijective (offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t)
    (offDiagonalBoundaryLeadingEquiv D Sc cutoff p j v t) (outputSDegree D j.1 v) (endpointQPDegree D cutoff j.1 v)
    (by
      intro d n b hn
      rw [offDiagonalCorrectedBoundaryRow_single]
      exact offDiagonalBoundary_corrected_above D Sc cutoff p j v t d n b hn)
    (by
      intro d n b hn
      rw [offDiagonalCorrectedBoundaryRow_single]
      exact offDiagonalBoundary_corrected_top D Sc cutoff p j v t d n b hn) 

/-- Unique polynomial-row division in both height ranges. -/
def offDiagonalBoundaryRowDivisionEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    (offDiagonalBoundaryRowHigh D Sc cutoff j v t × offDiagonalBoundaryRowWindow D Sc cutoff j v t) ≃ₗ[k]
      (ℕ →₀ Old D Sc cutoff v t) :=
  LinearEquiv.ofBijective (offDiagonalBoundaryRowAssembly D Sc cutoff p j v t)
    (offDiagonalBoundaryRowAssembly_bijective D Sc cutoff p j v t)

/-- The normal form reconstructs with the prescribed row, not a surrogate map. -/
theorem offDiagonalBoundaryRowDivisionEquiv_apply (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (x : offDiagonalBoundaryRowHigh D Sc cutoff j v t × offDiagonalBoundaryRowWindow D Sc cutoff j v t) :
    offDiagonalBoundaryRowDivisionEquiv D Sc cutoff p j v t x =
      offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t
        (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t x.1) + x.2 := rfl

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# The polynomial boundary row in both height ranges

The positive assembly is the original boundary plus literal polynomial-window
inclusion. The negative assembly is the low corrected kernel plus the section
constructed by boundary-row division. Their inverses and the positive cokernel
are proved here. These row results feed the snake and augmented-inverse
arguments; they do not identify the prescribed balanced crossing-column domain.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELV
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The positive-height row with its literal polynomial-window columns. -/
def offDiagonalBoundaryPositiveAssembly (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    ((ℕ →₀ Old D Sc cutoff v t) × offDiagonalBoundaryRowWindow D Sc cutoff j v t) →ₗ[k]
      (ℕ →₀ Old D Sc cutoff v t) :=
  (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t).coprod
    (offDiagonalBoundaryRowWindow D Sc cutoff j v t).subtype

theorem offDiagonalBoundaryPositiveAssembly_bijective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    Function.Bijective (offDiagonalBoundaryPositiveAssembly D Sc cutoff p j v t) := by
  constructor
  · intro x y hxy
    have hz : offDiagonalBoundaryPositiveAssembly D Sc cutoff p j v t (x - y) = 0 := by
      rw [(offDiagonalBoundaryPositiveAssembly D Sc cutoff p j v t).map_sub x y, hxy, sub_self]
    change offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t (x - y).1 + (x - y).2 = 0 at hz
    let q := (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t).symm (x - y).1
    have hh := offDiagonalCorrectedBoundaryRow_separation D Sc cutoff p j v t q (x - y).2
      (fun d _ => by omega) (fun n hn => (x - y).2.property hn)
      (by simpa only [q, offDiagonalCorrectedBoundaryRow, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using hz)
    apply sub_eq_zero.mp
    apply Prod.ext
    · change (x - y).1 = 0
      have he := congrArg (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t) hh.1
      simpa only [q, LinearEquiv.apply_symm_apply, map_zero] using he
    · exact Subtype.ext hh.2
  · intro f
    obtain ⟨q, r, he, _, hr⟩ := offDiagonalCorrectedBoundaryRow_division D Sc cutoff p j v t f
    refine ⟨(offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t q, ⟨r, fun _ hn => hr _ hn⟩), ?_⟩
    exact he

/-- Positive-height direct sum using the original polynomial boundary as its first entry. -/
def offDiagonalBoundaryPositiveEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    ((ℕ →₀ Old D Sc cutoff v t) × offDiagonalBoundaryRowWindow D Sc cutoff j v t) ≃ₗ[k]
      (ℕ →₀ Old D Sc cutoff v t) :=
  LinearEquiv.ofBijective (offDiagonalBoundaryPositiveAssembly D Sc cutoff p j v t)
    (offDiagonalBoundaryPositiveAssembly_bijective D Sc cutoff p j v t h)

@[simp] theorem offDiagonalBoundaryPositiveEquiv_apply (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v)
    (x : (ℕ →₀ Old D Sc cutoff v t) × offDiagonalBoundaryRowWindow D Sc cutoff j v t) :
    offDiagonalBoundaryPositiveEquiv D Sc cutoff p j v t h x =
      offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t x.1 + x.2 := rfl

/-- The low window in corrected source coordinates. -/
def offDiagonalBoundaryKernelWindow (j : {j : I // D.parity j = 1}) (v t : List I) :
    Submodule k (ℕ →₀ Old D Sc cutoff v t) :=
  Finsupp.supported (Old D Sc cutoff v t) k
    {d | d + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v}

/-- Inclusion of the low corrected window into the kernel of the original row. -/
def offDiagonalBoundaryKernelInclusion (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    offDiagonalBoundaryKernelWindow D Sc cutoff j v t →ₗ[k]
      LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t) :=
  (((offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t).toLinearMap).comp
    (offDiagonalBoundaryKernelWindow D Sc cutoff j v t).subtype).codRestrict _ (by
      intro f
      exact (offDiagonalCorrectedBoundaryRow_eq_zero_iff D Sc cutoff p j v t f).mpr (fun d hd => f.property hd))

/-- The low corrected window is precisely the kernel, in both directions. -/
def offDiagonalBoundaryKernelEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    offDiagonalBoundaryKernelWindow D Sc cutoff j v t ≃ₗ[k]
      LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t) :=
  LinearEquiv.ofBijective (offDiagonalBoundaryKernelInclusion D Sc cutoff p j v t) (by
    constructor
    · intro f g hfg
      apply Subtype.ext
      apply (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t).injective
      exact congrArg Subtype.val hfg
    · intro f
      let g := (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t).symm f.val
      have hg : offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t g = 0 := by
        simpa only [g, offDiagonalCorrectedBoundaryRow, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply] using (LinearMap.mem_ker.mp f.property)
      refine ⟨⟨g, fun d hd => (offDiagonalCorrectedBoundaryRow_eq_zero_iff D Sc cutoff p j v t g).mp hg d hd⟩, ?_⟩
      apply Subtype.ext
      change offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t g = f.val
      exact LinearEquiv.apply_symm_apply _ _)

/-- The section obtained by the proved row division, with zero low-source part. -/
def offDiagonalBoundaryRowSection (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t).toLinearMap.comp
    ((offDiagonalBoundaryRowHigh D Sc cutoff j v t).subtype.comp
      ((LinearMap.fst k _ _).comp (offDiagonalBoundaryRowDivisionEquiv D Sc cutoff p j v t).symm.toLinearMap))

theorem offDiagonalBoundaryRowSection_rightInverse (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t (offDiagonalBoundaryRowSection D Sc cutoff p j v t f) = f := by
  let x := (offDiagonalBoundaryRowDivisionEquiv D Sc cutoff p j v t).symm f
  have hx : (x.2 : ℕ →₀ Old D Sc cutoff v t) = 0 := by
    ext n
    by_contra hn
    have hh := x.2.property (Finsupp.mem_support_iff.mpr hn)
    change n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v at hh
    omega
  have he := (offDiagonalBoundaryRowDivisionEquiv D Sc cutoff p j v t).apply_symm_apply f
  rw [offDiagonalBoundaryRowDivisionEquiv_apply] at he
  change offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t
    (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t x.1) + x.2 = f at he
  rw [hx, add_zero] at he
  exact he

/-- At height a the remainder is exactly the polynomial window of degrees below a. -/
theorem offDiagonalBoundaryRowWindow_eq_height (j : {j : I // D.parity j = 1}) (v t : List I)
    (a : ℕ) (ha : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + a) :
    offDiagonalBoundaryRowWindow D Sc cutoff j v t =
      Finsupp.supported (Old D Sc cutoff v t) k (Set.Iio a) := by
  unfold offDiagonalBoundaryRowWindow
  congr 1
  ext n
  change (n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v) ↔ n < a
  omega

theorem offDiagonalBoundaryPositiveEquiv_symm_boundary (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    (offDiagonalBoundaryPositiveEquiv D Sc cutoff p j v t h).symm
      (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t f) = (f, 0) := by
  apply (offDiagonalBoundaryPositiveEquiv D Sc cutoff p j v t h).injective
  rw [LinearEquiv.apply_symm_apply, offDiagonalBoundaryPositiveEquiv_apply]
  exact (add_zero _).symm

end OddMath.QuiverHecke.ELV
end

end
