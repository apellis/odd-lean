import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalLongTransport
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalBoundary
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalRhoExtraction
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalCoefficientAction
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryRowLeading

/-! # The actual boundary leading map on arbitrary old Hom coefficients
The base long-section transport is iterated through the actual corrected
rho. Exact C0P factorization and actual output covariance identify every
corrected boundary coefficient with the existing diagonal Phi acting on
the entire off-diagonal coefficient. The specified scalar-unit leading map
therefore extends without a diagonal-corner sufficiency assumption.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
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
    change offDiagonalLongExtraction D Sc cutoff p j.1 v t
      (act D Sc cutoff j.1 (appendInsert D Sc cutoff j.1 v t g)
        ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[d] z)) = _
    rw [← boundaryRho_iterate_act, offDiagonalLongExtraction_rho_iterate,
      he0, offDiagonalLongExtraction_correctedLift]
  have hrow := congrArg (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t) he
  rw [← appendC0_pMap_offDiagonal, ← appendC0_pMap_offDiagonal,
    pMap_postcomp, appendC0_postcomp_general, appendC0_pMap D Sc cutoff p j v] at hrow
  exact hrow.symm

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
  obtain ⟨b, hb⟩ := (ideal D Sc cutoff v t).mkQ_surjective (oldTwist D Sc cutoff _ v t c)
  rw [← hb, oldComp_mk, Category.id_comp]

end OddMath.QuiverHecke.ELVOld
