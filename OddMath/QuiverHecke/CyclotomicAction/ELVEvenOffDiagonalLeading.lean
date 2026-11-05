import OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryLeading
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalLongTransport
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalCoefficientAction

/-! # Even polynomial-boundary leading maps on arbitrary old Homs

The parity-zero arbitrary-Hom transport in DeformedBoundaryDivision (5).
Generic bare-long output transport is iterated through the literal moving
dot. Actual C0P factorization and output covariance identify each full old
coefficient row with the independently computed even diagonal Phi row.
The leading map is a scalar unit times balance twist on Old(v,t).
No diagonal-corner sufficiency or even categorical inverse is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem evenMoving_act (i : I) (hi : D.parity i = 0) (v w t : List I)
    (g : hom D Sc cutoff w t) (z : Target D Sc cutoff i v w) :
    movingPowerTarget D Sc cutoff i v t 1 (by simp [hi]) (act D Sc cutoff i g z) =
      act D Sc cutoff i g (movingPowerTarget D Sc cutoff i v w 1 (by simp [hi]) z) := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  change projection D Sc cutoff i v t (_ ≫ (_ ≫ _)) =
    projection D Sc cutoff i v t ((_ ≫ _) ≫ _)
  rw [Category.assoc]

theorem evenMoving_iterate_act (i : I) (hi : D.parity i = 0) (v w t : List I)
    (g : hom D Sc cutoff w t) (d : ℕ) (z : Target D Sc cutoff i v w) :
    (movingPowerTarget D Sc cutoff i v t 1 (by simp [hi]))^[d] (act D Sc cutoff i g z) =
      act D Sc cutoff i g ((movingPowerTarget D Sc cutoff i v w 1 (by simp [hi]))^[d] z) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', ih, evenMoving_act D Sc cutoff i hi,
      Function.iterate_succ_apply']

theorem evenMoving_longSection_single_zero_iterate (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (d : ℕ) (c : Old D Sc cutoff v t) :
    (movingPowerTarget D Sc cutoff i v (t ++ [i]) 1 (by simp [hi]))^[d]
      (offDiagonalLongSection D Sc cutoff p i v t (Finsupp.single 0 c)) =
      offDiagonalLongSection D Sc cutoff p i v t (Finsupp.single d c) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', ih,
      evenMoving_offDiagonalLongSection D Sc cutoff p i hi, evenLongShift_single]

/-- The entire arbitrary-Hom row is the actual diagonal Phi row acting on its full coefficient. -/
theorem offDiagonalBoundary_even_rightAction (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (d : ℕ) (c : Old D Sc cutoff v t) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v t (Finsupp.single d c) =
      offDiagonalCoefficientRightAction D Sc cutoff i 0 v v t
        (oldTwist D Sc cutoff (p + D.parity i * wordSumParity D v) v t c)
        (evenBoundaryPhi D Sc cutoff p i v d) := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective c
  let g := twist k (p + D.parity i * wordSumParity D v) r
  let z := offDiagonalLongSection D Sc cutoff p i v v
    (Finsupp.single 0 ((ideal D Sc cutoff v v).mkQ (𝟙 _)))
  have hz : z = projection D Sc cutoff i v (v ++ [i]) (bareUFull D Sc cutoff i v) := by
    dsimp only [z]
    rw [offDiagonalLongSection_single_zero_pair, pair_id]
  have h0 := offDiagonalLongSection_zero_transport D Sc cutoff p i v t r
  rw [← ker_offDiagonalLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v t,
    LinearMap.mem_ker, map_sub, offDiagonalLongExtraction_section, sub_eq_zero] at h0
  have he0 : offDiagonalLongExtraction D Sc cutoff p i v t
      (act D Sc cutoff i (appendInsert D Sc cutoff i v t g) z) =
      Finsupp.single 0 ((ideal D Sc cutoff v t).mkQ r) := by
    rw [hz]
    exact h0
  have he : offDiagonalLongExtraction D Sc cutoff p i v t
      (act D Sc cutoff i (appendInsert D Sc cutoff i v t g)
        (offDiagonalLongSection D Sc cutoff p i v v
          (Finsupp.single d ((ideal D Sc cutoff v v).mkQ (𝟙 _))))) =
      Finsupp.single d ((ideal D Sc cutoff v t).mkQ r) := by
    rw [← evenMoving_longSection_single_zero_iterate D Sc cutoff p i hi v v d]
    rw [← evenMoving_iterate_act D Sc cutoff i hi,
      offDiagonalLongExtraction_evenMoving_iterate D Sc cutoff p i hi,
      he0, evenLongShift_iterate_single, Nat.add_zero]
  have hrow := congrArg (offDiagonalPolynomialBoundary D Sc cutoff p i v t) he
  have hphi := appendC0_pMap_offDiagonal D Sc cutoff p i v v
    (offDiagonalLongSection D Sc cutoff p i v v
      (Finsupp.single d ((ideal D Sc cutoff v v).mkQ (𝟙 _))))
  rw [offDiagonalLongExtraction_section] at hphi
  change _ = evenBoundaryPhi D Sc cutoff p i v d at hphi
  have hg : (ideal D Sc cutoff v t).mkQ g =
      oldTwist D Sc cutoff (p + D.parity i * wordSumParity D v) v t
        ((ideal D Sc cutoff v t).mkQ r) := rfl
  have hcov := appendC0_postcomp_general D Sc cutoff i v v t g
    (pMap D Sc cutoff i v (v ++ [i])
      (offDiagonalLongSection D Sc cutoff p i v v
        (Finsupp.single d ((ideal D Sc cutoff v v).mkQ (𝟙 _)))))
  rw [hg, hphi] at hcov
  calc
    offDiagonalPolynomialBoundary D Sc cutoff p i v t
        (Finsupp.single d ((ideal D Sc cutoff v t).mkQ r)) =
      appendC0 D Sc cutoff i v t
        (pMap D Sc cutoff i v (t ++ [i])
          (act D Sc cutoff i (appendInsert D Sc cutoff i v t g)
            (offDiagonalLongSection D Sc cutoff p i v v
              (Finsupp.single d ((ideal D Sc cutoff v v).mkQ (𝟙 _)))))) :=
      hrow.symm.trans (appendC0_pMap_offDiagonal D Sc cutoff p i v t _).symm
    _ = _ := by
      rw [pMap_postcomp]
      exact hcov

private theorem evenHom_twist_zero (v t : List I) (c : Old D Sc cutoff v t) :
    oldTwist D Sc cutoff 0 v t c = c := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective c
  change (ideal D Sc cutoff v t).mkQ (twist k 0 c) = _
  rw [twist_zero]

/-- Balance parity still twists the old coefficient even though the moving colour is even. -/
theorem offDiagonalBoundary_even_coefficient (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (d n : ℕ) (c : Old D Sc cutoff v t) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v t (Finsupp.single d c) n =
      oldComp D Sc cutoff v v t (evenBoundaryPhi D Sc cutoff p i v d n)
        (oldTwist D Sc cutoff p v t c) := by
  rw [offDiagonalBoundary_even_rightAction D Sc cutoff p i hi,
    offDiagonalCoefficientRightAction_apply]
  simp only [hi, nsmul_zero, zero_mul, add_zero, evenHom_twist_zero]

/-- Scalar-unit balance twist is an equivalence on every old Hom, including empty ones. -/
def evenOffDiagonalBoundaryLeadingEquiv (p : ZMod 2) (i : I) (v t : List I) :
    Old D Sc cutoff v t ≃ₗ[k] Old D Sc cutoff v t :=
  (LinearEquiv.ofInvolutive (oldTwist D Sc cutoff p v t)
    (oldTwist_twice D Sc cutoff p v t)).trans
      (LinearEquiv.smulOfUnit (appendQPProductUnit D Sc i v))

theorem offDiagonalBoundary_even_above (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (d n : ℕ) (c : Old D Sc cutoff v t)
    (hn : d + endpointQPDegree D cutoff i v < n + outputSDegree D i v) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v t (Finsupp.single d c) n = 0 := by
  rw [offDiagonalBoundary_even_coefficient D Sc cutoff p i hi,
    evenBoundaryPhi_above D Sc cutoff p i hi v d n hn, map_zero, LinearMap.zero_apply]

theorem offDiagonalBoundary_even_top (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) (d n : ℕ) (c : Old D Sc cutoff v t)
    (hn : n + outputSDegree D i v = d + endpointQPDegree D cutoff i v) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v t (Finsupp.single d c) n =
      evenOffDiagonalBoundaryLeadingEquiv D Sc cutoff p i v t c := by
  have hp := evenBoundaryPhi_top D Sc cutoff p i hi v d (by omega)
  have he : d + endpointQPDegree D cutoff i v - outputSDegree D i v = n := by omega
  rw [he] at hp
  rw [offDiagonalBoundary_even_coefficient D Sc cutoff p i hi, hp]
  change oldComp D Sc cutoff v v t
      ((appendQPProductUnit D Sc i v : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _))
      (oldTwist D Sc cutoff p v t c) =
    (appendQPProductUnit D Sc i v : k) • oldTwist D Sc cutoff p v t c
  rw [map_smul, LinearMap.smul_apply]
  congr 1
  obtain ⟨b, hb⟩ := (ideal D Sc cutoff v t).mkQ_surjective (oldTwist D Sc cutoff p v t c)
  rw [← hb, oldComp_mk, Category.id_comp]

end OddMath.QuiverHecke.ELVOld
