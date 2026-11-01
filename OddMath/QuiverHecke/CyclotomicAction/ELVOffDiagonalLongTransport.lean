import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalLongCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputOrderBalance
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputCompatibleLifts

/-! # Base long-section transport to arbitrary output arrows

The off-diagonal long section in degree zero is the literal bare-long pair.
The full-coefficient bare-long transport gives its comparison with the
diagonal section modulo the actual chronological short span. Corrected rho
commutes with arbitrary target postcomposition by associativity.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem castPair_heq (p : ZMod 2) (i : I) {v t w s s' : List I}
    (e : s = t) (e' : s' = t)
    (f : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D w))
    (g : (pres D Sc).obj (ob D (i :: s')) ⟶ (pres D Sc).obj (ob D w))
    (h : HEq f g) :
    Eq.mp (congrArg (fun a => Old D Sc cutoff v a →ₗ[k] Target D Sc cutoff i v w) e)
      (pair D Sc cutoff p i ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f)) =
    Eq.mp (congrArg (fun a => Old D Sc cutoff v a →ₗ[k] Target D Sc cutoff i v w) e')
      (pair D Sc cutoff p i ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] g)) := by
  subst s
  subst s'
  cases h
  rfl

theorem longHomLift_zero_pair (p : ZMod 2) (i : I) {v t : List I}
    (y : NFIdx v t) (b : Old D Sc cutoff v t) :
    longHomLift D Sc cutoff p i y 0 b =
      pair D Sc cutoff p i (bareUFull D Sc cutoff i t) b := by
  let z : PrependIdx i t (t ++ [i]) := longOutputIndex i t 0
  let y' : NFIdx v z.oldTarget := (longOutputIndex_oldTarget i t 0).symm ▸ y
  have hr := prependTail_rebase D Sc (i := i) (v := v) (s := t) (w := t ++ [i]) z y'
  have ht : HEq (prependTail D Sc (longHomIndex i y 0))
      (OutputOldComposite.bareU D Sc i t) :=
    hr.trans (tail_long_zero D Sc i t)
  have h := castPair_heq D Sc cutoff p i (v := v)
    (longHomIndex_oldTarget i y 0) rfl _ _ ht
  have hv := congrArg (fun f : Old D Sc cutoff v t →ₗ[k]
    Target D Sc cutoff i v (t ++ [i]) => f b) h
  simpa only [longHomLift, pow_zero, one_smul, bareUFull] using hv

theorem offDiagonalLongSection_single_zero_pair (p : ZMod 2) (i : I) (v t : List I)
    (b : Old D Sc cutoff v t) :
    offDiagonalLongSection D Sc cutoff p i v t (Finsupp.single 0 b) =
      pair D Sc cutoff p i (bareUFull D Sc cutoff i t) b := by
  by_cases h : Nonempty (NFIdx v t)
  · let y := Classical.choice h
    rw [offDiagonalLongSection_eq D Sc cutoff p i y, longHomSection,
      Finsupp.lsum_single, longHomLift_zero_pair]
  · rw [old_eq_zero_of_no_normal_form D Sc cutoff h b]
    simp only [Finsupp.single_zero, map_zero]

theorem outputLongLift_zero_pair (p : ZMod 2) (i : I) (v : List I)
    (b : Old D Sc cutoff v v) :
    outputLongLift D Sc cutoff p i v 0 b =
      pair D Sc cutoff p i (bareUFull D Sc cutoff i v) b := by
  have h := castPair_heq D Sc cutoff p i (v := v)
    (longOutputIndex_oldTarget i v 0) rfl _ _ (tail_long_zero D Sc i v)
  have hv := congrArg (fun f : Old D Sc cutoff v v →ₗ[k]
    Target D Sc cutoff i v (v ++ [i]) => f b) h
  simpa only [outputLongLift, pow_zero, one_smul, bareUFull] using hv

/-- The source balance and bare-long parity determine the whole output twist. -/
theorem offDiagonalLongSection_zero_transport (p : ZMod 2) (i : I) (v t : List I)
    (r : hom D Sc cutoff v t) :
    projection D Sc cutoff i v (t ++ [i])
      (bareUFull D Sc cutoff i v ≫ appendInsert D Sc cutoff i v t
        (twist k (p + D.parity i * wordSumParity D v) r)) -
      offDiagonalLongSection D Sc cutoff p i v t
        (Finsupp.single 0 ((ideal D Sc cutoff v t).mkQ r)) ∈
      chronologicalShortSpan D Sc cutoff i v t := by
  rw [offDiagonalLongSection_single_zero_pair, pair_mk]
  have hp : D.parity i * wordSumParity D v +
      (p + D.parity i * wordSumParity D v) = p := by
    calc
      _ = p + (D.parity i * wordSumParity D v + D.parity i * wordSumParity D v) := by abel
      _ = p := by rw [Supercategory.zmod2_add_self, add_zero]
  have he : twist k (D.parity i * wordSumParity D v)
      (twist k (p + D.parity i * wordSumParity D v) r) = twist k p r := by
    rw [← twist_add, hp]
  have h := bareUFull_transport D Sc cutoff i
    (twist k (p + D.parity i * wordSumParity D v) r)
  rwa [he, map_sub] at h

theorem boundaryRho_act (j : {j : I // D.parity j = 1}) (v w t : List I)
    (g : hom D Sc cutoff w t) (z : Target D Sc cutoff j.1 v w) :
    boundaryRho D Sc cutoff j v t (act D Sc cutoff j.1 g z) =
      act D Sc cutoff j.1 g (boundaryRho D Sc cutoff j v w z) := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff j.1 v w z
  change SKM.zsign k (D.parity j.1 * wordSumParity D v) •
      projection D Sc cutoff j.1 v t (boundaryFirstDot D Sc cutoff j v ≫ (h ≫ g)) =
    act D Sc cutoff j.1 g
      (SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        projection D Sc cutoff j.1 v w (boundaryFirstDot D Sc cutoff j v ≫ h))
  rw [map_smul]
  congr 1
  change projection D Sc cutoff j.1 v t (_ ≫ (_ ≫ _)) =
    projection D Sc cutoff j.1 v t ((_ ≫ _) ≫ _)
  rw [Category.assoc]

theorem boundaryRho_iterate_act (j : {j : I // D.parity j = 1}) (v w t : List I)
    (g : hom D Sc cutoff w t) (d : ℕ) (z : Target D Sc cutoff j.1 v w) :
    (boundaryRho D Sc cutoff j v t)^[d] (act D Sc cutoff j.1 g z) =
      act D Sc cutoff j.1 g ((boundaryRho D Sc cutoff j v w)^[d] z) := by
  induction d with
  | zero => rfl
  | succ d ih => rw [Function.iterate_succ_apply', ih, boundaryRho_act,
      Function.iterate_succ_apply']

end OddMath.QuiverHecke.ELVOld
