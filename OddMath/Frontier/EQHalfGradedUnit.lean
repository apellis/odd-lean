import OddMath.Frontier.EQSmallRankQuasiIso
import DG.HalfGraded.Diagonal
import DG.Bigraded.DegreeZero

/-!
# The actual integral unit functor on half-graded weight categories

Regrade the original unit inclusion `ℤ → OPol_N` on every homogeneous component,
retaining the cohomological degree, weight, multiplication and differential.
This constructs the actual dg functor on weight categories, not a new action
transported from a desired equivalence. It exists in every rank. The ordinary
low-rank quasi-isomorphism alone is not asserted to prove this functor is a
quasi-equivalence; that requires a separate weightwise cohomology comparison.
-/

noncomputable section
namespace OddMath.Frontier.EQHalfGradedUnit
open DG DG.HalfGradedDGRing EQSkewDifferential CategoryTheory
open scoped DG.DegreeZero

abbrev source : HalfGradedDGRing ℤ 2 := ofDGRing ℤ
abbrev target (N : ℕ) : HalfGradedDGRing (OPol N) 2 := ofDGRing (OPol N)

/-- The actual integer inclusion preserves the diagonal half-grading. -/
theorem intCast_mem {N : ℕ} {p : ℤ × ZMod 2} {z : ℤ}
    (hz : z ∈ source.hgrading p) : (z : OPol N) ∈ (target N).hgrading p := by
  refine Diagonal.induction_on hz (by simp)
    (fun n z hz hn => ?_) (fun a b ha hb => by simpa only [Int.cast_add] using add_mem ha hb)
  rw [← hn]
  exact Diagonal.mem_grading ((EQSmallRankDG.intInclusion N).map_mem hz)

/-- Apply the integer inclusion to each actual placed component. -/
def regradedMap (N : ℕ) : source.Regraded →+ (target N).Regraded :=
  DirectSum.toAddMonoid fun p =>
    { toFun := fun z => (target N).place p (z.1 : OPol N) (intCast_mem z.2)
      map_zero' := by
        change (target N).place p ((0 : ℤ) : OPol N) _ = 0
        simp
      map_add' := by
        intro a b
        change (target N).place p (((a.1 + b.1 : ℤ) : OPol N)) _ = _
        exact (place_congr rfl (Int.cast_add a.1 b.1) _ _).trans
          (place_add p (intCast_mem a.2) (intCast_mem b.2)) }

@[simp]
theorem regradedMap_place (N : ℕ) (p : ℤ × ℤ) (z : ℤ)
    (hz : z ∈ source.hgrading (halfDegree 2 p)) :
    regradedMap N (source.place p z hz) =
      (target N).place p (z : OPol N) (intCast_mem hz) :=
  DirectSum.toAddMonoid_of _ _ _

theorem regradedMap_mul (N : ℕ) (x y : source.Regraded) :
    regradedMap N (x * y) = regradedMap N x * regradedMap N y := by
  induction x using HalfGradedDGRing.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
  | mk p a ha =>
    induction y using HalfGradedDGRing.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
    | mk q b hb =>
      rw [place_mul_place, regradedMap_place, regradedMap_place, regradedMap_place,
        place_mul_place]
      exact place_congr rfl (Int.cast_mul a b) _ _

theorem regradedMap_grading (N : ℕ) {n : ℤ} {x : source.Regraded}
    (hx : x ∈ DG.grading n) : regradedMap N x ∈ DG.grading n := by
  refine HalfGradedDGRing.grading_induction
    (P := fun x => regradedMap N x ∈ DG.grading n) (by simp)
    (fun w z hz => ?_) (fun a b ha hb => by simpa only [map_add] using add_mem ha hb) hx
  rw [regradedMap_place]
  exact place_mem_grading (n, w) _

theorem regradedMap_weight (N : ℕ) {w : ℤ} {x : source.Regraded}
    (hx : x ∈ wgrading w) : regradedMap N x ∈ wgrading w := by
  refine HalfGradedDGRing.wgrading_induction
    (P := fun x => regradedMap N x ∈ wgrading w) (by simp)
    (fun n z hz => ?_) (fun a b ha hb => by simpa only [map_add] using add_mem ha hb) hx
  rw [regradedMap_place]
  exact place_mem_wgrading (n, w) _

theorem regradedMap_d (N : ℕ) (x : source.Regraded) :
    regradedMap N (DG.d x) = DG.d (regradedMap N x) := by
  induction x using HalfGradedDGRing.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | mk p z hz =>
    rw [d_place, regradedMap_place, regradedMap_place, d_place]
    exact place_congr rfl ((EQSmallRankDG.intInclusion N).map_d z) _ _

/-- The actual unit inclusion on regraded rings is a dg-ring homomorphism. -/
def regradedHom (N : ℕ) : source.Regraded →ᵈᵍ+* (target N).Regraded where
  __ := regradedMap N
  map_one' := by
    change regradedMap N 1 = 1
    rw [source.one_eq_place, regradedMap_place, (target N).one_eq_place]
    exact place_congr rfl (Int.cast_one) _ _
  map_mul' := regradedMap_mul N
  map_mem' := regradedMap_grading N
  map_d' := regradedMap_d N

/-- The induced additive dg functor is identity on weights and the unit map on Hom. -/
def weightFunctor (N : ℕ) : WeightCategory source.Regraded ⥤
    WeightCategory (target N).Regraded :=
  WeightCategory.mapFunctor (regradedHom N) (regradedMap_weight N)

instance (N : ℕ) : (weightFunctor N).Additive := inferInstanceAs
  (WeightCategory.mapFunctor (regradedHom N) (regradedMap_weight N)).Additive

instance (N : ℕ) : (weightFunctor N).IsDGFunctor := inferInstanceAs
  (WeightCategory.mapFunctor (regradedHom N) (regradedMap_weight N)).IsDGFunctor

@[simp]
theorem weightFunctor_map_val (N : ℕ) {X Y : WeightCategory source.Regraded}
    (f : X ⟶ Y) : ((weightFunctor N).map f).1 = regradedMap N f.1 := rfl

/-- The periodicity unit is the actual placed unit on both sides. -/
@[simp]
theorem regradedHom_periodUnit (N : ℕ) :
    regradedHom N source.periodUnit = (target N).periodUnit := by
  change regradedMap N source.periodUnit = (target N).periodUnit
  rw [periodUnit, regradedMap_place, periodUnit]
  exact place_congr rfl Int.cast_one _ _

/-- The inverse periodicity unit is preserved as well. -/
@[simp]
theorem regradedHom_periodUnitInv (N : ℕ) :
    regradedHom N source.periodUnitInv = (target N).periodUnitInv := by
  change regradedMap N source.periodUnitInv = (target N).periodUnitInv
  rw [periodUnitInv, regradedMap_place, periodUnitInv]
  exact place_congr rfl Int.cast_one _ _

end OddMath.Frontier.EQHalfGradedUnit
