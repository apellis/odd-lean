import OddMath.QuiverHecke.CyclotomicAction.ELVOutputLongExtraction
import OddMath.QuiverHecke.CyclotomicAction.ELVMovingShift

/-! # Long coordinates with different old source and target

The first off-diagonal prerequisite of `DeformedMackeyBoundary.md` (2).
An existing old normal-form index selects a long tail with arbitrary old
source and target. Extraction and reconstruction retain the entire old Hom,
not just its endomorphism ring. The supplied old index is an intermediate
hypothesis; canonical regrouping and independence of that index remain separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Rebase the canonical long tail by an existing old normal form. -/
def longHomIndex (i : I) {v t : List I} (y : NFIdx v t) (m : ℕ) :
    PrependIdx i v (t ++ [i]) :=
  (longOutputIndex i t m).rebase ((longOutputIndex_oldTarget i t m).symm ▸ y)

@[simp] theorem longHomIndex_oldTarget (i : I) {v t : List I}
    (y : NFIdx v t) (m : ℕ) : (longHomIndex i y m).oldTarget = t :=
  (PrependIdx.rebase_target _ _).trans (longOutputIndex_oldTarget i t m)

@[simp] theorem longHomIndex_exponent (i : I) {v t : List I}
    (y : NFIdx v t) (m : ℕ) : (longHomIndex i y m).1.1 = m := rfl

/-- The source-normalized coefficient of a long off-diagonal tail. -/
def longHomCoordinate (p : ZMod 2) (i : I) {v t : List I} (y : NFIdx v t) (m : ℕ) :
    Target D Sc cutoff i v (t ++ [i]) →ₗ[k] Old D Sc cutoff v t :=
  Eq.mp (congrArg (fun s => Target D Sc cutoff i v (t ++ [i]) →ₗ[k]
      Old D Sc cutoff v s) (longHomIndex_oldTarget i y m))
    ((SKM.zsign k (D.parity i * wordSumParity D v)) ^ m •
      prependOldCoordinate D Sc cutoff p (longHomIndex i y m))

/-- The corresponding lift accepts an arbitrary full off-diagonal old class. -/
def longHomLift (p : ZMod 2) (i : I) {v t : List I} (y : NFIdx v t) (m : ℕ) :
    Old D Sc cutoff v t →ₗ[k] Target D Sc cutoff i v (t ++ [i]) :=
  (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m •
    Eq.mp (congrArg (fun s => Old D Sc cutoff v s →ₗ[k]
      Target D Sc cutoff i v (t ++ [i])) (longHomIndex_oldTarget i y m))
      (pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc (longHomIndex i y m)))

@[simp] theorem longHomCoordinate_lift (p : ZMod 2) (i : I) {v t : List I}
    (y : NFIdx v t) (m : ℕ) (b : Old D Sc cutoff v t) :
    longHomCoordinate D Sc cutoff p i y m (longHomLift D Sc cutoff p i y m b) = b := by
  have transport {s s' : List I} (e : s = s')
      (f : Target D Sc cutoff i v (t ++ [i]) →ₗ[k] Old D Sc cutoff v s)
      (g : Old D Sc cutoff v s →ₗ[k] Target D Sc cutoff i v (t ++ [i]))
      (h : ∀ b, f (g b) = b) (a : k) (ha : a * a = 1)
      (b : Old D Sc cutoff v s') :
      (Eq.mp (congrArg (fun s => Target D Sc cutoff i v (t ++ [i]) →ₗ[k]
        Old D Sc cutoff v s) e) (a • f))
        (a • (Eq.mp (congrArg (fun s => Old D Sc cutoff v s →ₗ[k]
          Target D Sc cutoff i v (t ++ [i])) e) g) b) = b := by
    subst s'
    change a • f (a • g b) = b
    rw [map_smul, h, smul_smul, ha, one_smul]
  exact transport (longHomIndex_oldTarget i y m) _ _
    (prependOldCoordinate_pair D Sc cutoff p (longHomIndex i y m)) _
    (by rw [← mul_pow, SKM.zsign_mul_self', one_pow]) b

 theorem longHomCoordinate_lift_off (p : ZMod 2) (i : I) {v t : List I}
    (y : NFIdx v t) (m n : ℕ) (hmn : m ≠ n) (b : Old D Sc cutoff v t) :
    longHomCoordinate D Sc cutoff p i y m (longHomLift D Sc cutoff p i y n b) = 0 := by
  have transport {s s' : List I} (e : s = t) (e' : s' = t)
      (f : Target D Sc cutoff i v (t ++ [i]) →ₗ[k] Old D Sc cutoff v s)
      (g : Old D Sc cutoff v s' →ₗ[k] Target D Sc cutoff i v (t ++ [i]))
      (h : ∀ b, f (g b) = 0) (a c : k) (b : Old D Sc cutoff v t) :
      (Eq.mp (congrArg (fun s => Target D Sc cutoff i v (t ++ [i]) →ₗ[k]
        Old D Sc cutoff v s) e) (a • f))
        (c • (Eq.mp (congrArg (fun s => Old D Sc cutoff v s →ₗ[k]
          Target D Sc cutoff i v (t ++ [i])) e') g) b) = 0 := by
    subst s
    subst s'
    change a • f (c • g b) = 0
    rw [map_smul, h, smul_zero, smul_zero]
  exact transport (longHomIndex_oldTarget i y m) (longHomIndex_oldTarget i y n) _ _
    (prependOldCoordinate_pair_off D Sc cutoff p (longHomIndex i y m)
      (longHomIndex i y n) (fun h => hmn (congrArg Prod.fst h))) _ _ b

private theorem castHomCoordinate_zero (i : I) {v t s s' : List I} (e : s = s')
    (f : Target D Sc cutoff i v (t ++ [i]) →ₗ[k] Old D Sc cutoff v s)
    (z : Target D Sc cutoff i v (t ++ [i])) (hz : f z = 0) :
    (Eq.mp (congrArg (fun s => Target D Sc cutoff i v (t ++ [i]) →ₗ[k]
      Old D Sc cutoff v s) e) f) z = 0 := by
  cases e
  exact hz

/-- Finiteness follows from the actual affine PBW support of a quotient representative. -/
theorem longHomCoordinate_finite_support (p : ZMod 2) (i : I) {v t : List I}
    (y : NFIdx v t) (z : Target D Sc cutoff i v (t ++ [i])) :
    ∃ N : ℕ, ∀ m, N ≤ m → longHomCoordinate D Sc cutoff p i y m z = 0 := by
  obtain ⟨f, rfl⟩ := projection_surjective D Sc cutoff i v (t ++ [i]) z
  let c := prependAffineEquiv D Sc cutoff i v (t ++ [i]) f
  refine ⟨c.support.sup (fun x => x.1.1) + 1, ?_⟩
  intro m hm
  unfold longHomCoordinate
  apply castHomCoordinate_zero D Sc cutoff i (longHomIndex_oldTarget i y m)
  rw [LinearMap.smul_apply]
  suffices hz : prependOldCoordinate D Sc cutoff p (longHomIndex i y m)
      (projection D Sc cutoff i v (t ++ [i]) f) = 0 by rw [hz, smul_zero]
  rw [prependOldCoordinate_projection]
  have he : Finsupp.lcomapDomain (R := k) (longHomIndex i y m).replaceOld
      (longHomIndex i y m).replaceOld_injective c = 0 := by
    ext b
    simp only [Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply, Finsupp.zero_apply]
    apply Finsupp.notMem_support_iff.mp
    intro hb
    have hd := Finset.le_sup (f := fun x : PrependIdx i v (t ++ [i]) => x.1.1) hb
    have hdegree : ((longHomIndex i y m).replaceOld b).1.1 = m := rfl
    rw [hdegree] at hd
    omega
  change (ideal D Sc cutoff v (longHomIndex i y m).oldTarget).mkQ
    (prependExtractOld D Sc cutoff p (longHomIndex i y m) f) = 0
  unfold prependExtractOld
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  change (ideal D Sc cutoff v (longHomIndex i y m).oldTarget).mkQ
    ((twist k p) ((oldAffineEquiv D Sc cutoff v (longHomIndex i y m).oldTarget).symm
      ((Finsupp.mapRange.linearMap (coefficientTwist D cutoff
        (prependTailParity D (longHomIndex i y m))))
        (Finsupp.lcomapDomain (R := k) (longHomIndex i y m).replaceOld
          (longHomIndex i y m).replaceOld_injective c)))) = 0
  rw [he, map_zero, map_zero, map_zero, map_zero]

/-- The actual finite off-diagonal polynomial row. -/
def longHomExtraction (p : ZMod 2) (i : I) {v t : List I} (y : NFIdx v t) :
    Target D Sc cutoff i v (t ++ [i]) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) where
  toFun z := Finsupp.ofSupportFinite
    (fun m => longHomCoordinate D Sc cutoff p i y m z) (by
      obtain ⟨N, hN⟩ := longHomCoordinate_finite_support D Sc cutoff p i y z
      apply (Finset.finite_toSet (Finset.range N)).subset
      intro m hm
      simp only [Finset.mem_coe, Finset.mem_range]
      by_contra h
      exact hm (hN m (by omega)))
  map_add' z z' := by
    ext m
    exact (longHomCoordinate D Sc cutoff p i y m).map_add z z'
  map_smul' c z := by
    ext m
    exact (longHomCoordinate D Sc cutoff p i y m).map_smul c z

@[simp] theorem longHomExtraction_apply (p : ZMod 2) (i : I) {v t : List I}
    (y : NFIdx v t) (z : Target D Sc cutoff i v (t ++ [i])) (m : ℕ) :
    longHomExtraction D Sc cutoff p i y z m = longHomCoordinate D Sc cutoff p i y m z := rfl

/-- The normalized canonical tails give a concrete section of the finite row. -/
def longHomSection (p : ZMod 2) (i : I) {v t : List I} (y : NFIdx v t) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] Target D Sc cutoff i v (t ++ [i]) :=
  Finsupp.lsum k (longHomLift D Sc cutoff p i y)

@[simp] theorem longHomExtraction_lift (p : ZMod 2) (i : I) {v t : List I}
    (y : NFIdx v t) (m : ℕ) (b : Old D Sc cutoff v t) :
    longHomExtraction D Sc cutoff p i y (longHomLift D Sc cutoff p i y m b) =
      Finsupp.single m b := by
  ext n
  rw [longHomExtraction_apply]
  by_cases h : n = m
  · subst n
    rw [longHomCoordinate_lift, Finsupp.single_eq_same]
  · rw [longHomCoordinate_lift_off D Sc cutoff p i y n m h, Finsupp.single_eq_of_ne h]

@[simp] theorem longHomExtraction_section (p : ZMod 2) (i : I) {v t : List I}
    (y : NFIdx v t) (f : ℕ →₀ Old D Sc cutoff v t) :
    longHomExtraction D Sc cutoff p i y (longHomSection D Sc cutoff p i y f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b =>
    rw [longHomSection, Finsupp.lsum_single, longHomExtraction_lift]

/-- Every finite row over the full off-diagonal Hom has an explicitly reconstructed lift. -/
theorem longHomExtraction_surjective (p : ZMod 2) (i : I) {v t : List I}
    (y : NFIdx v t) : Function.Surjective (longHomExtraction D Sc cutoff p i y) := by
  intro f
  exact ⟨longHomSection D Sc cutoff p i y f, longHomExtraction_section D Sc cutoff p i y f⟩

end OddMath.QuiverHecke.ELVOld
