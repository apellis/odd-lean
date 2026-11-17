import OddMath.Algebra.DegreeShiftRowDivision
import OddMath.QuiverHecke.CyclotomicAction.AppendSourceRows.SourceSplitting
import OddMath.QuiverHecke.CyclotomicAction.LeadingSourceTransport

/-!
# Off diagonal long

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Long coordinates with different old source and target

The first off-diagonal prerequisite of `DeformedMackeyBoundary.md` (2).
An existing old normal-form index selects a long tail with arbitrary old
source and target. Extraction and reconstruction retain the entire old Hom,
not just its endomorphism ring. The supplied old index is used only in the intermediate construction. The final
finite-row maps choose an index when one exists and handle empty old Homs
explicitly; they carry no old-index hypothesis. Independence of this auxiliary
choice is proved. Identification of the full relative-short kernel and
transport of the polynomial boundary remain separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELV
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

private theorem castPair_eq_of_heq (p : ZMod 2) (i : I) {v t w s s' : List I}
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

/-- The long lift is independent of the auxiliary old normal-form index. -/
theorem longHomLift_independent (p : ZMod 2) (i : I) {v t : List I}
    (y y' : NFIdx v t) (m : ℕ) :
    longHomLift D Sc cutoff p i y m = longHomLift D Sc cutoff p i y' m := by
  unfold longHomLift
  exact congrArg
    (fun f : Old D Sc cutoff v t →ₗ[k] Target D Sc cutoff i v (t ++ [i]) =>
      (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m • f)
    (castPair_eq_of_heq D Sc cutoff p i
      (longHomIndex_oldTarget i y m) (longHomIndex_oldTarget i y' m) _ _
      (prependTail_heq_of_tailKey_eq D Sc (longHomIndex i y m)
        (longHomIndex i y' m) rfl))

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

/-- Consequently the finite long section does not depend on the chosen old index. -/
theorem longHomSection_independent (p : ZMod 2) (i : I) {v t : List I}
    (y y' : NFIdx v t) :
    longHomSection D Sc cutoff p i y = longHomSection D Sc cutoff p i y' := by
  unfold longHomSection
  congr 1
  funext m
  exact longHomLift_independent D Sc cutoff p i y y' m

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

private theorem homCoordinate_pair_transport (p : ZMod 2) {i : I} {v w : List I}
    (x y : PrependIdx i v w) (e : x.oldTarget = y.oldTarget)
    (ht : HEq (prependTail D Sc x) (prependTail D Sc y))
    (b : Old D Sc cutoff v y.oldTarget) :
    prependOldCoordinate D Sc cutoff p x
      (pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc y) b) = e.symm ▸ b := by
  have transport {s s' : List I} (e : s = s')
      (f : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D w))
      (g : (pres D Sc).obj (ob D (i :: s')) ⟶ (pres D Sc).obj (ob D w))
      (hf : HEq f g) (b : Old D Sc cutoff v s') :
      pair D Sc cutoff p i ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] g) b =
      pair D Sc cutoff p i ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f) (e.symm ▸ b) := by
    subst s'
    cases hf
    rfl
  rw [transport e _ _ ht b, prependOldCoordinate_pair]

private theorem castHomCoordinate_pair_value (i : I) {v t w s s' : List I}
    (e : s = t) (e' : s' = t)
    (f : Target D Sc cutoff i v w →ₗ[k] Old D Sc cutoff v s)
    (g : Old D Sc cutoff v s' →ₗ[k] Target D Sc cutoff i v w)
    (hf : ∀ b, f (g b) = (e'.trans e.symm) ▸ b) (a : k)
    (b : Old D Sc cutoff v s') :
    (Eq.mp (congrArg (fun s => Target D Sc cutoff i v w →ₗ[k]
      Old D Sc cutoff v s) e) (a • f)) (g b) = a • (e' ▸ b) := by
  subst s
  subst s'
  change a • f (g b) = a • b
  rw [hf]

/-- The coefficient functional also forgets the auxiliary old normal form. -/
theorem longHomCoordinate_independent (p : ZMod 2) (i : I) {v t : List I}
    (y y' : NFIdx v t) (m : ℕ) (z : Target D Sc cutoff i v (t ++ [i])) :
    longHomCoordinate D Sc cutoff p i y m z =
      longHomCoordinate D Sc cutoff p i y' m z := by
  obtain ⟨f, rfl⟩ := prependOldReconstruct_surjective D Sc cutoff p i v (t ++ [i]) z
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | of q b =>
    change longHomCoordinate D Sc cutoff p i y m
        (prependOldReconstruct D Sc cutoff p i v (t ++ [i]) (DirectSum.lof k _ _ q b)) =
      longHomCoordinate D Sc cutoff p i y' m
        (prependOldReconstruct D Sc cutoff p i v (t ++ [i]) (DirectSum.lof k _ _ q b))
    rw [prependOldReconstruct, DirectSum.toModule_lof]
    have hkey : (longHomIndex i y m).tailKey = (longHomIndex i y' m).tailKey := rfl
    by_cases hq : (longHomIndex i y m).tailKey = q.representative.tailKey
    · have hq' : (longHomIndex i y' m).tailKey = q.representative.tailKey := hkey.symm.trans hq
      have eq : q.representative.oldTarget = t :=
        ((longHomIndex i y m).oldTarget_eq_of_tailKey_eq q.representative hq).symm.trans
          (longHomIndex_oldTarget i y m)
      unfold longHomCoordinate
      have left := castHomCoordinate_pair_value D Sc cutoff i
        (longHomIndex_oldTarget i y m) eq
        (prependOldCoordinate D Sc cutoff p (longHomIndex i y m)) _
        (fun b => homCoordinate_pair_transport D Sc cutoff p _ _
          ((longHomIndex i y m).oldTarget_eq_of_tailKey_eq q.representative hq)
          (prependTail_heq_of_tailKey_eq D Sc _ _ hq) b)
        ((SKM.zsign k (D.parity i * wordSumParity D v)) ^ m) b
      have right := castHomCoordinate_pair_value D Sc cutoff i
        (longHomIndex_oldTarget i y' m) eq
        (prependOldCoordinate D Sc cutoff p (longHomIndex i y' m)) _
        (fun b => homCoordinate_pair_transport D Sc cutoff p _ _
          ((longHomIndex i y' m).oldTarget_eq_of_tailKey_eq q.representative hq')
          (prependTail_heq_of_tailKey_eq D Sc _ _ hq') b)
        ((SKM.zsign k (D.parity i * wordSumParity D v)) ^ m) b
      exact left.trans right.symm
    · have hq' : (longHomIndex i y' m).tailKey ≠ q.representative.tailKey := by
        intro h
        exact hq (hkey.trans h)
      have hz (u : NFIdx v t)
          (h : (longHomIndex i u m).tailKey ≠ q.representative.tailKey) :
          longHomCoordinate D Sc cutoff p i u m
            (pair D Sc cutoff p i
              ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
                prependTail D Sc q.representative) b) = 0 := by
        unfold longHomCoordinate
        apply castHomCoordinate_zero D Sc cutoff i (longHomIndex_oldTarget i u m)
        rw [LinearMap.smul_apply, prependOldCoordinate_pair_off D Sc cutoff p _ _ h, smul_zero]
      rw [hz y hq, hz y' hq']

theorem longHomExtraction_independent (p : ZMod 2) (i : I) {v t : List I}
    (y y' : NFIdx v t) :
    longHomExtraction D Sc cutoff p i y = longHomExtraction D Sc cutoff p i y' := by
  apply LinearMap.ext
  intro z
  apply Finsupp.ext
  intro m
  exact longHomCoordinate_independent D Sc cutoff p i y y' m z

/-- Empty old normal-form index type forces the actual old quotient Hom to vanish. -/
theorem old_eq_zero_of_no_normal_form {v t : List I} (h : ¬ Nonempty (NFIdx v t))
    (b : Old D Sc cutoff v t) : b = 0 := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  have hr : r = 0 := by
    by_contra hn
    exact h (exists_oldIndex_of_ne_zero D Sc cutoff r hn)
  rw [hr, map_zero]

/-- Off-diagonal long extraction with no supplied normal-form index.
In the empty-index case its codomain is proved zero. -/
def offDiagonalLongExtraction (p : ZMod 2) (i : I) (v t : List I) :
    Target D Sc cutoff i v (t ++ [i]) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  if h : Nonempty (NFIdx v t) then
    longHomExtraction D Sc cutoff p i (Classical.choice h)
  else 0

/-- Explicit finite long lift with no supplied normal-form index. -/
def offDiagonalLongSection (p : ZMod 2) (i : I) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] Target D Sc cutoff i v (t ++ [i]) :=
  if h : Nonempty (NFIdx v t) then
    longHomSection D Sc cutoff p i (Classical.choice h)
  else 0

/-- Every available normal-form index computes the same off-diagonal extraction. -/
theorem offDiagonalLongExtraction_eq (p : ZMod 2) (i : I) {v t : List I}
    (y : NFIdx v t) :
    offDiagonalLongExtraction D Sc cutoff p i v t = longHomExtraction D Sc cutoff p i y := by
  simp only [offDiagonalLongExtraction, dite_eq_left (show Nonempty (NFIdx v t) from ⟨y⟩)]
  exact longHomExtraction_independent D Sc cutoff p i _ y

/-- Every available old index likewise computes the same prescribed section. -/
theorem offDiagonalLongSection_eq (p : ZMod 2) (i : I) {v t : List I}
    (y : NFIdx v t) :
    offDiagonalLongSection D Sc cutoff p i v t = longHomSection D Sc cutoff p i y := by
  simp only [offDiagonalLongSection, dite_eq_left (show Nonempty (NFIdx v t) from ⟨y⟩)]
  exact longHomSection_independent D Sc cutoff p i _ y

/-- The actual finite off-diagonal row is split surjective, including empty old Homs. -/
@[simp] theorem offDiagonalLongExtraction_section (p : ZMod 2) (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalLongExtraction D Sc cutoff p i v t
      (offDiagonalLongSection D Sc cutoff p i v t f) = f := by
  by_cases h : Nonempty (NFIdx v t)
  · simp only [offDiagonalLongExtraction, offDiagonalLongSection, dite_eq_left h]
    exact longHomExtraction_section D Sc cutoff p i (Classical.choice h) f
  · have hf : f = 0 := by
      ext n
      exact old_eq_zero_of_no_normal_form D Sc cutoff h (f n)
    rw [hf, map_zero, map_zero]

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The chronological kernel of off-diagonal long extraction

The arbitrary-old-Hom form of DeformedMackeyBoundary (2). The actual finite
row on Target(i,v,t++[i]) has precisely the chronological short span as its
kernel, including empty old Homs and full polynomial/exterior coefficients.
No field, flatness, or action hypothesis is introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Rebasing retains the long shuffle, including its source-length transport. -/
theorem longHomIndex_shuffle (i : I) {v t : List I} (y : NFIdx v t) (m : ℕ) :
    (longHomIndex i y m).1.2.2.2 = longPrependShuffle v.length := by
  have hl : v.length = t.length := by
    have hh := congrArg List.length y.tgt_cw
    simpa only [length_tgt] using hh
  have transport {n m : ℕ} (h : n = m) :
      (h.symm ▸ longPrependShuffle m : PrependShuffle n) = longPrependShuffle n := by
    cases h
    rfl
  change (hl.symm ▸ longPrependShuffle t.length : PrependShuffle v.length) =
    longPrependShuffle v.length
  exact transport hl

/-- A long shuffle ending at t++[i] has the actual old target t. -/
theorem oldTarget_eq_of_long_shuffle {i : I} {v t : List I}
    (x : PrependIdx i v (t ++ [i]))
    (hx : x.1.2.2.2 = longPrependShuffle v.length) : x.oldTarget = t := by
  have hl : x.oldTarget.length = v.length := by simp [PrependIdx.oldTarget]
  have he := congrArg Subtype.val
    (prependShuffleTarget_long i (⟨x.oldTarget, hl⟩ : Word I v.length))
  change tgt (i :: x.oldTarget)
      (cw (canWord (v.length + 1) (longPrependShuffle v.length).1⁻¹)) =
    x.oldTarget ++ [i] at he
  have hm := x.moving_target
  rw [hx] at hm
  exact List.append_cancel_right (he.symm.trans hm)

private theorem offDiagonalSameTailCoordinate (p : ZMod 2) {i : I} {v w : List I}
    (x y : PrependIdx i v w) (h : x.tailKey = y.tailKey)
    (z : Target D Sc cutoff i v w) :
    HEq (prependOldCoordinate D Sc cutoff p x z)
      (prependOldCoordinate D Sc cutoff p y z) := by
  obtain ⟨f, rfl⟩ := projection_surjective D Sc cutoff i v w z
  rw [prependOldCoordinate_projection, prependOldCoordinate_projection]
  have ht := x.oldTarget_eq_of_tailKey_eq y h
  have hn := congrArg Prod.fst h
  have hd := congrArg Prod.snd h
  change x.1.1 = y.1.1 at hn
  change x.1.2.2.2 = y.1.2.2.2 at hd
  have hp : prependTailParity D x = prependTailParity D y := by
    unfold prependTailParity
    rw [ht, hn, hd]
  have hr : HEq x.replaceOld y.replaceOld := by
    apply Function.hfunext (congrArg (NFIdx v) ht)
    intro a b hab
    apply heq_of_eq
    apply Subtype.ext
    have val_heq {t t' : List I} (e : t = t') (a : NFIdx v t) (b : NFIdx v t')
        (ha : HEq a b) : a.val = b.val := by
      subst t'
      cases ha
      rfl
    have hv := val_heq ht a b hab
    change (x.1.1, a.1.1, a.1.2, x.1.2.2.2) =
      (y.1.1, b.1.1, b.1.2, y.1.2.2.2)
    rw [hn, hd, show a.1.1 = b.1.1 from congrArg Prod.fst hv,
      show a.1.2 = b.1.2 from congrArg Prod.snd hv]
  have transport (t t' : List I) (e : t = t') (r r' : ZMod 2) (er : r = r')
      (a : NFIdx v t → PrependIdx i v w) (b : NFIdx v t' → PrependIdx i v w)
      (ha : Function.Injective a) (hb : Function.Injective b) (he : HEq a b) :
      HEq ((ideal D Sc cutoff v t).mkQ ((twist k p)
        ((oldAffineEquiv D Sc cutoff v t).symm
          ((Finsupp.mapRange.linearMap (coefficientTwist D cutoff r))
            ((Finsupp.lcomapDomain (R := k) a ha) (prependAffineEquiv D Sc cutoff i v w f))))))
        ((ideal D Sc cutoff v t').mkQ ((twist k p)
        ((oldAffineEquiv D Sc cutoff v t').symm
          ((Finsupp.mapRange.linearMap (coefficientTwist D cutoff r'))
            ((Finsupp.lcomapDomain (R := k) b hb) (prependAffineEquiv D Sc cutoff i v w f)))))) := by
    subst t'
    subst r'
    cases he
    rfl
  exact transport _ _ ht _ _ hp _ _ x.replaceOld_injective y.replaceOld_injective hr

private theorem offDiagonalCastCoordinateZero (i : I) (v w t t' : List I) (e : t = t')
    (f : Target D Sc cutoff i v w →ₗ[k] Old D Sc cutoff v t)
    (z : Target D Sc cutoff i v w) (hz : f z = 0) :
    (Eq.mp (congrArg (fun t => Target D Sc cutoff i v w →ₗ[k]
      Old D Sc cutoff v t) e) f) z = 0 := by
  cases e
  exact hz

theorem longHomExtraction_chronological_generator (p : ZMod 2) (i : I)
    {v t : List I} (y : NFIdx v t) (s : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (h : hom D Sc cutoff (i :: s) t) :
    longHomExtraction D Sc cutoff p i y
      (projection D Sc cutoff i v (t ++ [i])
        (insert D Sc cutoff i v (s ++ [i]) r ≫
          rightContext D Sc cutoff [i] (i :: s) t h)) = 0 := by
  ext m
  rw [longHomExtraction_apply, Finsupp.zero_apply]
  unfold longHomCoordinate
  apply offDiagonalCastCoordinateZero D Sc cutoff i v (t ++ [i]) _ t
    (longHomIndex_oldTarget i y m)
  rw [LinearMap.smul_apply, prependOldCoordinate_projection]
  change _ • (ideal D Sc cutoff v (longHomIndex i y m).oldTarget).mkQ
    (prependExtractOld D Sc cutoff p (longHomIndex i y m) _) = 0
  rw [chronological_prependExtractOld_zero D Sc cutoff p r h
    (longHomIndex i y m) (longHomIndex_shuffle i y m), map_zero, smul_zero]

theorem chronologicalShortSpan_le_ker_longHomExtraction (p : ZMod 2) (i : I)
    {v t : List I} (y : NFIdx v t) :
    chronologicalShortSpan D Sc cutoff i v t ≤
      LinearMap.ker (longHomExtraction D Sc cutoff p i y) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, r, h, rfl⟩
  exact longHomExtraction_chronological_generator D Sc cutoff p i y s r h

/-- The finite row has exactly the prescribed chronological short kernel. -/
theorem ker_longHomExtraction_eq_chronologicalShortSpan
    (p : ZMod 2) (i : I) {v t : List I} (y : NFIdx v t) :
    LinearMap.ker (longHomExtraction D Sc cutoff p i y) =
      chronologicalShortSpan D Sc cutoff i v t := by
  apply le_antisymm
  · intro z hz
    change longHomExtraction D Sc cutoff p i y z = 0 at hz
    have hl (m : ℕ) : prependOldCoordinate D Sc cutoff p (longHomIndex i y m) z = 0 := by
      have hm := congrArg (fun f : ℕ →₀ Old D Sc cutoff v t => f m) hz
      change longHomCoordinate D Sc cutoff p i y m z = 0 at hm
      have uncast (s s' : List I) (e : s = s')
          (f : Target D Sc cutoff i v (t ++ [i]) →ₗ[k] Old D Sc cutoff v s)
          (h : (Eq.mp (congrArg (fun s => Target D Sc cutoff i v (t ++ [i]) →ₗ[k]
            Old D Sc cutoff v s) e) f) z = 0) : f z = 0 := by
        subst s'
        exact h
      have hs := uncast _ _ (longHomIndex_oldTarget i y m) _ hm
      change (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m •
        prependOldCoordinate D Sc cutoff p (longHomIndex i y m) z = 0 at hs
      have hs' := congrArg
        (fun a : Old D Sc cutoff v (longHomIndex i y m).oldTarget =>
          (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m • a) hs
      simpa only [smul_smul, ← mul_pow, SKM.zsign_mul_self', one_pow, one_smul,
        smul_zero] using hs'
    let f := prependOldCoordinateEquiv D Sc cutoff p i v (t ++ [i]) z
    have hterm (q : PrependIdx.Tail i v (t ++ [i])) :
        pair D Sc cutoff p i
          ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
            prependTail D Sc q.representative) (f q) ∈
          chronologicalShortSpan D Sc cutoff i v t := by
      by_cases hq : q.representative.1.2.2.2 = longPrependShuffle v.length
      · have hk : q.representative.tailKey =
            (longHomIndex i y q.representative.1.1).tailKey :=
          Prod.ext rfl (hq.trans (longHomIndex_shuffle i y _).symm)
        have he := offDiagonalSameTailCoordinate D Sc cutoff p q.representative
          (longHomIndex i y q.representative.1.1) hk z
        have zero_heq (s s' : List I) (e : s = s') :
            HEq (0 : Old D Sc cutoff v s) (0 : Old D Sc cutoff v s') := by
          subst s'
          rfl
        have hc : f q = 0 := by
          rw [prependOldCoordinateEquiv_apply]
          apply eq_of_heq
          rw [hl] at he
          exact he.trans (zero_heq _ _
            (q.representative.oldTarget_eq_of_tailKey_eq _ hk).symm)
        rw [hc, map_zero]
        exact Submodule.zero_mem _
      · obtain ⟨r, hr⟩ := (ideal D Sc cutoff v q.representative.oldTarget).mkQ_surjective (f q)
        rw [← hr]
        erw [pair_mk]
        exact prepend_short_mem D Sc cutoff i v t q.representative hq (twist k p r)
    rw [← prependOldReconstruct_coordinateEquiv D Sc cutoff p i v (t ++ [i]) z]
    exact dfinsuppSumAddHom_mem _ f
      (fun q => (pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc q.representative)).toAddMonoidHom)
      (fun q _ => hterm q)
  · exact chronologicalShortSpan_le_ker_longHomExtraction D Sc cutoff p i y

/-- If the old normal forms are empty, reconstruction consists entirely of short tails. -/
theorem mem_chronologicalShortSpan_of_no_old_normal_form
    (p : ZMod 2) (i : I) (v t : List I) (h : ¬ Nonempty (NFIdx v t))
    (z : Target D Sc cutoff i v (t ++ [i])) :
    z ∈ chronologicalShortSpan D Sc cutoff i v t := by
  let f := prependOldCoordinateEquiv D Sc cutoff p i v (t ++ [i]) z
  have hterm (q : PrependIdx.Tail i v (t ++ [i])) :
      pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc q.representative) (f q) ∈
        chronologicalShortSpan D Sc cutoff i v t := by
    have hq : q.representative.1.2.2.2 ≠ longPrependShuffle v.length := by
      intro hlong
      exact h ⟨oldTarget_eq_of_long_shuffle q.representative hlong ▸ q.representative.old⟩
    obtain ⟨r, hr⟩ := (ideal D Sc cutoff v q.representative.oldTarget).mkQ_surjective (f q)
    rw [← hr]
    erw [pair_mk]
    exact prepend_short_mem D Sc cutoff i v t q.representative hq (twist k p r)
  rw [← prependOldReconstruct_coordinateEquiv D Sc cutoff p i v (t ++ [i]) z]
  exact dfinsuppSumAddHom_mem _ f
    (fun q => (pair D Sc cutoff p i
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        prependTail D Sc q.representative)).toAddMonoidHom)
    (fun q _ => hterm q)

/-- Unconditional arbitrary-old-Hom chronological kernel, with no chosen old index. -/
theorem ker_offDiagonalLongExtraction_eq_chronologicalShortSpan
    (p : ZMod 2) (i : I) (v t : List I) :
    LinearMap.ker (offDiagonalLongExtraction D Sc cutoff p i v t) =
      chronologicalShortSpan D Sc cutoff i v t := by
  by_cases h : Nonempty (NFIdx v t)
  · obtain ⟨y⟩ := h
    rw [offDiagonalLongExtraction_eq D Sc cutoff p i y]
    exact ker_longHomExtraction_eq_chronologicalShortSpan D Sc cutoff p i y
  · rw [offDiagonalLongExtraction, dite_eq_right h, LinearMap.ker_zero]
    apply le_antisymm
    · intro z _
      exact mem_chronologicalShortSpan_of_no_old_normal_form D Sc cutoff p i v t h z
    · exact le_top

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Actual source splitting on arbitrary old Hom coefficients

The long extraction has the prescribed alpha range as its kernel. Correcting
the actual long section by its alpha coordinate gives the source normal form.
Both old endpoints are arbitrary; every moving colour is retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem ker_offDiagonalLongExtraction_eq_range_alpha (p : ZMod 2) (i : I) (v t : List I) :
    LinearMap.ker (offDiagonalLongExtraction D Sc cutoff p i v t) =
      LinearMap.range (alpha D Sc cutoff i v t) := by
  rw [ker_offDiagonalLongExtraction_eq_chronologicalShortSpan, range_alpha_eq_chronologicalShortSpan]

@[simp] theorem offDiagonalLongExtraction_alpha (p : ZMod 2) (i : I) (v t : List I)
    (a : PprimeDomain D Sc cutoff i v t) :
    offDiagonalLongExtraction D Sc cutoff p i v t (alpha D Sc cutoff i v t a) = 0 := by
  have h : alpha D Sc cutoff i v t a ∈ LinearMap.range (alpha D Sc cutoff i v t) := ⟨a, rfl⟩
  rw [← ker_offDiagonalLongExtraction_eq_range_alpha D Sc cutoff p i v t] at h
  exact h

/-- The existing long lift corrected by its prescribed short-source coordinate. -/
def offDiagonalSourceLongSection (p : ZMod 2) (i : I) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] Target D Sc cutoff i v (t ++ [i]) :=
  offDiagonalLongSection D Sc cutoff p i v t -
    alpha D Sc cutoff i v t ∘ₗ extract D Sc cutoff i v t ∘ₗ offDiagonalLongSection D Sc cutoff p i v t

@[simp] theorem extract_offDiagonalSourceLongSection (p : ZMod 2) (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    extract D Sc cutoff i v t (offDiagonalSourceLongSection D Sc cutoff p i v t f) = 0 := by
  simp only [offDiagonalSourceLongSection, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
    extract_alpha, sub_self]

@[simp] theorem offDiagonalLongExtraction_sourceLongSection (p : ZMod 2) (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalLongExtraction D Sc cutoff p i v t (offDiagonalSourceLongSection D Sc cutoff p i v t f) = f := by
  simp only [offDiagonalSourceLongSection, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
    offDiagonalLongExtraction_alpha, offDiagonalLongExtraction_section, sub_zero]

theorem offDiagonalSource_reconstruction (p : ZMod 2) (i : I) (v t : List I)
    (z : Target D Sc cutoff i v (t ++ [i])) :
    alpha D Sc cutoff i v t (extract D Sc cutoff i v t z) +
      offDiagonalSourceLongSection D Sc cutoff p i v t (offDiagonalLongExtraction D Sc cutoff p i v t z) = z := by
  have hz : z - offDiagonalSourceLongSection D Sc cutoff p i v t
      (offDiagonalLongExtraction D Sc cutoff p i v t z) ∈
      LinearMap.ker (offDiagonalLongExtraction D Sc cutoff p i v t) := by
    simp only [LinearMap.mem_ker, map_sub, offDiagonalLongExtraction_sourceLongSection, sub_self]
  rw [ker_offDiagonalLongExtraction_eq_range_alpha] at hz
  obtain ⟨a, ha⟩ := hz
  have he := congrArg (extract D Sc cutoff i v t) ha
  simp only [extract_alpha, map_sub, extract_offDiagonalSourceLongSection, sub_zero] at he
  rw [← he, ha]
  exact sub_add_cancel _ _

/-- Coordinates in the prescribed balanced source and the existing polynomial old module. -/
def offDiagonalSourceCoordinateEquiv (p : ZMod 2) (i : I) (v t : List I) :
    Target D Sc cutoff i v (t ++ [i]) ≃ₗ[k]
      (PprimeDomain D Sc cutoff i v t × (ℕ →₀ Old D Sc cutoff v t)) where
  toLinearMap := (extract D Sc cutoff i v t).prod (offDiagonalLongExtraction D Sc cutoff p i v t)
  invFun a := alpha D Sc cutoff i v t a.1 + offDiagonalSourceLongSection D Sc cutoff p i v t a.2
  left_inv := offDiagonalSource_reconstruction D Sc cutoff p i v t
  right_inv a := by
    apply Prod.ext
    · change extract D Sc cutoff i v t (_ + _) = a.1
      simp only [map_add, extract_alpha, extract_offDiagonalSourceLongSection, add_zero]
    · change offDiagonalLongExtraction D Sc cutoff p i v t (_ + _) = a.2
      simp only [map_add, offDiagonalLongExtraction_alpha,
        offDiagonalLongExtraction_sourceLongSection, zero_add]

@[simp] theorem offDiagonalSourceCoordinateEquiv_apply (p : ZMod 2) (i : I) (v t : List I)
    (z : Target D Sc cutoff i v (t ++ [i])) :
    offDiagonalSourceCoordinateEquiv D Sc cutoff p i v t z =
      (extract D Sc cutoff i v t z, offDiagonalLongExtraction D Sc cutoff p i v t z) := rfl

@[simp] theorem offDiagonalSourceCoordinateEquiv_symm_apply (p : ZMod 2) (i : I) (v t : List I)
    (a : PprimeDomain D Sc cutoff i v t) (f : ℕ →₀ Old D Sc cutoff v t) :
    (offDiagonalSourceCoordinateEquiv D Sc cutoff p i v t).symm (a, f) =
      alpha D Sc cutoff i v t a + offDiagonalSourceLongSection D Sc cutoff p i v t f := rfl

@[simp] theorem offDiagonalSourceCoordinateEquiv_alpha (p : ZMod 2) (i : I) (v t : List I)
    (a : PprimeDomain D Sc cutoff i v t) :
    offDiagonalSourceCoordinateEquiv D Sc cutoff p i v t (alpha D Sc cutoff i v t a) = (a, 0) := by
  simp only [offDiagonalSourceCoordinateEquiv_apply, extract_alpha, offDiagonalLongExtraction_alpha]

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Base long-section transport to arbitrary output arrows

The off-diagonal long section in degree zero is the literal bare-long pair.
The full-coefficient bare-long transport gives its comparison with the
diagonal section modulo the actual chronological short span. Corrected rho
commutes with arbitrary target postcomposition by associativity.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELV
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem castPair_heq (p : ZMod 2) (i : I) {v t w s : List I}
    (e : s = t)
    (f : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D w))
    (g : (pres D Sc).obj (ob D (i :: t)) ⟶ (pres D Sc).obj (ob D w))
    (h : HEq f g) :
    Eq.mp (congrArg (fun a => Old D Sc cutoff v a →ₗ[k] Target D Sc cutoff i v w) e)
      (pair D Sc cutoff p i (affineUnit D Sc cutoff _ _ f)) =
    pair D Sc cutoff p i (affineUnit D Sc cutoff _ _ g) := by
  subst s
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
    (longHomIndex_oldTarget i y 0) _ _ ht
  have hv := congrArg (fun f : Old D Sc cutoff v t →ₗ[k]
    Target D Sc cutoff i v (t ++ [i]) => f b) h
  unfold longHomLift
  rw [pow_zero, one_smul]
  change Eq.mp (congrArg (fun a => Old D Sc cutoff v a →ₗ[k]
    Target D Sc cutoff i v (t ++ [i])) (longHomIndex_oldTarget i y 0))
      (pair D Sc cutoff p i (affineUnit D Sc cutoff _ _
        (prependTail D Sc (longHomIndex i y 0)))) b =
    pair D Sc cutoff p i (affineUnit D Sc cutoff _ _ (OutputOldComposite.bareU D Sc i t)) b
  exact hv

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
    (longOutputIndex_oldTarget i v 0) _ _ (tail_long_zero D Sc i v)
  have hv := congrArg (fun f : Old D Sc cutoff v v →ₗ[k]
    Target D Sc cutoff i v (v ++ [i]) => f b) h
  unfold outputLongLift
  rw [pow_zero, one_smul]
  change Eq.mp (congrArg (fun a => Old D Sc cutoff v a →ₗ[k]
    Target D Sc cutoff i v (v ++ [i])) (longOutputIndex_oldTarget i v 0))
      (pair D Sc cutoff p i (affineUnit D Sc cutoff _ _
        (prependTail D Sc (longOutputIndex i v 0)))) b =
    pair D Sc cutoff p i (affineUnit D Sc cutoff _ _ (OutputOldComposite.bareU D Sc i v)) b
  exact hv

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

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Corrected rho on arbitrary old-Hom long sections

The source-operator comparison in DeformedMackeyBoundary (2)-(3), with
independent old source and target words. The entire old coefficient is
twisted, and delta acts at the old source. No field, action, matrix inverse
or supplied coordinate-intertwining hypothesis is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Corrected coefficient rho retains its full total-parity and source-delta actions. -/
def offDiagonalCoefficientRho (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) : (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  (Finsupp.lmapDomain (Old D Sc cutoff v t) k Nat.succ).comp
      (Finsupp.mapRange.linearMap (oldTwist D Sc cutoff (D.parity j.1) v t)) +
    SKM.zsign k (D.parity j.1 * wordSumParity D v) •
      ((2 * (-1 : k) ^ cutoff j.1) •
        Finsupp.mapRange.linearMap
          (oldPrecomp D Sc cutoff v t (twist k p (boundaryDelta D Sc cutoff j v))))

@[simp] theorem offDiagonalCoefficientRho_single (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ) (b : Old D Sc cutoff v t) :
    offDiagonalCoefficientRho D Sc cutoff p j v t (Finsupp.single m b) =
      Finsupp.single (m + 1) (oldTwist D Sc cutoff (D.parity j.1) v t b) +
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        ((2 * (-1 : k) ^ cutoff j.1) • Finsupp.single m
          (oldPrecomp D Sc cutoff v t (twist k p (boundaryDelta D Sc cutoff j v)) b)) := by
  simp only [offDiagonalCoefficientRho, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- Actual corrected rho acts on each off-diagonal long lift by the specified two terms. -/
theorem boundaryRho_longHomLift (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) {v t : List I} (y : NFIdx v t) (m : ℕ)
    (b : Old D Sc cutoff v t) :
    boundaryRho D Sc cutoff j v (t ++ [j.1]) (longHomLift D Sc cutoff p j.1 y m b) =
      longHomLift D Sc cutoff p j.1 y (m + 1) (oldTwist D Sc cutoff (D.parity j.1) v t b) +
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        ((2 * (-1 : k) ^ cutoff j.1) • longHomLift D Sc cutoff p j.1 y m
          (oldPrecomp D Sc cutoff v t (twist k p (boundaryDelta D Sc cutoff j v)) b)) := by
  have transport {s : List I} (e : s = t)
      (f g : Old D Sc cutoff v s →ₗ[k] Target D Sc cutoff j.1 v (t ++ [j.1]))
      (h : ∀ b, boundaryRho D Sc cutoff j v (t ++ [j.1]) (f b) =
        SKM.zsign k (D.parity j.1 * wordSumParity D v) •
          (g (oldTwist D Sc cutoff (D.parity j.1) v s b) +
            (2 * (-1 : k) ^ cutoff j.1) • f
              (oldPrecomp D Sc cutoff v s (twist k p (boundaryDelta D Sc cutoff j v)) b))) :
      ∀ b : Old D Sc cutoff v t,
      boundaryRho D Sc cutoff j v (t ++ [j.1])
        ((SKM.zsign k (D.parity j.1 * wordSumParity D v)) ^ m •
          (Eq.mp (congrArg (fun s => Old D Sc cutoff v s →ₗ[k]
            Target D Sc cutoff j.1 v (t ++ [j.1])) e) f) b) =
      (SKM.zsign k (D.parity j.1 * wordSumParity D v)) ^ (m + 1) •
        (Eq.mp (congrArg (fun s => Old D Sc cutoff v s →ₗ[k]
          Target D Sc cutoff j.1 v (t ++ [j.1])) e) g)
            (oldTwist D Sc cutoff (D.parity j.1) v t b) +
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        ((2 * (-1 : k) ^ cutoff j.1) •
          ((SKM.zsign k (D.parity j.1 * wordSumParity D v)) ^ m •
          (Eq.mp (congrArg (fun s => Old D Sc cutoff v s →ₗ[k]
            Target D Sc cutoff j.1 v (t ++ [j.1])) e) f)
              (oldPrecomp D Sc cutoff v t (twist k p (boundaryDelta D Sc cutoff j v)) b))) := by
    subst s
    intro b
    change boundaryRho D Sc cutoff j v (t ++ [j.1]) (_ • f b) =
      _ • g (oldTwist D Sc cutoff (D.parity j.1) v t b) + _ • (_ • (_ • f _))
    rw [map_smul, h, smul_add, smul_add, pow_succ]
    simp only [smul_smul]
    congr 1
    congr 1
    ring
  apply transport (longHomIndex_oldTarget j.1 y m)
  intro c
  have h := boundaryRho_pair D Sc cutoff p j (longHomIndex j.1 y m) c
  have ht : prependTail D Sc ((longHomIndex j.1 y m).shift 1) =
      prependTail D Sc (longHomIndex j.1 y (m + 1)) :=
    congrArg (fun n : ℕ => (show (pres D Sc).obj (ob D
      (j.1 :: (longHomIndex j.1 y m).oldTarget)) ⟶
        (pres D Sc).obj (ob D (t ++ [j.1])) from
          prependTail D Sc (longHomIndex j.1 y n))) (Nat.add_comm 1 m)
  rw [ht] at h
  exact h

@[simp] theorem longHomSection_single (p : ZMod 2) (i : I) {v t : List I}
    (y : NFIdx v t) (m : ℕ) (b : Old D Sc cutoff v t) :
    longHomSection D Sc cutoff p i y (Finsupp.single m b) =
      longHomLift D Sc cutoff p i y m b := by
  simp only [longHomSection, Finsupp.lsum_single]

theorem boundaryRho_longHomSection (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) {v t : List I}
    (y : NFIdx v t) (f : ℕ →₀ Old D Sc cutoff v t) :
    boundaryRho D Sc cutoff j v (t ++ [j.1]) (longHomSection D Sc cutoff p j.1 y f) =
      longHomSection D Sc cutoff p j.1 y (offDiagonalCoefficientRho D Sc cutoff p j v t f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b =>
    simp only [longHomSection_single, offDiagonalCoefficientRho_single, map_add, map_smul]
    exact boundaryRho_longHomLift D Sc cutoff p j y m b

/-- The unconditional arbitrary-Hom section intertwines the actual corrected operators. -/
theorem boundaryRho_offDiagonalLongSection (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    boundaryRho D Sc cutoff j v (t ++ [j.1]) (offDiagonalLongSection D Sc cutoff p j.1 v t f) =
      offDiagonalLongSection D Sc cutoff p j.1 v t
        (offDiagonalCoefficientRho D Sc cutoff p j v t f) := by
  by_cases h : Nonempty (NFIdx v t)
  · obtain ⟨y⟩ := h
    simp only [offDiagonalLongSection_eq D Sc cutoff p j.1 y]
    exact boundaryRho_longHomSection D Sc cutoff p j y f
  · have hf : f = 0 := by
      ext n
      exact old_eq_zero_of_no_normal_form D Sc cutoff h (f n)
    rw [hf]
    simp only [map_zero]

/-- Corrected off-diagonal lifts are actual source rho iterates. -/
def offDiagonalCorrectedLift (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (d : ℕ) (b : Old D Sc cutoff v t) :
    Target D Sc cutoff j.1 v (t ++ [j.1]) :=
  (boundaryRho D Sc cutoff j v (t ++ [j.1]))^[d]
    (offDiagonalLongSection D Sc cutoff p j.1 v t (Finsupp.single 0 b))

theorem offDiagonalLongSection_rho_iterate (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (d : ℕ) (b : Old D Sc cutoff v t) :
    offDiagonalLongSection D Sc cutoff p j.1 v t
      ((offDiagonalCoefficientRho D Sc cutoff p j v t)^[d] (Finsupp.single 0 b)) =
        offDiagonalCorrectedLift D Sc cutoff p j v t d b := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', ← boundaryRho_offDiagonalLongSection, ih]
    exact (Function.iterate_succ_apply' _ _ _).symm

/-- Extraction of actual corrected lifts gives the prescribed finite coefficient iterates. -/
theorem offDiagonalLongExtraction_correctedLift (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (d : ℕ) (b : Old D Sc cutoff v t) :
    offDiagonalLongExtraction D Sc cutoff p j.1 v t
      (offDiagonalCorrectedLift D Sc cutoff p j v t d b) =
      (offDiagonalCoefficientRho D Sc cutoff p j v t)^[d] (Finsupp.single 0 b) := by
  rw [← offDiagonalLongSection_rho_iterate, offDiagonalLongExtraction_section]

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Corrected rho on all off-diagonal old-only classes

The arbitrary-old-Hom extraction comparison of DeformedMackeyBoundary (2).
The coefficient recurrence holds on every Target class, not only the selected
section. All total-parity and source-delta terms are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELV
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
    simp only [offDiagonalLongExtraction_eq D Sc cutoff p j.1 y]
    exact longHomExtraction_boundaryRho D Sc cutoff p j y z
  · simp only [offDiagonalLongExtraction, dite_eq_right h, LinearMap.zero_apply, map_zero]

end OddMath.QuiverHecke.ELV
end

end
