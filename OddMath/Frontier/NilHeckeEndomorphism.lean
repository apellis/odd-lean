import OddMath.Frontier.NilHeckeBasis
import OddMath.Frontier.NilHeckeRightKernel
import OddMath.Frontier.SchubertBasis

/-! EKL1111.1320v1 p13 Corollary 2.14: integral, ungraded, natural action.
Right coefficients throughout; composition acts rightmost first. -/
namespace OddMath.Frontier.NilHeckeEndomorphism
open NilHeckeAction NilCoxeterWords OddSchubertAction
open OddMath.SkewPolynomial (SkewPolynomial monomial)
open scoped BigOperators
noncomputable section
abbrev K (n : ℕ) := OddSymmetricKernel.kernelSubring n

def rightKernelEnd (n : ℕ) : Subring (Module.End ℤ (SkewPolynomial (n+2))) where
  carrier := {T | ∀ (f : SkewPolynomial (n+2)) (k : K n), T (f * (k : SkewPolynomial (n+2))) = T f * k}
  zero_mem' := by simp
  one_mem' := by intro f k; rfl
  add_mem' := by
    intro T U hT hU f k
    simp only [LinearMap.add_apply, hT f k, hU f k, add_mul]
  neg_mem' := by
    intro T hT f k
    simp only [LinearMap.neg_apply, hT f k, neg_mul]
  mul_mem' := by
    intro T U hT hU f k
    change T (U (f * (k : SkewPolynomial (n+2)))) = T (U f) * k
    rw [hU, hT]

def restrictedAction (n : ℕ) : Presented n →+* rightKernelEnd n :=
  (action n).codRestrict (rightKernelEnd n) (fun a f k =>
    NilHeckeRightKernel.action_right_mul_kernel n a k f)

@[simp] theorem restrictedAction_apply (n : ℕ) (a : Presented n) (f : SkewPolynomial (n+2)) :
    (restrictedAction n a).val f = action n a f := rfl

theorem restrictedAction_injective (n : ℕ) : Function.Injective (restrictedAction n) := by
  intro a b h
  exact NilHeckeBasis.action_injective n (congrArg Subtype.val h)

/-- Every polynomial left multiplication is an actual presented action. -/
theorem exists_left (n : ℕ) (p : SkewPolynomial (n+2)) :
    ∃ a : Presented n, ∀ f, action n a f = p * f := by
  classical
  induction p using Finsupp.induction with
  | zero => exact ⟨0, by simp⟩
  | @single_add a c p _ _ ih =>
    obtain ⟨b,hb⟩ := ih
    refine ⟨c • NilHeckeBasis.dotMonomial a + b, ?_⟩
    intro f
    simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply,
      NilHeckeBasis.action_dotMonomial, hb, add_mul]
    congr 1
    rw [← smul_mul_assoc]
    congr 1
    change c • Finsupp.single a (1 : ℤ) = Finsupp.single a c
    simp

/-- Unit diagonal normalization uses an integral sign, not division. -/
theorem normalized_self {n : ℕ} (w : Perm n) :
    SchubertBasis.diagonal w • dividedElementOperator w (schubert w) = 1 := by
  have hone : (1 : SkewPolynomial (n+2)) (0 : Fin (n+2) → ℕ) = 1 := Finsupp.single_eq_same
  rcases action_self w with h | h <;>
    simp [SchubertBasis.diagonal, SchubertBasis.selector_apply, h, hone]

/-- Interpolate arbitrary polynomial values on all Schubert basis vectors.
At each increasing length, normalized D_w fixes one new value without changing shorter ones. -/
theorem interpolate (n : ℕ) (y : Perm n → SkewPolynomial (n+2)) :
    ∃ a : Presented n, ∀ w, action n a (schubert w) = y w := by
  classical
  have step : ∀ k : ℕ, ∃ a : Presented n, ∀ w, length w < k → action n a (schubert w) = y w := by
    intro k
    induction k with
    | zero => exact ⟨0, by intro w h; omega⟩
    | succ k ih =>
      obtain ⟨a,ha⟩ := ih
      choose b hb using exists_left n
      let S := Finset.univ.filter (fun w : Perm n => length w = k)
      let c := fun w : Perm n => b (y w - action n a (schubert w)) *
        (SchubertBasis.diagonal w • dividedElement w)
      refine ⟨a + ∑ w ∈ S, c w, ?_⟩
      intro v hv
      have hc (w : Perm n) : action n (c w) (schubert v) =
          (y w - action n a (schubert w)) *
            (SchubertBasis.diagonal w • dividedElementOperator w (schubert v)) := by
        simp only [c, action_mul_apply, map_zsmul, LinearMap.smul_apply, hb]
        rfl
      simp only [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply]
      simp_rw [hc]
      by_cases hkv : length v = k
      · rw [Finset.sum_eq_single v]
        · rw [normalized_self, mul_one]; abel
        · intro w hw hne
          have hwk := (Finset.mem_filter.mp hw).2
          rw [action_same_length_distinct w v (hkv.trans hwk.symm) (Ne.symm hne),
            smul_zero, mul_zero]
        · intro hn
          exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkv⟩)).elim
      · rw [Finset.sum_eq_zero]
        · simpa using ha v (by omega)
        · intro w hw
          have hwk := (Finset.mem_filter.mp hw).2
          rw [action_shorter w v (by omega), smul_zero, mul_zero]
  obtain ⟨a,ha⟩ := step ((n+2).choose 2 + 1)
  exact ⟨a,fun w => ha w (by have := length_le_max w; omega)⟩

/-- Right-linear endomorphisms are determined by their actual Schubert values. -/
theorem end_ext {n : ℕ} (T U : rightKernelEnd n)
    (h : ∀ w, T.val (schubert w) = U.val (schubert w)) : T = U := by
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  obtain ⟨c,hc,_⟩ := SchubertBasis.right_kernel_decomposition_unique n f
  rw [hc, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [T.property, U.property, h]

theorem restrictedAction_surjective (n : ℕ) : Function.Surjective (restrictedAction n) := by
  intro T
  obtain ⟨a,ha⟩ := interpolate n (fun w => T.val (schubert w))
  exact ⟨a, end_ext _ _ ha⟩

/-- Ungraded integral natural-action isomorphism, with no conclusion hypothesis. -/
def actionEquiv (n : ℕ) : Presented n ≃+* rightKernelEnd n :=
  RingEquiv.ofBijective (restrictedAction n)
    ⟨restrictedAction_injective n, restrictedAction_surjective n⟩

@[simp] theorem actionEquiv_apply (n : ℕ) (a : Presented n) (f : SkewPolynomial (n+2)) :
    (actionEquiv n a).val f = action n a f := rfl

/-- Synthesis with coefficients on the RIGHT. -/
def synthesis (n : ℕ) : (Perm n → K n) →ₗ[ℤ] SkewPolynomial (n+2) where
  toFun c := ∑ w, schubert w * (c w : SkewPolynomial (n+2))
  map_add' c d := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' z c := by
    simp only [Pi.smul_apply, AddSubgroupClass.coe_zsmul, mul_smul_comm, Finset.smul_sum]
    rfl

theorem synthesis_bijective (n : ℕ) : Function.Bijective (synthesis n) := by
  constructor
  · intro c d h
    obtain ⟨e,_,hu⟩ := SchubertBasis.right_kernel_decomposition_unique n (synthesis n c)
    exact (hu c rfl).trans (hu d h).symm
  · intro f
    obtain ⟨c,hc,_⟩ := SchubertBasis.right_kernel_decomposition_unique n f
    exact ⟨c,hc.symm⟩

def coordinates (n : ℕ) : SkewPolynomial (n+2) ≃ₗ[ℤ] (Perm n → K n) :=
  (LinearEquiv.ofBijective (synthesis n) (synthesis_bijective n)).symm

@[simp] theorem coordinates_synthesis (n : ℕ) (c : Perm n → K n) :
    coordinates n (synthesis n c) = c := (coordinates n).apply_symm_apply c

@[simp] theorem synthesis_coordinates (n : ℕ) (f : SkewPolynomial (n+2)) :
    synthesis n (coordinates n f) = f := (coordinates n).symm_apply_apply f

theorem coordinates_right_mul (n : ℕ) (f : SkewPolynomial (n+2)) (k : K n) :
    coordinates n (f * (k : SkewPolynomial (n+2))) = fun i => coordinates n f i * k := by
  apply (synthesis_bijective n).1
  rw [synthesis_coordinates]
  change f * (k : SkewPolynomial (n+2)) = ∑ i, schubert i * ((coordinates n f i * k : K n) : SkewPolynomial (n+2))
  simp only [Subring.coe_mul, ← mul_assoc, ← Finset.sum_mul]
  rw [show (∑ i, schubert i * (coordinates n f i : SkewPolynomial (n+2))) = f from
    synthesis_coordinates n f]

@[simp] theorem coordinates_schubert (n : ℕ) (w : Perm n) :
    coordinates n (schubert w) = Pi.single w 1 := by
  classical
  have h : synthesis n (Pi.single w 1) = schubert w := by
    simp [synthesis, Pi.single_apply, apply_ite]
  rw [← h, coordinates_synthesis]

/-- Column j is the RIGHT Schubert coefficient vector of T(s_j). -/
def toMatrix (n : ℕ) (T : rightKernelEnd n) : Matrix (Perm n) (Perm n) (K n) :=
  fun i j => coordinates n (T.val (schubert j)) i

/-- Coefficient columns transform by LEFT matrix multiplication in noncommutative K. -/
theorem coefficient_evaluation (n : ℕ) (T : rightKernelEnd n)
    (f : SkewPolynomial (n+2)) (i : Perm n) :
    coordinates n (T.val f) i = ∑ j, toMatrix n T i j * coordinates n f j := by
  have hf := synthesis_coordinates n f
  have he : T.val f = ∑ j, T.val (schubert j) * (coordinates n f j : SkewPolynomial (n+2)) := by
    conv_lhs => rw [← hf]
    simp only [synthesis, LinearMap.coe_mk, AddHom.coe_mk, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact T.property _ _
  rw [he, map_sum]
  simp only [Finset.sum_apply, coordinates_right_mul, toMatrix]

/-- The actual polynomial evaluation formula, not just a matrix-ring cardinality. -/
theorem polynomial_evaluation (n : ℕ) (T : rightKernelEnd n) (f : SkewPolynomial (n+2)) :
    T.val f = ∑ i, schubert i * ((∑ j, toMatrix n T i j * coordinates n f j : K n) : SkewPolynomial (n+2)) := by
  conv_lhs => rw [← synthesis_coordinates n (T.val f)]
  simp only [synthesis, LinearMap.coe_mk, AddHom.coe_mk, coefficient_evaluation]

def matrixHom (n : ℕ) : rightKernelEnd n →+* Matrix (Perm n) (Perm n) (K n) where
  toFun := toMatrix n
  map_one' := by
    classical
    funext i j
    change coordinates n (schubert j) i = (1 : Matrix (Perm n) (Perm n) (K n)) i j
    rw [coordinates_schubert]
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]
  map_mul' T U := by
    funext i j
    exact coefficient_evaluation n T (U.val (schubert j)) i
  map_zero' := by ext i j; simp [toMatrix]
  map_add' T U := by ext i j; simp [toMatrix]

def fromMatrix (n : ℕ) (M : Matrix (Perm n) (Perm n) (K n)) : rightKernelEnd n :=
  ⟨{ toFun := fun f => synthesis n (fun i => ∑ j, M i j * coordinates n f j)
     map_add' := by
       intro f g
       simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
       exact (synthesis n).map_add _ _
     map_smul' := by
       intro z f
       simp only [map_smul, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum]
       exact (synthesis n).map_smul z _ }, by
    intro f k
    change synthesis n (fun i => ∑ j, M i j * coordinates n (f * (k : SkewPolynomial (n+2))) j) =
      synthesis n (fun i => ∑ j, M i j * coordinates n f j) * (k : SkewPolynomial (n+2))
    rw [coordinates_right_mul]
    simp only [← mul_assoc, ← Finset.sum_mul]
    simp [synthesis, Finset.sum_mul, mul_assoc]⟩

@[simp] theorem toMatrix_fromMatrix (n : ℕ) (M : Matrix (Perm n) (Perm n) (K n)) :
    toMatrix n (fromMatrix n M) = M := by
  classical
  funext i j
  change coordinates n (synthesis n (fun a => ∑ b, M a b * coordinates n (schubert j) b)) i = M i j
  rw [coordinates_synthesis, coordinates_schubert]
  simp [Pi.single_apply]

theorem toMatrix_injective (n : ℕ) : Function.Injective (toMatrix n) := by
  intro T U h
  apply end_ext
  intro w
  apply (coordinates n).injective
  funext i
  exact congrFun (congrFun h i) w

/-- The Schubert matrix-ring equivalence over K itself, not Kᵐᵒᵖ. -/
def matrixEquiv (n : ℕ) : rightKernelEnd n ≃+* Matrix (Perm n) (Perm n) (K n) :=
  RingEquiv.ofBijective (matrixHom n)
    ⟨toMatrix_injective n, fun M => ⟨fromMatrix n M, toMatrix_fromMatrix n M⟩⟩

@[simp] theorem matrixEquiv_apply (n : ℕ) (T : rightKernelEnd n) (i j : Perm n) :
    matrixEquiv n T i j = coordinates n (T.val (schubert j)) i := rfl

end
end OddMath.Frontier.NilHeckeEndomorphism
