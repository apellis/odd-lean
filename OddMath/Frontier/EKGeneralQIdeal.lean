import OddMath.Frontier.EKGeneralQ
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# EK Proposition 2.3 and Corollary 2.4 at arbitrary q

Source: Ellis–Khovanov, arXiv:1107.5610v2, §2.1, p.8.

* p.8: `I ⊂ Λ'` is the radical of `(·,·)`, `I = ⊕ Iₙ`, `Λ = Λ'/I`.
* Proposition 2.3: `IΛ' = Λ'I = I`, `Δ(I) ⊂ I ⊗ Λ' + Λ' ⊗ I`.
* Corollary 2.4: `Λ` inherits a q-bialgebra structure from that of `Λ'`.

Here `Λ'`, Δ, ε, the form (2.1) and (2.2) are those of `EKGeneralQ`, with `q : k` arbitrary.

* The ideal part of Proposition 2.3 and the grading `I = ⊕ Iₙ` hold over every commutative
  ring `k` (`prop_2_3_ideal`, `radical_homogeneous`).
* The coideal part and Corollary 2.4 are proved over every principal ideal domain `k`
  (in particular every field, and `ℤ`), for every `q : k` (`prop_2_3_coideal`,
  `cor_2_4`).  The paper does not specify the base ring for these two statements; the proof
  "at once from adjointness" uses that an element of `Λ ⊗ Λ` pairing to zero with all pure
  tensors vanishes, which is proved here from the freeness of finitely generated torsion-free
  modules over a principal ideal domain.
-/
noncomputable section
open scoped TensorProduct BigOperators
namespace OddMath.Frontier.EKGeneralQ
open EKFreeCoproduct (W degree degree_one degree_mul)

variable {k : Type*} [CommRing k] (q : k)

/-! ## The radical is a two-sided, graded ideal (any `k`, any `q`) -/

theorem tensorForm_annihilates_left {x : L k} (hx : ∀ y, form q x y = 0) (a : L k)
    (z : LL k) : tensorForm q (x ⊗ₜ[k] a) z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b c => simp [hx]
  | add u v hu hv => simp only [map_add, hu, hv, add_zero]

theorem tensorForm_annihilates_right {x : L k} (hx : ∀ y, form q x y = 0) (a : L k)
    (z : LL k) : tensorForm q (a ⊗ₜ[k] x) z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b c => simp [hx]
  | add u v hu hv => simp only [map_add, hu, hv, add_zero]

/-- EK p.8: `I`, the radical of the form (2.1) on `Λ'` (a left ideal by (2.3)). -/
def radical : Ideal (L k) where
  carrier := {x | ∀ y, form q x y = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy z
    change ∀ z, form q x z = 0 at hx
    change ∀ z, form q y z = 0 at hy
    simp only [map_add, LinearMap.add_apply, hx, hy, add_zero]
  smul_mem' := by
    intro a x hx y
    change form q (a*x) y = 0
    rw [← adjointness]
    exact tensorForm_annihilates_right q hx a (coproduct q y)

@[simp] theorem mem_radical (x : L k) : x ∈ radical q ↔ ∀ y, form q x y = 0 := Iff.rfl

theorem radical_mul_left (a : L k) {x : L k} (hx : x ∈ radical q) : a*x ∈ radical q :=
  (radical q).mul_mem_left a hx

theorem radical_mul_right {x : L k} (hx : x ∈ radical q) (a : L k) : x*a ∈ radical q := by
  intro y
  rw [← adjointness]
  exact tensorForm_annihilates_left q hx a (coproduct q y)

instance : (radical q).IsTwoSided where
  mul_mem_of_left a hx := radical_mul_right q hx a

/-- EK Proposition 2.3, ideal part, literally: `IΛ' = I` and `Λ'I = I`. -/
theorem prop_2_3_ideal :
    {z : L k | ∃ x ∈ radical q, ∃ y, z = x*y} = radical q ∧
      {z : L k | ∃ y, ∃ x ∈ radical q, z = y*x} = radical q := by
  constructor
  · ext z
    constructor
    · rintro ⟨x, hx, y, rfl⟩; exact radical_mul_right q hx y
    · intro hz; exact ⟨z, hz, 1, (mul_one z).symm⟩
  · ext z
    constructor
    · rintro ⟨y, x, hx, rfl⟩; exact radical_mul_left q y hx
    · intro hz; exact ⟨1, z, hz, (one_mul z).symm⟩

variable (k) in
/-- Projection of `Λ'` onto its degree-`n` part `Λ'ₙ`. -/
def degreeProj (n : ℕ) : L k →ₗ[k] L k :=
  (wordBasis k).constr k fun w => if degree w = n then wordBasis k w else 0

@[simp] theorem degreeProj_basis (n : ℕ) (w : W) :
    degreeProj k n (wordBasis k w) = if degree w = n then wordBasis k w else 0 := by
  simp [degreeProj]

theorem parts_sum (w : W) : (∑ i, parts w i) = degree w :=
  EKPairingAdjoint.parts_sum w

/-- EK p.7: the weight spaces `Λ'ₙ` are pairwise orthogonal. -/
theorem form_degree_ne (v w : W) (h : degree v ≠ degree w) :
    form q (wordBasis k v) (wordBasis k w) = 0 := by
  rw [form_basis_mat]
  exact matForm_degree_mismatch q _ _ (by simpa only [parts_sum] using h)

theorem form_degreeProj (n : ℕ) (x y : L k) :
    form q (degreeProj k n x) y = form q x (degreeProj k n y) := by
  induction x using basis_induction k (wordBasis k) with
  | hz => simp
  | ha x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | hb v r =>
    induction y using basis_induction k (wordBasis k) with
    | hz => simp
    | ha y z hy hz => simp only [map_add, hy, hz]
    | hb w s =>
      simp only [map_smul, degreeProj_basis, LinearMap.smul_apply, smul_eq_mul]
      by_cases hv : degree v = n <;> by_cases hw : degree w = n
      · simp [hv, hw]
      · simp [hv, hw, form_degree_ne q v w (by omega)]
      · simp [hv, hw, form_degree_ne q v w (by omega)]
      · simp [hv, hw]

theorem degreeProj_self (w : W) :
    degreeProj k (degree w) (wordBasis k w) = wordBasis k w := by
  simp

/-- EK p.8: `I = ⊕ₙ Iₙ` — an element lies in `I` iff each homogeneous component does. -/
theorem radical_homogeneous (x : L k) :
    x ∈ radical q ↔ ∀ n, degreeProj k n x ∈ radical q := by
  constructor
  · intro hx n y
    rw [form_degreeProj]
    exact hx _
  · intro hx y
    induction y using basis_induction k (wordBasis k) with
    | hz => simp
    | ha y z hy hz => simp only [map_add, hy, hz, add_zero]
    | hb w r =>
      rw [map_smul, ← degreeProj_self w, ← form_degreeProj]
      simp only [hx (degree w) (wordBasis k w), smul_zero]

/-! ## The quotient `Λ = Λ'/I` and its form -/

/-- EK p.8: `Λ = Λ'/I` (written `Λ_q`). -/
abbrev Lam := L k ⧸ radical q

/-- The quotient map `Λ' → Λ`, a `k`-algebra homomorphism. -/
def piQ : L k →ₐ[k] Lam q := Ideal.Quotient.mkₐ k (radical q)

theorem piQ_surjective : Function.Surjective (piQ q) := Ideal.Quotient.mk_surjective

@[simp] theorem piQ_eq_zero_iff (x : L k) : piQ q x = 0 ↔ x ∈ radical q :=
  Ideal.Quotient.eq_zero_iff_mem

private def formRight (x : L k) : Lam q →ₗ[k] k :=
  ((radical q).restrictScalars k).liftQ (form q x) (by
    intro y hy
    change form q x y = 0
    rw [form_symm]
    exact hy x)

private theorem formRight_pi (x y : L k) : formRight q x (piQ q y) = form q x y := rfl

private def formToQuotient : L k →ₗ[k] Lam q →ₗ[k] k where
  toFun := formRight q
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := piQ_surjective q z
    simp only [LinearMap.add_apply, formRight_pi, map_add]
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := piQ_surjective q z
    simp only [LinearMap.smul_apply, formRight_pi, map_smul, RingHom.id_apply]

/-- The form induced on `Λ`. -/
def quotientForm : Lam q →ₗ[k] Lam q →ₗ[k] k :=
  ((radical q).restrictScalars k).liftQ (formToQuotient q) (by
    intro x hx
    apply LinearMap.ext
    intro y
    obtain ⟨y, rfl⟩ := piQ_surjective q y
    exact hx y)

@[simp] theorem quotientForm_pi (x y : L k) :
    quotientForm q (piQ q x) (piQ q y) = form q x y := rfl

theorem quotientForm_nondegenerate_left (x : Lam q)
    (hx : ∀ y : Lam q, quotientForm q x y = 0) : x = 0 := by
  obtain ⟨x, rfl⟩ := piQ_surjective q x
  apply (piQ_eq_zero_iff q x).mpr
  intro y
  exact hx (piQ q y)

/-! ## Counit -/

private instance uniqueMat00 (β : Fin 0 → ℕ) (α : Fin 0 → ℕ) :
    Unique (EKPairingMatrices.Mat β α) where
  default := ⟨fun i => Fin.elim0 i, funext fun i => Fin.elim0 i, funext fun j => Fin.elim0 j⟩
  uniq _ := Subtype.ext (funext fun i => Fin.elim0 i)

theorem matForm_zero_zero (β : Fin 0 → ℕ) (α : Fin 0 → ℕ) : matForm q β α = 1 := by
  unfold matForm
  rw [Fintype.sum_unique]
  simp [EKPairingMatrices.crossing]

theorem degree_eq_zero_iff (w : W) : degree w = 0 ↔ w = 1 := by
  constructor
  · intro he
    induction w using FreeMonoid.recOn with
    | h0 => rfl
    | ih i w _ =>
      simp only [degree_mul] at he
      have hi : degree (FreeMonoid.of i) = i+1 := rfl
      rw [hi] at he
      omega
  · rintro rfl; rfl

/-- The counit is the pairing with the unit: `(x, 1) = ε(x)`. -/
theorem form_right_one (x : L k) : form q x 1 = counit k x := by
  induction x using basis_induction k (wordBasis k) with
  | hz => simp
  | ha x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | hb w r =>
    simp only [map_smul, LinearMap.smul_apply, counit_word]
    congr 1
    by_cases hw : w = 1
    · subst hw
      rw [if_pos rfl, ← wordBasis_one, form_basis_mat]
      exact matForm_zero_zero q _ _
    · rw [if_neg hw, ← wordBasis_one]
      exact form_degree_ne q w 1 (by rw [degree_one]; exact (degree_eq_zero_iff w).not.mpr hw)

theorem counit_radical {x : L k} (hx : x ∈ radical q) : counit k x = 0 := by
  rw [← form_right_one q]
  exact hx 1

/-- The counit of `Λ`, a `k`-algebra homomorphism. -/
def quotientCounit : Lam q →ₐ[k] k :=
  Ideal.Quotient.liftₐ (radical q) (counitAlg k) (fun _ hx => counit_radical q hx)

@[simp] theorem quotientCounit_pi (x : L k) : quotientCounit q (piQ q x) = counit k x := rfl

/-! ## The quotient tensor map and the coideal submodule (any `k`) -/

/-- `Λ' ⊗ Λ' → Λ ⊗ Λ`. -/
def quotientTensorMap : LL k →ₗ[k] Lam q ⊗[k] Lam q :=
  TensorProduct.map (piQ q).toLinearMap (piQ q).toLinearMap

@[simp] theorem quotientTensorMap_tmul (x y : L k) :
    quotientTensorMap q (x ⊗ₜ[k] y) = piQ q x ⊗ₜ[k] piQ q y := rfl

/-- `I ⊗ Λ' + Λ' ⊗ I`, literally (images of the two subtype maps). -/
def coidealSubmodule : Submodule k (LL k) :=
  LinearMap.range (TensorProduct.map ((radical q).restrictScalars k).subtype
    (LinearMap.id : L k →ₗ[k] L k)) ⊔
  LinearMap.range (TensorProduct.map (LinearMap.id : L k →ₗ[k] L k)
    ((radical q).restrictScalars k).subtype)

theorem quotientTensorMap_eq_zero_iff (z : LL k) :
    quotientTensorMap q z = 0 ↔ z ∈ coidealSubmodule q := by
  let e := TensorProduct.quotientTensorQuotientEquiv
    ((radical q).restrictScalars k) ((radical q).restrictScalars k)
  have he : e (quotientTensorMap q z) = Submodule.Quotient.mk z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, Submodule.Quotient.mk_zero]
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, hx, hy, Submodule.Quotient.mk_add]
  rw [← e.map_eq_zero_iff, he]
  exact Submodule.Quotient.mk_eq_zero (coidealSubmodule q)

/-- Pairing with a pure tensor, on `Λ ⊗ Λ`. -/
def tensorTest (a b : Lam q) : Lam q ⊗[k] Lam q →ₗ[k] k :=
  TensorProduct.lift ((LinearMap.mul k k).compl₁₂
    ((quotientForm q).flip a) ((quotientForm q).flip b))

@[simp] theorem tensorTest_tmul (a b x y : Lam q) :
    tensorTest q a b (x ⊗ₜ[k] y) = quotientForm q x a * quotientForm q y b := rfl

theorem tensorTest_map (a b : L k) (z : LL k) :
    tensorTest q (piQ q a) (piQ q b) (quotientTensorMap q z) =
      tensorForm q z (a ⊗ₜ[k] b) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

theorem coproduct_radical_annihilates {x : L k} (hx : x ∈ radical q) (z : LL k) :
    tensorForm q (coproduct q x) z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [tensorForm_symm, adjointness, form_symm]
    exact hx (a*b)
  | add u v hu hv => simp only [map_add, hu, hv, add_zero]


/-! ## The q-twisted product descends to `Λ ⊗ Λ` (any `k`) -/

/-- Degree twist `w ↦ q^{deg w · n} w`, needed when a factor crosses an arbitrary element. -/
def twist (n : ℕ) : L k →ₗ[k] L k :=
  (wordBasis k).constr k (fun w => (q ^ (degree w * n)) • wordBasis k w)

@[simp] theorem twist_basis (n : ℕ) (w : W) :
    twist q n (wordBasis k w) = (q ^ (degree w * n)) • wordBasis k w := by
  simp [twist]

theorem form_twist (n : ℕ) (x y : L k) :
    form q (twist q n x) y = form q x (twist q n y) := by
  induction x using basis_induction k (wordBasis k) with
  | hz => simp
  | ha x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | hb v r =>
    induction y using basis_induction k (wordBasis k) with
    | hz => simp
    | ha x y hx hy => simp only [map_add, hx, hy]
    | hb w s =>
      simp only [map_smul, twist_basis, LinearMap.smul_apply, smul_eq_mul]
      by_cases h : degree v = degree w
      · rw [h]; ring
      · rw [form_degree_ne q v w h]; ring

theorem twist_radical (n : ℕ) {x : L k} (hx : x ∈ radical q) : twist q n x ∈ radical q := by
  intro y
  rw [form_twist]
  exact hx _

theorem tensorMul_basis_tmul (a b : W) (x y : L k) :
    tensorMul q (tensorBasis k (a,b)) (x ⊗ₜ[k] y) =
      (wordBasis k a * twist q (degree b) x) ⊗ₜ[k] (wordBasis k b * y) := by
  induction x using basis_induction k (wordBasis k) with
  | hz => simp
  | ha x z hx hz => simp only [TensorProduct.add_tmul, tensorMul_add_right,
      map_add, mul_add, hx, hz]
  | hb c r =>
    induction y using basis_induction k (wordBasis k) with
    | hz => simp
    | ha y z hy hz => simp only [TensorProduct.tmul_add, tensorMul_add_right,
        map_add, mul_add, hy, hz]
    | hb d s =>
      simp only [map_smul, twist_basis, mul_smul_comm, TensorProduct.smul_tmul,
        TensorProduct.tmul_smul, tensorMul_smul_right]
      rw [← tensorBasis_apply, tensorMul_basis]
      simp only [tensorBasis_apply, wordBasis_mul, TensorProduct.smul_tmul,
        TensorProduct.tmul_smul, smul_smul]
      rw [Nat.mul_comm (degree c) (degree b)]

theorem tensorMul_tmul_basis (x y : L k) (c d : W) :
    tensorMul q (x ⊗ₜ[k] y) (tensorBasis k (c,d)) =
      (x * wordBasis k c) ⊗ₜ[k] (twist q (degree c) y * wordBasis k d) := by
  induction x using basis_induction k (wordBasis k) with
  | hz => simp
  | ha x z hx hz => simp only [TensorProduct.add_tmul, tensorMul_add_left,
      map_add, add_mul, hx, hz]
  | hb a r =>
    induction y using basis_induction k (wordBasis k) with
    | hz => simp
    | ha y z hy hz => simp only [TensorProduct.tmul_add, tensorMul_add_left,
        map_add, add_mul, hy, hz]
    | hb b s =>
      simp only [map_smul, twist_basis, smul_mul_assoc, TensorProduct.smul_tmul,
        TensorProduct.tmul_smul, tensorMul_smul_left]
      rw [← tensorBasis_apply, tensorMul_basis]
      simp only [tensorBasis_apply, wordBasis_mul, TensorProduct.smul_tmul,
        TensorProduct.tmul_smul, smul_smul]
      congr 1
      ring

theorem kills_tensor_kernel {M : Type*} [AddCommGroup M] [Module k M]
    (f : LL k →ₗ[k] M)
    (h₁ : ∀ x ∈ radical q, ∀ y, f (x ⊗ₜ[k] y) = 0)
    (h₂ : ∀ y ∈ radical q, ∀ x, f (x ⊗ₜ[k] y) = 0)
    {z : LL k} (hz : quotientTensorMap q z = 0) : f z = 0 := by
  have hle : coidealSubmodule q ≤ LinearMap.ker f := by
    apply sup_le
    · rintro _ ⟨t, rfl⟩
      change f (TensorProduct.map ((radical q).restrictScalars k).subtype LinearMap.id t) = 0
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simpa using h₁ x x.property y
      | add a b ha hb => simp only [map_add, ha, hb, add_zero]
    · rintro _ ⟨t, rfl⟩
      change f (TensorProduct.map LinearMap.id ((radical q).restrictScalars k).subtype t) = 0
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simpa using h₂ y y.property x
      | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  exact hle ((quotientTensorMap_eq_zero_iff q z).mp hz)

theorem tensor_kernel_mul_right (x : LL k) {z : LL k} (hz : quotientTensorMap q z = 0) :
    quotientTensorMap q (tensorMul q x z) = 0 := by
  induction x using basis_induction k (tensorBasis k) with
  | hz => simp
  | ha x y hx hy => simp only [tensorMul_add_left, map_add, hx, hy, add_zero]
  | hb p r =>
    simp only [tensorMul_smul_left, map_smul]
    suffices quotientTensorMap q (tensorMul q (tensorBasis k p) z) = 0 by rw [this, smul_zero]
    apply kills_tensor_kernel q
      ((quotientTensorMap q).comp (tensorMulLinear q (tensorBasis k p))) ?_ ?_ hz
    · intro a ha b
      change quotientTensorMap q (tensorMul q (tensorBasis k p) (a ⊗ₜ[k] b)) = 0
      rw [tensorMul_basis_tmul, quotientTensorMap_tmul,
        (piQ_eq_zero_iff q _).mpr (radical_mul_left q _ (twist_radical q _ ha)),
        TensorProduct.zero_tmul]
    · intro b hb a
      change quotientTensorMap q (tensorMul q (tensorBasis k p) (a ⊗ₜ[k] b)) = 0
      rw [tensorMul_basis_tmul, quotientTensorMap_tmul,
        (piQ_eq_zero_iff q _).mpr (radical_mul_left q _ hb), TensorProduct.tmul_zero]

theorem tensor_kernel_mul_left {z : LL k} (hz : quotientTensorMap q z = 0) (y : LL k) :
    quotientTensorMap q (tensorMul q z y) = 0 := by
  induction y using basis_induction k (tensorBasis k) with
  | hz => simp
  | ha x y hx hy => simp only [tensorMul_add_right, map_add, hx, hy, add_zero]
  | hb p r =>
    simp only [tensorMul_smul_right, map_smul]
    suffices quotientTensorMap q (tensorMul q z (tensorBasis k p)) = 0 by rw [this, smul_zero]
    apply kills_tensor_kernel q
      ((quotientTensorMap q).comp ((tensorMulLinear q).flip (tensorBasis k p))) ?_ ?_ hz
    · intro a ha b
      change quotientTensorMap q (tensorMul q (a ⊗ₜ[k] b) (tensorBasis k p)) = 0
      rw [tensorMul_tmul_basis, quotientTensorMap_tmul,
        (piQ_eq_zero_iff q _).mpr (radical_mul_right q ha _), TensorProduct.zero_tmul]
    · intro b hb a
      change quotientTensorMap q (tensorMul q (a ⊗ₜ[k] b) (tensorBasis k p)) = 0
      rw [tensorMul_tmul_basis, quotientTensorMap_tmul,
        (piQ_eq_zero_iff q _).mpr (radical_mul_right q (twist_radical q _ hb) _),
        TensorProduct.tmul_zero]

theorem quotientTensorMap_surjective : Function.Surjective (quotientTensorMap q) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul x y =>
    obtain ⟨a, rfl⟩ := piQ_surjective q x
    obtain ⟨b, rfl⟩ := piQ_surjective q y
    exact ⟨a ⊗ₜ[k] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a+b, map_add _ _ _⟩

/-- Linear descent along `Λ' ⊗ Λ' → Λ ⊗ Λ`. -/
def descendTensor {M : Type*} [AddCommGroup M] [Module k M]
    (f : LL k →ₗ[k] M) (hf : ∀ z, quotientTensorMap q z = 0 → f z = 0) :
    (Lam q ⊗[k] Lam q) →ₗ[k] M :=
  ((LinearMap.ker (quotientTensorMap q)).liftQ f hf).comp
    ((quotientTensorMap q).quotKerEquivOfSurjective
      (quotientTensorMap_surjective q)).symm.toLinearMap

@[simp] theorem descendTensor_map {M : Type*} [AddCommGroup M] [Module k M]
    (f : LL k →ₗ[k] M) (hf : ∀ z, quotientTensorMap q z = 0 → f z = 0) (z : LL k) :
    descendTensor q f hf (quotientTensorMap q z) = f z := by
  let e := (quotientTensorMap q).quotKerEquivOfSurjective (quotientTensorMap_surjective q)
  change (LinearMap.ker (quotientTensorMap q)).liftQ f hf (e.symm (quotientTensorMap q z)) = _
  have he : e (Submodule.Quotient.mk z) = quotientTensorMap q z := rfl
  rw [← he, e.symm_apply_apply]
  rfl

private def mulRight (x : LL k) : (Lam q ⊗[k] Lam q) →ₗ[k] Lam q ⊗[k] Lam q :=
  descendTensor q ((quotientTensorMap q).comp (tensorMulLinear q x))
    (fun _ hz => tensor_kernel_mul_right q x hz)

private theorem mulRight_map (x y : LL k) :
    mulRight q x (quotientTensorMap q y) = quotientTensorMap q (tensorMul q x y) :=
  descendTensor_map q _ _ _

private def mulToQuotient : LL k →ₗ[k] (Lam q ⊗[k] Lam q) →ₗ[k] Lam q ⊗[k] Lam q where
  toFun := mulRight q
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := quotientTensorMap_surjective q z
    simp only [LinearMap.add_apply, mulRight_map, tensorMul_add_left, map_add]
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := quotientTensorMap_surjective q z
    simp only [LinearMap.smul_apply, mulRight_map, tensorMul_smul_left, map_smul,
      RingHom.id_apply]

/-- EK p.5 product `(x₁⊗x₂)(y₁⊗y₂) = q^{deg x₂ deg y₁} x₁y₁ ⊗ x₂y₂`, on `Λ ⊗ Λ`. -/
def quotientTensorMul : (Lam q ⊗[k] Lam q) →ₗ[k] (Lam q ⊗[k] Lam q) →ₗ[k] Lam q ⊗[k] Lam q :=
  descendTensor q (mulToQuotient q) (by
    intro x hx
    apply LinearMap.ext
    intro y
    obtain ⟨y, rfl⟩ := quotientTensorMap_surjective q y
    change mulRight q x (quotientTensorMap q y) = 0
    rw [mulRight_map]
    exact tensor_kernel_mul_left q hx y)

@[simp] theorem quotientTensorMul_map (x y : LL k) :
    quotientTensorMul q (quotientTensorMap q x) (quotientTensorMap q y) =
      quotientTensorMap q (tensorMul q x y) := by
  unfold quotientTensorMul
  rw [descendTensor_map]
  exact mulRight_map q x y

theorem quotientTensorMul_assoc (x y z : Lam q ⊗[k] Lam q) :
    quotientTensorMul q (quotientTensorMul q x y) z =
      quotientTensorMul q x (quotientTensorMul q y z) := by
  obtain ⟨x, rfl⟩ := quotientTensorMap_surjective q x
  obtain ⟨y, rfl⟩ := quotientTensorMap_surjective q y
  obtain ⟨z, rfl⟩ := quotientTensorMap_surjective q z
  simp only [quotientTensorMul_map, tensorMul_assoc]

@[simp] theorem quotientTensorMap_one :
    quotientTensorMap q (tensorOne k) = ((1 : Lam q) ⊗ₜ[k] (1 : Lam q)) := by
  simp [tensorOne]

theorem quotientTensorMul_one_left (x : Lam q ⊗[k] Lam q) :
    quotientTensorMul q ((1 : Lam q) ⊗ₜ[k] (1 : Lam q)) x = x := by
  obtain ⟨x, rfl⟩ := quotientTensorMap_surjective q x
  rw [← quotientTensorMap_one, quotientTensorMul_map, tensorMul_one_left]

theorem quotientTensorMul_one_right (x : Lam q ⊗[k] Lam q) :
    quotientTensorMul q x ((1 : Lam q) ⊗ₜ[k] (1 : Lam q)) = x := by
  obtain ⟨x, rfl⟩ := quotientTensorMap_surjective q x
  rw [← quotientTensorMap_one, quotientTensorMul_map, tensorMul_one_right]

/-- The literal EK p.5 rule on images of words in `Λ ⊗ Λ`. -/
theorem quotientTensorMul_hWords (α β γ δ : List ℕ) :
    quotientTensorMul q (piQ q (hWord k α) ⊗ₜ[k] piQ q (hWord k β))
      (piQ q (hWord k γ) ⊗ₜ[k] piQ q (hWord k δ)) =
      (q ^ (β.sum * γ.sum)) •
        ((piQ q (hWord k α) * piQ q (hWord k γ)) ⊗ₜ[k] (piQ q (hWord k β) * piQ q (hWord k δ))) := by
  rw [← quotientTensorMap_tmul, ← quotientTensorMap_tmul, quotientTensorMul_map,
    tensorMul_hWords, map_smul, quotientTensorMap_tmul, map_mul, map_mul]

/-! ## Tensor separation over a principal ideal domain -/

section PID
variable [IsDomain k] [IsPrincipalIdealRing k]

instance quotient_noZeroSMulDivisors : NoZeroSMulDivisors k (Lam q) where
  eq_zero_or_eq_zero_of_smul_eq_zero := by
    intro r x h
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    apply quotientForm_nondegenerate_left
    intro y
    have hh := congrArg (fun z => quotientForm q z y) h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, map_zero,
      LinearMap.zero_apply] at hh
    exact (mul_eq_zero.mp hh).resolve_left hr

/-- An element of `Λ ⊗ Λ` pairing to zero with every pure tensor vanishes. -/
theorem tensor_separation (z : Lam q ⊗[k] Lam q)
    (hz : ∀ a b : Lam q, tensorTest q a b z = 0) : z = 0 := by
  classical
  obtain ⟨M, hM, hm⟩ := TensorProduct.exists_finite_submodule_left_of_finite
    ({z} : Set (Lam q ⊗[k] Lam q)) (Set.finite_singleton z)
  letI : Module.Finite k M := hM
  obtain ⟨w, hw⟩ := hm (Set.mem_singleton z)
  obtain ⟨n, B⟩ := Module.basisOfFiniteTypeTorsionFree' (R := k) (M := M)
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_left B w
  have hw' : (∑ i : Fin n, (B i : Lam q) ⊗ₜ[k] c i) = z := by
    rw [← hw, ← hc]
    simp [Finsupp.sum_fintype, LinearMap.rTensor, TensorProduct.map_tmul]
  have hcoeff (b : Lam q) : ∀ i : Fin n, quotientForm q (c i) b = 0 := by
    have hv : (∑ i : Fin n, quotientForm q (c i) b • (B i : Lam q)) = 0 := by
      apply quotientForm_nondegenerate_left
      intro a
      have hh := hz a b
      rw [← hw'] at hh
      simpa only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, tensorTest_tmul, mul_comm] using hh
    have hi := B.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
    exact (Fintype.linearIndependent_iff.mp hi) _ hv
  have hc0 : ∀ i : Fin n, c i = 0 := by
    intro i
    exact quotientForm_nondegenerate_left q (c i) (fun b => hcoeff b i)
  rw [← hw']
  simp [hc0]

theorem coproduct_radical_zero {x : L k} (hx : x ∈ radical q) :
    quotientTensorMap q (coproduct q x) = 0 := by
  apply tensor_separation
  intro a b
  obtain ⟨a, rfl⟩ := piQ_surjective q a
  obtain ⟨b, rfl⟩ := piQ_surjective q b
  rw [tensorTest_map]
  exact coproduct_radical_annihilates q hx _

/-- EK Proposition 2.3, coideal part: `Δ(I) ⊂ I ⊗ Λ' + Λ' ⊗ I` (any PID `k`, any `q`). -/
theorem prop_2_3_coideal {x : L k} (hx : x ∈ radical q) :
    coproduct q x ∈ coidealSubmodule q :=
  (quotientTensorMap_eq_zero_iff q _).mp (coproduct_radical_zero q hx)

/-- The coproduct of `Λ` (EK Corollary 2.4). -/
def quotientCoproduct : Lam q →ₗ[k] Lam q ⊗[k] Lam q :=
  ((radical q).restrictScalars k).liftQ ((quotientTensorMap q).comp (coproduct q))
    (fun _ hx => coproduct_radical_zero q hx)

@[simp] theorem quotientCoproduct_pi (x : L k) :
    quotientCoproduct q (piQ q x) = quotientTensorMap q (coproduct q x) := rfl

omit [IsDomain k] [IsPrincipalIdealRing k] in
private theorem assoc_quotient (t : LL k) (y : L k) :
    TensorProduct.assoc k (Lam q) (Lam q) (Lam q) (quotientTensorMap q t ⊗ₜ[k] piQ q y) =
    TensorProduct.map (piQ q).toLinearMap (quotientTensorMap q)
      (TensorProduct.assoc k (L k) (L k) (L k) (t ⊗ₜ[k] y)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero]
  | tmul a b => simp
  | add a b ha hb => simp only [LinearMap.map_add, LinearEquiv.map_add, TensorProduct.add_tmul, ha, hb]

private theorem left_iterated_map (z : LL k) :
    TensorProduct.assoc k (Lam q) (Lam q) (Lam q)
      (TensorProduct.map (quotientCoproduct q) LinearMap.id (quotientTensorMap q z)) =
    TensorProduct.map (piQ q).toLinearMap (quotientTensorMap q)
      (TensorProduct.assoc k (L k) (L k) (L k) (TensorProduct.map (coproduct q) LinearMap.id z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero]
  | tmul x y =>
    simpa only [quotientTensorMap_tmul, TensorProduct.map_tmul,
      quotientCoproduct_pi, LinearMap.id_apply] using assoc_quotient q (coproduct q x) y
  | add x y hx hy => simp only [LinearMap.map_add, LinearEquiv.map_add, hx, hy]

private theorem right_iterated_map (z : LL k) :
    TensorProduct.map LinearMap.id (quotientCoproduct q) (quotientTensorMap q z) =
    TensorProduct.map (piQ q).toLinearMap (quotientTensorMap q)
      (TensorProduct.map LinearMap.id (coproduct q) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero]
  | tmul x y => simp
  | add x y hx hy => simp only [LinearMap.map_add, LinearEquiv.map_add, hx, hy]

theorem quotient_coassociativity (x : Lam q) :
    TensorProduct.assoc k (Lam q) (Lam q) (Lam q)
      (TensorProduct.map (quotientCoproduct q) LinearMap.id (quotientCoproduct q x)) =
    TensorProduct.map LinearMap.id (quotientCoproduct q) (quotientCoproduct q x) := by
  obtain ⟨x, rfl⟩ := piQ_surjective q x
  rw [quotientCoproduct_pi, left_iterated_map, right_iterated_map, coassociativity]

omit [IsDomain k] [IsPrincipalIdealRing k] in
private theorem left_counit_map (z : LL k) :
    TensorProduct.lid k (Lam q)
      (TensorProduct.map (quotientCounit q).toLinearMap LinearMap.id (quotientTensorMap q z)) =
    piQ q (leftCounit k z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero, map_zero (piQ q)]
  | tmul x y =>
    simp only [quotientTensorMap_tmul, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      quotientCounit_pi, LinearMap.id_apply, TensorProduct.lid_tmul, leftCounit_tmul]
    exact ((piQ q).toLinearMap.map_smul (counit k x) y).symm
  | add x y hx hy => simp only [LinearMap.map_add, LinearEquiv.map_add, map_add (piQ q), hx, hy]

omit [IsDomain k] [IsPrincipalIdealRing k] in
private theorem right_counit_map (z : LL k) :
    TensorProduct.rid k (Lam q)
      (TensorProduct.map LinearMap.id (quotientCounit q).toLinearMap (quotientTensorMap q z)) =
    piQ q (rightCounit k z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero, map_zero (piQ q)]
  | tmul x y =>
    simp only [quotientTensorMap_tmul, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      quotientCounit_pi, LinearMap.id_apply, TensorProduct.rid_tmul, rightCounit_tmul]
    exact ((piQ q).toLinearMap.map_smul (counit k y) x).symm
  | add x y hx hy => simp only [LinearMap.map_add, LinearEquiv.map_add, map_add (piQ q), hx, hy]

theorem quotient_counit_left (x : Lam q) :
    TensorProduct.lid k (Lam q)
      (TensorProduct.map (quotientCounit q).toLinearMap LinearMap.id (quotientCoproduct q x)) =
      x := by
  obtain ⟨x, rfl⟩ := piQ_surjective q x
  rw [quotientCoproduct_pi, left_counit_map, (counit_laws q x).1]

theorem quotient_counit_right (x : Lam q) :
    TensorProduct.rid k (Lam q)
      (TensorProduct.map LinearMap.id (quotientCounit q).toLinearMap (quotientCoproduct q x)) =
      x := by
  obtain ⟨x, rfl⟩ := piQ_surjective q x
  rw [quotientCoproduct_pi, right_counit_map, (counit_laws q x).2]

theorem quotient_coproduct_mul (x y : Lam q) :
    quotientCoproduct q (x*y) =
      quotientTensorMul q (quotientCoproduct q x) (quotientCoproduct q y) := by
  obtain ⟨x, rfl⟩ := piQ_surjective q x
  obtain ⟨y, rfl⟩ := piQ_surjective q y
  rw [← map_mul, quotientCoproduct_pi, coproduct_mul, quotientCoproduct_pi,
    quotientCoproduct_pi, quotientTensorMul_map]

theorem quotient_coproduct_one :
    quotientCoproduct q (1 : Lam q) = (1 : Lam q) ⊗ₜ[k] (1 : Lam q) := by
  have h := quotientCoproduct_pi q 1
  rwa [map_one, coproduct_one, quotientTensorMap_one] at h

/-- EK Corollary 2.4 at arbitrary `q`, over any principal ideal domain `k`: `Λ = Λ'/I` is a
`k`-algebra, `Λ ⊗ Λ` carries the q-twisted product (associative, unital, given on words by
EK p.5), and the descended Δ, ε make `Λ` a q-bialgebra (Δ unital and multiplicative for the
q-twisted product, coassociative, counital; ε an algebra map). -/
theorem cor_2_4 :
    (∀ x y z : Lam q ⊗[k] Lam q, quotientTensorMul q (quotientTensorMul q x y) z =
      quotientTensorMul q x (quotientTensorMul q y z)) ∧
    (∀ x : Lam q ⊗[k] Lam q, quotientTensorMul q ((1 : Lam q) ⊗ₜ[k] (1 : Lam q)) x = x ∧
      quotientTensorMul q x ((1 : Lam q) ⊗ₜ[k] (1 : Lam q)) = x) ∧
    (∀ α β γ δ : List ℕ, quotientTensorMul q (piQ q (hWord k α) ⊗ₜ[k] piQ q (hWord k β))
      (piQ q (hWord k γ) ⊗ₜ[k] piQ q (hWord k δ)) = (q ^ (β.sum * γ.sum)) •
        ((piQ q (hWord k α) * piQ q (hWord k γ)) ⊗ₜ[k]
          (piQ q (hWord k β) * piQ q (hWord k δ)))) ∧
    (∀ x : L k, quotientCoproduct q (piQ q x) = quotientTensorMap q (coproduct q x)) ∧
    quotientCoproduct q 1 = (1 : Lam q) ⊗ₜ[k] (1 : Lam q) ∧
    (∀ x y : Lam q, quotientCoproduct q (x*y) =
      quotientTensorMul q (quotientCoproduct q x) (quotientCoproduct q y)) ∧
    (∀ x : Lam q, TensorProduct.assoc k (Lam q) (Lam q) (Lam q)
      (TensorProduct.map (quotientCoproduct q) LinearMap.id (quotientCoproduct q x)) =
      TensorProduct.map LinearMap.id (quotientCoproduct q) (quotientCoproduct q x)) ∧
    (∀ x : Lam q, TensorProduct.lid k (Lam q)
      (TensorProduct.map (quotientCounit q).toLinearMap LinearMap.id (quotientCoproduct q x)) = x ∧
      TensorProduct.rid k (Lam q)
      (TensorProduct.map LinearMap.id (quotientCounit q).toLinearMap (quotientCoproduct q x)) = x) ∧
    (∀ x : L k, quotientCounit q (piQ q x) = counit k x) :=
  ⟨quotientTensorMul_assoc q,
    fun x => ⟨quotientTensorMul_one_left q x, quotientTensorMul_one_right q x⟩,
    quotientTensorMul_hWords q, quotientCoproduct_pi q, quotient_coproduct_one q,
    quotient_coproduct_mul q, quotient_coassociativity q,
    fun x => ⟨quotient_counit_left q x, quotient_counit_right q x⟩, quotientCounit_pi q⟩

end PID

end OddMath.Frontier.EKGeneralQ
