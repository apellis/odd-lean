import OddMath.Frontier.EKGeneralQSign
import OddMath.Frontier.EKGeneralQBaseChange
import OddMath.Frontier.EKGeneralQCommutative
import Mathlib.Data.ZMod.Basic

/-!
# EK Proposition 2.3 (coideal part) and Corollary 2.4 over an arbitrary commutative ring

Source: Ellis–Khovanov, arXiv:1107.5610v2, §2.1, p.8.  "Fix `q ∈ k` and define a symmetric
`k`-bilinear form on `Λ'`" (2.1); `I` is its radical, `Λ = Λ'/I`.

* Proposition 2.3: `IΛ' = Λ'I = I`, `Δ(I) ⊂ I ⊗ Λ' + Λ' ⊗ I`.
* Corollary 2.4: `Λ` inherits a q-bialgebra structure from that of `Λ'`.

The ideal part holds for every `k` and `q` (`EKGeneralQ.prop_2_3_ideal`).  For the coideal part:

* It FAILS for `k = ℤ/4`, `q = 2` (`coideal_counterexample`, module
  `EKGeneralQCounterexample`): the element `x = h₁₂₁ + h₁₃ + h₃₁ + h₄` lies in `I`, but
  `Δ(x) ∉ I ⊗ Λ' + Λ' ⊗ I`; consequently `Δ` does not descend to a map `Λ → Λ ⊗ Λ` and
  Corollary 2.4 fails as stated (`no_quotient_coproduct`).  The obstruction lives in
  `Λ₂ ⊗ Λ₂`: `Λ₂ ≅ ℤ/4 ⊕ ℤ/2` is not flat, and the coefficient of `h₁₁ ⊗ h₁₁` in `Δ(x)`
  is detected by a functional with values in `ℤ/2` that kills `I`.
* What holds for every `k` and `q`: `Δ(I)` lies in the radical of the form (2.2) on
  `Λ' ⊗ Λ'` (`EKGeneralQ.coproduct_radical_annihilates`).
* Repaired statement (`prop_2_3_coideal_of_separating`, `cor_2_4_of_separating`): if pure
  tensors separate the points of `Λ ⊗ Λ` (`Separating q`), then `Δ(I) ⊂ I ⊗ Λ' + Λ' ⊗ I` and
  Corollary 2.4 holds.  `Separating q` holds
  - over every principal ideal domain, for every `q` (`separating_of_pid`);
  - whenever `Λ` has a basis with a dual family for the form (`separating_of_dual`);
  - hence for `q = -1` over EVERY commutative ring (`separating_neg_one`: basis `h_λ`, dual
    family the images of the integral `m_λ`), and for `q = 1` over EVERY commutative ring
    (`separating_one`: basis `h_λ`, dual family from the unimodular classical Gram matrix).

So Proposition 2.3 and Corollary 2.4 hold as printed over every `k` in the two cases the paper
uses (`q = -1`, the odd case, and `q = 1`, the classical case), and over every field for every
`q`, but not over every commutative ring for every `q`.
-/
noncomputable section
open scoped TensorProduct BigOperators
namespace OddMath.Frontier.EKGeneralQ
open EKFreeCoproduct (W degree partWord partWord_degree)

variable {k : Type*} [CommRing k]
attribute [local instance] Classical.propDecidable

/-! ## The separation property and the coideal -/

/-- Pure tensors separate the points of `Λ ⊗ Λ`. -/
def Separating (q : k) : Prop :=
  ∀ z : Lam q ⊗[k] Lam q, (∀ a b : Lam q, tensorTest q a b z = 0) → z = 0

section Separating

variable {q : k} (hsep : Separating q)
include hsep

theorem coproduct_radical_zero_of_separating {x : L k} (hx : x ∈ radical q) :
    quotientTensorMap q (coproduct q x) = 0 := by
  apply hsep
  intro a b
  obtain ⟨a, rfl⟩ := piQ_surjective q a
  obtain ⟨b, rfl⟩ := piQ_surjective q b
  rw [tensorTest_map]
  exact coproduct_radical_annihilates q hx _

/-- EK Proposition 2.3, coideal part, under `Separating q`. -/
theorem prop_2_3_coideal_of_separating {x : L k} (hx : x ∈ radical q) :
    coproduct q x ∈ coidealSubmodule q :=
  (quotientTensorMap_eq_zero_iff q _).mp (coproduct_radical_zero_of_separating hsep hx)

/-- The coproduct of `Λ`, under `Separating q`. -/
def sepCoproduct : Lam q →ₗ[k] Lam q ⊗[k] Lam q :=
  ((radical q).restrictScalars k).liftQ ((quotientTensorMap q).comp (coproduct q))
    (fun _ hx => coproduct_radical_zero_of_separating hsep hx)

@[simp] theorem sepCoproduct_pi (x : L k) :
    sepCoproduct hsep (piQ q x) = quotientTensorMap q (coproduct q x) := rfl

omit hsep in
private theorem assoc_quotient' (t : LL k) (y : L k) :
    TensorProduct.assoc k (Lam q) (Lam q) (Lam q) (quotientTensorMap q t ⊗ₜ[k] piQ q y) =
    TensorProduct.map (piQ q).toLinearMap (quotientTensorMap q)
      (TensorProduct.assoc k (L k) (L k) (L k) (t ⊗ₜ[k] y)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero]
  | tmul a b => simp
  | add a b ha hb => simp only [LinearMap.map_add, LinearEquiv.map_add, TensorProduct.add_tmul,
      ha, hb]

theorem sep_coassociativity (x : Lam q) :
    TensorProduct.assoc k (Lam q) (Lam q) (Lam q)
      (TensorProduct.map (sepCoproduct hsep) LinearMap.id (sepCoproduct hsep x)) =
    TensorProduct.map LinearMap.id (sepCoproduct hsep) (sepCoproduct hsep x) := by
  obtain ⟨x, rfl⟩ := piQ_surjective q x
  have hl : ∀ z : LL k, TensorProduct.assoc k (Lam q) (Lam q) (Lam q)
      (TensorProduct.map (sepCoproduct hsep) LinearMap.id (quotientTensorMap q z)) =
      TensorProduct.map (piQ q).toLinearMap (quotientTensorMap q)
        (TensorProduct.assoc k (L k) (L k) (L k)
          (TensorProduct.map (coproduct q) LinearMap.id z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero]
    | tmul a b =>
      simpa only [quotientTensorMap_tmul, TensorProduct.map_tmul, sepCoproduct_pi,
        LinearMap.id_apply] using assoc_quotient' (coproduct q a) b
    | add a b ha hb => simp only [LinearMap.map_add, LinearEquiv.map_add, ha, hb]
  have hr : ∀ z : LL k,
      TensorProduct.map LinearMap.id (sepCoproduct hsep) (quotientTensorMap q z) =
      TensorProduct.map (piQ q).toLinearMap (quotientTensorMap q)
        (TensorProduct.map LinearMap.id (coproduct q) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [LinearMap.map_zero]
    | tmul a b => simp
    | add a b ha hb => simp only [LinearMap.map_add, ha, hb]
  rw [sepCoproduct_pi, hl, hr, coassociativity]

theorem sep_counit_left (x : Lam q) :
    TensorProduct.lid k (Lam q)
      (TensorProduct.map (quotientCounit q).toLinearMap LinearMap.id (sepCoproduct hsep x)) = x := by
  obtain ⟨x, rfl⟩ := piQ_surjective q x
  have h : ∀ z : LL k, TensorProduct.lid k (Lam q)
      (TensorProduct.map (quotientCounit q).toLinearMap LinearMap.id (quotientTensorMap q z)) =
      piQ q (leftCounit k z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, map_zero (piQ q)]
    | tmul a b =>
      simp only [quotientTensorMap_tmul, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        quotientCounit_pi, LinearMap.id_apply, TensorProduct.lid_tmul, leftCounit_tmul]
      exact ((piQ q).toLinearMap.map_smul (counit k a) b).symm
    | add a b ha hb => simp only [LinearMap.map_add, LinearEquiv.map_add, map_add (piQ q), ha, hb]
  rw [sepCoproduct_pi, h, (counit_laws q x).1]

theorem sep_counit_right (x : Lam q) :
    TensorProduct.rid k (Lam q)
      (TensorProduct.map LinearMap.id (quotientCounit q).toLinearMap (sepCoproduct hsep x)) = x := by
  obtain ⟨x, rfl⟩ := piQ_surjective q x
  have h : ∀ z : LL k, TensorProduct.rid k (Lam q)
      (TensorProduct.map LinearMap.id (quotientCounit q).toLinearMap (quotientTensorMap q z)) =
      piQ q (rightCounit k z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, map_zero (piQ q)]
    | tmul a b =>
      simp only [quotientTensorMap_tmul, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        quotientCounit_pi, LinearMap.id_apply, TensorProduct.rid_tmul, rightCounit_tmul]
      exact ((piQ q).toLinearMap.map_smul (counit k b) a).symm
    | add a b ha hb => simp only [LinearMap.map_add, LinearEquiv.map_add, map_add (piQ q), ha, hb]
  rw [sepCoproduct_pi, h, (counit_laws q x).2]

theorem sep_coproduct_mul (x y : Lam q) :
    sepCoproduct hsep (x*y) =
      quotientTensorMul q (sepCoproduct hsep x) (sepCoproduct hsep y) := by
  obtain ⟨x, rfl⟩ := piQ_surjective q x
  obtain ⟨y, rfl⟩ := piQ_surjective q y
  rw [← map_mul, sepCoproduct_pi, coproduct_mul, sepCoproduct_pi, sepCoproduct_pi,
    quotientTensorMul_map]

theorem sep_coproduct_one :
    sepCoproduct hsep (1 : Lam q) = (1 : Lam q) ⊗ₜ[k] (1 : Lam q) := by
  have h := sepCoproduct_pi hsep 1
  rwa [map_one, coproduct_one, quotientTensorMap_one] at h

/-- EK Corollary 2.4 under `Separating q` (arbitrary commutative `k`). -/
theorem cor_2_4_of_separating :
    (∀ x y z : Lam q ⊗[k] Lam q, quotientTensorMul q (quotientTensorMul q x y) z =
      quotientTensorMul q x (quotientTensorMul q y z)) ∧
    (∀ x : Lam q ⊗[k] Lam q, quotientTensorMul q ((1 : Lam q) ⊗ₜ[k] (1 : Lam q)) x = x ∧
      quotientTensorMul q x ((1 : Lam q) ⊗ₜ[k] (1 : Lam q)) = x) ∧
    (∀ x : L k, sepCoproduct hsep (piQ q x) = quotientTensorMap q (coproduct q x)) ∧
    sepCoproduct hsep 1 = (1 : Lam q) ⊗ₜ[k] (1 : Lam q) ∧
    (∀ x y : Lam q, sepCoproduct hsep (x*y) =
      quotientTensorMul q (sepCoproduct hsep x) (sepCoproduct hsep y)) ∧
    (∀ x : Lam q, TensorProduct.assoc k (Lam q) (Lam q) (Lam q)
      (TensorProduct.map (sepCoproduct hsep) LinearMap.id (sepCoproduct hsep x)) =
      TensorProduct.map LinearMap.id (sepCoproduct hsep) (sepCoproduct hsep x)) ∧
    (∀ x : Lam q, TensorProduct.lid k (Lam q)
      (TensorProduct.map (quotientCounit q).toLinearMap LinearMap.id (sepCoproduct hsep x)) = x ∧
      TensorProduct.rid k (Lam q)
      (TensorProduct.map LinearMap.id (quotientCounit q).toLinearMap (sepCoproduct hsep x)) = x) ∧
    (∀ x : L k, quotientCounit q (piQ q x) = counit k x) :=
  ⟨quotientTensorMul_assoc q,
    fun x => ⟨quotientTensorMul_one_left q x, quotientTensorMul_one_right q x⟩,
    sepCoproduct_pi hsep, sep_coproduct_one hsep, sep_coproduct_mul hsep,
    sep_coassociativity hsep, fun x => ⟨sep_counit_left hsep x, sep_counit_right hsep x⟩,
    quotientCounit_pi q⟩

end Separating

/-! ## Sufficient conditions for separation -/

theorem separating_of_pid [IsDomain k] [IsPrincipalIdealRing k] (q : k) : Separating q :=
  tensor_separation q

/-- If `Λ` has a basis `b` and a family `d` with `(bᵢ, dⱼ) = δᵢⱼ`, pure tensors separate. -/
theorem separating_of_dual (q : k) {ι : Type*} (b : Basis ι k (Lam q)) (d : ι → Lam q)
    (hd : ∀ i j, quotientForm q (b i) (d j) = if i = j then 1 else 0) : Separating q := by
  classical
  intro z hz
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b z
  have hc : ∀ j, c j = 0 := by
    intro j
    apply quotientForm_nondegenerate_left
    intro y
    have h := hz (d j) y
    rw [Finsupp.sum, map_sum] at h
    simp only [tensorTest_tmul, hd] at h
    rw [Finset.sum_eq_single j] at h
    · simpa using h
    · intro i _ hij; simp [hij]
    · intro hj; simp [Finsupp.not_mem_support_iff.mp hj]
  have : c = 0 := Finsupp.ext hc
  simp [this]

/-- `q = -1`, any commutative ring. -/
theorem separating_neg_one : Separating (-1 : k) := by
  classical
  refine separating_of_dual (-1 : k) hBasisK
    (fun μ => piQ (-1 : k) (iota k (mLift μ))) ?_
  intro i j
  rw [hBasisK_apply]
  have h := coordK_h (k := k) i j
  rw [coordK, LinearMap.flip_apply] at h
  exact h

/-- `q = 1`, any commutative ring. -/
theorem separating_one : Separating (1 : k) := by
  classical
  refine separating_of_dual (1 : k) hBasisOne (fun μ => piQ (1 : k) (dualOne k μ)) ?_
  intro i j
  rw [hBasisOne_apply, quotientForm_pi, form_dualOne]

/-- EK Proposition 2.3 (coideal part) at `q = -1`, over every commutative ring. -/
theorem prop_2_3_coideal_neg_one {x : L k} (hx : x ∈ radical (-1 : k)) :
    coproduct (-1 : k) x ∈ coidealSubmodule (-1 : k) :=
  prop_2_3_coideal_of_separating separating_neg_one hx

/-- EK Proposition 2.3 (coideal part) at `q = 1`, over every commutative ring. -/
theorem prop_2_3_coideal_one {x : L k} (hx : x ∈ radical (1 : k)) :
    coproduct (1 : k) x ∈ coidealSubmodule (1 : k) :=
  prop_2_3_coideal_of_separating separating_one hx

end OddMath.Frontier.EKGeneralQ
