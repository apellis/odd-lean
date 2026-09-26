import OddMath.Frontier.EKOverKChar2
import OddMath.Frontier.EKOverKHopf
import OddMath.Frontier.EKCenterPower
import OddMath.Frontier.EKRestSuperCenter
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Flat.Basic

/-!
# EK §3.2 over `k`: Proposition 3.4 and the centre

Source: Ellis–Khovanov, arXiv:1107.5610v2, §3.2 (pp. 25–26), stated over a field of
characteristic `0`.  `p_n = m_{(n)}` is the element dual to `h_n` (`EKCenterPower.p`).

* Prop. 3.4 over an arbitrary commutative ring `k` (`proposition_3_4_K`): for `n ≥ 1`,
  `p_n` is central in `Λ_k` iff `n` is even or `2 = 0` in `k`.  In particular, over every `k`
  with `2 ≠ 0` (every field of characteristic `≠ 2`), `p_n` is central iff `n` is even.
* p. 26 over every commutative `ℚ`-algebra `k` (in particular every field of characteristic
  `0`):
  - `centerK_iff`: `w ∈ Λ_k` is central iff `w ∈ k[p₂, p₄, …]`;
  - `algebraicIndependent_pK`: the `p_{2j}` are algebraically independent over `k`;
  - `centerEquivK : MvPolynomial ℕ k ≃ₐ[k] Z(Λ_k)`, `X_j ↦ p_{2(j+1)}`;
  - `superCentralK_odd`: a homogeneous supercentral element of odd degree is `0`;
  - `supercenterK_eq_center` (pp. 3, 26): the centre equals the supercentre (the span of the
    homogeneous supercentral elements).

Over a `ℚ`-algebra `k`, `Λ_k = k ⊗_ℚ Λ_ℚ` (`thetaEquivK`), and the centre of `k ⊗_ℚ Λ_ℚ` is
`k ⊗_ℚ Z(Λ_ℚ)` because `k` is free over `ℚ`; the case `k = ℚ` is `EKFinal.center_eq`.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct BigOperators

namespace OddMath.Frontier.EKOverK
open EKGeneralQ

variable {k : Type*} [CommRing k]

/-! ## Proposition 3.4 over `k` -/

variable (k) in
/-- `p_n ∈ Λ_k`, the image of the integral `p_n = m_{(n)}` (EK §3.2). -/
def pK (n : ℕ) : LamK k := psiRing (EKCenterPower.p n)

section IntegralValues
open CompleteElementary EKPairingAdjoint EKRadicalQuotient EKCenterPower EKCenterPowerControls

/-- For odd `n ≥ 3`: `(p_n h_1, h_n h_1) = 1` and `(h_1 p_n, h_n h_1) = -1` over `ℤ`. -/
theorem pairing_values_odd (n : ℕ) (hn3 : 3 ≤ n) (hn : Odd n) :
    quotientPairing (p n * EKElementaryQuotient.h 1) (pi (h n * h 1)) = 1 ∧
    quotientPairing (EKElementaryQuotient.h 1 * p n) (pi (h n * h 1)) = -1 := by
  obtain ⟨P, hP⟩ := pi_surjective (p n)
  rw [← hP]
  simp only [EKElementaryQuotient.h, ← map_mul, quotientPairing_pi]
  rw [pairing_mul_two, pairing_mul_two]
  constructor
  · rw [Fintype.sum_eq_single (Fin.last n)]
    · simp [Fin.sum_univ_two, pairing_h_two, phiP_k hP (by omega),
        phiP_mismatch hP n 1 (by omega)]
    · intro i hi
      have hik : i.val < n := by
        have := i.isLt
        have : i.val ≠ n := fun h => hi (Fin.ext (by simp [h]))
        omega
      apply Finset.sum_eq_zero
      intro j _
      have := j.isLt
      rw [pairing_h_two]
      rcases (show j.val = 0 ∨ j.val = 1 by omega) with hj | hj
      · rw [if_neg (by omega)]; simp
      · by_cases h1 : i.val = n - 1
        · rw [hj, h1, phiP_km1 hP (by omega)]; simp
        · rw [if_neg (by omega)]; simp
  · rw [Fintype.sum_eq_single 0]
    · simp [Fin.sum_univ_two, pairing_h_two, phiP_k hP (by omega), hn.neg_one_pow,
        phiP_mismatch hP n 1 (by omega)]
    · intro i hi
      have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
      apply Finset.sum_eq_zero
      intro j _
      have := j.isLt
      rw [pairing_h_two]
      rcases (show j.val = 0 ∨ j.val = 1 by omega) with hj | hj
      · by_cases h1 : i.val = 1
        · rw [hj, h1]; simp [phiP_km1 hP (k := n) (by omega)]
        · rw [if_neg (by omega)]; simp
      · rw [if_neg (by omega)]; simp

theorem p_one : p 1 = EKElementaryQuotient.h 1 := by
  rw [p, rowShape_one]
  exact p1_fixture

end IntegralValues

theorem two_eq_zero_of_h1h2_comm (h : hK k 1 * hK k 2 = hK k 2 * hK k 1) : (2 : k) = 0 := by
  have h' := h2h1_add_h1h2 (k := k)
  rw [h, ← two_smul k, ← hBasisK_yd21, ← hBasisK_yd3] at h'
  have := congrArg (fun x => (hBasisK (k := k)).repr x yd21) h'
  simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne yd21_ne_yd3.symm, smul_eq_mul, mul_one, mul_zero] at this
  exact this

/-- Central images: if `z` is central in `Λ_ℤ`, then `ψ(z)` is central in `Λ_k`. -/
theorem psiRing_central {z : QZ} (hz : ∀ y : QZ, z * y = y * z) (w : LamK k) :
    psiRing z * w = w * psiRing z := by
  induction w using induction_psi with
  | h0 => simp
  | hadd x y hx hy => rw [mul_add, add_mul, hx, hy]
  | hsm c y => rw [mul_smul_comm, smul_mul_assoc, ← map_mul, ← map_mul, hz]

/-- **EK Proposition 3.4 over every commutative ring `k`.**  For `n ≥ 1`, `p_n` is central in
`Λ_k` iff `n` is even or `2 = 0` in `k`. -/
theorem proposition_3_4_K (n : ℕ) (hn : 1 ≤ n) :
    (∀ y : LamK k, pK k n * y = y * pK k n) ↔ (Even n ∨ (2 : k) = 0) := by
  constructor
  · intro hc
    by_contra hne
    push_neg at hne
    obtain ⟨hodd, h2⟩ := hne
    have ho : Odd n := Nat.not_even_iff_odd.mp hodd
    by_cases h1 : n = 1
    · subst h1
      apply h2
      apply two_eq_zero_of_h1h2_comm
      have := hc (hK k 2)
      rw [pK, p_one] at this
      exact this
    · have hn3 : 3 ≤ n := by obtain ⟨t, ht⟩ := ho; omega
      obtain ⟨v1, v2⟩ := pairing_values_odd n hn3 ho
      have := congrArg (fun w => quotientForm (-1 : k) w
        (psiRing (EKRadicalQuotient.pi (CompleteElementary.h n * CompleteElementary.h 1))))
        (hc (hK k 1))
      simp only [pK, hK, ← map_mul, EKFinal.quotientForm_psiRing, v1, v2] at this
      apply h2
      have h3 : ((1 : ℤ) : k) = ((-1 : ℤ) : k) := this
      push_cast at h3
      rw [← one_add_one_eq_two]
      nth_rewrite 1 [h3]
      exact neg_add_cancel 1
  · rintro (he | h2) y
    · exact psiRing_central (EKCenterPower.central_of_even n (by omega) he) y
    · exact mul_comm_of_two h2 _ _

/-! ## `Λ_k = k ⊗_ℚ Λ_ℚ` for a `ℚ`-algebra `k` -/

section RatAlgebra

variable [Algebra ℚ k]

variable (k) in
/-- `Λ_ℚ → Λ_k`, as a `ℚ`-algebra map (`h_n ↦ h_n`). -/
def ratToK : LamK ℚ →ₐ[ℚ] LamK k :=
  (Algebra.TensorProduct.lift (Algebra.ofId ℚ (LamK k)) (psiRing (k := k)).toIntAlgHom
    (fun _ _ => Algebra.commutes' _ _)).comp (EKFinal.baseChangeAlgEquiv ℚ).symm.toAlgHom

@[simp] theorem ratToK_psiRing (z : QZ) : ratToK k (psiRing z) = psiRing z := by
  simp [ratToK, baseChangeAlgEquiv_symm_psiRing]

variable (k) in
/-- `k ⊗_ℚ Λ_ℚ → Λ_k`, `c ⊗ w ↦ c · w`. -/
def thetaK : k ⊗[ℚ] LamK ℚ →ₐ[k] LamK k :=
  Algebra.TensorProduct.lift (Algebra.ofId k (LamK k)) (ratToK k) (fun _ _ => Algebra.commutes' _ _)

@[simp] theorem thetaK_tmul (c : k) (w : LamK ℚ) : thetaK k (c ⊗ₜ[ℚ] w) = c • ratToK k w := by
  simp [thetaK, Algebra.smul_def, Algebra.ofId_apply]

variable (k) in
/-- `Λ_k → k ⊗_ℚ Λ_ℚ`, the inverse of `thetaK`. -/
def thetaInvK : LamK k →ₐ[k] k ⊗[ℚ] LamK ℚ :=
  (Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft : k →ₐ[k] k ⊗[ℚ] LamK ℚ)
    ((Algebra.TensorProduct.includeRight : LamK ℚ →ₐ[ℚ] k ⊗[ℚ] LamK ℚ).toRingHom.comp
      (psiRing (k := ℚ))).toIntAlgHom
    (fun c w => by
      change (c ⊗ₜ[ℚ] (1 : LamK ℚ)) * ((1 : k) ⊗ₜ[ℚ] psiRing w) =
        ((1 : k) ⊗ₜ[ℚ] psiRing w) * (c ⊗ₜ[ℚ] (1 : LamK ℚ))
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        one_mul, one_mul, mul_one])).comp (EKFinal.baseChangeAlgEquiv k).symm.toAlgHom

@[simp] theorem thetaInvK_psiRing (z : QZ) :
    thetaInvK k (psiRing z) = (1 : k) ⊗ₜ[ℚ] psiRing z := by
  simp [thetaInvK, baseChangeAlgEquiv_symm_psiRing]

theorem thetaK_thetaInvK (x : LamK k) : thetaK k (thetaInvK k x) = x := by
  have h := algHom_ext (F := (thetaK k).comp (thetaInvK k)) (G := AlgHom.id k (LamK k))
    (fun z => by simp)
  exact AlgHom.congr_fun h x

theorem thetaInvK_ratToK (w : LamK ℚ) : thetaInvK k (ratToK k w) = (1 : k) ⊗ₜ[ℚ] w := by
  have h := linearMap_ext (k := ℚ)
    (F := ((thetaInvK k).restrictScalars ℚ).toLinearMap ∘ₗ (ratToK k).toLinearMap)
    (G := (Algebra.TensorProduct.includeRight : LamK ℚ →ₐ[ℚ] k ⊗[ℚ] LamK ℚ).toLinearMap)
    (fun z => by simp)
  exact LinearMap.congr_fun h w

theorem thetaInvK_thetaK (x : k ⊗[ℚ] LamK ℚ) : thetaInvK k (thetaK k x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c w =>
    rw [thetaK_tmul, map_smul, thetaInvK_ratToK, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

variable (k) in
/-- `k ⊗_ℚ Λ_ℚ ≅ Λ_k` as `k`-algebras, for every commutative `ℚ`-algebra `k`. -/
def thetaEquivK : k ⊗[ℚ] LamK ℚ ≃ₐ[k] LamK k :=
  AlgEquiv.ofAlgHom (thetaK k) (thetaInvK k) (AlgHom.ext thetaK_thetaInvK)
    (AlgHom.ext thetaInvK_thetaK)

theorem ratToK_pQ (n : ℕ) : ratToK k (EKFinal.pQ n) = pK k n := by
  rw [EKFinal.pQ, ratToK_psiRing]; rfl

/-! ### The centre -/

variable (k) in
/-- `k[p₂, p₄, …] ⊆ Λ_k`. -/
def pAlgK : Subalgebra k (LamK k) :=
  Algebra.adjoin k (Set.range fun j : ℕ => pK k (2 * (j + 1)))

theorem tmul_one_commute {B : Type*} [Ring B] [Algebra ℚ B] (c : k) (u : k ⊗[ℚ] B) :
    u * (c ⊗ₜ[ℚ] (1 : B)) = (c ⊗ₜ[ℚ] (1 : B)) * u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul, mul_comm]
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]

/-- In `k ⊗_ℚ B` (with `k` commutative), commuting with `1 ⊗ B` is being central. -/
theorem central_of_commute_includeRight {B : Type*} [Ring B] [Algebra ℚ B]
    {w : k ⊗[ℚ] B} (hw : ∀ b : B, w * ((1 : k) ⊗ₜ[ℚ] b) = ((1 : k) ⊗ₜ[ℚ] b) * w)
    (y : k ⊗[ℚ] B) : w * y = y * w := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c b =>
    have hcb : c ⊗ₜ[ℚ] b = (c ⊗ₜ[ℚ] (1 : B)) * ((1 : k) ⊗ₜ[ℚ] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hcb, ← mul_assoc, tmul_one_commute, mul_assoc, hw, ← mul_assoc]
  | add a b ha hb => rw [mul_add, add_mul, ha, hb]

/-- The image of `k ⊗_ℚ ℚ[p₂, p₄, …]` in `k ⊗_ℚ Λ_ℚ`. -/
abbrev pTensor : Subalgebra ℚ (k ⊗[ℚ] LamK ℚ) :=
  (Algebra.TensorProduct.map (AlgHom.id ℚ k) (EKFinal.pAlg).val).range

theorem center_tensor_iff (w : k ⊗[ℚ] LamK ℚ) : (∀ y, w * y = y * w) ↔ w ∈ pTensor := by
  haveI : Module.Free ℚ k := Module.Free.of_divisionRing ℚ k
  have hc := Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct ℚ k (LamK ℚ)
  rw [EKFinal.center_eq] at hc
  rw [pTensor, ← hc, Subalgebra.mem_centralizer_iff]
  constructor
  · rintro hw _ ⟨b, rfl⟩
    exact (hw _).symm
  · intro hw
    apply central_of_commute_includeRight
    intro b
    exact (hw _ ⟨b, rfl⟩).symm

theorem ratToK_mem_pAlgK {s : LamK ℚ} (hs : s ∈ EKFinal.pAlg) : ratToK k s ∈ pAlgK k := by
  rw [EKFinal.pAlg] at hs
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [ratToK_pQ]
    exact Algebra.subset_adjoin ⟨j, rfl⟩
  | algebraMap q =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply ℚ k (LamK k)]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem thetaK_mem_of_mem {v : k ⊗[ℚ] LamK ℚ} (hv : v ∈ pTensor) : thetaK k v ∈ pAlgK k := by
  obtain ⟨x, rfl⟩ := (AlgHom.mem_range _).mp hv
  clear hv
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | tmul c s =>
    rw [Algebra.TensorProduct.map_tmul, thetaK_tmul]
    exact Subalgebra.smul_mem _ (ratToK_mem_pAlgK s.2) c
  | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb

theorem thetaInvK_mem_of_mem {w : LamK k} (hw : w ∈ pAlgK k) : thetaInvK k w ∈ pTensor := by
  rw [pAlgK] at hw
  induction hw using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine (AlgHom.mem_range _).mpr
      ⟨(1 : k) ⊗ₜ[ℚ] ⟨EKFinal.pQ (2 * (j + 1)), Algebra.subset_adjoin ⟨j, rfl⟩⟩, ?_⟩
    show _ = thetaInvK k (psiRing (EKCenterPower.p (2 * (j + 1))))
    rw [Algebra.TensorProduct.map_tmul, thetaInvK_psiRing]
    rfl
  | algebraMap c =>
    rw [AlgHom.commutes]
    refine (AlgHom.mem_range _).mpr ⟨c ⊗ₜ[ℚ] 1, ?_⟩
    rw [Algebra.TensorProduct.map_tmul, map_one, Algebra.TensorProduct.algebraMap_apply]
    rfl
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

/-- **EK p. 26 over every commutative `ℚ`-algebra `k` (e.g. every field of characteristic
`0`):** `w ∈ Λ_k` is central iff `w ∈ k[p₂, p₄, …]`. -/
theorem centerK_iff (w : LamK k) : (∀ y : LamK k, w * y = y * w) ↔ w ∈ pAlgK k := by
  set e := thetaEquivK k
  obtain ⟨v, rfl⟩ := e.surjective w
  have h1 : (∀ y : LamK k, e v * y = y * e v) ↔ (∀ y, v * y = y * v) := by
    constructor
    · intro h y
      apply e.injective
      rw [map_mul, map_mul, h]
    · intro h y
      obtain ⟨y, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, h]
  rw [h1, center_tensor_iff]
  constructor
  · exact thetaK_mem_of_mem
  · intro hv
    have := thetaInvK_mem_of_mem hv
    change thetaInvK k (thetaK k v) ∈ _ at this
    rwa [thetaInvK_thetaK] at this

theorem centerK_eq : Subalgebra.center k (LamK k) = pAlgK k := by
  ext w
  rw [Subalgebra.mem_center_iff, ← centerK_iff]
  exact ⟨fun h y => (h y).symm, fun h y => (h y).symm⟩

theorem pK_even_central (j : ℕ) : pK k (2 * (j + 1)) ∈ Subalgebra.center k (LamK k) := by
  rw [centerK_eq]
  exact Algebra.subset_adjoin ⟨j, rfl⟩

variable (k) in
/-- `p_{2(j+1)}` as an element of the centre of `Λ_k`. -/
def pcK (j : ℕ) : Subalgebra.center k (LamK k) := ⟨pK k (2 * (j + 1)), pK_even_central j⟩

theorem map_id_injective {B C : Type*} [Ring B] [Ring C] [Algebra ℚ B] [Algebra ℚ C]
    (f : B →ₐ[ℚ] C) (hf : Function.Injective f) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id k k) f) := by
  haveI : Module.Free ℚ k := Module.Free.of_divisionRing ℚ k
  have he : ⇑(Algebra.TensorProduct.map (AlgHom.id k k) f) = ⇑(f.toLinearMap.lTensor k) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  rw [he]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hf

set_option maxHeartbeats 1000000 in
theorem map_center_central (x : k ⊗[ℚ] Subalgebra.center ℚ (LamK ℚ)) (y : k ⊗[ℚ] LamK ℚ) :
    Algebra.TensorProduct.map (AlgHom.id k k) (Subalgebra.center ℚ (LamK ℚ)).val x * y =
      y * Algebra.TensorProduct.map (AlgHom.id k k) (Subalgebra.center ℚ (LamK ℚ)).val x := by
  apply central_of_commute_includeRight
  intro b
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c z =>
    have hz : b * (z : LamK ℚ) = z * b := Subalgebra.mem_center_iff.mp z.2 b
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hz]
  | add a c ha hc =>
    rw [map_add, add_mul, mul_add, ha, hc]

theorem thetaK_map_center_central (x : k ⊗[ℚ] Subalgebra.center ℚ (LamK ℚ)) (y : LamK k) :
    thetaK k (Algebra.TensorProduct.map (AlgHom.id k k) (Subalgebra.center ℚ (LamK ℚ)).val x) * y =
      y * thetaK k
        (Algebra.TensorProduct.map (AlgHom.id k k) (Subalgebra.center ℚ (LamK ℚ)).val x) := by
  obtain ⟨y, rfl⟩ := (thetaEquivK k).surjective y
  change _ * thetaK k y = thetaK k y * _
  rw [← map_mul, ← map_mul, map_center_central]

/-- `k ⊗_ℚ Z(Λ_ℚ) → Z(Λ_k)`. -/
def centerMapK : k ⊗[ℚ] Subalgebra.center ℚ (LamK ℚ) →ₐ[k] Subalgebra.center k (LamK k) :=
  ((thetaK k).comp (Algebra.TensorProduct.map (AlgHom.id k k)
    (Subalgebra.center ℚ (LamK ℚ)).val)).codRestrict _ (by
      intro x
      rw [Subalgebra.mem_center_iff, AlgHom.comp_apply]
      intro y
      exact (thetaK_map_center_central x y).symm)

theorem centerMapK_injective : Function.Injective (centerMapK (k := k)) := by
  intro a b h
  have h' := congrArg Subtype.val h
  change thetaK k _ = thetaK k _ at h'
  exact map_id_injective _ Subtype.val_injective ((thetaEquivK k).injective h')

/-- **EK p. 26 over every commutative `ℚ`-algebra `k`:** the `p_{2j}` (`j ≥ 1`) are
algebraically independent over `k` (in the centre of `Λ_k`). -/
theorem algebraicIndependent_pK : AlgebraicIndependent k (pcK k) := by
  let F : MvPolynomial ℕ k →ₐ[k] Subalgebra.center k (LamK k) :=
    centerMapK.comp ((Algebra.TensorProduct.map (AlgHom.id k k)
      (MvPolynomial.aeval EKFinal.pcK)).comp
      (MvPolynomial.algebraTensorAlgEquiv ℚ k).symm.toAlgHom)
  have hF : F = MvPolynomial.aeval (pcK k) := by
    apply MvPolynomial.algHom_ext
    intro j
    apply Subtype.ext
    simp only [F, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
      MvPolynomial.algebraTensorAlgEquiv_symm_X, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, MvPolynomial.aeval_X]
    change thetaK k ((1 : k) ⊗ₜ[ℚ] EKFinal.pQ (2 * (j + 1))) = pK k (2 * (j + 1))
    rw [thetaK_tmul, one_smul, ratToK_pQ]
  have hinj : Function.Injective F :=
    centerMapK_injective.comp ((map_id_injective (k := k) _ EKFinal.algebraicIndependent_p).comp
      (AlgEquiv.injective _))
  rw [hF] at hinj
  exact hinj

theorem adjoin_pcK_eq_top : Algebra.adjoin k (Set.range (pcK k)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  have hz : z.val ∈ pAlgK k := (centerK_eq (k := k)) ▸ z.2
  have hmap : (Algebra.adjoin k (Set.range (pcK k))).map (Subalgebra.center k (LamK k)).val =
      pAlgK k := by
    rw [AlgHom.map_adjoin, pAlgK, ← Set.range_comp]
    rfl
  rw [← hmap] at hz
  obtain ⟨u, hu, he⟩ := hz
  have : u = z := Subtype.ext he
  rwa [← this]

variable (k) in
/-- **EK p. 26 over every commutative `ℚ`-algebra `k`:** the centre of `Λ_k` is the polynomial
algebra on the `p_{2j}`: `MvPolynomial ℕ k ≅ Z(Λ_k)`, `X_j ↦ p_{2(j+1)}`. -/
def centerEquivK : MvPolynomial ℕ k ≃ₐ[k] Subalgebra.center k (LamK k) :=
  (algebraicIndependent_pK (k := k)).aevalEquiv.trans
    ((Subalgebra.equivOfEq _ _ adjoin_pcK_eq_top).trans Subalgebra.topEquiv)

theorem centerEquivK_X (j : ℕ) :
    ((centerEquivK k (MvPolynomial.X j) : Subalgebra.center k (LamK k)) : LamK k) =
      pK k (2 * (j + 1)) := by
  simp [centerEquivK, pcK]

/-! ### The supercentre -/

omit [Algebra ℚ k] in
/-- The homogeneous decomposition commutes with base change. -/
theorem decomposeK_psiRing (x : QZ) (d : ℕ) :
    decomposeK (psiRing (k := k) x) d = psiRing (EKIntegralBases.decompose x d) := by
  induction x using EKPairingAdjoint.basis_induction EKIntegralBases.hBasis with
  | hz => simp
  | ha x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply,
      map_add]
  | hb μ r =>
    simp only [map_zsmul, Finsupp.smul_apply]
    rw [EKIntegralBases.hBasis_apply, ← hBasisK_eq_psiRing, decomposeK_hBasisK,
      EKIntegralBases.decompose_hPartition]
    by_cases hd : μ.card = d
    · subst hd; rw [Finsupp.single_eq_same, Finsupp.single_eq_same, hBasisK_eq_psiRing]
    · rw [Finsupp.single_eq_of_ne hd, Finsupp.single_eq_of_ne hd, map_zero]

theorem psiRing_rat_injective : Function.Injective (psiRing (k := ℚ)) := by
  intro x y h
  rw [← EKFinal.ratEquiv_iota, ← EKFinal.ratEquiv_iota] at h
  exact EKRest.iota_injective ((EKFinal.baseChangeAlgEquiv ℚ).injective h)

theorem psiRing_rat_surj (w : LamK ℚ) : ∃ x : QZ, ∃ N : ℤ, N ≠ 0 ∧ (N : ℚ) • w = psiRing x := by
  obtain ⟨x, N, hN, h⟩ := EKRest.iota_surj ((EKFinal.baseChangeAlgEquiv ℚ).symm w)
  refine ⟨x, N, hN, ?_⟩
  have := congrArg (EKFinal.baseChangeAlgEquiv ℚ) h
  rw [map_smul, AlgEquiv.apply_symm_apply, EKFinal.ratEquiv_iota] at this
  exact this

omit [Algebra ℚ k] in
/-- A homogeneous supercentral element of `Λ_k`. -/
def SuperCentralK (d : ℕ) (z : LamK k) : Prop :=
  z ∈ degreePieceK k d ∧ ∀ e, ∀ y ∈ degreePieceK k e, z * y = ((-1 : k) ^ (d * e)) • (y * z)

/-- Over `ℚ`: a degree-`d` element (`d` odd) that supercommutes with the images of the
homogeneous integral elements is `0`. -/
theorem superCentral_odd_rat (m : ℕ) (w : LamK ℚ) (hw : w ∈ degreePieceK ℚ (2 * m + 1))
    (hsc : ∀ e, ∀ y ∈ EKIntegralBases.degreePiece e,
      w * psiRing y = ((-1 : ℚ) ^ ((2 * m + 1) * e)) • (psiRing y * w)) : w = 0 := by
  obtain ⟨x, N, hN, hx⟩ := psiRing_rat_surj w
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  -- `x` is homogeneous of degree `2m+1`
  have hxd : x ∈ EKIntegralBases.degreePiece (2 * m + 1) := by
    have hdec : ∀ d, d ≠ 2 * m + 1 → EKIntegralBases.decompose x d = 0 := by
      intro d hd
      apply psiRing_rat_injective
      rw [← decomposeK_psiRing, ← hx, map_smul, decomposeK_piece hw, Finsupp.smul_apply,
        Finsupp.single_eq_of_ne (Ne.symm hd), smul_zero, map_zero]
    have hx' : x = EKIntegralBases.decompose x (2 * m + 1) := by
      conv_lhs => rw [← EKIntegralBases.recompose_decompose x]
      rw [EKIntegralBases.recompose_apply, Finsupp.sum]
      rw [Finset.sum_eq_single (2 * m + 1)]
      · intro d _ hd; exact hdec d hd
      · intro h0; exact (Finsupp.not_mem_support_iff.mp h0)
    rw [hx']
    exact EKIntegralBases.decompose_mem x _
  have hsc' : EKRest.SuperCentral (2 * m + 1) x := by
    refine ⟨hxd, fun e y hy => ?_⟩
    apply psiRing_rat_injective
    rw [map_mul, psiRing_zsmul, map_mul, ← hx, smul_mul_assoc, hsc e y hy, mul_smul_comm,
      smul_comm]
    push_cast; rfl
  rw [EKRest.superCentral_odd m x hsc', map_zero] at hx
  exact (smul_eq_zero.mp hx).resolve_left hNq

variable (k) in
/-- `c ⊗ z ↦ φ(c) ⊗ z`: the map `Λ_k → Λ_ℚ` induced by a `ℚ`-linear functional `φ` on `k`. -/
def dualMap (φ : Module.Dual ℚ k) : LamK k →ₗ[ℤ] LamK ℚ :=
  (EKFinal.baseChangeAlgEquiv ℚ).toLinearEquiv.toLinearMap.restrictScalars ℤ ∘ₗ
    ((φ.restrictScalars ℤ).rTensor QZ) ∘ₗ
      (EKFinal.baseChangeAlgEquiv k).symm.toLinearEquiv.toLinearMap.restrictScalars ℤ

theorem dualMap_smul_psiRing (φ : Module.Dual ℚ k) (c : k) (z : QZ) :
    dualMap k φ (c • psiRing z) = φ c • psiRing z := by
  simp only [dualMap, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply, map_smul, baseChangeAlgEquiv_symm_psiRing,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one, LinearMap.rTensor_tmul,
    EKFinal.baseChangeAlgEquiv_tmul]

theorem dualMap_mul_psiRing (φ : Module.Dual ℚ k) (x : LamK k) (y : QZ) :
    dualMap k φ (x * psiRing y) = dualMap k φ x * psiRing y ∧
      dualMap k φ (psiRing y * x) = psiRing y * dualMap k φ x := by
  induction x using induction_psi with
  | h0 => simp
  | hadd x x' hx hx' =>
    constructor
    · rw [add_mul, map_add, hx.1, hx'.1, map_add, add_mul]
    · rw [mul_add, map_add, hx.2, hx'.2, map_add, mul_add]
  | hsm c z =>
    rw [smul_mul_assoc, mul_smul_comm, ← map_mul, ← map_mul, dualMap_smul_psiRing,
      dualMap_smul_psiRing, dualMap_smul_psiRing, smul_mul_assoc, mul_smul_comm, map_mul, map_mul]
    exact ⟨rfl, rfl⟩

theorem dualMap_zsmul (φ : Module.Dual ℚ k) (n : ℤ) (x : LamK k) :
    dualMap k φ ((n : k) • x) = (n : ℚ) • dualMap k φ x := by
  rw [Int.cast_smul_eq_zsmul, map_zsmul, Int.cast_smul_eq_zsmul]

theorem dualMap_degree (φ : Module.Dual ℚ k) {d : ℕ} {x : LamK k} (hx : x ∈ degreePieceK k d) :
    dualMap k φ x ∈ degreePieceK ℚ d := by
  refine degreePieceK_induction (P := fun x => dualMap k φ x ∈ degreePieceK ℚ d) ?_ ?_ ?_ hx
  · simp
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  · intro c z hz
    rw [dualMap_smul_psiRing]
    exact Submodule.smul_mem _ _ (psi_degreePiece hz)

theorem dualMap_repr (φ : Module.Dual ℚ k) (x : LamK k) (μ : YoungDiagram) :
    (hBasisK (k := ℚ)).repr (dualMap k φ x) μ = φ ((hBasisK (k := k)).repr x μ) := by
  induction x using induction_psi with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add,
      Finsupp.add_apply, map_add]
  | hsm c z =>
    rw [dualMap_smul_psiRing, map_smul, map_smul, Finsupp.smul_apply, Finsupp.smul_apply,
      hBasisK_repr_psiRing, hBasisK_repr_psiRing, smul_eq_mul, smul_eq_mul, mul_comm c,
      ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]

/-- **EK p. 26 over every commutative `ℚ`-algebra `k`:** a homogeneous supercentral element of
odd degree is `0`. -/
theorem superCentralK_odd (m : ℕ) (z : LamK k) (hz : SuperCentralK (2 * m + 1) z) : z = 0 := by
  haveI : Module.Free ℚ k := Module.Free.of_divisionRing ℚ k
  apply (hBasisK (k := k)).repr.injective
  ext μ
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
  intro φ
  rw [← dualMap_repr]
  have h0 : dualMap k φ z = 0 := by
    apply superCentral_odd_rat m _ (dualMap_degree φ hz.1)
    intro e y hy
    have := congrArg (dualMap k φ) (hz.2 e (psiRing y) (psi_degreePiece hy))
    rw [(dualMap_mul_psiRing φ z y).1] at this
    rw [this, show ((-1 : k) ^ ((2 * m + 1) * e)) = (((-1 : ℤ) ^ ((2 * m + 1) * e) : ℤ) : k) by
      push_cast; rfl, dualMap_zsmul, (dualMap_mul_psiRing φ z y).2]
    push_cast; rfl
  rw [h0, map_zero, Finsupp.coe_zero, Pi.zero_apply]

omit [Algebra ℚ k] in
theorem superCentralK_even_central {m : ℕ} {z : LamK k} (hz : SuperCentralK (2 * m) z)
    (y : LamK k) : z * y = y * z := by
  rw [← sum_decomposeK y, Finsupp.sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hz.2 e _ (decomposeK_mem y e),
    show (-1 : k) ^ (2 * m * e) = 1 by rw [mul_assoc, pow_mul, neg_one_sq, one_pow], one_smul]

variable (k) in
/-- The supercentre: the `k`-span of the homogeneous supercentral elements. -/
def supercenterK : Submodule k (LamK k) := Submodule.span k {z | ∃ d, SuperCentralK d z}

omit [Algebra ℚ k] in
theorem pAlgK_le_supercenter : Subalgebra.toSubmodule (pAlgK k) ≤ supercenterK k := by
  rw [pAlgK, Algebra.adjoin_eq_span, Submodule.span_le]
  intro x hx
  have key : ∃ d, x ∈ degreePieceK k (2 * d) ∧ ∀ y, x * y = y * x := by
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact ⟨j + 1, psi_degreePiece (EKRest.p_mem _),
        (proposition_3_4_K (k := k) _ (by omega)).mpr (Or.inl ⟨j + 1, by ring⟩)⟩
    | one => exact ⟨0, one_mem_degreePieceK, fun y => by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, hca⟩ := hx
      obtain ⟨b, hb, hcb⟩ := hy
      refine ⟨a + b, by rw [mul_add]; exact mul_mem_degreePieceK ha hb, fun w => ?_⟩
      rw [mul_assoc, hcb, ← mul_assoc, hca, mul_assoc]
  obtain ⟨d, hd, hc⟩ := key
  apply Submodule.subset_span
  refine ⟨2 * d, hd, fun e y _ => ?_⟩
  rw [show (-1 : k) ^ (2 * d * e) = 1 by rw [mul_assoc, pow_mul, neg_one_sq, one_pow], one_smul]
  exact hc y

/-- **EK pp. 3, 26 over every commutative `ℚ`-algebra `k`: the centre of `Λ_k` coincides with
its supercentre.** -/
theorem supercenterK_eq_center :
    (supercenterK k : Set (LamK k)) = Subalgebra.center k (LamK k) := by
  ext z
  constructor
  · intro hz
    change z ∈ supercenterK k at hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨d, hd⟩ := hx
      rw [SetLike.mem_coe, Subalgebra.mem_center_iff]
      intro y
      obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' d
      · exact (superCentralK_even_central hd y).symm
      · rw [superCentralK_odd m x hd, mul_zero, zero_mul]
    | zero => exact Subalgebra.zero_mem _
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | smul c x _ hx => exact Subalgebra.smul_mem _ hx c
  · intro hz
    rw [SetLike.mem_coe, centerK_eq] at hz
    exact pAlgK_le_supercenter hz

end RatAlgebra

end OddMath.Frontier.EKOverK
